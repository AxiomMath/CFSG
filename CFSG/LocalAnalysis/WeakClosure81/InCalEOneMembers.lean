module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
import CFSG.LocalAnalysis.WeakClosure81.InCalEOneSurjective
import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalQuasisimple
import CFSG.LocalAnalysis.WeakClosure81.EOnePermThree
import CFSG.GroupTheory.PermFinThree
import CFSG.Quasithin.Vol2.Ch11SecU1Mem3
import CFSG.GroupTheory.CyclicNormalizerInvolution
import CFSG.GroupTheory.NormalSimpleTwoQuotient

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem inCalEi_sup_tA_of_isPGroup {T A : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P B : Subgroup G} (hT : CFSG.Quasithin.IsSylowIn 2 T ⊤) (hAT : A ≤ T)
    (hA : CFSG.Open.IsElemAbelian 2 A) {i : ℕ} (hi : 1 ≤ i)
    (hP : IsPGroup p P) (hne : P ≠ ⊥)
    (hτP : tA T A ≤ normalizer (P : Set G)) (hcomm : ⁅P, A⁆ = P)
    (hBA : B ≤ A) (hBc : B ≤ centralizer (P : Set G)) (hBidx : B.relIndex A ≤ 2) :
    InCalEi i T A (P ⊔ tA T A) := by
  obtain ⟨hE, hOne, -⟩ :=
    E1.isE_one_sup hp hp2 hT hAT hA hP hne hτP hcomm hBA hBc hBidx
  exact inCalEi_of_eOne hAT hA hE.2.1 hE.2.2.1 hOne hi

theorem inCalEi_sup_tA_of_isCyclic {T A : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hT : CFSG.Quasithin.IsSylowIn 2 T ⊤) (hAT : A ≤ T)
    (hA : CFSG.Open.IsElemAbelian 2 A) {i : ℕ} (hi : 1 ≤ i)
    (hP : IsPGroup p P) (hcyc : IsCyclic ↥P)
    (hτP : tA T A ≤ normalizer (P : Set G))
    (ha : ∃ a ∈ A, ¬ P ≤ centralizer ({a} : Set G)) :
    InCalEi i T A (P ⊔ tA T A) := by
  have hAτ : A ≤ tA T A := CFSG.LocalAnalysis.WeakClosure81.le_tA_of_isElemAbelian hAT hA
  have hAN : A ≤ normalizer (P : Set G) := hAτ.trans hτP
  obtain ⟨a, haA, haP⟩ := ha
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply haP
    intro x hx
    rw [hbot] at hx
    rw [Subgroup.mem_bot.mp hx]
    exact (Subgroup.centralizer ({a} : Set G)).one_mem
  have ha2 : a ^ 2 = 1 := hA.2 a haA
  have ha1 : a ≠ 1 := by
    intro h
    apply haP
    intro x hx
    rw [h]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  have hdich := CFSG.GroupTheory.conj_eq_or_eq_inv_of_isCyclic_of_isPGroup
    hp hp2 hP hcyc (hAN haA) ha2
  have hinv : ∀ x ∈ P, a * x * a⁻¹ = x⁻¹ := by
    rcases hdich with hc | hi'
    · exfalso
      apply haP
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * a = (a * x * a⁻¹) * a := by rw [hc x hx]
        _ = a * x := by group
    · exact hi'
  have hcomm : ⁅P, A⁆ = P :=
    CFSG.GroupTheory.commutator_eq_of_isCyclic_of_isPGroup_of_inverts
      hp hp2 hP hcyc hAN ⟨a, haA, hinv⟩
  have hAsup := CFSG.GroupTheory.sup_inf_centralizer_eq_of_isCyclic_of_isPGroup
    hp hp2 hP hcyc hAN hA haA hinv
  have hBidx := CFSG.GroupTheory.relIndex_inf_centralizer_eq_two_of_isCyclic_of_isPGroup
    hA haA haP ha2 ha1 hAsup
  exact inCalEi_sup_tA_of_isPGroup hp hp2 hT hAT hA hi hP hPne hτP hcomm
    inf_le_left inf_le_right hBidx.le

private theorem eCaseII_and_pow_mem_of_isSimpleGroup_branch {T A K L₀ τ : Subgroup G}
    (hAτ : A ≤ τ) (hτL : τ ≤ Subgroup.normalizer (L₀ : Set G))
    (hτT : τ ≤ T) (hT2 : IsPGroup 2 T)
    (hKdef : K = L₀ ⊔ τ) (hJn : (L₀.subgroupOf K).Normal)
    (e : ↥(L₀.subgroupOf K) ≃* ↥L₀)
    (hs : IsSimpleGroup ↥L₀) (hna : ∃ x y : ↥L₀, x * y ≠ y * x)
    (hidx : (A ⊓ Subgroup.centralizer (L₀ : Set G)).relIndex A = 2) :
    ECaseII T A K ∧ ∀ q : ↥K, ∃ k : ℕ, q ^ 2 ^ k ∈ L₀.subgroupOf K := by
  classical
  have hJK : L₀ ≤ K := by rw [hKdef]; exact le_sup_left
  have hAK : A ≤ K := hAτ.trans (by rw [hKdef]; exact le_sup_right)
  have hJ : IsSimpleGroup (L₀.subgroupOf K) := e.isSimpleGroup
  have hnaJ : ∃ x y : ↥(L₀.subgroupOf K), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hna
    refine ⟨e.symm x, e.symm y, ?_⟩
    intro h
    exact hxy (by simpa using congrArg e h)
  let J' : Subgroup ↥K := L₀.subgroupOf K
  have hτ2 : IsPGroup 2 τ := hT2.to_le hτT
  have hsup : J' ⊔ τ.subgroupOf K = ⊤ := by
    change L₀.subgroupOf K ⊔ τ.subgroupOf K = ⊤
    rw [hKdef]
    exact (Subgroup.codisjoint_subgroupOf_sup L₀ τ).eq_top
  have hτ2sub : IsPGroup 2 (τ.subgroupOf K) :=
    hτ2.comap_of_injective K.subtype K.subtype_injective
  have : J'.Normal := hJn
  have hK2sub : ∀ q : ↥K, ∃ k : ℕ, q ^ 2 ^ k ∈ J' :=
    CFSG.Quasithin.F6.exists_pow_mem_of_sup_eq_top hτ2sub hsup
  have hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ L₀ := by
    intro x hx
    obtain ⟨k, hk⟩ := hK2sub ⟨x, hx⟩
    exact ⟨k, Subgroup.mem_subgroupOf.mp hk⟩
  have hR2 := CFSG.GroupTheory.isPGroup_two_solvableRadical_of_isSimpleGroup hJ hnaJ hK2sub
  have hR : E1.IsTwoClosed (CFSG.solvableRadical ↥K) :=
    ⟨CFSG.solvableRadical ↥K,
      ⟨le_rfl, hR2, by rw [Subgroup.relIndex_self]; norm_num⟩,
      by rw [Subgroup.subgroupOf_self]; infer_instance⟩
  have hAN : A ≤ Subgroup.normalizer (L₀ : Set G) := hAτ.trans hτL
  have hAJ := CFSG.GroupTheory.exists_commutator_not_mem_solvableRadical_of_relIndex_two
    (K := K) hAN hJK hs hna hidx
  have hqPair := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥L₀) hna
  have hJq : CFSG.Open.IsQuasisimple ↥L₀ :=
    ⟨hqPair.1.1.commutator_eq_top, hqPair.1.2.1⟩
  refine ⟨?_, hK2sub⟩
  exact eCaseII_of_normal_quasisimple (hJK := hJK) (hJn := hJn) (hJq := hJq)
    hK2 hR hAK hAJ

private theorem pCore_two_eq_centralizer_of_isSimpleGroup {K L₀ : Subgroup G}
    (hJK : L₀ ≤ K) (hJn : (L₀.subgroupOf K).Normal)
    (e : ↥(L₀.subgroupOf K) ≃* ↥L₀)
    (hs : IsSimpleGroup ↥L₀) (hna : ∃ x y : ↥L₀, x * y ≠ y * x)
    (hcenterL : Subgroup.center ↥L₀ = ⊥)
    (hK2sub : ∀ q : ↥K, ∃ k : ℕ, q ^ 2 ^ k ∈ L₀.subgroupOf K) :
    CFSG.pCore 2 ↥K = (Subgroup.centralizer (L₀ : Set G)).subgroupOf K := by
  classical
  let J' : Subgroup ↥K := L₀.subgroupOf K
  have hJ : IsSimpleGroup J' := e.isSimpleGroup
  have hnaJ : ∃ x y : J', x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hna
    refine ⟨e.symm x, e.symm y, ?_⟩
    intro h
    exact hxy (by simpa using congrArg e h)
  have hcenterJ : Subgroup.center J' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply e.injective
    rw [map_one]
    have hzmap : e z ∈ Subgroup.center ↥L₀ := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := e.surjective w
      simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hz y)
    rw [hcenterL, Subgroup.mem_bot] at hzmap
    exact hzmap
  have hcent_eq : Subgroup.centralizer (J' : Set ↥K) =
      (Subgroup.centralizer (L₀ : Set G)).subgroupOf K := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      exact congrArg Subtype.val (h ⟨y, hJK hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
    · intro h y hy
      exact Subtype.ext (h y.1 (Subgroup.mem_subgroupOf.mp hy))
  apply le_antisymm
  · have h := CFSG.GroupTheory.pCore_two_le_centralizer_of_normal_simple
      (J := J') hJ hnaJ
    rwa [hcent_eq] at h
  · have : J'.Normal := hJn
    have hJC : J' ⊓ Subgroup.centralizer (J' : Set ↥K) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxc : (⟨x, hx.1⟩ : J') ∈ Subgroup.center J' := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y.1 y.2)
      rw [hcenterJ, Subgroup.mem_bot] at hxc
      exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hxc)
    have h := CFSG.LieType.BorelTits.le_pCore 2
      (inferInstance : (Subgroup.centralizer (J' : Set ↥K)).Normal)
      (CFSG.Quasithin.Vol2.Ch11.SecU1.Comp.isPGroup_two hJC hK2sub)
    rwa [hcent_eq] at h

theorem inCalEi_sup_tA_of_isSimpleGroup {T A : Subgroup G} {i : ℕ}
    (hT : CFSG.Quasithin.IsSylowIn 2 T ⊤) (hAT : A ≤ T)
    (hA : CFSG.Open.IsElemAbelian 2 A) (hi : 1 ≤ i)
    {L₀ : Subgroup G} (hs : IsSimpleGroup ↥L₀)
    (hna : ∃ x y : ↥L₀, x * y ≠ y * x)
    (hτL : tA T A ≤ normalizer (L₀ : Set G))
    (hSylL : CFSG.Quasithin.IsSylowIn 2 (T ⊓ L₀) L₀)
    (hidx : (A ⊓ centralizer (L₀ : Set G)).relIndex A = 2) :
    InCalEi i T A (L₀ ⊔ tA T A) := by
  classical
  have hE := CFSG.Quasithin.Vol2.Ch11.SecU1.componentMember_holds G T A L₀
    hT hAT hA hs hna hτL hSylL hidx
  obtain ⟨-, hτ, hSyl, hbranch⟩ := hE
  rcases hbranch with ⟨hOne, -⟩ | ⟨-, -⟩
  · exact inCalEi_of_eOne hAT hA hτ hSyl hOne hi
  · set τ : Subgroup G := tA T A with hτdef
    set K : Subgroup G := L₀ ⊔ τ with hKdef
    have hAτ : A ≤ τ := CFSG.LocalAnalysis.WeakClosure81.le_tA_of_isElemAbelian hAT hA
    have hAK : A ≤ K := hAτ.trans le_sup_right
    have hJK : L₀ ≤ K := le_sup_left
    have hτT : τ ≤ T := E1.tauOf_le _ _ _
    have hτK : τ ≤ K := le_sup_right
    have hKN : K ≤ Subgroup.normalizer (L₀ : Set G) := sup_le Subgroup.le_normalizer hτL
    have hJn : (L₀.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mpr hKN
    have : (L₀.subgroupOf K).Normal := hJn
    have hT2 : IsPGroup 2 T := hT.2.1
    let e : ↥(L₀.subgroupOf K) ≃* ↥L₀ := Subgroup.subgroupOfEquivOfLe hJK
    obtain ⟨hII, hK2sub⟩ :=
      eCaseII_and_pow_mem_of_isSimpleGroup_branch hAτ hτL hτT hT2 hKdef hJn e hs hna hidx
    have hqPair := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥L₀) hna
    have hcenterL : Subgroup.center ↥L₀ = ⊥ := hqPair.2
    have hOeqC := pCore_two_eq_centralizer_of_isSimpleGroup hJK hJn e hs hna hcenterL hK2sub
    set O : Subgroup ↥K := CFSG.pCore 2 ↥K with hOdef
    have hOrel : O.relIndex (A.subgroupOf K) = 2 := by
      rw [hOeqC, Subgroup.relIndex_subgroupOf hAK, ← Subgroup.inf_relIndex_right, inf_comm]
      exact hidx
    have hAbar2 : Nat.card (E1.barO2 ↥K (A.subgroupOf K)) = 2 := by
      have hbarrel : Nat.card (E1.barO2 ↥K (A.subgroupOf K)) =
          O.relIndex (A.subgroupOf K) := by
        unfold E1.barO2
        rw [← Subgroup.relIndex_ker (f := QuotientGroup.mk' O) (K := A.subgroupOf K),
          QuotientGroup.ker_mk' O]
      rw [hbarrel, hOrel]
    have hnA : ¬ A ≤ pCoreOf 2 K := by
      intro hle
      have h1 : (pCoreOf 2 K).relIndex A = 1 := Subgroup.relIndex_eq_one.mpr hle
      have h2 : Nat.card (E1.barO2 ↥K (A.subgroupOf K)) = 1 := by
        rw [card_barO2_subgroupOf_eq hAK, h1]
      omega
    have hm : E3.mQuot A (pCoreOf 2 K) = 1 := by
      have hrel : (pCoreOf 2 K).relIndex A = 2 := by
        rw [← card_barO2_subgroupOf_eq hAK, hAbar2]
      unfold E3.mQuot
      rw [hrel]
      exact padicValNat.self (p := 2) (by norm_num)
    refine ⟨⟨hτ, CFSG.ABGLocalTools.isSylowOf_iff.mpr hSyl, hnA, Or.inr hII⟩, ?_⟩
    rw [hm]
    exact hi

theorem inCalEi_of_bar2_mulEquiv_perm_three {T A K : Subgroup G} {i : ℕ}
    (hAT : A ≤ T) (hA : CFSG.Open.IsElemAbelian 2 A) (hi : 1 ≤ i)
    (hτ : tA T A ≤ T ⊓ K) (hSyl : CFSG.Quasithin.IsSylowIn 2 (T ⊓ K) K)
    (hK : Nonempty (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 K ≃* Equiv.Perm (Fin 3)))
    (hAO : ¬ A ≤ pCoreOf 2 K) : InCalEi i T A K := by
  classical
  obtain ⟨e⟩ := hK
  have hAK : A ≤ K :=
    (CFSG.LocalAnalysis.WeakClosure81.le_tA_of_isElemAbelian hAT hA).trans (hτ.trans inf_le_right)
  set Ā : Subgroup (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 K) :=
    E1.barO2 ↥K (A.subgroupOf K) with hĀdef
  set B : Subgroup (Equiv.Perm (Fin 3)) := Ā.map e.toMonoidHom with hBdef
  have hĀne : Ā ≠ ⊥ := by
    intro hbot
    apply hAO
    have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker = CFSG.pCore 2 ↥K :=
      QuotientGroup.ker_mk' _
    have hle : A.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff _).mp hbot
    calc A = (A.subgroupOf K).map K.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hAK).symm
      _ ≤ (CFSG.pCore 2 ↥K).map K.subtype := Subgroup.map_mono hle
      _ = pCoreOf 2 K := rfl
  have hBne : B ≠ ⊥ := by
    intro hbot
    apply hĀne
    exact (E1.map_eq_bot_iff_mulEquiv e Ā).mp hbot
  have hĀ2 : IsPGroup 2 Ā :=
    (hA.subgroupOf K).isPGroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have hB2 : IsPGroup 2 B := hĀ2.map e.toMonoidHom
  have hBcard : Nat.card B = 2 :=
    CFSG.GroupTheory.card_eq_two_of_isPGroup_two_of_ne_bot hB2 hBne
  have hOneBar : E1.EOne (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 K) Ā :=
    (E1.eOne_map e Ā).mpr (by simpa [B] using
      CFSG.LocalAnalysis.WeakClosure81.eOne_perm_fin_three_of_card_eq_two hBcard)
  have hOneK : E1.EOne ↥K (A.subgroupOf K) :=
    E1.eOne_of_surjective_of_isPGroup_ker
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (QuotientGroup.mk'_surjective _)
      (by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        rw [QuotientGroup.ker_mk']
        exact CFSG.pCore_isPGroup (p := 2) (G := ↥K))
      (A.subgroupOf K) hOneBar
  exact inCalEi_of_eOne hAT hA hτ hSyl hOneK hi

end CFSG.LocalAnalysis.WeakClosure81

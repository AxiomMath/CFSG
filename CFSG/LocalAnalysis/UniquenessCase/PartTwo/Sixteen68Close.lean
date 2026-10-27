module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen65
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s1668_comm_eq_bot_of_conj_le (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hW : ⁅E3.wClos V 0 D.T, V⁆ = ⊥) {g : G} (hg : conjSubgroup V g ≤ D.M) :
    ⁅V, conjSubgroup V g⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := h.isElemAbelian.isPGroup
  obtain ⟨m, hmM, hm⟩ := UC6.exists_conj_le_of_isSylowOf D.sylowM hg
    (E3.isPGroup_conjSubgroup hV2 g)
  have hle : conjSubgroup V (g * m) ≤ D.T := by
    rw [← conjSubgroup_conjSubgroup]
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have := hm _ hx
    simpa [mul_assoc] using this
  have hle0 : conjSubgroup V (g * m) ≤ E3.wClos V 0 D.T :=
    E3.le_wClos ⟨hle, g * m, le_rfl, E3.mQuot_self _⟩
  have h1 : ⁅V, conjSubgroup V (g * m)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact le_bot_iff.1 ((Subgroup.commutator_mono hle0 le_rfl).trans hW.le)
  have hVm : conjSubgroup V m⁻¹ = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (h.pairFacts.le_normalizer (by simpa using hmM))
  have h2 := E3.conjSubgroup_commutator V (conjSubgroup V (g * m)) m⁻¹
  rw [h1, E3.conjSubgroup_bot, hVm, conjSubgroup_conjSubgroup, mul_inv_cancel_right] at h2
  exact h2.symm

theorem s1668_gammaOneBar_le (D : Data G) (h22 : R1622 D) {V₀ V : Subgroup G}
    (h : Hyp16 D V₀ V) (hr : ((2 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V 1 D.M) {g : G} (hAg : A ≤ conjSubgroup V g) :
    gammaOneBar V A ≤ conjSubgroup D.M g := by
  rw [gammaOneBar]
  refine iSup_le fun B => iSup_le fun hBA => iSup_le fun hq => ?_
  have hi2 : E3.mQuot (conjSubgroup V g) B ≤ 2 := by
    have hadd := E3.mQuot_add hBA hAg
    rw [hadd, mQuot_eq_of_mem_gammaSet hA hAg]
    omega
  have hB : B ∈ E3.gammaSet V (E3.mQuot (conjSubgroup V g) B) D.M :=
    ⟨hBA.trans hA.1, g, hBA.trans hAg, rfl⟩
  have hi : ((E3.mQuot (conjSubgroup V g) B + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right hi2 (mSub V₀)) hr
  exact (sixteen_twentyThree_one D h22 h hB (hBA.trans hAg) hi).2.2

theorem s1668_card_barSub_bot {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ normalizer (V : Set G)) :
    Nat.card (barSub ⊥ V hV A) = (centralizer (V : Set G)).relIndex A := by
  have hstab : stabTil (⊥ : Subgroup G) V = normalizer (V : Set G) := by
    have hbot : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)
    rw [stabTil, hbot]
    simp
  have hAstab : A ≤ stabTil (⊥ : Subgroup G) V := by
    intro a ha
    rw [hstab]
    exact hA ha
  have hmem_ker : ∀ g : ↥(stabTil (⊥ : Subgroup G) V),
      actTil ⊥ V hV g = 1 ↔ (g : G) ∈ centralizer (V : Set G) := by
    intro g
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one', actTil_eq_one_iff]
    refine forall₂_congr fun v _hv => ?_
    rw [Subgroup.mem_bot, commutatorElement_def]
  let K : Subgroup ↥(stabTil (⊥ : Subgroup G) V) := A.subgroupOf (stabTil (⊥ : Subgroup G) V)
  have hker : (actTil ⊥ V hV).ker =
      (centralizer (V : Set G)).subgroupOf (stabTil (⊥ : Subgroup G) V) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hmem_ker g]
  let e : ↥K ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAstab
  let e' : ↥A →* ↥K := (e.symm : ↥A →* ↥K)
  have heq : ((actTil ⊥ V hV).ker.subgroupOf K).comap e' =
      (centralizer (V : Set G)).subgroupOf A := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change actTil ⊥ V hV (e' x) = 1 ↔ (x : G) ∈ centralizer (V : Set G)
    rw [hmem_ker (e' x)]
    rfl
  have hidx : ((actTil ⊥ V hV).ker.subgroupOf K).index =
      ((centralizer (V : Set G)).subgroupOf A).index := by
    rw [← Subgroup.index_comap_of_surjective (H := (actTil ⊥ V hV).ker.subgroupOf K)
      (f := e') e.symm.surjective, heq]
  calc Nat.card (barSub ⊥ V hV A) = (actTil ⊥ V hV).ker.relIndex K :=
        (Subgroup.relIndex_ker (K := K) (actTil ⊥ V hV)).symm
    _ = ((actTil ⊥ V hV).ker.subgroupOf K).index := rfl
    _ = ((centralizer (V : Set G)).subgroupOf A).index := hidx
    _ = (centralizer (V : Set G)).relIndex A := rfl

theorem r16_68_close_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h1217 : R1217 D) (h22 : R1622 D) (h129 : R129_1 D) (h159 : R15_9Small D) :
    R16_68_close D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro V₀ V L hV hS hs h0 A g hA hAbar hAg
  subst h0
  have hmsubbot : mSub (⊥ : Subgroup G) = 0 := by
    rw [mSub, rk, Subgroup.card_bot]
    exact padicValNat.eq_zero_of_not_dvd (by norm_num)
  obtain ⟨x, hxM, hxn⟩ := c23_exists_mem_not_nBar D hS.setting.hyp151 hV hs.1.2.2.1
  let W : Subgroup G := wSub ⊥ V hV L
  let W₂ : Subgroup G := conjSubgroup W x
  have hsup : W ⊔ W₂ = V := s1667_sup_conj_eq D h1217 hS hs.1 hxM hxn
  have hinf : W ⊓ W₂ = ⊥ := s1667_inf_conj_eq D hS hs.1 hxM hxn
  have hW₁ : Nat.card W = 4 := by
    change Nat.card (wSub ⊥ V hV L) = 4
    rw [s1667_card_wSub D hS hs.1, Subgroup.card_bot, mul_one]
  have hW₂ : Nat.card W₂ = 4 := by
    change Nat.card (conjSubgroup (wSub ⊥ V hV L) x) = 4
    rw [E3.card_conjSubgroup (wSub ⊥ V hV L) x]
    exact hW₁
  have hAea : IsElemAbelian 2 A := (E3.isElemAbelian_conjSubgroup hV g).mono hAg
  have hperm : ∀ a ∈ A, (conjSubgroup W a = W ∧ conjSubgroup W₂ a = W₂) ∨
      (conjSubgroup W a = W₂ ∧ conjSubgroup W₂ a = W) := by
    intro a ha
    have ham : a ∈ D.M := D.sylowM.le (hA.1 ha)
    have h := s1667_conj_cases D hS hs.1 hxM hxn ham
    simpa only [W, W₂] using h
  have h4le : (centralizer (V : Set G)).relIndex A ≤ 4 :=
    s1667_relIndex_centralizer_le_four hV hsup hinf hW₁ hW₂ hAea hperm
  have hAM : A ∈ E3.gammaSet V 1 D.M := E3.gammaSet_mono D.sylowM.le hA
  have hAnorm : A ≤ normalizer (V : Set G) :=
    (hA.1.trans D.sylowM.le).trans hS.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hcard : Nat.card (barSub ⊥ V hV A) = (centralizer (V : Set G)).relIndex A :=
    s1668_card_barSub_bot hV hAnorm
  have hr65 : (2 : ℕ∞) < rMV D.M V := r16_65_holds D hSg h61 h1217 ⊥ V L hV hS hs rfl
  have hr : ((2 + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
    simpa [hmsubbot] using hr65
  have hΓ : gammaOneBar V A ≤ conjSubgroup D.M g :=
    s1668_gammaOneBar_le D h22 hS.setting.hyp16 hr hAM hAg
  have hApg : IsPGroup 2 A := hAea.isPGroup
  have hpow : ∃ k, (centralizer (V : Set G)).relIndex A = 2 ^ k := by
    refine ⟨E3.mQuot A (A ⊓ centralizer (V : Set G)), ?_⟩
    rw [← E3.relIndex_eq_two_pow hApg (A ⊓ centralizer (V : Set G))]
    show ((centralizer (V : Set G)).subgroupOf A).index =
      ((A ⊓ centralizer (V : Set G)).subgroupOf A).index
    rw [Subgroup.inf_subgroupOf_left]
  have hn1 : (centralizer (V : Set G)).relIndex A ≠ 1 := by
    intro h1
    exact hAbar (Subgroup.eq_bot_of_card_eq (H := barSub ⊥ V hV A) (hcard.trans h1))
  have hn2 : (centralizer (V : Set G)).relIndex A ≠ 2 := by
    intro h2
    let B : Subgroup G := A ⊓ centralizer (V : Set G)
    have hBA : B ≤ A := inf_le_left
    have hrelB : B.relIndex A = 2 := by
      show (A ⊓ centralizer (V : Set G)).relIndex A = 2
      rw [inf_comm, Subgroup.inf_relIndex_right]
      exact h2
    have hmq : E3.mQuot A B ≤ 1 := by
      change E3.mQuot A (A ⊓ centralizer (V : Set G)) ≤ 1
      unfold E3.mQuot
      rw [hrelB]
      simpa using (padicValNat.prime_pow (p := 2) 1)
    have hVleCB : V ≤ centralizer (B : Set G) := by
      have hBle : B ≤ centralizer (V : Set G) := inf_le_right
      exact Subgroup.le_centralizer_iff.mp hBle
    have hVB : V ⊓ centralizer (B : Set G) = V := inf_eq_left.mpr hVleCB
    have hVgamma : V ≤ gammaOneBar V A := by
      have hle : V ⊓ centralizer (B : Set G) ≤ gammaOneBar V A :=
        le_iSup_of_le B (le_iSup_of_le hBA (le_iSup_of_le hmq le_rfl))
      rwa [hVB] at hle
    have hVgM : V ≤ conjSubgroup D.M g := hVgamma.trans hΓ
    have hconj : conjSubgroup V g⁻¹ ≤ D.M := by
      have hmono := E3.conjSubgroup_mono_left g⁻¹ hVgM
      rwa [E3.conjSubgroup_conj_inv] at hmono
    have hW0 : ⁅E3.wClos V 0 D.T, V⁆ = ⊥ :=
      (sixteen_sixtyThree D hSg h129 h61 h159 ⊥ V L hV hS ⟨Or.inr hs.1, hs.2⟩).1
    have hcomm : ⁅V, conjSubgroup V g⁻¹⁆ = ⊥ :=
      s1668_comm_eq_bot_of_conj_le D hS.setting.hyp16.hyp125 hW0 hconj
    have hcomm' : ⁅conjSubgroup V g, V⁆ = ⊥ := by
      have hconj2 := E3.conjSubgroup_commutator V (conjSubgroup V g⁻¹) g
      rw [hcomm, E3.conjSubgroup_bot, E3.conjSubgroup_inv_conj] at hconj2
      exact hconj2.symm
    have hconjC : conjSubgroup V g ≤ centralizer (V : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm'
    have hAC : A ≤ centralizer (V : Set G) := hAg.trans hconjC
    have hone : (centralizer (V : Set G)).relIndex A = 1 := by
      show ((centralizer (V : Set G)).subgroupOf A).index = 1
      rw [Subgroup.subgroupOf_eq_top.mpr hAC, Subgroup.index_top]
    exact hn1 hone
  obtain ⟨k, hk⟩ := hpow
  have hk_le : k ≤ 2 := by
    have h2k : 2 ^ k ≤ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hk]
      exact h4le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2k
  have hk0 : k ≠ 0 := fun hk0 => hn1 (by rw [hk, hk0, pow_zero])
  have hk1 : k ≠ 1 := fun hk1 => hn2 (by rw [hk, hk1, pow_one])
  have hk2 : k = 2 := by omega
  have hn4 : (centralizer (V : Set G)).relIndex A = 4 := by
    rw [hk, hk2]
    norm_num
  refine ⟨?_, hΓ, ?_⟩
  · rw [rk, hcard, hn4, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact padicValNat.prime_pow (p := 2) 2
  · exact s1667_relIndex_gammaOneBar_le_two hV hsup hinf hW₁ hW₂ hAea hperm hn4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftBij
public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftIndex
public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftMaps
public import CFSG.Quasithin.H13.L32A53c
public import CFSG.Quasithin.H13.L32A58a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Family
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSubnormal_of_open_top {H : Subgroup G} (h : CFSG.Open.IsSubnormal H ⊤) :
    H.IsSubnormal :=
  CFSG.Open.IsSubnormal.top_iff.1 h

theorem isQuasisimple_of_isSimpleGroup' {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hnc : ∃ x y : Q, x * y ≠ y * x) : CFSG.IsQuasisimple Q := by
  have hperf : Group.IsPerfect Q := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have : ⁅x, y⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
        (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact ⟨h⟩
  have hc : Subgroup.center Q = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      exact hxy ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y)) x)
  have e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨hperf, (MulEquiv.isSimpleGroup_congr e).mpr hs, ?_⟩
  obtain ⟨x, y, hxy⟩ := hnc
  exact ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩

namespace T53

namespace Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx G T L V V₂ Y)
include C

omit [Finite G] C in
theorem isSimpleGroup_quot {K : Subgroup G}
    (hiso : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* GL32)) :
    IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
  rcases hiso with h5 | h3
  · obtain ⟨e⟩ := h5
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact (MulEquiv.isSimpleGroup_congr e).mpr this
  · obtain ⟨e⟩ := h3
    exact G58.isSimpleGroup_of_gl32 e

theorem structure_of_mem_cComp (h4 : Lemma14_7_4_two_three) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    {K : Subgroup G} (hK : K ∈ cComp (hY T L V₂ Y))
    (hiso : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* GL32)) :
    hY T L V₂ Y ≤ Subgroup.normalizer (K : Set G) ∧ hY T L V₂ Y = K ⊔ T ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* GL32) ∧ xL L V₂ ≤ K ∧ Y ≤ K := by
  set I := hY T L V₂ Y with hIdef
  have hGI : F6.IsGoldschmidtTripleIn I (xL L V₂ ⊔ T) (Y ⊔ T) := C.goldschmidt h4
  have hKI : K ≤ I := le_of_mem_cComp hK
  have hKsub : IsSubnormal K I := subnormal_of_mem_cComp hK
  have hs : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥I) := hGI.isSolvable_pPrimeCore
  have hsimple := isSimpleGroup_quot hiso
  have hnorm : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  set S := Gold14610.imgMod3 I K with hSdef
  set p : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥S :=
    QuotientGroup.lift (CFSG.pCore 2 ↥K) (Gold14610.toImg hKI)
      (Gold14610.pCore_le_ker_toImg hKI hKsub) with hpdef
  have hpk : ∀ k : ↥K, p (QuotientGroup.mk k) = Gold14610.toImg hKI k := fun k => rfl
  have hp : Function.Surjective p := by
    intro b
    obtain ⟨k, rfl⟩ := Gold14610.toImg_surjective hKI b
    exact ⟨QuotientGroup.mk k, hpk k⟩
  have hinj : Function.Injective p := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal p.ker with hb | ht
    · exact (MonoidHom.ker_eq_bot_iff p).mp hb
    ·
      exfalso
      have hmem : ∀ k : ↥K, Subgroup.inclusion hKI k ∈ CFSG.pPrimeCore 3 ↥I := by
        intro k
        have h1 : (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ p.ker := ht ▸ Subgroup.mem_top _
        rw [MonoidHom.mem_ker, hpk] at h1
        exact (Gold14610.mem_ker_toImg hKI k).mp h1
      have hinjf : Function.Injective
          ((Subgroup.inclusion hKI).codRestrict (CFSG.pPrimeCore 3 ↥I) hmem) := by
        intro a b hab
        exact Subgroup.inclusion_injective hKI (congrArg Subtype.val hab)
      exact not_isSolvable_of_mem_cComp hK (Group.isSolvable_of_isSolvable_injective hinjf)
  set eK : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥S := MulEquiv.ofBijective p ⟨hinj, hp⟩ with heK
  have hnc : ∃ x y : ↥K ⧸ CFSG.pCore 2 ↥K, x * y ≠ y * x := by
    by_contra hall
    push Not at hall
    have : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) := Group.isSolvable_of_comm hall
    have : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := by
      have h2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := by
        exact CFSG.LieType.BorelTits.pCore_isPGroup 2
      have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) := h2.isNilpotent
      infer_instance
    exact not_isSolvable_of_mem_cComp hK
      (Group.isSolvable_of_subgroup_quotient (CFSG.pCore 2 ↥K))
  have hsS : IsSimpleGroup ↥S := (MulEquiv.isSimpleGroup_congr eK.symm).mpr hsimple
  have hncS : ∃ x y : ↥S, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eK x, eK y, fun h => hxy (eK.injective (by rw [map_mul, map_mul, h]))⟩
  rcases hGI.goldschmidt_mod_pPrimeCore with ⟨-, hA, -⟩ | ⟨-, -, ⟨eS3⟩, -, -⟩
  swap
  · exfalso
    have h1 : Nat.card ↥S ≤ Nat.card (↥I ⧸ CFSG.pPrimeCore 3 ↥I) :=
      Subgroup.card_le_card_group S
    rw [Nat.card_congr eS3.toEquiv, gold_card_perm_fin_three,
      ← Nat.card_congr eK.toEquiv] at h1
    rcases hiso with h5 | h3
    · obtain ⟨e⟩ := h5
      rw [Nat.card_congr e.toEquiv, G58.card_alt5] at h1
      norm_num at h1
    · obtain ⟨e⟩ := h3
      rw [G58.card_of_gl32 e] at h1
      norm_num at h1
  have hX3 : Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2 :=
    stronglyQuasithin_of_pCoreOf_ne_bot C.hyp.fsu.qtke hQ 3 Nat.prime_three (by norm_num)
  obtain ⟨hO3, hm3⟩ := F6.pPrimeCore_eq_bot_and_pRank_le hX3
    (MulEquiv.refl (↥I ⧸ CFSG.pPrimeCore 3 ↥I))
  have hSc : CFSG.IsComponent S := by
    refine ⟨isQuasisimple_of_isSimpleGroup' hsS hncS, ?_⟩
    exact isSubnormal_of_open_top
      (subnormal_of_mem_cComp ((Gold14610.imgMod3_bijOn I hs).mapsTo hK))
  obtain ⟨hSn, hcases, -⟩ := F6.f6_10 hA.toIsGoldschmidtTriple hSc
    (F6.index_normalizer_le_two_of_isComponent hO3 hm3 hSc)
  have hS' : Nonempty (↥S ≃* alternatingGroup (Fin 5)) ∨ Nonempty (↥S ≃* GL32) := by
    rcases hiso with h5 | h3
    · obtain ⟨e⟩ := h5
      exact Or.inl ⟨eK.symm.trans e⟩
    · obtain ⟨e⟩ := h3
      exact Or.inr ⟨eK.symm.trans e⟩
  have hL : twoResidual (Gold14610.imgMod3 I (xL L V₂ ⊔ T)) ≤ S ∨
      twoResidual (Gold14610.imgMod3 I (Y ⊔ T)) ≤ S := by
    rcases hcases with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact Or.inl h1
    · exact Or.inr h2
  obtain ⟨⟨eS⟩, h₁, h₂⟩ := G58.gl32_of_amalgam hA.toIsGoldschmidtTriple hA.pCore_eq_bot hS' hL
  have hn : I ≤ Subgroup.normalizer (K : Set G) :=
    Gold14610.le_normalizer_of_imgMod3_normal hs hK hSn
  have hIKT : I = K ⊔ T := by
    have := Gold14610.eq_sup_inf_of_twoResidual_le hKI hn hGI h₁ h₂
    rwa [C.inf_eq h4] at this
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := le_sup_right.trans hn
  have hO2 : oTwoUpper I ≤ K := by
    rw [hIKT]
    exact oTwoUpper_sup_le_of_two C.hyp.fsu.sylow.1 hTK
  refine ⟨hn, hIKT, ⟨eK.trans eS⟩, ?_, ?_⟩
  · calc xL L V₂ = oTwoUpper (xL L V₂ ⊔ T) := C.oTwoUpper_xT.symm
      _ ≤ oTwoUpper I := oTwoUpper_mono (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      _ ≤ K := hO2
  · calc Y = oTwoUpper (Y ⊔ T) := C.oTwoUpper_yT.symm
      _ ≤ oTwoUpper I := oTwoUpper_mono (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
      _ ≤ K := hO2

end Ctx

end T53

end CFSG.Quasithin.H13.L32A

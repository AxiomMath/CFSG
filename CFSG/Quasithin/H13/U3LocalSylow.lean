module

public import CFSG.Quasithin.H13.U3ElemNine
public import CFSG.Quasithin.H13.U3FrameKernel
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

theorem exists_noncomm_of_isSimpleGroup_of_card_nine {S : Type*} [Group S] [IsSimpleGroup S]
    {E : Subgroup S} (hE : IsElementaryAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hEne : E ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at hE9
    norm_num at hE9
  obtain ⟨⟨x, hx⟩, hx1⟩ := ne_bot_iff_exists_ne_one.mp hEne
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  have hx3 : x ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hn : (zpowers x).Normal :=
    ⟨fun a ha g => by rw [h g a, mul_inv_cancel_right]; exact ha⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers x) with hb | ht
  · exact hx1' (by rw [← mem_bot, ← hb]; exact mem_zpowers x)
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1'
    have hS : Nat.card S = 3 := by rw [← card_top, ← ht, Nat.card_zpowers, hord]
    have : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
    have := card_le_card_group E
    omega

theorem center_eq_bot_of_isSimpleGroup_of_noncomm {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((mem_center_iff.mp (h ▸ mem_top b)) a)

theorem isQuasisimple_of_isSimpleGroup_of_noncomm {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : CFSG.IsQuasisimple S := by
  have hc : center S = ⊥ := center_eq_bot_of_isSimpleGroup_of_noncomm hnab
  let e : S ⧸ center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hcomm : commutator S = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator S := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
      exact hmem
    · exact h
  refine ⟨Group.isPerfect_def.mpr hcomm, ?_, ?_⟩
  · exact @MulEquiv.isSimpleGroup _ _ _ _ ‹IsSimpleGroup S› e
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩

variable {G : Type} [Group G]

theorem map_conj_eq_self_of_mem {E : Subgroup G} {t : G} (ht : t ∈ E) :
    E.map (MulAut.conj t).toMonoidHom = E := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact E.mul_mem (E.mul_mem ht hy) (E.inv_mem ht)
  · intro hx
    refine ⟨t⁻¹ * x * t, E.mul_mem (E.mul_mem (E.inv_mem ht) hx) ht, ?_⟩
    change t * (t⁻¹ * x * t) * t⁻¹ = x
    group

theorem unitary_three_field_three_local_Sylow_normalization [Finite G] (hG : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : QuasithinUnique.quasithinIsQTKECat G)
    {T L : Subgroup G} (hL : quasithinIsLocal T L)
    (hU3 : CFSG.Blueprint.LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    (L.subgroupOf (L ⊔ T)).Normal ∧ T ≤ normalizer (L : Set G) ∧
      ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup G := hG
  obtain ⟨-, hLc, -, hQ1⟩ := hL
  set E := L ⊔ T with hE
  set Q := pCoreOf 2 E with hQ
  have hLE : L ≤ E := le_sup_left
  have hQE : Q ≤ E := LieType.BorelTits.pCoreOf_le 2 E
  have hQn : (Q.subgroupOf E).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQE).2 (LieType.BorelTits.le_normalizer_pCoreOf 2 E)
  have hQ2 : IsPGroup 2 Q := LieType.BorelTits.pCoreOf_isPGroup 2 E
  have hQs : Group.IsSolvable Q := by
    have := hQ2.isNilpotent
    infer_instance
  have hbij := cComp_quotient_bijOn_of_le hQE hQn hQs
  have hLc' : L ∈ cComp E := hLc
  set X := ↥E ⧸ Q.subgroupOf E
  set π := QuotientGroup.mk' (Q.subgroupOf E) with hπ
  set A := (L.subgroupOf E).map π with hA
  have hAc : A ∈ cComp (⊤ : Subgroup X) := hbij.mapsTo hLc'
  set f : ↥L →* X := π.comp (inclusion hLE) with hf
  have hfrange : f.range = A := by
    rw [hf, MonoidHom.range_comp, inclusion_range]
  have hfker : f.ker = CFSG.pCore 2 ↥L := by
    have hker : f.ker = Q.subgroupOf L := by
      ext l
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
      rfl
    rw [hker]
    refine le_antisymm ?_ ?_
    · refine le_sSup ⟨?_, ?_⟩
      · have h1 : (Q.subgroupOf E).comap (inclusion hLE) = Q.subgroupOf L := by
          ext l
          rfl
        rw [← h1]
        exact hQn.comap _
      · exact hQ2.comap_of_injective (L.subtype) L.subtype_injective |>.of_equiv
          (MulEquiv.refl _)
    · intro l hl
      rw [mem_subgroupOf]
      have h1 : (l : G) ∈ CFSG.inSubgroup (CFSG.pCore 2) L := ⟨l, hl, rfl⟩
      rw [inSubgroup_pCore_eq_pCoreOf] at h1
      exact RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2
        (subnormal_of_mem_cComp hLc') h1
  let e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥A :=
    ((QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hfrange)
  have hLsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := isSimpleGroup_of_lieModel_PSU hU3
  have hAsimple : IsSimpleGroup ↥A := e.symm.isSimpleGroup
  obtain ⟨⟨E9, hE9e, hE9c⟩, -⟩ := unitary_three_field_three_elementary_nine_subgroup hU3
  have hE9A : IsElementaryAbelian 3 (E9.map e.toMonoidHom) := by
    have := hE9e
    exact IsElementaryAbelian.map _
  have hE9Ac : Nat.card (E9.map e.toMonoidHom) = 9 := by
    rw [card_map_of_injective e.injective, hE9c]
  have hAnab : ∃ a b : ↥A, a * b ≠ b * a :=
    exists_noncomm_of_isSimpleGroup_of_card_nine hE9A hE9Ac
  have hArank : 2 ≤ CFSG.pRank 3 ↥A :=
    le_csSup (SteinbergBM.bddAbove_pRank_set (X := ↥A) (by norm_num))
      ⟨_, hE9A, by rw [hE9Ac]; norm_num⟩
  have hAZ : center ↥A = ⊥ := center_eq_bot_of_isSimpleGroup_of_noncomm hAnab
  have hAcomp : CFSG.IsComponent A :=
    ⟨isQuasisimple_of_isSimpleGroup_of_noncomm hAnab,
      A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hAc)⟩
  have hcore := QuasithinUnique.qtkeCore_of_cat hnonab hqtke
  have hEsqtk := hcore.1 E hQ1
  have hE3 : CFSG.pRank 3 ↥E ≤ 2 := hEsqtk.1 3 Nat.prime_three (by norm_num)
  have hX3 : CFSG.pRank 3 X ≤ 2 := by
    have : (Q.subgroupOf E).Normal := hQn
    have hN : ¬ 3 ∣ Nat.card (Q.subgroupOf E) := by
      have hQ2' : IsPGroup 2 (Q.subgroupOf E) :=
        hQ2.of_equiv (subgroupOfEquivOfLe hQE).symm
      obtain ⟨k, hk⟩ := hQ2'.exists_card_eq
      rw [hk]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_quotient_eq _ hN,
      ← SectionRank.pRank_eq_open_pRank_top]
    exact hE3
  have hAn : A.Normal := SteinbergBM.centerless_component_rank_forces_normality
    Nat.prime_three hAcomp hAZ (lt_of_le_of_lt hX3 (by omega))
  have hTN : T ≤ normalizer (L : Set G) := by
    intro t ht
    have htE : t ∈ E := (le_sup_right : T ≤ E) ht
    set L' := L.map (MulAut.conj t).toMonoidHom with hL'
    have hL'c : L' ∈ cComp E := by
      have h1 := cComp_map_mulEquiv (MulAut.conj t) hLc'
      rwa [map_conj_eq_self_of_mem htE] at h1
    have hL'img : (L'.subgroupOf E).map π ∈ cComp (⊤ : Subgroup X) := hbij.mapsTo hL'c
    have hle : (L'.subgroupOf E).map π ≤ A := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨l, hl, hly⟩ := hy
      have hlE : l ∈ E := hLE hl
      have hy' : y = ⟨t, htE⟩ * ⟨l, hlE⟩ * (⟨t, htE⟩ : ↥E)⁻¹ := Subtype.ext hly.symm
      rw [hy', map_mul, map_mul, map_inv]
      exact hAn.conj_mem _ ⟨⟨l, hlE⟩, hl, rfl⟩ _
    have heq : (L'.subgroupOf E).map π = A := by
      by_contra hne
      exact not_subnormal_of_mem_cComp hAc (lt_of_le_of_ne hle hne)
        (ne_bot_of_mem_cComp hL'img) (perfect_of_mem_cComp hL'img)
        (subnormal_of_mem_cComp hL'img)
    have hLL : L' = L := hbij.injOn hL'c hLc' heq
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : t * h * t⁻¹ ∈ L' := ⟨h, hh, rfl⟩
      rwa [hLL] at this
    · intro hh
      rw [← hLL] at hh
      obtain ⟨l, hl, hlh⟩ := hh
      have : l = h := by
        have h1 : t * l * t⁻¹ = t * h * t⁻¹ := hlh
        simpa using h1
      exact this ▸ hl
  refine ⟨(normal_subgroupOf_iff_le_normalizer hLE).2 (sup_le le_normalizer hTN), hTN, ?_⟩
  exact coe_mul_of_right_le_normalizer_left L T hTN

end CFSG.Quasithin.H13.U3

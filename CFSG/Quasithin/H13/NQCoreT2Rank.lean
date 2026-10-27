module

public import CFSG.Quasithin.H13.NQCoreT2Gap
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5aAut
public import CFSG.Quasithin.H13.NQCoreEscapingResidual
public import CFSG.Quasithin.H13.NQCoreHYPair
public import CFSG.Quasithin.H13.NQCoreHYTools

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem center_eq_bot_of_isSimpleGroup_of_isPerfect {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : Group.IsPerfect S) : center S = ⊥ := by
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hc : commutator S = ⊥ := by
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [mem_centralizer_iff]
      intro y _
      exact mem_center_iff.mp (h ▸ mem_top x) y
    rw [hS.commutator_eq_top] at hc
    exact top_ne_bot hc

theorem center_eq_bot_of_conj_injective {S : Type*} [Group S]
    (h : Function.Injective (MulAut.conj : S →* MulAut S)) : center S = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  apply h
  rw [map_one]
  ext x
  rw [MulAut.conj_apply, MulAut.one_apply, ← mem_center_iff.mp hz x, mul_inv_cancel_right]

theorem center_eq_bot_of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : center S' = ⊥) : center S = ⊥ := by
  rw [← map_center_mulEquiv e] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem conjNormal_injective_of_two_quotient {B : Type*} [Group B] {Yb : Subgroup B}
    [Yb.Normal] (hZ : center ↥Yb = ⊥) (h2 : ∀ b : B, ∃ k : ℕ, b ^ 2 ^ k ∈ Yb)
    (hO : CFSG.pCore 2 B = ⊥) : Function.Injective (MulAut.conjNormal : B →* MulAut ↥Yb) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hC2 : IsPGroup 2 (centralizer (Yb : Set B)) := by
    intro c
    obtain ⟨k, hk⟩ := h2 c
    refine ⟨k, Subtype.ext ?_⟩
    have hcZ : (⟨(c : B) ^ 2 ^ k, hk⟩ : ↥Yb) ∈ center ↥Yb := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp (pow_mem c.2 _) y y.2)
    rw [hZ, mem_bot] at hcZ
    have h3 := congrArg Subtype.val hcZ
    simpa using h3
  have hC : centralizer (Yb : Set B) ≤ CFSG.pCore 2 B :=
    le_sSup (show centralizer (Yb : Set B) ∈ {K : Subgroup B | K.Normal ∧ IsPGroup 2 K} from
      ⟨inferInstance, hC2⟩)
  have hbC : b ∈ centralizer (Yb : Set B) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut ↥Yb => ((φ ⟨y, hy⟩ : ↥Yb) : B)) hb
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc y * b = b * y * b⁻¹ * b := by rw [h1]
      _ = b * y := by group
  have := hC hbC
  rwa [hO, mem_bot] at this

theorem nonempty_map_mk_pCore_equiv {Q : Type*} [Group Q] [Finite Q] (Y : Subgroup Q)
    [Y.Normal] :
    Nonempty (↥(Y.map (QuotientGroup.mk' (CFSG.pCore 2 Q))) ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  set f : ↥Y →* Q ⧸ CFSG.pCore 2 Q := (QuotientGroup.mk' (CFSG.pCore 2 Q)).comp Y.subtype
    with hf
  have hker : f.ker = CFSG.pCore 2 ↥Y := by
    ext y
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have h1 := pCore_map_eq_inf_of_normal (Q := Q) (Y := Y)
    constructor
    · intro hy
      have h2 : (y : Q) ∈ Y ⊓ CFSG.Open.pCore 2 Q := mem_inf.mpr ⟨y.2, hy⟩
      rw [← h1] at h2
      obtain ⟨z, hz, hzy⟩ := h2
      rwa [show z = y from Subtype.ext hzy] at hz
    · intro hy
      have h2 := mem_map_of_mem Y.subtype hy
      rw [h1] at h2
      exact (mem_inf.mp h2).2
  have hrange : f.range = Y.map (QuotientGroup.mk' (CFSG.pCore 2 Q)) := by
    rw [hf, MonoidHom.range_comp, range_subtype]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker))⟩

theorem isSylowTwoOf_map_range_of_top {Q D : Type*} [Group Q] [Group D] {T : Subgroup Q}
    (hT : IsSylowTwoOf T ⊤) (φ : Q →* D) : IsSylowTwoOf (T.map φ) φ.range := by
  refine ⟨map_le_range _ _, hT.2.1.map φ, ?_⟩
  have heq : (T.map φ).subgroupOf φ.range = T.map φ.rangeRestrict := by
    ext y
    simp only [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨t, ht, hty⟩
      exact ⟨t, ht, Subtype.ext hty⟩
    · rintro ⟨t, ht, hty⟩
      exact ⟨t, ht, congrArg Subtype.val hty⟩
  rw [heq]
  intro hdvd
  refine hT.2.2 ?_
  change 2 ∣ T.relIndex ⊤
  rw [relIndex_top_right]
  exact hdvd.trans (index_map_dvd _ φ.rangeRestrict_surjective)

theorem pRank_quotient_pCore_le_two_of_models {Q : Type} [Group Q] [Finite Q]
    {T X Y : Subgroup Q} [Y.Normal] (hT : IsSylowTwoOf T ⊤) (hXlt : X < ⊤)
    (hmax : ∀ Y' : Subgroup Q, T ≤ Y' → Y' < ⊤ → Y' ≤ X) (hYT : Y ⊔ T = ⊤)
    (hYp : Group.IsPerfect Y)
    (hE : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
      CFSG.Blueprint.LieModel (↥Y ⧸ CFSG.pCore 2 ↥Y) .PSL 3 2 1 ∨
      CFSG.Blueprint.LieModel (↥Y ⧸ CFSG.pCore 2 ↥Y) .PSU 3 3 1) :
    CFSG.pRank 2 (Q ⧸ CFSG.pCore 2 Q) ≤ 2 ∧
      ¬ CFSG.Blueprint.LieModel (↥Y ⧸ CFSG.pCore 2 ↥Y) .PSU 3 3 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Yb, hYb⟩ : ∃ Yb : Subgroup (Q ⧸ CFSG.pCore 2 Q),
      Y.map (QuotientGroup.mk' (CFSG.pCore 2 Q)) = Yb := ⟨_, rfl⟩
  have hYbn : Yb.Normal := hYb ▸ Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e₀⟩ := nonempty_map_mk_pCore_equiv Y
  have eY : ↥Yb ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y := (MulEquiv.subgroupCongr hYb).symm.trans e₀
  have hperf : Group.IsPerfect ↥Yb := isPerfect_of_surjective
    ((MulEquiv.subgroupCongr hYb).toMonoidHom.comp ((QuotientGroup.mk' _).subgroupMap Y))
    ((MulEquiv.subgroupCongr hYb).surjective.comp ((QuotientGroup.mk' _).subgroupMap_surjective Y))
    hYp
  have h2 : ∀ b : Q ⧸ CFSG.pCore 2 Q, ∃ k : ℕ, b ^ 2 ^ k ∈ Yb := by
    intro b
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 Q) b
    have hq : q ∈ Y ⊔ T := hYT ▸ mem_top q
    obtain ⟨y, hy, t, ht, rfl⟩ := mem_sup_of_normal_left.mp hq
    obtain ⟨k, hk⟩ := hT.2.1 ⟨t, ht⟩
    refine ⟨k, hYb ▸ ⟨(y * t) ^ 2 ^ k, ?_, map_pow _ _ _⟩⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow]
    have ht1 : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [ht1, QuotientGroup.mk_one]
  set φ : Q →* MulAut ↥Yb :=
    (MulAut.conjNormal : (Q ⧸ CFSG.pCore 2 Q) →* MulAut ↥Yb).comp
      (QuotientGroup.mk' (CFSG.pCore 2 Q)) with hφ
  have hInn : (MulAut.conj : ↥Yb →* MulAut ↥Yb).range ≤ φ.range := by
    rintro _ ⟨y, rfl⟩
    have hy : (y : Q ⧸ CFSG.pCore 2 Q) ∈ Y.map (QuotientGroup.mk' (CFSG.pCore 2 Q)) :=
      hYb ▸ y.2
    obtain ⟨q, -, hq⟩ := hy
    refine ⟨q, ?_⟩
    rw [hφ, MonoidHom.comp_apply, hq, MulAut.conjNormal_val]
  have hU : ¬ CFSG.Blueprint.LieModel (↥Y ⧸ CFSG.pCore 2 ↥Y) .PSU 3 3 1 := by
    intro hU
    have hU' := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eY.symm hU
    obtain ⟨D₁, D₂, hP₁, hP₂, hD₁, hD₂, hgen⟩ :=
      Setup.X5.unitary_three_at_three_overgroups_not_minimal hU' hInn
        (isSylowTwoOf_map_range_of_top hT φ)
    have hT₁ : T ≤ D₁.comap φ := fun t ht => hP₁ (mem_map_of_mem φ ht)
    have hT₂ : T ≤ D₂.comap φ := fun t ht => hP₂ (mem_map_of_mem φ ht)
    have hlt : ∀ D : Subgroup (MulAut ↥Yb), D < φ.range → D.comap φ < ⊤ := by
      intro D hD
      refine lt_top_iff_ne_top.mpr fun htop => not_le_of_gt hD ?_
      rintro _ ⟨q, rfl⟩
      have hq : q ∈ D.comap φ := htop ▸ mem_top q
      exact hq
    have hsup : D₁.comap φ ⊔ D₂.comap φ = ⊤ := by
      have hm : (D₁.comap φ ⊔ D₂.comap φ).map φ = (⊤ : Subgroup Q).map φ := by
        rw [Subgroup.map_sup, map_comap_eq, map_comap_eq, inf_eq_right.mpr hD₁.le,
          inf_eq_right.mpr hD₂.le, hgen, MonoidHom.range_eq_map]
      have hc := congrArg (Subgroup.comap φ) hm
      rw [comap_map_eq, comap_map_eq, top_sup_eq] at hc
      rw [← hc]
      exact (sup_eq_left.mpr (le_sup_of_le_left (MonoidHom.ker_le_comap φ D₁))).symm
    exact hXlt.ne (top_le_iff.mp (hsup ▸ sup_le (hmax _ hT₁ (hlt _ hD₁))
      (hmax _ hT₂ (hlt _ hD₂))))
  refine ⟨?_, hU⟩
  have hE' : Nonempty (↥Yb ≃* alternatingGroup (Fin 5)) ∨
      CFSG.Blueprint.LieModel ↥Yb .PSL 3 2 1 := by
    rcases hE with h5 | hL | hU'
    · obtain ⟨e5⟩ := h5
      exact Or.inl ⟨eY.trans e5⟩
    · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eY.symm hL)
    · exact absurd hU' hU
  have hZ : center ↥Yb = ⊥ := by
    rcases hE' with h5 | hL
    · obtain ⟨e5⟩ := h5
      have : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance
      have : IsSimpleGroup ↥Yb := e5.isSimpleGroup
      exact center_eq_bot_of_isSimpleGroup_of_isPerfect hperf
    · obtain ⟨e3⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL
      exact center_eq_bot_of_mulEquiv e3
        (center_eq_bot_of_conj_injective CFSG.LieType.SteinbergBR.AutGL32.conj_injective)
  have hθ := conjNormal_injective_of_two_quotient hZ h2
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hInn' : (MulAut.conj : ↥Yb →* MulAut ↥Yb).range ≤
      (MulAut.conjNormal : (Q ⧸ CFSG.pCore 2 Q) →* MulAut ↥Yb).range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, MulAut.conjNormal_val⟩
  have h1 := (CFSG.LieType.nq_Alt5_and_binary_GL3_full_automorphism_two_rank ↥Yb hE').1 _ hInn'
  refine le_trans ?_ h1.le
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) _
    (MonoidHom.rangeRestrict_injective_iff.mpr hθ)

theorem stmtEscapingSingleTwoRank_holds :
    StmtEscapingSingleTwoRank := by
  intro G _ _ T L M h hTI hW H₀ H hH₀ hTH₀ hTH hHH₀ hHM hmin _ _ hmodels
  classical
  obtain ⟨hT'syl, hTn, hT'X, hXlt, hmax, hns⟩ :=
    minimal_escaping_abstract h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨-, hYT, -, hYp, hYc⟩ := perfectResidual_minimal_structure hT'syl hTn hT'X hXlt hmax hns
  have := hYc
  obtain ⟨e⟩ := nonempty_quotient_pCore_map_equiv H (CFSG.perfectResidual ↥H)
  have hE : Nonempty (↥(CFSG.perfectResidual ↥H) ⧸ CFSG.pCore 2 ↥(CFSG.perfectResidual ↥H) ≃*
        alternatingGroup (Fin 5)) ∨
      CFSG.Blueprint.LieModel (↥(CFSG.perfectResidual ↥H) ⧸
        CFSG.pCore 2 ↥(CFSG.perfectResidual ↥H)) .PSL 3 2 1 ∨
      CFSG.Blueprint.LieModel (↥(CFSG.perfectResidual ↥H) ⧸
        CFSG.pCore 2 ↥(CFSG.perfectResidual ↥H)) .PSU 3 3 1 := by
    rcases hmodels with h5 | hL | hU
    · obtain ⟨e5⟩ := h5
      exact Or.inl ⟨e.trans e5⟩
    · exact Or.inr (Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hL))
    · exact Or.inr (Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hU))
  exact (pRank_quotient_pCore_le_two_of_models hT'syl hXlt hmax hYT hYp hE).1

end CFSG.Quasithin.H13.NQCore

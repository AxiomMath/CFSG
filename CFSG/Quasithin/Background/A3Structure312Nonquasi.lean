module

public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.A3Structure312Embed
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.Quasithin.Background.A3Structure312Transport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace A312

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_oddCore_ne_bot {L : Subgroup G} (h : A36Common ↥L)
    (hnq : ¬ CFSG.IsQuasisimple ↥L) :
    ⁅(CFSG.oddCore ↥L).map L.subtype, L⁆ ≠ ⊥ := by
  intro hbot
  have h1 : ⁅CFSG.oddCore ↥L, (⊤ : Subgroup ↥L)⁆ = ⊥ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [Subgroup.map_bot]
    exact hbot
  obtain ⟨hF, -, -, hderiv, hq⟩ := h
  have h2 : ⁅CFSG.solvableRadical ↥L, CFSG.solvableRadical ↥L⁆ = ⊥ := by
    rw [hderiv, hF, h1]
  have e : ↥L ⧸ ⁅CFSG.solvableRadical ↥L, CFSG.solvableRadical ↥L⁆ ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq h2).trans QuotientGroup.quotientBot
  exact hnq (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)

omit [Finite G] in
theorem exists_isSL2_oddCore {L : Subgroup G} (h : A36Strong L) (hnq : ¬ CFSG.IsQuasisimple ↥L) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L) := by
  obtain ⟨hconcl, hcommon, -⟩ := h
  have hF : CFSG.fittingSubgroup ↥L = CFSG.oddCore ↥L := hcommon.1
  let e : ↥L ⧸ CFSG.fittingSubgroup ↥L ≃* ↥L ⧸ CFSG.oddCore ↥L :=
    QuotientGroup.quotientMulEquivOfEq hF
  rcases hconcl with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
  · exact absurd hc.1 hnq
  · exact absurd hc.1 hnq
  · obtain ⟨p, hp, hp3, -, -, -, ψ, hψs, hψk, -⟩ := h3
    let e1 : ↥L ⧸ CFSG.fittingSubgroup ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
    exact ⟨p, hp, hp3, ⟨e.symm.trans e1⟩⟩
  · obtain ⟨-, -, h5, -⟩ := h4
    exact ⟨5, by norm_num, by norm_num, IsSL2.of_mulEquiv e h5⟩

theorem isSylowTwoOf_lFamily_subgroupOf {T B L : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hL : L ∈ cComp (⊤ : Subgroup G)) (hBL : B ≤ L) (hB : B ∈ lFamily T) :
    IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ ∧ B.subgroupOf L ∈ lFamily ((T ⊓ L).subgroupOf L) := by
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hL) hT
  have hB1 : B ∈ cComp (B ⊔ (T ⊓ L)) :=
    cComp_mem_of_le hB le_sup_left (sup_le_sup_left inf_le_left B)
  refine ⟨?_, ?_⟩
  · rw [isSylowTwoOf_top_iff_map, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    exact hTL
  · have := mem_cComp_subgroupOf (L := L) (sup_le hBL inf_le_right : B ⊔ (T ⊓ L) ≤ L) hB1
    rwa [Subgroup.subgroupOf_sup hBL inf_le_right] at this

omit [Finite G] in
theorem le_normalizer_oddCoreSub (L : Subgroup G) :
    L ≤ Subgroup.normalizer (((CFSG.oddCore ↥L).map L.subtype : Subgroup G) : Set G) := by
  have hOn : (((CFSG.oddCore ↥L).map L.subtype : Subgroup G).subgroupOf L).Normal := by
    rw [A4.subgroupOf_map_subtype']
    exact inferInstance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hOn

omit [Finite G] in
theorem normal_subgroupOf_sup_oddCoreSub {B L : Subgroup G} (hBL : B ≤ L) :
    (((CFSG.oddCore ↥L).map L.subtype : Subgroup G).subgroupOf
      (B ⊔ (CFSG.oddCore ↥L).map L.subtype)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
    (sup_le (hBL.trans (le_normalizer_oddCoreSub L)) Subgroup.le_normalizer)

omit [Finite G] in
noncomputable def quotEquivImage {B L : Subgroup G} (hBL : B ≤ L)
    [hN : (((CFSG.oddCore ↥L).map L.subtype : Subgroup G).subgroupOf
      (B ⊔ (CFSG.oddCore ↥L).map L.subtype)).Normal] :
    (↥(B ⊔ (CFSG.oddCore ↥L).map L.subtype) ⧸
      ((CFSG.oddCore ↥L).map L.subtype).subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype)) ≃*
      ↥((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.oddCore ↥L))) := by
  set O : Subgroup ↥L := CFSG.oddCore ↥L with hO
  set OL : Subgroup G := O.map L.subtype with hOLdef
  have hOLL : OL ≤ L := Subgroup.map_subtype_le _
  have hBOL : B ⊔ OL ≤ L := sup_le hBL hOLL
  have hLnorm : L ≤ Subgroup.normalizer (OL : Set G) := le_normalizer_oddCoreSub L
  let π : ↥L →* ↥L ⧸ O := QuotientGroup.mk' O
  let χ : ↥(B ⊔ OL) →* ↥L ⧸ O := π.comp (Subgroup.inclusion hBOL)
  have hker' : OL.subgroupOf (B ⊔ OL) = χ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    show (x : G) ∈ O.map L.subtype ↔ π (Subgroup.inclusion hBOL x) = 1
    rw [show π (Subgroup.inclusion hBOL x) = QuotientGroup.mk (Subgroup.inclusion hBOL x) from rfl,
      QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = Subgroup.inclusion hBOL x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro h
      exact ⟨_, h, rfl⟩
  have hrange : χ.range = (B.subgroupOf L).map π := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      have hx : (x : G) ∈ (↑(B ⊔ OL) : Set G) := x.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right B OL (hBL.trans hLnorm)] at hx
      obtain ⟨b, hb, o, ho, hbo⟩ := hx
      refine ⟨⟨b, hBL hb⟩, hb, ?_⟩
      show π ⟨b, hBL hb⟩ = π (Subgroup.inclusion hBOL x)
      have h1 : (Subgroup.inclusion hBOL x : ↥L) = ⟨b, hBL hb⟩ * ⟨o, hOLL ho⟩ :=
        Subtype.ext hbo.symm
      rw [h1, map_mul]
      have h2 : π ⟨o, hOLL ho⟩ = 1 := by
        rw [show π ⟨o, hOLL ho⟩ = QuotientGroup.mk ⟨o, hOLL ho⟩ from rfl, QuotientGroup.eq_one_iff]
        obtain ⟨y, hy, hyo⟩ := ho
        have : y = ⟨o, hOLL ⟨y, hy, hyo⟩⟩ := Subtype.ext hyo
        rw [← this]
        exact hy
      rw [h2, mul_one]
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, Subgroup.mem_sup_left hb⟩, rfl⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker').trans
    ((QuotientGroup.quotientKerEquivRange χ).trans (MulEquiv.subgroupCongr hrange))

theorem nonquasi_of_lFamily (hSL2 : A312SL2Fact) {T B L : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hL : L ∈ cComp (⊤ : Subgroup G)) (hBL : B ≤ L) (hB : B ∈ lFamily T)
    (h36 : A36Strong L) (hnq : ¬ CFSG.IsQuasisimple ↥L) : A312Nonquasi B L := by
  have hOL := commutator_oddCore_ne_bot h36.2.1 hnq
  obtain ⟨p, hp, hp3, hpSL⟩ := exists_isSL2_oddCore h36 hnq
  unfold A312Nonquasi
  dsimp only
  by_cases hLB : L = B ⊔ (CFSG.oddCore ↥L).map L.subtype
  · exact Or.inl ⟨hOL, hLB, p, hp, by omega, hpSL⟩
  refine Or.inr ⟨hOL, ?_⟩
  set O : Subgroup ↥L := CFSG.oddCore ↥L with hO
  set OL : Subgroup G := O.map L.subtype with hOLdef
  have hOLL : OL ≤ L := Subgroup.map_subtype_le _
  have hBOL : B ⊔ OL ≤ L := sup_le hBL hOLL
  obtain ⟨hT'Syl, hB2⟩ := isSylowTwoOf_lFamily_subgroupOf hT hL hBL hB
  set T' : Subgroup ↥L := (T ⊓ L).subgroupOf L with hT'
  set B' : Subgroup ↥L := B.subgroupOf L with hB'
  let π : ↥L →* ↥L ⧸ O := QuotientGroup.mk' O
  have hker : Group.IsSolvable ↥(π.ker ⊓ (B' ⊔ T')) := by
    have := oddCore_isSolvable ↥L
    have hk : π.ker = O := QuotientGroup.ker_mk' O
    rw [hk]
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : O ⊓ (B' ⊔ T') ≤ O)) (Subgroup.inclusion_injective _)
  have hB3 : B'.map π ∈ lFamily (T'.map π) := by
    have := map_mem_cComp π hker hB2
    rwa [Subgroup.map_sup] at this
  have hS3 : IsSylowTwoOf (T'.map π) ⊤ :=
    isSylowTwoOf_top_map π (QuotientGroup.mk'_surjective O) hT'Syl
  have hne : B'.map π ≠ ⊤ := by
    intro htop
    apply hLB
    refine le_antisymm (fun l hl => ?_) (sup_le hBL hOLL)
    have h1 : π ⟨l, hl⟩ ∈ B'.map π := by rw [htop]; trivial
    obtain ⟨b, hb, hbl⟩ := h1
    have h2 : b⁻¹ * ⟨l, hl⟩ ∈ O := by
      have := (QuotientGroup.eq (s := O)).mp hbl
      exact this
    have h3 : (b : G)⁻¹ * l ∈ OL := ⟨b⁻¹ * ⟨l, hl⟩, h2, rfl⟩
    have : l = (b : G) * ((b : G)⁻¹ * l) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hb h3
  obtain ⟨hB5, hp5, hp8⟩ := hSL2 p hp hp3 (↥L ⧸ O) hpSL (T'.map π) hS3 (B'.map π) hB3 hne
  refine ⟨⟨p, hp, hp5, hp8, hpSL⟩, ?_⟩
  have hNn := normal_subgroupOf_sup_oddCoreSub hBL
  exact ⟨OL.subgroupOf (B ⊔ OL), hNn, rfl, IsSL2.of_mulEquiv (quotEquivImage hBL).symm hB5⟩

theorem commutator_oddCore_eq_bot_of_quasisimple {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) :
    ⁅(CFSG.oddCore ↥L).map L.subtype, L⁆ = ⊥ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (inferInstance : (CFSG.oddCore ↥L).Normal)
    with htop | hle
  · exfalso
    have hs : Group.IsSolvable ↥(CFSG.oddCore ↥L) := oddCore_isSolvable _
    let e : ↥(CFSG.oddCore ↥L) ≃* ↥L := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have hsL : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    have : Group.IsPerfect ↥L := hq.1
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact Group.IsPerfect.not_isSolvable ↥L hsL
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨o, ho, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    have h1 := Subgroup.mem_center_iff.mp (hle ho) ⟨l, hl⟩
    exact congrArg Subtype.val h1

theorem not_quasisimple_of_nonquasi {B L : Subgroup G} (h : A312Nonquasi B L) :
    ¬ CFSG.IsQuasisimple ↥L := by
  intro hq
  have h0 := commutator_oddCore_eq_bot_of_quasisimple hq
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact h1 h0

end A312

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimQuotient
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofOne
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.Line63.H5

theorem card_range_ggGamma_eq_redMk
    {G : Type} [Group G] [Finite G] {X B J : Subgroup G}
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hJX : J ≤ X)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hJperf : commutator J = ⊤) :
    ∃ hbar : (redMkB hBX).range ≤ Subgroup.normalizer
      (((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X)) : Set (RedGrp X)),
      Nat.card (ggGamma J hBJ).range = Nat.card (ggGamma
        ((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X)) hbar).range := by
  let NX := Subgroup.normalizer (X : Set G)
  let Jbar : Subgroup (RedGrp X) := (J.subgroupOf NX).map (redMk X)
  let Bbar : Subgroup (RedGrp X) := (redMkB hBX).range
  have hJN : J ≤ NX := hJX.trans Subgroup.le_normalizer
  have hBmap : (B.subgroupOf NX).map (redMk X) = Bbar := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨b, hBX b.2⟩, b.2, rfl⟩
  have hbar : Bbar ≤ Subgroup.normalizer (Jbar : Set (RedGrp X)) := by
    rw [← hBmap]
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.map_le_normalizer_map (redMk X) hBJ
  refine ⟨hbar, ?_⟩
  let q₀ : J →* RedGrp X := (redMk X).comp (Subgroup.inclusion hJN)
  have hqrange : q₀.range = Jbar := by
    dsimp [q₀, Jbar]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let q : J →* Jbar := q₀.codRestrict Jbar (fun j => hqrange ▸ ⟨j, rfl⟩)
  have hq : Function.Surjective q := by
    intro j
    obtain ⟨j₀, hj₀⟩ := show ∃ j₀, q₀ j₀ = (j : RedGrp X) from
      MonoidHom.mem_range.mp (hqrange.symm ▸ j.2)
    exact ⟨j₀, Subtype.ext hj₀⟩
  have hqker : q.ker ≤ Subgroup.center J := by
    intro j hj
    have hjq : q₀ j = 1 := by
      simpa only [q, MonoidHom.codRestrict_apply, Subgroup.coe_one] using
        congrArg Subtype.val (MonoidHom.mem_ker.mp hj)
    have htwo : (j : G) ∈ twoCenter X :=
      (redMk_eq_one_iff X (Subgroup.inclusion hJN j)).mp hjq
    rw [Subgroup.mem_center_iff]
    intro j'
    exact Subtype.ext (htwo.2.1 j' (hJX j'.2)).symm
  let α := ggGamma J hBJ
  let β := (ggGamma Jbar hbar).comp (redMkB hBX).rangeRestrict
  have heq : ∀ b j, q (α b j) = β b (q j) := by
    intro b j
    apply Subtype.ext
    change redMk X ⟨(b : G) * (j : G) * (b : G)⁻¹, _⟩ =
      redMk X ⟨b, hBX b.2⟩ * redMk X ⟨j, hJN j.2⟩ *
        (redMk X ⟨b, hBX b.2⟩)⁻¹
    simp only [← map_mul, ← map_inv]
    rfl
  let : Group.IsPerfect J := Group.isPerfect_def.mpr hJperf
  have hc := card_range_eq_of_central_quotient_equivariant q hq hqker α β heq
  have hβrange : β.range = (ggGamma Jbar hbar).range := by
    dsimp [β]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      (redMkB hBX).rangeRestrict_surjective, Subgroup.map_top]
  rw [hβrange] at hc
  exact hc

end CFSG.StandardType

end

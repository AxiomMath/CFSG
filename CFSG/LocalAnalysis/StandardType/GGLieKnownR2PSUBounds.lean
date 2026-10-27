module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLDims
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri

public section

namespace CFSG.StandardType.LieKnownR2.PSU

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

private theorem l10sb_conj_eq_sl {F : Type} [Field F] [Finite F] [CharP F 2]
    (s : GL (Fin 2) F) :
    ∃ s' : Matrix.SpecialLinearGroup (Fin 2) F, ∀ u : Matrix.SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.toGL (s' * u * s'⁻¹) =
        s * Matrix.SpecialLinearGroup.toGL u * s⁻¹ := by
  let δ : Fˣ := Matrix.GeneralLinearGroup.det s
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) ((δ⁻¹ : Fˣ) : F)
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h0 : ((δ⁻¹ : Fˣ) : F) = 0 := by rw [hr, mul_zero]
    exact (Units.ne_zero (δ⁻¹)) h0
  let c : Fˣ := Units.mk0 r hr0
  have hc2 : (c : F) ^ 2 = ((δ⁻¹ : Fˣ) : F) := by
    rw [show (c : F) = r from Units.val_mk0 (a := r) hr0, hr, sq]
  have hcd : δ * c ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
    rw [show (c : F) ^ 2 = ((δ⁻¹ : Fˣ) : F) from hc2]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set a : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) c with ha
  have hca : a ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [ha]
    exact Subgroup.mem_center_iff.mpr fun B =>
      (Matrix.GeneralLinearGroup.scalar_commute (n := Fin 2) c B).symm
  have hconj : ∀ X : GL (Fin 2) F, a * X * a⁻¹ = X := by
    intro X
    rw [← Subgroup.mem_center_iff.mp hca X, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : a * s ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, ha]
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar]
    simp only [Fintype.card_fin]
    rw [mul_comm]
    exact hcd
  obtain ⟨s', hs'⟩ := hmem
  refine ⟨s', fun u => ?_⟩
  rw [map_mul, map_mul, map_inv, hs']
  rw [show a * s * Matrix.SpecialLinearGroup.toGL u * (a * s)⁻¹ =
      a * (s * Matrix.SpecialLinearGroup.toGL u * s⁻¹) * a⁻¹ by
    rw [mul_inv_rev]; group]
  exact hconj _

private theorem l10sb_mem_mul_centralizer {F : Type} [Field F] [Finite F] [CharP F 2]
    {X : Type} [Group X] (φ : Matrix.SpecialLinearGroup (Fin 2) F →* X) {b : X}
    {s : GL (Fin 2) F} (hs : IsGLLift Matrix.SpecialLinearGroup.toGL φ s b) :
    ∃ j ∈ φ.range, ∀ x ∈ φ.range, b⁻¹ * x * b = j * x * j⁻¹ := by
  obtain ⟨s', hs'⟩ := l10sb_conj_eq_sl s
  refine ⟨φ s', ⟨s', rfl⟩, ?_⟩
  intro x hx
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨u', hu'1, hu'2⟩ := hs u
  have hu'eq : u' = s' * u * s'⁻¹ :=
    Matrix.SpecialLinearGroup.toGL_injective (by rw [hu'1, hs' u])
  rw [hu'2, hu'eq]
  simp only [map_mul, map_inv]

private theorem l10sb_card_le {F : Type} [Field F] [Finite F] [CharP F 2]
    {X : Type} [Group X] (φ : Matrix.SpecialLinearGroup (Fin 2) F →* X)
    (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B₁ : Subgroup X}
    (hB₁e : IsElemAbelian p B₁) (hB₁ : B₁ ≤ Subgroup.normalizer (φ.range : Set X))
    (hinn : ∀ b ∈ B₁, ∃ j ∈ φ.range, ∀ x ∈ φ.range, b⁻¹ * x * b = j * x * j⁻¹) :
    Nat.card B₁ ≤ p * Nat.card (B₁ ⊓ Subgroup.centralizer (φ.range : Set X) : Subgroup X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let J : Subgroup X := φ.range
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* J := MonoidHom.ofInjective hφ
  let ψ : B₁ →* MulAut J := (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom J).comp
    (Subgroup.inclusion hB₁)
  have hmap : ψ.ker.map B₁.subtype = B₁ ⊓ Subgroup.centralizer (J : Set X) := by
    ext g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
      have hx1 : ψ x = 1 := MonoidHom.mem_ker.1 hx
      have hxker : Subgroup.inclusion hB₁ x ∈
          (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom J).ker := by
        rw [MonoidHom.mem_ker]
        exact hx1
      rw [CFSG.LocalAnalysis.ComponentInitial.ker_normalizerConjHom J] at hxker
      exact Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_subgroupOf.1 hxker⟩
    · intro hg
      obtain ⟨hgB, hgC⟩ := Subgroup.mem_inf.1 hg
      refine Subgroup.mem_map.2 ⟨⟨g, hgB⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      have h : Subgroup.inclusion hB₁ ⟨g, hgB⟩ ∈
          (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom J).ker := by
        rw [CFSG.LocalAnalysis.ComponentInitial.ker_normalizerConjHom J]
        exact Subgroup.mem_subgroupOf.2 hgC
      exact MonoidHom.mem_ker.1 h
  have hkerCard : Nat.card ψ.ker =
      Nat.card (B₁ ⊓ Subgroup.centralizer (J : Set X) : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective B₁.subtype_injective, hmap]
  have hsplit : Nat.card B₁ = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hcenterSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 F,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_two_eq_bot F]
  have hcenterbot : ∀ g : J, g ∈ Subgroup.center J → g = 1 := by
    intro g hg
    have hmem : e.symm g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (Subgroup.mem_center_iff.mp hg) (e y)
    rw [hcenterSL, Subgroup.mem_bot] at hmem
    rw [← e.apply_symm_apply g, hmem, map_one]
  have hcj : Function.Injective (MulAut.conj : J →* MulAut J) := by
    intro g h hgh
    have h1 : MulAut.conj (g * h⁻¹) = 1 := by
      rw [map_mul, map_inv, hgh, mul_inv_cancel]
    have h2 : g * h⁻¹ ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := congrArg (fun f : MulAut J => f x) h1
      rw [MulAut.conj_apply, MulAut.one_apply] at hx
      have hxa : (g * h⁻¹) * x = x * (g * h⁻¹) := by
        calc (g * h⁻¹) * x
            = (g * h⁻¹) * x * (g * h⁻¹)⁻¹ * (g * h⁻¹) := by group
          _ = x * (g * h⁻¹) := by rw [hx]
      exact hxa.symm
    have h3 : g * h⁻¹ = 1 := hcenterbot _ h2
    calc g = g * h⁻¹ * h := by group
      _ = 1 * h := by rw [h3]
      _ = h := one_mul h
  have hinner : ∀ b : B₁, ψ b ∈ (MulAut.conj : J →* MulAut J).range := by
    intro b
    obtain ⟨j, hj, hconj⟩ := hinn (b : X) b.2
    refine ⟨(⟨j, hj⟩ : J)⁻¹, ?_⟩
    have h1 : (ψ b)⁻¹ = MulAut.conj (⟨j, hj⟩ : J) := by
      rw [← map_inv]
      ext x
      rw [show ψ b⁻¹ = CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom J
          (Subgroup.inclusion hB₁ b⁻¹) from rfl]
      rw [CFSG.LocalAnalysis.ComponentInitial.coe_normalizerConjHom_apply]
      simp only [Subgroup.coe_inclusion, Subgroup.coe_inv, Subgroup.coe_mul, inv_inv,
        MulAut.conj_apply]
      exact hconj x x.2
    rw [map_inv, ← h1, inv_inv]
  have hle : ψ.range ≤ (MulAut.conj : J →* MulAut J).range := by
    rintro y ⟨b, rfl⟩
    exact hinner b
  let f : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut J :=
    (MulAut.conj : J →* MulAut J).comp e.toMonoidHom
  have hf : Function.Injective f := hcj.comp e.injective
  let A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := ψ.range.comap f
  have hr : ψ.range ≤ f.range := by
    refine hle.trans ?_
    rintro y ⟨j, rfl⟩
    obtain ⟨u, hu⟩ := e.surjective j
    refine ⟨u, ?_⟩
    show MulAut.conj (e u) = MulAut.conj j
    rw [hu]
  have hAran : A.map f = ψ.range := by
    rw [Subgroup.map_comap_eq_self hr]
  have hcardA : Nat.card A = Nat.card ψ.range := by
    rw [← Subgroup.card_map_of_injective hf, hAran]
  have hψe : IsElemAbelian p ψ.range := by
    haveI : IsMulCommutative B₁ := hB₁e.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change a.1 * b.1 = b.1 * a.1
      rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm' x y]
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hz
      have hxp : x ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hB₁e.2 (x : X) x.2, Subgroup.coe_one]
      rw [← hx, ← map_pow, hxp, map_one]
  have hAe : IsElemAbelian p A := by
    haveI : IsMulCommutative ψ.range := hψe.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · apply Subtype.ext
      apply hf
      change f (a * b) = f (b * a)
      rw [map_mul, map_mul]
      exact congrArg Subtype.val
        (mul_comm' ⟨f a, show f a ∈ ψ.range from a.2⟩
          ⟨f b, show f b ∈ ψ.range from b.2⟩)
    · apply hf
      change f (z ^ p) = f 1
      rw [map_pow, map_one]
      exact hψe.2 (f z) (show f z ∈ ψ.range from hz)
  have hψrange : Nat.card ψ.range ≤ p := by
    calc Nat.card ψ.range = Nat.card A := hcardA.symm
      _ ≤ p := CFSG.StandardType.TableBExcSmallRest.card_le_of_isElemAbelian_sl2 hp hp2 hAe
  rw [hsplit, hkerCard]
  exact Nat.mul_le_mul_right _ hψrange

theorem jDim_dualPair_psu {f k : ℕ} {X : Type} [Group X]
    (φ : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 (2 * f)) →* X)
    (hker : φ.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 (2 * f))))
    (hns : ¬ Group.IsSolvable ↥φ.range) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B₁ D : Subgroup X} (hB₁e : IsElemAbelian p B₁)
    (hB₁ : B₁ ≤ Subgroup.normalizer (φ.range : Set X))
    (hBD : B₁ ⊓ Subgroup.centralizer (φ.range : Set X) = D)
    (hcard : p ^ 4 ≤ Nat.card B₁) (hD : Nat.card D = p ^ 2)
    (hlift : ∀ b ∈ B₁, ∃ s : GL (Fin (k + 1)) (GaloisField 2 (2 * f)),
      IsGLLift Matrix.SpecialLinearGroup.toGL φ s b) :
    2 ≤ k := by
  by_contra hk
  push Not at hk
  have hk1 : 1 ≤ k := PSL.one_le_of_not_isSolvable_psl φ hns
  have hk_eq : k = 1 := by omega
  subst hk_eq
  simp only [Nat.reduceAdd] at hker
  have hcenter : Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * f))) = ⊥ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2
        (GaloisField 2 (2 * f)),
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_two_eq_bot]
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hφ : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hkerbot
  have hinn : ∀ b ∈ B₁, ∃ j ∈ φ.range, ∀ x ∈ φ.range, b⁻¹ * x * b = j * x * j⁻¹ := by
    intro b hb
    obtain ⟨s, hs⟩ := hlift b hb
    exact l10sb_mem_mul_centralizer φ hs
  have hle := l10sb_card_le φ hφ hp hp2 hB₁e hB₁ hinn
  rw [hBD, hD] at hle
  have hp4 : p ^ 4 ≤ p ^ 3 := by
    calc p ^ 4 ≤ Nat.card B₁ := hcard
      _ ≤ p * p ^ 2 := hle
      _ = p ^ 3 := by ring
  have hple1 : p ≤ 1 := by
    refine Nat.le_of_mul_le_mul_left ?_ (pow_pos hp.pos 3)
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ p ^ 3 := hp4
      _ = p ^ 3 * 1 := by ring
  have := hp.two_le
  omega

theorem ggRootPosG0_dualPair_psu
    {X : Type} [Group X] {n f p : ℕ} (ψ : (ggU .PSU n f).K →* X) {R Rm : Subgroup X}
    (hp : p ∣ 2 ^ f - 1)
    (h : ∃ β : Fin (ggU .PSU n f).D.rank → ℤ, β ∈ (ggU .PSU n f).D.roots ∧
      2 • β ∉ (ggU .PSU n f).D.roots ∧ ∃ u : (ggU .PSU n f).K,
        R = ggRootSub (ggU .PSU n f).D ψ β u ∧ Rm = ggRootSub (ggU .PSU n f).D ψ (-β) u) :
    GGRootPosG0 .PSU n f p ψ R Rm := by
  obtain ⟨β, hβ, h2β, u, hRu, hRmu⟩ := h
  refine ⟨β, hβ, Or.inr ⟨?_, h2β⟩, u, hRu, hRmu⟩
  exact Or.inr (Or.inr ⟨Or.inl rfl, hp⟩)

end CFSG.StandardType.LieKnownR2.PSU

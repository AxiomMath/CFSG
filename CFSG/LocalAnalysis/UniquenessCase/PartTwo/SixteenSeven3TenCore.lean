module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3TenGL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3TenInvert
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_card_le_four_of_ten (hsq : ∀ w : W, w * w = 1) (hcard : Nat.card W ≤ 2 ^ 12)
    {M T : Subgroup (MulAut W)} (hTn : ∀ g ∈ M, ∀ t ∈ T, g * t * g⁻¹ ∈ T)
    (hTc : ∀ x ∈ M, (∀ t ∈ T, x * t = t * x) → x ∈ T) (hT : IsElemAbelianOfRank 7 3 ↥T)
    {X : Subgroup (MulAut W)} (hXM : X ≤ M) (hX : IsElemAbelian2 X) : Nat.card X ≤ 4 := by
  classical
  have hsqX : ∀ x : ↥X, (x : MulAut W) * (x : MulAut W) = 1 := fun x => by
    have h2 := hX.2 (x : MulAut W) x.2
    rwa [pow_two] at h2
  let ρ : ↥X →* MulAut ↥T :=
    { toFun := fun x =>
        { toFun := fun t => ⟨(x : MulAut W) * t * (x : MulAut W)⁻¹, hTn _ (hXM x.2) t t.2⟩
          invFun := fun t => ⟨(x : MulAut W)⁻¹ * t * (x : MulAut W), by
            have h := hTn _ (hXM (X.inv_mem x.2)) t t.2
            simpa using h⟩
          left_inv := fun t => Subtype.ext (by
            show (x : MulAut W)⁻¹ * ((x : MulAut W) * t * (x : MulAut W)⁻¹) * (x : MulAut W) = t
            group)
          right_inv := fun t => Subtype.ext (by
            show (x : MulAut W) * ((x : MulAut W)⁻¹ * t * (x : MulAut W)) * (x : MulAut W)⁻¹ = t
            group)
          map_mul' := fun a b => Subtype.ext (by
            show (x : MulAut W) * ((a : MulAut W) * b) * (x : MulAut W)⁻¹ =
              (x : MulAut W) * a * (x : MulAut W)⁻¹ * ((x : MulAut W) * b * (x : MulAut W)⁻¹)
            group) }
      map_one' := MulEquiv.ext fun t => Subtype.ext (by
        show ((1 : ↥X) : MulAut W) * t * ((1 : ↥X) : MulAut W)⁻¹ = t
        simp)
      map_mul' := fun x y => MulEquiv.ext fun t => Subtype.ext (by
        show ((x * y : ↥X) : MulAut W) * t * ((x * y : ↥X) : MulAut W)⁻¹ =
          (x : MulAut W) * ((y : MulAut W) * t * (y : MulAut W)⁻¹) * (x : MulAut W)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  have hρ : ∀ (x : ↥X) (t : ↥T),
      ((ρ x t : ↥T) : MulAut W) = (x : MulAut W) * t * (x : MulAut W)⁻¹ := fun _ _ => rfl
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hcomm : ∀ t ∈ T, (x : MulAut W) * t = t * (x : MulAut W) := by
      intro t ht
      have h1 := congrArg (fun φ : MulAut ↥T => ((φ ⟨t, ht⟩ : ↥T) : MulAut W)) hx
      have h2 : (x : MulAut W) * t * (x : MulAut W)⁻¹ = t := h1
      calc (x : MulAut W) * t = ((x : MulAut W) * t * (x : MulAut W)⁻¹) * (x : MulAut W) := by
            group
        _ = t * (x : MulAut W) := by rw [h2]
    have hxT : (x : MulAut W) ∈ T := hTc _ (hXM x.2) hcomm
    have h7 : (x : MulAut W) ^ 7 = 1 :=
      congrArg Subtype.val (s16c167_pow_seven_of_isElemAbelianOfRank hT ⟨(x : MulAut W), hxT⟩)
    apply Subtype.ext
    calc (x : MulAut W) = (x : MulAut W) ^ 7 * (((x : MulAut W) ^ 2) ^ 3)⁻¹ := by group
      _ = 1 := by rw [h7, pow_two, hsqX x]; simp
  have hrsq : ∀ y ∈ ρ.range, y * y = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hsqX x), map_one]
  have hcardX : Nat.card ↥ρ.range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  obtain ⟨h8, hinv8⟩ := s16c167_elem_two_in_aut hT hrsq
  rw [hcardX] at h8 hinv8
  have hne8 : Nat.card X ≠ 8 := by
    intro h
    obtain ⟨y, ⟨x, rfl⟩, hy⟩ := hinv8 h
    have hxinv : ∀ t ∈ T, (x : MulAut W) * t * (x : MulAut W)⁻¹ = t⁻¹ := by
      intro t ht
      have h1 := congrArg Subtype.val (hy ⟨t, ht⟩)
      rw [hρ] at h1
      exact h1
    exact s16c167_no_inversion hsq hcard hT (hsqX x) hxinv
  have hp : IsPGroup 2 ↥X := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hX.2 (x : MulAut W) x.2
  rw [card_eq_two_pow_of_isPGroup hp] at h8 hne8 ⊢
  have hk : rk ↥X ≤ 2 := by
    by_contra hk
    have h3 : 2 ^ 3 ≤ 2 ^ rk ↥X := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 2 ^ rk ↥X ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk
    _ = 4 := by norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

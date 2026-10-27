module

public import CFSG.LargeExtraspecial.S111SJRee
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoVacFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

theorem exists_eq_conj_of_sylow_eight {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hT : ∀ T : Sylow 2 X, Nat.card (T : Subgroup X) = 8 ∧ IsMulCommutative (T : Subgroup X) ∧
      ∀ t ∈ (T : Subgroup X), t * t = 1)
    {a : MulAut X} (ha : a * a = 1) : ∃ x : X, a = MulAut.conj x := by
  classical
  have : Finite (MulAut X) := Finite.of_injective (fun f : MulAut X => (f : X → X))
    DFunLike.coe_injective
  have hcenter : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab ((mem_center_iff.mp (h ▸ mem_top a : a ∈ center X)) b).symm
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have : g ∈ center X := mem_center_iff.mpr fun y => by
      have := congrArg (fun σ : MulAut X => σ y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = (g * y * g⁻¹) * g := by rw [this]
        _ = g * y := by group
    rw [hcenter, mem_bot] at this
    exact this
  obtain ⟨P, hP⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoVacFix.exists_stable_sylow a ha
  obtain ⟨hP8, hPc, hPsq⟩ := hT P
  have hfix : ∀ x ∈ (P : Subgroup X), a x = x :=
    CFSG.LargeExtraspecial.S11.apply_eq_self_of_sylow_eight hnonab P hPc hP8 hPsq ha hP
  by_contra hno
  push Not at hno
  have ha1 : a ≠ 1 := fun h => hno 1 (by simp [h])
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hcomm : ∀ (p : (P : Subgroup X)) (z : zpowers a),
      Commute ((MulAut.conj.comp (P : Subgroup X).subtype) p) ((zpowers a).subtype z) := by
    rintro p ⟨z, hz⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
    have h1 : Commute (MulAut.conj (p : X)) a := by
      have h2 : a * MulAut.conj (p : X) * a⁻¹ = MulAut.conj (a p) := by
        ext x
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
      rw [hfix p p.2] at h2
      show MulAut.conj (p : X) * a = a * MulAut.conj (p : X)
      calc MulAut.conj (p : X) * a = (a * MulAut.conj (p : X) * a⁻¹) * a := by rw [h2]
        _ = a * MulAut.conj (p : X) := by group
    exact h1.zpow_right n
  let φ : ↥(P : Subgroup X) × ↥(zpowers a) →* MulAut X :=
    MonoidHom.noncommCoprod (MulAut.conj.comp (P : Subgroup X).subtype) (zpowers a).subtype hcomm
  have hφ : ∀ (p : (P : Subgroup X)) (z : zpowers a),
      φ (p, z) = MulAut.conj (p : X) * (z : MulAut X) := fun _ _ => rfl
  have hz : ∀ z : zpowers a, (z : MulAut X) = 1 ∨ (z : MulAut X) = a := fun z =>
    CFSG.Walter.eq_one_or_eq_of_mem_zpowers hao z.2
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨p, z⟩ h
    rw [hφ] at h
    rcases hz z with h1 | h1
    · rw [h1, mul_one] at h
      have hp : p = 1 := Subtype.ext (hinj (by simp [h]))
      have hz1 : z = 1 := Subtype.ext h1
      rw [hp, hz1, Prod.mk_one_one]
    · exfalso
      apply hno (p : X)⁻¹
      rw [map_inv, ← h1]
      exact eq_inv_of_mul_eq_one_right h
  have hA : ∀ b ∈ φ.range, b * b = 1 := by
    rintro _ ⟨⟨p, z⟩, rfl⟩
    rw [← map_mul]
    have hsq : ((p, z) * (p, z) : ↥(P : Subgroup X) × ↥(zpowers a)) = 1 := by
      refine Prod.ext (Subtype.ext (hPsq p p.2)) (Subtype.ext ?_)
      show (z : MulAut X) * z = 1
      rcases hz z with h1 | h1
      · rw [h1, mul_one]
      · rw [h1, ha]
    rw [hsq, map_one]
  have h8 := CFSG.LargeExtraspecial.S11.card_le_eight_of_sylow_eight hnonab hT φ.range hA
  rw [Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm, Nat.card_prod, hP8,
    Nat.card_zpowers, hao] at h8
  omega

theorem mem_of_mul_self_eq_one_of_sylow_eight {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    [K.Normal] [IsSimpleGroup K] (hC : centralizer (K : Set Y) = ⊥)
    (hnonab : ∃ a b : K, a * b ≠ b * a)
    (hT : ∀ T : Sylow 2 K, Nat.card (T : Subgroup K) = 8 ∧ IsMulCommutative (T : Subgroup K) ∧
      ∀ t ∈ (T : Subgroup K), t * t = 1)
    {v : Y} (hv : v * v = 1) : v ∈ K := by
  have ha : MulAut.conjNormal v * MulAut.conjNormal v = (1 : MulAut K) := by
    rw [← map_mul, hv, map_one]
  obtain ⟨k, hk⟩ := exists_eq_conj_of_sylow_eight hnonab hT ha
  have hmem : (k : Y)⁻¹ * v ∈ centralizer (K : Set Y) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun σ : MulAut K => ((σ ⟨x, hx⟩ : K) : Y)) hk
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h1
    calc x * ((k : Y)⁻¹ * v) = (k : Y)⁻¹ * ((k : Y) * x * (k : Y)⁻¹) * v := by group
      _ = (k : Y)⁻¹ * (v * x * v⁻¹) * v := by rw [h1]
      _ = (k : Y)⁻¹ * v * x := by group
  rw [hC, mem_bot] at hmem
  have hvk : v = k := by
    calc v = k * ((k : Y)⁻¹ * v) := by group
      _ = k := by rw [hmem, mul_one]
  rw [hvk]
  exact k.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

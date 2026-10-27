module

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.CGT.T75N.PpdCyclic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderNilpotent
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem22

theorem comm_mem_of_inv_mod {K : Type*} [Group K] {O R : Subgroup K} [O.Normal]
    (hR2 : IsPGroup 2 ↥R) {v x r₀ : K} (hx3 : x ^ 3 = 1) (hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R)
    (hv : ∀ r ∈ R, v * r * v⁻¹ * r⁻¹ ∈ O) (hr₀ : r₀ ∈ R) (hvx : v * x * v⁻¹ = x⁻¹ * r₀) :
    ∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ O := by
  set φ := QuotientGroup.mk' O with hφ
  have hφ1 : ∀ y : K, φ y = 1 ↔ y ∈ O := fun y => by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hvφ : ∀ r ∈ R, φ (v * r * v⁻¹) = φ r := by
    intro r hr
    have h1 := (hφ1 _).mpr (hv r hr)
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hstep1 : ∀ r ∈ R, φ (x * x * r * (x * x)⁻¹) = φ (r₀ * r * r₀⁻¹) := by
    intro r hr
    have h1 := hvφ _ (hxR r hr)
    have e : v * (x * r * x⁻¹) * v⁻¹ = (v * x * v⁻¹) * (v * r * v⁻¹) * (v * x * v⁻¹)⁻¹ := by group
    rw [e, hvx, map_mul, map_mul, map_inv, hvφ r hr] at h1
    have e2 : x * x * r * (x * x)⁻¹ = x * (x * r * x⁻¹) * x⁻¹ := by group
    rw [e2, map_mul, map_mul, map_inv, ← h1]
    simp only [map_mul, map_inv]
    group
  have hstep2 : ∀ r ∈ R, φ (x * r * x⁻¹) = φ (r₀ * r₀) * φ r * (φ (r₀ * r₀))⁻¹ := by
    intro r hr
    have hr' : x * x * r * (x * x)⁻¹ ∈ R := by
      have e : x * x * r * (x * x)⁻¹ = x * (x * r * x⁻¹) * x⁻¹ := by group
      rw [e]
      exact hxR _ (hxR r hr)
    have h1 := hstep1 _ hr'
    have e : x * x * (x * x * r * (x * x)⁻¹) * (x * x)⁻¹ = x * r * x⁻¹ := by
      have hx4 : x * x * x * x = x := by
        calc x * x * x * x = x ^ 3 * x := by rw [pow_three]; group
          _ = x := by rw [hx3, one_mul]
      calc x * x * (x * x * r * (x * x)⁻¹) * (x * x)⁻¹
          = (x * x * x * x) * r * (x * x * x * x)⁻¹ := by group
        _ = x * r * x⁻¹ := by rw [hx4]
    rw [e] at h1
    rw [h1, map_mul, map_mul, map_inv, hstep1 r hr]
    simp only [map_mul, map_inv]
    group
  set c := φ (r₀ * r₀) with hc
  have hc3 : ∀ r ∈ R, c ^ 3 * φ r = φ r * c ^ 3 := by
    intro r hr
    have h1 := hstep2 _ (hxR _ (hxR r hr))
    rw [hstep2 _ (hxR r hr), hstep2 r hr] at h1
    have e : x * (x * (x * r * x⁻¹) * x⁻¹) * x⁻¹ = r := by
      calc x * (x * (x * r * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * r * (x ^ 3)⁻¹ := by
            rw [pow_three]; group
        _ = r := by rw [hx3]; group
    rw [e] at h1
    have h2 : φ r = c ^ 3 * φ r * (c ^ 3)⁻¹ := by
      refine h1.trans ?_
      rw [pow_three]
      group
    calc c ^ 3 * φ r = c ^ 3 * φ r * (c ^ 3)⁻¹ * c ^ 3 := by group
      _ = φ r * c ^ 3 := by rw [← h2]
  obtain ⟨j, hj⟩ := hR2 ⟨r₀, hr₀⟩
  have hj' : r₀ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcj : c ^ 2 ^ j = 1 := by
    rw [hc, ← map_pow, ← pow_two, ← pow_mul, mul_comm, pow_mul, hj', one_pow, map_one]
  have hcop : Nat.Coprime 3 (orderOf c) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hcj)
      (Nat.Coprime.pow_right _ (by norm_num))
  obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hcop
  have hcc : ∀ r ∈ R, c * φ r = φ r * c := by
    intro r hr
    rw [← ha]
    exact ((Commute.pow_left (hc3 r hr) a))
  intro r hr
  rw [← hφ1, map_mul, map_inv, hstep2 r hr, hcc r hr]
  group

theorem eq_one_of_fix_of_norm {G : Type*} [Group G] {W : Subgroup G} {S : Set G} {z : G}
    (hWS : W = Subgroup.closure S) (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hzW : ∀ w ∈ W, z * w * z⁻¹ ∈ W)
    (hS : ∀ s ∈ S, s * (z * s * z⁻¹) * (z * z * s * (z * z)⁻¹) = 1) :
    ∀ w ∈ W, z * w * z⁻¹ = w → w = 1 := by
  have hz2W : ∀ w ∈ W, z * z * w * (z * z)⁻¹ ∈ W := fun w hw => by
    have e : z * z * w * (z * z)⁻¹ = z * (z * w * z⁻¹) * z⁻¹ := by group
    rw [e]
    exact hzW _ (hzW w hw)
  have hN : ∀ w ∈ W, w * (z * w * z⁻¹) * (z * z * w * (z * z)⁻¹) = 1 := by
    intro w hw
    have hSW : S ⊆ W := by rw [hWS]; exact Subgroup.subset_closure
    rw [hWS] at hw
    induction hw using Subgroup.closure_induction with
    | mem s hs => exact hS s hs
    | one => group
    | mul a b ha hb iha ihb =>
      rw [← hWS] at ha hb
      have h1 := hzW a ha
      have h2 := hzW b hb
      have h3 := hz2W a ha
      have h4 := hz2W b hb
      have e : a * b * (z * (a * b) * z⁻¹) * (z * z * (a * b) * (z * z)⁻¹) =
          a * b * ((z * a * z⁻¹) * (z * b * z⁻¹)) *
            ((z * z * a * (z * z)⁻¹) * (z * z * b * (z * z)⁻¹)) := by group
      rw [e]
      have c1 : b * (z * a * z⁻¹) = (z * a * z⁻¹) * b := hWc _ hb _ h1
      have c2 : (z * b * z⁻¹) * (z * z * a * (z * z)⁻¹) =
          (z * z * a * (z * z)⁻¹) * (z * b * z⁻¹) := hWc _ h2 _ h3
      have c3 : b * (z * z * a * (z * z)⁻¹) = (z * z * a * (z * z)⁻¹) * b := hWc _ hb _ h3
      calc a * b * ((z * a * z⁻¹) * (z * b * z⁻¹)) *
            ((z * z * a * (z * z)⁻¹) * (z * z * b * (z * z)⁻¹))
          = a * (b * (z * a * z⁻¹)) * (z * b * z⁻¹) * (z * z * a * (z * z)⁻¹) *
              (z * z * b * (z * z)⁻¹) := by group
        _ = a * ((z * a * z⁻¹) * b) * (z * b * z⁻¹) * (z * z * a * (z * z)⁻¹) *
              (z * z * b * (z * z)⁻¹) := by rw [c1]
        _ = a * (z * a * z⁻¹) * b * ((z * b * z⁻¹) * (z * z * a * (z * z)⁻¹)) *
              (z * z * b * (z * z)⁻¹) := by group
        _ = a * (z * a * z⁻¹) * b * ((z * z * a * (z * z)⁻¹) * (z * b * z⁻¹)) *
              (z * z * b * (z * z)⁻¹) := by rw [c2]
        _ = a * (z * a * z⁻¹) * (b * (z * z * a * (z * z)⁻¹)) * (z * b * z⁻¹) *
              (z * z * b * (z * z)⁻¹) := by group
        _ = a * (z * a * z⁻¹) * ((z * z * a * (z * z)⁻¹) * b) * (z * b * z⁻¹) *
              (z * z * b * (z * z)⁻¹) := by rw [c3]
        _ = (a * (z * a * z⁻¹) * (z * z * a * (z * z)⁻¹)) *
              (b * (z * b * z⁻¹) * (z * z * b * (z * z)⁻¹)) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a ha iha =>
      rw [← hWS] at ha
      have h1 := hzW a ha
      have h3 := hz2W a ha
      have hn : a * (z * a * z⁻¹) * (z * z * a * (z * z)⁻¹) = 1 := iha
      have c1 : a * (z * a * z⁻¹) = (z * a * z⁻¹) * a := hWc _ ha _ h1
      have c2 : a * (z * z * a * (z * z)⁻¹) = (z * z * a * (z * z)⁻¹) * a := hWc _ ha _ h3
      have c3 : (z * a * z⁻¹) * (z * z * a * (z * z)⁻¹) =
          (z * z * a * (z * z)⁻¹) * (z * a * z⁻¹) := hWc _ h1 _ h3
      have e : a⁻¹ * (z * a⁻¹ * z⁻¹) * (z * z * a⁻¹ * (z * z)⁻¹) =
          ((z * z * a * (z * z)⁻¹) * (z * a * z⁻¹) * a)⁻¹ := by group
      rw [e]
      have e2 : (z * z * a * (z * z)⁻¹) * (z * a * z⁻¹) * a =
          a * (z * a * z⁻¹) * (z * z * a * (z * z)⁻¹) := by
        calc (z * z * a * (z * z)⁻¹) * (z * a * z⁻¹) * a
            = (z * z * a * (z * z)⁻¹) * ((z * a * z⁻¹) * a) := by group
          _ = (z * z * a * (z * z)⁻¹) * (a * (z * a * z⁻¹)) := by rw [c1]
          _ = ((z * z * a * (z * z)⁻¹) * a) * (z * a * z⁻¹) := by group
          _ = (a * (z * z * a * (z * z)⁻¹)) * (z * a * z⁻¹) := by rw [c2]
          _ = a * ((z * z * a * (z * z)⁻¹) * (z * a * z⁻¹)) := by group
          _ = a * ((z * a * z⁻¹) * (z * z * a * (z * z)⁻¹)) := by rw [c3]
          _ = a * (z * a * z⁻¹) * (z * z * a * (z * z)⁻¹) := by group
      rw [e2, hn, inv_one]
  intro w hw hzw
  have h1 := hN w hw
  have hz2 : z * z * w * (z * z)⁻¹ = w := by
    calc z * z * w * (z * z)⁻¹ = z * (z * w * z⁻¹) * z⁻¹ := by group
      _ = w := by rw [hzw, hzw]
  rw [hzw, hz2] at h1
  have h2 := hW2 w hw
  calc w = w * (w * w) := by rw [← pow_two, h2, mul_one]
    _ = w * w * w := by group
    _ = 1 := h1

end Lem22

end CFSG.Quasithin.H13

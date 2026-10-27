module

public import CFSG.RankThree.PartOne.N1322.ExtraspecialAbs
public import CFSG.RankThree.PartOne.N1322.CaseConj
public import CFSG.RankThree.PartOne.N1322.CasePair

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory

@[expose] def Cz {p : ℕ} (z : GL (Fin 3) (ZMod p)) : Prop :=
  ∀ g : GL (Fin 3) (ZMod p), g * z = z * g

theorem Cz.one {p : ℕ} : Cz (1 : GL (Fin 3) (ZMod p)) := fun g => by simp

theorem Cz.mul {p : ℕ} {z w : GL (Fin 3) (ZMod p)} (hz : Cz z) (hw : Cz w) : Cz (z * w) := by
  intro g
  rw [← mul_assoc, hz g, mul_assoc, hw g, mul_assoc]

theorem Cz.inv {p : ℕ} {z : GL (Fin 3) (ZMod p)} (hz : Cz z) : Cz z⁻¹ := by
  intro g
  calc g * z⁻¹ = z⁻¹ * (z * g) * z⁻¹ := by group
    _ = z⁻¹ * (g * z) * z⁻¹ := by rw [hz g]
    _ = z⁻¹ * g := by group

theorem trv_mul {p : ℕ} {H : Subgroup (GL (Fin 3) (ZMod p))} {g h : GL (Fin 3) (ZMod p)}
    (hg : ∀ a ∈ H, Cz (g * a * g⁻¹ * a⁻¹)) (hh : ∀ a ∈ H, Cz (h * a * h⁻¹ * a⁻¹)) :
    ∀ a ∈ H, Cz ((g * h) * a * (g * h)⁻¹ * a⁻¹) := by
  intro a ha
  have hζg := hg a ha
  have hζh := hh a ha
  have e : (g * h) * a * (g * h)⁻¹ * a⁻¹ = (h * a * h⁻¹ * a⁻¹) * (g * a * g⁻¹ * a⁻¹) := by
    calc (g * h) * a * (g * h)⁻¹ * a⁻¹ = g * (h * a * h⁻¹) * g⁻¹ * a⁻¹ := by group
      _ = g * ((h * a * h⁻¹ * a⁻¹) * a) * g⁻¹ * a⁻¹ := by group
      _ = (g * (h * a * h⁻¹ * a⁻¹)) * a * g⁻¹ * a⁻¹ := by group
      _ = ((h * a * h⁻¹ * a⁻¹) * g) * a * g⁻¹ * a⁻¹ := by rw [hζh g]
      _ = (h * a * h⁻¹ * a⁻¹) * (g * a * g⁻¹ * a⁻¹) := by group
  rw [e]
  exact Cz.mul hζh hζg

theorem trv_pow {p : ℕ} {H : Subgroup (GL (Fin 3) (ZMod p))} {g : GL (Fin 3) (ZMod p)}
    (hg : ∀ a ∈ H, Cz (g * a * g⁻¹ * a⁻¹)) (k : ℕ) :
    ∀ a ∈ H, Cz (g ^ k * a * (g ^ k)⁻¹ * a⁻¹) := by
  induction k with
  | zero => intro a ha; simpa using Cz.one
  | succ k ih =>
    rw [pow_succ]
    exact trv_mul ih hg

theorem trv_of_neg {p : ℕ} {H : Subgroup (GL (Fin 3) (ZMod p))} {t s : GL (Fin 3) (ZMod p)}
    (ht : ∀ a ∈ H, Cz (t * a * t⁻¹ * a)) (hs : ∀ a ∈ H, Cz (s * a * s⁻¹ * a)) :
    ∀ a ∈ H, Cz ((t * s) * a * (t * s)⁻¹ * a⁻¹) := by
  intro a ha
  have hζ₁ := hs a ha
  have hζ₂ := ht a ha
  obtain ⟨ζ₁, hζ₁d⟩ : ∃ z, z = s * a * s⁻¹ * a := ⟨_, rfl⟩
  obtain ⟨ζ₂, hζ₂d⟩ : ∃ z, z = t * a * t⁻¹ * a := ⟨_, rfl⟩
  rw [← hζ₁d] at hζ₁
  rw [← hζ₂d] at hζ₂
  have e1 : s * a * s⁻¹ = ζ₁ * a⁻¹ := by rw [hζ₁d]; group
  have e2 : t * a * t⁻¹ = ζ₂ * a⁻¹ := by rw [hζ₂d]; group
  have e : (t * s) * a * (t * s)⁻¹ * a⁻¹ = ζ₁ * ζ₂⁻¹ := by
    calc (t * s) * a * (t * s)⁻¹ * a⁻¹ = t * (s * a * s⁻¹) * t⁻¹ * a⁻¹ := by group
      _ = t * (ζ₁ * a⁻¹) * t⁻¹ * a⁻¹ := by rw [e1]
      _ = (t * ζ₁) * a⁻¹ * t⁻¹ * a⁻¹ := by group
      _ = (ζ₁ * t) * a⁻¹ * t⁻¹ * a⁻¹ := by rw [hζ₁ t]
      _ = ζ₁ * (t * a * t⁻¹)⁻¹ * a⁻¹ := by group
      _ = ζ₁ * (ζ₂ * a⁻¹)⁻¹ * a⁻¹ := by rw [e2]
      _ = ζ₁ * (a * ζ₂⁻¹) * a⁻¹ := by group
      _ = ζ₁ * (ζ₂⁻¹ * a) * a⁻¹ := by rw [(Cz.inv hζ₂) a]
      _ = ζ₁ * ζ₂⁻¹ := by group
  rw [e]
  exact Cz.mul hζ₁ (Cz.inv hζ₂)

theorem case7_false {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (h : CoreHyp d)
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hnorm : ∀ g ∈ d.X, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hirr : IsIrreducibleMatrixRep H.subtype)
    (hcard : Nat.card H = 27) (hext : CFSG.IsExtraspecialPGroup 3 H) : False := by
  have h2 := two_ne_zero_of_five_le h.p5
  have hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := ext27_noncomm hcard hext
    exact ⟨a, a.2, b, b.2, fun hc => hab (Subtype.ext hc)⟩
  have hsch := scalar_commutant_of_noncomm hirr hnc
  have hcenGL : ∀ z : H, z ∈ Subgroup.center H → Cz (z : GL (Fin 3) (ZMod p)) := by
    intro z hz g
    exact central_of_center hsch (fun x hx => by
      simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)) g
  have hdich : ∀ u ∈ d.X, u * u = 1 →
      (∀ a ∈ H, Cz (u * a * u⁻¹ * a⁻¹)) ∨ (∀ a ∈ H, Cz (u * a * u⁻¹ * a)) := by
    intro u hu hu2
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    obtain ⟨φ, hφ⟩ : ∃ φ : H ≃* H, ∀ x : H, ((φ x : H) : GL (Fin 3) (ZMod p)) = u * x * u⁻¹ :=
      ⟨actOn hnorm hu, fun x => rfl⟩
    have hφz : ∀ z ∈ Subgroup.center H, φ z = z := by
      intro z hz
      apply Subtype.ext
      rw [hφ, hcenGL z hz u]
      group
    have hφ2 : ∀ x, φ (φ x) = x := by
      intro x
      apply Subtype.ext
      rw [hφ, hφ, huinv]
      calc u * (u * (x : GL (Fin 3) (ZMod p)) * u) * u
          = (u * u) * (x : GL (Fin 3) (ZMod p)) * (u * u) := by group
        _ = x := by rw [hu2]; group
    rcases ext27_pm hcard hext φ hφz hφ2 with h1 | h1
    · left
      intro a ha
      have := hcenGL _ (h1 ⟨a, ha⟩)
      simpa [hφ] using this
    · right
      intro a ha
      have := hcenGL _ (h1 ⟨a, ha⟩)
      simpa [hφ] using this
  have htriv : ∀ u ∈ d.Lm, u * u = 1 → (∀ a ∈ H, Cz (u * a * u⁻¹ * a⁻¹)) → u = 1 := by
    intro u huL hu2 htr
    have huX : u ∈ d.X := h.Lle huL
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    refine lm_central_eq_one h hsch huL (fun x hx => ?_)
    have hζ := htr x hx
    obtain ⟨ζ, hζdef⟩ : ∃ z, z = u * x * u⁻¹ * x⁻¹ := ⟨_, rfl⟩
    rw [← hζdef] at hζ
    have hζH : ζ ∈ H := by
      rw [hζdef]
      exact H.mul_mem (hnorm u huX x hx) (H.inv_mem hx)
    have hux : u * x * u⁻¹ = ζ * x := by rw [hζdef]; group
    have e0 : u * (u * x * u⁻¹) * u⁻¹ = x := by
      rw [huinv]
      calc u * (u * x * u) * u = (u * u) * x * (u * u) := by group
        _ = x := by rw [hu2]; group
    have hζ2 : ζ * ζ = 1 := by
      have e1 : ζ * (ζ * x) = x := by
        calc ζ * (ζ * x) = ζ * (u * x * u⁻¹) := by rw [hux]
          _ = (ζ * u) * x * u⁻¹ := by group
          _ = (u * ζ) * x * u⁻¹ := by rw [← hζ u]
          _ = u * (ζ * x) * u⁻¹ := by group
          _ = u * (u * x * u⁻¹) * u⁻¹ := by rw [hux]
          _ = x := e0
      have e2 : ζ * ζ * x = x := by rw [mul_assoc]; exact e1
      exact mul_right_cancel (by rw [one_mul]; exact e2)
    have hζmem : (⟨ζ, hζH⟩ : H) ∈ Subgroup.center H :=
      Subgroup.mem_center_iff.mpr (fun y => Subtype.ext (hζ y))
    have hζ3 : ζ ^ 3 = 1 := by
      simpa using congrArg Subtype.val (ext27_center_cube hext _ hζmem)
    have hζ1 : ζ = 1 := by
      calc ζ = ζ * (ζ * ζ) := by rw [hζ2, mul_one]
        _ = ζ ^ 3 := (pow_three ζ).symm
        _ = 1 := hζ3
    have hxu : u * x * u⁻¹ = x := by rw [hux, hζ1, one_mul]
    exact (mul_inv_eq_iff_eq_mul.mp hxu).symm
  obtain ⟨ρ, t₀, hg, ht₀D, hs₀D⟩ := exists_refl_pair h
  have ht₀X := mem_X_of_mem_D h ht₀D
  have hs₀X := mem_X_of_mem_D h hs₀D
  have ht₀2 : (t₀ : GL (Fin 3) (ZMod p)) * t₀ = 1 := (h.refl _ ht₀D).sq
  have hs₀2 : ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) = 1 :=
    (h.refl _ hs₀D).sq
  have hne1 : ∀ t : GL (Fin 3) (ZMod p), IsRefl t → t ≠ 1 := by
    intro t ht h1
    have h3 := ht.det_eq
    rw [h1] at h3
    simp at h3
    apply h2
    linear_combination h3
  have hneg₀ : ∀ a ∈ H, Cz ((t₀ : GL (Fin 3) (ZMod p)) * a * (t₀ : GL (Fin 3) (ZMod p))⁻¹ * a) := by
    rcases hdich _ ht₀X ht₀2 with htr | hng
    · exact absurd (htriv _ t₀.2 ht₀2 htr) (hne1 _ (h.refl _ ht₀D))
    · exact hng
  have hneg₁ : ∀ a ∈ H, Cz (((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) * a *
      ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p))⁻¹ * a) := by
    rcases hdich _ hs₀X hs₀2 with htr | hng
    · exact absurd (htriv _ (t₀ * ρ).2 hs₀2 htr) (hne1 _ (h.refl _ hs₀D))
    · exact hng
  have hprod : (t₀ : GL (Fin 3) (ZMod p)) * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) =
      (ρ : GL (Fin 3) (ZMod p)) := by
    have := congrArg Subtype.val (show t₀ * (t₀ * ρ) = ρ by rw [← mul_assoc, hg.sq, one_mul])
    simpa using this
  have hρtriv : ∀ a ∈ H, Cz ((ρ : GL (Fin 3) (ZMod p)) * a * (ρ : GL (Fin 3) (ZMod p))⁻¹ * a⁻¹) := by
    have := trv_of_neg hneg₀ hneg₁
    rwa [hprod] at this
  obtain ⟨k, hk⟩ := hg.ev
  have hρk := trv_pow hρtriv k
  have hρord : (ρ : GL (Fin 3) (ZMod p)) ^ d.n = 1 := by
    have := pow_orderOf_eq_one (ρ : GL (Fin 3) (ZMod p))
    rwa [Subgroup.orderOf_coe, hg.ord] at this
  have hρk2 : (ρ : GL (Fin 3) (ZMod p)) ^ k * (ρ : GL (Fin 3) (ZMod p)) ^ k = 1 := by
    rw [← pow_add, ← hk]
    exact hρord
  have hρk1 : (ρ : GL (Fin 3) (ZMod p)) ^ k = 1 :=
    htriv _ (d.Lm.pow_mem ρ.2 k) hρk2 hρk
  have hdvd : d.n ∣ k := by
    have := orderOf_dvd_of_pow_eq_one hρk1
    rwa [Subgroup.orderOf_coe, hg.ord] at this
  have h4 := hg.four
  have hkpos : 0 < k := by omega
  have := Nat.le_of_dvd hkpos hdvd
  omega

end CFSG.RankThree.PartOne.N1322

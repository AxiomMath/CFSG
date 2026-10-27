module

public import CFSG.Timmesfeld.Exceptional.CaseSplit
public import CFSG.Timmesfeld.Exceptional.CaseTwo

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def ExcCollinearComm (D : Set G) : Prop :=
  ∀ y ∈ D, ∀ x₁ ∈ D, ∀ x₂ ∈ D, Commute y x₁ → y * x₁ ∈ D → Commute y x₂ →
    orderOf (x₁ * x₂) = 4 → (x₁ * x₂) ^ 2 = y

@[expose] def ExcCollinearCommInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → (∀ d ∈ D, rootSet D d = {d}) →
    (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
    NoLevi D → ExcCollinearComm D

private theorem conj_eq_of_sq_eq {a b c : G} (ha : a * a = 1) (h : (a * b) ^ 2 = c) :
    b * a * b = a * c := by
  rw [← h, pow_two]
  calc b * a * b = a * a * (b * a * b) := by rw [ha, one_mul]
    _ = a * (a * b * (a * b)) := by group

theorem noPlane_of_collinearComm [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hNL : NoLevi D)
    (hC : ExcCollinearComm D) : ExcNoPlane D := by
  intro d hd x hx z hz hdx hdz hxz hne _ _ _ hdxD hdzD hxzD hdxzD
  have hd2 : d * d = 1 := hD.mul_self_eq_one hd
  have hx2 : x * x = 1 := hD.mul_self_eq_one hx
  have hxdD : x * d ∈ D := hdx.eq ▸ hdxD
  obtain ⟨f, hf, hdf, hxf⟩ := exists_commute_not_commute hclass hsing hd hx hdx (Ne.symm hne)
  have hf2 : f * f = 1 := hD.mul_self_eq_one hf
  have hfinv : f⁻¹ = f := hD.inv_eq hf
  have hfx : f * x * f = x * d :=
    conj_eq_of_sq_eq hx2
      (hC d hd x hx f hf hdx hdxD hdf (hNL.orderOf_eq_four hD hd hx hf hdx hdf hxf))
  obtain ⟨g, hg, hxg, hdg⟩ := exists_commute_not_commute hclass hsing hx hd hdx.symm hne
  have hg2 : g * g = 1 := hD.mul_self_eq_one hg
  have hginv : g⁻¹ = g := hD.inv_eq hg
  have hgd : g * d * g = d * x := conj_eq_of_sq_eq hd2
    (hC x hx d hd g hg hdx.symm hxdD hxg (hNL.orderOf_eq_four hD hx hd hg hdx.symm hxg hdg))
  have hfd : f * d * f = d := by rw [← hdf.eq, mul_assoc, hf2, mul_one]
  have hgx : g * x * g = x := by rw [← hxg.eq, mul_assoc, hg2, mul_one]
  have hinv : (f * g)⁻¹ = g * f := by rw [mul_inv_rev, hfinv, hginv]
  have hconj : ∀ a : G, (f * g) * a * (f * g)⁻¹ = f * (g * a * g) * f := fun a => by
    rw [hinv]; group
  have hfpush : ∀ a b : G, f * (a * b) * f = (f * a * f) * (f * b * f) := fun a b => by
    calc f * (a * b) * f = f * a * (f * f) * b * f := by rw [hf2]; group
      _ = (f * a * f) * (f * b * f) := by group
  have hgpush : ∀ a b : G, g * (a * b) * g = (g * a * g) * (g * b * g) := fun a b => by
    calc g * (a * b) * g = g * a * (g * g) * b * g := by rw [hg2]; group
      _ = (g * a * g) * (g * b * g) := by group
  have h1 : (f * g) * d * (f * g)⁻¹ = x := by
    rw [hconj, hgd, hfpush, hfd, hfx, ← mul_assoc, hdx.eq, mul_assoc, hd2, mul_one]
  have h2 : (f * g) * x * (f * g)⁻¹ = d * x := by
    rw [hconj, hgx, hfx, hdx.eq]
  have h3 : (f * g) * (d * x) * (f * g)⁻¹ = d := by
    rw [hconj, hgpush, hgd, hgx, mul_assoc d x x, hx2, mul_one, hfd]
  have hx1 : x ≠ 1 := hD.ne_one hx
  have hdx1 : d * x ≠ d := fun h => hx1 (by simpa using h)
  have hxd1 : x ≠ d := Ne.symm hne
  set u := f * g with hu
  have hne2 : u * u ≠ 1 := by
    intro h
    have e : (u * u) * d * (u * u)⁻¹ = u * (u * d * u⁻¹) * u⁻¹ := by group
    rw [h, one_mul, inv_one, mul_one, h1, h2] at e
    exact hdx1 e.symm
  have hne4 : u * u * u * u ≠ 1 := by
    intro h
    have e : (u * u * u * u) * d * (u * u * u * u)⁻¹ =
        u * (u * (u * (u * d * u⁻¹) * u⁻¹) * u⁻¹) * u⁻¹ := by group
    rw [h, one_mul, inv_one, mul_one, h1, h2, h3, h1] at e
    exact hxd1 e.symm
  have hne1 : u ≠ 1 := fun h => hne2 (by rw [h, one_mul])
  have hodd : Odd (orderOf u) := by
    rcases hD.orderOf_mul hf hg with h | h | h
    · exact absurd (by rw [← pow_two, ← h, pow_orderOf_eq_one]) hne2
    · exact absurd (by
        rw [show u * u * u * u = u ^ 4 by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, mul_assoc], ← h,
          pow_orderOf_eq_one]) hne4
    · exact h
  have hfg : ¬ Commute f g := fun h => hne2 (by
    have h' := (commute_iff_mul_sq_eq_one hf2 hg2).1 h
    rwa [pow_two] at h')
  have hcomm : ∀ a b : G, b * b = 1 → b * a * b = a → Commute a b := fun a b hb2 h => by
    show a * b = b * a
    calc a * b = b * a * b * b := by rw [h]
      _ = b * a := by rw [mul_assoc, hb2, mul_one]
  have hzf : Commute z f ∨ f * (x * z) * f = x * z := by
    by_cases h : Commute z f
    · exact .inl h
    · right
      have hfz : f * z * f = z * d :=
        conj_eq_of_sq_eq (hD.mul_self_eq_one hz)
          (hC d hd z hz f hf hdz hdzD hdf (hNL.orderOf_eq_four hD hd hz hf hdz hdf h))
      have hdzd : d * z * d = z := by rw [hdz.eq, mul_assoc, hd2, mul_one]
      rw [hfpush, hfx, hfz, show x * d * (z * d) = x * (d * z * d) by group, hdzd]
  have hzg : Commute z g ∨ g * (d * z) * g = d * z := by
    by_cases h : Commute z g
    · exact .inl h
    · right
      have hgz : g * z * g = z * x :=
        conj_eq_of_sq_eq (hD.mul_self_eq_one hz)
          (hC x hx z hz g hg hxz hxzD hxg (hNL.orderOf_eq_four hD hx hz hg hxz hxg h))
      have hxzx : x * z * x = z := by rw [hxz.eq, mul_assoc, hx2, mul_one]
      rw [hgpush, hgd, hgz, show d * x * (z * x) = d * (x * z * x) by group, hxzx]
  have hfixf : ∀ a : G, Commute a f → f * a * f = a := fun a h => by
    rw [← h.eq, mul_assoc, hf2, mul_one]
  have hfixg : ∀ a : G, Commute a g → g * a * g = a := fun a h => by
    rw [← h.eq, mul_assoc, hg2, mul_one]
  have hlevi : ∀ e ∈ D, f * e * f = e → g * e * g = e → False := fun e he h1 h2 =>
    hNL f hf g hg hfg hodd e he (hcomm e f hf2 h1) (hcomm e g hg2 h2)
  rcases hzf with hzf | hzf <;> rcases hzg with hzg | hzg
  · exact hlevi z hz (hfixf z hzf) (hfixg z hzg)
  · exact hlevi (d * z) hdzD (by rw [hfpush, hfd, hfixf z hzf]) hzg
  · exact hlevi (x * z) hxzD hzf (by rw [hgpush, hgx, hfixg z hzg])
  · refine hlevi (d * x * z) hdxzD ?_ ?_
    · rw [show d * x * z = d * (x * z) by group, hfpush, hfd, hzf]
    · rw [show d * x * z = d * z * x by rw [mul_assoc, hxz.eq, ← mul_assoc], hgpush, hzg, hgx]

theorem exceptionalNoLeviPlaneStep_of_collinearComm (h : ExcCollinearCommInput) :
    ExceptionalNoLeviPlaneStep := by
  intro G _ D hH IH hsing hex hNL
  have := hH.finite
  exact noPlane_of_collinearComm hH.isClass hH.root hsing hNL (h G D hH IH hsing hex hNL)

end CFSG.Timmesfeld.Moufang

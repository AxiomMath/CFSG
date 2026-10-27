module

public import CFSG.RankThree.PartOne.A6N.Setup
public import CFSG.RankThree.PartOne.A6N.Trace
public import CFSG.RankThree.PartOne.A6N.Finite
public import CFSG.RankThree.PartOne.N1322.CoreHyp
public import CFSG.RankThree.PartOne.N1322.Mono
public import Mathlib.Algebra.Algebra.Subalgebra.Rank

public section

namespace CFSG.RankThree.PartOne.A6N

open CFSG.RankThree.PartOne.N1322 CFSG.RepresentationTheory Equiv Matrix

namespace Val

variable {p : ℕ} [Fact p.Prime] (V : Val p)

local notation "G3" => GL (Fin 3) (ZMod p)

omit V in
theorem trace_conj (g U : G3) :
    ((g * U * g⁻¹ : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)).trace =
      ((U : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem trace_cases {u s : V.H} (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1) (hsu : s * u * s⁻¹ = u⁻¹)
    {g : G3} {k : ℕ} (hk : g * (u : G3) * g⁻¹ = (u : G3) ^ k) :
    g * (u : G3) * g⁻¹ = (u : G3) ∨ g * (u : G3) * g⁻¹ = (u : G3)⁻¹ := by
  have := V.perf
  set U : G3 := (u : G3) with hU
  have hU5 : U ^ 5 = 1 := by simpa using congrArg Subtype.val hu5
  have hU1 : U ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hdet : (U : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := det_eq_one_of_perfect u.2
  have hsU : (s : G3) * U * (s : G3)⁻¹ = U⁻¹ := by
    simpa using congrArg Subtype.val hsu
  have htr_inv : ((U⁻¹ : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)).trace =
      (U : Matrix (Fin 3) (Fin 3) (ZMod p)).trace := by
    rw [← hsU]
    exact trace_conj _ U
  have hsq : (((U ^ 2 : G3)) : Matrix (Fin 3) (Fin 3) (ZMod p)).trace ≠
      (U : Matrix (Fin 3) (Fin 3) (ZMod p)).trace := by
    have := tr_sq_ne V.five_ne_zero hdet (by rw [← Units.val_pow_eq_pow_val, hU5]; rfl)
      (fun h => hU1 (Units.ext h)) (by rw [← Matrix.coe_units_inv]; exact htr_inv)
    rwa [← Units.val_pow_eq_pow_val] at this
  have hk' : g * U * g⁻¹ = U ^ (k % 5) := by rw [hk]; exact pow_eq_pow_mod k hU5
  have htr_g : (((U ^ (k % 5) : G3)) : Matrix (Fin 3) (Fin 3) (ZMod p)).trace =
      (U : Matrix (Fin 3) (Fin 3) (ZMod p)).trace := by
    rw [← hk']
    exact trace_conj g U
  have hk5 : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases hm : k % 5
  · exfalso
    apply hU1
    have h1 : g * U * g⁻¹ = 1 := by rw [hk']; rfl
    have h2 : U = g⁻¹ * (g * U * g⁻¹) * g := by group
    rw [h2, h1]
    group
  · left
    simpa using hk'
  · exfalso
    exact hsq (by simpa using htr_g)
  · exfalso
    have h3 : U ^ 3 = (s : G3) * U ^ 2 * (s : G3)⁻¹ := by
      rw [show (s : G3) * U ^ 2 * (s : G3)⁻¹ = ((s : G3) * U * (s : G3)⁻¹) ^ 2 by
        rw [conj_pow], hsU]
      have h5 : U ^ 3 * U ^ 2 = 1 := by rw [← pow_add]; exact hU5
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_left h5
    apply hsq
    rw [← trace_conj (s : G3) (U ^ 2), ← h3]
    exact htr_g
  · right
    have h5 : U ^ 4 * U = 1 := by rw [← pow_succ]; exact hU5
    rw [hk']
    exact eq_inv_of_mul_eq_one_left h5

omit V in
theorem a₀A_ne_one : a₀A ≠ 1 := fun h => a₀_ne_one (congrArg Subtype.val h)

omit V in
theorem comm_of_conj {g U : G3} (h : g * U * g⁻¹ = U) : g * U = U * g :=
  calc g * U = (g * U * g⁻¹) * g := by group
    _ = U * g := by rw [h]

theorem exists_fix_u {u s : V.H} (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1) (hsu : s * u * s⁻¹ = u⁻¹)
    {g : G3} (hg : ∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H) :
    ∃ h : V.H, ((h : G3) * g) * (u : G3) = (u : G3) * ((h : G3) * g) := by
  obtain ⟨h₁, k, hk⟩ := V.frattini5 hu5 hu1 hg
  have hsU : (s : G3) * (u : G3) * (s : G3)⁻¹ = (u : G3)⁻¹ := by
    simpa using congrArg Subtype.val hsu
  rcases V.trace_cases hu5 hu1 hsu hk with h | h
  · exact ⟨h₁, comm_of_conj h⟩
  · refine ⟨s * h₁, ?_⟩
    have h2 : (s : G3) * (((h₁ : G3) * g) * (u : G3) * ((h₁ : G3) * g)⁻¹) * (s : G3)⁻¹ =
        (u : G3) := by
      rw [h, show (s : G3) * (u : G3)⁻¹ * (s : G3)⁻¹ = ((s : G3) * (u : G3) * (s : G3)⁻¹)⁻¹ by
        group, hsU, inv_inv]
    have h3 : ((s * h₁ : V.H) : G3) * g = (s : G3) * ((h₁ : G3) * g) := by
      rw [Subgroup.coe_mul, mul_assoc]
    rw [h3]
    refine comm_of_conj ?_
    calc (s : G3) * ((h₁ : G3) * g) * (u : G3) * ((s : G3) * ((h₁ : G3) * g))⁻¹
        = (s : G3) * (((h₁ : G3) * g) * (u : G3) * ((h₁ : G3) * g)⁻¹) * (s : G3)⁻¹ := by group
      _ = (u : G3) := h2

section WithCertificate


theorem exists_fix_s {u s : V.H} (hu5 : u ^ 5 = 1) (hEu : V.E u = a₀A) (hs2 : s * s = 1)
    (hEs : V.E s = s₀A) (hsu : s * u * s⁻¹ = u⁻¹) {g : G3}
    (hg : ∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H) (hgu : g * (u : G3) = (u : G3) * g) :
    ∃ h : V.H, ((h : G3) * g) * (u : G3) = (u : G3) * ((h : G3) * g) ∧
      ((h : G3) * g) * (s : G3) = (s : G3) * ((h : G3) * g) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  let s' : V.H := ⟨g * (s : G3) * g⁻¹, hg s s.2⟩
  have hs'2 : s' * s' = 1 := by
    apply Subtype.ext
    show g * (s : G3) * g⁻¹ * (g * (s : G3) * g⁻¹) = 1
    have : (s : G3) * (s : G3) = 1 := by simpa using congrArg Subtype.val hs2
    calc g * (s : G3) * g⁻¹ * (g * (s : G3) * g⁻¹) = g * ((s : G3) * (s : G3)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hguinv : g⁻¹ * (u : G3) * g = (u : G3) := by
    calc g⁻¹ * (u : G3) * g = g⁻¹ * ((u : G3) * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * (u : G3)) := by rw [hgu]
      _ = (u : G3) := by group
  have hgconj : g * (u : G3) * g⁻¹ = (u : G3) := by rw [hgu]; group
  have hs'u : s' * u * s'⁻¹ = u⁻¹ := by
    apply Subtype.ext
    have hsU : (s : G3) * (u : G3) * (s : G3)⁻¹ = (u : G3)⁻¹ := by
      simpa using congrArg Subtype.val hsu
    show g * (s : G3) * g⁻¹ * (u : G3) * (g * (s : G3) * g⁻¹)⁻¹ = (u : G3)⁻¹
    calc g * (s : G3) * g⁻¹ * (u : G3) * (g * (s : G3) * g⁻¹)⁻¹
        = g * ((s : G3) * (g⁻¹ * (u : G3) * g) * (s : G3)⁻¹) * g⁻¹ := by group
      _ = (u : G3)⁻¹ := by
        rw [hguinv, hsU]
        calc g * (u : G3)⁻¹ * g⁻¹ = (g * (u : G3) * g⁻¹)⁻¹ := by group
          _ = (u : G3)⁻¹ := by rw [hgconj]
  have hc : (s⁻¹ * s') * u = u * (s⁻¹ * s') := by
    have e1 : s' * u = u⁻¹ * s' := by
      calc s' * u = (s' * u * s'⁻¹) * s' := by group
        _ = u⁻¹ * s' := by rw [hs'u]
    have e2 : s * u = u⁻¹ * s := by
      calc s * u = (s * u * s⁻¹) * s := by group
        _ = u⁻¹ * s := by rw [hsu]
    have e3 : s⁻¹ * u⁻¹ = u * s⁻¹ := by
      calc s⁻¹ * u⁻¹ = s⁻¹ * (u⁻¹ * s) * s⁻¹ := by group
        _ = s⁻¹ * (s * u) * s⁻¹ := by rw [e2]
        _ = u * s⁻¹ := by group
    calc (s⁻¹ * s') * u = s⁻¹ * (s' * u) := by rw [mul_assoc]
      _ = s⁻¹ * (u⁻¹ * s') := by rw [e1]
      _ = (s⁻¹ * u⁻¹) * s' := by rw [mul_assoc]
      _ = (u * s⁻¹) * s' := by rw [e3]
      _ = u * (s⁻¹ * s') := by rw [mul_assoc]
  have hcomm : V.E (s⁻¹ * s') * a₀A = a₀A * V.E (s⁻¹ * s') := by
    rw [← hEu, ← map_mul, ← map_mul, hc]
  obtain ⟨i, hi⟩ := centralizer_a₀ hcomm
  have hsus : ∀ n : ℕ, s * u ^ n * s = (u⁻¹) ^ n := by
    intro n
    have h := conj_pow (a := s) (b := u) (i := n)
    rw [hsu, hsinv] at h
    exact h.symm
  have hs'eq : s' = s * u ^ i := by
    refine V.eq_of_E_eq (n := 2) (by norm_num) ?_ ?_ ?_
    · rw [pow_two]; exact hs'2
    · calc (s * u ^ i) ^ 2 = (s * u ^ i * s) * u ^ i := by
            simp only [pow_two, mul_assoc]
        _ = 1 := by rw [hsus, inv_pow, inv_mul_cancel]
    · calc V.E s' = V.E (s * (s⁻¹ * s')) := by rw [mul_inv_cancel_left]
        _ = s₀A * a₀A ^ i := by rw [map_mul, hEs, hi]
        _ = V.E (s * u ^ i) := by rw [map_mul, map_pow, hEs, hEu]
  have ha2 : (u ^ (3 * i)) ^ 2 = u ^ i := by
    rw [← pow_mul, show 3 * i * 2 = 5 * i + i by ring, pow_add, pow_mul, hu5, one_pow, one_mul]
  have hz : (u⁻¹) ^ (3 * i) * u ^ i * (u ^ (3 * i))⁻¹ = 1 := by
    rw [inv_pow, ← ha2]
    group
  have hkey : u ^ (3 * i) * (s * u ^ i) * (u ^ (3 * i))⁻¹ = s := by
    have hus : u ^ (3 * i) * s = s * (u⁻¹) ^ (3 * i) := by
      have h := hsus (3 * i)
      calc u ^ (3 * i) * s = (s * s) * u ^ (3 * i) * s := by rw [hs2, one_mul]
        _ = s * (s * u ^ (3 * i) * s) := by simp only [mul_assoc]
        _ = s * (u⁻¹) ^ (3 * i) := by rw [h]
    calc u ^ (3 * i) * (s * u ^ i) * (u ^ (3 * i))⁻¹
        = (u ^ (3 * i) * s) * u ^ i * (u ^ (3 * i))⁻¹ := by simp only [mul_assoc]
      _ = s * ((u⁻¹) ^ (3 * i) * u ^ i * (u ^ (3 * i))⁻¹) := by
          rw [hus]; simp only [mul_assoc]
      _ = s := by rw [hz, mul_one]
  have hkey' : ((u : G3) ^ (3 * i)) * ((g * (s : G3) * g⁻¹)) * ((u : G3) ^ (3 * i))⁻¹ =
      (s : G3) := by
    have h1 : g * (s : G3) * g⁻¹ = ((s * u ^ i : V.H) : G3) := congrArg Subtype.val hs'eq
    rw [h1]
    simpa using congrArg Subtype.val hkey
  refine ⟨u ^ (3 * i), ?_, ?_⟩
  · have hP : ((u ^ (3 * i) : V.H) : G3) = (u : G3) ^ (3 * i) := by simp
    have hPU : (u : G3) ^ (3 * i) * (u : G3) = (u : G3) * (u : G3) ^ (3 * i) :=
      ((Commute.refl (u : G3)).pow_left (3 * i)).eq
    rw [hP]
    calc (u : G3) ^ (3 * i) * g * (u : G3) = (u : G3) ^ (3 * i) * (g * (u : G3)) := by
          rw [mul_assoc]
      _ = (u : G3) ^ (3 * i) * ((u : G3) * g) := by rw [hgu]
      _ = ((u : G3) ^ (3 * i) * (u : G3)) * g := by rw [mul_assoc]
      _ = ((u : G3) * (u : G3) ^ (3 * i)) * g := by rw [hPU]
      _ = (u : G3) * ((u : G3) ^ (3 * i) * g) := by rw [mul_assoc]
  · have hP : ((u ^ (3 * i) : V.H) : G3) = (u : G3) ^ (3 * i) := by simp
    rw [hP]
    refine comm_of_conj ?_
    calc (u : G3) ^ (3 * i) * g * (s : G3) * ((u : G3) ^ (3 * i) * g)⁻¹
        = ((u : G3) ^ (3 * i)) * ((g * (s : G3) * g⁻¹)) * ((u : G3) ^ (3 * i))⁻¹ := by group
      _ = (s : G3) := hkey'

theorem sq_scalar {u s : V.H} (hEu : V.E u = a₀A) (hEs : V.E s = s₀A) {g : G3}
    (hg : ∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H) (hgu : g * (u : G3) = (u : G3) * g)
    (hgs : g * (s : G3) = (s : G3) * g) :
    ∃ c : ZMod p, ((g * g : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) = Matrix.scalar (Fin 3) c := by
  obtain ⟨ψ, hψ⟩ := V.exists_induced (V.conjAut hg)
  have hαu : V.conjAut hg u = u := by
    apply Subtype.ext
    rw [coe_conjAut]
    calc g * (u : G3) * g⁻¹ = ((u : G3) * g) * g⁻¹ := by rw [hgu]
      _ = (u : G3) := by group
  have hαs : V.conjAut hg s = s := by
    apply Subtype.ext
    rw [coe_conjAut]
    calc g * (s : G3) * g⁻¹ = ((s : G3) * g) * g⁻¹ := by rw [hgs]
      _ = (s : G3) := by group
  have ha : ψ a₀A = a₀A := by rw [← hEu, ← hψ, hαu]
  have hs : ψ s₀A = s₀A := by rw [← hEs, ← hψ, hαs]
  have hα2 := V.aut_sq_eq_one (V.conjAut hg) ψ hψ (aut_sq ψ ha hs)
  refine scalar_commutant_of_noncomm V.irr V.exists_noncomm _ fun h hh => ?_
  have h1 : g * (g * (h : G3) * g⁻¹) * g⁻¹ = (h : G3) := by
    have := congrArg Subtype.val (hα2 ⟨h, hh⟩)
    simpa [coe_conjAut] using this
  have h2 : (g * g) * (h : G3) = (h : G3) * (g * g) :=
    calc (g * g) * (h : G3) = (g * (g * (h : G3) * g⁻¹) * g⁻¹) * (g * g) := by group
      _ = (h : G3) * (g * g) := by rw [h1]
  have h3 := congrArg (fun w : G3 => (w : Matrix (Fin 3) (Fin 3) (ZMod p))) h2
  simpa using h3.symm

theorem reduce {u s : V.H} (hu5 : u ^ 5 = 1) (hEu : V.E u = a₀A) (hs2 : s * s = 1)
    (hEs : V.E s = s₀A) (hsu : s * u * s⁻¹ = u⁻¹) {g : G3} (hg : ∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H) :
    ∃ h : V.H, ((h : G3) * g) * (u : G3) = (u : G3) * ((h : G3) * g) ∧
      ((h : G3) * g) * (s : G3) = (s : G3) * ((h : G3) * g) ∧
      ∃ c : ZMod p, ((((h : G3) * g) * ((h : G3) * g) : G3) :
        Matrix (Fin 3) (Fin 3) (ZMod p)) = Matrix.scalar (Fin 3) c := by
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, map_one] at hEu
    exact a₀A_ne_one hEu.symm
  have hnorm : ∀ (h : V.H) {g : G3}, (∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H) →
      ∀ x ∈ V.H, ((h : G3) * g) * x * ((h : G3) * g)⁻¹ ∈ V.H := by
    intro h g hg x hx
    have e : ((h : G3) * g) * x * ((h : G3) * g)⁻¹ = (h : G3) * (g * x * g⁻¹) * (h : G3)⁻¹ := by
      group
    rw [e]
    exact V.H.mul_mem (V.H.mul_mem h.2 (hg x hx)) (V.H.inv_mem h.2)
  obtain ⟨h₂, hh₂⟩ := V.exists_fix_u hu5 hu1 hsu hg
  have hg₂ := hnorm h₂ hg
  obtain ⟨h₃, hu₃, hs₃⟩ := V.exists_fix_s hu5 hEu hs2 hEs hsu hg₂ hh₂
  have hg₃ := hnorm h₃ hg₂
  have hcoe : ((h₃ * h₂ : V.H) : G3) * g = (h₃ : G3) * ((h₂ : G3) * g) := by
    rw [Subgroup.coe_mul, mul_assoc]
  refine ⟨h₃ * h₂, ?_, ?_, ?_⟩
  · rw [hcoe]; exact hu₃
  · rw [hcoe]; exact hs₃
  · rw [hcoe]; exact V.sq_scalar hEu hEs hg₃ hu₃ hs₃

end WithCertificate

end Val

end CFSG.RankThree.PartOne.A6N

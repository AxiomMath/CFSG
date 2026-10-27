module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

namespace S153E59

theorem comm_end_sl2_table : ∀ A : SL(2, ZMod 2), A ≠ 1 → A ^ 3 = 1 →
    ∀ a b : Fin 2 → ZMod 2,
      (∀ u : Fin 2 → ZMod 2, (fun v : Fin 2 → ZMod 2 => v 0 • a + v 1 • b) (A • u) =
        A • (fun v : Fin 2 → ZMod 2 => v 0 • a + v 1 • b) u) →
      (fun v : Fin 2 → ZMod 2 => v 0 • a + v 1 • b) = 0 ∨
      (fun v : Fin 2 → ZMod 2 => v 0 • a + v 1 • b) = id ∨
      (fun v : Fin 2 → ZMod 2 => v 0 • a + v 1 • b) = (fun u => A • u) ∨
      (fun v : Fin 2 → ZMod 2 => v 0 • a + v 1 • b) = (fun u => A • (A • u)) := by
  decide +kernel

theorem additive_eq_table (g : (Fin 2 → ZMod 2) → (Fin 2 → ZMod 2))
    (h : ∀ u v, g (u + v) = g u + g v) :
    g = fun v : Fin 2 → ZMod 2 => v 0 • g (Pi.single 0 1) + v 1 • g (Pi.single 1 1) := by
  have h0 : g 0 = 0 := by
    have := h 0 0
    simpa using this
  have hsc : ∀ (c : ZMod 2) (e : Fin 2 → ZMod 2), g (c • e) = c • g e := by
    intro c e
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simp [h0]
    · simp
  funext v
  have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → ZMod 2) + v 1 • (Pi.single 1 1 : Fin 2 → ZMod 2) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [h, hsc, hsc]

theorem sl2_fpf : ∀ B : SL(2, ZMod 2), B ≠ 1 → B ^ 3 = 1 → ∀ w : Fin 2 → ZMod 2, B • w = w → w = 0 := by
  decide +kernel

theorem smul_iterate (A : SL(2, ZMod 2)) (n : ℕ) (u : Fin 2 → ZMod 2) :
    ((fun v : Fin 2 → ZMod 2 => A • v)^[n]) u = A ^ n • u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, ← mul_smul, ← pow_succ]

theorem eq_id_of_iterate {A : SL(2, ZMod 2)} (hA1 : A ≠ 1) (hA3 : A ^ 3 = 1)
    (g : (Fin 2 → ZMod 2) → (Fin 2 → ZMod 2)) (hadd : ∀ u v, g (u + v) = g u + g v)
    (hcomm : ∀ u, g (A • u) = A • g u) {m : ℕ} (hg : ∀ u, g^[2 ^ m] u = u) : g = id := by
  have htab := additive_eq_table g hadd
  have hcomm' : ∀ u : Fin 2 → ZMod 2,
      (fun v : Fin 2 → ZMod 2 => v 0 • g (Pi.single 0 1) + v 1 • g (Pi.single 1 1)) (A • u) =
        A • (fun v : Fin 2 → ZMod 2 => v 0 • g (Pi.single 0 1) + v 1 • g (Pi.single 1 1)) u := by
    intro u
    rw [← htab]
    exact hcomm u
  have hu0 : (Pi.single 0 1 : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hfix : ∀ B : SL(2, ZMod 2), B ^ 3 = 1 → B • (Pi.single 0 1 : Fin 2 → ZMod 2) =
      (Pi.single 0 1 : Fin 2 → ZMod 2) → B = 1 := by
    intro B hB3 hBu
    by_contra hB1
    exact hu0 (sl2_fpf B hB1 hB3 _ hBu)
  have hord : orderOf A = 3 := orderOf_eq_prime hA3 hA1
  have hpow : ∀ k : ℕ, ¬ 3 ∣ k * 2 ^ m → ∀ B : SL(2, ZMod 2), B = A ^ (k * 2 ^ m) → B ≠ 1 := by
    intro k hk B hB h1
    apply hk
    rw [hB] at h1
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h1
  have h3m : ¬ 3 ∣ 2 ^ m := by
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  rcases comm_end_sl2_table A hA1 hA3 _ _ hcomm' with h | h | h | h
  · exfalso
    have hg0 : g = 0 := htab.trans h
    have h1 := hg (Pi.single 0 1)
    have hpos : 2 ^ m ≠ 0 := by positivity
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    rw [hn, Function.iterate_succ_apply, hg0] at h1
    have h2 : ((0 : (Fin 2 → ZMod 2) → (Fin 2 → ZMod 2))^[n]) 0 = 0 :=
      Function.iterate_fixed (by rfl) n
    have h3 : ((0 : (Fin 2 → ZMod 2) → (Fin 2 → ZMod 2))^[n])
        ((0 : (Fin 2 → ZMod 2) → (Fin 2 → ZMod 2)) (Pi.single 0 1)) = 0 := h2
    rw [h3] at h1
    exact hu0 h1.symm
  · exact htab.trans h
  · exfalso
    have hgA : g = fun u => A • u := htab.trans h
    have h1 := hg (Pi.single 0 1)
    rw [hgA, smul_iterate] at h1
    have hB3 : (A ^ 2 ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hA3, one_pow]
    have hB := hfix (A ^ 2 ^ m) hB3 h1
    exact hpow 1 (by rw [one_mul]; exact h3m) (A ^ 2 ^ m) (by rw [one_mul]) hB
  · exfalso
    have hgA : g = fun u => (A ^ 2) • u := by
      refine htab.trans (h.trans ?_)
      funext u
      rw [← mul_smul, ← pow_two]
    have h1 := hg (Pi.single 0 1)
    rw [hgA, smul_iterate] at h1
    have h23 : (A ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hA3, one_pow]
    have hB3 : ((A ^ 2) ^ 2 ^ m) ^ 3 = 1 := by
      rw [pow_right_comm, h23, one_pow]
    have hB := hfix ((A ^ 2) ^ 2 ^ m) hB3 h1
    refine hpow 2 ?_ ((A ^ 2) ^ 2 ^ m) (by rw [← pow_mul]) hB
    intro h32
    have := (Nat.Prime.dvd_mul Nat.prime_three).1 h32
    rcases this with h | h
    · omega
    · exact h3m h

section GroupPart

variable {X : Type*} [Group X]

theorem commutes_of_equivariant {P₁ V : Subgroup X}
    (π : ↥P₁ → (Fin 2 → ZMod 2))
    (hπadd : ∀ x y : ↥P₁, π (x * y) = π x + π y)
    (hπs : Function.Surjective π)
    (hπk : ∀ x : ↥P₁, π x = 0 ↔ (x : X) ∈ V)
    {d : X} (hdP : ∀ x ∈ P₁, d * x * d⁻¹ ∈ P₁) {A : SL(2, ZMod 2)} (hA1 : A ≠ 1) (hA3 : A ^ 3 = 1)
    (hrel : ∀ x : ↥P₁, π ⟨d * x * d⁻¹, hdP x x.2⟩ = A • π x)
    {r : X} (hrP : ∀ x ∈ P₁, r * x * r⁻¹ ∈ P₁) (hrd : r * d = d * r)
    (hrV : ∀ v ∈ V, r * v * r⁻¹ = v) {m : ℕ} (hr : r ^ 2 ^ m = 1) :
    ∀ x ∈ P₁, r * x * r⁻¹ * x⁻¹ ∈ V := by
  let ρ : ↥P₁ → ↥P₁ := fun x => ⟨r * x * r⁻¹, hrP x x.2⟩
  have hρmul : ∀ x y, ρ (x * y) = ρ x * ρ y := by
    intro x y
    apply Subtype.ext
    show r * ((x : X) * y) * r⁻¹ = (r * x * r⁻¹) * (r * y * r⁻¹)
    group
  have hπ1 : π 1 = 0 := by
    have := hπadd 1 1
    simpa using this
  have hπinv : ∀ x, π x⁻¹ = - π x := by
    intro x
    have := hπadd x⁻¹ x
    rw [inv_mul_cancel, hπ1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hρwd : ∀ x y : ↥P₁, π x = π y → π (ρ x) = π (ρ y) := by
    intro x y hxy
    have hxy' : π (x⁻¹ * y) = 0 := by
      rw [hπadd, hπinv, hxy]
      exact neg_add_cancel _
    have hv : ((x⁻¹ * y : ↥P₁) : X) ∈ V := (hπk _).1 hxy'
    have hρv : ρ (x⁻¹ * y) = x⁻¹ * y := Subtype.ext (hrV _ hv)
    have e : ρ y = ρ x * (x⁻¹ * y) := by
      rw [← hρv, ← hρmul]
      congr 1
      group
    rw [e, hπadd, hxy', add_zero]
  let sec : (Fin 2 → ZMod 2) → ↥P₁ := Function.surjInv hπs
  have hsec : ∀ u, π (sec u) = u := Function.surjInv_eq hπs
  let g : (Fin 2 → ZMod 2) → (Fin 2 → ZMod 2) := fun u => π (ρ (sec u))
  have hgspec : ∀ x : ↥P₁, g (π x) = π (ρ x) := fun x => hρwd _ _ (hsec _)
  have hgadd : ∀ u v, g (u + v) = g u + g v := by
    intro u v
    obtain ⟨x, rfl⟩ := hπs u
    obtain ⟨y, rfl⟩ := hπs v
    rw [← hπadd, hgspec, hgspec, hgspec, hρmul, hπadd]
  have hgcomm : ∀ u, g (A • u) = A • g u := by
    intro u
    obtain ⟨x, rfl⟩ := hπs u
    rw [← hrel x, hgspec, hgspec, ← hrel (ρ x)]
    congr 1
    apply Subtype.ext
    show r * (d * (x : X) * d⁻¹) * r⁻¹ = d * (r * (x : X) * r⁻¹) * d⁻¹
    have : r * (d * (x : X) * d⁻¹) * r⁻¹ = (r * d) * (x : X) * (r * d)⁻¹ := by group
    rw [this, hrd]
    group
  have hρiter : ∀ n (x : ↥P₁), ((ρ^[n] x : ↥P₁) : X) = r ^ n * (x : X) * (r ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      show r * ((ρ^[n] x : ↥P₁) : X) * r⁻¹ = r ^ (n + 1) * (x : X) * (r ^ (n + 1))⁻¹
      rw [ih, pow_succ']
      group
  have hgiter : ∀ n (x : ↥P₁), g^[n] (π x) = π (ρ^[n] x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', hgspec]
  have hg2m : ∀ u, g^[2 ^ m] u = u := by
    intro u
    obtain ⟨x, rfl⟩ := hπs u
    rw [hgiter]
    congr 1
    apply Subtype.ext
    rw [hρiter, hr]
    simp
  have hgid : g = id := eq_id_of_iterate hA1 hA3 g hgadd hgcomm hg2m
  intro x hx
  have h1 : π (ρ ⟨x, hx⟩) = π ⟨x, hx⟩ := by
    rw [← hgspec, hgid]
    rfl
  have h2 : π (ρ ⟨x, hx⟩ * (⟨x, hx⟩ : ↥P₁)⁻¹) = 0 := by
    rw [hπadd, hπinv, h1]
    exact add_neg_cancel _
  exact (hπk _).1 h2

theorem comm_eq_one_of_fixed {V : Subgroup X} {d r x : X}
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hrV : ∀ v ∈ V, r * v * r⁻¹ = v)
    (hVf : ∀ v ∈ V, d * v * d⁻¹ = v → v = 1)
    (hrd : r * d = d * r)
    (hx : d * x * d⁻¹ * x⁻¹ ∈ V) (hrx : r * x * r⁻¹ * x⁻¹ ∈ V) :
    r * x * r⁻¹ * x⁻¹ = 1 := by
  set w := r * x * r⁻¹ * x⁻¹ with hw
  set v := d * x * d⁻¹ * x⁻¹ with hv
  have hdr : d * r * d⁻¹ = r := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hrd.symm
  have hdri : d * r⁻¹ * d⁻¹ = r⁻¹ := by
    rw [show d * r⁻¹ * d⁻¹ = (d * r * d⁻¹)⁻¹ by group, hdr]
  have e1 : d * w * d⁻¹ = (r * v * r⁻¹) * w * v⁻¹ := by
    calc d * w * d⁻¹ = (d * r * d⁻¹) * (d * x * d⁻¹) * (d * r⁻¹ * d⁻¹) * (d * x⁻¹ * d⁻¹) := by
          rw [hw]; group
      _ = r * (d * x * d⁻¹) * r⁻¹ * (d * x * d⁻¹)⁻¹ := by rw [hdr, hdri]; group
      _ = (r * v * r⁻¹) * w * v⁻¹ := by rw [hv, hw]; group
  rw [hrV v hx] at e1
  have e2 : v * w * v⁻¹ = w := by
    rw [hVab v hx w hrx]
    group
  rw [e2] at e1
  exact hVf w hrx e1

end GroupPart

end S153E59

end CFSG.Quasithin

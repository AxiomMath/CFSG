module

public import Mathlib.GroupTheory.OrderOfElement


public section

namespace CFSG.StandardType

private lemma gnrlq_coprime_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    Nat.Coprime (2 ^ k) p := by
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)
  induction k with
  | zero => simp [Nat.Coprime]
  | succ k ih =>
      rw [pow_succ, Nat.coprime_mul_iff_left]
      exact ⟨ih, hcop⟩

private lemma gnrlq_eq_one_of_pow_two_pow {V : Type*} [Group V] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : V} {k : ℕ} (h2 : x ^ 2 ^ k = 1) (hxp : x ^ p = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ k) p := gnrlq_coprime_two_pow hp hp2 k
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one hxp))

private lemma gnrlq_eq_one_of_sq_eq_one {V : Type*} [Group V] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : V} (h2 : x ^ 2 = 1) (hxp : x ^ p = 1) : x = 1 := by
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one hxp))

theorem isReflection_of_quotient {V Q : Type*} [Group V] [Group Q] [Finite V] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hVc : ∀ a b : V, a * b = b * a) (hVp : ∀ v : V, v ^ p = 1)
    (π : V →* Q) (hπ : Function.Surjective π) (c : MulAut V) (r : MulAut Q)
    (hcr : ∀ v, π (c v) = r (π v)) (hfix : ∀ v ∈ π.ker, c v = v) {a : ℕ} (hc : c ^ 2 ^ a = 1)
    (hr2 : r ^ 2 = 1) (hrf : Nat.card {q : Q // r q = q} * p = Nat.card Q) :
    c ^ 2 = 1 ∧ Nat.card {v : V // c v = v} * p = Nat.card V := by
  classical
  haveI hQfin : Finite Q := Finite.of_surjective π hπ
  set u : MulAut V := c ^ 2 with hu_def
  have hu_apply : ∀ v, u v = c (c v) := by
    intro v
    rw [hu_def, pow_two, MulAut.mul_apply]
  have hπu : ∀ v, π (u v) = π v := by
    intro v
    rw [hu_apply v, hcr (c v), hcr v]
    have hr2' : r * r = 1 := by rw [← pow_two, hr2]
    calc r (r (π v)) = (r * r) (π v) := rfl
      _ = (1 : MulAut Q) (π v) := by rw [hr2']
      _ = π v := rfl
  have hδ_ker : ∀ v, v⁻¹ * u v ∈ π.ker := by
    intro v
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπu v]
    simp
  have hδ_fix : ∀ v, c (v⁻¹ * u v) = v⁻¹ * u v := fun v => hfix _ (hδ_ker v)
  set δ : V → V := fun v => v⁻¹ * u v with hδ_def
  have hδv : ∀ v, δ v = v⁻¹ * u v := by intro v; rw [hδ_def]
  have hu_v : ∀ v, u v = v * δ v := by
    intro v
    rw [hδv v]
    exact (mul_inv_cancel_left v (u v)).symm
  have hu_δ : ∀ v, u (δ v) = δ v := by
    intro v
    rw [hδv v]
    have h1 : u (v⁻¹ * u v) = c (c (v⁻¹ * u v)) := hu_apply _
    rw [h1, hδ_fix v, hδ_fix v]
  have hpow : ∀ k v, (u ^ k) v = v * δ v ^ k := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [pow_succ', MulAut.mul_apply, ih v, map_mul, map_pow, hu_δ v]
        rw [hu_v v, mul_assoc, ← pow_succ']
  have hc2 : c ^ 2 = 1 := by
    rcases a with _ | a'
    · have hc1 : c = 1 := by simpa using hc
      rw [hc1, one_pow]
    · have hu_pow : u ^ 2 ^ a' = 1 := by
        rw [hu_def, ← pow_mul, ← pow_succ']
        exact hc
      have hδ2 : ∀ v, δ v ^ 2 ^ a' = 1 := by
        intro v
        have h := hpow (2 ^ a') v
        rw [hu_pow] at h
        have hv : v = v * δ v ^ 2 ^ a' := by simpa using h
        exact (mul_left_cancel (show v * 1 = v * δ v ^ 2 ^ a' by
          rw [mul_one]; exact hv)).symm
      have hδ1 : ∀ v, δ v = 1 := fun v =>
        gnrlq_eq_one_of_pow_two_pow hp hp2 (hδ2 v) (hVp _)
      have hu1 : u = 1 := by
        ext v
        calc u v = v * δ v := hu_v v
          _ = v * 1 := by rw [hδ1 v]
          _ = v := mul_one v
      simpa [hu_def] using hu1
  have hQc : ∀ a b : Q, a * b = b * a := by
    intro q1 q2
    obtain ⟨v1, rfl⟩ := hπ q1
    obtain ⟨v2, rfl⟩ := hπ q2
    calc π v1 * π v2 = π (v1 * v2) := (map_mul π v1 v2).symm
      _ = π (v2 * v1) := by rw [hVc v1 v2]
      _ = π v2 * π v1 := map_mul π v2 v1
  letI : CommGroup V := { ‹Group V› with mul_comm := hVc }
  letI : CommGroup Q := { ‹Group Q› with mul_comm := hQc }
  let ε : V →* V := (MonoidHom.id V) * (invMonoidHom.comp c.toMonoidHom)
  let εQ : Q →* Q := (MonoidHom.id Q) * (invMonoidHom.comp r.toMonoidHom)
  have hε : ∀ v : V, ε v = v * (c v)⁻¹ := by intro v; rfl
  have hεQ : ∀ q : Q, εQ q = q * (r q)⁻¹ := by intro q; rfl
  have hrange_inj : ∀ x ∈ ε.range, π x = 1 → x = 1 := by
    intro x hx hπx
    obtain ⟨v, hv⟩ := hx
    have hcx : c x = x := hfix x (by rw [MonoidHom.mem_ker]; exact hπx)
    have hccv : c (c v) = v := by
      have h : (c ^ 2) v = (1 : MulAut V) v := congrArg (fun f : MulAut V => f v) hc2
      simpa [pow_two, MulAut.mul_apply] using h
    have hcv : c x = c v * v⁻¹ := by
      rw [← hv, hε v, map_mul, map_inv, hccv]
    have hxinv : x = x⁻¹ := by
      calc x = c x := hcx.symm
        _ = c v * v⁻¹ := hcv
        _ = x⁻¹ := by rw [← hv, hε v, mul_inv_rev, inv_inv]
    have hx2 : x ^ 2 = 1 := by
      calc x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := by rw [← hxinv]
        _ = 1 := mul_inv_cancel x
    exact gnrlq_eq_one_of_sq_eq_one hp hp2 hx2 (hVp _)
  let φ : ε.range → εQ.range := fun e =>
    ⟨π e, by
      obtain ⟨v, hv⟩ := e.2
      refine ⟨π v, ?_⟩
      rw [← hv, hεQ, hε v, map_mul, map_inv, hcr v]⟩
  have hφinj : Function.Injective φ := by
    intro e1 e2 he
    apply Subtype.ext
    have hπe : π (e1 : V) = π (e2 : V) := congrArg Subtype.val he
    have hmem : (e1 : V) * (e2 : V)⁻¹ ∈ ε.range :=
      ε.range.mul_mem e1.2 (ε.range.inv_mem e2.2)
    have hker : π ((e1 : V) * (e2 : V)⁻¹) = 1 := by
      rw [map_mul, map_inv, hπe, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hrange_inj _ hmem hker)
  have hφsurj : Function.Surjective φ := by
    intro e
    obtain ⟨v, hv⟩ := e.2
    obtain ⟨w, hw⟩ := hπ v
    refine ⟨⟨ε w, ⟨w, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    rw [← hw] at hv
    have h1 : π (ε w) = εQ (π w) := by rw [hεQ, hε w, map_mul, map_inv, hcr w]
    show π (ε w) = (e : Q)
    rw [h1, hv]
  have hrange_eq : Nat.card ε.range = Nat.card εQ.range :=
    Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)
  have hkerV : Nat.card ε.ker = Nat.card {v : V // c v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => by
      rw [MonoidHom.mem_ker (f := ε), hε v, mul_inv_eq_one, eq_comm]))
  have hkerQ : Nat.card εQ.ker = Nat.card {q : Q // r q = q} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun q => by
      rw [MonoidHom.mem_ker (f := εQ), hεQ q, mul_inv_eq_one, eq_comm]))
  have hVcard : Nat.card ε.ker * Nat.card ε.range = Nat.card V :=
    Subgroup.card_ker_mul_card_range ε
  have hQcard : Nat.card εQ.ker * Nat.card εQ.range = Nat.card Q :=
    Subgroup.card_ker_mul_card_range εQ
  haveI : Nonempty {q : Q // r q = q} := ⟨1, map_one r⟩
  have hKQpos : 0 < Nat.card {q : Q // r q = q} := Nat.card_pos
  have hrangeQ : Nat.card εQ.range = p := by
    have h1 : Nat.card {q : Q // r q = q} * p
        = Nat.card {q : Q // r q = q} * Nat.card εQ.range := by
      rw [hrf, ← hkerQ, ← hQcard]
    exact (Nat.mul_left_cancel hKQpos h1).symm
  refine ⟨hc2, ?_⟩
  have hrangeV : Nat.card ε.range = p := hrange_eq.trans hrangeQ
  rw [← hkerV, ← hrangeV]
  exact hVcard

end CFSG.StandardType

end

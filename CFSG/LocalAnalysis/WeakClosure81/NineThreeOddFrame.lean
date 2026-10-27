module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreAct
public import CFSG.Quasithin.Background.D2Tools
public import CFSG.ClassicalInvolution.Asc77.AscP1Thompson3T
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.ClassicalInvolution.Asc77 Subgroup
open scoped Pointwise commutatorElement

variable {Γ : Type} [Group Γ] {p m : ℕ}

structure Nine3OddFrame (p m : ℕ) (π : Γ →* Equiv.Perm (ZMod p)) (D : Set Γ) : Prop where
  sq : ∀ d ∈ D, d * d = 1
  conj : ∀ d ∈ D, ∀ γ : Γ, γ * d * γ⁻¹ ∈ D
  gen : Subgroup.closure D = ⊤
  refl : ∀ d ∈ D, ∃ c : ZMod p, π d = zmodRefl p c
  card : ∀ c : ZMod p, Nat.card {d : Γ // d ∈ D ∧ π d = zmodRefl p c} = m
  comm : ∀ d ∈ D, ∀ e ∈ D, π d = π e → d * e = e * d
  pow : ∀ d ∈ D, ∀ e ∈ D, π d ≠ π e → (d * e) ^ p = 1
  trans : ∀ a b : ZMod p, a ≠ b → ∀ d ∈ D, π d = zmodRefl p a → ∀ e ∈ D, π e = zmodRefl p a →
    ∃ z ∈ Subgroup.closure {f | f ∈ D ∧ π f = zmodRefl p b} ⊓ π.ker, z * d * z⁻¹ = e

@[expose] def nine3FibreSet (π : Γ →* Equiv.Perm (ZMod p)) (D : Set Γ) (c : ZMod p) : Set Γ :=
  {d | d ∈ D ∧ π d = zmodRefl p c}

@[expose] def Nine3FibreIndep (p : ℕ) (π : Γ →* Equiv.Perm (ZMod p)) (D : Set Γ) : Prop :=
  ∀ (c : ZMod p) (l : List Γ), l.Nodup → l ≠ [] → (∀ d ∈ l, d ∈ D ∧ π d = zmodRefl p c) →
    l.prod ≠ 1

private lemma nine3_two_ne_zero (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hc
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hc
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

private lemma nine3_zmodRefl_mul_self (c : ZMod p) :
    zmodRefl p c * zmodRefl p c = 1 := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply, Equiv.Perm.one_apply]
  ring

private lemma nine3_zmodRefl_conj (s a : ZMod p) :
    zmodRefl p s * zmodRefl p a * zmodRefl p s = zmodRefl p (2 * s - a) := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply]
  ring

private lemma nine3_zmodRefl_ne_one (hp : p.Prime) (hp2 : p ≠ 2) (c : ZMod p) :
    zmodRefl p c ≠ 1 := by
  intro h
  have h1 := congrArg (fun f : Equiv.Perm (ZMod p) => f (c + 1)) h
  simp only [zmodRefl, Equiv.subLeft_apply, Equiv.Perm.one_apply] at h1
  have h2 : (2 : ZMod p) = 0 := by
    have h3 : 2 * c - (c + 1) - (c + 1) = 0 := by rw [h1]; ring
    have h4 : 2 * c - (c + 1) - (c + 1) = -(2 : ZMod p) := by ring
    rw [h4] at h3
    exact neg_eq_zero.mp h3
  exact nine3_two_ne_zero hp hp2 h2

private lemma nine3_zmod3_cover {ca cb x : ZMod 3} (h : ca ≠ cb) :
    x = ca ∨ x = cb ∨ x = 2 * ca - cb := by
  revert h ca cb x
  decide

theorem zmodRefl_inj (hp : p.Prime) (hp2 : p ≠ 2) {c c' : ZMod p}
    (h : zmodRefl p c = zmodRefl p c') : c = c' := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 := congrArg (fun f : Equiv.Perm (ZMod p) => f 0) h
  simp only [zmodRefl, Equiv.subLeft_apply, sub_eq_add_neg] at h0
  exact mul_left_cancel₀ (nine3_two_ne_zero hp hp2) (add_right_cancel h0)

private lemma nine3_mem_closure_pair {a b x : Γ} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    x ∈ Subgroup.closure ({a, b} : Set Γ) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hle : Subgroup.closure ({a, b} : Set Γ) ≤ klein a b ha hb hab.symm :=
    (Subgroup.closure_le _).mpr (by
      intro y hy
      rcases hy with rfl | rfl
      · exact mem_klein.mpr (Or.inr (Or.inl rfl))
      · exact mem_klein.mpr (Or.inr (Or.inr (Or.inl rfl))))
  constructor
  · intro hx
    exact mem_klein.mp (hle hx)
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

private theorem nine3_two_p_aux (hp : p.Prime) (hp2 : p ≠ 2)
    {π : Γ →* Equiv.Perm (ZMod p)} {D : Set Γ} (h : Nine3OddFrame p 2 π D) :
    ∃ z : ZMod p → Γ, (∀ c, z c * z c = 1) ∧ (∀ c, z c ≠ 1) ∧
      (∀ a b, a ≠ b → z a * z b * z (2 * a - b) = 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let F : ZMod p → Set Γ := nine3FibreSet π D
  have hFcard : ∀ c, (F c).ncard = 2 := by
    intro c
    have hc : Nat.card (Subtype (fun d : Γ => d ∈ D ∧ π d = zmodRefl p c)) = 2 := h.card c
    rw [← Nat.card_coe_set_eq]
    exact hc
  have hFpair : ∀ c, ∃ x y : Γ, x ≠ y ∧ F c = {x, y} :=
    fun c => Set.ncard_eq_two.mp (hFcard c)
  choose d0 d1 hdne hdF using hFpair
  have hd0F : ∀ c, d0 c ∈ F c := by intro c; rw [hdF c]; simp
  have hd1F : ∀ c, d1 c ∈ F c := by intro c; rw [hdF c]; simp
  have hd0D : ∀ c, d0 c ∈ D := fun c => (hd0F c).1
  have hd1D : ∀ c, d1 c ∈ D := fun c => (hd1F c).1
  have hd0pi : ∀ c, π (d0 c) = zmodRefl p c := fun c => (hd0F c).2
  have hd1pi : ∀ c, π (d1 c) = zmodRefl p c := fun c => (hd1F c).2
  have hd0sq : ∀ c, d0 c * d0 c = 1 := fun c => h.sq _ (hd0D c)
  have hd1sq : ∀ c, d1 c * d1 c = 1 := fun c => h.sq _ (hd1D c)
  have hcomm01 : ∀ c, d0 c * d1 c = d1 c * d0 c :=
    fun c => h.comm _ (hd0D c) _ (hd1D c) (by rw [hd0pi, hd1pi])
  let z : ZMod p → Γ := fun c => d0 c * d1 c
  have hzsq : ∀ c, z c * z c = 1 := by
    intro c
    change (d0 c * d1 c) * (d0 c * d1 c) = 1
    calc (d0 c * d1 c) * (d0 c * d1 c) = d0 c * (d1 c * d0 c) * d1 c := by
          simp only [mul_assoc]
      _ = d0 c * (d0 c * d1 c) * d1 c := by rw [← hcomm01 c]
      _ = (d0 c * d0 c) * (d1 c * d1 c) := by simp only [mul_assoc]
      _ = 1 := by rw [hd0sq c, hd1sq c, one_mul]
  have hzne : ∀ c, z c ≠ 1 := by
    intro c hz1
    have hz1' : d0 c * d1 c = 1 := hz1
    have hd1eq : d1 c = d0 c := by
      have := eq_inv_of_mul_eq_one_right hz1'
      rwa [inv_eq_of_mul_eq_one_right (hd0sq c)] at this
    exact hdne c hd1eq.symm
  have hzpi : ∀ c, π (z c) = 1 := by
    intro c
    change π (d0 c * d1 c) = 1
    rw [map_mul, hd0pi c, hd1pi c]
    exact nine3_zmodRefl_mul_self c
  have hpair_prod : ∀ c u v, u ∈ nine3FibreSet π D c → v ∈ nine3FibreSet π D c →
      u ≠ v → u * v = z c := by
    intro c u v hu hv huv
    rw [show nine3FibreSet π D c = {d0 c, d1 c} from hdF c] at hu hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv
    · rfl
    · exact (hcomm01 c).symm
    · exact absurd rfl huv
  have hz2 : ∀ a b : ZMod p, a ≠ b → z b * d0 a * z b = d1 a := by
    intro a b hab
    obtain ⟨w, hw_mem, hw_conj⟩ :=
      h.trans a b hab (d0 a) (hd0D a) (hd0pi a) (d1 a) (hd1D a) (hd1pi a)
    have hw_cl : w ∈ Subgroup.closure {d0 b, d1 b} := by
      have h1 : w ∈ Subgroup.closure (nine3FibreSet π D b) := hw_mem.1
      rwa [show nine3FibreSet π D b = {d0 b, d1 b} from hdF b] at h1
    have hw_pi : π w = 1 := MonoidHom.mem_ker.mp hw_mem.2
    rcases (nine3_mem_closure_pair (hd0sq b) (hd1sq b) (hcomm01 b)).mp hw_cl with
      hw1 | hw0 | hw1' | hwz
    · exact absurd (by simpa [hw1] using hw_conj) (hdne a)
    · exact absurd (by rw [← hd0pi, ← hw0, hw_pi]) (nine3_zmodRefl_ne_one hp hp2 b)
    · exact absurd (by rw [← hd1pi, ← hw1', hw_pi]) (nine3_zmodRefl_ne_one hp hp2 b)
    · have hw_eq : w * d0 a * w⁻¹ = d1 a := hw_conj
      rw [hwz] at hw_eq
      rwa [inv_eq_of_mul_eq_one_right (hzsq b)] at hw_eq
  have hzconj : ∀ s a : ZMod p, d0 s * z a * (d0 s)⁻¹ = z (2 * s - a) := by
    intro s a
    have huF : d0 s * d0 a * (d0 s)⁻¹ ∈ nine3FibreSet π D (2 * s - a) := by
      refine ⟨h.conj (d0 a) (hd0D a) (d0 s), ?_⟩
      rw [map_mul, map_mul, map_inv, hd0pi, hd0pi,
        inv_eq_of_mul_eq_one_right (nine3_zmodRefl_mul_self s)]
      exact nine3_zmodRefl_conj s a
    have hvF : d0 s * d1 a * (d0 s)⁻¹ ∈ nine3FibreSet π D (2 * s - a) := by
      refine ⟨h.conj (d1 a) (hd1D a) (d0 s), ?_⟩
      rw [map_mul, map_mul, map_inv, hd0pi, hd1pi,
        inv_eq_of_mul_eq_one_right (nine3_zmodRefl_mul_self s)]
      exact nine3_zmodRefl_conj s a
    have huv : d0 s * d0 a * (d0 s)⁻¹ ≠ d0 s * d1 a * (d0 s)⁻¹ := by
      intro huv
      have h2 := congrArg (fun x => (d0 s)⁻¹ * x * d0 s) huv
      have h3 : (d0 s)⁻¹ * (d0 s * d0 a * (d0 s)⁻¹) * d0 s = d0 a := by group
      have h4 : (d0 s)⁻¹ * (d0 s * d1 a * (d0 s)⁻¹) * d0 s = d1 a := by group
      rw [h3, h4] at h2
      exact hdne a h2
    have hprod : (d0 s * d0 a * (d0 s)⁻¹) * (d0 s * d1 a * (d0 s)⁻¹) =
        d0 s * z a * (d0 s)⁻¹ := by
      change (d0 s * d0 a * (d0 s)⁻¹) * (d0 s * d1 a * (d0 s)⁻¹) =
        d0 s * (d0 a * d1 a) * (d0 s)⁻¹
      group
    rw [hpair_prod (2 * s - a) _ _ huF hvF huv] at hprod
    exact hprod.symm
  have hzrel : ∀ a b : ZMod p, a ≠ b → z a * z b * z (2 * a - b) = 1 := by
    intro a b hab
    have hb_d0 : z b * d0 a * z b = d1 a := hz2 a b hab
    have hza : z a = z (2 * a - b) * z b := by
      change d0 a * d1 a = z (2 * a - b) * z b
      rw [← hb_d0, ← hzconj a b, inv_eq_of_mul_eq_one_right (hd0sq a)]
      group
    rw [hza]
    calc (z (2 * a - b) * z b) * z b * z (2 * a - b)
        = z (2 * a - b) * (z b * z b) * z (2 * a - b) := by group
      _ = 1 := by rw [hzsq b, mul_one, hzsq (2 * a - b)]
  exact ⟨z, hzsq, hzne, hzrel⟩

theorem nine3OddFrame_two_p (hp : p.Prime) (hp2 : p ≠ 2) {π : Γ →* Equiv.Perm (ZMod p)}
    {D : Set Γ} (h : Nine3OddFrame p 2 π D) : p = 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨z, hzsq, hzne, hzrel⟩ := nine3_two_p_aux hp hp2 h
  by_contra hp3
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro hc
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hc
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3eq
    · exact hp.ne_one h1
    · exact hp3 h3eq
  have hstep : ∀ i : ZMod p, z (i + 3) = z i := by
    intro i
    have hz2' : z (i + 2) = z i * z (i + 1) := by
      have hR := hzrel (i + 1) i (by
        intro h
        have h' : (1 : ZMod p) = 0 := by
          calc (1 : ZMod p) = i + 1 - i := by ring
            _ = i - i := by rw [h]
            _ = 0 := by ring
        exact one_ne_zero h')
      have h2' : 2 * (i + 1) - i = i + 2 := by ring
      rw [h2'] at hR
      have key : z i * z (i + 2) = z (i + 1) := by
        have h := congrArg (fun x => z (i + 1) * x) hR
        rw [mul_one] at h
        have h' : z (i + 1) * (z (i + 1) * z i * z (i + 2)) =
            (z (i + 1) * z (i + 1)) * (z i * z (i + 2)) := by group
        rw [h'] at h
        rwa [hzsq (i + 1), one_mul] at h
      have h2 := congrArg (fun x => z i * x) key
      have h2' : z i * (z i * z (i + 2)) = (z i * z i) * z (i + 2) := by group
      rw [h2'] at h2
      rwa [hzsq i, one_mul] at h2
    have hR2 := hzrel (i + 2) (i + 1) (by
      intro h
      have h' : (1 : ZMod p) = 0 := by
        calc (1 : ZMod p) = i + 2 - (i + 1) := by ring
          _ = (i + 1) - (i + 1) := by rw [h]
          _ = 0 := by ring
      exact one_ne_zero h')
    have h2'' : 2 * (i + 2) - (i + 1) = i + 3 := by ring
    rw [h2''] at hR2
    have hzi2' : z (i + 2) * z (i + 1) = z i := by
      rw [hz2', mul_assoc, hzsq (i + 1), mul_one]
    have hmain : z i * z (i + 3) = 1 := by
      rw [← hzi2']
      exact hR2
    have h1 : z (i + 3) = (z i)⁻¹ := eq_inv_of_mul_eq_one_right hmain
    rwa [inv_eq_of_mul_eq_one_right (hzsq i)] at h1
  have hper : ∀ n : ℕ, z (((n : ℕ) : ZMod p) * 3) = z 0 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        have hcast : (((n + 1 : ℕ) : ZMod p)) * 3 = (n : ZMod p) * 3 + 3 := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
        rw [hcast, hstep, ih]
  have hzj : ∀ j : ZMod p, z j = z 0 := by
    intro j
    have hk : (((3⁻¹ * j).val : ℕ) : ZMod p) * 3 = j := by
      rw [ZMod.natCast_zmod_val]
      calc (3⁻¹ * j) * 3 = 3⁻¹ * (j * 3) := by rw [mul_assoc]
        _ = 3⁻¹ * (3 * j) := by rw [mul_comm j 3]
        _ = (3⁻¹ * 3) * j := by rw [mul_assoc]
        _ = 1 * j := by rw [inv_mul_cancel₀ h3]
        _ = j := by rw [one_mul]
    have := hper (3⁻¹ * j).val
    rwa [hk] at this
  have hz0 : z 0 = 1 := by
    have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h := hzrel (1 : ZMod p) 0 h10
    rw [show 2 * (1 : ZMod p) - 0 = 2 by ring] at h
    rw [hzj 1, hzj 2] at h
    rw [hzsq 0] at h
    simpa using h
  exact hzne 0 hz0

theorem nine3OddFrame_isTT {π : Γ →* Equiv.Perm (ZMod 3)} {D : Set Γ}
    (h : Nine3OddFrame 3 m π D) : Star3T.IsTT D where
  mul_self := h.sq
  ne_one := by
    intro d hd hd1
    obtain ⟨c, hc⟩ := h.refl d hd
    exact nine3_zmodRefl_ne_one (p := 3) (by norm_num) (by norm_num) c
      (by rw [← hc, hd1, map_one])
  conj_mem := fun d hd γ => h.conj d hd γ
  closure_eq_top := h.gen
  comm_or_cube := by
    intro a ha b hb
    by_cases hπ : π a = π b
    · exact Or.inl (h.comm a ha b hb hπ)
    · exact Or.inr (h.pow a ha b hb hπ)

theorem nine3OddFrame_isStar {π : Γ →* Equiv.Perm (ZMod 3)} {D : Set Γ}
    (h : Nine3OddFrame 3 m π D) : Star3T.IsStar D := by
  intro a ha b hb hnab c hc
  obtain ⟨ca, ha_ca⟩ := h.refl a ha
  obtain ⟨cb, hb_cb⟩ := h.refl b hb
  have hcab : ca ≠ cb := fun hcc =>
    hnab (h.comm a ha b hb (by rw [ha_ca, hb_cb, hcc]))
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.sq a ha)
  have haba_mem : a * b * a ∈ D := by
    have hconj := h.conj b hb a
    rwa [ha_inv] at hconj
  have hpi_aba : π (a * b * a) = zmodRefl 3 (2 * ca - cb) := by
    calc π (a * b * a) = π a * π b * π a := by rw [map_mul, map_mul]
      _ = zmodRefl 3 ca * zmodRefl 3 cb * zmodRefl 3 ca := by rw [ha_ca, hb_cb]
      _ = zmodRefl 3 (2 * ca - cb) := nine3_zmodRefl_conj ca cb
  obtain ⟨cc, hcc⟩ := h.refl c hc
  rcases nine3_zmod3_cover (ca := ca) (cb := cb) (x := cc) hcab with hcase | hcase | hcase
  · exact Or.inl (h.comm c hc a ha (by rw [hcc, hcase, ha_ca]))
  · exact Or.inr (Or.inl (h.comm c hc b hb (by rw [hcc, hcase, hb_cb])))
  · exact Or.inr (Or.inr (h.comm c hc (a * b * a) haba_mem (by rw [hcc, hcase, ← hpi_aba])))

private lemma nine3_pi_eq_of_comm_three {π : Γ →* Equiv.Perm (ZMod 3)} {D : Set Γ}
    (h : Nine3OddFrame 3 m π D) {x y : Γ} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : x * y = y * x) : π x = π y := by
  by_contra hne
  have h3 := h.pow x hx y hy hne
  have hsq : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [← hxy]
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [h.sq x hx, h.sq y hy, one_mul]
  have h1 : x * y = 1 := by
    have e : (x * y) ^ 3 = (x * y) ^ 2 * (x * y) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one]
    rw [e, pow_two, hsq, one_mul] at h3
    exact h3
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left (h.sq y hy)
  have hxy1 : x = y := by
    have := eq_inv_of_mul_eq_one_left h1
    rwa [hyinv] at this
  exact hne (by rw [hxy1])

private lemma nine3_conn_pi_eq_three {π : Γ →* Equiv.Perm (ZMod 3)} {D : Set Γ}
    (h : Nine3OddFrame 3 m π D) {x y : Γ} (hx : x ∈ D) (hy : y ∈ D)
    (hc : Star3T.Conn D x y) : π x = π y := by
  have aux : ∀ z, Star3T.Conn D x z → π x = π z := by
    intro z hz
    induction hz with
    | refl => rfl
    | tail _ hbc ih =>
        exact ih.trans (nine3_pi_eq_of_comm_three h hbc.1 hbc.2.1 hbc.2.2)
  exact aux y hc

theorem nine3OddFrame_not_conn {π : Γ →* Equiv.Perm (ZMod 3)} {D : Set Γ}
    (h : Nine3OddFrame 3 m π D) {d a : Γ} (hd : d ∈ D) (ha : a ∈ D) (hne : π d ≠ π a) :
    ¬ Star3T.Conn D d a := by
  intro hc
  exact hne (nine3_conn_pi_eq_three h hd ha hc)

theorem nine3OddFrame_ncard_cent {π : Γ →* Equiv.Perm (ZMod 3)} {D : Set Γ}
    (h : Nine3OddFrame 3 m π D) {d : Γ} (hd : d ∈ D) : (Star3T.cent D d).ncard = m := by
  obtain ⟨c, hc⟩ := h.refl d hd
  have hset : Star3T.cent D d = nine3FibreSet π D c := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      have := nine3_pi_eq_of_comm_three h hx.1 hd hx.2
      rwa [hc] at this
    · intro hx
      exact ⟨hx.1, h.comm x hx.1 d hd (by rw [hx.2, hc])⟩
  rw [hset]
  exact h.card c

theorem nine3OddFrame_exists_ne {π : Γ →* Equiv.Perm (ZMod 3)} {D : Set Γ}
    (h : Nine3OddFrame 3 m π D) (hm : 0 < m) : ∃ d ∈ D, ∃ a ∈ D, π d ≠ π a := by
  have hcard0 : 0 < Nat.card {d : Γ // d ∈ D ∧ π d = zmodRefl 3 (0 : ZMod 3)} := by
    rw [h.card 0]; exact hm
  have hcard1 : 0 < Nat.card {a : Γ // a ∈ D ∧ π a = zmodRefl 3 (1 : ZMod 3)} := by
    rw [h.card 1]; exact hm
  obtain ⟨d⟩ := (Nat.card_pos_iff.mp hcard0).1
  obtain ⟨a⟩ := (Nat.card_pos_iff.mp hcard1).1
  refine ⟨d, d.2.1, a, a.2.1, ?_⟩
  intro heq
  have h01 : (0 : ZMod 3) = 1 :=
    zmodRefl_inj (p := 3) (by norm_num) (by norm_num)
      (by rw [← d.2.2, heq, a.2.2])
  exact (by decide : (0 : ZMod 3) ≠ 1) h01

end CFSG.LocalAnalysis.WeakClosure81

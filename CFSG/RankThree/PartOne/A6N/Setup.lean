module

public import CFSG.RankThree.PartOne.A6N.Defs
public import CFSG.RankThree.PartOne.N1322.CaseBasic

public section

namespace CFSG.RankThree.PartOne.A6N

open CFSG.RankThree.PartOne.N1322 CFSG.RepresentationTheory Equiv

structure Val (p : ℕ) [Fact p.Prime] where
  H : Subgroup (GL (Fin 3) (ZMod p))
  irr : IsIrreducibleMatrixRep H.subtype
  perf : Group.IsPerfect H
  card : Nat.card (Subgroup.center H) = 3
  e : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)

namespace Val

variable {p : ℕ} [Fact p.Prime] (V : Val p)

include V

@[expose] def E : V.H →* alternatingGroup (Fin 6) :=
  V.e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center V.H))

theorem E_apply (x : V.H) : V.E x = V.e (QuotientGroup.mk x) := rfl

theorem E_surjective : Function.Surjective V.E := fun y => by
  obtain ⟨q, hq⟩ := V.e.surjective y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective q
  exact ⟨x, by rw [E_apply, hx, hq]⟩

theorem E_eq_one_iff (x : V.H) : V.E x = 1 ↔ x ∈ Subgroup.center V.H := by
  rw [E_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem center_pow_three (z : V.H) (hz : z ∈ Subgroup.center V.H) : z ^ 3 = 1 := by
  have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center V.H)
  rw [V.card] at h1
  have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
  simpa using congrArg (fun w : Subgroup.center V.H => (w : V.H)) h2

theorem eq_of_E_eq {x y : V.H} {n : ℕ} (hn : Nat.Coprime n 3) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (h : V.E x = V.E y) : x = y := by
  have hz : x⁻¹ * y ∈ Subgroup.center V.H := by
    rw [← V.E_eq_one_iff, map_mul, map_inv, h, inv_mul_cancel]
  have hc : Commute x (x⁻¹ * y) := Subgroup.mem_center_iff.mp hz x
  have h1 : (x⁻¹ * y) ^ n = 1 := by
    have h2 : y = x * (x⁻¹ * y) := by group
    have h3 : y ^ n = x ^ n * (x⁻¹ * y) ^ n := by
      conv_lhs => rw [h2]
      exact hc.mul_pow n
    rw [hy, hx, one_mul] at h3
    exact h3.symm
  have h4 : (x⁻¹ * y) ^ Nat.gcd n 3 = 1 := pow_gcd_eq_one.2 ⟨h1, V.center_pow_three _ hz⟩
  rw [hn, pow_one] at h4
  exact inv_mul_eq_one.mp h4

theorem exists_noncomm : ∃ a ∈ V.H, ∃ b ∈ V.H, a * b ≠ b * a := by
  obtain ⟨a, ha⟩ := V.E_surjective a₀A
  obtain ⟨b, hb⟩ := V.E_surjective y₀A
  refine ⟨a, a.2, b, b.2, fun h => ?_⟩
  have h1 : a * b = b * a := Subtype.ext h
  have h2 := congrArg V.E h1
  rw [map_mul, map_mul, ha, hb] at h2
  have h3 := congrArg Subtype.val h2
  revert h3
  simp only [coe_a₀A, coe_y₀A, Subgroup.coe_mul]
  decide +kernel

theorem scalar_of_center (z : V.H) (hz : z ∈ Subgroup.center V.H) :
    ∃ c : ZMod p, ((z : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      Matrix.scalar (Fin 3) c := by
  refine scalar_commutant_of_noncomm V.irr V.exists_noncomm _ fun g hg => ?_
  have := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
  have h2 := congrArg (fun w : V.H => (w : GL (Fin 3) (ZMod p))) this
  have h3 := congrArg (fun w : GL (Fin 3) (ZMod p) => (w : Matrix (Fin 3) (Fin 3) (ZMod p))) h2
  simpa using h3

theorem card_H : Nat.card V.H = 1080 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center V.H)
  have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [V.card, Nat.card_congr V.e.toEquiv, h6] at h
  simpa using h

theorem finite_H : Finite V.H :=
  Nat.finite_of_card_ne_zero (by rw [V.card_H]; norm_num)

theorem p_ne_five : p ≠ 5 := by
  intro h5
  have : Finite (Subgroup.center V.H) :=
    Nat.finite_of_card_ne_zero (by rw [V.card]; norm_num)
  have : Nontrivial (Subgroup.center V.H) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [V.card]; norm_num)
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center V.H)
  obtain ⟨c, hc⟩ := V.scalar_of_center z.1 z.2
  have h3 : (z.1 : V.H) ^ 3 = 1 := V.center_pow_three z.1 z.2
  have hc3 : c ^ 3 = 1 := by
    have h4 := congrArg (fun w : V.H => ((w : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3)
      (ZMod p))) h3
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hc, Subgroup.coe_one, Units.val_one] at h4
    have h5 : Matrix.scalar (Fin 3) (c ^ 3) = (Matrix.scalar (Fin 3) (1 : ZMod p)) := by
      rw [map_pow, h4, map_one]
    have := congrFun (congrFun h5 0) 0
    simpa using this
  have hc1 : c ≠ 1 := by
    intro h1
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hc, h1]
    simp
  have key : ∀ c : ZMod 5, c ^ 3 = 1 → c ≠ 1 → False := by decide
  subst h5
  exact key c hc3 hc1

theorem five_ne_zero : (5 : ZMod p) ≠ 0 := by
  intro h
  have h1 : p ∣ 5 := by
    have := (ZMod.natCast_eq_zero_iff 5 p).1 (by exact_mod_cast h)
    exact this
  have h2 : p = 5 := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_five).1 h1
  exact V.p_ne_five h2

omit V in
theorem a₀A_pow_five : a₀A ^ 5 = 1 := Subtype.ext (by simpa using a₀_pow_five)

omit V in
theorem s₀A_sq : s₀A ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using s₀_mul_self)

omit V in
theorem s₀A_cube : s₀A ^ 3 = s₀A := by
  rw [pow_succ, s₀A_sq, one_mul]

omit V in
theorem s₀A_conj : s₀A * a₀A * s₀A⁻¹ = a₀A⁻¹ := Subtype.ext (by simpa using s₀_mul_a₀)

theorem exists_u : ∃ u : V.H, u ^ 5 = 1 ∧ V.E u = a₀A := by
  obtain ⟨u₁, hu₁⟩ := V.E_surjective a₀A
  refine ⟨u₁ ^ 6, ?_, ?_⟩
  · have hz : u₁ ^ 5 ∈ Subgroup.center V.H := by
      rw [← V.E_eq_one_iff, map_pow, hu₁, a₀A_pow_five]
    have h3 := V.center_pow_three _ hz
    calc (u₁ ^ 6) ^ 5 = ((u₁ ^ 5) ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul, ← pow_mul]
      _ = 1 := by rw [h3, one_pow]
  · rw [map_pow, hu₁, pow_succ, a₀A_pow_five, one_mul]

theorem exists_s {u : V.H} (hu5 : u ^ 5 = 1) (hu : V.E u = a₀A) :
    ∃ s : V.H, s * s = 1 ∧ V.E s = s₀A ∧ s * u * s⁻¹ = u⁻¹ := by
  obtain ⟨s₁, hs₁⟩ := V.E_surjective s₀A
  have hs : (s₁ ^ 3) * (s₁ ^ 3) = 1 := by
    have hz : s₁ ^ 2 ∈ Subgroup.center V.H := by
      rw [← V.E_eq_one_iff, map_pow, hs₁, s₀A_sq]
    have h3 := V.center_pow_three _ hz
    rw [← pow_add, ← pow_mul] at *
    simpa using h3
  have hEs : V.E (s₁ ^ 3) = s₀A := by rw [map_pow, hs₁, s₀A_cube]
  refine ⟨s₁ ^ 3, hs, hEs, ?_⟩
  refine V.eq_of_E_eq (n := 5) (by norm_num) ?_ ?_ ?_
  · rw [conj_pow, hu5, mul_one, mul_inv_cancel]
  · rw [inv_pow, hu5, inv_one]
  · rw [map_mul, map_mul, map_inv, map_inv, hEs, hu, s₀A_conj]

theorem frattini5 {u : V.H} (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1) {g : GL (Fin 3) (ZMod p)}
    (hg : ∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H) :
    ∃ h : V.H, ∃ k : ℕ, (h : GL (Fin 3) (ZMod p)) * g * (u : GL (Fin 3) (ZMod p)) *
      ((h : GL (Fin 3) (ZMod p)) * g)⁻¹ = (u : GL (Fin 3) (ZMod p)) ^ k := by
  have : Finite V.H := V.finite_H
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hu : orderOf u = 5 := orderOf_eq_prime hu5 hu1
  let w : V.H := ⟨g * (u : GL (Fin 3) (ZMod p)) * g⁻¹, hg u u.2⟩
  have hw5 : w ^ 5 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, w]
    rw [conj_pow]
    have : (u : GL (Fin 3) (ZMod p)) ^ 5 = 1 := by
      simpa using congrArg Subtype.val hu5
    rw [this, mul_one, mul_inv_cancel]
  have hw1 : w ≠ 1 := by
    intro h
    apply hu1
    apply Subtype.ext
    have h1 : g * (u : GL (Fin 3) (ZMod p)) * g⁻¹ = 1 := congrArg Subtype.val h
    simpa using h1
  have hwo : orderOf w = 5 := orderOf_eq_prime hw5 hw1
  have h1080 : (Nat.card V.H).factorization 5 = 1 := by
    rw [V.card_H]
    decide +kernel
  let P : Sylow 5 V.H := Sylow.ofCard (Subgroup.zpowers u) (by
    rw [Nat.card_zpowers, hu, h1080]; norm_num)
  let Q : Sylow 5 V.H := Sylow.ofCard (Subgroup.zpowers w) (by
    rw [Nat.card_zpowers, hwo, h1080]; norm_num)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq V.H Q P
  have hwQ : w ∈ (Q : Subgroup V.H) := by
    rw [Sylow.coe_ofCard]
    exact Subgroup.mem_zpowers w
  have hmem : h * w * h⁻¹ ∈ (P : Subgroup V.H) := by
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨w, hwQ, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [Sylow.coe_ofCard] at hmem
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.2 ⟨5, by norm_num, hu5⟩
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
    ((hfin.mem_powers_iff_mem_zpowers).2 hmem)
  refine ⟨h, k, ?_⟩
  have h2 := congrArg (fun x : V.H => (x : GL (Fin 3) (ZMod p))) hk
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, w] at h2
  rw [h2]
  group

theorem perfect_hom_eq (φ₁ φ₂ : V.H →* V.H) (h : ∀ x, (φ₁ x)⁻¹ * φ₂ x ∈ Subgroup.center V.H) :
    φ₁ = φ₂ := by
  have := V.perf
  let χ : V.H →* Subgroup.center V.H :=
    { toFun := fun x => ⟨(φ₁ x)⁻¹ * φ₂ x, h x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (h x) (φ₁ y)⁻¹
        show (φ₁ (x * y))⁻¹ * φ₂ (x * y) = (φ₁ x)⁻¹ * φ₂ x * ((φ₁ y)⁻¹ * φ₂ y)
        rw [map_mul, map_mul, mul_inv_rev]
        calc (φ₁ y)⁻¹ * (φ₁ x)⁻¹ * (φ₂ x * φ₂ y)
            = (φ₁ y)⁻¹ * ((φ₁ x)⁻¹ * φ₂ x) * φ₂ y := by group
          _ = ((φ₁ x)⁻¹ * φ₂ x) * (φ₁ y)⁻¹ * φ₂ y := by rw [hc]
          _ = _ := by group }
  have hker : χ.ker = ⊤ := by
    rw [eq_top_iff, ← V.perf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker χ
  refine MonoidHom.ext fun x => ?_
  have h1 : χ x = 1 := MonoidHom.mem_ker.mp (by rw [hker]; trivial)
  exact inv_mul_eq_one.mp (congrArg Subtype.val h1)

@[expose] noncomputable def conjAut {g : GL (Fin 3) (ZMod p)} (hg : ∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H) :
    V.H ≃* V.H := by
  have := V.finite_H
  let f : V.H →* V.H :=
    { toFun := fun x => ⟨g * (x : GL (Fin 3) (ZMod p)) * g⁻¹, hg x x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show g * ((x : GL (Fin 3) (ZMod p)) * (y : GL (Fin 3) (ZMod p))) * g⁻¹ =
          g * (x : GL (Fin 3) (ZMod p)) * g⁻¹ * (g * (y : GL (Fin 3) (ZMod p)) * g⁻¹)
        group }
  refine MulEquiv.ofBijective f ?_
  rw [← Finite.injective_iff_bijective]
  intro x y hxy
  apply Subtype.ext
  have h1 : g * (x : GL (Fin 3) (ZMod p)) * g⁻¹ = g * (y : GL (Fin 3) (ZMod p)) * g⁻¹ :=
    congrArg Subtype.val hxy
  simpa using h1

theorem coe_conjAut {g : GL (Fin 3) (ZMod p)} (hg : ∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H) (x : V.H) :
    ((V.conjAut hg x : V.H) : GL (Fin 3) (ZMod p)) = g * (x : GL (Fin 3) (ZMod p)) * g⁻¹ := rfl

theorem exists_induced (α : V.H ≃* V.H) :
    ∃ ψ : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6), ∀ x, V.E (α x) = ψ (V.E x) := by
  have hα : (Subgroup.center V.H).map α.toMonoidHom = Subgroup.center V.H :=
    Subgroup.map_center_eq α
  refine ⟨V.e.symm.trans ((QuotientGroup.congr _ _ α hα).trans V.e), fun x => ?_⟩
  simp only [E_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem aut_sq_eq_one (α : V.H ≃* V.H) (ψ : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
    (hψ : ∀ x, V.E (α x) = ψ (V.E x)) (hsq : ∀ y, ψ (ψ y) = y) (x : V.H) : α (α x) = x := by
  have h := V.perfect_hom_eq (α.toMonoidHom.comp α.toMonoidHom) (MonoidHom.id _) (fun x => by
    rw [← V.E_eq_one_iff]
    simp [hψ, hsq])
  exact DFunLike.congr_fun h x

end Val

end CFSG.RankThree.PartOne.A6N

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Assembly.LowTwoRank Matrix

section ZModPow

variable {M : Type*} [Group M] {p : ℕ} [NeZero p]

@[expose] def zpowZMod (ζ : M) (hζ : ζ ^ p = 1) : Multiplicative (ZMod p) →* M where
  toFun x := ζ ^ (Multiplicative.toAdd x).val
  map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' x y := by rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]

theorem zpowZMod_injective {ζ : M} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    Function.Injective (zpowZMod ζ hζ) := by
  intro x y h
  have h1 : ζ ^ (Multiplicative.toAdd x).val = ζ ^ (Multiplicative.toAdd y).val := h
  rw [pow_eq_pow_iff_modEq, hζo] at h1
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2
  exact Multiplicative.toAdd.injective h2

end ZModPow

theorem zmod_pow_eq_one {p : ℕ} (z : Multiplicative (ZMod p)) : z ^ p = 1 := by
  rw [← ofAdd_toAdd z, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem exists_elemAbelian_of_injective {G : Type*} [Group G] {L : Subgroup G} {p : ℕ}
    [NeZero p] (f : Multiplicative (ZMod p) × Multiplicative (ZMod p) →* ↥L)
    (hf : Function.Injective f) :
    ∃ E : Subgroup G, E ≤ L ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  set g := L.subtype.comp f with hg
  have hginj : Function.Injective g := L.subtype_injective.comp hf
  refine ⟨g.range, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (f y).2
  · apply Subtype.ext
    obtain ⟨ya, hya⟩ := a.2
    obtain ⟨yb, hyb⟩ := b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hya, ← hyb, ← map_mul, ← map_mul, mul_comm ya yb]
  · obtain ⟨y, rfl⟩ := hx
    rw [← map_pow]
    have hy : y ^ p = 1 := Prod.ext (by rw [Prod.pow_fst]; exact zmod_pow_eq_one _)
      (by rw [Prod.pow_snd]; exact zmod_pow_eq_one _)
    rw [hy, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv, Nat.card_prod,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod, sq]

variable {K : Type} [Field K]

@[expose] def diag3Hom : Kˣ × Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun xy := ⟨diagonal ![(xy.1 : K), (xy.2 : K), ((xy.1 * xy.2)⁻¹ : Kˣ)], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Units.val_inv_eq_inv_val, Units.val_mul]
    rw [mul_inv, mul_assoc, ← mul_assoc (xy.2 : K), mul_comm (xy.2 : K) (xy.1 : K)⁻¹,
      ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ xy.1.ne_zero, one_mul,
      mul_inv_cancel₀ xy.2.ne_zero]⟩
  map_one' := by
    apply Subtype.ext
    change diagonal _ = (1 : Matrix (Fin 3) (Fin 3) K)
    rw [← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · simp [mul_comm]
    · simp [mul_comm]
    · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Prod.fst_mul, Prod.snd_mul, Units.val_inv_eq_inv_val, Units.val_mul]
      ring

theorem diag3Hom_apply (xy : Kˣ × Kˣ) :
    ((diag3Hom xy : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(xy.1 : K), (xy.2 : K), ((xy.1 * xy.2)⁻¹ : Kˣ)] := rfl

theorem diag3Hom_injective : Function.Injective (diag3Hom (K := K)) := by
  intro a b h
  have h0 := congrArg (fun A : SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 1) h
  simp only [diag3Hom_apply, diagonal_apply_eq] at h0 h1
  exact Prod.ext (Units.ext (by simpa using h0)) (Units.ext (by simpa using h1))

@[expose] noncomputable def diagZMod {p : ℕ} [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1) :
    Multiplicative (ZMod p) × Multiplicative (ZMod p) →* ↥(StatedSL 3 K) :=
  (specialLinearGroupEquivStatedSL 3 K).toMonoidHom.comp
    (diag3Hom.comp ((zpowZMod ζ hζ).prodMap (zpowZMod ζ hζ)))

theorem diagZMod_injective {p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    Function.Injective (diagZMod ζ hζ) :=
  (specialLinearGroupEquivStatedSL 3 K).injective.comp
    (diag3Hom_injective.comp (Prod.map_injective.mpr
      ⟨zpowZMod_injective hζo hζ, zpowZMod_injective hζo hζ⟩))

theorem coe_diagZMod {p : ℕ} [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (x : Multiplicative (ZMod p) × Multiplicative (ZMod p)) :
    (((diagZMod ζ hζ x : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![((zpowZMod ζ hζ x.1 : Kˣ) : K), ((zpowZMod ζ hζ x.2 : Kˣ) : K),
        ((zpowZMod ζ hζ x.1 * zpowZMod ζ hζ x.2)⁻¹ : Kˣ)] := rfl

noncomputable abbrev projSL3 (K : Type) [Field K] :
    ↥(StatedSL 3 K) →* StatedProj (StatedSL 3 K) :=
  QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))

theorem exists_scalar_of_proj_eq_one {x : ↥(StatedSL 3 K)} (hx : projSL3 K x = 1) :
    ∃ u : Kˣ, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (u : K) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
  obtain ⟨u, hu⟩ := hx
  exact ⟨u, by rw [← hu]; rfl⟩

theorem diagZModProj_injective {p : ℕ} [NeZero p] (hp : p.Prime) (hp3 : p ≠ 3) {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    Function.Injective ((projSL3 K).comp (diagZMod ζ hζ)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨u, hu⟩ := exists_scalar_of_proj_eq_one hx
  rw [coe_diagZMod] at hu
  have e0 := congrFun (congrFun hu 0) 0
  have e1 := congrFun (congrFun hu 1) 1
  have e2 := congrFun (congrFun hu 2) 2
  simp only [diagonal_apply_eq, Matrix.scalar_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
  have h0 : zpowZMod ζ hζ x.1 = u := Units.ext (by simpa using e0)
  have h1 : zpowZMod ζ hζ x.2 = u := Units.ext (by simpa using e1)
  have h2 : (zpowZMod ζ hζ x.1 * zpowZMod ζ hζ x.2)⁻¹ = u := Units.ext (by simpa using e2)
  rw [h0, h1] at h2
  have hu3 : u ^ 3 = 1 := by
    have : u * (u * u)⁻¹ = u * u := by rw [h2]
    calc u ^ 3 = (u * u) * u := by rw [pow_succ, sq]
      _ = 1 := by
        rw [← this]
        group
  have hup : u ^ p = 1 := by
    rw [← h0, ← map_pow, zmod_pow_eq_one, map_one]
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hp3)
  have hu1 : u = 1 := by
    have hd : orderOf u ∣ Nat.gcd 3 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu3) (orderOf_dvd_of_pow_eq_one hup)
    rw [hcop.gcd_eq_one, Nat.dvd_one] at hd
    exact orderOf_eq_one_iff.mp hd
  have hx1 : x.1 = 1 := zpowZMod_injective hζo hζ (by rw [h0, hu1, map_one])
  have hx2 : x.2 = 1 := zpowZMod_injective hζo hζ (by rw [h1, hu1, map_one])
  exact Prod.ext hx1 hx2

theorem exists_unit_orderOf [Finite K] {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_units] at hpq
  exact exists_prime_orderOf_dvd_card' p hpq

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB

module

public import CFSG.Quasithin.Vol2.Ch10SecV1SI
public import CFSG.Quasithin.Vol2.Ch10SecV1SH

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {H : Type} [Group H] {L : Subgroup H} {K : Type} [Field K]
  {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)} {I : Subgroup H}

namespace NatCoord

@[expose] def cactHom (c : NatCoord φ I) :
    Subgroup.normalizer (I : Set H) →* Equiv.Perm (Fin 3 → K) where
  toFun g := ⟨c.cact g g.2, c.cact (g : H)⁻¹ (Subgroup.inv_mem _ g.2), c.cact_inv_cact g g.2,
    c.cact_cact_inv g g.2⟩
  map_one' := Equiv.ext fun x => c.cact_one (Subgroup.one_mem _) x
  map_mul' g g' := Equiv.ext fun x => c.cact_mul g g' g.2 g'.2 x

theorem cactHom_apply (c : NatCoord φ I) (g : Subgroup.normalizer (I : Set H)) (x : Fin 3 → K) :
    c.cactHom g x = c.cact g g.2 x := rfl

theorem perm_pow_comm {f : Equiv.Perm (Fin 3 → K)} {D : Matrix (Fin 3) (Fin 3) K}
    (hD : ∀ x, f (D *ᵥ x) = D *ᵥ f x) (n : ℕ) (x : Fin 3 → K) :
    (f ^ n) (D *ᵥ x) = D *ᵥ (f ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hD, ih]

theorem comm_mem_O2 (c : NatCoord φ I) (hLn : L.Normal) {g : H}
    (hg : g ∈ Subgroup.normalizer (I : Set H)) (l : ↥L)
    (hcomm : ∀ x, c.cact g hg (mat φ l *ᵥ x) = mat φ l *ᵥ c.cact g hg x) :
    g * l * g⁻¹ * (l : H)⁻¹ ∈ O2 L := by
  have hmem : g * l * g⁻¹ * (l : H)⁻¹ ∈ L := L.mul_mem (hLn.conj_mem _ l.2 g) (L.inv_mem l.2)
  refine (mat_eq_one_iff φ ⟨_, hmem⟩).mp (eq_one_of_mulVec fun x => ?_)
  set G : Subgroup.normalizer (I : Set H) := ⟨g, hg⟩
  set Λ : Subgroup.normalizer (I : Set H) := ⟨l, c.le_normalizer l.2⟩
  have hΛ : ∀ y, c.cactHom Λ y = mat φ l *ᵥ y := c.cact_of_mem l
  have hΛi : ∀ y, c.cactHom Λ⁻¹ y = mat φ l⁻¹ *ᵥ y := c.cact_of_mem l⁻¹
  rw [← c.cact_of_mem]
  show c.cactHom (G * Λ * G⁻¹ * Λ⁻¹) x = x
  rw [map_mul, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, hΛi, hΛ, cactHom_apply, hcomm]
  show mat φ l *ᵥ c.cactHom G (c.cactHom G⁻¹ (mat φ l⁻¹ *ᵥ x)) = x
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply,
    Matrix.mulVec_mulVec, ← mat_mul, mul_inv_cancel, mat_one, Matrix.one_mulVec]

theorem exists_y [Finite H] (c : NatCoord φ I) (hLn : L.Normal) {h : H}
    (hhI : h ∈ Subgroup.normalizer (I : Set H)) (hh3 : h ^ 3 ∈ L) (hhL : h ∉ L) :
    ∃ y : H, ∃ hy : y ∈ Subgroup.normalizer (I : Set H), y ^ 3 = 1 ∧ y ∉ L ∧
      ∀ d : Fin 3 → K, (∀ i, d i ^ 3 = 1) → ∀ x,
        c.cact y hy (Matrix.diagonal d *ᵥ x) = Matrix.diagonal d *ᵥ c.cact y hy x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ⟩ := c.exists_semilinear hhI (mem_normalizer_of_normal hLn h)
  set Hh : Subgroup.normalizer (I : Set H) := ⟨h, hhI⟩ with hHh
  set l₃ : ↥L := ⟨h ^ 3, hh3⟩ with hl₃
  have hT3 : ∀ x, c.cact h hhI (c.cact h hhI (c.cact h hhI x)) = mat φ l₃ *ᵥ x := fun x => by
    rw [← c.cact_of_mem l₃]
    have e : (⟨(l₃ : H), c.le_normalizer l₃.2⟩ : Subgroup.normalizer (I : Set H)) = Hh ^ 3 :=
      Subtype.ext (by simp [hl₃, hHh])
    show c.cactHom Hh (c.cactHom Hh (c.cactHom Hh x)) =
      c.cactHom ⟨(l₃ : H), c.le_normalizer l₃.2⟩ x
    rw [e, map_pow]
    simp [pow_succ, Equiv.Perm.mul_apply]
  have hσ3 := pow_three_eq hσ (det_mat φ l₃) hT3
  obtain ⟨P, hPdet, hP3, hPcomm⟩ := exists_B (c.cact_add h hhI) hσ (det_mat φ l₃) hT3
  obtain ⟨l₀, hl₀⟩ := exists_mat φ (specialLinearGroupEquivStatedSL 3 K ⟨P, hPdet⟩)
  have hl₀' : mat φ l₀ = P := hl₀
  set Y₀ : Subgroup.normalizer (I : Set H) := ⟨l₀, c.le_normalizer l₀.2⟩ * Hh with hY₀
  have hact : ∀ x, c.cactHom Y₀ x = P *ᵥ c.cact h hhI x := fun x => by
    rw [hY₀, map_mul, Equiv.Perm.mul_apply, cactHom_apply, c.cact_of_mem l₀, hl₀']
    rfl
  have hY3 : c.cactHom (Y₀ ^ 3) = 1 := Equiv.ext fun x => by
    rw [map_pow]
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, hact, Equiv.Perm.one_apply]
    exact hP3 x
  have hmk : ∀ m : ℕ, (QuotientGroup.mk ((Y₀ : H) ^ m) : H ⧸ L) = QuotientGroup.mk (h ^ m) := by
    intro m
    have : ((l₀ : H) : H ⧸ L) = 1 := (QuotientGroup.eq_one_iff _).mpr l₀.2
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow, hY₀, Subgroup.coe_mul, QuotientGroup.mk_mul,
      this, one_mul]
  have hY3L : ((Y₀ ^ 3 : Subgroup.normalizer (I : Set H)) : H) ∈ L := by
    rw [← QuotientGroup.eq_one_iff, Subgroup.coe_pow, hmk, QuotientGroup.mk_pow,
      ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr hh3]
  have hO := c.mem_pCore_of_cact ⟨_, hY3L⟩ fun x => congrArg (fun f => f x) hY3
  obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (⟨⟨_, hY3L⟩, hO⟩ : CFSG.pCore 2 ↥L)
  have hj' : ((Y₀ : H) ^ 3) ^ 2 ^ j = 1 := by
    have := congrArg (fun z : CFSG.pCore 2 ↥L => ((z : ↥L) : H)) hj
    simpa using this
  refine ⟨((Y₀ ^ 2 ^ j : Subgroup.normalizer (I : Set H)) : H), (Y₀ ^ 2 ^ j).2, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, hj']
  · intro hyL
    have h1 : (QuotientGroup.mk h : H ⧸ L) ^ 2 ^ j = 1 := by
      rw [← QuotientGroup.mk_pow, ← hmk, ← Subgroup.coe_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hyL
    have h2 : (QuotientGroup.mk h : H ⧸ L) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hh3
    have h3 : orderOf (QuotientGroup.mk h : H ⧸ L) = 1 := by
      have hg := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 3)),
        Nat.dvd_one] at hg
    exact hhL ((QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3))
  · intro d hd x
    have hfix : ∀ i, σ (d i) = d i := fun i => fix_of_pow_three hσ3 (hd i)
    have hY₀c : ∀ x, c.cactHom Y₀ (Matrix.diagonal d *ᵥ x) =
        Matrix.diagonal d *ᵥ c.cactHom Y₀ x := fun x => by
      rw [hact, hact]
      exact hPcomm d hfix x
    show c.cactHom (Y₀ ^ 2 ^ j) (Matrix.diagonal d *ᵥ x) =
      Matrix.diagonal d *ᵥ c.cactHom (Y₀ ^ 2 ^ j) x
    rw [map_pow]
    exact perm_pow_comm hY₀c _ x

end NatCoord

end CFSG.Quasithin.Vol2.Ch10.V1C.A319

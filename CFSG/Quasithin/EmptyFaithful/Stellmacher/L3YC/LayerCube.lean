module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.V4Aut
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.SL3Scalar
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.BlockRep

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Open (pCoreOf)

namespace Stellmacher.L3YC

section Matrices

theorem matrix_pow_six {k : ℕ} (hk : k ≤ 2) (B : Matrix (Fin k) (Fin k) (ZMod 2))
    (hB : B.det = 1) : B ^ 6 = 1 := by
  interval_cases k
  · exact Subsingleton.elim _ _
  · revert B; decide
  · revert B; decide

theorem matrix_pow_three_of_pow {k : ℕ} (hk : k ≤ 2) (B : Matrix (Fin k) (Fin k) (ZMod 2))
    {m : ℕ} (hB : B ^ 3 ^ m = 1) : B ^ 3 = 1 := by
  have hdet : B.det = 1 := by
    have h1 := congrArg Matrix.det hB
    rw [Matrix.det_pow, Matrix.det_one] at h1
    have h2 : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
    rcases h2 B.det with h | h
    · rw [h, zero_pow (by positivity)] at h1
      exact absurd h1 (by decide)
    · exact h
  have h6 : B ^ 6 = 1 := matrix_pow_six hk B hdet
  have h := pow_gcd_eq_one.mpr ⟨hB, h6⟩
  have hg : Nat.gcd (3 ^ m) 6 ∣ 3 := by
    rcases m with _ | m
    · simp
    · have e1 : 3 ^ (m + 1) = 3 * 3 ^ m := by rw [pow_succ']
      have e2 : (6 : ℕ) = 3 * 2 := by norm_num
      rw [e1, e2, Nat.gcd_mul_left]
      have : Nat.gcd (3 ^ m) 2 = 1 := Nat.Coprime.pow_left m (by norm_num)
      rw [this]
  exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one h).trans hg)

end Matrices

section Rep

variable {F : Type} [Field F] {k : ℕ}

def rep (B : Matrix (Fin k) (Fin k) F) (w : Fin k → Fin 3 → F) : Fin k → Fin 3 → F :=
  fun i => ∑ j, B i j • w j

theorem rep_one (w : Fin k → Fin 3 → F) : rep (1 : Matrix (Fin k) (Fin k) F) w = w := by
  ext i m
  simp only [rep, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

theorem rep_mul (B C : Matrix (Fin k) (Fin k) F) (w : Fin k → Fin 3 → F) :
    rep (B * C) w = rep B (rep C w) := by
  ext i m
  simp only [rep, Matrix.mul_apply, Finset.sum_apply, Finset.sum_smul, Finset.smul_sum, mul_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]

theorem rep_single (B : Matrix (Fin k) (Fin k) F) (i j : Fin k) :
    rep B (Pi.single j (Pi.single 0 1)) i 0 = B i j := by
  rw [rep, Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

theorem eq_of_rep_eq {B C : Matrix (Fin k) (Fin k) F} (h : ∀ w, rep B w = rep C w) : B = C := by
  ext i j
  rw [← rep_single B i j, ← rep_single C i j, h]

end Rep

section Layer

variable {G : Type} [Group G]

theorem layer_cube_trivial {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) {k : ℕ}
    (hk : k ≤ 2) {L V Z : Subgroup G} (α : ↥L →* ↥(StatedSL 3 F)) (hα : IsModO2Surj L α)
    (dual : Bool) (hV : IsSumOfNaturalModulesVia L V Z α dual k) {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hg0 : ∀ x ∈ L, g * x * g⁻¹ * x⁻¹ ∈ pCoreOf 2 L) {m : ℕ} (hgm : g ^ 3 ^ m = 1) :
    ∀ v ∈ V, v⁻¹ * (g ^ 3 * v * (g ^ 3)⁻¹) ∈ Z := by
  classical
  obtain ⟨hLV, hZV, β, hβs, hβk, hβe⟩ := hV
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF).symm
  have h01 : ∀ c : F, c = 0 ∨ c = 1 := by
    intro c
    have h2 : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
    rcases h2 (e c) with h | h
    · left
      exact e.injective (by rw [h, map_zero])
    · right
      exact e.injective (by rw [h, map_one])
  let a0 : MulAut ↥V := actAut hgV
  have hψ : ∀ v : ↥V, ((a0 v : ↥V) : G) = g * v * g⁻¹ := fun v => rfl
  have hker : β.ker ≤ (β.comp a0.toMonoidHom).ker := by
    intro z hz
    rw [hβk] at hz
    have hz' : (z : G) ∈ Z := hz
    have h1 : a0 z ∈ β.ker := by
      rw [hβk]
      show g * z * g⁻¹ ∈ Z
      exact (Subgroup.mem_normalizer_iff.mp hgZ _).mp hz'
    exact h1
  let φ : Multiplicative (Fin k → Fin 3 → F) →* Multiplicative (Fin k → Fin 3 → F) :=
    MonoidHom.liftOfSurjective β hβs ⟨β.comp a0.toMonoidHom, hker⟩
  have hφ : ∀ v : ↥V, φ (β v) = β (a0 v) := fun v =>
    MonoidHom.liftOfRightInverse_comp_apply β _ _ ⟨β.comp a0.toMonoidHom, hker⟩ v
  let Φ : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F) :=
    AddMonoidHom.mk' (fun w => Multiplicative.toAdd (φ (Multiplicative.ofAdd w)))
      (fun x y => by simp [ofAdd_add, map_mul, toAdd_mul])
  have hΦ : ∀ v : ↥V, Φ (Multiplicative.toAdd (β v)) = Multiplicative.toAdd (β (a0 v)) := by
    intro v
    show Multiplicative.toAdd (φ (Multiplicative.ofAdd (Multiplicative.toAdd (β v)))) = _
    rw [ofAdd_toAdd, hφ]
  let S : Set (Matrix (Fin 3) (Fin 3) F) := {M | ∃ h ∈ StatedSL 3 F, moduleAct dual h = M}
  have hcomm : ∀ A ∈ S, ∀ w : Fin k → Fin 3 → F,
      Φ (fun i => A.mulVec (w i)) = fun i => A.mulVec (Φ w i) := by
    rintro A ⟨h, hh, rfl⟩ w
    obtain ⟨a, ha⟩ := hα.1 ⟨h, hh⟩
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
    have hw : w = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    have hah : ((α a : ↥(StatedSL 3 F)) : GL (Fin 3) F) = h := congrArg Subtype.val ha
    have hav : (a : G) * u * (a : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV a.2) u).mp u.2
    let v : ↥V := ⟨a * u * a⁻¹, hav⟩
    have hAv : (fun i => (moduleAct dual h).mulVec (w i)) = Multiplicative.toAdd (β v) := by
      funext i
      rw [hw, hβe a u v rfl i, hah]
    have ha' : (g * a * g⁻¹ : G) ∈ L := (Subgroup.mem_normalizer_iff.mp hgL a).mp a.2
    let a' : ↥L := ⟨g * a * g⁻¹, ha'⟩
    have hαa' : α a' = α a := by
      obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.mp (hg0 a a.2)
      have h1 : o = a' * a⁻¹ := Subtype.ext (by simpa [a'] using hoe)
      have h2 : α o = 1 := by
        have : o ∈ α.ker := by rw [hα.2]; exact ho
        exact this
      have h3 : a' = o * a := by rw [h1]; group
      rw [h3, map_mul, h2, one_mul]
    rw [hAv, hΦ, hw, hΦ]
    funext i
    have hcoe : ((a0 v : ↥V) : G) = (a' : G) * ((a0 u : ↥V) : G) * (a' : G)⁻¹ := by
      rw [hψ, hψ]
      show g * (↑a * ↑u * (↑a)⁻¹) * g⁻¹ = (g * ↑a * g⁻¹) * (g * ↑u * g⁻¹) * (g * ↑a * g⁻¹)⁻¹
      group
    have := hβe a' (a0 u) (a0 v) hcoe i
    rw [this, hαa', hah]
  have hS : ∀ X : Matrix (Fin 3) (Fin 3) F, (∀ A ∈ S, A * X = X * A) → X = 0 ∨ X = 1 :=
    fun X hX => end_scalar_of_commutes hF dual X (fun h hh => hX _ ⟨h, hh, rfl⟩)
  obtain ⟨B, hB⟩ := exists_block_rep h01 S hS Φ hcomm
  have hΦrep : ∀ w, Φ w = rep B w := fun w => funext (hB w)
  have hrep : ∀ n : ℕ, ∀ w, (⇑Φ)^[n] w = rep (B ^ n) w := by
    intro n
    induction n with
    | zero => intro w; simp [rep_one]
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', ih, pow_succ', rep_mul, hΦrep]
  have hit : ∀ n : ℕ, ∀ v : ↥V, Multiplicative.toAdd (β ((a0 ^ n) v)) =
      (⇑Φ)^[n] (Multiplicative.toAdd (β v)) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply', ← ih, pow_succ', MulAut.mul_apply, hΦ]
  have ha0m : a0 ^ 3 ^ m = 1 := by
    show actAut hgV ^ 3 ^ m = 1
    rw [actAut_pow, actAut_eq_one_iff]
    intro x _
    rw [hgm]
    group
  have hBm : B ^ 3 ^ m = 1 := by
    refine eq_of_rep_eq fun w => ?_
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
    have hw : w = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    rw [← hrep, rep_one, hw, ← hit, ha0m]
    rfl
  have hBe : (B.map e) ^ 3 ^ m = 1 := by
    have h1 : (e.toRingHom.mapMatrix (B ^ 3 ^ m) : Matrix (Fin k) (Fin k) (ZMod 2)) = 1 := by
      rw [hBm, map_one]
    rw [map_pow] at h1
    exact h1
  have hB3e : (B.map e) ^ 3 = 1 := matrix_pow_three_of_pow hk _ hBe
  have hB3 : B ^ 3 = 1 := by
    have h1 : (e.toRingHom.mapMatrix (B ^ 3) : Matrix (Fin k) (Fin k) (ZMod 2)) = 1 := by
      rw [map_pow]
      exact hB3e
    have h2 : (e.toRingHom.mapMatrix (B ^ 3) : Matrix (Fin k) (Fin k) (ZMod 2)) =
        e.toRingHom.mapMatrix 1 := by rw [h1, map_one]
    exact (Matrix.map_injective e.injective) h2
  intro v hv
  let v' : ↥V := ⟨v, hv⟩
  have h1 : Multiplicative.toAdd (β ((a0 ^ 3) v')) = Multiplicative.toAdd (β v') := by
    rw [hit, hrep, hB3, rep_one]
  have h2 : β ((a0 ^ 3) v') = β v' := Multiplicative.toAdd.injective h1
  have h3 : (v'⁻¹ * (a0 ^ 3) v' : ↥V) ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  rw [hβk] at h3
  have h4 : ((a0 ^ 3) v' : ↥V) = ⟨g ^ 3 * v * (g ^ 3)⁻¹, (Subgroup.mem_normalizer_iff.mp
      (pow_mem hgV 3) v).mp hv⟩ := by
    have : a0 ^ 3 = actAut (pow_mem hgV 3) := actAut_pow hgV 3
    rw [this]
    rfl
  have h5 : (((v'⁻¹ * (a0 ^ 3) v' : ↥V)) : G) = v⁻¹ * (g ^ 3 * v * (g ^ 3)⁻¹) := by
    rw [Subgroup.coe_mul, h4]
    rfl
  have h6 := (Subgroup.mem_subgroupOf.mp h3)
  rw [h5] at h6
  exact h6

end Layer

end Stellmacher.L3YC

end CFSG.Quasithin

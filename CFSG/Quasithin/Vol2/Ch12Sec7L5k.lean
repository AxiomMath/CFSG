module

public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

@[expose] def L34CoverFact : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSL 3 2 2 (K ⧸ Subgroup.center K) →
    ∀ E : Subgroup K, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
      Nat.card ↥E = 16 * Nat.card ↥(E ⊓ Subgroup.center K) →
      ∀ z ∈ Subgroup.center K, z ^ 2 = 1

namespace S127.L5

theorem pow_eq_one_or_eq_of_sq_eq_one {M : Type} [Monoid M] {a : M} (ha : a ^ 2 = 1) (n : ℕ) :
    a ^ n = 1 ∨ a ^ n = a := by
  induction n with
  | zero => exact Or.inl (pow_zero a)
  | succ n ih =>
    rcases ih with h | h
    · right
      rw [pow_succ, h, one_mul]
    · left
      rw [pow_succ, h, ← sq, ha]

theorem exists_eq_pow_ofAdd_one {n : ℕ} [NeZero n] (y : Multiplicative (ZMod n)) :
    ∃ k : ℕ, y = Multiplicative.ofAdd (1 : ZMod n) ^ k :=
  ⟨(Multiplicative.toAdd y).val, by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]
    rfl⟩

theorem card_center_dvd_four
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(Subgroup.center K)) (hpsl : IsPSL 3 2 2 (K ⧸ Subgroup.center K))
    (h2 : ∀ z ∈ Subgroup.center K, z ^ 2 = 1) : Nat.card ↥(Subgroup.center K) ∣ 4 := by
  classical
  have : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  set q : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hqk : q.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  set h₀ := CFSG.RankThree.PerfectCover.hopfLift q hqs hqk.le with hh₀
  have hmap : (CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ Subgroup.center K)).map h₀ =
      Subgroup.center K :=
    (CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hqs hqk.le).trans hqk
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hpsl
  let ψ : ↥(CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ Subgroup.center K)) →*
      ↥(Subgroup.center K) :=
    MonoidHom.codRestrict
      (h₀.comp (CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ Subgroup.center K)).subtype)
      _ fun m => hmap.le (Subgroup.mem_map_of_mem _ m.2)
  have hψs : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨m, hm, rfl⟩ := hmap.ge hz
    exact ⟨⟨m, hm⟩, rfl⟩
  let ε := (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (K ⧸ Subgroup.center K))
  set φ := ψ.comp (ε.toMonoidHom.comp e.symm.toMonoidHom) with hφ
  have hφs : Function.Surjective φ := hψs.comp (ε.surjective.comp e.symm.surjective)
  have hsq : ∀ z : ↥(Subgroup.center K), z ^ 2 = 1 := fun z =>
    Subtype.ext (by simpa using h2 z z.2)
  have hgen : Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 3 2 2) = 3 := by
    simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.genericOrders]
  have hgen1 : ∀ x : CFSG.Blueprint.Multiplier.generic .PSL 3 2 2, φ (x, 1) = 1 := by
    intro x
    have h3 : φ (x, 1) ^ 3 = 1 := by
      rw [← map_pow]
      have hx : x ^ 3 = 1 := by
        have h := (pow_card_eq_one' : x ^ Nat.card _ = 1)
        rwa [hgen] at h
      have : ((x, 1) : _ × CFSG.Blueprint.Multiplier.exceptional .PSL 3 2 2) ^ 3 = 1 := by
        rw [Prod.pow_def, hx, one_pow]
        rfl
      rw [this, map_one]
    calc φ (x, 1) = φ (x, 1) ^ 3 * (φ (x, 1) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, hsq, inv_one, one_mul]
  have hne : NeZero (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 2 2).1 := ⟨by decide⟩
  have hne' : NeZero (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 2 2).2 := ⟨by decide⟩
  set a := φ (1, (Multiplicative.ofAdd 1, 1)) with ha
  set b := φ (1, (1, Multiplicative.ofAdd 1)) with hb
  have hA : ∀ y, φ (1, (y, 1)) = 1 ∨ φ (1, (y, 1)) = a := by
    intro y
    obtain ⟨k, rfl⟩ := exists_eq_pow_ofAdd_one y
    have : ((1, (Multiplicative.ofAdd 1 ^ k, 1)) :
        CFSG.Blueprint.Multiplier.generic .PSL 3 2 2 ×
          CFSG.Blueprint.Multiplier.exceptional .PSL 3 2 2) =
        (1, (Multiplicative.ofAdd 1, 1)) ^ k := by
      simp [Prod.pow_def]
    rw [this, map_pow]
    exact pow_eq_one_or_eq_of_sq_eq_one (hsq a) k
  have hB : ∀ y, φ (1, (1, y)) = 1 ∨ φ (1, (1, y)) = b := by
    intro y
    obtain ⟨k, rfl⟩ := exists_eq_pow_ofAdd_one y
    have : ((1, (1, Multiplicative.ofAdd 1 ^ k)) :
        CFSG.Blueprint.Multiplier.generic .PSL 3 2 2 ×
          CFSG.Blueprint.Multiplier.exceptional .PSL 3 2 2) =
        (1, (1, Multiplicative.ofAdd 1)) ^ k := by
      simp [Prod.pow_def]
    rw [this, map_pow]
    exact pow_eq_one_or_eq_of_sq_eq_one (hsq b) k
  let F : Bool × Bool → ↥(Subgroup.center K) := fun ij =>
    (if ij.1 then a else 1) * (if ij.2 then b else 1)
  have hFs : Function.Surjective F := by
    intro z
    obtain ⟨⟨x, y₁, y₂⟩, rfl⟩ := hφs z
    have hm : ((x, (y₁, y₂)) : CFSG.Blueprint.Multiplier.generic .PSL 3 2 2 ×
        CFSG.Blueprint.Multiplier.exceptional .PSL 3 2 2) =
        (x, 1) * (1, (y₁, 1)) * (1, (1, y₂)) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    rw [hm, map_mul, map_mul, hgen1, one_mul]
    rcases hA y₁ with h1 | h1 <;> rcases hB y₂ with h3 | h3
    · exact ⟨(false, false), by simp [F, h1, h3]⟩
    · exact ⟨(false, true), by simp [F, h1, h3]⟩
    · exact ⟨(true, false), by simp [F, h1, h3]⟩
    · exact ⟨(true, true), by simp [F, h1, h3]⟩
  have hle : Nat.card ↥(Subgroup.center K) ≤ 4 := by
    have := Nat.card_le_card_of_surjective F hFs
    simpa using this
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at hle ⊢
  have hk2 : k ≤ 2 := by
    by_contra hk2
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (pow_dvd_pow 2 hk2).trans (by norm_num)

end S127.L5

end CFSG.Quasithin.H13

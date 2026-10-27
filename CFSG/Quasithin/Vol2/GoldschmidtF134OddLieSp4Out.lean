module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSp4Inner
public import CFSG.Quasithin.Vol2.F134LieSp4

public section

namespace CFSG.Quasithin.H13.NQCore.Psp4

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Lin2.Five (tauAut tauAut_mul_self)

theorem tauAut_pow_two_mul {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : Nat.card F = 2 ^ n) :
    (tauAut : MulAut (StatedProj (StatedSp 2 F))) ^ (2 * n) = 1 := by
  rw [pow_mul, pow_two, tauAut_mul_self, ← map_pow, frobAut_pow_card hn, map_one]

theorem exists_forall_eq_conj_mul_pow_pow {L : Type*} [Group L] {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hn : Nat.card F = 2 ^ n) (e : L ≃* StatedProj (StatedSp 2 F)) :
    ∃ τ : MulAut L, τ ^ (2 * n) = 1 ∧
      ∀ α : MulAut L, ∃ (x : L) (m : ℕ), α = MulAut.conj x * τ ^ m := by
  refine ⟨(MulAut.congr e).symm tauAut, ?_, fun α => ?_⟩
  · rw [← map_pow, tauAut_pow_two_mul hn, map_one]
  · obtain ⟨x, m, hx⟩ := CFSG.Quasithin.F134.Sp4.exists_eq_conj_mul_tauAut_pow (MulAut.congr e α)
    refine ⟨e.symm x, m, (MulAut.congr e).injective ?_⟩
    rw [map_mul, map_pow, MulEquiv.apply_symm_apply, hx]
    congr 1
    ext y
    simp [MulAut.congr_apply]

theorem pow_mem_inner {L : Type*} [Group L] {τ : MulAut L} {m : ℕ} (hτm : τ ^ m = 1)
    (hτ : ∀ α : MulAut L, ∃ (x : L) (k : ℕ), α = MulAut.conj x * τ ^ k) (α : MulAut L) :
    ∃ y : L, α ^ m = MulAut.conj y := by
  have := CFSG.Quasithin.F134.Sp4.range_conj_normal L
  set I := (MulAut.conj : L →* MulAut L).range with hI
  obtain ⟨x, k, rfl⟩ := hτ α
  have hx : (QuotientGroup.mk' I) (MulAut.conj x) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  have h1 : (QuotientGroup.mk' I) ((MulAut.conj x * τ ^ k) ^ m) = 1 := by
    rw [map_pow, map_mul, hx, one_mul, map_pow, ← pow_mul, mul_comm, pow_mul, ← map_pow, hτm,
      map_one, one_pow]
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨y, hy.symm⟩

theorem pow_centralizes {A : Type*} [Group A] [Finite A] {L U P : Subgroup A} [L.Normal]
    (hZ : Subgroup.center L = ⊥) (hU : IsSylowTwoOf U L) (hPL : P ≤ L) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (hPU : ∀ y ∈ P, ∀ u ∈ U, y * u * y⁻¹ ∈ U)
    {τ : MulAut L} {m : ℕ} (hτm : τ ^ m = 1)
    (hτ : ∀ α : MulAut L, ∃ (x : L) (k : ℕ), α = MulAut.conj x * τ ^ k) {t : A}
    (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (htU : t ∈ Subgroup.normalizer (U : Set A))
    (htP : t ∈ Subgroup.normalizer (P : Set A)) {y : A} (hy : y ∈ P) :
    t ^ m * y * (t ^ m)⁻¹ = y := by
  obtain ⟨x, hx⟩ := pow_mem_inner hτm hτ (MulAut.conjNormal (H := L) t)
  refine conj_eq_of_conjNormal_eq_conj_odd hZ hU hPL hp2 hP hPU ?_ (pow_mem htU m)
    (pow_mem htP m) (x := x) ?_ hy
  · exact ht2.to_le (Subgroup.zpowers_le.mpr (pow_mem (Subgroup.mem_zpowers t) m))
  · rw [map_pow]
    exact hx

end CFSG.Quasithin.H13.NQCore.Psp4

module

public import CFSG.Quasithin.MS93.S37Nat
public import CFSG.Quasithin.MS93.S38PU
public import CFSG.Quasithin.MS93.M15Lift

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_pow_eq_mul_pow {x y d : G} (h1 : x * y * x⁻¹ = y * d) (h2 : x * d * x⁻¹ = d)
    (m : ℕ) : x ^ m * y * (x ^ m)⁻¹ = y * d ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hd : x * d ^ m * x⁻¹ = d ^ m := by rw [← conj_pow, h2]
    calc x ^ (m + 1) * y * (x ^ (m + 1))⁻¹ = x * (x ^ m * y * (x ^ m)⁻¹) * x⁻¹ := by group
      _ = x * (y * d ^ m) * x⁻¹ := by rw [ih]
      _ = (x * y * x⁻¹) * (x * d ^ m * x⁻¹) := by group
      _ = y * d * d ^ m := by rw [h1, hd]
      _ = y * d ^ (m + 1) := by rw [mul_assoc, ← pow_succ']

theorem eq_one_of_pow_two_pow_of_pow_odd {g : G} {e m : ℕ} (hm : Odd m) (h1 : g ^ 2 ^ e = 1)
    (h2 : g ^ m = 1) : g = 1 := by
  have hc : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hm)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hc.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem conj_eq_of_odd {x y d : G} {e m : ℕ} (hm : Odd m) (hx : x ^ m = 1)
    (h1 : x * y * x⁻¹ = y * d) (h2 : x * d * x⁻¹ = d) (hd : d ^ 2 ^ e = 1) :
    x * y * x⁻¹ = y := by
  have h := conj_pow_eq_mul_pow h1 h2 m
  rw [hx, one_mul, inv_one, mul_one, left_eq_mul] at h
  rw [h1, eq_one_of_pow_two_pow_of_pow_odd hm hd h, mul_one]

variable [Finite G] {M T L : Subgroup G}

theorem vq_eq_uq (h : PUHyp M T L) (h36 : S36) (hb : critDist (puAmalgam h.le) = 2) {k : ℕ}
    {F : Type} [Field F] [Fintype F] {α : ↥L →* ↥(StatedSp 2 F)} (hk : 2 ≤ k)
    (hF : Fintype.card F = 2 ^ k) (hα : Function.Surjective α)
    (hn : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1) :
    Vq M L = Uq M T L := by
  obtain ⟨hV | hV, -⟩ := h36 G M T L h hb
  · exact hV
  · exfalso
    obtain ⟨-, hX, n, F', _, _, β, hF', hβ, hβn, -⟩ := hV
    refine sl3_sp4U_false h hF' hβ (fun y hy => ?_)
      (Or.inl ⟨k, F, inferInstance, inferInstance, α, hk, hF, hα, ?_⟩)
    · rw [MonoidHom.mem_ker]
      refine eq_one_of_isSumOfNaturalModulesVia hβn fun v hv => ?_
      refine commute_of_mem_pCore h.L_le h.le_normalizer hy ?_
      rw [hX]
      exact le_sup_right (a := Zq M L) hv
    · rwa [← h.Uq_inf_Zq]

section Kernel

variable {F : Type} [Field F]
  (N : Sp4NatData L (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) F)

omit [Finite G] in
include N in
theorem inv_mul_conj_mem {y : G} (hy : y ∈ L) (hαy : N.α ⟨y, hy⟩ = 1) {u : G}
    (hu : u ∈ Uq M T L) :
    u⁻¹ * (y * u * y⁻¹) ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  have hyu : y * u * y⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (N.hLU hy) u).1 hu
  have hco : N.co ⟨u, hu⟩ = N.co ⟨y * u * y⁻¹, hyu⟩ := by
    have := N.β_equiv ⟨y, hy⟩ ⟨u, hu⟩ ⟨y * u * y⁻¹, hyu⟩ rfl
    rw [hαy, mat_one, Matrix.one_mulVec] at this
    exact this.symm
  exact (N.co_eq_co_iff _ _).1 hco

variable (h : PUHyp M T L)
include h N

theorem conj_eq_of_odd_of_mem_Uq {y : G} (hy : y ∈ L) (hαy : N.α ⟨y, hy⟩ = 1) {m : ℕ}
    (hm : Odd m) (hym : y ^ m = 1) {u : G} (hu : u ∈ Uq M T L) : y * u * y⁻¹ = u := by
  have hd := inv_mul_conj_mem N hy hαy hu
  refine conj_eq_of_odd (e := 1) hm hym (d := u⁻¹ * (y * u * y⁻¹)) (by group) ?_ ?_
  · have := Subgroup.mem_centralizer_iff.1 hd.2 y hy
    rw [this, mul_inv_cancel_right]
  · simpa using Sp4L.uq_sq h hd.1

theorem eq_one_of_odd (hVU : Vq M L = Uq M T L) {y : G} (hy : y ∈ L) (hαy : N.α ⟨y, hy⟩ = 1)
    {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) : y = 1 := by
  have hcQ : ∀ x ∈ pCoreOf 2 M, y * x * y⁻¹ = x := by
    intro x hx
    have hd : x⁻¹ * (y * x * y⁻¹) ∈ Uq M T L := by
      rw [← hVU]
      have := Subgroup.commutator_mem_commutator (inv_mem hx) hy
      rw [commutatorElement_def, inv_inv] at this
      simpa [mul_assoc] using this
    refine conj_eq_of_odd (e := 1) hm hym (d := x⁻¹ * (y * x * y⁻¹)) (by group) ?_ ?_
    · exact conj_eq_of_odd_of_mem_Uq N h hy hαy hm hym hd
    · simpa using Sp4L.uq_sq h hd
  have hyQ : y ∈ pCoreOf 2 M := by
    refine h.charTwo ⟨h.L_le hy, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    have := hcQ x hx
    calc x * y = y * x * y⁻¹ * y := by rw [this]
      _ = y * x := by group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) ⟨y, hyQ⟩
  exact eq_one_of_pow_two_pow_of_pow_odd hm (by simpa using congrArg Subtype.val he) hym

theorem mem_pCoreOf_of_alpha_eq_one (hVU : Vq M L = Uq M T L) {y : G} (hy : y ∈ L)
    (hαy : N.α ⟨y, hy⟩ = 1) : y ∈ pCoreOf 2 M := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hz : y ^ 2 ^ a ∈ L := pow_mem hy _
  have hαz : N.α ⟨y ^ 2 ^ a, hz⟩ = 1 := by
    have : (⟨y ^ 2 ^ a, hz⟩ : ↥L) = ⟨y, hy⟩ ^ 2 ^ a := rfl
    rw [this, map_pow, hαy, one_pow]
  have hzm : (y ^ 2 ^ a) ^ m = 1 := by rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  have hz1 := eq_one_of_odd N h hVU hz hαz hm hzm
  refine h.mem_pCoreOf_of_comm_Uq_two (h.L_le hy) ⟨a, hz1⟩ fun u hu => ?_
  have hd := inv_mul_conj_mem N hy hαy (inv_mem hu)
  have e : ⁅u, y⁆ = u⁻¹⁻¹ * (y * u⁻¹ * y⁻¹) := by
    rw [commutatorElement_def, inv_inv]
    group
  rw [e]
  exact hd.2

end Kernel

end CFSG.Quasithin.MS93.S37

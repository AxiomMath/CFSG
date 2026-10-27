module

public import CFSG.RankThree.PartOne.S11c.HeisenbergDim
public import CFSG.RankThree.CentralLift.ClassicalScalarCover
public import CFSG.RankThree.CentralExtension.CentralKernelTools

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup
open scoped commutatorElement

section Lift

variable {G B : Type*} [Group G] [Group B]

theorem eq_one_of_pow_five_of_not_dvd [Finite G] {ν : G →* B} (hC5 : ¬ 5 ∣ Nat.card ν.ker)
    {c : G} (hc : c ∈ ν.ker) (hc5 : c ^ 5 = 1) : c = 1 := by
  have h1 : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one hc5
  have h2 : orderOf c ∣ Nat.card ν.ker := by
    have := orderOf_dvd_natCard (⟨c, hc⟩ : ν.ker)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h2) hC5

theorem exists_lift_of_pow_five_eq_one [Finite G] {ν : G →* B} (hν : Function.Surjective ν)
    (hC5 : ¬ 5 ∣ Nat.card ν.ker) {b : B} (hb : b ^ 5 = 1) : ∃ a : G, ν a = b ∧ a ^ 5 = 1 := by
  obtain ⟨a₀, rfl⟩ := hν b
  set N := Nat.card ν.ker with hN
  have hcop : Nat.Coprime N 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hC5).symm
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 5)
  refine ⟨a₀ ^ (N * u), ?_, ?_⟩
  · rw [map_pow, pow_mod_five hb (N * u), hu, pow_one]
  · have hc : a₀ ^ 5 ∈ ν.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hb
    have h1 : (⟨a₀ ^ 5, hc⟩ : ν.ker) ^ N = 1 := pow_card_eq_one'
    have h2 : (a₀ ^ 5) ^ N = 1 := congrArg Subtype.val h1
    rw [← pow_mul, show N * u * 5 = 5 * N * u by ring, pow_mul, pow_mul, h2, one_pow]

theorem commutator_pow_five_eq_one {a b : G} (hw : ∀ g : G, ⁅a, b⁆ * g = g * ⁅a, b⁆)
    (hb : b ^ 5 = 1) : ⁅a, b⁆ ^ 5 = 1 := by
  set w := ⁅a, b⁆ with hwdef
  have hab : a * b = w * (b * a) := by rw [hwdef, commutatorElement_def]; group
  have key : ∀ k : ℕ, a * b ^ k = w ^ k * (b ^ k * a) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc a * b ^ (k + 1) = (a * b ^ k) * b := by rw [pow_succ, mul_assoc]
        _ = (w ^ k * (b ^ k * a)) * b := by rw [ih]
        _ = w ^ k * (b ^ k * (a * b)) := by simp only [mul_assoc]
        _ = w ^ k * (b ^ k * (w * (b * a))) := by rw [hab]
        _ = w ^ k * (w * (b ^ k * (b * a))) := by
          rw [← mul_assoc (b ^ k) w, ← hw (b ^ k), mul_assoc]
        _ = w ^ (k + 1) * (b ^ (k + 1) * a) := by
          rw [pow_succ w k, pow_succ b k]
          simp only [mul_assoc]
  have h5 := key 5
  rw [hb, mul_one, one_mul] at h5
  have : w ^ 5 * a = 1 * a := by rw [one_mul]; exact h5.symm
  exact mul_right_cancel this

end Lift

section Relations

variable {G B : Type*} [Group G] [Group B]

theorem exists_lifted_heisenberg [Finite G] {ν : G →* B} (hν : Function.Surjective ν)
    (hcent : ν.ker ≤ Subgroup.center G) (hC5 : ¬ 5 ∣ Nat.card ν.ker) {x y h : B} {m : ℕ}
    (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hcx : Commute ⁅y, x⁆ x) (hcy : Commute ⁅y, x⁆ y)
    (hhz : h * ⁅y, x⁆ * h⁻¹ = ⁅y, x⁆ ^ m) :
    ∃ x' y' h' : G, ν x' = x ∧ ν y' = y ∧ ν h' = h ∧ x' ^ 5 = 1 ∧ Commute ⁅y', x'⁆ x' ∧
      Commute ⁅y', x'⁆ y' ∧ ⁅y', x'⁆ ^ 5 = 1 ∧ h' * ⁅y', x'⁆ * h'⁻¹ = ⁅y', x'⁆ ^ m := by
  obtain ⟨x', hx', hx5⟩ := exists_lift_of_pow_five_eq_one hν hC5 hx
  obtain ⟨y', hy', hy5⟩ := exists_lift_of_pow_five_eq_one hν hC5 hy
  obtain ⟨h', hh'⟩ := hν h
  set z' : G := ⁅y', x'⁆ with hz'
  have hνz : ν z' = ⁅y, x⁆ := by rw [hz', map_commutatorElement, hx', hy']
  have hker_central : ∀ c ∈ ν.ker, ∀ g : G, c * g = g * c := fun c hc g =>
    (Subgroup.mem_center_iff.mp (hcent hc) g).symm
  have hw1 : ⁅z', x'⁆ ∈ ν.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hνz, hx']
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcx.eq
  have hz1x : ⁅z', x'⁆ = 1 :=
    eq_one_of_pow_five_of_not_dvd hC5 hw1
      (commutator_pow_five_eq_one (hker_central _ hw1) hx5)
  have hw2 : ⁅z', y'⁆ ∈ ν.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hνz, hy']
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcy.eq
  have hz1y : ⁅z', y'⁆ = 1 :=
    eq_one_of_pow_five_of_not_dvd hC5 hw2
      (commutator_pow_five_eq_one (hker_central _ hw2) hy5)
  have hcx' : Commute z' x' := commutatorElement_eq_one_iff_commute.mp hz1x
  have hcy' : Commute z' y' := commutatorElement_eq_one_iff_commute.mp hz1y
  have hy_x : y' * x' = z' * x' * y' := by
    rw [hz', commutatorElement_def]; group
  have key : ∀ k : ℕ, y' ^ k * x' = z' ^ k * (x' * y' ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y' ^ (k + 1) * x' = y' ^ k * (y' * x') := by rw [pow_succ, mul_assoc]
        _ = y' ^ k * (z' * x' * y') := by rw [hy_x]
        _ = z' * (y' ^ k * x') * y' := by
          have hc : y' ^ k * z' = z' * y' ^ k := (hcy'.symm.pow_left k).eq
          calc y' ^ k * (z' * x' * y') = (y' ^ k * z') * x' * y' := by simp only [mul_assoc]
            _ = z' * y' ^ k * x' * y' := by rw [hc]
            _ = z' * (y' ^ k * x') * y' := by simp only [mul_assoc]
        _ = z' * (z' ^ k * (x' * y' ^ k)) * y' := by rw [ih]
        _ = z' ^ (k + 1) * (x' * y' ^ (k + 1)) := by
          rw [pow_succ' z' k, pow_succ y' k]
          simp only [mul_assoc]
  have hz5 : z' ^ 5 = 1 := by
    have h5 := key 5
    rw [hy5, one_mul] at h5
    have : z' ^ 5 * x' = 1 * x' := by rw [one_mul]; simpa [hy5] using h5.symm
    exact mul_right_cancel this
  have hc0 : h' * z' * h'⁻¹ * (z' ^ m)⁻¹ ∈ ν.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hνz, hh', map_pow, hνz,
      hhz, mul_inv_cancel]
  have hc5 : (h' * z' * h'⁻¹ * (z' ^ m)⁻¹) ^ 5 = 1 := by
    set c := h' * z' * h'⁻¹ * (z' ^ m)⁻¹ with hc
    have ha : (h' * z' * h'⁻¹) ^ 5 = 1 := by
      rw [show h' * z' * h'⁻¹ = MulAut.conj h' z' from rfl, ← map_pow, hz5, map_one]
    have hb : (z' ^ m) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz5, one_pow]
    have hca : h' * z' * h'⁻¹ = c * z' ^ m := by rw [hc]; group
    have hcomm : Commute c (z' ^ m) := (hker_central c hc0 _)
    rw [hca, hcomm.mul_pow, hb, mul_one] at ha
    exact ha
  have hcz : h' * z' * h'⁻¹ * (z' ^ m)⁻¹ = 1 :=
    eq_one_of_pow_five_of_not_dvd hC5 hc0 hc5
  refine ⟨x', y', h', hx', hy', hh', hx5, hcx', hcy', hz5, ?_⟩
  exact mul_inv_eq_one.mp hcz

end Relations

section Cover

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem pKernel_eq_bot_of_unitary_three_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (5 ^ 1) ^ 2) {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (η : L →* StatedProj (StatedSU 3 (5 ^ 1) K)) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup 5 η.ker) : η.ker = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨φ, -, -, -, hφD, -, -⟩, hD⟩ :=
    CFSG.RankThree.CentralLift.unitary_exact_scalar_cover_of_three_or_defining
      (p := 5) (ℓ := 5) (f := 1) Nat.prime_five (by norm_num) Nat.prime_five (by decide) le_rfl
      hK (le_refl 3) (Or.inl rfl) η hη hC hCp
  have h1 : Nat.card η.ker ∣ 3 := by
    rw [← hφD]
    exact (Subgroup.card_map_dvd _ φ).trans (hD.trans (by norm_num))
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hCp
  have h2 : 5 ^ a ∣ 3 := ha ▸ h1
  have ha0 : a = 0 := by
    by_contra hne
    have := Nat.le_of_dvd (by norm_num) h2
    have h5 : 5 ≤ 5 ^ a := by
      calc 5 = 5 ^ 1 := by norm_num
        _ ≤ 5 ^ a := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hne)
    omega
  rw [ha0, pow_zero] at ha
  exact Subgroup.eq_bot_of_card_eq _ ha

theorem not_five_dvd_card_ker {B : Type} [Group B] (hB : StatedClassicalModel B .PSU 3 5 1)
    {F : Type} [Group F] [Finite F] [Group.IsPerfect F] (ν : F →* B)
    (hν : Function.Surjective ν) (hC : ν.ker ≤ Subgroup.center F) : ¬ 5 ∣ Nat.card ν.ker := by
  obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hK, ⟨eB⟩⟩ := hB
  intro h5
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let π : F →* StatedProj (StatedSU 3 (5 ^ 1) K) := eB.toMonoidHom.comp ν
  have hπker : π.ker = ν.ker := by
    ext g
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact MulEquiv.map_eq_one_iff eB
  have h5' : 5 ∣ Nat.card π.ker := by rw [hπker]; exact h5
  have hC' : π.ker ≤ Subgroup.center F := hπker ▸ hC
  have Cp : Sylow 5 π.ker := default
  have hbot := CFSG.RankThree.CentralExtension.sylow_ker_eq_bot_of_pKernel π
    (eB.surjective.comp hν) hC'
    (fun E' _ _ _ π' hπ' hC'' hp' => pKernel_eq_bot_of_unitary_three_five hK π' hπ' hC'' hp') Cp
  exact Sylow.ne_bot_of_dvd_card Cp h5' hbot

end Cover

end CFSG.RankThree.PartOne.HNRed

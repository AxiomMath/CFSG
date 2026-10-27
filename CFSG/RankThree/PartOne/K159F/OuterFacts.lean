module

public import CFSG.RankThree.PartOne.S12.Sec153Syl

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne Sec153

variable {G : Type} [Group G] [Finite G]

theorem outer_facts' {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G 5 A c L E)
    (M : ModData 5 E) {y : G} (hyN : y ∈ Subgroup.normalizer (E : Set G)) {a : ℕ}
    (hpow : conjAut E y hyN ^ (5 ^ a) = 1) (hne : conjAut E y hyN ≠ 1) :
    Nat.card {u : ↥E // conjAut E y hyN u = u} ≤ 5 := by
  classical
  have hp := h.prime
  have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  have hE : ∀ e : ↥E, e ^ 5 = 1 := fun e =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 5 ↥E) e
  have hW : conjAut E y hyN ∈ torusWeyl E := ⟨⟨y, hyN⟩, rfl⟩
  have hI := M.mem_of_pPower hp hEc hE hW hpow
  let _ : CommGroup ↥E := commE hEc
  have hrel' : ∀ a : Fin 5 → ℤ, ∏ i, M.v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, ((5 : ℕ) : ℤ) ∣ a i - m :=
    fun a => by rw [Fin.prod_univ_five]; exact M.rel a
  have hgen' : ∀ x : ↥E, ∃ a : Fin 5 → ℤ, x = ∏ i, M.v i ^ a i := fun x => by
    obtain ⟨a, ha⟩ := M.gen x
    exact ⟨a, by rw [Fin.prod_univ_five]; exact ha⟩
  have hπpow : (M.θ ⟨conjAut E y hyN, hI⟩) ^ (5 ^ a) = 1 := by
    rw [← map_pow]
    have : (⟨conjAut E y hyN, hI⟩ : ↥(reflectionGroup 5 E)) ^ (5 ^ a) = 1 :=
      Subtype.ext (by simpa using hpow)
    rw [this, map_one]
  have hπ5 : (M.θ ⟨conjAut E y hyN, hI⟩) ^ 5 = 1 := by
    set π := M.θ ⟨conjAut E y hyN, hI⟩ with hπ
    have h1 : orderOf π ∣ 5 ^ a := orderOf_dvd_of_pow_eq_one hπpow
    have h2 : orderOf π ∣ 120 := by
      have := orderOf_dvd_natCard π
      rwa [card_perm5] at this
    obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow hp).1 h1
    have hj1 : j ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have h25 : 25 ∣ 120 := by
        have : 5 ^ 2 ∣ 5 ^ j := pow_dvd_pow 5 hcon
        rw [hjo] at h2
        exact (by norm_num : (25 : ℕ) = 5 ^ 2) ▸ this.trans h2
      omega
    have h3 : orderOf π ∣ 5 := by
      rw [hjo]
      exact (pow_dvd_pow 5 hj1).trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.1 h3
  have hπ1 : M.θ ⟨conjAut E y hyN, hI⟩ ≠ 1 := by
    intro h1
    apply hne
    have := M.θ.injective (h1.trans (map_one M.θ).symm)
    exact congrArg Subtype.val this
  have htrans : ∀ i j : Fin 5, ∃ k : ℕ, (M.θ ⟨conjAut E y hyN, hI⟩ ^ k) i = j := fun i j => by
    obtain ⟨k, hk⟩ := trans5 _ hπ5 hπ1 i j
    exact ⟨k, hk⟩
  exact card_fixed_le M.v hrel' hgen' _ htrans (conjAut E y hyN)
    (fun k => M.perm ⟨conjAut E y hyN, hI⟩ k)

end CFSG.RankThree.PartOne.K159F

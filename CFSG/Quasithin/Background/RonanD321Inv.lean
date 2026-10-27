module

public import CFSG.Quasithin.Background.RonanD321Lift
public import CFSG.Quasithin.Background.RonanD321Uniq
public import CFSG.Quasithin.Background.RonanD321Odd

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391
  CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem exists_two_pow_smul_eq (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L)
    (hle : commV L ≤ fixV (conjAutSub t L))
    (hcent : M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∀ y (hy : y ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W))), ∃ k : ℕ,
      ∀ q ∈ tilde Mp ⊤ (commV L), (⟨y, hy.1⟩ : ↥M) ^ (2 ^ k) • q = q := by
  classical
  let _i := qAct hB.hD.hyp.Mp_normal
  intro y hy
  set g : ↥M := ⟨y, hy.1⟩ with hg
  set Y := tilde Mp ⊤ (commV L) with hY
  have hyL : ∀ l ∈ L, y * l = l * y := fun l hl =>
    ((Subgroup.mem_centralizer_iff.1 hy.2) l hl).symm
  have hmul : ∀ a c : ℕ, (∀ q ∈ Y, g ^ a • q = q) → ∀ q ∈ Y, g ^ (a * c) • q = q := by
    intro a c ha
    induction c with
    | zero => intro q _; rw [mul_zero, pow_zero, one_smul]
    | succ c ih =>
      intro q hq
      rw [mul_add, mul_one, pow_add, mul_smul, ha q hq, ih q hq]
  have hsub : ∀ a b : ℕ, b ≤ a → (∀ q ∈ Y, g ^ a • q = q) → (∀ q ∈ Y, g ^ b • q = q) →
      ∀ q ∈ Y, g ^ (a - b) • q = q := by
    intro a b hba ha hb q hq
    have h1 : g ^ a • q = g ^ (a - b) • (g ^ b • q) := by
      rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hba]
    rw [hb q hq] at h1
    rw [← h1, ha q hq]
  have hNpos : 0 < orderOf g := orderOf_pos g
  have hN : ∀ q ∈ Y, g ^ orderOf g • q = q := fun q _ => by rw [pow_orderOf_eq_one, one_smul]
  have hex : ∃ k, 0 < k ∧ ∀ q ∈ Y, g ^ k • q = q := ⟨_, hNpos, hN⟩
  set d := Nat.find hex with hd_def
  have hd : 0 < d ∧ ∀ q ∈ Y, g ^ d • q = q := Nat.find_spec hex
  have hdvd : ∀ k, (∀ q ∈ Y, g ^ k • q = q) → d ∣ k := by
    intro k hk
    have hmod : ∀ q ∈ Y, g ^ (k % d) • q = q := by
      have e : k % d = k - d * (k / d) := Nat.mod_eq_sub_mul_div
      rw [e]
      exact hsub _ _ (Nat.mul_div_le k d) hk (hmul _ _ hd.2)
    by_contra hnd
    have hpos : 0 < k % d := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    exact Nat.find_min hex (Nat.mod_lt k hd.1) ⟨hpos, hmod⟩
  have h2 : ∀ {p : ℕ}, p.Prime → p ∣ d → p = 2 := by
    intro p hp hpd
    by_contra hp2
    obtain ⟨e, m, hm, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hNpos.ne' p hp.one_lt.ne'
    obtain ⟨d', hd'⟩ := hpd
    have hd'pos : 0 < d' := Nat.pos_of_ne_zero fun h => by
      have := hd.1
      rw [hd', h, mul_zero] at this
      exact lt_irrefl 0 this
    set w : ↥M := g ^ (d' * m) with hw
    have hwnt : ¬ ∀ q ∈ Y, w • q = q := by
      intro h
      have h1 := hdvd (d' * m) h
      rw [hd', mul_comm p d'] at h1
      exact hm ((Nat.dvd_of_mul_dvd_mul_left hd'pos h1))
    have hwp : ∀ q ∈ Y, w ^ p • q = q := by
      intro q hq
      rw [hw, ← pow_mul, show d' * m * p = p * d' * m by ring, ← hd']
      exact hmul _ _ hd.2 q hq
    have hwk : w ^ (p ^ e) = 1 := by
      rw [hw, ← pow_mul, show d' * m * p ^ e = (p ^ e * m) * d' by ring, ← hNe, pow_mul,
        pow_orderOf_eq_one, one_pow]
    have hwM : (w : MulAut W) ∈ M := w.2
    have hwL : ∀ l ∈ L, (w : MulAut W) * l = l * (w : MulAut W) := by
      intro l hl
      have : (w : MulAut W) = y ^ (d' * m) := by rw [hw, Subgroup.coe_pow]
      rw [this]
      exact ((Commute.pow_left (hyL l hl) (d' * m)) : _)
    have hwk' : ∃ k : ℕ, (w : MulAut W) ^ (p ^ k) = 1 :=
      ⟨e, by rw [← Subgroup.coe_pow, hwk]; rfl⟩
    have hwe : (⟨(w : MulAut W), hwM⟩ : ↥M) = w := rfl
    have h := smul_eq_of_odd hB h3 hle hcent hp hp2 hwM hwL hwk' (by rw [hwe]; exact hwp)
    rw [hwe] at h
    exact hwnt h
  have hdpow : d = 2 ^ d.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hd.1.ne' fun hp hpd => h2 hp hpd
  exact ⟨d.primeFactorsList.length, hdpow ▸ hd.2⟩

theorem exists_inv_irrPlus (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L)
    (hle : commV L ≤ fixV (conjAutSub t L))
    (hcent : M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥) :
    ∃ I ∈ IrrPlus L (commV L), M ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub I := by
  let _i := qAct hB.hD.hyp.Mp_normal
  by_cases hnt : ∃ y, ∃ hy : y ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)),
      ∃ q ∈ tilde Mp ⊤ (commV L), (⟨y, hy.1⟩ : ↥M) • q ≠ q
  · obtain ⟨J, hJ, hJU, hJN⟩ :=
      exists_fixed_of_nontrivial hB h3 (exists_two_pow_smul_eq hB h3 hle hcent) hnt
    exact exists_irrPlus_of_fixed hB h3 hJ hJU hJN
  · push Not at hnt
    obtain ⟨J, hJ, hJU, hJN⟩ := exists_fixed_of_trivial hB h3 hnt
    exact exists_irrPlus_of_fixed hB h3 hJ hJU hJN

end CFSG.Quasithin.RonanD321

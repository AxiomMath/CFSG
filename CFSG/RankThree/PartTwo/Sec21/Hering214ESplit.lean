module

public import CFSG.RankThree.PartTwo.Sec21.Hering214ECent

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Res2Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem barAct_of_mem_split {L : Subgroup G} {l : G} (hl : l ∈ L) :
    barAct L ⟨l, Subgroup.le_normalizer hl⟩ = MulAut.conj ((⟨l, hl⟩ : L) : lBar L) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H w => rfl

private theorem isPGroup_zpowers_pow_of_dvd {p : ℕ} (hp : p.Prime) {x : G} {b r k : ℕ}
    (hx : x ^ (p ^ b * r) = 1) (hk : r ∣ k) : IsPGroup p (Subgroup.zpowers (x ^ k)) := by
  have h1 : (x ^ k) ^ (p ^ b) = 1 := by
    obtain ⟨t, rfl⟩ := hk
    rw [← pow_mul, show r * t * p ^ b = p ^ b * r * t by ring, pow_mul, hx, one_pow]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one h1)
  refine IsPGroup.of_card (n := j) ?_
  rw [Nat.card_zpowers, hj]

theorem exists_mul_of_barAct_inner {p : ℕ} [Fact p.Prime] {L : Subgroup G} [Group.IsPerfect L]
    (hθc : aschbacherSolvableCore 3 L ≤ Subgroup.center L) {e : G}
    (he : e ∈ Subgroup.normalizer (L : Set G)) (hp : IsPGroup p (Subgroup.zpowers e))
    (hinn : barAct L ⟨e, he⟩ ∈ (MulAut.conj : lBar L →* MulAut (lBar L)).range) :
    ∃ l ∈ L, ∃ z ∈ Subgroup.centralizer (L : Set G), e = l * z ∧ l * z = z * l ∧
      IsPGroup p (Subgroup.zpowers l) ∧ IsPGroup p (Subgroup.zpowers z) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hinn
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective x
  have hg₀N : (l₀ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l₀.2
  have hact₀ : barAct L ⟨(l₀ : G), hg₀N⟩ = MulAut.conj (QuotientGroup.mk l₀ : lBar L) :=
    barAct_of_mem_split l₀.2
  have hz₀N : (l₀ : G)⁻¹ * e ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem hg₀N) he
  have hbar : barAct L ⟨(l₀ : G)⁻¹ * e, hz₀N⟩ = 1 := by
    have h1 : (⟨(l₀ : G)⁻¹ * e, hz₀N⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨(l₀ : G), hg₀N⟩ : Subgroup.normalizer (L : Set G))⁻¹ *
          (⟨e, he⟩ : Subgroup.normalizer (L : Set G)) := rfl
    rw [h1, map_mul, map_inv, hact₀, hx, inv_mul_cancel]
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : G, z₀ = (l₀ : G)⁻¹ * e := ⟨_, rfl⟩
  have hzC : z₀ ∈ Subgroup.centralizer (L : Set G) := by
    rw [hz₀]
    exact mem_centralizer_of_barAct_eq_one hθc hz₀N hbar
  have hcomm : Commute (l₀ : G) z₀ := Subgroup.mem_centralizer_iff.mp hzC (l₀ : G) l₀.2
  have he_eq : e = (l₀ : G) * z₀ := by rw [hz₀, mul_inv_cancel_left]
  have hn0 : orderOf (l₀ : G) * orderOf z₀ ≠ 0 :=
    mul_ne_zero (orderOf_pos _).ne' (orderOf_pos _).ne'
  obtain ⟨b, r, hr, hnr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hpp.ne_one
  have hgn : (l₀ : G) ^ (p ^ b * r) = 1 := by
    rw [← hnr]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_mul_right _ _)
  have hzn : z₀ ^ (p ^ b * r) = 1 := by
    rw [← hnr]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_mul_left _ _)
  have hen : e ^ (p ^ b * r) = 1 := by
    rw [he_eq, hcomm.mul_pow, hgn, hzn, one_mul]
  obtain ⟨j, hj⟩ := hp ⟨e, Subgroup.mem_zpowers e⟩
  have hej : e ^ (p ^ j) = 1 := by
    simpa using congrArg Subtype.val hj
  have hdvd : orderOf e ∣ p ^ b := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hpp).1 (orderOf_dvd_of_pow_eq_one hej)
    have hcop : Nat.Coprime (orderOf e) r := by
      rw [hi]
      exact Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hpp).2 hr)
    exact hcop.dvd_of_dvd_mul_right (orderOf_dvd_of_pow_eq_one hen)
  have hcop_rpb : Nat.Coprime r (p ^ b) :=
    Nat.Coprime.pow_right b ((Nat.Prime.coprime_iff_not_dvd hpp).2 hr).symm
  obtain ⟨k, hk1, hkr⟩ : ∃ k : ℕ, k ≡ 1 [MOD p ^ b] ∧ r ∣ k :=
    ⟨r ^ Nat.totient (p ^ b), Nat.ModEq.pow_totient hcop_rpb,
      dvd_pow_self r (Nat.totient_pos.2 (pow_pos hpp.pos b)).ne'⟩
  have hek : e ^ k = e := by
    have h : e ^ k = e ^ 1 := pow_eq_pow_iff_modEq.2 (Nat.ModEq.of_dvd hdvd hk1)
    rwa [pow_one] at h
  have hsplit : e = (l₀ : G) ^ k * z₀ ^ k := by
    calc e = e ^ k := hek.symm
      _ = ((l₀ : G) * z₀) ^ k := by rw [← he_eq]
      _ = (l₀ : G) ^ k * z₀ ^ k := hcomm.mul_pow k
  exact ⟨(l₀ : G) ^ k, pow_mem l₀.2 k, z₀ ^ k, pow_mem hzC k, hsplit,
    (hcomm.pow_pow k k).eq, isPGroup_zpowers_pow_of_dvd hpp hgn hkr,
    isPGroup_zpowers_pow_of_dvd hpp hzn hkr⟩

end CFSG.RankThree.PartTwo.Sec21.Hering214Even

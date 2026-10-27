module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin.H13

section L827B

theorem card_modEq_card_fix_827 {R : Type*} [Group R] [Finite R] {q : ℕ} [Fact q.Prime]
    {α : MulAut R} (hα : α ^ q = 1) :
    Nat.card R ≡ Nat.card ↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id R)) [MOD q] := by
  classical
  set H := Subgroup.zpowers α with hHdef
  have hH : IsPGroup q ↥H := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hα, one_zpow]
  have h := hH.card_modEq_card_fixedPoints R
  have hfix : ∀ r : R, r ∈ MulAction.fixedPoints ↥H R ↔ α r = r := by
    intro r
    constructor
    · intro hr
      have h1 := hr ⟨α, Subgroup.mem_zpowers α⟩
      rwa [Subgroup.smul_def, MulAut.smul_def] at h1
    · intro hr g
      have hst : α ∈ MulAction.stabilizer (MulAut R) r := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hr
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
      have h2 := Subgroup.zpow_mem _ hst n
      rw [hn] at h2
      exact h2
  have hcard : Nat.card (MulAction.fixedPoints ↥H R) =
      Nat.card ↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id R)) :=
    Nat.card_congr (Equiv.subtypeEquivRight hfix)
  rw [hcard] at h
  exact h

theorem eq_one_of_pow_five_827 {R : Type*} [Group R] [Finite R]
    (hR : Nat.card R = 1 ∨ Nat.card R = 3 ∨ Nat.card R = 5 ∨ Nat.card R = 7 ∨ Nat.card R = 9)
    {α : MulAut R} (hα : α ^ 5 = 1) : α = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := card_modEq_card_fix_827 hα
  set F := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id R) with hFdef
  have hF : Nat.card F ∣ Nat.card R := Subgroup.card_subgroup_dvd_card F
  have hF1 : 0 < Nat.card F := Nat.card_pos
  have hle : Nat.card F ≤ Nat.card R := Nat.le_of_dvd Nat.card_pos hF
  have hFR : Nat.card F = Nat.card R := by
    unfold Nat.ModEq at h
    generalize Nat.card F = c at hF hF1 hle h ⊢
    rcases hR with hR | hR | hR | hR | hR <;> rw [hR] at hF hle h ⊢ <;> interval_cases c <;> omega
  have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F hFR
  ext r
  have hr : r ∈ F := htop ▸ Subgroup.mem_top r
  exact hr

theorem card_mulAut_827 {W : Type*} [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hW2 : ∀ w : W, w ^ 2 = 1) (hW : Nat.card W = 16) : Nat.card (MulAut W) = 20160 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hW2
    (n := 4) (by rw [hW]; norm_num)
  rw [Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv, Matrix.card_GL_field,
    ZMod.card, Fin.prod_univ_four]
  norm_num

theorem prime_dvd_20160_827 {s : ℕ} (hs : s.Prime) (h : s ∣ 20160) :
    s = 2 ∨ s = 3 ∨ s = 5 ∨ s = 7 := by
  have h' : s ∣ 2 ^ 6 * (3 ^ 2 * (5 * 7)) := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hs).mp h' with h2 | h2
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h2))
  rcases (Nat.Prime.dvd_mul hs).mp h2 with h3 | h3
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp
      (hs.dvd_of_dvd_pow h3)))
  rcases (Nat.Prime.dvd_mul hs).mp h3 with h5 | h7
  · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hs (by norm_num)).mp h5)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hs (by norm_num)).mp h7)))

theorem card_of_isPGroup_827 {W : Type*} [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hW2 : ∀ w : W, w ^ 2 = 1) (hW : Nat.card W = 16) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (MulAut W)} (hP : IsPGroup p ↥P) :
    Nat.card P = 1 ∨ Nat.card P = 3 ∨ Nat.card P = 5 ∨ Nat.card P = 7 ∨ Nat.card P = 9 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut W) := Finite.of_injective (fun f : MulAut W => (f : W → W))
    fun f f' h => MulEquiv.ext (congrFun h)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : p ^ k ∣ 20160 := by
    rw [← hk, ← card_mulAut_827 hcomm hW2 hW]
    exact Subgroup.card_subgroup_dvd_card P
  rcases k with _ | k
  · left
    rw [hk, pow_zero]
  have hp' : p ∣ 20160 := (dvd_pow_self p (Nat.succ_ne_zero k)).trans hdvd
  have hbound : ∀ j : ℕ, ¬ p ^ j ∣ 20160 → k + 1 < j := by
    intro j hj
    by_contra hc
    exact hj ((pow_dvd_pow p (not_lt.mp hc)).trans hdvd)
  rcases prime_dvd_20160_827 hp hp' with rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · have h3 : k < 2 := by have := hbound 3 (by norm_num); omega
    interval_cases k
    · right; left; rw [hk]; norm_num
    · right; right; right; right; rw [hk]; norm_num
  · have h5 : k < 1 := by have := hbound 2 (by norm_num); omega
    interval_cases k
    right; right; left; rw [hk]; norm_num
  · have h7 : k < 1 := by have := hbound 2 (by norm_num); omega
    interval_cases k
    right; right; right; left; rw [hk]; norm_num

end L827B

end CFSG.Quasithin.H13

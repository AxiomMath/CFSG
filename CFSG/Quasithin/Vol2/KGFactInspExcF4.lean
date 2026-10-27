module

public import CFSG.Quasithin.Vol2.KGFactInspExcCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4
public import CFSG.Quasithin.EmptyFaithful.R3c18WF4
public import CFSG.LieType.BorelTits.Ree

public section

namespace CFSG.Quasithin.H13.KGInsp4316.Exc

open CFSG.Quasithin (perfectCore)
open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Ree.LargeReeInvolution

section F4

theorem not_three_dvd_card_sz {a : ℕ} {L : Type} [Field L] [Finite L]
    (hL : Nat.card L = 2 ^ (2 * a + 1)) : ¬ 3 ∣ Nat.card (CFSG.Blueprint.suzukiGroup a L) := by
  rw [CFSG.LieType.Ree.suzuki_order hL]
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize q ^ 2 = q2 at hq2 ⊢
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h <;> omega
  · omega


variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X} {n : ℕ} {x : X}

theorem two_le_pRank_f4 (h : Cfg4316 S R K n x) (hRS : R ≤ S) {f : ℕ}
    (hm : ReeTitsModel ↥S .twistedF4 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) : 2 ≤ CFSG.Open.pRank p S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, L, _, _, _, ha, hfa, hL, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hm
  subst hfa
  have : Finite (ModGL F4.tag L) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a L w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent L a ≤ F4.reeGamma L a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (F4.reeFixedPosUnipotent L a)
      (F4.reeGamma L a) := by
    refine CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hUsyl
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent L a) := hUsyl.2.1
  have hBT : CFSG.LieType.BorelTits.Holds ↥(F4.reeGamma L a) 2 :=
    (CFSG.LieType.BorelTits.holds_of_reeTitsModel hm (by decide)).of_mulEquiv e
  obtain ⟨j, D, hD, hdvd⟩ := exists_le_perfectCore h hRS e hBT hU₀
    (CFSG.QuasithinUnique.Setup.X6.large_Ree_residualOvergroupsAt hL)
  have hn2 := h.two_le
  have hodd : Odd (4 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
      ((Nat.even_pow' (by omega)).mpr (by decide)) odd_one
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model ha hL
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hnf : n ∣ 2 * a + 1 := by
    rcases hcases (CFSG.QuasithinUnique.Setup.X6.f4Index j) with hj | hj
    ·
      have : IsSimpleGroup ↥(rankOneGroupOne L a) := (isSimpleGroup_rankOneGroupOne ha hL).1
      obtain ⟨g, hg, hk⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.ree_levi_hom (K := L) (a := a)
        hUp (CFSG.QuasithinUnique.Setup.X6.f4Index j) (M := rankOneGroupOne L a)
        (by rw [hj]; exact h0eq) (isSimpleGroup_rankOneGroupOne ha hL).2
      have h1 := odd_dvd_card_of_le hD g hk hodd hdvd
      rw [← Nat.card_congr (rankOneEquivSL L a hL).toEquiv,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hL, ← pow_mul,
        mul_comm (2 * a + 1) 2, pow_mul] at h1
      norm_num at h1
      exact dvd_of_four_pow_sub_one_dvd (by omega) h1
    ·
      exfalso
      have : IsSimpleGroup ↥(rankOneGroupTwo L a) := (isSimpleGroup_rankOneGroupTwo ha hL).1
      obtain ⟨g, hg, hk⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.ree_levi_hom (K := L) (a := a)
        hUp (CFSG.QuasithinUnique.Setup.X6.f4Index j) (M := rankOneGroupTwo L a)
        (by rw [hj]; exact h1eq) (isSimpleGroup_rankOneGroupTwo ha hL).2
      have h1 := odd_dvd_card_of_le hD g hk hodd hdvd
      rw [Nat.card_congr (rankOneEquivSuzuki L a ha hL).toEquiv] at h1
      have h3 : 3 ∣ 4 ^ n - 1 := by
        simpa using Nat.sub_one_dvd_pow_sub_one 4 n
      exact not_three_dvd_card_sz hL (h3.trans h1)
  have hnodd : Odd n := Odd.of_dvd_nat (by exact ⟨a, by ring⟩) hnf
  have hp5 : 5 ≤ p := by
    have h3 : ¬ 3 ∣ 2 ^ n - 1 := by
      obtain ⟨k, rfl⟩ := hnodd
      intro h3
      have h4 : (2 ^ (2 * k + 1) - 1) % 3 = 1 := by
        have h5 : 2 ^ (2 * k + 1) % 3 = 2 := by
          rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
          norm_num
        have h6 : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
        generalize 2 ^ (2 * k + 1) = y at h5 h6 ⊢
        omega
      rw [Nat.dvd_iff_mod_eq_zero] at h3
      generalize 2 ^ (2 * k + 1) - 1 = y at h3 h4
      omega
    have hp3 : p ≠ 3 := fun h => h3 (h ▸ hpn)
    have h2 := hp.two_le
    have h4 : p ≠ 4 := fun h4 => by rw [h4] at hp; exact absurd hp (by decide)
    omega
  have hpQ : p ∣ 2 ^ (2 * a + 1) - 1 := hpn.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)
  have h2 := CFSG.Quasithin.R3c18.f4ReeRank_holds hL hp hp5 (Or.inl hpQ)
  obtain ⟨E, hE, hEel⟩ := CFSG.Quasithin.R3c18.exists_sq_of_two_le_pRank hp h2
  have h2' : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(F4.reeGamma L a)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hEel hE
  exact CFSG.QuasithinUnique.Lin2.OddRank.le_pRank_of_equiv e hp.one_lt h2'

end F4

end CFSG.Quasithin.H13.KGInsp4316.Exc

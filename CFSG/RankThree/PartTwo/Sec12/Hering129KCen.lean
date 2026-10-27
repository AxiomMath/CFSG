module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KFix
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank

theorem four_le_of_isSLThreePiAt {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    (hq : CFSG.IsQuasisimple Y) (h : Sec4.IsSLThreePiAt Y m) : 4 ≤ m := by
  obtain ⟨K, _, _, h⟩ := h
  have hK2 : 1 < Nat.card K := Finite.one_lt_card
  rcases h with ⟨hc, hm, -⟩ | ⟨hc, hm, ⟨φ⟩⟩
  · omega
  · by_contra hlt
    have hm2 : m = 2 := by
      have h2 : 2 ≤ m ^ 2 := by omega
      have hm1 : 2 ≤ m := by
        by_contra h1
        have : m ≤ 1 := by omega
        have : m ^ 2 ≤ 1 := by nlinarith
        omega
      omega
    subst hm2
    have hcard : Nat.card Y = 216 := by
      rw [Nat.card_congr φ.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hc]
      norm_num
    have hsolv : Group.IsSolvable Y := by
      refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
      rw [hcard]
      have h216 : Nat.primeFactors 216 = {2, 3} := by
        rw [show (216 : ℕ) = 2 ^ 3 * 3 ^ 3 by norm_num,
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
          Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
        rfl
      rw [h216]
      decide
    haveI : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hq
    haveI : Group.IsPerfect Y := hq.1
    exact Group.IsPerfect.not_isSolvable Y hsolv

@[expose] def Gap127D4Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
      GTwoType129At L K q →
      (∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid, Nonempty (K ⧸ CFSG.pCore 2 K ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) → q.p = 2

theorem gap127TwoCfgPlus_of (h : Gap127TwoCfg) (hD4 : Gap127D4Even)
    (hTL : KS129ThreeLocalFix) : Gap127TwoCfgPlus := by
  refine ⟨h, ?_⟩
  intro G _ _ A c L b a K S cfg q hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hq4 : 4 ≤ q.card :=
    four_le_of_isSLThreePiAt (isQuasisimple_thetaQuot_of_mem hstd.mem_thetaComponentsAt) hq.1
  have hq2 := hD4 G A c L b a K S cfg q hq
  refine ⟨hq4, hq2, fun hcK => ?_⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hcA : c ∈ A := hstd.mem_A
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hc1 : c ≠ 1 := hstd.ne_one
  have hbB : b ∈ Sec4.thetaQuotCentralizer L := cfg.hb.2
  have hAL : A ⊓ L ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) :=
    BCensus.inf_le_residual hstd hbA hbB
  have hcI := hAL ⟨hcA, hstd.mem_L⟩
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hstd.mem_thetaComponentsAt
  have hcRes : c ∈ resCent K c := by
    have hle : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤
        resCent K c := by
      apply le_inSubgroup_perfectResidual_of_isPerfect
      · exact le_inf cfg.hIK (((Subgroup.map_subtype_le _ :
          inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ _)).trans
            (inf_le_left.trans hLc))
      · exact Sec6.isPerfect_inSubgroup_perfectResidual _
    exact hle hcI
  set N : Subgroup K := CFSG.pCore 2 K with hNdef
  have hN3 : ¬ 3 ∣ Nat.card N := not_three_dvd_card_pCore_two K
  set ct : K := ⟨c, hcK⟩ with hct
  have hct3 : ct ^ 3 = 1 := Subtype.ext hc3
  set π : K →* K ⧸ N := QuotientGroup.mk' N with hπ
  have hct1 : π ct ≠ 1 := by
    intro h1
    have h2 : ct ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one (Y := K) h2
    exact hc1 (congrArg Subtype.val (eq_one_of_pow_three_of_pow_two_pow hct3 hk))
  have hct3' : π ct ^ 3 = 1 := by rw [← map_pow, hct3, map_one]
  have hord : orderOf (π ct) = 3 := orderOf_eq_prime hct3' hct1
  have hq3 : q.p ≠ 3 := by
    obtain ⟨F, _, _, h⟩ := hq.1
    have hmod : q.card % 3 = 1 ∨ q.card % 3 = 2 := by
      rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    intro hp3
    have : 3 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, hp3]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    omega
  obtain ⟨δ, hG2D4, hδ3⟩ : ∃ δ : ℕ, IsG2D4 (K ⧸ N) q δ ∧ (δ = 3 → q.p = 2) := by
    rcases hq.2 with h | ⟨hq', h⟩
    · exact ⟨1, Or.inl ⟨rfl, h⟩, fun h => absurd h (by norm_num)⟩
    · exact ⟨3, Or.inr ⟨rfl, hq', h⟩, fun _ => hq2 ⟨hq', h⟩⟩
  obtain ⟨h0, -, -, hd⟩ := hTL (K ⧸ N) q δ hG2D4 hq4 hq3 hδ3
  have hmem : π ct ∈ resCent (⊤ : Subgroup (K ⧸ N)) (π ct) := by
    rw [resCent_eq_map K hcK] at hcRes
    obtain ⟨y, hy, hyc⟩ := hcRes
    have hy' : y = ct := Subtype.ext hyc
    rw [← map_resCent_quot N hN3 hct3]
    exact ⟨y, hy, by rw [hy']⟩
  rcases h0 (π ct) hord with hA | hB
  · exact hA
  · exact (hd (π ct) hB).1 (π ct) hmem hord

end CFSG.RankThree.PartTwo.Sec12

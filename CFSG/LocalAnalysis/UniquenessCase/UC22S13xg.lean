module

public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.GroupTheory.WeirSylow.GL
import CFSG.GroupTheory.WeirSylow.Unitary
import CFSG.LieType.BorelTits.Basic
import CFSG.LieType.ChevTwo.OppositeFixedExcTits
import CFSG.RankThree.PartOne.KC.CentralizerOfInnerTrivial
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.AbelianTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Small
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarCat
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Open (rankThreeLayer)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IrrOnMod)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
  (sylow_isMulCommutative_of_sigmaModel_of_lt sylow_comm_of_subgroup sylow_comm_of_surjective)

theorem uc22s13xg_le_or_le_frattini {G : Type} [Group G] [Finite G] {N D K : Subgroup G}
    (hND : N ≤ normalizer (D : Set G)) (hNK : N ≤ normalizer (K : Set G))
    (hirr : IrrOnMod N D (inSubgroup frattini D)) :
    D ≤ K ∨ D ⊓ K ≤ inSubgroup frattini D := by
  have hFD : inSubgroup frattini D ≤ D := Subgroup.map_subtype_le _
  have hNF : N ≤ normalizer ((inSubgroup frattini D : Subgroup G) : Set G) :=
    hND.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (frattini D))
  have hNDK : N ≤ normalizer ((D ⊓ K : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (hND hg) h)
      (Subgroup.mem_normalizer_iff.mp (hNK hg) h)
  have hNW : N ≤ normalizer ((inSubgroup frattini D ⊔ D ⊓ K : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNF hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNDK hg)]
  rcases hirr _ le_sup_left (sup_le hFD inf_le_left) hNW with h | h
  · exact Or.inr (le_sup_right.trans_eq h)
  · left
    have h' : (frattini D).map D.subtype ⊔ D ⊓ K = D := h
    have htop : K.subgroupOf D ⊔ frattini D = ⊤ := by
      apply Subgroup.map_injective D.subtype_injective
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, inf_comm, sup_comm]
      exact h'
    exact Subgroup.subgroupOf_eq_top.mp (frattini_nongenerating htop)

theorem uc22s13xg_frattini_le_ker {D Y : Type*} [Group D] [Finite D] [Group Y] {p : ℕ}
    [Fact p.Prime] (f : D →* Y) (hexp : ∀ a : D, a ^ p = 1)
    (hcomm : ∀ a b : D, f a * f b = f b * f a) : frattini D ≤ f.ker := by
  have hsurj : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  haveI : Finite f.range := Finite.of_surjective _ hsurj
  haveI : Fact (IsPGroup p f.range) := ⟨fun y => by
    obtain ⟨a, rfl⟩ := hsurj y
    exact ⟨1, by rw [pow_one, ← map_pow, hexp, map_one]⟩⟩
  haveI : IsElementaryAbelian p f.range :=
    { toIsMulCommutative := ⟨⟨fun y z => by
        obtain ⟨a, rfl⟩ := hsurj y
        obtain ⟨b, rfl⟩ := hsurj z
        exact Subtype.ext (by
          simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict]
          exact hcomm a b)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun y => by
        obtain ⟨a, rfl⟩ := hsurj y
        rw [← map_pow, hexp, map_one] }
  have h1 := frattini_le_comap_frattini_of_surjective hsurj
  rw [CFSG.frattini_eq_bot_of_isElementaryAbelian (R := f.range) (p := p), MonoidHom.comap_bot,
    MonoidHom.ker_rangeRestrict] at h1
  exact h1

theorem uc22s13xg_sylow_comm_l2 {X : Type} [Group X] [Finite X] {n p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hX : IsL2 X n) (S : Sylow p X) : IsMulCommutative (S : Subgroup X) := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX
  haveI : Fintype K := Fintype.ofFinite K
  have hpK : ¬ p ∣ Fintype.card K := by
    rw [Fintype.card_eq_nat_card, hK]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h))
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hc := sylow_isMulCommutative_of_sigmaModel_of_lt hp.out
    (G := GL (Fin 2) K) (e := orderOf (Fintype.card K : ZMod p))
    (a := padicValNat p (Fintype.card K ^ orderOf (Fintype.card K : ZMod p) - 1)) (N := 2)
    (lt_of_le_of_lt (Nat.div_le_self 2 _) (by omega))
    (fun P => CFSG.GroupTheory.WeirSylow.sylow_GL (hp.out.odd_of_ne_two hp2) K hpK 2 P)
  exact sylow_comm_of_surjective φ.symm.toMonoidHom φ.symm.surjective
    (sylow_comm_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (sylow_comm_of_subgroup (CFSG.Open.StatedSL 2 K) hc)) S

theorem uc22s13xg_sylow_comm_u3 {X : Type} [Group X] [Finite X] {n p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hn : Even n) (hX : IsU3 X n) (S : Sylow p X) :
    IsMulCommutative (S : Subgroup X) := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX
  haveI : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = (2 ^ n) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hK
  have hpq : ¬ p ∣ 2 ^ n := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h))
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hlt : 3 / orderOf (-((2 ^ n : ℕ) : ZMod p)) < p := by
    rcases Nat.lt_or_ge 3 p with h | h
    · exact lt_of_le_of_lt (Nat.div_le_self 3 _) h
    · have hp3' : p = 3 := by omega
      have h1 : orderOf (-((2 ^ n : ℕ) : ZMod p)) ≠ 1 := by
        intro h
        rw [orderOf_eq_one_iff] at h
        have hdvd : p ∣ 2 ^ n + 1 := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, neg_eq_iff_eq_neg.1 h,
            neg_add_cancel]
        rw [hp3'] at hdvd
        obtain ⟨m, rfl⟩ := hn
        have h4 : (2 ^ (m + m) + 1) % 3 = 2 := by
          rw [← two_mul, pow_mul, Nat.add_mod, Nat.pow_mod]
          norm_num
        omega
      generalize orderOf (-((2 ^ n : ℕ) : ZMod p)) = e at h1 ⊢
      rw [hp3']
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, Nat.div_zero]
        omega
      · rw [Nat.div_lt_iff_lt_mul h0]
        omega
  have hGU : ∀ P : Sylow p (CFSG.Quasithin.StatedGU 3 (2 ^ n) K),
      IsMulCommutative (P : Subgroup (CFSG.Quasithin.StatedGU 3 (2 ^ n) K)) :=
    sylow_isMulCommutative_of_sigmaModel_of_lt hp.out hlt
      (fun P => CFSG.GroupTheory.WeirSylow.sylow_GU (hp.out.odd_of_ne_two hp2) K hKc hpq
        (by norm_num) P)
  have hle := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU
    (L := K) (q := 2 ^ n) (n := 3)
  have hSU := sylow_comm_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hle).surjective
    (sylow_comm_of_subgroup ((CFSG.Open.StatedSU 3 (2 ^ n) K).subgroupOf
      (CFSG.Quasithin.StatedGU 3 (2 ^ n) K)) hGU)
  exact sylow_comm_of_surjective φ.symm.toMonoidHom φ.symm.surjective
    (sylow_comm_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) hSU) S

theorem uc22s13xg_even_center_outer {X : Type} [Group X] [Finite X] {n : ℕ} (hn : IsPowTwo n)
    (hX : IsL2 X n ∨ IsU3 X n) : Even n ∧ center X = ⊥ ∧ IsPGroup 2 (Outer X) := by
  have hn2 : 2 ≤ n := by
    have h1 : 1 ≤ n ∧ 2 ^ n ≠ 2 := by
      rcases hX with h | h
      · have hadm := CFSG.Blueprint.LieModel.admissible h
        exact ⟨hadm.2.1, fun h2 => hadm.2.2.2.1 (by rw [h2])⟩
      · have hadm := CFSG.Blueprint.LieModel.admissible h
        exact ⟨hadm.2.1, fun h2 => hadm.2.2.2 (by rw [h2])⟩
    rcases Nat.lt_or_ge n 2 with h | h
    · exfalso
      have hn1 : n = 1 := by omega
      exact h1.2 (by rw [hn1]; norm_num)
    · exact h
  obtain ⟨k, hk⟩ := hn
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk
      omega
    · exact h0
  have hev : n = 2 * 2 ^ (k - 1) := by
    rw [hk, ← pow_succ']
    congr 1
    omega
  have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := by
    have h4 : 2 ^ n = 4 ^ 2 ^ (k - 1) := by
      rw [hev, pow_mul]
      norm_num
    have h41 : 4 ^ 2 ^ (k - 1) % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have hnd : ¬ 3 ∣ 2 ^ n + 1 := by
      rw [h4]
      omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd
  obtain ⟨i, e, hK, hOut⟩ : ∃ i e : ℕ, BenderType X n i e ∧ IsPGroup 2 (Outer X) := by
    rcases hX with h | h
    · obtain ⟨φ⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2Model_of_lieModel h
      have hK : BenderType X n 1 1 := .linear n hn2 φ
      exact ⟨1, 1, hK, IsPGroup.of_card (n := k) (hK.outer_linear.2.trans hk)⟩
    · obtain ⟨e, hK⟩ := CFSG.SeitzReduction.RankOne.exists_benderType_of_lieModel_psu3 hn2 h
      obtain ⟨Dd, hDn, -, hDcard, -, hQcard⟩ := hK.outer_unitary
      refine ⟨3, e, hK, IsPGroup.of_card (n := k + 1) ?_⟩
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Dd, hQcard, hDcard, hgcd, mul_one, hk]
      ring
  exact ⟨⟨2 ^ (k - 1), by omega⟩, hK.center_eq_bot, hOut⟩

theorem uc22s13xg_comm_of_isPGroup {X : Type} [Group X] [Finite X] {n p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hn : IsPowTwo n) (hX : IsL2 X n ∨ IsU3 X n) {A : Subgroup (MulAut X)}
    (hA : IsPGroup p A) {a b : MulAut X} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  obtain ⟨hev, hZ, hOut⟩ := uc22s13xg_even_center_outer hn hX
  have hinj := CFSG.RankThree.PartOne.conj_injective_of_center_eq_bot hZ
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have hinn : ∀ α ∈ A, ∃ y : X, MulAut.conj y = α := fun α hα => by
    obtain ⟨k, hk⟩ := hA ⟨α, hα⟩
    have h1 : α ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact MonoidHom.mem_range.mp (CFSG.LieType.ChevTwo.inner_of_odd_orderOf_of_outer hOut α
      ((hpodd.pow).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)))
  obtain ⟨u, rfl⟩ := hinn a ha
  obtain ⟨v, rfl⟩ := hinn b hb
  have hY : IsPGroup p (A.comap (MulAut.conj : X →* MulAut X)) := hA.comap_of_injective _ hinj
  obtain ⟨S, hS⟩ := hY.exists_le_sylow
  have hSc : IsMulCommutative (S : Subgroup X) := by
    rcases hX with h | h
    · exact uc22s13xg_sylow_comm_l2 hp2 h S
    · exact uc22s13xg_sylow_comm_u3 hp2 hev h S
  have huv : u * v = v * u := by
    have := congrArg Subtype.val
      (hSc.is_comm.comm ⟨u, hS (Subgroup.mem_comap.mpr ha)⟩ ⟨v, hS (Subgroup.mem_comap.mpr hb)⟩)
    simpa using this
  rw [← map_mul, ← map_mul, huv]

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xg_le_of_alt1 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M H P D₀ L : Subgroup G}
    (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) {n : ℕ} (hn : IsPowTwo n)
    (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) (hPM : P ≤ M) (hexp : ∀ x ∈ D₀, x ^ p = 1)
    (h1 : H ⊓ M = H ⊓ normalizer (P : Set G))
    (h2 : IrrOnMod (rankThreeLayer H ⊓ normalizer (P : Set G)) D₀ (inSubgroup frattini D₀))
    (h3 : P = D₀) {x : G} (hxD : x ∈ D₀) (hxL : x ∈ L) (hx1 : x ≠ 1) : D₀ ≤ L := by
  haveI : Fact p.Prime := ⟨hp⟩
  subst h3
  have hMN : M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hEH : rankThreeLayer H ≤ H := sSup_le fun _ hK => hK.1
  have hNM : rankThreeLayer H ⊓ normalizer (P : Set G) ≤ M := by
    intro g hg
    have hg' : g ∈ H ⊓ M := by
      rw [h1]
      exact Subgroup.mem_inf.mpr ⟨hEH (Subgroup.mem_inf.mp hg).1, (Subgroup.mem_inf.mp hg).2⟩
    exact (Subgroup.mem_inf.mp hg').2
  rcases uc22s13xg_le_or_le_frattini inf_le_right (hNM.trans hMN) h2 with h | h
  · exact h
  · exfalso
    obtain ⟨x', hx', rfl⟩ := h (Subgroup.mem_inf.mpr ⟨hxD, hxL⟩)
    have hPN : P ≤ normalizer (L : Set G) := hPM.trans hMN
    set f : ↥P →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hPN) with hf
    have hexp' : ∀ a : ↥P, a ^ p = 1 := fun a => Subtype.ext (by simpa using hexp a a.2)
    have hPp : IsPGroup p ↥P := fun a => ⟨1, by rw [pow_one]; exact hexp' a⟩
    have hcomm : ∀ a b : ↥P, f a * f b = f b * f a := fun a b =>
      uc22s13xg_comm_of_isPGroup hp2 hn hX
        (hPp.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
        (MonoidHom.mem_range.mpr ⟨a, rfl⟩) (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
    have hker : f x' = 1 := uc22s13xg_frattini_le_ker f hexp' hcomm hx'
    have hfx : f x' = MulAut.conj (QuotientGroup.mk (⟨(x' : G), hxL⟩ : ↥L) : Bar2 L) := by
      rw [← UC6S846.rhoL_inner L (x' : G) hxL]
      rfl
    obtain ⟨-, hZ, -⟩ := uc22s13xg_even_center_outer hn hX
    have hmk : (QuotientGroup.mk (⟨(x' : G), hxL⟩ : ↥L) : Bar2 L) = 1 := by
      apply CFSG.RankThree.PartOne.conj_injective_of_center_eq_bot hZ
      rw [map_one, ← hfx, hker]
    rw [QuotientGroup.eq_one_iff] at hmk
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hmk⟩
    have h2k : (x' : G) ^ 2 ^ k = 1 := by
      have := congrArg (fun z => ((z : ↥L) : G)) (congrArg Subtype.val hk)
      simpa using this
    have hpx : (x' : G) ^ p = 1 := hexp _ hxD
    have hcop : Nat.Coprime (2 ^ k) p :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have hdvd : orderOf (x' : G) ∣ Nat.gcd (2 ^ k) p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2k) (orderOf_dvd_of_pow_eq_one hpx)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    exact hx1 hdvd

end CFSG.LocalAnalysis.UniquenessCase.UC22

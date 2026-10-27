module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xf
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xg
import CFSG.GroupTheory.SylowNormalElements
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xh
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IrrOnMod)

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xm_sec7Hyp {D : Data G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) {B : Subgroup G} (hB1 : B ≠ ⊥)
    (hBM : B ≤ D.M) (hN : ¬ normalizer (B : Set G) ≤ D.M)
    (hr : 1 < CFSG.Open.pRank p (normalizer (B : Set G) ⊓ D.M)) :
    Sec7Hyp D p (normalizer (B : Set G)) := by
  refine ⟨hp, hp2, hsp, fun htop => ?_, hN, hr⟩
  haveI := D.standing.simple
  haveI : B.Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h | h
  · exact hB1 h
  · exact hsp.1 (top_le_iff.mp (by rw [← h]; exact hBM))

theorem uc22s13xm_exists_elem {M L T B : Subgroup G} (hLM : L ≤ M)
    (hLn : (L.subgroupOf M).Normal) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hBM : B ≤ M)
    (hB : Odd (Nat.card B)) (hBT : Permutes B T) {n : ℕ} (hn : IsPowTwo n)
    (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) {q : ℕ} (hq : q.Prime)
    (hqd : q ∣ 2 ^ n - 1 ∨ (IsU3 (Bar2 L) n ∧ q ∣ 2 ^ n + 1)) :
    ∃ x ∈ L, x ∈ centralizer (B : Set G) ∧ orderOf x = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hBN : B ≤ normalizer (L : Set G) :=
    hBM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn)
  obtain ⟨Q, t, -, -, -, h2, h3, -, hfix⟩ := uc22s13xf_fix_cartan hLM hLn hT hBN hB hBT hn hX
  have hsq : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [two_mul, pow_add, mul_self_tsub_one]
  have hqC : q ∣ Nat.card (cartan (Q : Subgroup (Bar2 L)) t) := by
    rcases hqd with hq1 | ⟨hU, hq1⟩
    · rcases hX with hL2 | hU
      · rw [h2 hL2]
        exact hq1
      · rw [h3 hU, hsq]
        exact Dvd.dvd.mul_left hq1 _
    · rw [h3 hU, hsq]
      exact Dvd.dvd.mul_right hq1 _
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' q hqC
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (d : Bar2 L)
  obtain ⟨c, hcB, hcl⟩ := uc22s13xh_exists_lift hBN hB l fun b hb => by
    rw [hl]
    exact hfix b hb d d.2
  have hcd : orderOf (QuotientGroup.mk c : Bar2 L) = q := by
    rw [hcl, hl, Subgroup.orderOf_coe, hd]
  have hqc : q ∣ orderOf (c : G) := by
    rw [Subgroup.orderOf_coe, ← hcd]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) c
  exact ⟨(c : G) ^ (orderOf (c : G) / q), Subgroup.pow_mem _ c.2 _, Subgroup.pow_mem _ hcB _,
    orderOf_pow_orderOf_div (orderOf_pos _).ne' hqc⟩

theorem uc22s13xm_exists_sylow {p : ℕ} (hp : p.Prime) {K : Subgroup G} {x : G} (hxK : x ∈ K)
    (hx : orderOf x = p) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P K ∧ x ∈ P ∧
      x ∈ CFSG.RankThree.PartOne.omegaOne p P := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP, hxP⟩ := UC6.exists_isSylowOf_ge (zpowers_le.mpr hxK) hZ
  have hxP' : x ∈ P := hxP (mem_zpowers x)
  exact ⟨P, hP, hxP', Subgroup.subset_closure ⟨hxP', by rw [← hx]; exact pow_orderOf_eq_one x⟩⟩

theorem uc22s13xm_orderOf_bar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Subgroup G} {x : G}
    (hxM : x ∈ M) (hx : orderOf x = p) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ : Bar2 M) = p := by
  have h0 : orderOf (⟨x, hxM⟩ : ↥M) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hx
  have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ : Bar2 M) ∣ p := by
    rw [← h0]
    exact orderOf_map_dvd _ _
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exfalso
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥M) ⟨_, h1⟩
    have h2k : x ^ 2 ^ k = 1 := by
      have := congrArg (fun z => ((z : ↥M) : G)) (congrArg Subtype.val hk)
      simpa using this
    have hpk : p ∣ 2 ^ k := by
      rw [← hx]
      exact orderOf_dvd_of_pow_eq_one h2k
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpk))
  · exact h1

theorem uc22s13xm_not_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L : Subgroup G}
    (hJ : barImage M L ⊓ centralizer (barImage M L : Set (Bar2 M)) = ⊥) {y : G} (hyM : y ∈ M)
    (hy : orderOf y = p)
    (hyc : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ : Bar2 M) ∈
      centralizer (barImage M L : Set (Bar2 M))) : y ∉ L := by
  intro hyL
  have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ : Bar2 M) ∈ barImage M L :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL)
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ : Bar2 M) = 1 := by
    have h : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ : Bar2 M) ∈
        (⊥ : Subgroup (Bar2 M)) := by
      rw [← hJ]
      exact Subgroup.mem_inf.mpr ⟨hmem, hyc⟩
    exact Subgroup.mem_bot.mp h
  have h2 := uc22s13xm_orderOf_bar hp hp2 hyM hy
  rw [h1, orderOf_one] at h2
  exact hp.one_lt.ne h2

theorem uc22s13xm_pRank_sup {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {J A B : Subgroup Q} (hJ : J ⊓ centralizer (J : Set Q) = ⊥)
    (hA : A ≤ centralizer (J : Set Q)) (hB : B ≤ J) :
    CFSG.Open.pRank p (A ⊔ B) = CFSG.Open.pRank p A + CFSG.Open.pRank p B := by
  refine PartTwo.s13_pRank_sup_eq_add hp (hB.trans (Subgroup.le_centralizer_iff.mp hA)) ?_
  rw [eq_bot_iff, ← hJ]
  exact le_inf (inf_le_right.trans hB) (inf_le_left.trans hA)

theorem uc22s13xm_one_le_pRank_zpowers {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {y : Q} (hy : orderOf y = p) : 1 ≤ CFSG.Open.pRank p (zpowers y) := by
  refine CFSG.SectionRank.le_pRank hp.one_lt le_rfl
    (CFSG.Open.isElemAbelian_zpowers (by rw [← hy]; exact pow_orderOf_eq_one y)) ?_
  rw [Nat.card_zpowers, hy, pow_one]

theorem uc22s13xm_succ_le_pRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M K : Subgroup G}
    (hKM : K ≤ M) {J A : Subgroup (Bar2 M)} (hJ : J ⊓ centralizer (J : Set (Bar2 M)) = ⊥)
    (hA : A ≤ centralizer (J : Set (Bar2 M))) (hAK : A ≤ barImage M K) {x : G} (hxK : x ∈ K)
    (hx : orderOf x = p)
    (hxJ : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hKM hxK⟩ : Bar2 M) ∈ J) :
    CFSG.Open.pRank p A + 1 ≤ CFSG.Open.pRank p K := by
  have hx'K : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hKM hxK⟩ : Bar2 M) ∈ barImage M K :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxK)
  have h1 := uc22s13xm_pRank_sup hp hJ hA (zpowers_le.mpr hxJ)
  have h2 := uc22s13xm_one_le_pRank_zpowers hp (uc22s13xm_orderOf_bar hp hp2 (hKM hxK) hx)
  have h3 := CFSG.SectionRank.pRank_mono (p := p) hp.one_lt (sup_le hAK (zpowers_le.mpr hx'K))
  rw [PartTwo.s13_pRank_barImage hp hp2 hKM] at h3
  omega

theorem uc22s13xm_false_of_alt1 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M H P D₀ L : Subgroup G}
    (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) {n : ℕ} (hn : IsPowTwo n)
    (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) (hP : CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M))
    (hexp : ∀ x ∈ D₀, x ^ p = 1) (h1 : H ⊓ M = H ⊓ normalizer (P : Set G))
    (h2 : IrrOnMod (rankThreeLayer H ⊓ normalizer (P : Set G)) D₀ (inSubgroup frattini D₀))
    (h3 : P = D₀) {x y : G} (hxD : x ∈ D₀) (hxL : x ∈ L) (hx1 : x ≠ 1) (hyHM : y ∈ H ⊓ M)
    (hy : orderOf y = p) (hyL : y ∉ L) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hPM : P ≤ M := hP.le.trans inf_le_right
  have hDL := uc22s13xg_le_of_alt1 hp hp2 hLM hLn hn hX hPM hexp h1 h2 h3 hxD hxL hx1
  have hMN : M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hK : (L.subgroupOf (H ⊓ M)).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have hg : ((g : ↥(H ⊓ M)) : G) ∈ normalizer (L : Set G) := hMN (Subgroup.mem_inf.mp g.2).2
    simpa using (Subgroup.mem_normalizer_iff.mp hg _).mp ha
  have hPL : P ≤ L := by
    rw [h3]
    exact hDL
  exact hyL (CFSG.GroupTheory.mem_of_normal_of_isSylowOf hK hP hPL hyHM (k := 1)
    (by rw [pow_one]; exact hy))

end CFSG.LocalAnalysis.UniquenessCase.UC22

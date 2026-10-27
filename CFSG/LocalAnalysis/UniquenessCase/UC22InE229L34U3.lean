module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34Rank
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z5U3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBU3
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.GroupTheory.WielandtProductBasic
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.LayerBasic
public import CFSG.Milestones.ASVolI.I2
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.GroupTheory.WielandtProduct (mem_smul_sylow_iff)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_l34_three_comm {M Y N B : Subgroup G} (hYM : Y ≤ M)
    (hnorm : M ≤ normalizer (Y : Set G)) (hNM : N ≤ M) (hBN : B ≤ N) (hB3 : IsPGroup 3 B)
    (hBc : Nat.card B = 3 ^ 2)
    (hN9 : ∀ R : Subgroup G, R ≤ N → IsPGroup 3 R → Nat.card R ≤ 3 ^ 2)
    (hBY : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M) :
    ∀ ρ ∈ N, IsPGroup 3 (zpowers ρ) → ∀ y ∈ Y, ρ * y * ρ⁻¹ * y⁻¹ ∈ pCoreOf 2 Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro ρ hρN hρ3 y hy
  obtain ⟨S, hS⟩ := (hB3.comap_subtype (K := N)).exists_le_sylow
  have hBS : B.subgroupOf N = S.toSubgroup := by
    refine Subgroup.eq_of_le_of_card_ge hS ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv, hBc]
    have := hN9 (S.toSubgroup.map N.subtype) (Subgroup.map_subtype_le _)
      (S.isPGroup'.map N.subtype)
    rwa [Subgroup.card_map_of_injective N.subtype_injective] at this
  obtain ⟨S', hS'⟩ := (hρ3.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥N) S' S
  have hρ' : (⟨ρ, hρN⟩ : ↥N) ∈ S' := hS' (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers ρ))
  have hmem : g * ⟨ρ, hρN⟩ * g⁻¹ ∈ S := by
    rw [← hg, mem_smul_sylow_iff]
    simpa [mul_assoc] using hρ'
  have hb : (g : G) * ρ * (g : G)⁻¹ ∈ B := by
    have h : g * ⟨ρ, hρN⟩ * g⁻¹ ∈ S.toSubgroup := hmem
    rw [← hBS] at h
    exact h
  have hgM : (g : G) ∈ M := hNM g.2
  have hy' : (g : G) * y * (g : G)⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.1 (hnorm hgM) y).1 hy
  have hc : (g : G)⁻¹ * ((g : G) * ρ * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) *
      ((g : G) * ρ * (g : G)⁻¹)⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹) * (g : G)⁻¹⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.1 (UC6S846.normalizer_le_normalizer_pCoreOf M
      (Subgroup.le_normalizer (M.inv_mem hgM))) _).1 (hBY _ hb _ hy')
  have heq : ρ * y * ρ⁻¹ * y⁻¹ = (g : G)⁻¹ * ((g : G) * ρ * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) *
      ((g : G) * ρ * (g : G)⁻¹)⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹) * (g : G)⁻¹⁻¹ := by group
  have hρM : ρ ∈ M := hNM hρN
  have hY : ρ * y * ρ⁻¹ * y⁻¹ ∈ Y :=
    Y.mul_mem ((Subgroup.mem_normalizer_iff.1 (hnorm hρM) y).1 hy) (Y.inv_mem hy)
  rw [heq] at hY ⊢
  exact uc22p2214_pCoreOf_inf_le hYM ⟨hc, heq ▸ hY⟩

theorem uc22ine229_pRank_le_bar (Y : Subgroup G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q Y ≤ CFSG.Open.pRank q (⊤ : Subgroup (Bar2 Y)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hN : ¬ q ∣ Nat.card (CFSG.pCore 2 ↥Y) := by
    intro hdvd
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
    rw [hn] at hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))
  rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥Y) hN,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]

theorem uc22ine229_l34_false_of_isSU3 (hT : uc22pwTorusSU3) (hgr : GriessAllModelsStatement)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (k : Sec7Core4 G) (hp3 : k.p = 3) {Y : Subgroup G} (hY : Y ∈ calC k.M) {n : ℕ}
    (hn : IsSU3 (Bar2 Y) n)
    (h846 : ∀ r : ℕ, r.Prime → 3 < r → r ∣ 2 ^ n + 1 → IsStronglyPEmbedded r k.M)
    {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hXc : Nat.card X = q)
    (hqn : q ∣ 2 ^ n - 1) (hH : Sec7Core4.Config k (normalizer (X : Set G)))
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥(normalizer (X : Set G)) ⧸
        CFSG.pPrimeCore k.p ↥(normalizer (X : Set G))))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩))
    {B₁ : Subgroup G} (hB₁M : B₁ ≤ k.M) (hB₁ : IsElemAbelian k.p B₁)
    (hB₁c : Nat.card B₁ = k.p ^ 2) (hB₁X : B₁ ≤ centralizer (X : Set G))
    (hB₁Y : ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 k.M) : False := by
  have hq2 : q ≠ 2 := by omega
  have hn2 := uc22ine229_two_le_of_isSU3 hn
  have hn3 : 3 ≤ n := by
    by_contra h
    obtain rfl : n = 2 := by omega
    have h3 : q ∣ 3 := by simpa using hqn
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · obtain rfl : n = 3 := by omega
    have hq1 : CFSG.Open.pRank q Y ≤ 1 :=
      (uc22ine229_pRank_le_bar Y hq hq2).trans (uc22ine229_pRank_le_one_of_isSU3 hn hq hq2
        (uc22ine229_not_dvd_two_pow_add_one hq hq2 hqn)
        (uc22ine229_not_dvd_card_center hgr hn hq hq2 hqn))
    obtain ⟨hnorm, -, -, h9⟩ := uc22ine229_l34_decomp hG3 hRee k hp3 hY hXY hq hq5 hXc hq1 hH hF
    have hBN : B₁ ≤ normalizer (X : Set G) ⊓ k.M :=
      fun b hb => ⟨Subgroup.centralizer_le_normalizer _ (hB₁X hb), hB₁M hb⟩
    have hB3 : IsPGroup 3 B₁ := fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa [hp3] using hB₁.2 x x.2)⟩
    have hcomm := uc22ine229_l34_three_comm hY.1.le hnorm inf_le_right hBN hB3
      (by rw [hB₁c, hp3]) (fun R hR hR3 => h9 R (hR.trans inf_le_left) hR3) hB₁Y
    obtain ⟨ρ, hρ, hρ3, y, hy, hne⟩ := uc22ine229_exists_three_noncentral hT hgr hY (by norm_num)
      hn (by norm_num) hq hq5 hqn hXY hXc
    exact hne (hcomm ρ ⟨hρ.2, hY.1.le hρ.1⟩ hρ3 y hy)
  · obtain ⟨r, hr, hr3, hrn⟩ := UC6S898.exists_prime_gt_three_dvd (by omega) (by omega)
    obtain ⟨ρ, hρ, hρo⟩ := uc22ine229_exists_prime_order_normalizer hT hgr hY (by omega) hn hq hq5
      hqn hXY hXc hr hr3 hrn
    have hr5 : 5 ≤ r := by
      have : r ≠ 4 := by
        rintro rfl
        norm_num at hr
      omega
    refine uc22ine229_l34_not_dvd hG3 hRee k hp3 hH hF hr hr5 (h846 r hr hr3 hrn) ?_
    rw [← hρo]
    exact Subgroup.orderOf_dvd_natCard _ (show ρ ∈ normalizer (X : Set G) ⊓ k.M from
      ⟨hρ.2, hY.1.le hρ.1⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22

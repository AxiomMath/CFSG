module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.E9O2Normal
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Thin
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34Rank
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3CZL34
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Layer3
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3B1
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (Standing Setup)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

variable {G : Type} [Group G] [Finite G]

theorem sup_pCoreOf_normal_of_mul {M Y N B : Subgroup G} (hNM : N ≤ M)
    (hNB : N ≤ normalizer (B : Set G)) (hmul : ∀ m ∈ M, ∃ h ∈ N, ∃ y ∈ Y, m = h * y)
    (hBY : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M) :
    ((B ⊔ pCoreOf 2 M).subgroupOf M).Normal := by
  have hQN : ∀ g ∈ M, ∀ x ∈ pCoreOf 2 M, g * x * g⁻¹ ∈ pCoreOf 2 M := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg) x).mp hx
  have key : ∀ g ∈ M, ∀ b ∈ B, g * b * g⁻¹ ∈ B ⊔ pCoreOf 2 M := by
    intro g hg b hb
    obtain ⟨h, hh, y, hy, rfl⟩ := hmul g hg
    have hc := hBY b hb y hy
    have h2 : h * y * b * (h * y)⁻¹ =
        (h * (b * y * b⁻¹ * y⁻¹)⁻¹ * h⁻¹) * (h * b * h⁻¹) := by group
    rw [h2]
    exact mul_mem (Subgroup.mem_sup_right (hQN h (hNM hh) _ (inv_mem hc)))
      (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hNB hh) b).mp hb))
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hle : B ⊔ pCoreOf 2 M ≤ (B ⊔ pCoreOf 2 M).comap (MulAut.conj (g : G)).toMonoidHom :=
    sup_le (fun b hb => key g g.2 b hb) (fun x hx => Subgroup.mem_sup_right (hQN g g.2 x hx))
  simpa [Subgroup.mem_comap, MulAut.conj_apply] using hle hn

theorem inf_le_normalizer_of_l34 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    (h75 : Sec7Core4.Step75 k) {H : Subgroup G} (hH : Sec7Core4.Config k H)
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩))
    (h9 : ∀ R : Subgroup G, R ≤ H → IsPGroup 3 R → Nat.card R ≤ 3 ^ 2)
    {B₁ : Subgroup G} (hB₁H : B₁ ≤ H) (hB₁M : B₁ ≤ k.M) (hB₁ : IsPGroup 3 B₁)
    (hB₁c : Nat.card B₁ = 3 ^ 2) :
    H ⊓ k.M ≤ normalizer (B₁ : Set G) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  have hB₁p : IsPGroup k.p B₁ := hp3 ▸ hB₁
  have hB₁HM : B₁ ≤ H ⊓ k.M := le_inf hB₁H hB₁M
  have hB₁' : IsPGroup k.p ↥(B₁.subgroupOf (H ⊓ k.M)) :=
    hB₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hB₁HM).symm
  obtain ⟨Q, hQ⟩ := hB₁'.exists_le_sylow
  set P : Subgroup G := (Q : Subgroup ↥(H ⊓ k.M)).map (H ⊓ k.M).subtype with hPdef
  have hBP : B₁ ≤ P := by
    intro b hb
    exact ⟨⟨b, hB₁HM hb⟩, hQ (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  have hPH : P ≤ H := (Subgroup.map_subtype_le _).trans inf_le_left
  have hPp : IsPGroup 3 P := by
    intro g
    obtain ⟨n, hn⟩ := Q.isPGroup'.map (H ⊓ k.M).subtype g
    exact ⟨n, by rw [← hp3]; exact hn⟩
  have hPB : P = B₁ :=
    (Subgroup.eq_of_le_of_card_ge hBP (by rw [hB₁c]; exact h9 P hPH hPp)).symm
  have hSyl : CFSG.ABGLocalTools.IsSylowOf k.p B₁ (H ⊓ k.M) := ⟨Q, hPB⟩
  obtain ⟨P', hP', hP'N⟩ := k.exists_sylow_map_of_isSylowOf hH hSyl
  have hBbar : IsPGroup 3 ↥((B₁.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) :=
    (hB₁.of_equiv (Subgroup.subgroupOfEquivOfLe hB₁H).symm).map _
  have hPL := R847E3.le_generalizedFitting_of_l34 hG3 hRee k hp3 hH hF hBbar
  have hPK := k.commutator_pPrimeCore_eq_bot_of_isPGroup h75 hH hB₁H hB₁p hPL
  have hN := (k.inf_eq_and_le_normalizer_quotient hG3 hp3 hH P' hP'N).2
  rw [hP', inf_eq_left.mpr hPL] at hN
  intro m hm
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.mem_normalizer_of_mk_mem_normalizer
    (p := k.p) hB₁H hB₁p hPK
    (h := ⟨m, hm.1⟩) (hN (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hm)))

theorem e9O2Normal_of_l34 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    (h75 : Sec7Core4.Step75 k) {Y : Subgroup G} (hY : Y ∈ calC k.M) {X : Subgroup G}
    (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hXc : Nat.card X = q)
    (hq1 : CFSG.Open.pRank q Y ≤ 1) (hH : Sec7Core4.Config k (normalizer (X : Set G)))
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥(normalizer (X : Set G)) ⧸
        CFSG.pPrimeCore k.p ↥(normalizer (X : Set G))))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩))
    {B₁ : Subgroup G} (hB₁M : B₁ ≤ k.M) (hB₁ : IsElemAbelian 3 B₁) (hB₁c : Nat.card B₁ = 3 ^ 2)
    (hB₁X : B₁ ≤ centralizer (X : Set G))
    (hB₁Y : ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 k.M) :
    E9O2Normal k.M := by
  obtain ⟨-, hmul, -, h9⟩ := uc22ine229_l34_decomp hG3 hRee k hp3 hY hXY hq hq5 hXc hq1 hH hF
  have hB₁N : B₁ ≤ normalizer (X : Set G) :=
    hB₁X.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hNB := inf_le_normalizer_of_l34 hG3 hRee k hp3 h75 hH hF h9 hB₁N hB₁M hB₁.isPGroup hB₁c
  exact ⟨B₁, hB₁M, hB₁, hB₁c, sup_pCoreOf_normal_of_mul inf_le_right hNB hmul hB₁Y⟩

theorem normalizer_le_or_e9O2Normal_of_thin_three (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G)
    (hp : 3 ∈ (dataOfSetup hS S).sig) {Y : Subgroup G} (hY : Y ∈ calC S.M)
    (hYN : (Y.subgroupOf S.M).Normal) (hthin : F08.Thin8 Y) {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q) :
    normalizer (X : Set G) ≤ S.M ∨ E9O2Normal S.M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  have hK : CFSG.Open.IsKGroup ↥S.M := hS.kProper.isKGroup S.M hsp.1
  have hYM : Y ≤ S.M := hY.1.le
  have hMN : S.M ≤ normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).1 hYN
  have hOp := UC6.opRes_eq_of_stronglyEmbedded_uc6 hS.simple hS.nonab Nat.prime_three hsp
  have h3 := hSg.three_le 3 hp
  refine R847E3.normalizer_le_or_of_thin_three_of_l34 (A := E9O2Normal) hG3 hRee hK3 ?_ hS S hp
    hY hthin ?_ hq hq5 hXY hXc
  · intro k hp3 h75 Y' hY' X' hXY' q' hq' hq5' hXc' hq1 hH hF B₁ hB₁M hB₁ hB₁c hB₁X hB₁Y
    exact e9O2Normal_of_l34 hG3 hRee k hp3 h75 hY' hXY' hq' hq5' hXc' hq1 hH hF hB₁M hB₁ hB₁c
      hB₁X hB₁Y
  · intro q hq hq5 X hXY hXc
    have hq2 : q ≠ 2 := by omega
    have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
    exact R847E3.exists_B₁_of_thin hThin hCyc hK hY hMN hthin Nat.prime_three (by norm_num) hOp
      h3 hXY hq hq2 hXq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17


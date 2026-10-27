module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.GH74.Constrained

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105U3Quot
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTen
import CFSG.GroupTheory.Fitting.LayerProjection
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpCoreSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

private lemma ncl_conj_mem {N B' : Subgroup G} {n : G} (hn : n ∈ N)
    {x : G} (hx : x ∈ ncl N B') : n * x * n⁻¹ ∈ ncl N B' := by
  unfold ncl at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨g, hg, b, hb, rfl⟩ := hy
      have hmem : n * (g * b * g⁻¹) * n⁻¹ = (n * g) * b * (n * g)⁻¹ := by group
      rw [hmem]
      exact Subgroup.subset_closure ⟨n * g, mul_mem hn hg, b, hb, rfl⟩
  | one => simp
  | mul a b ha hb iha ihb =>
      have h : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ iha ihb
  | inv a ha iha =>
      have h : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ iha

private lemma ncl_subgroupOf_normal {N B' : Subgroup G} :
    ((ncl N B').subgroupOf N).Normal := by
  refine ⟨fun n hn g => ?_⟩
  simp only [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using ncl_conj_mem g.2 hn

private lemma ncl_image_normal {N B' : Subgroup G}
    [hI : ((relPPrimeCore 3 N).subgroupOf N).Normal] :
    (((ncl N B').subgroupOf N).map
      (QuotientGroup.mk' ((relPPrimeCore 3 N).subgroupOf N))).Normal := by
  have hsurj : Function.Surjective
      (QuotientGroup.mk' ((relPPrimeCore 3 N).subgroupOf N)) :=
    QuotientGroup.mk'_surjective _
  have hN₂ : ((ncl N B').subgroupOf N).Normal := ncl_subgroupOf_normal
  exact hN₂.map _ hsurj

private lemma ncl_le {N B' : Subgroup G} (hB'N : B' ≤ N) : ncl N B' ≤ N := by
  rw [ncl, Subgroup.closure_le]
  rintro y ⟨g, hg, x, hx, rfl⟩
  exact N.mul_mem (N.mul_mem hg (hB'N hx)) (N.inv_mem hg)

private def quotientMapNcl {N B' : Subgroup G} (hB'N : B' ≤ N)
    [hI : ((relPPrimeCore 3 N).subgroupOf N).Normal] :
    ↥(ncl N B') →*
      ↥(((ncl N B').subgroupOf N).map
        (QuotientGroup.mk' ((relPPrimeCore 3 N).subgroupOf N))) where
  toFun x := ⟨QuotientGroup.mk' _ ⟨x.1, ncl_le hB'N x.2⟩,
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 x.2)⟩
  map_one' := by rfl
  map_mul' := by intro a b; rfl

private lemma quotientMapNcl_surjective {N B' : Subgroup G} (hB'N : B' ≤ N)
    [hI : ((relPPrimeCore 3 N).subgroupOf N).Normal] :
    Function.Surjective (quotientMapNcl hB'N) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
  exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, Subtype.ext hxy⟩

private lemma relPPrimeCore_subgroupOf_normal (N : Subgroup G) :
    ((relPPrimeCore 3 N).subgroupOf N).Normal :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
    Nat.prime_three N

private lemma pPrimeCore_quotient_eq_bot (N : Subgroup G)
    [hI : ((relPPrimeCore 3 N).subgroupOf N).Normal] :
    CFSG.pPrimeCore 3 (↥N ⧸ (relPPrimeCore 3 N).subgroupOf N) = ⊥ := by
  have hIeq : (relPPrimeCore 3 N).subgroupOf N = CFSG.pPrimeCore 3 ↥N := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three N]
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  haveI : (CFSG.pPrimeCore 3 ↥N).Normal := CFSG.pPrimeCore_normal
  let e := QuotientGroup.quotientMulEquivOfEq hIeq
  have h := CFSG.pPrimeCore_map_iso 3 e
  have hY' : CFSG.pPrimeCore 3 (↥N ⧸ CFSG.pPrimeCore 3 ↥N) = ⊥ :=
    CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥N 3
  rw [hY'] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

private lemma quotientMapNcl_ker {N B' : Subgroup G} (hB'N : B' ≤ N)
    [hI : ((relPPrimeCore 3 N).subgroupOf N).Normal] :
    (quotientMapNcl hB'N).ker = (relPPrimeCore 3 N).subgroupOf (ncl N B') := by
  ext x
  constructor
  · intro hx
    simp only [MonoidHom.mem_ker, quotientMapNcl] at hx
    have h := Subtype.ext_iff.1 hx
    rw [Subgroup.mem_subgroupOf]
    have h' := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h'
    simp only [mul_one] at h'
    simpa [Subgroup.inv_mem_iff] using h'
  · intro hx
    simp only [MonoidHom.mem_ker, quotientMapNcl]
    refine Subtype.ext (QuotientGroup.eq.2 ?_)
    rw [mul_one, Subgroup.inv_mem_iff]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx)

private lemma kOf8103_le_N {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : F08.KOf8103 L B ≤ N :=
  c.memH.2.2.1.trans c.memN.2

private lemma kOf8103_le_M {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : F08.KOf8103 L B ≤ D.M :=
  c.memH.2.2.1.trans c.memH.1

private lemma commutator_kOf8103 (L B : Subgroup G) :
    ⁅F08.KOf8103 L B, F08.KOf8103 L B⁆ = F08.KOf8103 L B := by
  haveI : Group.IsPerfect ↥(F08.KOf8103 L B) := isPerfect_derInf8 (L ⊓ centralizer (B : Set G))
  exact CFSG.GroupTheory.commutator_eq_self_of_isPerfect_subgroup

private lemma ne_top_of_ctx {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : N ≠ ⊤ := by
  haveI := D.standing.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab c.memN.1.1

private lemma relPPrimeCore_le_N (N : Subgroup G) : relPPrimeCore 3 N ≤ N :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N

private theorem isU3_map (hU3 : KU3Ident) (h332 : UCK.K332ThreeAb) (hS : KSuzukiL2)
    {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    (hQ : pCoreOf 2 N ≤ D.M) [((relPPrimeCore 3 N).subgroupOf N).Normal] :
    UC22.IsU3 ↥(((ncl N B').subgroupOf N).map
      (QuotientGroup.mk' ((relPPrimeCore 3 N).subgroupOf N))) (2 * n) := by
  have hKN := kOf8103_le_N c
  have hJN := relPPrimeCore_le_N N
  have hJ3 := prime_not_dvd_card_relPPrimeCore Nat.prime_three N
  have hB'N : B' ≤ N := c.le.trans hKN
  have hD₀N : D₀ ≤ N := c.le_D₀.trans hKN
  have hcop : Nat.Coprime (Nat.card D₀) (Nat.card (relPPrimeCore 3 N)) := by
    rw [c.card_D₀]
    exact (Nat.Prime.coprime_iff_not_dvd c.prime).2 (not_dvd_card_relPPrimeCore c)
  refine hU3 (↥N ⧸ (relPPrimeCore 3 N).subgroupOf N)
    ((D.standing.kProper.isKGroup N (ne_top_of_ctx c)).quotient _) (pPrimeCore_quotient_eq_bot N)
    (((ncl N B').subgroupOf N).map (QuotientGroup.mk' ((relPPrimeCore 3 N).subgroupOf N)))
    (((F08.KOf8103 L B).subgroupOf N).map (QuotientGroup.mk' ((relPPrimeCore 3 N).subgroupOf N)))
    ((D₀.subgroupOf N).map (QuotientGroup.mk' ((relPPrimeCore 3 N).subgroupOf N))) n p
    ncl_image_normal ?_ (map_ncl_eq_normalClosure hB'N c.le (kOf8103_le_ncl c))
    (commutator_map_mk'_eq hKN (commutator_kOf8103 L B))
    (isL2_bar2_map_mk' hKN hJN hJ3 (by have := c.two_le; omega) c.notB.2.2) c.two_le c.even
    c.prime c.dvd
    (Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.2 (c.le_D₀ (Subgroup.mem_subgroupOf.1 hx)))
    ((card_map_mk'_eq hD₀N hJN hcop).trans c.card_D₀) ?_ ?_
  · rw [pRank_map_mk'_eq Nat.prime_three (ncl_le hB'N) hJN hJ3]
    exact pRank_ncl h332 c (Or.inr rfl)
  · rintro y ⟨hyX, hyC⟩
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hyX
    have hxM : (x : G) ∈ D.M :=
      mem_of_commutator_mem hS c hQ x.2 (commutator_mem_of_mk'_mem_centralizer hD₀N hyC)
    exact mk'_mem_normalizer_map hKN hJN (inf_le_normalizer h332 c ⟨hxM, x.2⟩)
  · intro hXK
    exact not_ncl_le c ((le_sup_of_map_mk'_eq (ncl_le hB'N) hXK).trans
      (sup_le (kOf8103_le_M c) (relPPrimeCore_le hS c hQ)))

theorem isU3_ncl (hU3 : KU3Ident) (h332 : UCK.K332ThreeAb) (hS : KSuzukiL2) {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    (hQ : pCoreOf 2 N ≤ D.M) :
    ∃ (X : Type) (_ : Group X) (φ : ↥(ncl N B') →* X), Function.Surjective φ ∧
      φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B') ∧ UC22.IsU3 X (2 * n) := by
  haveI := relPPrimeCore_subgroupOf_normal N
  have hB'N : B' ≤ N := c.le.trans (kOf8103_le_N c)
  exact ⟨_, inferInstance, quotientMapNcl hB'N, quotientMapNcl_surjective hB'N,
    quotientMapNcl_ker hB'N, isU3_map hU3 h332 hS c hQ⟩

theorem false_of_sylow (hU3 : KU3Ident) (hF : KU3Facts) (h332 : UCK.K332ThreeAb)
    (hS : KSuzukiL2) {D : Data G} {L P B B' D₀ H N T : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (hT : IsSylowOf 2 T N) (hTM : T ≤ D.M) : False := by
  haveI := relPPrimeCore_subgroupOf_normal N
  have hKN := kOf8103_le_N c
  have hJN := relPPrimeCore_le_N N
  have hTN : T ≤ N := by
    obtain ⟨Q, rfl⟩ := hT
    exact Subgroup.map_subtype_le _
  have hQ : pCoreOf 2 N ≤ D.M :=
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section12.pCoreOf_le_of_isSylowOf hT).trans hTM
  have h2n : 4 ≤ 2 * n := by have := c.two_le; omega
  exact false_of_isSylowOf_le_normalizer hF (isU3_map hU3 h332 hS c hQ) h2n (even_two_mul n)
    ncl_image_normal
    (Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.2 (kOf8103_le_ncl c (Subgroup.mem_subgroupOf.1 hx)))
    (commutator_map_mk'_eq hKN (commutator_kOf8103 L B))
    (isL2_bar2_map_mk' hKN hJN (prime_not_dvd_card_relPPrimeCore Nat.prime_three N) (by omega)
      c.notB.2.2)
    (isSylowOf_map_mk' hT)
    (map_mk'_le_normalizer_map hKN hJN fun t ht => inf_le_normalizer h332 c ⟨hTM ht, hTN ht⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

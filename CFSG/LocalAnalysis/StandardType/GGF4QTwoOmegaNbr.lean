module

public import CFSG.LocalAnalysis.StandardType.GGF4QTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmCent
import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof3
import CFSG.LocalAnalysis.StandardType.GGF4QTwoHypA
import CFSG.LocalAnalysis.StandardType.GGF4QTwoOmegaEnd
import CFSG.LocalAnalysis.StandardType.GGF4QTwoOmegaNbrCore
import CFSG.LocalAnalysis.StandardType.GGHalfRowData
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

private theorem ggBstar {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) : GGBstar 3 B Bs :=
  hR.1.2.1

private theorem x_mem_bstar {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) : x ∈ Bs :=
  hR.1.tableB_facts.2.2.1

private theorem y_mem_bstar {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) {y : G}
    {K : Subgroup G} (hNb : GGNbr 3 B x D J y K) : y ∈ Bs :=
  hR.1.2.1.1 hNb.1.2.1

private theorem L_le_centralizer {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) :
    L ≤ Subgroup.centralizer {x} :=
  hR.1.tableB_facts.2.2.2.1

private theorem K_le_centralizer {G : Type} [Group G] [Finite G] {B : Subgroup G} {x : G}
    {D J : Subgroup G} {y : G} {K : Subgroup G} (hNb : GGNbr 3 B x D J y K) :
    K ≤ Subgroup.centralizer {y} :=
  hNb.1.2.2.2.1

private theorem bstar_le_normalizer_L {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) :
    Bs ≤ Subgroup.normalizer (L : Set G) :=
  GGInnerDiagOn.le_normalizer hR.2.2.1.1

private theorem bstar_le_normalizer_K {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) {y : G}
    {K : Subgroup G} (hNb : GGNbr 3 B x D J y K) :
    Bs ≤ Subgroup.normalizer (K : Set G) :=
  GGInnerDiagOn.le_normalizer (hR.2.2.1.2 y K hNb)

private theorem bstar_inf_centralizer_L {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) :
    Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
  hR.1.bstar_inf_centralizer_L

theorem ggF4QTwoOmegaNbr_D_facts {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J) {y : G}
    {K : Subgroup G} (hNb : GGNbr 3 B x D J y K) :
    D ≤ Bs ∧ x ∈ D ∧ y ∈ D ∧ Nat.card ↥D = 9 := by
  obtain ⟨hDB, -, hDc, hxD, -⟩ := hC.2.2.1
  refine ⟨hDB.trans hC.2.1.1, hxD, ?_, by rw [hDc]; norm_num⟩
  rw [hNb.2.1]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem ggF4QTwoOmegaNbr_y_not_mem_zpowers_x {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J) {y : G}
    {K : Subgroup G} (hNb : GGNbr 3 B x D J y K) :
    y ∉ Subgroup.zpowers x := by
  intro hy
  have := Fact.mk Nat.prime_three
  have hS : CFSG.Assembly.LargeEvenSStar 3 B x L := hC.1.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hyB : y ∈ B := hNb.1.2.1
  have hox : orderOf x = 3 := orderOf_eq_prime (hS.1.1.2 x hxB) hS.2.2.1
  have hoy : orderOf y = 3 := orderOf_eq_prime (hS.1.1.2 y hyB) hNb.1.2.2.1
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoy])
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hNb.1.2.2.2.1 hk)
  have hz : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
    heq ▸ Subgroup.zpowers_le.mpr hyK
  apply hNb.2.2.2
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hz)]
  exact bot_le

theorem ggF4QTwoOmegaNbr_hasLabel_of_marking_twD41 {X : Type} [Group X]
    (h : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    GGHasLabel ⟨.twD, 4, 1⟩ (X ⧸ Subgroup.center X) := by
  obtain ⟨⟨t, r, m⟩, -, hHas, -, -, -, -, -, ht, hr, hm⟩ := largeEvenMarking_exists_hasLabel h
  dsimp only at ht hr hm
  subst ht hr hm
  exact hHas

open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal in
private theorem card_le_of_isElemAbelian_twoOmega {E : Subgroup ↥Two.omega}
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card ↥E ≤ 3 ^ 3 := by
  have h3 : (3 : ZMod 2) ≠ 0 := by decide +kernel
  have hbc : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide +kernel
  have hQ : (QuadraticMap.polarBilin (modelForm (1 : ZMod 2) 1)).Nondegenerate :=
    nondegenerate_polarBilin_modelForm h3 hbc
  have hdim : Module.finrank (ZMod 2) (ModelSpace (ZMod 2)) = 2 * 4 := by
    rw [← (toModelIso h3 hbc).toLinearEquiv.finrank_eq]
    exact CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (by norm_num)
  have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (modelForm (1 : ZMod 2) 1) := fun h =>
    CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := 4) (by norm_num) hbc
      ((CFSG.GroupTheory.WeirSylow.isPlusType_congr (toModelIso h3 hbc)).mpr h)
  have hΩ : Two.omega = CFSG.RankThree.Classical2.orthDerived (modelForm (1 : ZMod 2) 1) := rfl
  have hE' : CFSG.Open.IsElemAbelian 3 (E.map (MulEquiv.subgroupCongr hΩ).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have h := CFSG.LocalAnalysis.GLTheoremA.T171S.card_le_three_pow_three_orthDerived_minus_eight
    hQ hdim hminus _ hE'
  rwa [Subgroup.card_map_of_injective (MulEquiv.subgroupCongr hΩ).injective] at h

private theorem card_le_of_isElemAbelian_le_of_marking_twD41 {G : Type} [Group G]
    {N : Subgroup G} (hZ : Subgroup.center ↥N = ⊥)
    (hN : LargeEvenMarking ↥N
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1))
    {E : Subgroup G} (hEN : E ≤ N) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card ↥E ≤ 3 ^ 3 := by
  obtain ⟨ψ⟩ := nonempty_mulEquiv_twoOmega_of_marking hZ hN
  have hE₁ : CFSG.Open.IsElemAbelian 3 (E.comap N.subtype) :=
    E6IDB.isElemAbelian_comap hE N.subtype_injective
  have hE₂ : CFSG.Open.IsElemAbelian 3 ((E.comap N.subtype).map ψ.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE₁ _
  have h := card_le_of_isElemAbelian_twoOmega hE₂
  rwa [Subgroup.card_map_of_injective ψ.injective,
    show Nat.card ↥(E.comap N.subtype) = Nat.card ↥E from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv] at h

theorem ggF4QTwoOmegaNbr_card_bstar
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hIL : GGInnerDiagOn Bs L)
    (hL : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    Nat.card ↥Bs = 3 ^ 4 := by
  have hcfg := hC
  obtain ⟨-, hBsE, -, -, h81⟩ := hcfg.tableB_facts
  obtain ⟨hZ, hinner⟩ :=
    ggHalfRowDataInput_holds G Bs L hIL
      (Or.inl (ggF4QTwoOmegaNbr_hasLabel_of_marking_twD41 hL))
  have hsplit := card_ggBstar_split hcfg.2.1 hZ (GGInnerDiagOn.le_normalizer hIL) hinner
  rw [hcfg.card_bstar_inf_centralizer_L] at hsplit
  have hle := card_le_of_isElemAbelian_le_of_marking_twD41 hZ hL (E := Bs ⊓ L) inf_le_right
    (CFSG.Open.IsElemAbelian.mono hBsE inf_le_left)
  rw [show (3 : ℕ) ^ 3 = 27 by norm_num] at hle
  rw [show (3 : ℕ) ^ 4 = 81 by norm_num] at h81 ⊢
  omega

theorem ggF4QTwoOmegaNbr_card_bstar_inf_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hIL : GGInnerDiagOn Bs L)
    (hL : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    Nat.card ↥(Bs ⊓ L) = 27 := by
  obtain ⟨hZ, hinner⟩ :=
    ggHalfRowDataInput_holds G Bs L hIL
      (Or.inl (ggF4QTwoOmegaNbr_hasLabel_of_marking_twD41 hL))
  exact card_bstar_inf_of_split hC.2.1 hZ (GGInnerDiagOn.le_normalizer hIL) hinner
    hC.bstar_inf_centralizer_L (ggF4QTwoOmegaNbr_card_bstar hC hIL hL) hC.orderOf_x

theorem ggF4QTwoOmegaNbr_B_eq_bstar
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hIL : GGInnerDiagOn Bs L)
    (hL : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    B = Bs := by
  have hcfg := hC
  obtain ⟨⟨-, -, -, -, -, hβ, hS, -⟩, hBs, -⟩ := hcfg
  have hB : Nat.card B = 3 ^ CFSG.Open.twoLocalPrimeRank 3 G := hS.1.2.1
  have h4 : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G := hβ.2.2.2
  apply Subgroup.eq_of_le_of_card_ge hBs.1
  rw [ggF4QTwoOmegaNbr_card_bstar hC hIL hL, hB]
  exact Nat.pow_le_pow_right (by norm_num) h4

private theorem bstar_inf_centralizer_K
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hNb : GGNbr 3 B x D J y K)
    (hL : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  rw [← ggF4QTwoOmegaNbr_B_eq_bstar hR.1 hR.2.2.1.1 hL]
  exact inf_centralizer_eq_zpowers_of_sHat hNb.1

private theorem L_normal_centralizer
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hL : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    (L.subgroupOf (Subgroup.centralizer {x})).Normal := by
  have hS : CFSG.Assembly.LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  obtain ⟨-, hBsE, -, -, -⟩ := hR.1.tableB_facts
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (L_le_centralizer hR)]
  refine le_normalizer_of_isComponentOf_cyclic hS.2.2.2.1
    (fun S _ hSL hS3 => hS.2.2.2.2 S hSL hS3) ⟨Bs ⊓ L, inf_le_right, ?_, ?_⟩
  · exact CFSG.Open.IsElemAbelian.isPGroup (CFSG.Open.IsElemAbelian.mono hBsE inf_le_left)
  · refine TableB.not_isCyclic_of_card (by norm_num) (fun g hg => hBsE.2 g hg.1) ?_
    rw [ggF4QTwoOmegaNbr_card_bstar_inf_L hR.1 hR.2.2.1.1 hL]
    norm_num

theorem ggF4QTwoOmegaNbr_J_le {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J) :
    J ≤ L ∧ J ≤ Subgroup.centralizer (D : Set G) := by
  obtain ⟨-, -, -, -, -, ⟨hJle, -, -⟩, -⟩ := hC.2.2.1
  exact ⟨hJle.trans inf_le_left, hJle.trans inf_le_right⟩

theorem ggF4QTwoOmegaNbr_J_perfect_ne_bot {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J) :
    ⁅J, J⁆ = J ∧ J ≠ ⊥ := by
  obtain ⟨-, -, -, -, -, ⟨-, -, hJq⟩, -⟩ := hC.2.2.1
  refine ⟨?_, fun hJ => ?_⟩
  · rw [← J.map_subtype_commutator, hJq.1, ← MonoidHom.range_eq_map, J.range_subtype]
  · have h1 := (Subgroup.eq_bot_iff_forall J).mp hJ
    obtain ⟨a, b, hab⟩ := hJq.2.toNontrivial.exists_pair_ne
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have hab' : a' = b' := Subtype.ext ((h1 a' a'.2).trans (h1 b' b'.2).symm)
    exact hab (congrArg _ hab')

theorem ggF4QTwoOmegaNbr_bstar_inf_centralizer_J
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hIL : GGInnerDiagOn Bs L)
    (hL : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  obtain ⟨-, -, -, -, -, -, hDJ⟩ := hC.2.2.1
  rw [← ggF4QTwoOmegaNbr_B_eq_bstar hC hIL hL, ← hDJ]

theorem not_twD41_nbr_of_twD41_end
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hNb : GGNbr 3 B x D J y K)
    (hW : GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hL : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    ¬ LargeEvenMarking ↥K (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1) := by
  intro hK
  have hBstar := ggBstar hR
  have hcard := ggF4QTwoOmegaNbr_card_bstar hR.1 hR.2.2.1.1 hL
  obtain ⟨hZL, hinL⟩ :=
    ggHalfRowDataInput_holds G Bs L hR.2.2.1.1
      (Or.inl (ggF4QTwoOmegaNbr_hasLabel_of_marking_twD41 hL))
  obtain ⟨hZK, hinK⟩ :=
    ggHalfRowDataInput_holds G Bs K (hR.2.2.1.2 y K hNb)
      (Or.inl (ggF4QTwoOmegaNbr_hasLabel_of_marking_twD41 hK))
  obtain ⟨τx, hEx⟩ := exists_ggOmegaTwoEndCoords hBstar hcard (x_mem_bstar hR)
    (L_le_centralizer hR) hZL hL (bstar_le_normalizer_L hR) hinL (bstar_inf_centralizer_L hR)
  obtain ⟨τy, hEy⟩ := exists_ggOmegaTwoEndCoords hBstar hcard (y_mem_bstar hR hNb)
    (K_le_centralizer hNb) hZK hK (bstar_le_normalizer_K hR hNb) hinK
    (bstar_inf_centralizer_K hR hNb hL)
  obtain ⟨-, hxD, hyD, hDcard⟩ := ggF4QTwoOmegaNbr_D_facts hR.1 hNb
  obtain ⟨hJL, hJD⟩ := ggF4QTwoOmegaNbr_J_le hR.1
  obtain ⟨hJJ, hJbot⟩ := ggF4QTwoOmegaNbr_J_perfect_ne_bot hR.1
  exact false_of_ggOmegaTwoEndCoords hBstar.2.1 hcard hW (x_mem_bstar hR) (y_mem_bstar hR hNb)
    (L_le_centralizer hR) (K_le_centralizer hNb) hEx hEy (L_normal_centralizer hR hL)
    hxD hyD hDcard (ggF4QTwoOmegaNbr_y_not_mem_zpowers_x hR.1 hNb) hJL hJD hJJ hJbot
    (ggF4QTwoOmegaNbr_bstar_inf_centralizer_J hR.1 hR.2.2.1.1 hL)

theorem ggF4QTwoEndsKInput_of_kl
    (hKl : GGF4QTwoEndsKlInput) : GGF4QTwoEndsKInput := by
  intro G _ _ B Bs x L D J hR hWc hq y K hNb hW hL
  rcases hKl G B Bs x L D J hR hWc hq y K hNb hW hL with h | h
  · exact h
  · exact absurd h (not_twD41_nbr_of_twD41_end hR hNb hW hL)

end CFSG.StandardType

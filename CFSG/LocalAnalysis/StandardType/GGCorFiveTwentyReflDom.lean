module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNS
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith
public import CFSG.LocalAnalysis.StandardType.GGNbrPrimeFieldExcl
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Labels

private theorem four_pow_sub_one_eq (n : ℕ) : 4 ^ n - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
  have h4 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
    calc (4 : ℕ) ^ n = (2 * 2) ^ n := by norm_num
      _ = 2 ^ n * 2 ^ n := mul_pow 2 2 n
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [h4, hk]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  exact Nat.sub_eq_of_eq_add (by ring)

private theorem two_pow_sq_eq (n : ℕ) : (2 ^ n) ^ 2 = 4 ^ n := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem ggLabPhiOneTwo_of_largeEvenSplit {p : ℕ} {lab : LargeEvenLabel}
    (h : LargeEvenSplit p lab) : GGLabPhiOneTwo p lab := by
  unfold GGLabPhiOneTwo
  rw [four_pow_sub_one_eq]
  rcases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨hn, hp⟩
  · exact h.mul_right _
  · exact h.mul_left _
  · exact h.mul_right _
  · rw [hn, hp]
    norm_num

theorem ggInnerDiagOnLabel_phiOneTwo_L_of_innerDiag (hRig : GGLabelRigidInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagOn Bs L) :
    GGInnerDiagOnLabel GGLabPhiOneTwo p Bs L := by
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hst.1
  have hmark := ggInnerDiagOn_relabel hRig hInn hlab hhas
  refine largeEvenMarking_mono (fun lab' _ _ _ _ _ hP' => ⟨?_, hP'.2⟩) hmark
  rw [hP'.1]
  exact ggLabPhiOneTwo_of_largeEvenSplit hP.1

theorem ggInnerDiagOnLabel_phiOneTwo_L (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) :
    GGInnerDiagOnLabel GGLabPhiOneTwo p Bs L :=
  ggInnerDiagOnLabel_phiOneTwo_L_of_innerDiag hRig hHyp.1 hHyp.2.2.1.1

variable {G : Type} [Group G] [Finite G]

theorem ggNbr_halfSplit_of_hyp (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hInnK : GGInnerDiagOn Bs K) :
    LargeEvenMarking ↥K fun lab _ _ _ _ _ =>
      LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have h5 : GGNbrClauseFiveMarking p x K :=
    (hcfg.1.2.2.2.2.2.2.2.2.2.1 y K ⟨hK.1, D, J, hcfg.2.2, hK.2⟩).2
  rcases largeEvenMarking_or h5 with hh | hh
  · exact hh
  · exact absurd hh (ggNbr_not_primeField hraw hiso hp hp2 hxBs hInnK)

theorem ggNbr_sameMarking_of_innerDiag
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hK : GGNbr p B x D J y K)
    (hInnK : GGInnerDiagOn Bs K) :
    ∃ (lab : LargeEvenLabel) (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (θ : ↥K ⧸ Subgroup.center ↥K ≃* R),
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
      commutator K = ⊤ ∧
      Bs ≤ Subgroup.normalizer (K : Set G) ∧
      (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' : K => (l' : G) = b⁻¹ * l * b) φ) ∧
      GGRawInnField p R I F ∧
      LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥) := by
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hHS : LargeEvenMarking ↥K
      (fun lab _ _ _ _ _ => LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥)) :=
    ggNbr_halfSplit_of_hyp hraw hiso hcfg hK hInnK
  obtain ⟨lab, hlab, hhas, _, _, _, _, _, hHSlab⟩ :=
    largeEvenMarking_exists_hasLabel hHS
  have hInnLab : LargeEvenMarking ↥K (fun lab' _ _ I _ θ =>
      lab' = lab ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' : K => (l' : G) = b⁻¹ * l * b) φ) :=
    ggInnerDiagOn_relabel hRig hInnK hlab hhas
  have hperf : commutator K = ⊤ := hInnLab.1
  have hCombined :=
    largeEvenMarking_and_labelAll (S := fun _ => True)
      (P' := GGRawInnField p)
      (fun lab' hlab' _ => hraw p hp hp2 lab' hlab')
      (fun _ _ _ _ _ _ _ => trivial) hInnLab
  obtain ⟨lab', hlab', hhas', R, _, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hCombined
  obtain ⟨⟨hEq, hN, hBsInv⟩, hfield⟩ := hP
  have hHSlab' : LargeEvenHalfSplit p lab' (Subgroup.center ↥K = ⊥) := by
    rw [hEq]
    exact hHSlab
  exact ⟨lab', R, inferInstance, I, F, θ, hlab', hhas', hperf, hN, hBsInv, hfield, hHSlab'⟩

theorem ggBeta_range_rank_three_of_innerDiag {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) {R : Type} [Group R]
    (I : Set (MulAut R)) (θ : ↥X ⧸ Subgroup.center ↥X ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hK : commutator ↥X = ⊤)
    (hI : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
      (fun l l' : ↥X => (l' : G) = b⁻¹ * l * b) φ) :
    IsElemAbelian p (ggBeta X θ hN).range ∧
      ((ggBeta X θ hN).range : Set (MulAut R)) ⊆ I ∧
      p ^ 3 ≤ Nat.card (ggBeta X θ hN).range := by
  haveI : Finite R := Finite.of_injective θ.symm.toFun θ.symm.injective
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBelBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hBN : B ≤ Subgroup.normalizer (X : Set G) := hBBs.trans hN
  have htrans : (ggBeta X θ hBN).range ≤ (ggBeta X θ hN).range :=
    range_ggBeta_le θ hBBs hBN hN
  have hEsub : ((ggBeta X θ hN).range : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem X θ hN (fun b hb => hI b hb) b
  refine ⟨isElemAbelian_range_ggBeta θ hBelBs hN, hEsub, ?_⟩
  rcases hX with rfl | ⟨y, hnb⟩
  · exact (card_range_ggBeta_bstar hcfg hK θ hBN hN).2.1.trans
      (Subgroup.card_le_of_le htrans)
  · obtain ⟨⟨hBel, hBcard, -⟩, hyB, -, -, -, -⟩ := hnb.1
    obtain ⟨hp, -, -, h4⟩ := hcfg.1.2.2.2.2.2.1
    have hker : (ggBeta X θ hBN).ker.map B.subtype ≤ Subgroup.zpowers y := by
      have h := Subgroup.map_mono (f := B.subtype)
        (ker_ggBeta_le_of_sHat hnb.1 hK θ hBN)
      rw [Subgroup.subgroupOf_map_subtype] at h
      exact h.trans inf_le_left
    have hcard : Nat.card (ggBeta X θ hBN).ker ≤ p := by
      rw [← Subgroup.card_map_of_injective B.subtype_injective]
      refine (Subgroup.card_le_of_le hker).trans ?_
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one hp.pos (hBel.2 y hyB)
    have h3B : p ^ 3 ≤ Nat.card (ggBeta X θ hBN).range := by
      refine Nat.le_of_mul_le_mul_right ?_ hp.pos
      calc p ^ 3 * p = p ^ 4 := by ring
        _ ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
        _ = Nat.card ↥B := hBcard.symm
        _ = Nat.card (ggBeta X θ hBN).range * Nat.card (ggBeta X θ hBN).ker :=
            (TableB.card_range_mul_card_ker _).symm
        _ ≤ Nat.card (ggBeta X θ hBN).range * p := Nat.mul_le_mul_left _ hcard
    exact h3B.trans (Subgroup.card_le_of_le htrans)

theorem pow_le_card_ggBeta_of_torusLift_of_ggConfig
    {G : Type} [Group G] [Finite G] {p r : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) {R : Type} [Group R]
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hK : commutator ↥X = ⊤)
    (hlift : GGTorusLift p r R) : p ^ r ≤ Nat.card (ggBeta X θ hN).range := by
  have : Finite R := Finite.of_surjective θ θ.surjective
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (X : Set G) := hBBs.trans hN
  have htrans : (ggBeta X θ hBN).range ≤ (ggBeta X θ hN).range :=
    range_ggBeta_le θ hBBs hBN hN
  rcases hX with rfl | ⟨y, hnb⟩
  · obtain ⟨-, -, -, -, -, -, hS, -⟩ := hcfg.1
    exact (pow_le_card_range_ggBeta hp hS hK θ hBN hlift).trans
      (Subgroup.card_le_of_le htrans)
  · obtain ⟨⟨hBel, hBcard, -⟩, hyB, -, -, -, -⟩ := hnb.1
    have hrank := succ_le_twoLocalRank_of_torusLift hp hnb.1.2.2.2.1
      (hBel.2 y hyB) hnb.1.2.2.1 hK θ hlift
    have hker : (ggBeta X θ hBN).ker.map B.subtype ≤ Subgroup.zpowers y := by
      have h := Subgroup.map_mono (f := B.subtype)
        (ker_ggBeta_le_of_sHat hnb.1 hK θ hBN)
      rw [Subgroup.subgroupOf_map_subtype] at h
      exact h.trans inf_le_left
    have hcard : Nat.card (ggBeta X θ hBN).ker ≤ p := by
      rw [← Subgroup.card_map_of_injective B.subtype_injective]
      refine (Subgroup.card_le_of_le hker).trans ?_
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one hp.pos (hBel.2 y hyB)
    have hrB : p ^ r ≤ Nat.card (ggBeta X θ hBN).range := by
      refine Nat.le_of_mul_le_mul_right ?_ hp.pos
      calc p ^ r * p = p ^ (r + 1) := (pow_succ p r).symm
        _ ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos hrank
        _ = Nat.card ↥B := hBcard.symm
        _ = Nat.card (ggBeta X θ hBN).range * Nat.card (ggBeta X θ hBN).ker :=
            (TableB.card_range_mul_card_ker _).symm
        _ ≤ Nat.card (ggBeta X θ hBN).range * p := Nat.mul_le_mul_left _ hcard
    exact hrB.trans (Subgroup.card_le_of_le htrans)

theorem ggAllFixedArithMarking (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hAll : GGInnerDiagAll p B Bs x L D J)
    {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) :
    LargeEvenMarking ↥X fun lab R _ I F θ =>
      LargeEvenHalfSplit p lab (Subgroup.center ↥X = ⊥) ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
          (fun l l' : ↥X => (l' : G) = b⁻¹ * l * b) φ) ∧
        GGRawInnField p R I F ∧
        IsElemAbelian p (ggBeta X θ hN).range ∧
        ((ggBeta X θ hN).range : Set (MulAut R)) ⊆ I ∧
        p ^ 3 ≤ Nat.card (ggBeta X θ hN).range := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact hAll.1
    · exact hAll.2 y X hnb
  have hHS : LargeEvenMarking ↥X
      (fun lab _ _ _ _ _ => LargeEvenHalfSplit p lab (Subgroup.center ↥X = ⊥)) := by
    rcases hX with rfl | ⟨y, hnb⟩
    · have hst : LargeEvenStandardType p B x X := hcfg.1.2.2.2.2.2.2.2
      exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => Or.inl h.1) hst.1
    · exact ggNbr_halfSplit_of_hyp hraw hiso hcfg hnb hInn
  obtain ⟨lab, hlab, hhas, _, _, _, _, _, hHalf⟩ :=
    largeEvenMarking_exists_hasLabel hHS
  have hmark := ggInnerDiagOn_relabel hRig hInn hlab hhas
  have hCombined := largeEvenMarking_and_labelAll (S := fun _ => True)
    (P' := GGRawInnField p) (fun lab' hlab' _ => hraw p hp hp2 lab' hlab')
    (fun _ _ _ _ _ _ _ => trivial) hmark
  refine largeEvenMarking_mono (fun lab' R _ I F θ hP => ?_) hCombined
  obtain ⟨⟨hEq, hN, hInv⟩, hfield⟩ := hP
  have hHalf' : LargeEvenHalfSplit p lab' (Subgroup.center ↥X = ⊥) := by
    rw [hEq]
    exact hHalf
  exact ⟨hHalf', hN, hInv, hfield,
    ggBeta_range_rank_three_of_innerDiag hcfg hX I θ hN hCombined.1 hInv⟩

theorem ggAllFixedArithDispatch (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hAll : GGInnerDiagAll p B Bs x L D J)
    {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) :
    ∃ (lab : LargeEvenLabel) (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* R),
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧
      commutator ↥X = ⊤ ∧
      (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' : ↥X => (l' : G) = b⁻¹ * l * b) φ) ∧
      GGRawInnField p R I F ∧
      IsElemAbelian p (ggBeta X θ hN).range ∧
      ((ggBeta X θ hN).range : Set (MulAut R)) ⊆ I ∧
      p ^ 3 ≤ Nat.card (ggBeta X θ hN).range ∧
      (p ∣ (2 ^ lab.n) ^ 2 - 1 ∨ (p = 7 ∧ (lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩))) := by
  have hmark := ggAllFixedArithMarking hRig hraw hiso hcfg hAll hX
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hHalf, hN, hInv, hfield, hEab, hEsub, hE3⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  exact ⟨lab, R, inferInstance, I, F, hN, θ, hlab, hhas, hmark.1, hInv, hfield,
    hEab, hEsub, hE3, largeEvenHalfSplit_dvd hlab hHalf⟩

theorem ggInnerDiagOnLabel_phiOneTwo_nbr (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hN : GGNbrLabelsOk p B Bs x D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    GGInnerDiagOnLabel GGLabPhiOneTwo p Bs K := by
  have hInnK : GGInnerDiagOn Bs K := hHyp.2.2.1.2 y K hnb
  have hHS := ggNbr_halfSplit_of_hyp hraw hiso hHyp.1 hnb hInnK
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
  obtain ⟨labq, hlq, hhq, Rq, _, Iq, Fq, θq, hokq, -⟩ :=
    largeEvenMarking_exists_hasLabel (hN y K hnb)
  have hdvd : p ∣ (2 ^ lab.n) ^ 2 - 1 := by
    rcases largeEvenHalfSplit_dvd hlab hHSlab with h | ⟨hp7, hex⟩
    · exact h
    · exfalso
      have hlabiso : GGLabelIso labq lab :=
        hRig labq lab (↥K ⧸ Subgroup.center ↥K) hlq hlab hhq hhas
      have heq : labq = lab := eq_of_ggLabelIso_of_exc hex hlabiso
      rw [heq, hp7] at hokq
      rcases hex with rfl | rfl <;> simp [GGLabNbrOk] at hokq
  have hmark := ggInnerDiagOn_relabel hRig hInnK hlab hhas
  refine largeEvenMarking_mono (fun lab' _ _ _ _ _ hP' => ⟨?_, hP'.2⟩) hmark
  rw [hP'.1]
  unfold GGLabPhiOneTwo
  rwa [← two_pow_sq_eq]

end Labels

@[expose] def GGCorFiveTwentyReflDom {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) : Prop :=
  GGReflGenerated p (ggAutomizer L Bs) ∧
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs)

theorem GGCorFiveTwentyWeylDomNS.toReflDom {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (h : GGCorFiveTwentyWeylDomNS p B Bs x L D J) : GGCorFiveTwentyReflDom p B Bs x L D J :=
  ⟨h.1, fun y K hnb => (h.2.2 y K hnb).1⟩

theorem ggCorFiveTwentyWeylDomNS_of_reflDom (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hN : GGNbrLabelsOk p B Bs x D J)
    (h : GGCorFiveTwentyReflDom p B Bs x L D J) : GGCorFiveTwentyWeylDomNS p B Bs x L D J :=
  ⟨h.1, ggInnerDiagOnLabel_phiOneTwo_L hRig hHyp, fun y K hnb =>
    ⟨h.2 y K hnb, ggInnerDiagOnLabel_phiOneTwo_nbr hRig hraw hiso hHyp hN hnb⟩⟩

@[expose] def GGCorFiveTwentyQFourReflFailInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → ¬ GGCorFiveTwentyReflDom p B Bs x L D J →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem ggCorFiveTwentyQFourReflFailInput_of_nonWeylNS
    (h : GGCorFiveTwentyQFourNonWeylNSInput) : GGCorFiveTwentyQFourReflFailInput :=
  fun G _ _ p B Bs x L D J hH hq hN hD =>
    h G p B Bs x L D J hH hq hN fun hW => hD hW.toReflDom

theorem ggCorFiveTwentyQFourNonWeylNSInput_of_reflFail (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (h : GGCorFiveTwentyQFourReflFailInput) : GGCorFiveTwentyQFourNonWeylNSInput :=
  fun G _ _ p B Bs x L D J hH hq hN hD =>
    h G p B Bs x L D J hH hq hN fun hR =>
      hD (ggCorFiveTwentyWeylDomNS_of_reflDom hRig hraw hiso hH hN hR)

theorem ggCorFiveTwentyQFourReflFailInput_of_aggregate (h : GGCorFiveTwentyInput) :
    GGCorFiveTwentyQFourReflFailInput :=
  fun G _ _ p B Bs x L D J hH _ _ _ =>
    h G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2

theorem ggCorFiveTwentyQFourReflFailInput_of_nonWeyl (h : GGCorFiveTwentyQFourNonWeylInput) :
    GGCorFiveTwentyQFourReflFailInput :=
  ggCorFiveTwentyQFourReflFailInput_of_nonWeylNS (ggCorFiveTwentyQFourNonWeylNSInput_of_nonWeyl h)

theorem ggCorFiveTwentyQFourNonWeylInput_of_scalarFail_reflFail (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hS : GGCorFiveTwentyQFourScalarFailInput) (hF : GGCorFiveTwentyQFourReflFailInput) :
    GGCorFiveTwentyQFourNonWeylInput :=
  ggCorFiveTwentyQFourNonWeylInput_iff.mpr
    ⟨ggCorFiveTwentyQFourNonWeylNSInput_of_reflFail hRig hraw hiso hF, hS⟩

end CFSG.StandardType

end

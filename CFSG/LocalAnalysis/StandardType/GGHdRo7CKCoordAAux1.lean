module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelI
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordD

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord

theorem hdRo7CKCoordAux_y_pow_eq_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : y ^ p = 1 :=
  hH.1.tableB_facts.2.1.2 y (hH.1.2.1.1 hH.2.2.2.2.1.1.2.1)

theorem hdRo7CKCoordAux_y_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : y ≠ 1 :=
  hH.2.2.2.2.1.1.2.2.1

theorem hdRo7CKCoordAux_inf_ab {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : IsElemAbelian p (Bs ⊓ K) :=
  hH.1.tableB_facts.2.1.mono inf_le_left

theorem hdRo7CKCoordAux_card_bstar_ge {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : p ^ 4 ≤ Nat.card ↥Bs :=
  hH.1.tableB_facts.2.2.2.2

theorem hdRo7CKCoordAux_center_K_eq_bot
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowCorank2C p J K) :
    Subgroup.center ↥K = ⊥ := by
  obtain ⟨labJ, labK, hJ2, hK2, hHasJ, hHasK, hp3, htagJ, hnJ, htagK, hnK, hrank⟩ := hrow
  have hnbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hperf : commutator ↥K = ⊤ := by
    have hID : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnbr
    unfold GGInnerDiagOn LargeEvenMarking LargeEvenMarkingLegacy at hID
    exact hID.1
  have h4 : 4 ≤ labK.rank := by
    have h5 : 5 ≤ labK.rank := hdRo7CLCoordAux_rank_ge_five hJ2 hnJ htagJ (by
      have := hrank; omega)
    omega
  have h1n : 1 ≤ labK.n := by omega
  have hmodel : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSp labK.rank 2 labK.n :=
    hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC htagK (by omega) h1n hHasK
  obtain ⟨φ, hinj, hrange⟩ :=
    ggSpLiftInput_holds G K labK.rank labK.n h4 hperf hmodel
  have hZsp : Subgroup.center (StatedSp labK.rank (GaloisField 2 labK.n)) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have he := Subgroup.map_center_eq (MonoidHom.ofInjective hinj)
  rw [hZsp, Subgroup.map_bot] at he
  rw [← hrange]
  exact he.symm

theorem hdRo7CKCoordAux_torus_data
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hRig : GGLabelRigidInput) (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowCorank2C p J K) :
    ∃ (R : Type) (_ : Group R) (I : Set (MulAut R)) (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
      (hBsN : Bs ≤ Subgroup.normalizer (K : Set G)),
      commutator ↥K = ⊤ ∧ GGTorusSignedEltSC p R ∧ GGCenterPrime p R ∧
      Subgroup.center R = ⊥ ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R) ∧
      (∀ b ∈ Bs, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' : ↥K => (l' : G) = b⁻¹ * (l : G) * b) φ) := by
  classical
  obtain ⟨labJ, labK, hJ2, hK2, hHasJ, hHasK, hp3, htagJ, hnJ, htagK, hnK, hrank⟩ := hrow
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := by omega
  have h2rank : 2 ≤ labK.rank := by
    have h := hK2
    unfold LargeEvenInLambda2 at h
    rcases htagK with hB | hC
    · rw [hB] at h; exact h.2.1
    · rw [hC] at h; exact h.2.1
  haveI : NeZero labK.rank := ⟨by omega⟩
  have hnbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hID : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnbr
  have hmark := ggInnerDiagOn_relabel hRig hID hK2 hHasK
  obtain ⟨hperf, lab', hlab'_2, hraw'⟩ := hmark
  have hlab'_eq : lab' = labK := by
    obtain ⟨R0, hR0grp, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw'
    letI : Group R0 := hR0grp
    obtain ⟨_, _, hθ0⟩ := hQ0
    obtain ⟨_, hlab, _, _⟩ := hθ0
    exact hlab
  have hrawK : LargeEvenRawDatum labK
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R,
          lab' = labK ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I,
              LargeEvenInduces θ (fun l l' : ↥K => (l' : G) = b⁻¹ * (l : G) * b) φ) :=
    hlab'_eq ▸ hraw'
  obtain ⟨K', hK'field, hK'fin, hK'char, hK'card, hQK⟩ :=
    hdRo7CLCoordAux_recipe_symplectic htagK hrawK
  obtain ⟨_, _, hθ⟩ := hQK
  obtain ⟨θ, _hlab', hBsN, hBs3⟩ := hθ
  have hpK : p ∣ Nat.card K' + 1 := by rw [hK'card, hnK, hp3]; norm_num
  exact ⟨LargeEvenProj (LargeEvenSpGroup K' labK.rank), inferInstance,
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K' labK.rank))
      (LargeEvenGSpSet K' labK.rank),
    θ, hBsN, hperf,
    ggSpNonsplitSignedEltInput_holds K' labK.rank p h2rank hp hpK,
    ggCenterPrime_sp (K := K') hp hp2,
    TableBSymp.center_spProj_eq_bot,
    TableBSymp.sp_I_subset_inn,
    hBs3⟩

end CFSG.StandardType.HdRo7C

end

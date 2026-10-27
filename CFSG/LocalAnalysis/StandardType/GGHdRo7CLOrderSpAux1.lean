module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelI

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord
open CFSG.StandardType.OrdPNsSp CFSG.StandardType.OrdPNsGen Matrix NoOffOm

theorem hdRo7CLOSpAux_center_L_eq_bot
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hLlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (htag : lab.tag = .B ∨ lab.tag = .C) (hn1 : lab.n = 1) (h4 : 4 ≤ lab.rank) :
    Subgroup.center ↥L = ⊥ := by
  have hperf : commutator ↥L = ⊤ := by
    have hID : GGInnerDiagOn Bs L := hH.2.2.1.1
    unfold GGInnerDiagOn LargeEvenMarking LargeEvenMarkingLegacy at hID
    exact hID.1
  have h1n : 1 ≤ lab.n := by omega
  have hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp lab.rank 2 lab.n :=
    hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC htag (by omega) h1n hLlab
  obtain ⟨φ, hinj, hrange⟩ :=
    ggSpLiftInput_holds G L lab.rank lab.n h4 hperf hmodel
  have hZsp : Subgroup.center (StatedSp lab.rank (GaloisField 2 lab.n)) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have he := Subgroup.map_center_eq (MonoidHom.ofInjective hinj)
  rw [hZsp, Subgroup.map_bot] at he
  rw [← hrange]
  exact he.symm

theorem hdRo7CLOSpAux_torus_data
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hRig : GGLabelRigidInput) (hH : GGResHyp p B Bs x L D J y K)
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hLlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (htag : lab.tag = .B ∨ lab.tag = .C) (hn1 : lab.n = 1) (hp3 : p = 3) :
    ∃ (R : Type) (_ : Group R) (I : Set (MulAut R)) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
      (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)),
      commutator ↥L = ⊤ ∧ GGTorusSignedEltSC p R ∧ GGCenterPrime p R ∧
      Subgroup.center R = ⊥ ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R) ∧
      (∀ b ∈ Bs, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ) := by
  classical
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := by omega
  have h2rank : 2 ≤ lab.rank := by
    have h := hlab
    unfold LargeEvenInLambda2 at h
    rcases htag with hB | hC
    · rw [hB] at h; exact h.2.1
    · rw [hC] at h; exact h.2.1
  haveI : NeZero lab.rank := ⟨by omega⟩
  have hID : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hmark := ggInnerDiagOn_relabel hRig hID hlab hLlab
  obtain ⟨hperf, lab', hlab'_2, hraw'⟩ := hmark
  have hlab'_eq : lab' = lab := by
    obtain ⟨R0, hR0grp, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw'
    letI : Group R0 := hR0grp
    obtain ⟨_, _, hθ0⟩ := hQ0
    obtain ⟨_, hlab, _, _⟩ := hθ0
    exact hlab
  have hrawL : LargeEvenRawDatum lab
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
          lab' = lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I,
              LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ) :=
    hlab'_eq ▸ hraw'
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, hQK⟩ :=
    hdRo7CLCoordAux_recipe_symplectic htag hrawL
  obtain ⟨_, _, hθ⟩ := hQK
  obtain ⟨θ, _hlab', hBsN, hBs3⟩ := hθ
  have hpK : p ∣ Nat.card K + 1 := by rw [hKcard, hn1, hp3]; norm_num
  exact ⟨LargeEvenProj (LargeEvenSpGroup K lab.rank), inferInstance,
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K lab.rank)) (LargeEvenGSpSet K lab.rank),
    θ, hBsN, hperf,
    ggSpNonsplitSignedEltInput_holds K lab.rank p h2rank hp hpK,
    ggCenterPrime_sp (K := K) hp hp2,
    TableBSymp.center_spProj_eq_bot,
    TableBSymp.sp_I_subset_inn,
    hBs3⟩

theorem hdRo7CLOSpAux_card_inf_pow
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hLlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (htag : lab.tag = .B ∨ lab.tag = .C) (hn1 : lab.n = 1) (h4 : 4 ≤ lab.rank)
    (hp3 : p = 3)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ L, ∀ y ∈ L, b * y * b⁻¹ = x * y * x⁻¹) :
    Nat.card ↥(Bs ⊓ L) = p ^ lab.rank := by
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := by omega
  have hperf : commutator ↥L = ⊤ := by
    have hID : GGInnerDiagOn Bs L := hH.2.2.1.1
    unfold GGInnerDiagOn LargeEvenMarking LargeEvenMarkingLegacy at hID
    exact hID.1
  have h1n : 1 ≤ lab.n := by omega
  have hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp lab.rank 2 lab.n :=
    hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC htag (by omega) h1n hLlab
  obtain ⟨φ, hinj, hrange⟩ :=
    ggSpLiftInput_holds G L lab.rank lab.n h4 hperf hmodel
  haveI : CharP (GaloisField 2 lab.n) 2 :=
    charP_two_of_card (GaloisField.card 2 lab.n (by omega))
  obtain ⟨hpow, hcomm, hmax, hcardE⟩ :=
    comap_inf_maximal hH.1.2.1 φ hinj hrange
      (hdRo7CLOSpAux_center_L_eq_bot hH lab hlab hLlab htag hn1 h4) hBsN hinner
  set E : Subgroup (StatedSp lab.rank (GaloisField 2 lab.n)) :=
    (Bs ⊓ L).comap φ with hEdef
  have hcardBs : Nat.card ↥(Bs ⊓ L) = Nat.card ↥E := hcardE.symm
  have hA := genMax_map_statedSpGL (n := lab.rank) (K := GaloisField 2 lab.n) hp hp2 hpow hcomm hmax
  have hΓ : ∀ g : GL (Fin (lab.rank + lab.rank)) (GaloisField 2 lab.n),
      (∀ v w, spFormD lab.rank (GaloisField 2 lab.n) (glin g v) (glin g w) =
        spFormD lab.rank (GaloisField 2 lab.n) v w) → g ∈ isoGL (spFormD lab.rank (GaloisField 2 lab.n)) :=
    fun g hg => hg
  have hneE : E ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥E = 1 := by rw [h]; exact Subgroup.card_bot
    have h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ L) :=
      hdRo7CLCoordAux_card_inf_ge p B Bs x L D J y K hH
        (hdRo7CLOSpAux_center_L_eq_bot hH lab hlab hLlab htag hn1 h4) hBsN hinner
    rw [hcardBs, h1] at h3
    have h2 : (8 : ℕ) ≤ p ^ 3 := by simpa using Nat.pow_le_pow_left hp.two_le 3
    omega
  have hne : ∃ c ∈ E.map (statedSpGL lab.rank (GaloisField 2 lab.n)), c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hneE
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    have h1 : statedSpGL lab.rank (GaloisField 2 lab.n) s = 1 := hcon _ ⟨s, hs, rfl⟩
    exact statedSpGL_injective (h1.trans (map_one _).symm)
  have hle := card_le_pow_lcm (K := GaloisField 2 lab.n) (d := lab.rank + lab.rank)
    (spFormD_isAlt) hA
  have hge := pow_lcm_le_card (K := GaloisField 2 lab.n) (d := lab.rank + lab.rank)
    (spFormD_isAlt) hA hΓ hne
  have hKcard : Nat.card (GaloisField 2 lab.n) = 2 := by
    rw [GaloisField.card 2 lab.n (by omega), hn1]; norm_num
  have hord : OrdPNS.ordQ (GaloisField 2 lab.n) p = 2 := by
    unfold OrdPNS.ordQ
    rw [hKcard, hp3]
    exact orderOf_eq_prime (p := 2) (by decide) (by decide)
  have hexp : (lab.rank + lab.rank) / Nat.lcm 2 (OrdPNS.ordQ (GaloisField 2 lab.n) p) =
      lab.rank := by
    rw [hord, Nat.lcm_self,
      show lab.rank + lab.rank = 2 * lab.rank by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hcardmap : Nat.card ↥(E.map (statedSpGL lab.rank (GaloisField 2 lab.n))) =
      Nat.card ↥E := Subgroup.card_map_of_injective statedSpGL_injective
  have hEcard : Nat.card ↥E = p ^ lab.rank := by
    apply le_antisymm
    · rw [hcardmap, hexp] at hle
      exact hle
    · rw [hcardmap, hexp] at hge
      exact hge
  rw [hcardBs, hEcard]

theorem hdRo7CLOSpAux_hinner
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hRig : GGLabelRigidInput) (hH : GGResHyp p B Bs x L D J y K)
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hLlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (htag : lab.tag = .B ∨ lab.tag = .C) (hn1 : lab.n = 1) (h4 : 4 ≤ lab.rank)
    (hp3 : p = 3) :
    (∃ (R : Type) (_ : Group R) (I : Set (MulAut R)) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
      (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)),
      commutator ↥L = ⊤ ∧ GGTorusSignedEltSC p R ∧ GGCenterPrime p R ∧
      Subgroup.center R = ⊥ ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R) ∧
      (∀ b ∈ Bs, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ)) ∧
    Subgroup.center ↥L = ⊥ ∧
    (∀ b ∈ Bs, ∃ x ∈ L, ∀ y ∈ L, b * y * b⁻¹ = x * y * x⁻¹) := by
  obtain ⟨R, hRgrp, I, θ, hBsN, hperf, hTSC, hCP, hcenter, hI, hBs3⟩ :=
    hdRo7CLOSpAux_torus_data hRig hH lab hlab hLlab htag hn1 hp3
  letI : Group R := hRgrp
  have hZL := hdRo7CLOSpAux_center_L_eq_bot hH lab hlab hLlab htag hn1 h4
  have hinner := hdRo7CLCoordAux_hinner p B Bs x L D J y K hH R I θ hI hZL hBsN hBs3
  exact ⟨⟨R, hRgrp, I, θ, hBsN, hperf, hTSC, hCP, hcenter, hI, hBs3⟩, hZL, hinner⟩

end CFSG.StandardType.HdRo7C

end

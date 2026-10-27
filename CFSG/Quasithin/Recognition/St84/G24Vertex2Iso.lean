module

public import CFSG.Quasithin.Recognition.St84.G24ModelFacts
public import CFSG.Quasithin.Recognition.St84.G24ModelFrameFacts
import CFSG.Quasithin.Recognition.St84.G24Vertex2Prep
import CFSG.Quasithin.Recognition.St84.G24Vertex2H1
import CFSG.Quasithin.Recognition.St84.G24RelsA
import CFSG.Quasithin.Recognition.St84.G24ModelSquares
import CFSG.Quasithin.Recognition.St84.G24Vertex2Relations
import CFSG.GroupTheory.PGroup.ClassTwoFrameIso
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSpecial
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSylow
public import CFSG.Quasithin.Recognition.St84.G24Vertex2Frame
public import Certificates.Data.G24LinEq

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7
open CFSG.Quasithin.St84
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single commute_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem conj_eElt_eq_mulVec sq_eElt_mul
  quadMapOfCoeffs
  frameQuotEquiv frameQuotEquiv_mk_eq_iff eBasisMulEquiv eBasisMulEquiv_apply
  IsQuotFrame IsEBasisOf isQuotFrame_of_card isEBasisOf_of_card
  frameQuotEquiv_conj_of_closure eBasisMulEquiv_conj_of_closure)
open Certificates.A5GL42 (aN bN)
open CFSG.Quasithin.H.Q13 (om)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

private lemma mem_iff_of_restrict {G G' : Type*} [Group G] [Group G']
    {P A : Subgroup G} {P' A' : Subgroup G'} (hA : A ≤ P) (ψ : ↥P ≃* ↥P')
    (θ : ↥A ≃* ↥A') (hψ : ∀ a : ↥A, (ψ ⟨a, hA a.2⟩ : G') = θ a) (x : ↥P) :
    (x : G) ∈ A ↔ (ψ x : G') ∈ A' := by
  constructor
  · intro hx
    rw [show (ψ x : G') = θ ⟨x, hx⟩ from hψ ⟨x, hx⟩]
    exact (θ ⟨x, hx⟩).2
  · intro hx
    let a : ↥A := θ.symm ⟨(ψ x : G'), hx⟩
    have ha : (ψ ⟨a, hA a.2⟩ : G') = (ψ x : G') := by
      rw [hψ a]
      exact congrArg Subtype.val (θ.apply_symm_apply _)
    have hxeq : (⟨a, hA a.2⟩ : ↥P) = x := ψ.injective (Subtype.ext ha)
    have hxa : (x : G) = (a : G) := by rw [← hxeq]
    rw [hxa]
    exact a.2

private theorem isQuotFrame_v2 [Finite G] {L1 L2 S : Subgroup G}
    (F : G24Frame2 L1 L2 S) (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G}
    (hu : u ∈ F.W) (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) :
    IsQuotFrame (dsQ L2 L1 S) (centerOf (dsQ L2 L1 S)) (v2Frame F.k u n) := by
  have hZc : ∀ y ∈ centerOf (dsQ L2 L1 S), ∀ x ∈ dsQ L2 L1 S,
      y * x = x * y := (F.special_data hD).2.2.2.1
  haveI : ((centerOf (dsQ L2 L1 S)).subgroupOf (dsQ L2 L1 S)).Normal :=
    Subgroup.normal_of_le_center fun z hz =>
      Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZc z hz x x.2).symm
  obtain ⟨h1, h2, h3, h4, h5⟩ := F.frame_spec hD hu hn
  exact
    { le := inf_le_left
      mem := h1
      comm := h2
      sq := h3
      cm := h4
      indep := F.indep hD hu hu' hn
      card := h5 }

private theorem isEBasisOf_zb [Finite G] {L1 L2 S : Subgroup G}
    (F : G24Frame2 L1 L2 S) (hD : G24LocalData L1 L2 S) {zb : Fin 4 → G}
    (hzb : F.IsZBasis zb) :
    IsEBasisOf (centerOf (dsQ L2 L1 S)) zb := by
  obtain ⟨hsq, hcomm, -, - , hcov⟩ := F.zBasis_spec hD hzb
  obtain ⟨hZ, -, -, -, -⟩ := hzb
  refine isEBasisOf_of_card hZ (fun t => (pow_two (zb t)).symm.trans (hsq t)) hcomm ?_ ?_
  · intro y hy
    obtain ⟨u, hu⟩ := hcov y hy
    rw [hu, eElt]
    exact Subgroup.list_prod_mem (K := Subgroup.closure (Set.range zb)) fun x hx => by
      obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hx
      exact (Subgroup.closure (Set.range zb)).pow_mem
        (Subgroup.subset_closure (k := Set.range zb) (a := zb t)
          (show zb t ∈ Set.range zb from ⟨t, rfl⟩)) _
  · rw [hD.card_centerOf_dsQ_right]


private theorem isQuotFrame_frame2 (hM : G24M.Facts) :
    IsQuotFrame G24M.Q2 G24M.Z2 G24M.frame2 := by
  have hZc : ∀ y ∈ G24M.Z2, ∀ x ∈ G24M.Q2, y * x = x * y := fun y hy x hx =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 x hx).symm
  haveI : (G24M.Z2.subgroupOf G24M.Q2).Normal := Subgroup.normal_of_le_center fun z hz =>
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZc z hz x x.2).symm
  have hgen : G24M.Q2 ≤ Subgroup.closure (Set.range G24M.frame2) ⊔ G24M.Z2 := by
    change Subgroup.closure (Set.range G24M.pc2Y) ≤
      Subgroup.closure (Set.range G24M.frame2) ⊔ G24M.Z2
    apply (Subgroup.closure_le
      (K := Subgroup.closure (Set.range G24M.frame2) ⊔ G24M.Z2)).mpr
    rintro x ⟨j, rfl⟩
    refine Fin.addCases (m := 6) (n := 4) (fun i => ?_) (fun t => ?_) j
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, rfl⟩)
    · refine Subgroup.mem_sup_right ?_
      rw [hM.Z2_eq]
      exact Subgroup.subset_closure (by fin_cases t <;> simp [G24M.zb2])
  refine isQuotFrame_of_card (inf_le_left : G24M.Z2 ≤ G24M.Q2) ?_ ?_ ?_ ?_ hgen ?_
  · intro i
    exact Subgroup.subset_closure ⟨Fin.castAdd 4 i, rfl⟩
  · intro y hy i
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 _
      (Subgroup.subset_closure ⟨Fin.castAdd 4 i, rfl⟩)).symm
  · intro i
    exact hM.sq_Q2 _ (Subgroup.subset_closure ⟨Fin.castAdd 4 i, rfl⟩)
  · intro i j
    exact hM.comm_Q2 _ (Subgroup.subset_closure ⟨Fin.castAdd 4 i, rfl⟩) _
      (Subgroup.subset_closure ⟨Fin.castAdd 4 j, rfl⟩)
  · rw [hM.card_Q2, hM.card_Z2]
    norm_num

private theorem isEBasisOf_zb2 (hM : G24M.Facts) :
    IsEBasisOf G24M.Z2 G24M.zb2 := by
  have hmem : ∀ t, G24M.zb2 t ∈ G24M.Z2 := by
    intro t
    rw [hM.Z2_eq]
    exact Subgroup.subset_closure (by fin_cases t <;> simp [G24M.zb2])
  refine isEBasisOf_of_card hmem ?_ ?_ ?_ hM.card_Z2
  · intro t
    exact (pow_two (G24M.zb2 t)).symm.trans (hM.sq_Z2 _ (hmem t))
  · intro t s
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hmem t)).2 _
      ((inf_le_left : G24M.Z2 ≤ G24M.Q2) (hmem s))).symm
  · intro y hy
    rw [hM.Z2_eq] at hy
    have hrange : Subgroup.closure ({G24M.pc2Y 6, G24M.pc2Y 7, G24M.pc2Y 8,
        G24M.pc2Y 9} : Set G24M.Y) ≤ Subgroup.closure (Set.range G24M.zb2) := by
      apply (Subgroup.closure_le (K := Subgroup.closure (Set.range G24M.zb2))).mpr
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact Subgroup.subset_closure (k := Set.range G24M.zb2) (a := G24M.pc2Y 6)
          (show G24M.pc2Y 6 ∈ Set.range G24M.zb2 from ⟨0, rfl⟩)
      · exact Subgroup.subset_closure (k := Set.range G24M.zb2) (a := G24M.pc2Y 7)
          (show G24M.pc2Y 7 ∈ Set.range G24M.zb2 from ⟨1, rfl⟩)
      · exact Subgroup.subset_closure (k := Set.range G24M.zb2) (a := G24M.pc2Y 8)
          (show G24M.pc2Y 8 ∈ Set.range G24M.zb2 from ⟨2, rfl⟩)
      · exact Subgroup.subset_closure (k := Set.range G24M.zb2) (a := G24M.pc2Y 9)
          (show G24M.pc2Y 9 ∈ Set.range G24M.zb2 from ⟨3, rfl⟩)
    exact hrange hy

private theorem model_k2_fixes_Z2 (hM : G24M.Facts) (hFr : G24M.FrameFacts)
    {z : G24M.Y} (hz : z ∈ G24M.Z2) :
    G24M.A2img 2 * z * (G24M.A2img 2)⁻¹ = z := by
  have hfix : ∀ t, G24M.A2img 2 * G24M.zb2 t * (G24M.A2img 2)⁻¹ =
      eElt G24M.zb2 (fun s => CFSG.Quasithin.St84.G24MF.matZ2 2 s t) := by
    intro t
    have h := hFr.actZ2 2 t
    rw [G24M.matZ2_two] at h ⊢
    have hsingle : (fun s : Fin 4 =>
        (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) s t) = Pi.single t 1 := by
      funext s
      by_cases hst : s = t
      · subst hst; simp [Matrix.one_apply, Pi.single]
      · simp [Matrix.one_apply, Pi.single, hst]
    rw [hsingle, eElt_single] at h ⊢
    exact h
  obtain ⟨w, hw⟩ := (isEBasisOf_zb2 hM).span z hz
  rw [hw, conj_eElt_eq_mulVec (isEBasisOf_zb2 hM).ebasis.sq
    (isEBasisOf_zb2 hM).ebasis.comm (CFSG.Quasithin.St84.G24MF.matZ2 2) hfix w,
    G24M.matZ2_two, Matrix.one_mulVec]

theorem exists_vertexIso_right [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) (hM : G24M.Facts) (hFr : G24M.FrameFacts)
    (ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥G24M.M1)
    (hψ₁S : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.T0)
    (hψ₁Q : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ dsQ L1 L2 S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.Q1) :
    ∃ ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥G24M.M2,
      (∀ x : ↥(L2 ⊔ bigB L1 L2 S),
        (x : G) ∈ S ↔ ((ψ₂ x : ↥G24M.M2) : G24M.Y) ∈ G24M.T0) ∧
      (∀ x : ↥(L2 ⊔ bigB L1 L2 S),
        (x : G) ∈ dsQ L1 L2 S ↔ ((ψ₂ x : ↥G24M.M2) : G24M.Y) ∈ G24M.Q1) := by
  classical
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q1 : Subgroup G := dsQ L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf Q2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  obtain ⟨F, hMk⟩ := exists_g24Frame2_omegaN hF h2 hD hM ψ₁ hψ₁S hψ₁Q
  obtain ⟨u, n, hu, hu', hn, hX⟩ := F.exists_isAct_nonsplitX hD hMk
  obtain ⟨zb, hzb⟩ := F.exists_zBasis
  let f : Fin 6 → G := v2Frame F.k u n
  have hspec := F.special_data hD
  have hZc : ∀ z ∈ Z2, ∀ x ∈ Q2, z * x = x * z := hspec.2.2.2.1
  haveI : (Z2.subgroupOf Q2).Normal := Subgroup.normal_of_le_center fun z hz =>
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZc z hz x x.2).symm
  have hZc' : ∀ z ∈ G24M.Z2, ∀ x ∈ G24M.Q2, z * x = x * z := fun z hz x hx =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 x hx).symm
  haveI : (G24M.Z2.subgroupOf G24M.Q2).Normal := Subgroup.normal_of_le_center fun z hz =>
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZc' z hz x x.2).symm
  have hf : IsQuotFrame Q2 Z2 f := isQuotFrame_v2 F hD hu hu' hn
  have hf' : IsQuotFrame G24M.Q2 G24M.Z2 G24M.frame2 := isQuotFrame_frame2 hM
  have hz : IsEBasisOf Z2 zb := isEBasisOf_zb F hD hzb
  have hz' : IsEBasisOf G24M.Z2 G24M.zb2 := isEBasisOf_zb2 hM
  obtain ⟨sq, cm, hsqf, hcmf, hqa, hqb, hqk, hne⟩ := F.exists_quad hD hu hu' hn hX hzb
  rw [hMk] at hqk
  obtain ⟨s, hs3, hs⟩ := G24M.quad2_proportional hqa hqb hqk hne
  let μ : Matrix (Fin 4) (Fin 4) (ZMod 2) := CFSG.Quasithin.St84.G24LE.omegaN ^ (3 - s)
  let ν : Matrix (Fin 4) (Fin 4) (ZMod 2) := CFSG.Quasithin.St84.G24LE.omegaN ^ s
  have hμν : μ * ν = 1 := by
    rw [show μ * ν = CFSG.Quasithin.St84.G24LE.omegaN ^ ((3 - s) + s) from
      (pow_add _ (3 - s) s).symm, show (3 - s) + s = 3 by omega,
      G24M.omegaN_pow_three]
  have hνμ : ν * μ = 1 := by
    rw [show ν * μ = CFSG.Quasithin.St84.G24LE.omegaN ^ (s + (3 - s)) from
      (pow_add _ s (3 - s)).symm, show s + (3 - s) = 3 by omega,
      G24M.omegaN_pow_three]
  let aA : ↥F.A := ⟨F.a, F.a_mem.1⟩
  let bA : ↥F.A := ⟨F.b, F.b_mem.1⟩
  let kA : ↥F.A := ⟨F.k, F.k_mem_A⟩
  let gen : Fin 3 → ↥F.A := ![aA, bA, kA]
  have hgen_top : Subgroup.closure (Set.range gen) = ⊤ := by
    apply Subgroup.map_injective (f := F.A.subtype) Subtype.val_injective
    rw [MonoidHom.map_closure]
    have hmap : F.A.subtype '' Set.range gen = ({F.a, F.b, F.k} : Set G) := by
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        fin_cases i <;> simp [gen, aA, bA, kA]
      · intro hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨aA, ⟨0, rfl⟩, rfl⟩
        · exact ⟨bA, ⟨1, rfl⟩, rfl⟩
        · exact ⟨kA, ⟨2, rfl⟩, rfl⟩
    rw [hmap, F.closure_eq]
    rw [← MonoidHom.range_eq_map]
    exact F.A.range_subtype.symm
  have hgen_rels : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA,
      CFSG.Certificates.signedProd gen w = 1 := by
    have h := CFSG.Quasithin.St84.signedProd_relsA (a := aA) (b := bA) (k := kA)
      (Subtype.ext (by simpa using F.a_sq))
      (Subtype.ext (by simpa using F.b_cube))
      (Subtype.ext (by simpa using F.ab_five))
      (Subtype.ext (by rw [← F.orderOf_k]; exact pow_orderOf_eq_one F.k))
      (Subtype.ext (by
        simpa using (Subgroup.mem_centralizer_iff.mp (F.A_le F.a_mem.1).2 F.k
          (by simp)).symm))
      (Subtype.ext (by
        simpa using (Subgroup.mem_centralizer_iff.mp (F.A_le F.b_mem.1).2 F.k
          (by simp)).symm))
    simpa [gen] using h
  obtain ⟨e, he⟩ := CFSG.Quasithin.St84.exists_mulEquiv_relsA gen G24M.A2imgQ hgen_rels
    hM.rels_A2imgQ hgen_top hM.closure_range_A2imgQ F.card_A hM.card_A2
  have heY : ∀ j, ((e (gen j) : ↥G24M.A2) : G24M.Y) = G24M.A2img j := by
    intro j
    have h := congrArg Subtype.val (he j)
    fin_cases j <;> simpa [G24M.A2imgQ, G24M.A2img, G24M.A2Q, G24M.A2gen] using h
  let fmap : ↥Q2 ⧸ Z2.subgroupOf Q2 ≃*
      ↥G24M.Q2 ⧸ G24M.Z2.subgroupOf G24M.Q2 := frameQuotEquiv hf hf'
  let gmap : ↥Z2 ≃* ↥G24M.Z2 := eBasisMulEquiv hz hz' μ ν hμν hνμ
  have hconjf : ∀ (r : ↥F.A) (v w : ↥Q2) (v' w' : ↥G24M.Q2),
      (w : G) = (r : G) * v * (r : G)⁻¹ →
      (w' : G24M.Y) = (e r : G24M.Y) * v' * (e r : G24M.Y)⁻¹ →
      fmap (QuotientGroup.mk v) = QuotientGroup.mk v' →
      fmap (QuotientGroup.mk w) = QuotientGroup.mk w' := by
    refine frameQuotEquiv_conj_of_closure hf hf' hspec.1 hspec.2.2.2.2.2.2.1
      (hM.A2_le_M2.trans hM.M2_le_normalizer_Q2) ?_ e gen hgen_top
      CFSG.Quasithin.St84.G24MF.matV2 ?_ ?_
    · intro r hr z hz
      exact (Subgroup.mem_normalizer_iff.mp (hM.M2_le_normalizer_Z2 (hM.A2_le_M2 hr)) z).mp hz
    · intro l j
      fin_cases l
      · simpa [gen, aA, G24M.matV2_zero] using hX.1 j
      · simpa [gen, bA, G24M.matV2_one] using hX.2.1 j
      · simpa [gen, kA, G24M.matV2_two, hMk] using hX.2.2 j
    · intro l j
      obtain ⟨c, hc⟩ := hFr.act2 l j
      rw [← heY l] at hc
      have hfQ' : ∀ i, G24M.frame2 i ∈ G24M.Q2 := fun i =>
        Subgroup.subset_closure ⟨Fin.castAdd 4 i, rfl⟩
      have hcomm : Commute (eElt G24M.zb2 c)
          (eElt G24M.frame2 (fun i => CFSG.Quasithin.St84.G24MF.matV2 l i j)) := by
        apply commute_eElt (x := eElt G24M.zb2 c)
        intro i
        exact (commute_eElt (x := G24M.frame2 i) (fun t =>
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hz'.mem t)).2 _
            (hfQ' i)) c).symm
      rw [hc]
      rw [show eElt G24M.frame2 (fun i => CFSG.Quasithin.St84.G24MF.matV2 l i j) *
          eElt G24M.zb2 c *
          (eElt G24M.frame2 (fun i => CFSG.Quasithin.St84.G24MF.matV2 l i j))⁻¹ =
          eElt G24M.zb2 c from by
        rw [← hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]]
      exact eElt_mem_of_forall_mem hz'.mem c
  have hconjg : ∀ (r : ↥F.A) (y w : ↥Z2),
      (w : G) = (r : G) * y * (r : G)⁻¹ →
      (gmap w : G24M.Y) = (e r : G24M.Y) * (gmap y : G24M.Y) * (e r : G24M.Y)⁻¹ := by
    refine eBasisMulEquiv_conj_of_closure hz hz' μ ν hμν hνμ
      hspec.2.2.2.2.2.2.1 e gen hgen_top CFSG.Quasithin.St84.G24MF.matZ2 ?_ ?_ ?_
    · intro l
      fin_cases l
      · have hωa : Commute CFSG.Quasithin.St84.G24LE.omegaN aN := by
          show CFSG.Quasithin.St84.G24LE.omegaN * aN =
            aN * CFSG.Quasithin.St84.G24LE.omegaN
          decide
        change Commute μ (CFSG.Quasithin.St84.G24MF.matZ2 0)
        rw [G24M.matZ2_zero]
        simpa only [μ] using hωa.pow_left (3 - s)
      · have hωb : Commute CFSG.Quasithin.St84.G24LE.omegaN bN := by
          show CFSG.Quasithin.St84.G24LE.omegaN * bN =
            bN * CFSG.Quasithin.St84.G24LE.omegaN
          decide
        change Commute μ (CFSG.Quasithin.St84.G24MF.matZ2 1)
        rw [G24M.matZ2_one]
        simpa only [μ] using hωb.pow_left (3 - s)
      · change Commute μ (CFSG.Quasithin.St84.G24MF.matZ2 2)
        rw [G24M.matZ2_two]
        show μ * 1 = 1 * μ
        rw [mul_one, one_mul]
    · intro l t
      fin_cases l
      · simpa [gen, aA, G24M.matZ2_zero] using hzb.2.2.1 t
      · simpa [gen, bA, G24M.matZ2_one] using hzb.2.2.2.1 t
      · change (gen 2 : ↥F.A) * zb t * ((gen 2 : ↥F.A))⁻¹ =
            eElt zb (fun s => CFSG.Quasithin.St84.G24MF.matZ2 2 s t)
        rw [G24M.matZ2_two]
        have hsingle : (fun s : Fin 4 =>
            (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) s t) = Pi.single t 1 := by
          funext s
          by_cases hst : s = t
          · subst hst; simp [Matrix.one_apply, Pi.single]
          · simp [Matrix.one_apply, Pi.single, hst]
        rw [hsingle, eElt_single]
        simpa [gen, kA] using hzb.2.2.2.2 t
    · intro l t
      have h := hFr.actZ2 l t
      rwa [← heY l] at h
  have hsq : ∀ (v : ↥Q2) (v' : ↥G24M.Q2),
      fmap (QuotientGroup.mk v) = QuotientGroup.mk v' →
      ∀ hzsq : (v : G) ^ 2 ∈ Z2,
        (gmap ⟨(v : G) ^ 2, hzsq⟩ : G24M.Y) = (v' : G24M.Y) ^ 2 := by
    intro v v' hv hzsq
    obtain ⟨w, y, hy, y', hy', hvv, hv'v⟩ :=
      (frameQuotEquiv_mk_eq_iff hf hf' v v').mp hv
    have hfQ : ∀ i, f i ∈ Q2 := (F.frame_spec hD hu hn).1
    have hfQ' : ∀ i, G24M.frame2 i ∈ G24M.Q2 := fun i =>
      Subgroup.subset_closure ⟨Fin.castAdd 4 i, rfl⟩
    have hzf : ∀ t i, zb t * f i = f i * zb t := fun t i =>
      (F.zBasis_spec hD hzb).2.2.1 t (f i) (hfQ i)
    have hzf' : ∀ t i, G24M.zb2 t * G24M.frame2 i = G24M.frame2 i * G24M.zb2 t :=
      fun t i => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (hz'.mem t)).2 (G24M.frame2 i) (hfQ' i)).symm
    have hyf : ∀ i, y * f i = f i * y := fun i =>
      (Subgroup.mem_centralizer_iff.mp hy.2 (f i) (hfQ i)).symm
    have hyf' : ∀ i, y' * G24M.frame2 i = G24M.frame2 i * y' := fun i =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy').2 (G24M.frame2 i)
        (hfQ' i)).symm
    have hsqv : (v : G) ^ 2 = eElt zb (quadMapOfCoeffs sq cm w) := by
      rw [hvv]
      exact sq_eElt_mul hz hzf hsqf hcmf w hy hyf
    have hsqv' : (v' : G24M.Y) ^ 2 = eElt G24M.zb2
        (quadMapOfCoeffs CFSG.Quasithin.St84.G24MF.sqV2
          CFSG.Quasithin.St84.G24MF.cmV2 w) := by
      rw [hv'v]
      exact sq_eElt_mul hz' hzf' (G24M.sq_frame2 hM)
        (fun i j hij => G24M.comm_frame2 hM hij) w hy' hyf'
    rw [show (gmap ⟨(v : G) ^ 2, hzsq⟩ : G24M.Y) =
        eElt G24M.zb2 (μ *ᵥ quadMapOfCoeffs sq cm w) from
      eBasisMulEquiv_apply hz hz' μ ν hμν hνμ hsqv, hsqv']
    congr 1
    rw [hs w, Matrix.mulVec_mulVec, hμν, Matrix.one_mulVec]
  have hR'Z' : ∀ r ∈ G24M.A2, ∀ z ∈ G24M.Z2, r * z * r⁻¹ ∈ G24M.Z2 := fun r hr z hz =>
    (Subgroup.mem_normalizer_iff.mp (hM.M2_le_normalizer_Z2 (hM.A2_le_M2 hr)) z).mp hz
  have hZ'c : ∀ a ∈ G24M.Z2, ∀ b ∈ G24M.Z2, a * b = b * a := fun a ha b hb =>
    hZc' a ha b ((inf_le_left : G24M.Z2 ≤ G24M.Q2) hb)
  have hfixk : ∀ r : ↥F.A, (r : G) = F.k → ∀ z ∈ G24M.Z2,
      ((e r : ↥G24M.A2) : G24M.Y) * z * ((e r : ↥G24M.A2) : G24M.Y)⁻¹ = z := by
    intro r hr z hz
    have hr2 : r = gen 2 := by
      apply Subtype.ext
      rw [hr]
      rfl
    rw [hr2, heY 2]
    exact model_k2_fixes_Z2 hM hFr hz
  have hH1 : CrossedHomPrincipal Q2 Z2 F.A G24M.Z2 G24M.A2 e :=
    F.crossedHomPrincipal hD e hR'Z' hZ'c hM.sq_Z2 hfixk
  have hZQ : Z2 ≤ Q2 := inf_le_left
  have hZQ' : G24M.Z2 ≤ G24M.Q2 := inf_le_left
  obtain ⟨θ, ψ, hψQ, hψR, hθf, hθg⟩ :=
    exists_vertexIso_special hspec.1
      (by rw [disjoint_iff, inf_comm]; exact F.inf_A)
      (hM.A2_le_M2.trans hM.M2_le_normalizer_Q2)
      (by rw [disjoint_iff, inf_comm]; exact hM.inf_A2_Q2)
      hZQ hZc (fun z hz => hD.sq_eq_one_of_mem_centerOf_right hz)
      hspec.2.2.2.2.2.1 hspec.2.2.2.2.2.2.1
      hZQ' hZc' (fun z hz => hM.sq_Z2 z hz) (fun x hx => hM.sq_Q2 x hx) hR'Z'
      e fmap gmap hconjf hconjg hsq hH1
  let ψ₀ : ↥P2 ≃* ↥G24M.M2 :=
    (MulEquiv.subgroupCongr hspec.2.2.2.2.2.2.2.symm).trans
      (ψ.trans (MulEquiv.subgroupCongr hM.sup_Q2_A2))
  have hψmem : ∀ x : ↥P2,
      (x : G) ∈ Q2 ↔ ((ψ₀ x : ↥G24M.M2) : G24M.Y) ∈ G24M.Q2 := by
    intro x
    have hmemψ : ∀ y : ↥(Q2 ⊔ F.A), (y : G) ∈ Q2 ↔
        ((ψ y : ↥(G24M.Q2 ⊔ G24M.A2)) : G24M.Y) ∈ G24M.Q2 :=
      mem_iff_of_restrict (le_sup_left : Q2 ≤ Q2 ⊔ F.A) ψ θ hψQ
    have hcoe : ((ψ₀ x : ↥G24M.M2) : G24M.Y) =
        ((ψ (MulEquiv.subgroupCongr hspec.2.2.2.2.2.2.2.symm x) :
          ↥(G24M.Q2 ⊔ G24M.A2)) : G24M.Y) := rfl
    have hxcoe : ((MulEquiv.subgroupCongr hspec.2.2.2.2.2.2.2.symm x :
        ↥(Q2 ⊔ F.A)) : G) = (x : G) := rfl
    rw [hcoe, ← hxcoe]
    exact hmemψ _
  obtain ⟨ψ₂, hψ₂Q2, hψ₂S, -⟩ := exists_mulEquiv_sylow ψ₀ hψmem
    hM.M2_le_normalizer_Q2 (F112W.isSylowTwoOf_parabolic' hR) hM.isSylowTwoOf_T0_M2
  have hbigB2 : bigB L1 L2 S = P2 ⊓ Subgroup.normalizer (S : Set G) := by
    have h := F1.bigB_eq_parabolic_inf hR.symm
    rw [bigB_comm L1 L2 S, inf_eq_left.mpr hD.le_right] at h
    exact h
  have hψB := mem_B0_iff_of_mulEquiv hM hbigB2 (hD.le_right.trans le_sup_left)
    hM.B0_le_M2 ψ₂ hψ₂S
  have hQ1B : Q1 ≤ bigB L1 L2 S := by
    change dsQ L1 L2 S ≤ bigB L1 L2 S
    rw [dsQ_eq_pCoreOf_left]
    exact (F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic hR)).trans le_sup_right
  have hQ1BN : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 : Set G) :=
    le_sup_right.trans (P_le_normalizer_dsQ_left L1 L2 S)
  have hQ1 : ∀ x : ↥P2, (x : G) ∈ Q1 ↔
      ((ψ₂ x : ↥G24M.M2) : G24M.Y) ∈ G24M.Q1 := by
    rcases eq_Q1_or_eq_Q2_of_mulEquiv hM hM.B0_le_M2 ψ₂ le_sup_right hψB hQ1B hQ1BN
      hD.card_dsQ_left with h | h
    · exact h
    · exfalso
      have hQ1P2 : Q1 ≤ P2 := hQ1B.trans le_sup_right
      have hQ2P2 : Q2 ≤ P2 := dsQ_le_P_right L1 L2 S
      have heq : Q1 = Q2 := by
        apply le_antisymm
        · intro x hx
          exact (hψ₂Q2 ⟨x, hQ1P2 hx⟩).mpr ((h ⟨x, hQ1P2 hx⟩).mp hx)
        · intro x hx
          exact (h ⟨x, hQ2P2 hx⟩).mpr ((hψ₂Q2 ⟨x, hQ2P2 hx⟩).mp hx)
      exact hD.Q1_ne_Q2 heq
  exact ⟨ψ₂, hψ₂S, hQ1⟩

end CFSG.Quasithin.F112R.St84

end

module

public import CFSG.Quasithin.Recognition.St84.G24Vertex1Abs
public import CFSG.Quasithin.Recognition.St84.G24ModelFacts
public import CFSG.Quasithin.Recognition.St84.G24ModelFrameFacts
import CFSG.Quasithin.Recognition.St84.G24Vertex1AbsQuad
import CFSG.Quasithin.Recognition.St84.G24Vertex1H1
import CFSG.Quasithin.Recognition.St84.G24RelsA
import CFSG.Quasithin.Recognition.St84.G24LinFacts
import CFSG.Quasithin.Recognition.St84.G24ModelSquares
import CFSG.GroupTheory.PGroup.ClassTwoFrameIso
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSpecial
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSylow
public import CFSG.Quasithin.Background.HSL4Q13

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.St84
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single eElt_add eElt_injective commute_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem eElt_add_mul_inv_mem conj_eElt_mul_inv_mem
  conj_eElt_eq_mulVec eEltQuotEquiv eEltQuotEquiv_ofAdd isQuotFrame_of_card IsQuotFrame
  isEBasisOf_of_card IsEBasisOf frameQuotEquiv frameQuotEquiv_mk_eq_iff
  frameQuotEquiv_conj_of_closure eBasisMulEquiv eBasisMulEquiv_apply
  eBasisMulEquiv_conj_of_closure sq_eElt_mul quadMapOfCoeffs)
open Certificates.A5GL42 (aO bO)
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

private theorem centerOf_le_self (X : Subgroup G) : centerOf X ≤ X := by
  rw [centerOf]
  exact inf_le_left

section Abstract

variable {L1 L2 S : Subgroup G}

private theorem abstract_quotFrame [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) :
    IsQuotFrame (dsQ L1 L2 S) (centerOf (dsQ L1 L2 S)) (v1Frame F.k F.e) :=
  { le := inf_le_left
    mem := (F.frame_spec hD).1
    comm := (F.frame_spec hD).2.1
    sq := (F.frame_spec hD).2.2.1
    cm := (F.frame_spec hD).2.2.2.1
    indep := F.indep
    card := (F.frame_spec hD).2.2.2.2 }

private theorem abstract_eBasis [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {z : G} (hz : z ∈ centerOf (dsQ L1 L2 S)) (hz1 : z ≠ 1) :
    IsEBasisOf (centerOf (dsQ L1 L2 S)) (z1Frame F.k z) := by
  have hspec := F.z1Frame_spec hD hz hz1
  have hmem := hspec.1
  have hZc : ∀ z ∈ centerOf (dsQ L1 L2 S), ∀ x ∈ dsQ L1 L2 S, z * x = x * z :=
    G24Vertex1.centerOf_dsQ_comm
  refine isEBasisOf_of_card hmem (fun t => ?_) (fun t s => ?_) ?_ ?_
  · rw [← pow_two]
    exact hD.sq_eq_one_of_mem_centerOf_left (hmem t)
  · exact hZc (z1Frame F.k z t) (hmem t) (z1Frame F.k z s) (centerOf_le_self _ (hmem s))
  · intro y hy
    obtain ⟨u, hu⟩ := hspec.2.2.1 y hy
    rw [hu]
    exact eElt_mem_of_forall_mem (fun t => Subgroup.subset_closure (Set.mem_range_self t)) u
  · rw [hD.card_centerOf_dsQ_left]
    norm_num

private theorem exists_z1_ne_one [Finite G] (hD : G24LocalData L1 L2 S) :
    ∃ z : G, z ∈ centerOf (dsQ L1 L2 S) ∧ z ≠ 1 := by
  haveI : Nontrivial ↥(centerOf (dsQ L1 L2 S)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hD.card_centerOf_dsQ_left]
    norm_num
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(centerOf (dsQ L1 L2 S)))
  exact ⟨(z : G), z.2, fun h => hz (Subtype.ext h)⟩

private def v1Gen (F : G24Frame1 L1 L2 S) :
    Fin 3 → ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)) :=
  ![⟨F.a, ⟨Subgroup.mem_sup_left F.a_mem.1, F.a_mem.2⟩⟩,
    ⟨F.b, ⟨Subgroup.mem_sup_left F.b_mem.1, F.b_mem.2⟩⟩,
    ⟨F.k, ⟨Subgroup.mem_sup_right F.k_mem,
      Subgroup.mem_centralizer_singleton_iff.mpr (by simp)⟩⟩]

private theorem v1Gen_closure [Finite G] (F : G24Frame1 L1 L2 S) :
    Subgroup.closure (Set.range (v1Gen F)) = ⊤ := by
  have hset : Set.range ![F.a, F.b, F.k] = ({F.a, F.b, F.k} : Set G) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  let R : Subgroup G := (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)
  apply Subgroup.map_injective (f := R.subtype) Subtype.val_injective
  rw [MonoidHom.map_closure]
  have himg : R.subtype '' Set.range (v1Gen F) = Set.range ![F.a, F.b, F.k] := by
    rw [← Set.range_comp]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [himg, hset, F.closure_eq]
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨m, -, rfl⟩
    exact m.2

private theorem v1Gen_relators [Finite G] (F : G24Frame1 L1 L2 S) :
    ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA,
      CFSG.Certificates.signedProd (v1Gen F) w = 1 := by
  have ha : (v1Gen F 0) ^ 2 = 1 := Subtype.ext F.a_sq
  have hb : (v1Gen F 1) ^ 3 = 1 := by
    apply Subtype.ext
    show F.b ^ 3 = 1
    exact F.b_cube
  have hab : (v1Gen F 0 * v1Gen F 1) ^ 5 = 1 := by
    apply Subtype.ext
    show (F.a * F.b) ^ 5 = 1
    exact F.ab_five
  have hk : (v1Gen F 2) ^ 3 = 1 := by
    apply Subtype.ext
    show F.k ^ 3 = 1
    rw [← F.orderOf_k]
    exact pow_orderOf_eq_one F.k
  have hak : v1Gen F 0 * v1Gen F 2 = v1Gen F 2 * v1Gen F 0 := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp F.a_mem.2
  have hbk : v1Gen F 1 * v1Gen F 2 = v1Gen F 2 * v1Gen F 1 := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp F.b_mem.2
  simpa [v1Gen] using signedProd_relsA ha hb hab hk hak hbk

private theorem v1Gen_frame_action [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) (l : Fin 3) (j : Fin 8) :
    (v1Gen F l : G) * v1Frame F.k F.e j * (v1Gen F l : G)⁻¹ *
      (eElt (v1Frame F.k F.e) fun i => CFSG.Quasithin.St84.G24MF.matV1 l i j)⁻¹ ∈
      centerOf (dsQ L1 L2 S) := by
  fin_cases l
  · change (F.a : G) * v1Frame F.k F.e j * (F.a : G)⁻¹ *
      (eElt (v1Frame F.k F.e) fun i => CFSG.Quasithin.St84.G24MF.matV1 0 i j)⁻¹ ∈
      centerOf (dsQ L1 L2 S)
    rw [G24M.matV1_zero]
    exact F.act_a j
  · change (F.b : G) * v1Frame F.k F.e j * (F.b : G)⁻¹ *
      (eElt (v1Frame F.k F.e) fun i => CFSG.Quasithin.St84.G24MF.matV1 1 i j)⁻¹ ∈
      centerOf (dsQ L1 L2 S)
    rw [G24M.matV1_one]
    exact F.act_b j
  · change (F.k : G) * v1Frame F.k F.e j * (F.k : G)⁻¹ *
      (eElt (v1Frame F.k F.e) fun i => CFSG.Quasithin.St84.G24MF.matV1 2 i j)⁻¹ ∈
      centerOf (dsQ L1 L2 S)
    rw [G24M.matV1_two]
    exact F.act_k j

private theorem v1Gen_z1Frame_action [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {z : G} (hz : z ∈ centerOf (dsQ L1 L2 S)) (hz1 : z ≠ 1)
    (l : Fin 3) (t : Fin 2) :
    (v1Gen F l : G) * z1Frame F.k z t * (v1Gen F l : G)⁻¹ =
      eElt (z1Frame F.k z) (fun s => CFSG.Quasithin.St84.G24MF.matZ1 l s t) := by
  have hspec := F.z1Frame_spec hD hz hz1
  have hsingle : (fun s : Fin 2 =>
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) s t) = Pi.single t 1 := by
    funext s
    by_cases hst : s = t
    · subst hst; simp [Matrix.one_apply, Pi.single]
    · simp [Matrix.one_apply, Pi.single, hst]
  fin_cases l
  · change (F.a : G) * z1Frame F.k z t * (F.a : G)⁻¹ =
      eElt (z1Frame F.k z) (fun s => CFSG.Quasithin.St84.G24MF.matZ1 0 s t)
    rw [G24M.matZ1_zero, hsingle, eElt_single]
    exact hspec.2.2.2.1 t
  · change (F.b : G) * z1Frame F.k z t * (F.b : G)⁻¹ =
      eElt (z1Frame F.k z) (fun s => CFSG.Quasithin.St84.G24MF.matZ1 1 s t)
    rw [G24M.matZ1_one, hsingle, eElt_single]
    exact hspec.2.2.2.2.1 t
  · change (F.k : G) * z1Frame F.k z t * (F.k : G)⁻¹ =
      eElt (z1Frame F.k z) (fun s => CFSG.Quasithin.St84.G24MF.matZ1 2 s t)
    rw [G24M.matZ1_two]
    exact hspec.2.2.2.2.2 t

end Abstract

private theorem model_frame_gen (hM : G24M.Facts) :
    G24M.Q1 ≤ Subgroup.closure (Set.range G24M.frame1) ⊔ G24M.Z1 := by
  rw [show G24M.Q1 = Subgroup.closure (Set.range G24M.pc1Y) from rfl]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨j, rfl⟩
  refine Fin.addCases (m := 8) (n := 2) (fun i => ?_) (fun t => ?_) j
  · rw [show G24M.pc1Y (Fin.castAdd 2 i) = G24M.frame1 i from rfl]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, rfl⟩)
  · rw [show G24M.pc1Y (Fin.natAdd 8 t) = G24M.zb1 t from rfl]
    exact Subgroup.mem_sup_right (by
      rw [hM.Z1_eq]
      exact Subgroup.subset_closure (by fin_cases t <;> simp [G24M.zb1]))

private theorem model_zb1_gen (hM : G24M.Facts) :
    G24M.Z1 ≤ Subgroup.closure (Set.range G24M.zb1) := by
  rw [hM.Z1_eq]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ (rfl | rfl)
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨1, rfl⟩

private theorem model_zb1_mem (hM : G24M.Facts) (t : Fin 2) : G24M.zb1 t ∈ G24M.Z1 := by
  rw [hM.Z1_eq]
  exact Subgroup.subset_closure (by fin_cases t <;> simp [G24M.zb1])

private theorem model_quotFrame (hM : G24M.Facts) :
    IsQuotFrame G24M.Q1 G24M.Z1 G24M.frame1 := by
  haveI : (G24M.Z1.subgroupOf G24M.Q1).Normal :=
    Subgroup.normal_of_le_center fun z hz =>
      Subgroup.mem_center_iff.mpr fun x =>
        Subtype.ext (by
          simpa [Subgroup.coe_mul] using (Subgroup.mem_centralizer_iff.mp
            (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).2 x x.2))
  have hmem : ∀ i : Fin 8, G24M.frame1 i ∈ G24M.Q1 := fun i =>
    Subgroup.subset_closure ⟨Fin.castAdd 2 i, rfl⟩
  refine isQuotFrame_of_card (centerOf_le_self _) hmem ?_ ?_ ?_
    (model_frame_gen hM) ?_
  · intro y hy i
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2
      (G24M.frame1 i) (hmem i)).symm
  · intro i
    exact hM.sq_Q1 _ (hmem i)
  · intro i j
    exact hM.comm_Q1 _ (hmem i) _ (hmem j)
  · rw [hM.card_Q1, hM.card_Z1]
    norm_num

private theorem model_eBasis (hM : G24M.Facts) : IsEBasisOf G24M.Z1 G24M.zb1 := by
  have hmem := model_zb1_mem hM
  refine isEBasisOf_of_card hmem (fun t => ?_) (fun t s => ?_)
    (model_zb1_gen hM) ?_
  · rw [← pow_two]
    exact hM.sq_Z1 _ (hmem t)
  · exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hmem t)).2
      (G24M.zb1 s) (centerOf_le_self _ (hmem s))).symm
  · rw [hM.card_Z1]
    norm_num

private theorem model_a1_fixes_Z1 (hM : G24M.Facts) (hFr : G24M.FrameFacts)
    {z : G24M.Y} (hz : z ∈ G24M.Z1) :
    G24M.A1img 0 * z * (G24M.A1img 0)⁻¹ = z := by
  have hfix : ∀ t, G24M.A1img 0 * G24M.zb1 t * (G24M.A1img 0)⁻¹ =
      eElt G24M.zb1 (fun s => CFSG.Quasithin.St84.G24MF.matZ1 0 s t) := by
    intro t
    have h := hFr.actZ1 0 t
    rw [G24M.matZ1_zero] at h ⊢
    have hsingle : (fun s : Fin 2 =>
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) s t) = Pi.single t 1 := by
      funext s
      by_cases hst : s = t
      · subst hst; simp [Matrix.one_apply, Pi.single]
      · simp [Matrix.one_apply, Pi.single, hst]
    rw [hsingle, eElt_single] at h ⊢
    exact h
  obtain ⟨w, hw⟩ := (model_eBasis hM).span z hz
  rw [hw, conj_eElt_eq_mulVec (model_eBasis hM).ebasis.sq
    (model_eBasis hM).ebasis.comm (CFSG.Quasithin.St84.G24MF.matZ1 0) hfix w,
    G24M.matZ1_zero, Matrix.one_mulVec]

private theorem model_b1_fixes_Z1 (hM : G24M.Facts) (hFr : G24M.FrameFacts)
    {z : G24M.Y} (hz : z ∈ G24M.Z1) :
    G24M.A1img 1 * z * (G24M.A1img 1)⁻¹ = z := by
  have hfix : ∀ t, G24M.A1img 1 * G24M.zb1 t * (G24M.A1img 1)⁻¹ =
      eElt G24M.zb1 (fun s => CFSG.Quasithin.St84.G24MF.matZ1 1 s t) := by
    intro t
    have h := hFr.actZ1 1 t
    rw [G24M.matZ1_one] at h ⊢
    have hsingle : (fun s : Fin 2 =>
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) s t) = Pi.single t 1 := by
      funext s
      by_cases hst : s = t
      · subst hst; simp [Matrix.one_apply, Pi.single]
      · simp [Matrix.one_apply, Pi.single, hst]
    rw [hsingle, eElt_single] at h ⊢
    exact h
  obtain ⟨w, hw⟩ := (model_eBasis hM).span z hz
  rw [hw, conj_eElt_eq_mulVec (model_eBasis hM).ebasis.sq
    (model_eBasis hM).ebasis.comm (CFSG.Quasithin.St84.G24MF.matZ1 1) hfix w,
    G24M.matZ1_one, Matrix.one_mulVec]

private theorem exists_complement_iso [Finite G]
    {L1 L2 S : Subgroup G} (F : G24Frame1 L1 L2 S) (hD : G24LocalData L1 L2 S)
    (hM : G24M.Facts) :
    ∃ e : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)) ≃* ↥G24M.A1,
      ∀ j, e (v1Gen F j) = G24M.A1imgQ j :=
  exists_mulEquiv_relsA (v1Gen F) G24M.A1imgQ (v1Gen_relators F) hM.rels_A1imgQ
    (v1Gen_closure F) hM.closure_range_A1imgQ F.card_A hM.card_A1

theorem exists_vertexIso_left [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) (hM : G24M.Facts) (hFr : G24M.FrameFacts) :
    ∃ ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥G24M.M1,
      (∀ x : ↥(L1 ⊔ bigB L1 L2 S),
        (x : G) ∈ S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.T0) ∧
      (∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ dsQ L1 L2 S ↔
        ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.Q1) := by
  classical
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let Q1 : Subgroup G := dsQ L1 L2 S
  let Z1 : Subgroup G := centerOf Q1
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  obtain ⟨F⟩ := nonempty_g24Frame1 hF h1 h2 hD
  obtain ⟨z0, hz0, hz1⟩ := exists_z1_ne_one hD
  let R : Subgroup G := P1 ⊓ Subgroup.centralizer ({F.k} : Set G)
  have hspec := F.special_data hD
  have hZc : ∀ z ∈ Z1, ∀ x ∈ Q1, z * x = x * z := hspec.2.2.2.1
  haveI : (Z1.subgroupOf Q1).Normal := Subgroup.normal_of_le_center fun z hz =>
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZc z hz x x.2).symm
  have hZc' : ∀ z ∈ G24M.Z1, ∀ x ∈ G24M.Q1, z * x = x * z := fun z hz x hx =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 x hx).symm
  haveI : (G24M.Z1.subgroupOf G24M.Q1).Normal := Subgroup.normal_of_le_center fun z hz =>
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZc' z hz x x.2).symm
  have hf : IsQuotFrame Q1 Z1 (v1Frame F.k F.e) := abstract_quotFrame F hD
  have hf' : IsQuotFrame G24M.Q1 G24M.Z1 G24M.frame1 := model_quotFrame hM
  have hz : IsEBasisOf Z1 (z1Frame F.k z0) := abstract_eBasis F hD hz0 hz1
  have hz' : IsEBasisOf G24M.Z1 G24M.zb1 := model_eBasis hM
  obtain ⟨sq, cm, hsqf, hcmf, hqa, hqb, hqk, hne⟩ := F.exists_quad hD hz0 hz1
  obtain ⟨s, hs3, hs⟩ := G24M.quad1_proportional hqa hqb hqk hne
  let μ : Matrix (Fin 2) (Fin 2) (ZMod 2) := om ^ (3 - s)
  let ν : Matrix (Fin 2) (Fin 2) (ZMod 2) := om ^ s
  have hμν : μ * ν = 1 := by
    rw [show μ * ν = om ^ ((3 - s) + s) from (pow_add _ (3 - s) s).symm,
      show (3 - s) + s = 3 by omega, G24M.om_pow_three]
  have hνμ : ν * μ = 1 := by
    rw [show ν * μ = om ^ (s + (3 - s)) from (pow_add _ s (3 - s)).symm,
      show s + (3 - s) = 3 by omega, G24M.om_pow_three]
  obtain ⟨e, he⟩ := exists_complement_iso F hD hM
  have heY : ∀ j, ((e (v1Gen F j) : ↥G24M.A1) : G24M.Y) = G24M.A1img j := by
    intro j
    have h := congrArg Subtype.val (he j)
    fin_cases j <;> simpa [G24M.A1imgQ, G24M.A1img, G24M.A1Q, G24M.A1gen] using h
  let fmap : ↥Q1 ⧸ Z1.subgroupOf Q1 ≃*
      ↥G24M.Q1 ⧸ G24M.Z1.subgroupOf G24M.Q1 := frameQuotEquiv hf hf'
  let gmap : ↥Z1 ≃* ↥G24M.Z1 := eBasisMulEquiv hz hz' μ ν hμν hνμ
  have hconjf : ∀ (r : ↥R) (v w : ↥Q1) (v' w' : ↥G24M.Q1),
      (w : G) = (r : G) * v * (r : G)⁻¹ →
      (w' : G24M.Y) = (e r : G24M.Y) * v' * (e r : G24M.Y)⁻¹ →
      fmap (QuotientGroup.mk v) = QuotientGroup.mk v' →
      fmap (QuotientGroup.mk w) = QuotientGroup.mk w' := by
    refine frameQuotEquiv_conj_of_closure hf hf' hspec.1 hspec.2.2.2.2.2.2.1
      (hM.A1_le_M1.trans hM.M1_le_normalizer_Q1) ?_ e (v1Gen F) (v1Gen_closure F)
      CFSG.Quasithin.St84.G24MF.matV1 ?_ ?_
    · intro r hr z hzr
      exact (Subgroup.mem_normalizer_iff.mp (hM.M1_le_normalizer_Z1 (hM.A1_le_M1 hr)) z).mp hzr
    · intro l j
      exact v1Gen_frame_action F hD l j
    · intro l j
      obtain ⟨c, hc⟩ := hFr.act1 l j
      rw [← heY l] at hc
      have hfQ' : ∀ i, G24M.frame1 i ∈ G24M.Q1 := fun i =>
        Subgroup.subset_closure ⟨Fin.castAdd 2 i, rfl⟩
      have hcomm : Commute (eElt G24M.zb1 c)
          (eElt G24M.frame1 (fun i => CFSG.Quasithin.St84.G24MF.matV1 l i j)) := by
        apply commute_eElt (x := eElt G24M.zb1 c)
        intro i
        exact (commute_eElt (x := G24M.frame1 i) (fun t =>
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hz'.mem t)).2 _
            (hfQ' i)) c).symm
      rw [hc]
      rw [show eElt G24M.frame1 (fun i => CFSG.Quasithin.St84.G24MF.matV1 l i j) *
          eElt G24M.zb1 c *
          (eElt G24M.frame1 (fun i => CFSG.Quasithin.St84.G24MF.matV1 l i j))⁻¹ =
          eElt G24M.zb1 c from by
        rw [← hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]]
      exact eElt_mem_of_forall_mem hz'.mem c
  have hconjg : ∀ (r : ↥R) (y w : ↥Z1),
      (w : G) = (r : G) * y * (r : G)⁻¹ →
      (gmap w : G24M.Y) = (e r : G24M.Y) * (gmap y : G24M.Y) * (e r : G24M.Y)⁻¹ := by
    refine eBasisMulEquiv_conj_of_closure hz hz' μ ν hμν hνμ
      hspec.2.2.2.2.2.2.1 e (v1Gen F) (v1Gen_closure F) CFSG.Quasithin.St84.G24MF.matZ1
      ?_ ?_ ?_
    · intro l
      fin_cases l
      · change Commute μ (CFSG.Quasithin.St84.G24MF.matZ1 0)
        rw [G24M.matZ1_zero]
        show μ * 1 = 1 * μ
        rw [mul_one, one_mul]
      · change Commute μ (CFSG.Quasithin.St84.G24MF.matZ1 1)
        rw [G24M.matZ1_one]
        show μ * 1 = 1 * μ
        rw [mul_one, one_mul]
      · change Commute μ (CFSG.Quasithin.St84.G24MF.matZ1 2)
        rw [G24M.matZ1_two]
        exact (Commute.self_pow om (3 - s)).symm
    · intro l t
      exact v1Gen_z1Frame_action F hD hz0 hz1 l t
    · intro l t
      have h := hFr.actZ1 l t
      rwa [← heY l] at h
  have hsq : ∀ (v : ↥Q1) (v' : ↥G24M.Q1),
      fmap (QuotientGroup.mk v) = QuotientGroup.mk v' →
      ∀ hzsq : (v : G) ^ 2 ∈ Z1,
        (gmap ⟨(v : G) ^ 2, hzsq⟩ : G24M.Y) = (v' : G24M.Y) ^ 2 := by
    intro v v' hv hzsq
    obtain ⟨w, y, hy, y', hy', hvv, hv'v⟩ :=
      (frameQuotEquiv_mk_eq_iff hf hf' v v').mp hv
    have hfQ : ∀ i, v1Frame F.k F.e i ∈ Q1 := (F.frame_spec hD).1
    have hfQ' : ∀ i, G24M.frame1 i ∈ G24M.Q1 := fun i =>
      Subgroup.subset_closure ⟨Fin.castAdd 2 i, rfl⟩
    have hzf : ∀ t i, z1Frame F.k z0 t * v1Frame F.k F.e i =
        v1Frame F.k F.e i * z1Frame F.k z0 t := fun t i =>
      hf.comm (z1Frame F.k z0 t) (hz.mem t) i
    have hzf' : ∀ t i, G24M.zb1 t * G24M.frame1 i = G24M.frame1 i * G24M.zb1 t :=
      fun t i => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (hz'.mem t)).2 (G24M.frame1 i) (hfQ' i)).symm
    have hyf : ∀ i, y * v1Frame F.k F.e i = v1Frame F.k F.e i * y := fun i =>
      (Subgroup.mem_centralizer_iff.mp hy.2 (v1Frame F.k F.e i) (hfQ i)).symm
    have hyf' : ∀ i, y' * G24M.frame1 i = G24M.frame1 i * y' := fun i =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy').2 (G24M.frame1 i)
        (hfQ' i)).symm
    have hsqv : (v : G) ^ 2 = eElt (z1Frame F.k z0) (quadMapOfCoeffs sq cm w) := by
      rw [hvv]
      exact sq_eElt_mul hz hzf hsqf hcmf w hy hyf
    have hsqv' : (v' : G24M.Y) ^ 2 = eElt G24M.zb1
        (quadMapOfCoeffs CFSG.Quasithin.St84.G24MF.sqV1
          CFSG.Quasithin.St84.G24MF.cmV1 w) := by
      rw [hv'v]
      exact sq_eElt_mul hz' hzf' (G24M.sq_frame1 hM)
        (fun i j hij => G24M.comm_frame1 hM hij) w hy' hyf'
    have harg : μ *ᵥ quadMapOfCoeffs sq cm w = quadMapOfCoeffs
        CFSG.Quasithin.St84.G24MF.sqV1 CFSG.Quasithin.St84.G24MF.cmV1 w := by
      rw [hs w, Matrix.mulVec_mulVec, hμν, Matrix.one_mulVec]
    rw [show (gmap ⟨(v : G) ^ 2, hzsq⟩ : G24M.Y) =
        eElt G24M.zb1 (μ *ᵥ quadMapOfCoeffs sq cm w) from
      eBasisMulEquiv_apply hz hz' μ ν hμν hνμ hsqv, hsqv', harg]
  have hR'Z' : ∀ r ∈ G24M.A1, ∀ z ∈ G24M.Z1, r * z * r⁻¹ ∈ G24M.Z1 := fun r hr z hzr =>
    (Subgroup.mem_normalizer_iff.mp (hM.M1_le_normalizer_Z1 (hM.A1_le_M1 hr)) z).mp hzr
  have hZ'c : ∀ a ∈ G24M.Z1, ∀ b ∈ G24M.Z1, a * b = b * a := fun a ha b hb =>
    hZc' a ha b ((inf_le_left : G24M.Z1 ≤ G24M.Q1) hb)
  have ha : ∀ r : ↥R, (r : G) = F.a → ∀ z ∈ G24M.Z1,
      ((e r : ↥G24M.A1) : G24M.Y) * z * ((e r : ↥G24M.A1) : G24M.Y)⁻¹ = z := by
    intro r hr z hzr
    have hr2 : r = v1Gen F 0 := by
      apply Subtype.ext
      rw [hr]
      rfl
    rw [hr2, heY 0]
    exact model_a1_fixes_Z1 hM hFr hzr
  have hb : ∀ r : ↥R, (r : G) = F.b → ∀ z ∈ G24M.Z1,
      ((e r : ↥G24M.A1) : G24M.Y) * z * ((e r : ↥G24M.A1) : G24M.Y)⁻¹ = z := by
    intro r hr z hzr
    have hr2 : r = v1Gen F 1 := by
      apply Subtype.ext
      rw [hr]
      rfl
    rw [hr2, heY 1]
    exact model_b1_fixes_Z1 hM hFr hzr
  have hH1 : CrossedHomPrincipal Q1 Z1 R G24M.Z1 G24M.A1 e :=
    F.crossedHomPrincipal hD e hR'Z' hZ'c hM.sq_Z1 ha hb
  have hZQ : Z1 ≤ Q1 := inf_le_left
  have hZQ' : G24M.Z1 ≤ G24M.Q1 := inf_le_left
  obtain ⟨θ, ψ, hψQ, hψR, hθf, hθg⟩ :=
    exists_vertexIso_special hspec.1 hspec.2.1
      (hM.A1_le_M1.trans hM.M1_le_normalizer_Q1)
      (by rw [disjoint_iff, inf_comm]; exact hM.inf_A1_Q1)
      hZQ hZc (fun z hzr => hD.sq_eq_one_of_mem_centerOf_left hzr)
      hspec.2.2.2.2.2.1 hspec.2.2.2.2.2.2.1
      hZQ' hZc' (fun z hzr => hM.sq_Z1 z hzr) (fun x hx => hM.sq_Q1 x hx) hR'Z'
      e fmap gmap hconjf hconjg hsq hH1
  let ψ₀ : ↥P1 ≃* ↥G24M.M1 :=
    (MulEquiv.subgroupCongr hspec.2.2.2.2.2.2.2.symm).trans
      (ψ.trans (MulEquiv.subgroupCongr hM.sup_Q1_A1))
  have hψmem : ∀ x : ↥P1,
      (x : G) ∈ Q1 ↔ ((ψ₀ x : ↥G24M.M1) : G24M.Y) ∈ G24M.Q1 := by
    intro x
    have hmemψ : ∀ y : ↥(Q1 ⊔ R), (y : G) ∈ Q1 ↔
        ((ψ y : ↥(G24M.Q1 ⊔ G24M.A1)) : G24M.Y) ∈ G24M.Q1 :=
      mem_iff_of_restrict (le_sup_left : Q1 ≤ Q1 ⊔ R) ψ θ hψQ
    have hcoe : ((ψ₀ x : ↥G24M.M1) : G24M.Y) =
        ((ψ (MulEquiv.subgroupCongr hspec.2.2.2.2.2.2.2.symm x) :
          ↥(G24M.Q1 ⊔ G24M.A1)) : G24M.Y) := rfl
    have hxcoe : ((MulEquiv.subgroupCongr hspec.2.2.2.2.2.2.2.symm x :
        ↥(Q1 ⊔ R)) : G) = (x : G) := rfl
    rw [hcoe, ← hxcoe]
    exact hmemψ _
  obtain ⟨ψ₁, hψ₁Q, hψ₁S, -⟩ := exists_mulEquiv_sylow ψ₀ hψmem
    hM.M1_le_normalizer_Q1 (F112W.isSylowTwoOf_parabolic hR) hM.isSylowTwoOf_T0_M1
  exact ⟨ψ₁, hψ₁S, hψ₁Q⟩

end CFSG.Quasithin.F112R.St84

end

end

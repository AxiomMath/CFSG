module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenPair
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenDict
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenMod
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenRS
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenRpp
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenWt
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinSetup
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinMain
public import CFSG.Quasithin.EmptyFaithful.S14612GB0a
public import CFSG.Quasithin.EmptyFaithful.S14612GB1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417
open scoped commutatorElement

namespace NoE9Z4GenBridge

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem pairCtx_gen (S : Setting146 G T M) (hH : IsHTM T M H)
    (hB : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
      conjClosure (VZ T M) H) :
    ∃ z : G, NoE9Z4GenGrp.PairCtx (pCoreOf 2 H) (conjClosure (VZ T M) H)
      (quasithinOmegaOneCenter T)
      (conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) H z := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  obtain ⟨z, hz, hz1, hZe⟩ := NoE9Z4MinGrp.exists_involution_of_card_two S.card_Z
  have hUab := S.lemma_14_5_15_two hH
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ conjClosure (VZ T M) H := le_conjClosure _ _
  have hzcent : ∀ g ∈ H, g * z = z * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp (S.le_mcOf hH hg) z hz).symm
  refine ⟨z, ?_⟩
  exact
  { z_ne := hz1
    z_mem := hz
    Z_eq := hZe
    Z_le_U := hZV.trans hVU
    U_le_Q := h91.conjClosure_Vp_le_pCoreOf
    Q_le_H := pCoreOf_le 2 H
    U_comm := fun u hu u' hu' =>
      congrArg Subtype.val (hUab.1.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩)
    U_sq := fun u hu => by
      have := isElemAbelian_pow_eq_one hUab hu
      rwa [pow_two] at this
    z_cent := hzcent
    normQ := fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hg) x).mp hx
    normU := fun g hg u hu =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hg) u).mp hu
    pair_mem := fun u hu x hx => by
      have := h91.commutator_conjClosure_le u hu x hx
      rwa [commutatorElement_def]
    ker_left := fun x hx hcomm =>
      hB.le ⟨hx, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        commutatorElement_eq_one_iff_mul_comm.mp (hcomm u hu)⟩
    Z_le_Cq := fun c hc => ⟨(hZV.trans hVU) hc, Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rcases hZe c hc with rfl | rfl
      · simp
      · exact hzcent x (pCoreOf_le 2 H hx)⟩
    Cq_le_U := inf_le_left
    Cq_cent := fun c hc x hx =>
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hc.2 x hx).symm
    ker_right := fun u hu hcomm =>
      ⟨hu, Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (commutatorElement_eq_one_iff_mul_comm.mp (hcomm x hx)).symm⟩ }

omit [Finite G] in
theorem cls_cq_ker {Q U Z Cq Hs : Subgroup G} {z : G}
    (P : NoE9Z4GenGrp.PairCtx Q U Z Cq Hs z)
    {U0 : Subgroup G} {K : Type*} [CommGroup K] {β : ↥Hs →* MulAut K} {cls : G → K}
    (hirr : ∀ W' : Subgroup K, (∀ x ∈ β.range, ∀ w ∈ W', x w ∈ W') → W' = ⊥ ∨ W' = ⊤)
    (hK : commV β.range = ⊤) (hU0U : U0 ≤ U)
    (hmul : ∀ u ∈ U, ∀ u' ∈ U, cls (u * u') = cls u * cls u')
    (hker0 : ∀ u ∈ U0, (cls u = 1 ↔ u ∈ Z))
    (hconj : ∀ x : ↥Hs, ∀ u ∈ U, cls ((x : G) * u * (x : G)⁻¹) = β x (cls u))
    (hcomm : ∀ u ∈ U, ∀ x ∈ Hs, ⁅u, x⁆ ∈ U0)
    (hUK : ⁅U, Hs⁆ ≤ Subgroup.centralizer (Q : Set G) → False) :
    ∀ c ∈ Cq, cls c = 1 := by
  have hone : cls 1 = 1 := (hker0 1 U0.one_mem).mpr Z.one_mem
  have hinv : ∀ u ∈ U, cls u⁻¹ = (cls u)⁻¹ := by
    intro u hu
    have h1 := hmul u hu u⁻¹ (U.inv_mem hu)
    rw [mul_inv_cancel, hone] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  let clsHom : ↥U →* K := MonoidHom.mk' (fun u => cls u.1) (fun a b => hmul a.1 a.2 b.1 b.2)
  let Sg : Subgroup K := (Cq.subgroupOf U).map clsHom
  have hSgmem : ∀ k : K, k ∈ Sg ↔ ∃ c ∈ Cq, cls c = k := by
    intro k
    constructor
    · rintro ⟨⟨c, hcU⟩, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, P.Cq_le_U hc⟩, hc, rfl⟩
  have hCqinv : ∀ x ∈ Hs, ∀ c ∈ Cq, x * c * x⁻¹ ∈ Cq := by
    intro x hx c hc
    refine P.ker_right _ (P.normU x hx c (P.Cq_le_U hc)) fun y hy => ?_
    have hy' : x⁻¹ * y * x ∈ Q := by simpa using P.normQ x⁻¹ (inv_mem hx) y hy
    have h1 := P.Cq_cent c hc _ hy'
    have e : ⁅x * c * x⁻¹, y⁆ = x * ⁅c, x⁻¹ * y * x⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, h1]
    group
  have hinvSg : ∀ g ∈ β.range, ∀ w ∈ Sg, g w ∈ Sg := by
    rintro _ ⟨y, rfl⟩ w hw
    obtain ⟨c, hc, rfl⟩ := (hSgmem w).mp hw
    exact (hSgmem _).mpr ⟨(y : G) * c * (y : G)⁻¹, hCqinv y y.2 c hc,
      hconj y c (P.Cq_le_U hc)⟩
  rcases hirr Sg hinvSg with hbot | htop
  · intro c hc
    have h1 : cls c ∈ Sg := (hSgmem _).mpr ⟨c, hc, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact h1
  · exfalso
    let Dg : Subgroup K := ((Cq ⊓ U0).subgroupOf U).map clsHom
    have hDgmem : ∀ c ∈ Cq ⊓ U0, cls c ∈ Dg := fun c hc =>
      ⟨⟨c, P.Cq_le_U hc.1⟩, hc, rfl⟩
    have hgen : commV β.range ≤ Dg := by
      unfold commV
      rw [Subgroup.closure_le]
      rintro _ ⟨g, hg, k, rfl⟩
      obtain ⟨y, rfl⟩ := hg
      have hk : k ∈ Sg := by rw [htop]; exact Subgroup.mem_top k
      obtain ⟨c, hc, rfl⟩ := (hSgmem k).mp hk
      have hcU := P.Cq_le_U hc
      have hyc : (y : G) * c⁻¹ * (y : G)⁻¹ ∈ Cq := hCqinv y y.2 c⁻¹ (Cq.inv_mem hc)
      have e : ⁅c, (y : G)⁆ = c * ((y : G) * c⁻¹ * (y : G)⁻¹) := by
        simp only [commutatorElement_def]
        group
      have hc'' : ⁅c, (y : G)⁆ ∈ Cq ⊓ U0 := ⟨e ▸ Cq.mul_mem hc hyc, hcomm c hcU y y.2⟩
      have hcl : cls ⁅c, (y : G)⁆ = cls c * (β y (cls c))⁻¹ := by
        rw [e, hmul c hcU _ (P.normU y y.2 c⁻¹ (U.inv_mem hcU)), hconj y c⁻¹ (U.inv_mem hcU),
          hinv c hcU, map_inv]
      have e2 : (β y) (cls c) * (cls c)⁻¹ = (cls ⁅c, (y : G)⁆)⁻¹ := by
        rw [hcl, mul_inv_rev, inv_inv, mul_comm]
      rw [e2]
      exact Dg.inv_mem (hDgmem _ hc'')
    have hDtop : Dg = ⊤ := by
      rw [eq_top_iff, ← hK]
      exact hgen
    have hU0Cq : U0 ≤ Cq := by
      intro u hu
      have hk : cls u ∈ Dg := by rw [hDtop]; exact Subgroup.mem_top _
      obtain ⟨⟨c, hcU⟩, hc, hcls⟩ := hk
      have hcC : c ∈ Cq ⊓ U0 := hc
      have hcls' : cls c = cls u := hcls
      have huc : u * c⁻¹ ∈ U0 := U0.mul_mem hu (U0.inv_mem hcC.2)
      have hcls1 : cls (u * c⁻¹) = 1 := by
        rw [hmul u (hU0U hu) c⁻¹ (U.inv_mem hcU), hinv c hcU, hcls', mul_inv_cancel]
      have hZ : u * c⁻¹ ∈ Z := (hker0 _ huc).mp hcls1
      have e : u = (u * c⁻¹) * c := by group
      rw [e]
      exact Cq.mul_mem (P.Z_le_Cq hZ) hcC.1
    refine hUK (Subgroup.commutator_le.2 fun u hu x hx => ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (commutatorElement_eq_one_iff_mul_comm.mp
        (P.Cq_cent _ (hU0Cq (hcomm u hu x hx)) y hy)).symm

end NoE9Z4GenBridge

theorem noE9Z4_caseA (h35 : Lemma1435) (h5 : Stage1461Five) {G : Type} [Group G] [Finite G]
    {T M H PQ : Subgroup G} {p : ℕ} (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p)
    (hB : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
      conjClosure (VZ T M) H)
    (hA : ∀ u ∈ conjClosure (VZ T M) H, (∀ x ∈ H, ⁅u, x⁆ ∈ quasithinOmegaOneCenter T) →
      ∀ y ∈ pCoreOf 2 H, ⁅u, y⁆ = 1) : False := by
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  obtain ⟨-, -, -, hsplit, hinf, -, -⟩ := class_data_of_lemma1435 h35 S hred h91 h98
  have hES := e9z4Str_of_shape classAutShapeStmt h35 S hred hshape h98
  have hK : commV (resBeta (rhoH h91)).range = ⊤ := hES.commV_X
  obtain ⟨cls, U0, hU0U, hZU0, hnormU0, hmul, hker0, hconj, hsurj, hcomm, hkerH⟩ :=
    NoE9Z4GenBridge.exists_cls hsplit hinf
  obtain ⟨z, P⟩ := NoE9Z4GenBridge.pairCtx_gen S hH hB
  have hCq : ∀ c ∈ conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G),
      cls c = 1 :=
    NoE9Z4GenBridge.cls_cq_ker P (fun _ hinv => hES.irreducible hinv) hK hU0U hmul hker0 hconj hcomm
      (S.not_uK_le_centralizer_pCoreOf h5 hred)
  have hker : ∀ u ∈ conjClosure (VZ T M) H, cls u = 1 →
      u ∈ conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    fun u hu h1 => ⟨hu, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (commutatorElement_eq_one_iff_mul_comm.mp (hA u hu (hkerH u hu h1) y hy)).symm⟩
  have D : NoE9Z4GenGrp.ClsData P U0 (resBeta (rhoH h91)) cls :=
    { U0_le := hU0U
      Z_le_U0 := hZU0
      normU0 := hnormU0
      mul := hmul
      ker0 := hker0
      ker := hker
      Cq_ker := hCq
      conj := hconj
      surj := hsurj }
  obtain ⟨a, b, Ua, Ub, W⟩ := NoE9Z4GenGrp.exists_wtCtx P D hES
  have hker' : ∀ x : ↥H, resBeta (rhoH h91) x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    have hkb : (resBeta (rhoH h91)).ker = (rhoH h91).ker := ker_resBeta (rhoH h91) hsplit
    constructor
    · intro hx
      have h1 : x ∈ (resBeta (rhoH h91)).ker := hx
      rw [hkb] at h1
      exact (rhoH_eq_one_iff h91 x).mp h1
    · intro hx
      have h1 : x ∈ (rhoH h91).ker := (rhoH_eq_one_iff h91 x).mpr hx
      rw [← hkb] at h1
      exact h1
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ conjClosure (VZ T M) H := le_conjClosure _ _
  obtain ⟨v, hvV, hvZ, hV⟩ := NoE9Z4MinGrp.exists_basis_of_card_four hZV S.hyp.rank_two
    S.card_Z P.z_mem P.z_ne
  have hone : cls 1 = 1 := (hker0 1 U0.one_mem).mpr (quasithinOmegaOneCenter T).one_mem
  have hinv : ∀ u ∈ conjClosure (VZ T M) H, cls u⁻¹ = (cls u)⁻¹ := by
    intro u hu
    have h1 := hmul u hu u⁻¹ ((conjClosure (VZ T M) H).inv_mem hu)
    rw [mul_inv_cancel, hone] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hvcls : cls v ≠ 1 := by
    intro hv1
    have hzU : z ∈ conjClosure (VZ T M) H := P.Z_le_U P.z_mem
    have hz1 : cls z = 1 := (hker0 z (hZU0 P.z_mem)).mpr P.z_mem
    let Ck : Subgroup G :=
      { carrier := {u | u ∈ conjClosure (VZ T M) H ∧ cls u = 1}
        one_mem' := ⟨one_mem _, hone⟩
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hmul a ha.1 b hb.1, ha.2, hb.2,
          mul_one]⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [hinv a ha.1, ha.2, inv_one]⟩ }
    have hVCk : ∀ w ∈ VZ T M, cls w = 1 := by
      intro w hw
      rcases hV w hw with rfl | rfl | rfl | rfl
      · exact hone
      · exact hz1
      · exact hv1
      · rw [hmul _ (hVU hvV) _ hzU, hv1, hz1, mul_one]
    have hUCk : conjClosure (VZ T M) H ≤ Ck := by
      refine conjClosure_le fun x hx w hw => ?_
      have hwU : w ∈ conjClosure (VZ T M) H := hVU hw
      refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hx) w).mp hwU, ?_⟩
      rw [show x * w * x⁻¹ = ((⟨x, hx⟩ : ↥H) : G) * w * ((⟨x, hx⟩ : ↥H) : G)⁻¹ from rfl,
        hconj ⟨x, hx⟩ w hwU, hVCk w hw, map_one]
    have hNT : Nontrivial ↥(kOf (rhoH h91)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hES.card_V]; norm_num)
    obtain ⟨k, hk⟩ := exists_ne (1 : ↥(kOf (rhoH h91)))
    obtain ⟨u, hu0, hu⟩ := hsurj k
    exact hk (hu ▸ (hUCk (hU0U hu0)).2)
  have hvC : v ∉ conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    fun hv => hvcls (hCq v hv)
  have hVb : ∃ v ∈ VZ T M, v ∉ quasithinOmegaOneCenter T ∧
      v ∉ conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      ∀ x ∈ VZ T M, x = 1 ∨ x = z ∨ x = v ∨ x = v * z := ⟨v, hvV, hvZ, hvC, hV⟩
  have hTV : ∀ t ∈ T, ∀ x ∈ VZ T M, t * x * t⁻¹ ∈ VZ T M := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ M (hTM ht)) x).mp hx
  obtain ⟨hTQ, hS1⟩ := NoE9Z4GenGrp.exists_rS1 P D hES T (VZ T M) rfl hker' hTH hQT hVU hZV
    hVb hTV
  obtain ⟨y, hyN, hyR, hnc, h3⟩ := NoE9Z4MinBridge.exists_y S
  have hyz : y * z * y⁻¹ ≠ z :=
    NoE9Z4MinGrp.y_moves_of_order_three (P.Z_sq P.z_mem) P.z_mem hvV hvZ hV
      (fun x hx => (Subgroup.mem_normalizer_iff.mp hyN x).mp hx) hnc h3
  exact NoE9Z4GenGrp.rpp_false P T (VZ T M) y (fun x hx x' hx' => W.comm_mem_Cq hx hx') hTH hQT
    hTQ hVU hZV hVb hS1 hyR (fun x hx => (Subgroup.mem_normalizer_iff.mp hyN x).mp hx) hyz

end CFSG.Quasithin

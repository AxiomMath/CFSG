module

public import CFSG.Quasithin.EmptyFaithful.S14612GC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinPair
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinDict
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinMod
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinRS
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinRpp
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinSetup
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinWt
import CFSG.Quasithin.EmptyFaithful.S1422Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417
open scoped commutatorElement

namespace NoE9Z4MinBridge

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem pairCtx_of_min (S : Setting146 G T M) (hH : IsHTM T M H)
    (hB : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
      conjClosure (VZ T M) H)
    (hC : conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) =
      quasithinOmegaOneCenter T) :
    ∃ z : G, NoE9Z4MinGrp.PairCtx (pCoreOf 2 H) (conjClosure (VZ T M) H)
      (quasithinOmegaOneCenter T) H z := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  obtain ⟨z, hz, hz1, hZe⟩ := NoE9Z4MinGrp.exists_involution_of_card_two S.card_Z
  have hUab := S.lemma_14_5_15_two hH
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ conjClosure (VZ T M) H := le_conjClosure _ _
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
    z_cent := fun g hg => (Subgroup.mem_centralizer_iff.mp (S.le_mcOf hH hg) z hz).symm
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
    ker_right := fun u hu hcomm =>
      hC.le ⟨hu, Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (commutatorElement_eq_one_iff_mul_comm.mp (hcomm x hx)).symm⟩ }

theorem inf_centralizer_eq_pCoreOf (S : Setting146 G T M) :
    T ⊓ Subgroup.centralizer (VZ T M : Set G) = pCoreOf 2 (yOfL22 T M ⊔ T) := by
  have hC := S.facts.centralizer_yT
  have hTsyl : IsSylowTwoOf T (yOfL22 T M ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow le_sup_right
  apply le_antisymm
  · rw [← hC]
    exact inf_le_inf_right _ le_sup_right
  · intro x hx
    refine ⟨pCoreOf_two_le_of_isSylowTwoOf hTsyl hx, ?_⟩
    rw [← hC] at hx
    exact hx.2

theorem exists_y (S : Setting146 G T M) :
    ∃ y : G, y ∈ Subgroup.normalizer (VZ T M : Set G) ∧
      y ∈ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) ∧
      ¬ (∀ x ∈ VZ T M, y * x = x * y) ∧ (∀ x ∈ VZ T M, y ^ 3 * x = x * y ^ 3) := by
  have hcard := S.facts.y_card
  have hne : ∃ σ ∈ autOn (yOfL22 T M) (VZ T M), σ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : autOn (yOfL22 T M) (VZ T M) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot] at hcard
    simp at hcard
  obtain ⟨σ, hσ, hσ1⟩ := hne
  obtain ⟨y, hyN, hyY, rfl⟩ := mem_autOn_iff_exists_conj.mp hσ
  refine ⟨y, hyN, ?_, ?_, ?_⟩
  · rw [inf_centralizer_eq_pCoreOf S]
    exact le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hyY)
  · intro hall
    apply hσ1
    refine A4.conjAct_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    exact (hall x hx).symm
  · have h3 : (⟨_, hσ⟩ : ↥(autOn (yOfL22 T M) (VZ T M))) ^ 3 = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have h4 : conjAct (VZ T M) ⟨y, hyN⟩ ^ 3 = 1 := congrArg Subtype.val h3
    have h5 : conjAct (VZ T M) ((⟨y, hyN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) ^ 3) = 1 := by
      rw [map_pow]
      exact h4
    have h6 := A4.conjAct_eq_one_iff.mp h5
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp h6 x hx).symm

end NoE9Z4MinBridge

theorem noE9Z4Min_of (h35 : Lemma1435) : NoE9Z4Min := by
  intro G _ _ T M S H PQ p hred _ hshape _ hU _ hB hC _
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  obtain ⟨-, -, -, hsplit, -, -, -⟩ := class_data_of_lemma1435 h35 S hred h91 h98
  have hES := e9z4Str_of_shape classAutShapeStmt h35 S hred hshape h98
  have hK : commV (resBeta (rhoH h91)).range = ⊤ := hES.commV_X
  obtain ⟨z, P⟩ := NoE9Z4MinBridge.pairCtx_of_min S hH hB hC
  obtain ⟨cls, hcls⟩ := exists_cls h91 hsplit hU hK
  have D := clsData_of h91 hsplit hU hK P hcls
  obtain ⟨a, b, Ua, Ub, W⟩ := NoE9Z4MinGrp.exists_wtCtx P D hES
  have hker : ∀ x : ↥H, resBeta (rhoH h91) x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
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
  have hVb : ∃ v ∈ VZ T M, v ∉ quasithinOmegaOneCenter T ∧
      ∀ x ∈ VZ T M, x = 1 ∨ x = z ∨ x = v ∨ x = v * z := ⟨v, hvV, hvZ, hV⟩
  have hTV : ∀ t ∈ T, ∀ x ∈ VZ T M, t * x * t⁻¹ ∈ VZ T M := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ M (hTM ht)) x).mp hx
  obtain ⟨hTQ, hS1⟩ := NoE9Z4MinGrp.exists_rS1 P D hES T (VZ T M) rfl hker hTH hQT hVU hZV
    hVb hTV
  obtain ⟨y, hyN, hyR, hnc, h3⟩ := NoE9Z4MinBridge.exists_y S
  have hyz : y * z * y⁻¹ ≠ z :=
    NoE9Z4MinGrp.y_moves_of_order_three (P.Z_sq P.z_mem) P.z_mem hvV hvZ hV
      (fun x hx => (Subgroup.mem_normalizer_iff.mp hyN x).mp hx) hnc h3
  exact NoE9Z4MinGrp.rpp_false P T (VZ T M) y (fun x hx x' hx' => W.comm_mem_Z hx hx') hTH hQT
    hTQ hVU hZV hVb hS1 hyR hyz

end CFSG.Quasithin

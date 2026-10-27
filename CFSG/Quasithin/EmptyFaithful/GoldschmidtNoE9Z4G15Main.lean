module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenPair
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenMain
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenDict
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenMod
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenRS
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenRpp
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4G15Quad
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4G15Aux
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinSetup
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinMain
public import CFSG.Quasithin.Background.F9Dual
public import CFSG.Quasithin.EmptyFaithful.S14612GB0a
public import CFSG.Quasithin.EmptyFaithful.S14612GB1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417
open scoped commutatorElement

namespace NoE9Z4G15Bridge

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem pairCtx_sub (S : Setting146 G T M) (hH : IsHTM T M H) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hZe : ∀ g ∈ quasithinOmegaOneCenter T, g = 1 ∨ g = z) {Q' : Subgroup G}
    (hUQ' : conjClosure (VZ T M) H ≤ Q') (hQ'Q : Q' ≤ pCoreOf 2 H)
    (hnorm : ∀ h ∈ H, ∀ x ∈ Q', h * x * h⁻¹ ∈ Q')
    (hB : Q' ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
      conjClosure (VZ T M) H) :
    NoE9Z4GenGrp.PairCtx Q' (conjClosure (VZ T M) H) (quasithinOmegaOneCenter T)
      (conjClosure (VZ T M) H ⊓ Subgroup.centralizer (Q' : Set G)) H z := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hUab := S.lemma_14_5_15_two hH
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ conjClosure (VZ T M) H := le_conjClosure _ _
  have hzcent : ∀ g ∈ H, g * z = z * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp (S.le_mcOf hH hg) z hz).symm
  exact
  { z_ne := hz1
    z_mem := hz
    Z_eq := hZe
    Z_le_U := hZV.trans hVU
    U_le_Q := hUQ'
    Q_le_H := hQ'Q.trans (pCoreOf_le 2 H)
    U_comm := fun u hu u' hu' =>
      congrArg Subtype.val (hUab.1.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩)
    U_sq := fun u hu => by
      have := isElemAbelian_pow_eq_one hUab hu
      rwa [pow_two] at this
    z_cent := hzcent
    normQ := hnorm
    normU := fun g hg u hu =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hg) u).mp hu
    pair_mem := fun u hu x hx => by
      have := h91.commutator_conjClosure_le u hu x (hQ'Q hx)
      rwa [commutatorElement_def]
    ker_left := fun x hx hcomm =>
      hB.le ⟨hx, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        commutatorElement_eq_one_iff_mul_comm.mp (hcomm u hu)⟩
    Z_le_Cq := fun c hc => ⟨(hZV.trans hVU) hc, Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rcases hZe c hc with rfl | rfl
      · simp
      · exact hzcent x (pCoreOf_le 2 H (hQ'Q hx))⟩
    Cq_le_U := inf_le_left
    Cq_cent := fun c hc x hx =>
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hc.2 x hx).symm
    ker_right := fun u hu hcomm =>
      ⟨hu, Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (commutatorElement_eq_one_iff_mul_comm.mp (hcomm x hx)).symm⟩ }

end NoE9Z4G15Bridge

theorem noE9Z4_caseB (h35 : Lemma1435) (h5 : Stage1461Five) {G : Type} [Group G] [Finite G]
    {T M H PQ : Subgroup G} {p : ℕ} (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p)
    (hB : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
      conjClosure (VZ T M) H)
    (hnA : ∃ u ∈ conjClosure (VZ T M) H, (∀ x ∈ H, ⁅u, x⁆ ∈ quasithinOmegaOneCenter T) ∧
      ∃ y ∈ pCoreOf 2 H, ⁅u, y⁆ ≠ 1) : False := by
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  obtain ⟨-, -, -, hsplit, hinf, -, -⟩ := class_data_of_lemma1435 h35 S hred h91 h98
  have hES := e9z4Str_of_shape classAutShapeStmt h35 S hred hshape h98
  have hK : commV (resBeta (rhoH h91)).range = ⊤ := hES.commV_X
  obtain ⟨cls, U0, hU0U, hZU0, hnormU0, hmul, hker0, hconj, hsurj, hcomm, hkerH⟩ :=
    NoE9Z4GenBridge.exists_cls hsplit hinf
  obtain ⟨z, hz, hz1, hZe⟩ := NoE9Z4MinGrp.exists_involution_of_card_two S.card_Z
  have hUab := S.lemma_14_5_15_two hH
  obtain ⟨u₁, hu₁U, hu₁H, y₁, hy₁Q, hy₁ne⟩ := hnA
  have hUQ : conjClosure (VZ T M) H ≤ pCoreOf 2 H := h91.conjClosure_Vp_le_pCoreOf
  have P := NoE9Z4G15Bridge.pairCtx_sub S hH hz hz1 hZe hUQ le_rfl
    (fun h hh x hx => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) x).mp hx) hB
  have hCq : ∀ c ∈ conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G),
      cls c = 1 :=
    NoE9Z4GenBridge.cls_cq_ker P (fun _ hinv => hES.irreducible hinv) hK hU0U hmul hker0 hconj
      hcomm (S.not_uK_le_centralizer_pCoreOf h5 hred)
  have hone : cls 1 = 1 := (hker0 1 U0.one_mem).mpr (quasithinOmegaOneCenter T).one_mem
  have hinv : ∀ u ∈ conjClosure (VZ T M) H, cls u⁻¹ = (cls u)⁻¹ := by
    intro u hu
    have h1 := hmul u hu u⁻¹ ((conjClosure (VZ T M) H).inv_mem hu)
    rw [mul_inv_cancel, hone] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hu₁Z : u₁ ∉ quasithinOmegaOneCenter T := fun h => hy₁ne (P.pair_one_of_mem_Z h hy₁Q)
  have hcls1 : cls u₁ = 1 := by
    have hfixk : ∀ x : ↥H, resBeta (rhoH h91) x (cls u₁) = cls u₁ := by
      intro x
      have hxu : (x : G) * u₁⁻¹ * (x : G)⁻¹ ∈ conjClosure (VZ T M) H :=
        P.normU x x.2 u₁⁻¹ ((conjClosure (VZ T M) H).inv_mem hu₁U)
      have hcomm1 : ⁅u₁, (x : G)⁆ ∈ quasithinOmegaOneCenter T := hu₁H x x.2
      have e : ⁅u₁, (x : G)⁆ = u₁ * ((x : G) * u₁⁻¹ * (x : G)⁻¹) := by
        simp only [commutatorElement_def]
        group
      have hc : cls ⁅u₁, (x : G)⁆ = 1 := (hker0 _ (hZU0 hcomm1)).mpr hcomm1
      rw [e, hmul u₁ hu₁U _ hxu, hconj x u₁⁻¹ ((conjClosure (VZ T M) H).inv_mem hu₁U),
        hinv u₁ hu₁U, map_inv] at hc
      exact (mul_inv_eq_one.mp hc).symm
    have hF : ((cls u₁ : ↥(kOf (rhoH h91))) : UMod h91) ∈ fixV (rhoH h91).range := by
      rintro _ ⟨x, rfl⟩
      have h1 := congrArg Subtype.val (hfixk x)
      simpa [resBeta_apply] using h1
    have hmem : ((cls u₁ : ↥(kOf (rhoH h91))) : UMod h91) ∈
        kOf (rhoH h91) ⊓ fixV (rhoH h91).range := ⟨(cls u₁).2, hF⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hu₁U0 : u₁ ∉ U0 := fun h => hu₁Z ((hker0 u₁ h).mp hcls1)
  have hUKZ : uK T M H ⊔ quasithinOmegaOneCenter T ≤ U0 :=
    sup_le (Subgroup.commutator_le.2 fun u hu x hx => hcomm u hu x hx) hZU0
  have hidx := NoE9Z4GenGrp.index_two_cosets hUKZ (S.relIndex_uK_sup_Z_le_two hH) hu₁U hu₁U0
  have hidx1 : ∀ u ∈ conjClosure (VZ T M) H, u ∈ U0 ∨ u₁⁻¹ * u ∈ U0 := fun u hu => by
    by_cases hu0 : u ∈ U0
    · exact Or.inl hu0
    · exact Or.inr (hidx u₁ hu₁U u hu hu₁U0 hu0)
  obtain ⟨f, hf1, hf2⟩ := NoE9Z4GenGrp.exists_hom_of_index_two (U := conjClosure (VZ T M) H)
    (U0 := U0) (Z := quasithinOmegaOneCenter T) hz (P.Z_sq hz) hidx
  have hfker : ∀ u : ↥(conjClosure (VZ T M) H),
      (∀ x ∈ pCoreOf 2 H, x * (u : G) = (u : G) * x) → f u = 1 := by
    intro u hu
    by_cases hu0 : (u : G) ∈ U0
    · exact hf1 u hu0
    · exfalso
      have hcu : cls u = 1 := hCq u ⟨u.2, Subgroup.mem_centralizer_iff.mpr hu⟩
      have hc0 : u₁⁻¹ * (u : G) ∈ U0 := (hidx1 u u.2).resolve_left hu0
      have hcz : u₁⁻¹ * (u : G) ∈ quasithinOmegaOneCenter T := by
        refine (hker0 _ hc0).mp ?_
        rw [hmul _ ((conjClosure (VZ T M) H).inv_mem hu₁U) _ u.2, hinv u₁ hu₁U, hcls1, hcu,
          inv_one, one_mul]
      apply hy₁ne
      have e : u₁ = (u : G) * (u₁⁻¹ * (u : G))⁻¹ := by group
      rw [e, P.pair_mul_Cq u.2 (P.Z_le_Cq ((quasithinOmegaOneCenter T).inv_mem hcz)) hy₁Q]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hu y₁ hy₁Q).symm
  obtain ⟨e, heQ, hfe⟩ := h91.F97_surj hUab f hfker
  have he0 : ∀ u ∈ U0, ⁅u, e⁆ = 1 := by
    intro u hu
    have h1 := hfe ⟨u, hU0U hu⟩
    rw [hf1 ⟨u, hU0U hu⟩ hu] at h1
    have h2 : e * u * e⁻¹ * u⁻¹ = 1 := h1.symm
    have h3 : e * u = u * e := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)
    exact commutatorElement_eq_one_iff_mul_comm.mpr h3.symm
  have hez : ∀ u ∈ conjClosure (VZ T M) H, u ∉ U0 → e * u * e⁻¹ * u⁻¹ = z := by
    intro u hu hn
    have h1 := hfe ⟨u, hu⟩
    rw [hf2 ⟨u, hu⟩ hn] at h1
    exact h1.symm
  have hzz : z * z = 1 := P.Z_sq hz
  have hnU0e : ∀ u ∈ conjClosure (VZ T M) H, u ∉ U0 → ⁅u, e⁆ = z := by
    intro u hu hn
    have h1 : ⁅e, u⁆ = z := by
      rw [commutatorElement_def]
      exact hez u hu hn
    rw [← commutatorElement_inv, h1]
    exact inv_eq_of_mul_eq_one_right hzz
  have he_fix : ∀ h ∈ H, e⁻¹ * (h * e * h⁻¹) ∈ conjClosure (VZ T M) H := by
    intro h hh
    refine P.pair_ext heQ (P.normQ h hh e heQ) fun u hu => ?_
    rw [P.pair_conj_inv hh hu heQ]
    have hu' : h⁻¹ * u * h ∈ conjClosure (VZ T M) H := by
      simpa using P.normU h⁻¹ (inv_mem hh) u hu
    by_cases hu0 : u ∈ U0
    · have hu0' : h⁻¹ * u * h ∈ U0 := by simpa using hnormU0 h⁻¹ (inv_mem hh) u hu0
      rw [he0 u hu0, he0 _ hu0']
    · have hu0' : h⁻¹ * u * h ∉ U0 := fun hm => hu0 (by simpa [mul_assoc] using hnormU0 h hh _ hm)
      rw [hnU0e u hu hu0, hnU0e _ hu' hu0']
  let Qe : Subgroup G := pCoreOf 2 H ⊓ Subgroup.centralizer ({u₁} : Set G)
  have hmemQe : ∀ x, x ∈ Qe ↔ x ∈ pCoreOf 2 H ∧ ⁅u₁, x⁆ = 1 := fun x => by
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, commutatorElement_eq_one_iff_mul_comm.mpr (h u₁ rfl)⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun g hg => by
        rw [Set.mem_singleton_iff.mp hg]
        exact commutatorElement_eq_one_iff_mul_comm.mp h⟩
  have hQeQ : Qe ≤ pCoreOf 2 H := inf_le_left
  have hUQe : conjClosure (VZ T M) H ≤ Qe := fun u hu =>
    (hmemQe u).mpr ⟨hUQ hu, P.pair_U_U hu₁U hu⟩
  have hdec : ∀ x ∈ pCoreOf 2 H, x ∈ Qe ∨ x * e⁻¹ ∈ Qe := by
    intro x hx
    rcases hZe _ (P.pair_mem u₁ hu₁U x hx) with h | h
    · exact Or.inl ((hmemQe x).mpr ⟨hx, h⟩)
    · right
      have hue : ⁅u₁, e⁆ = z := hnU0e u₁ hu₁U hu₁U0
      refine (hmemQe _).mpr ⟨(pCoreOf 2 H).mul_mem hx ((pCoreOf 2 H).inv_mem heQ), ?_⟩
      rw [P.pair_mul_right hu₁U hx ((pCoreOf 2 H).inv_mem heQ), P.pair_inv_right hu₁U heQ, h,
        hue]
      exact mul_inv_cancel z
  have hnormQe : ∀ h ∈ H, ∀ x ∈ Qe, h * x * h⁻¹ ∈ Qe := by
    intro h hh x hx
    obtain ⟨hxQ, hx1⟩ := (hmemQe x).mp hx
    refine (hmemQe _).mpr ⟨P.normQ h hh x hxQ, ?_⟩
    have hh1 : ⁅h, u₁⁆ ∈ quasithinOmegaOneCenter T := by
      have := (quasithinOmegaOneCenter T).inv_mem (hu₁H h hh)
      rwa [commutatorElement_inv] at this
    rw [P.pair_conj_inv hh hu₁U hxQ, P.pair_conj_inv_triv hh hu₁U hh1 hxQ]
    exact hx1
  have hBe : Qe ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
      conjClosure (VZ T M) H := by
    apply le_antisymm
    · intro x hx
      rw [← hB]
      exact ⟨hx.1.1, hx.2⟩
    · intro u hu
      exact ⟨hUQe hu, Subgroup.mem_centralizer_iff.mpr fun w hw => P.U_comm w hw u hu⟩
  have Pe := NoE9Z4G15Bridge.pairCtx_sub S hH hz hz1 hZe hUQe hQeQ hnormQe hBe
  have hUKe : ⁅conjClosure (VZ T M) H, H⁆ ≤ Subgroup.centralizer (Qe : Set G) → False := by
    intro hle
    refine S.not_uK_le_centralizer_pCoreOf h5 hred fun w hw => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hw0 : w ∈ U0 := hUKZ (Subgroup.mem_sup_left hw)
    have hwc := Subgroup.mem_centralizer_iff.mp (hle hw)
    rcases hdec x hx with hx0 | hx0
    · exact hwc x hx0
    · have h1 : (x * e⁻¹) * w = w * (x * e⁻¹) := hwc _ hx0
      have h2 : ⁅w, e⁆ = 1 := he0 w hw0
      have h3 : w * e = e * w := commutatorElement_eq_one_iff_mul_comm.mp h2
      calc x * w = (x * e⁻¹) * (e * w) := by group
        _ = (x * e⁻¹) * (w * e) := by rw [h3]
        _ = ((x * e⁻¹) * w) * e := by group
        _ = (w * (x * e⁻¹)) * e := by rw [h1]
        _ = w * x := by group
  have hCqe : ∀ c ∈ conjClosure (VZ T M) H ⊓ Subgroup.centralizer (Qe : Set G), cls c = 1 :=
    NoE9Z4GenBridge.cls_cq_ker Pe (fun _ hinv => hES.irreducible hinv) hK hU0U hmul hker0 hconj
      hcomm hUKe
  have hkerE : ∀ u ∈ conjClosure (VZ T M) H, cls u = 1 →
      u ∈ conjClosure (VZ T M) H ⊓ Subgroup.centralizer (Qe : Set G) := by
    intro u hu hcu
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    obtain ⟨hxQ, hx1⟩ := (hmemQe x).mp hx
    rcases hidx1 u hu with hu0 | hc0
    · have huZ := (hker0 u hu0).mp hcu
      exact (commutatorElement_eq_one_iff_mul_comm.mp (P.pair_one_of_mem_Z huZ hxQ)).symm
    · have hcz : u₁⁻¹ * u ∈ quasithinOmegaOneCenter T := by
        refine (hker0 _ hc0).mp ?_
        rw [hmul _ ((conjClosure (VZ T M) H).inv_mem hu₁U) _ hu, hinv u₁ hu₁U, hcls1, hcu,
          inv_one, one_mul]
      have e : u = u₁ * (u₁⁻¹ * u) := by group
      have h1 : ⁅u, x⁆ = 1 := by
        rw [e, P.pair_mul_left hu₁U (P.Z_le_U hcz) hxQ, hx1, P.pair_one_of_mem_Z hcz hxQ,
          mul_one]
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have De : NoE9Z4GenGrp.ClsData Pe U0 (resBeta (rhoH h91)) cls :=
    { U0_le := hU0U
      Z_le_U0 := hZU0
      normU0 := hnormU0
      mul := hmul
      ker0 := hker0
      ker := hkerE
      Cq_ker := hCqe
      conj := hconj
      surj := hsurj }
  obtain ⟨a, b, Ua, Ub, W, hUaU0, hUbU0, t, ht1, ht2, ht3, htUa, htUb⟩ :=
    NoE9Z4GenGrp.exists_wtCtx_t Pe De hES
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
  have D15 : NoE9Z4GenGrp.Data15 P Pe W e (t : G) :=
    { Qe_le := hQeQ
      e_mem := heQ
      e_fix := he_fix
      e_cent_a := fun u hu => he0 u (hUaU0 hu)
      e_cent_b := fun u hu => he0 u (hUbU0 hu)
      t_mem := t.2
      tt_mem := (hker' (t * t)).mp ht1
      ta_mem := (hker' _).mp ht2
      tb_mem := (hker' _).mp ht3
      tUa := htUa
      tUb := htUb }
  have hTe : ∀ x ∈ pCoreOf 2 H, ∀ y ∈ pCoreOf 2 H,
      NoE9Z4GenGrp.PairCtx.T x y e = 1 := by
    intro x hx y hy
    have hee : NoE9Z4GenGrp.PairCtx.T e e e = 1 := NoE9Z4GenGrp.PairCtx.T_self e e
    rcases hdec x hx with hx0 | hx0 <;> rcases hdec y hy with hy0 | hy0
    · exact (D15.T_xye_xee hx0 hy0).1
    · obtain ⟨y₀, hy₀, rfl⟩ : ∃ y₀ ∈ Qe, y = y₀ * e := ⟨y * e⁻¹, hy0, by group⟩
      have hy₀Q := hQeQ hy₀
      rw [P.T_mul_mid hx hy₀Q heQ heQ, (D15.T_xye_xee hx0 hy₀).1, (D15.T_xye_xee hx0 hy₀).2,
        mul_one]
    · obtain ⟨x₀, hx₀, rfl⟩ : ∃ x₀ ∈ Qe, x = x₀ * e := ⟨x * e⁻¹, hx0, by group⟩
      have hx₀Q := hQeQ hx₀
      rw [P.T_mul_left hx₀Q heQ hy heQ, (D15.T_xye_xee hx₀ hy0).1,
        P.T_swap hy heQ heQ, (D15.T_xye_xee hy0 hy0).2, mul_one]
    · obtain ⟨x₀, hx₀, rfl⟩ : ∃ x₀ ∈ Qe, x = x₀ * e := ⟨x * e⁻¹, hx0, by group⟩
      obtain ⟨y₀, hy₀, rfl⟩ : ∃ y₀ ∈ Qe, y = y₀ * e := ⟨y * e⁻¹, hy0, by group⟩
      have hx₀Q := hQeQ hx₀
      have hy₀Q := hQeQ hy₀
      rw [P.T_mul_left hx₀Q heQ ((pCoreOf 2 H).mul_mem hy₀Q heQ) heQ,
        P.T_mul_mid hx₀Q hy₀Q heQ heQ, P.T_mul_mid heQ hy₀Q heQ heQ, (D15.T_xye_xee hx₀ hy₀).1,
        (D15.T_xye_xee hx₀ hy₀).2, hee, P.T_swap hy₀Q heQ heQ,
        (D15.T_xye_xee hy₀ hy₀).2]
      simp
  have hQQ : ⁅pCoreOf 2 H, pCoreOf 2 H⁆ ≤ U0 := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    have hw : ⁅x, y⁆ ∈ conjClosure (VZ T M) H := P.comm_mem_U hx hy
    by_contra hn
    have h1 := hez _ hw hn
    have h2 : ⁅⁅x, y⁆, e⁆ = 1 := hTe x hx y hy
    have h3 : ⁅x, y⁆ * e = e * ⁅x, y⁆ := commutatorElement_eq_one_iff_mul_comm.mp h2
    apply hz1
    rw [← h1]
    calc e * ⁅x, y⁆ * e⁻¹ * ⁅x, y⁆⁻¹ = (⁅x, y⁆ * e) * e⁻¹ * ⁅x, y⁆⁻¹ := by rw [h3]
      _ = 1 := by group
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ conjClosure (VZ T M) H := le_conjClosure _ _
  obtain ⟨v, hvV, hvZ, hV⟩ := NoE9Z4MinGrp.exists_basis_of_card_four hZV S.hyp.rank_two
    S.card_Z P.z_mem P.z_ne
  have hzU : z ∈ conjClosure (VZ T M) H := P.Z_le_U hz
  have hz1' : cls z = 1 := (hker0 z (hZU0 hz)).mpr hz
  have hvcls : cls v ≠ 1 := by
    intro hv1
    let Ck : Subgroup G :=
      { carrier := {u | u ∈ conjClosure (VZ T M) H ∧ cls u = 1}
        one_mem' := ⟨one_mem _, hone⟩
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
          rw [hmul a ha.1 b hb.1, ha.2, hb.2, mul_one]⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [hinv a ha.1, ha.2, inv_one]⟩ }
    have hVCk : ∀ w ∈ VZ T M, cls w = 1 := by
      intro w hw
      rcases hV w hw with rfl | rfl | rfl | rfl
      · exact hone
      · exact hz1'
      · exact hv1
      · rw [hmul _ (hVU hvV) _ hzU, hv1, hz1', mul_one]
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
  have hκ : ∀ v' ∈ VZ T M,
      v' ∉ conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) → cls v' ≠ 1 := by
    intro v' hv' hvC'
    rcases hV v' hv' with h | h | h | h
    · exact absurd (h ▸ one_mem _) hvC'
    · exact absurd (h ▸ P.Z_le_Cq hz) hvC'
    · rw [h]; exact hvcls
    · rw [h, hmul v (hVU hvV) z hzU, hz1', mul_one]
      exact hvcls
  have D0 : NoE9Z4GenGrp.ClsBase P U0 (resBeta (rhoH h91)) cls :=
    { U0_le := hU0U
      Z_le_U0 := hZU0
      mul := hmul
      ker0 := hker0
      Cq_ker := hCq
      conj := hconj
      surj := hsurj }
  have hTV : ∀ t ∈ T, ∀ x ∈ VZ T M, t * x * t⁻¹ ∈ VZ T M := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ M (hTM ht)) x).mp hx
  obtain ⟨hTQ, hS1⟩ := NoE9Z4GenGrp.exists_rS1_base P D0 hES T (VZ T M) rfl hker' hTH hQT hVU
    hZV hκ hVb hTV
  obtain ⟨y, hyN, hyR, hnc, h3⟩ := NoE9Z4MinBridge.exists_y S
  have hyz : y * z * y⁻¹ ≠ z :=
    NoE9Z4MinGrp.y_moves_of_order_three (P.Z_sq P.z_mem) P.z_mem hvV hvZ hV
      (fun x hx => (Subgroup.mem_normalizer_iff.mp hyN x).mp hx) hnc h3
  have hv0 : v ∉ U0 := by
    intro hv0
    have hVU0 : ∀ w ∈ VZ T M, w ∈ U0 := by
      intro w hw
      rcases hV w hw with rfl | rfl | rfl | rfl
      · exact U0.one_mem
      · exact hZU0 hz
      · exact hv0
      · exact U0.mul_mem hv0 (hZU0 hz)
    have hUU0 : conjClosure (VZ T M) H ≤ U0 :=
      conjClosure_le fun x hx w hw => hnormU0 x hx w (hVU0 w hw)
    exact hu₁U0 (hUU0 hu₁U)
  refine NoE9Z4GenGrp.rpp_false_of_not_mem P T (VZ T M) y (fun w hw hwZ hwQ => ?_) hTH hQT hTQ
    hVU hZV hVb hS1 hyR (fun x hx => (Subgroup.mem_normalizer_iff.mp hyN x).mp hx) hyz
  have hwU0 : w ∈ U0 := hQQ hwQ
  rcases hV w hw with rfl | rfl | rfl | rfl
  · exact hwZ (Subgroup.one_mem _)
  · exact hwZ hz
  · exact hv0 hwU0
  · exact hv0 (by
      have := U0.mul_mem hwU0 (U0.inv_mem (hZU0 hz))
      simpa using this)

end CFSG.Quasithin

module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Simple
import CFSG.RankThree.GF2n.Smith81.Sec220TvLemmas
import CFSG.RankThree.GF2n.Smith81.OrthE1Small
import CFSG.LargeExtraspecial.DWFldLinear
public import CFSG.RankThree.GF2n.Smith81.OrthE2Layer

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section GenericLayer

variable {A : Type} [Group A] [Finite A]

theorem layer_map_auto_eq (α : A ≃* A) : (CFSG.layer A).map α.toMonoidHom = CFSG.layer A :=
  (Subgroup.characteristic_iff_map_eq.mp CFSG.LocalCores.layer_characteristic) α

theorem sup_eq_of_layer (N X Y L : Subgroup A) (hN : N.Normal) (hXN : X ≤ N) (hYN : Y ≤ N)
    (hLXY : L ≤ X ⊔ Y) (hX : (X.subgroupOf N).Normal) (hY : (Y.subgroupOf N).Normal)
    (hXl : CFSG.layer ↥(X.subgroupOf N) = ⊤) (hYl : CFSG.layer ↥(Y.subgroupOf N) = ⊤)
    (hC : ∀ n ∈ N, (∀ x ∈ X, ⁅n, x⁆ = 1) → n ∈ Y)
    (hcent : Subgroup.centralizer (N : Set A) = ⊥) (𝒜 : Set (A ≃* A))
    (hgen : N ≤ ⨆ α ∈ 𝒜, L.map α.toMonoidHom) : N = X ⊔ Y := by
  have hNl : (CFSG.layer ↥N).map N.subtype ≤ CFSG.layer A :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.L102.map_layer_le_layer_of_normal (W := N)
  have hXl' : X.subgroupOf N ≤ CFSG.layer ↥N := by
    have h := CFSG.GH74.GLS.Stage2.Bender.Thm2.L102.map_layer_le_layer_of_normal
      (A := ↥N) (W := X.subgroupOf N)
    rw [hXl] at h
    intro z hz
    exact h ⟨⟨z, hz⟩, Subgroup.mem_top _, rfl⟩
  have hYl' : Y.subgroupOf N ≤ CFSG.layer ↥N := by
    have h := CFSG.GH74.GLS.Stage2.Bender.Thm2.L102.map_layer_le_layer_of_normal
      (A := ↥N) (W := Y.subgroupOf N)
    rw [hYl] at h
    intro z hz
    exact h ⟨⟨z, hz⟩, Subgroup.mem_top _, rfl⟩
  have hXle : X ≤ CFSG.layer A := by
    intro x hx
    have hxN : x ∈ N := hXN hx
    exact hNl ⟨⟨x, hxN⟩, hXl' (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hYle : Y ≤ CFSG.layer A := by
    intro y hy
    have hyN : y ∈ N := hYN hy
    exact hNl ⟨⟨y, hyN⟩, hYl' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hXsub : X.IsSubnormal := Subgroup.IsSubnormal.step X N hXN hN.isSubnormal hX
  have hlayer_le : CFSG.layer A ≤ X ⊔ Y := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun K hK => ?_
    have hKN : K ≤ N := by
      rcases CFSG.LocalCores.component_normal_subgroup hK hN with h | h
      · exact h
      · have hK' : K ≤ Subgroup.centralizer (N : Set A) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
        rw [hcent] at hK'
        exact hK'.trans bot_le
    rcases CFSG.LocalCores.component_subnormal_subgroup hK hXsub with h | h
    · exact h.trans le_sup_left
    · intro k hk
      have hkY : k ∈ Y := hC k (hKN hk) fun x hx => by
        have hmem : ⁅k, x⁆ ∈ ⁅K, X⁆ := Subgroup.commutator_mem_commutator hk hx
        rw [h] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact (le_sup_right : Y ≤ X ⊔ Y) hkY
  have hNle : N ≤ CFSG.layer A := by
    refine hgen.trans (iSup₂_le fun α _ => ?_)
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l ∈ CFSG.layer A := (sup_le hXle hYle) (hLXY hl)
    rw [← layer_map_auto_eq α]
    exact ⟨l, hl', rfl⟩
  exact le_antisymm (hNle.trans hlayer_le) (sup_le hXN hYN)

end GenericLayer

theorem layer_eq_top_of_isOmegaPlus_two {q k : ℕ} (hq : 4 ≤ q) (hk : q = 2 ^ k) {X : Type}
    [Group X] (h : IsOmegaPlus 2 q X) : layer X = ⊤ := by
  obtain ⟨K, _, _, hK, ⟨eB⟩⟩ := h
  haveI : CharP K 2 := charP_two_of_natCard_pow_two (hK.trans hk)
  have hK4 : 4 ≤ Nat.card K := hK ▸ hq
  obtain ⟨e4⟩ := statedOmega_plus_four_nonempty_equiv K hK4
  have hSL : layer ↥(StatedSL 2 K) = ⊤ :=
    CFSG.WholeGroup.layer_eq_top_of_isQuasisimple (statedSL_quasisimple_of_card 2 K le_rfl hK4)
  exact layer_eq_top_of_mulEquiv (eB.trans e4).symm (layer_prod_eq_top hSL hSL)

theorem layer_eq_top_of_isOmegaMinus_two {q k : ℕ} (hq : 4 ≤ q) (hk : q = 2 ^ k) {X : Type}
    [Group X] (h : IsOmegaMinus 2 q X) : layer X = ⊤ := by
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨eB⟩⟩ := h
  haveI : CharP K 2 := charP_two_of_natCard_pow_two (hK.trans hk)
  exact layer_eq_top_of_mulEquiv eB.symm
    (CFSG.WholeGroup.layer_eq_top_of_isQuasisimple
      (statedOmega_minus_quasisimple_of_two_le K (le_refl 2) hirr))

section Ysub

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}

theorem Q_conj_mem_of (hc : Ctx M Q Z B) {m q : G} (hm : m ∈ M) (hq : q ∈ Q) :
    m * q * m⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) q).mp hq

@[expose] def thY (hc : Ctx M Q Z B) (t : G) : Subgroup G where
  carrier := {y | y ∈ Lgen M (LB M Q B) ∧ ∀ x ∈ E1Xpre M Q B t, ⁅y, x⁆ ∈ Q}
  one_mem' := ⟨one_mem _, fun x _ => by simp [commutatorElement_def]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx => ?_⟩
    have hid : ⁅a * b, x⁆ = (a * ⁅b, x⁆ * a⁻¹) * ⁅a, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [hid]
    exact Q.mul_mem (Q_conj_mem_of hc ((Lgen_le_H0 hc ha).1) (hb' x hx)) (ha' x hx)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx => ?_⟩
    have hid : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [hid]
    exact Q_conj_mem_of hc (inv_mem ((Lgen_le_H0 hc ha).1)) (Q.inv_mem (ha' x hx))

theorem mem_thY (hc : Ctx M Q Z B) {y : G} :
    y ∈ thY hc t ↔ y ∈ Lgen M (LB M Q B) ∧ ∀ x ∈ E1Xpre M Q B t, ⁅y, x⁆ ∈ Q := Iff.rfl

theorem thY_le_Lgen (hc : Ctx M Q Z B) : thY hc t ≤ Lgen M (LB M Q B) := fun _ hy => hy.1

theorem Q_le_thY (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) : Q ≤ thY hc t := by
  intro q hq
  refine ⟨(le_sup_left.trans (le_Lgen_self M (LB M Q B))) hq, fun x hx => ?_⟩
  have hxM : x ∈ M := (Lgen_le_H0 hc (E1Xpre_le_Lgen hc ht hx)).1
  have hid : ⁅q, x⁆ = q * (x * q⁻¹ * x⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [hid]
  exact Q.mul_mem hq (Q_conj_mem_of hc hxM (Q.inv_mem hq))

theorem thY_normal (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B)
    (hP1 : ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ E1Xpre M Q B t, s * x * s⁻¹ ∈ E1Xpre M Q B t) :
    ∀ s ∈ Lgen M (LB M Q B), ∀ y ∈ thY hc t, s * y * s⁻¹ ∈ thY hc t := by
  intro s hs y hy
  rw [mem_thY] at hy ⊢
  refine ⟨mul_mem (mul_mem hs hy.1) (inv_mem hs), fun x hx => ?_⟩
  have hx' : s⁻¹ * x * s⁻¹⁻¹ ∈ E1Xpre M Q B t := hP1 s⁻¹ (inv_mem hs) x hx
  have hid : ⁅s * y * s⁻¹, x⁆ = s * ⁅y, s⁻¹ * x * s⁻¹⁻¹⁆ * s⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [hid]
  exact Q_conj_mem_of hc ((Lgen_le_H0 hc hs).1) (hy.2 _ hx')

theorem phi_comm_iff_mem (AM : ActionModel M Q Z) {g h : G} (hg : g ∈ H0 M Z)
    (hh : h ∈ H0 M Z) : AM.φ ⟨g, hg⟩ * AM.φ ⟨h, hh⟩ = AM.φ ⟨h, hh⟩ * AM.φ ⟨g, hg⟩ ↔
      ⁅g, h⁆ ∈ Q := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  constructor
  · intro h1; exact (AM.φ_ker _).mp h1
  · intro h1; exact (AM.φ_ker _).mpr h1

end Ysub

theorem center_statedSL_two_bot (K : Type) [Field K] [CharP K 2] :
    Subgroup.center ↥(StatedSL 2 K) = ⊥ := by
  rw [CFSG.GH74.L5U5.center_statedSL_eq 2, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := CFSG.LargeExtraspecial.DW.mem_statedScalars_iff.mp hg
  have hdet : Matrix.det ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp g.2
  rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (c + 1) ^ 2 = 0 := by linear_combination hdet + (c + 1) * h2
  have hc1' : c + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
  have hc1 : c = 1 := by linear_combination hc1' - h2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Units.ext
  rw [hc, hc1]
  simp

section Phi

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}

theorem E1Xpre_le_Rt (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) :
    E1Xpre M Q B t ≤ Rt M (LB M Q B) t := by
  refine sup_le (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (hc.Q_le_Rt ht)
  rw [commutatorElement_def]
  exact (Rt M (LB M Q B) t).mul_mem
    ((Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem ha hb)
      ((Rt M (LB M Q B) t).inv_mem ha)) ((Rt M (LB M Q B) t).inv_mem hb)

theorem comm_of_beta {K E : Type*} [Field K] [AddCommGroup E] [Module K E] (β : E →ₗ[K] E)
    (f ν : E ≃ₗ[K] E) (c : K) (hν : ∀ e, ν e = e + c • β e) (hf : ∀ e, β (f e) = f (β e)) :
    ν * f = f * ν := by
  refine LinearEquiv.ext fun e => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hν (f e), hν e, map_add, map_smul, hf]

theorem Nt_le_thY (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) (hNL : Nt M (LB M Q B) t ≤ LB M Q B)
    (AM : ActionModel M Q Z) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hβr : ∀ r : ↥(H0 M Z), (r : G) ∈ Rt M (LB M Q B) t → ∀ e, AM.φ r (β e) = β (AM.φ r e))
    (hβn : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t → ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e) :
    Nt M (LB M Q B) t ≤ thY hc t := by
  intro n hn
  have hnlg : n ∈ Lgen M (LB M Q B) := le_Lgen_self M (LB M Q B) (hNL hn)
  have hn0 : n ∈ H0 M Z := Lgen_le_H0 hc hnlg
  refine ⟨hnlg, fun x hx => ?_⟩
  have hx0 : x ∈ H0 M Z := Lgen_le_H0 hc (E1Xpre_le_Lgen hc ht hx)
  have hxR : x ∈ Rt M (LB M Q B) t := E1Xpre_le_Rt hc ht hx
  obtain ⟨c, hc'⟩ := hβn ⟨n, hn0⟩ hn
  have hcomm : AM.φ ⟨n, hn0⟩ * AM.φ ⟨x, hx0⟩ = AM.φ ⟨x, hx0⟩ * AM.φ ⟨n, hn0⟩ :=
    comm_of_beta β _ _ c hc' (fun e => (hβr ⟨x, hx0⟩ hxR e).symm)
  exact (phi_comm_iff_mem AM hn0 hx0).mp hcomm

theorem thY_phi_mem_cent (hc : Ctx M Q Z B) (AM : ActionModel M Q Z) {y : G}
    (hy : y ∈ thY hc t) :
    AM.φ ⟨y, Lgen_le_H0 hc hy.1⟩ ∈ AM.S.Cent ((AM.actImage (E1Xpre M Q B t) : Subgroup _) :
      Set (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E)) := by
  refine Subgroup.mem_inf.mpr ⟨fun e => AM.φ_Qf _ e, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hy0 : y ∈ H0 M Z := Lgen_le_H0 hc hy.1
  exact ((phi_comm_iff_mem AM hy0 x.2).mpr (hy.2 x.1 (Subgroup.mem_subgroupOf.mp hx))).symm

theorem card_actImage_mul (AM : ActionModel M Q Z) {N' : Subgroup G} (hN'H : N' ≤ H0 M Z)
    (hQN : Q ≤ N') : Nat.card (AM.actImage N') * Nat.card Q = Nat.card N' := by
  have hQH : Q ≤ H0 M Z := hQN.trans hN'H
  let N0 : Subgroup ↥(H0 M Z) := N'.subgroupOf (H0 M Z)
  let f : ↥N0 →* (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) := AM.φ.comp N0.subtype
  have hrange : f.range = AM.actImage N' := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, Subgroup.mem_subgroupOf.mp x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mpr hx⟩, rfl⟩
  have hQH' : (Q.subgroupOf (H0 M Z)) ≤ N0 := fun x hx => Subgroup.mem_subgroupOf.mpr
    (hQN (Subgroup.mem_subgroupOf.mp hx))
  have hker : f.ker = (Q.subgroupOf (H0 M Z)).subgroupOf N0 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (AM.φ_ker x.1).trans Iff.rfl
  have hcardN0 : Nat.card N0 = Nat.card N' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN'H).toEquiv
  have hcardK : Nat.card f.ker = Nat.card Q := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH').toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (↥N0 ⧸ f.ker) = Nat.card (AM.actImage N') := by
    rw [← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [← hcardN0, h1, h2, hcardK]

theorem card_actImage_nt (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) (hH : E1Hyp M Q Z B t)
    (hNL : Nt M (LB M Q B) t ≤ LB M Q B) (AM : ActionModel M Q Z) :
    Nat.card (AM.actImage (Nt M (LB M Q B) t)) = Nat.card Z := by
  have hNH : Nt M (LB M Q B) t ≤ H0 M Z := fun n hn =>
    Lgen_le_H0 hc (le_Lgen_self M (LB M Q B) (hNL hn))
  have h := card_actImage_mul AM hNH (smith23E1_Q_le_Nt hc ht)
  rw [hH.case.2.1] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.trans (mul_comm _ _))

theorem Vsp_isTS (AM : ActionModel M Q Z) {V : Submodule AM.K AM.M₀.E}
    {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E} (hβ : BetaProps AM.S V β)
    (hβq : ∀ c : AM.K, ∃ x : ↥(H0 M Z), ∀ e, AM.φ x e = e + c • β e)
    (hV : Module.finrank AM.K V = 4) (hE : Module.finrank AM.K AM.M₀.E = 8) :
    AM.S.IsTS V := by
  have hQ : ∀ e, AM.M₀.Qf (β e) = 0 := by
    intro e
    obtain ⟨x, hx⟩ := hβq 1
    have h1 := AM.φ_Qf x e
    have hal : AM.M₀.B e (β e) = 0 := hβ.alt e
    rw [hx e, one_smul, AM.M₀.Qf_add, hal, add_zero] at h1
    linear_combination h1
  have hker : LinearMap.ker β = V := by
    ext e
    constructor
    · intro h
      exact hβ.ker e (LinearMap.mem_ker.mp h)
    · intro h
      exact LinearMap.mem_ker.mpr (hβ.kills e h)
  have hrange : LinearMap.range β = V := by
    have hle : LinearMap.range β ≤ V := by
      rintro _ ⟨e, rfl⟩
      exact hβ.range e
    have hr := LinearMap.finrank_range_add_finrank_ker β
    rw [hker, hV, hE] at hr
    exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
  intro e he
  rw [← hrange] at he
  obtain ⟨e', rfl⟩ := he
  exact hQ e'

theorem lemmaC_concl (hLC : LemmaCStatement) (hNK : E1NaturalKStatement) (hLine : NtLineStatement)
    (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z) :
    LemmaCConclusion AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) := by
  have hc : Ctx M Q Z B := hH.ctx
  have hsec : Sec5Hyp hc 4 t := hH.sec
  have hK1 : 1 < Nat.card AM.K := by
    have := hc.hyp.q4
    have := AM.glob.card
    omega
  have hK4 : 4 ≤ Nat.card AM.K := by
    have := hc.hyp.q4
    have := AM.glob.card
    omega
  have hE8 : Module.finrank AM.K AM.M₀.E = 8 := by
    have h := AM.glob.finrank_E hsec.width hK1
    omega
  obtain ⟨β, hβ, -, -, hβall⟩ := hLine G M Q Z B t hH AM
  have hβq : ∀ c : AM.K, ∃ x : ↥(H0 M Z), ∀ e, AM.φ x e = e + c • β e := fun c => by
    obtain ⟨x, -, hx⟩ := hβall c
    exact ⟨x, hx⟩
  have hXg : AM.actImage (E1Xpre M Q B t) ≤ AM.S.O := by
    intro g hg
    rw [ActionModel.actImage, Subgroup.mem_map] at hg
    obtain ⟨x, -, rfl⟩ := hg
    exact fun e => AM.φ_Qf x e
  rcases (caseE1_iff M Q Z B t).mp hH.case with hP | hM
  · obtain ⟨c, hnat⟩ := (hNK _ M Q Z B t hH AM).1 hP
    have hV4 : Module.finrank AM.K (AM.Vsp hc t) = 4 := by
      rw [c.finrank_eq]
      simp
    exact (hLC AM.K hK4 AM.S hE8 AM.glob.hyperbolic (AM.Vsp hc t)
      (Vsp_isTS AM hβ hβq hV4 hE8) hV4 _ hXg).1 c hnat
  · obtain ⟨b, c', hirr, c, hnat⟩ := (hNK _ M Q Z B t hH AM).2 hM
    have hV4 : Module.finrank AM.K (AM.Vsp hc t) = 4 := by
      rw [c.finrank_eq]
      simp
    exact (hLC AM.K hK4 AM.S hE8 AM.glob.hyperbolic (AM.Vsp hc t)
      (Vsp_isTS AM hβ hβq hV4 hE8) hV4 _ hXg).2 b c' hirr c hnat

theorem eq_of_actImage_eq (AM : ActionModel M Q Z) {N' N'' : Subgroup G}
    (h1 : N' ≤ H0 M Z) (h2 : N'' ≤ H0 M Z) (hQ' : Q ≤ N') (hQ'' : Q ≤ N'')
    (h : AM.actImage N' = AM.actImage N'') : N' = N'' := by
  have key : ∀ A B : Subgroup G, A ≤ H0 M Z → B ≤ H0 M Z → Q ≤ B →
      AM.actImage A ≤ AM.actImage B → A ≤ B := by
    intro A B hA hB hQB hAB a ha
    have hmem : AM.φ ⟨a, hA ha⟩ ∈ AM.actImage B := hAB ⟨⟨a, hA ha⟩, ha, rfl⟩
    rw [ActionModel.actImage, Subgroup.mem_map] at hmem
    obtain ⟨x, hx, hxeq⟩ := hmem
    have hy : AM.φ (x⁻¹ * ⟨a, hA ha⟩) = 1 := by
      rw [map_mul, map_inv, hxeq, inv_mul_cancel]
    have hyQ : ((x⁻¹ * ⟨a, hA ha⟩ : ↥(H0 M Z)) : G) ∈ Q := (AM.φ_ker _).mp hy
    have hxB : (x : G) ∈ B := Subgroup.mem_subgroupOf.mp hx
    have ha_eq : a = (x : G) * (((x⁻¹ * ⟨a, hA ha⟩ : ↥(H0 M Z))) : G) := by
      simp
    rw [ha_eq]
    exact B.mul_mem hxB (hQB hyQ)
  exact le_antisymm (key N' N'' h1 h2 hQ'' h.le) (key N'' N' h2 h1 hQ' h.ge)

theorem conjSubgroup_eq_of_normal {A : Subgroup G} {S : Subgroup G}
    (hS : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A) {s : G} (hs : s ∈ S) :
    conjSubgroup s A = A := by
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro h
    have h' := hS s hs _ h
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rw [e] at h'
    exact h'
  · intro h
    have h' := hS s⁻¹ (inv_mem hs) x h
    rw [inv_inv] at h'
    exact h'

theorem quotSat_nilpotent_of_line (hc : Ctx M Q Z B) (AM : ActionModel M Q Z) {A : Subgroup G}
    (hA : A ≤ H0 M Z) (hQA : Q ≤ A) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hββ : ∀ e, β (β e) = 0)
    (hline : ∀ a (ha : a ∈ A), ∃ c : AM.K, ∀ e, AM.φ ⟨a, hA ha⟩ e = e + c • β e) :
    QuotSat A Q (fun W _ => Group.IsNilpotent W) := by
  have hnorm : (Q.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => hc.hyp.Q_normal.2 (hA hx).1
  refine ⟨hnorm, ?_⟩
  have hcomm : ∀ a (ha : a ∈ A) b (hb : b ∈ A), ⁅a, b⁆ ∈ Q := by
    intro a ha b hb
    obtain ⟨c, hc'⟩ := hline a ha
    obtain ⟨d, hd'⟩ := hline b hb
    exact (phi_comm_iff_mem AM (hA ha) (hA hb)).mp <| LinearEquiv.ext fun e => by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        phi_mul_apply β hββ _ _ c d hc' hd' e, phi_mul_apply β hββ _ _ d c hd' hc' e, add_comm c d]
  have hcommQ : ∀ x y : A ⧸ Q.subgroupOf A, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [← commutatorElement_eq_one_iff_mul_comm]
        have h1 : QuotientGroup.mk' (Q.subgroupOf A) ⁅x, y⁆ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          exact hcomm x.1 x.2 y.1 y.2
        have h2 := map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf A)) x y
        rw [h1] at h2
        exact h2.symm
  haveI : IsMulCommutative (A ⧸ Q.subgroupOf A) := ⟨⟨hcommQ⟩⟩
  exact inferInstance

theorem exists_sylow_of_card_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    (T : Subgroup ↥(StatedSL 2 K)) (hT : Nat.card T = Nat.card K) :
    ∃ P : Sylow 2 ↥(StatedSL 2 K), P.toSubgroup = T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (by rw [hT, hq])
  obtain ⟨P, hTP⟩ := IsPGroup.exists_le_sylow hT2
  have hPc := card_sylow_statedSL_two K P
  exact ⟨P, (Subgroup.eq_of_le_of_card_ge hTP (by rw [hT, hPc])).symm⟩

@[expose] def Cgrp (AM : ActionModel M Q Z) (X : Subgroup G) :
    Subgroup (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) :=
  AM.S.Cent ((AM.actImage X : Subgroup (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E)) :
    Set (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E))

theorem actImage_thY_le_Cgrp (hc : Ctx M Q Z B) (AM : ActionModel M Q Z) :
    AM.actImage (thY hc t) ≤ Cgrp AM (E1Xpre M Q B t) := by
  intro g hg
  rw [ActionModel.actImage, Subgroup.mem_map] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  exact thY_phi_mem_cent hc AM hy

theorem conj_Nt_le_thY (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B)
    (hP1 : ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ E1Xpre M Q B t,
    s * x * s⁻¹ ∈ E1Xpre M Q B t) {s : G} (hs : s ∈ Lgen M (LB M Q B))
    (hNY : Nt M (LB M Q B) t ≤ thY hc t) :
    conjSubgroup s (Nt M (LB M Q B) t) ≤ thY hc t := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have h := thY_normal hc ht hP1 s hs _ (hNY hx)
  have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
  rw [e] at h
  exact h

theorem exists_conj_ne (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) (hH : E1Hyp M Q Z B t)
    (hF : M1FittingTrivialStatement) (AM : ActionModel M Q Z) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hβ : BetaProps AM.S (AM.Vsp hc t) β)
    (hβn : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t → ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hNL : Nt M (LB M Q B) t ≤ LB M Q B) :
    ∃ s ∈ Lgen M (LB M Q B), conjSubgroup s (Nt M (LB M Q B) t) ≠ Nt M (LB M Q B) t := by
  by_contra hcon
  push_neg at hcon
  have hNH : Nt M (LB M Q B) t ≤ H0 M Z := fun n hn =>
    Lgen_le_H0 hc (le_Lgen_self M (LB M Q B) (hNL hn))
  have hββ : ∀ e, β (β e) = 0 := fun e => hβ.kills _ (hβ.range e)
  have hquot : QuotSat (Nt M (LB M Q B) t) Q (fun W _ => Group.IsNilpotent W) :=
    quotSat_nilpotent_of_line hc AM hNH (smith23E1_Q_le_Nt hc ht) hββ
      (fun a ha => hβn ⟨a, hNH ha⟩ ha)
  have hNQ : Nt M (LB M Q B) t = Q :=
    hF _ M Q Z B t hH _ (smith23E1_Q_le_Nt hc ht)
      (hNL.trans (le_Lgen_self M (LB M Q B))) hcon hquot
  have hcard := hH.case.2.1
  rw [hNQ] at hcard
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have h1 : Nat.card Q * 1 = Nat.card Q * Nat.card Z := by
    rw [mul_one]
    exact hcard
  have h2 := Nat.eq_of_mul_eq_mul_left hQpos h1
  have hq4 := hc.hyp.q4
  omega

theorem eq_of_T_eq {K' : Type} [Field K'] {E' : Type} [AddCommGroup E'] [Module K' E']
    {Cg U U' : Subgroup (E' ≃ₗ[K'] E')}
    (ψ : ↥(StatedSL 2 K') ≃* ↥Cg) (hU : U ≤ Cg) (hU' : U' ≤ Cg)
    (h : (U.subgroupOf Cg).map ψ.symm.toMonoidHom = (U'.subgroupOf Cg).map ψ.symm.toMonoidHom) :
    U = U' := by
  ext g
  constructor
  · intro hg
    have hgC : g ∈ Cg := hU hg
    have hmem : ψ.symm ⟨g, hgC⟩ ∈ (U.subgroupOf Cg).map ψ.symm.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    rw [h] at hmem
    obtain ⟨d, hd, hdeq⟩ := Subgroup.mem_map.mp hmem
    have hd' : d = ⟨g, hgC⟩ := ψ.symm.injective hdeq
    have h2 : (d : E' ≃ₗ[K'] E') = g := by rw [hd']
    rw [← h2]
    exact Subgroup.mem_subgroupOf.mp hd
  · intro hg
    have hgC : g ∈ Cg := hU' hg
    have hmem : ψ.symm ⟨g, hgC⟩ ∈ (U'.subgroupOf Cg).map ψ.symm.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    rw [← h] at hmem
    obtain ⟨d, hd, hdeq⟩ := Subgroup.mem_map.mp hmem
    have hd' : d = ⟨g, hgC⟩ := ψ.symm.injective hdeq
    have h2 : (d : E' ≃ₗ[K'] E') = g := by rw [hd']
    rw [← h2]
    exact Subgroup.mem_subgroupOf.mp hd

theorem actImage_mono (AM : ActionModel M Q Z) {A B : Subgroup G} (h : A ≤ B) :
    AM.actImage A ≤ AM.actImage B :=
  Subgroup.map_mono (fun x hx => h hx)

theorem actImage_thY_eq_of_alt (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) (hH : E1Hyp M Q Z B t)
    (hF : M1FittingTrivialStatement) (hKF6 : SL2RootStatement)
    (hNL : Nt M (LB M Q B) t ≤ LB M Q B)
    (hP1 : ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ E1Xpre M Q B t, s * x * s⁻¹ ∈ E1Xpre M Q B t)
    (AM : ActionModel M Q Z) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hβ : BetaProps AM.S (AM.Vsp hc t) β)
    (hβn : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t → ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hNY : Nt M (LB M Q B) t ≤ thY hc t)
    (ψ : ↥(StatedSL 2 AM.K) ≃* ↥(Cgrp AM (E1Xpre M Q B t))) :
    AM.actImage (thY hc t) = Cgrp AM (E1Xpre M Q B t) := by
  have hH'C : AM.actImage (thY hc t) ≤ Cgrp AM (E1Xpre M Q B t) := actImage_thY_le_Cgrp hc AM
  have hNH0 : Nt M (LB M Q B) t ≤ H0 M Z := fun n hn =>
    Lgen_le_H0 hc (le_Lgen_self M (LB M Q B) (hNL hn))
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc ht
  have hUCg : AM.actImage (Nt M (LB M Q B) t) ≤ Cgrp AM (E1Xpre M Q B t) :=
    (actImage_mono AM hNY).trans hH'C
  have hUcard : Nat.card (AM.actImage (Nt M (LB M Q B) t)) = Nat.card AM.K :=
    (card_actImage_nt hc ht hH hNL AM).trans AM.glob.card.symm
  obtain ⟨s, hs, hsN⟩ := exists_conj_ne hc ht hH hF AM hβ hβn hNL
  have hN'Y : conjSubgroup s (Nt M (LB M Q B) t) ≤ thY hc t :=
    conj_Nt_le_thY hc ht hP1 hs hNY
  have hN'H0 : conjSubgroup s (Nt M (LB M Q B) t) ≤ H0 M Z := fun x hx =>
    Lgen_le_H0 hc (thY_le_Lgen hc (hN'Y hx))
  have hQN' : Q ≤ conjSubgroup s (Nt M (LB M Q B) t) := by
    intro q hq
    rw [mem_conjSubgroup]
    have hsM : s⁻¹ ∈ M := (Lgen_le_H0 hc (inv_mem hs)).1
    have h1 := Q_conj_mem_of hc hsM hq
    rw [inv_inv] at h1
    exact hQN h1
  have hN'card : Nat.card (conjSubgroup s (Nt M (LB M Q B) t)) =
      Nat.card (Nt M (LB M Q B) t) := by
    unfold conjSubgroup
    exact Subgroup.card_map_of_injective (f := (MulAut.conj s).toMonoidHom)
      (MulAut.conj s).injective
  have hU'card : Nat.card (AM.actImage (conjSubgroup s (Nt M (LB M Q B) t))) = Nat.card AM.K := by
    have h := card_actImage_mul AM hN'H0 hQN'
    rw [hN'card, hH.case.2.1] at h
    have h' : Nat.card (AM.actImage (conjSubgroup s (Nt M (LB M Q B) t))) * Nat.card Q =
        Nat.card AM.K * Nat.card Q := by
      rw [h, AM.glob.card, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h'
  have hU'Cg : AM.actImage (conjSubgroup s (Nt M (LB M Q B) t)) ≤ Cgrp AM (E1Xpre M Q B t) :=
    (actImage_mono AM hN'Y).trans hH'C
  have hne : AM.actImage (conjSubgroup s (Nt M (LB M Q B) t)) ≠
      AM.actImage (Nt M (LB M Q B) t) := fun h =>
    hsN (eq_of_actImage_eq AM hN'H0 hNH0 hQN' hQN h)
  have hT₁ : Nat.card ((AM.actImage (Nt M (LB M Q B) t)).subgroupOf (Cgrp AM (E1Xpre M Q B t))
      |>.map ψ.symm.toMonoidHom) = Nat.card AM.K := by
    rw [Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) ψ.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUCg).toEquiv, hUcard]
  have hT₂ : Nat.card ((AM.actImage (conjSubgroup s (Nt M (LB M Q B) t))).subgroupOf
      (Cgrp AM (E1Xpre M Q B t)) |>.map ψ.symm.toMonoidHom) = Nat.card AM.K := by
    rw [Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) ψ.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU'Cg).toEquiv, hU'card]
  obtain ⟨P₁, hP₁⟩ := exists_sylow_of_card_eq _ hT₁
  obtain ⟨P₂, hP₂⟩ := exists_sylow_of_card_eq _ hT₂
  have hne12 : P₁ ≠ P₂ := by
    intro hPP
    apply hne
    refine (eq_of_T_eq ψ hUCg hU'Cg ?_).symm
    rw [← hP₁, ← hP₂, hPP]
  have hKF := hKF6 AM.K P₁ P₂ hne12
  apply le_antisymm hH'C
  intro c hc'
  have hsub : ∀ P : Sylow 2 ↥(StatedSL 2 AM.K),
      ∀ U : Subgroup (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E), U ≤ AM.actImage (thY hc t) →
      U ≤ Cgrp AM (E1Xpre M Q B t) →
      P.toSubgroup = (U.subgroupOf (Cgrp AM (E1Xpre M Q B t))).map ψ.symm.toMonoidHom →
      P.toSubgroup ≤ ((AM.actImage (thY hc t)).subgroupOf (Cgrp AM (E1Xpre M Q B t))).comap
        ψ.toMonoidHom := by
    intro P U hUH hUC hPT σ hσ
    rw [hPT] at hσ
    obtain ⟨d, hd, hdeq⟩ := Subgroup.mem_map.mp hσ
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    have h2 : ψ.toMonoidHom σ = d := by
      rw [← hdeq]
      exact MulEquiv.apply_symm_apply ψ d
    rw [h2]
    exact hUH (Subgroup.mem_subgroupOf.mp hd)
  have htop : (⊤ : Subgroup ↥(StatedSL 2 AM.K)) ≤
      ((AM.actImage (thY hc t)).subgroupOf (Cgrp AM (E1Xpre M Q B t))).comap ψ.toMonoidHom := by
    rw [← hKF]
    exact sup_le (hsub P₁ _ (actImage_mono AM hNY) hUCg hP₁)
      (hsub P₂ _ (actImage_mono AM hN'Y) hU'Cg hP₂)
  have hσ := htop (Subgroup.mem_top (ψ.symm ⟨c, hc'⟩))
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hσ
  have h3 : ψ.toMonoidHom (ψ.symm ⟨c, hc'⟩) = ⟨c, hc'⟩ := MulEquiv.apply_symm_apply ψ _
  rw [h3] at hσ
  exact hσ

theorem quotSat_thY_SL (hc : Ctx M Q Z B) (AM : ActionModel M Q Z)
    (ψ : ↥(StatedSL 2 AM.K) ≃* ↥(Cgrp AM (E1Xpre M Q B t)))
    (hsurj : AM.actImage (thY hc t) = Cgrp AM (E1Xpre M Q B t)) :
    QuotSat (thY hc t) Q (IsSLModel 2 (Nat.card Z)) := by
  have hYH : thY hc t ≤ H0 M Z := fun y hy => Lgen_le_H0 hc (thY_le_Lgen hc hy)
  haveI hnorm : (Q.subgroupOf (thY hc t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun y hy => hc.hyp.Q_normal.2 (hYH hy).1
  let f0 : ↥(thY hc t) →* (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) :=
    AM.φ.comp (Subgroup.inclusion hYH)
  let f : ↥(thY hc t) →* ↥(Cgrp AM (E1Xpre M Q B t)) :=
    f0.codRestrict _ (fun y => thY_phi_mem_cent hc AM y.2)
  have hfy : ∀ y : ↥(thY hc t), (f y : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) =
      AM.φ (Subgroup.inclusion hYH y) := fun y => rfl
  have hf : Function.Surjective f := by
    intro c
    have hc2 : (c : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) ∈ AM.actImage (thY hc t) := by
      rw [hsurj]
      exact c.2
    rw [ActionModel.actImage, Subgroup.mem_map] at hc2
    obtain ⟨y, hy, hyeq⟩ := hc2
    refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    rw [hfy]
    exact hyeq
  have hker : f.ker = Q.subgroupOf (thY hc t) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : AM.φ (Subgroup.inclusion hYH y) = 1 := by
        rw [← hfy]
        exact congrArg Subtype.val h
      exact (AM.φ_ker _).mp h'
    · intro h
      apply Subtype.ext
      rw [hfy]
      exact (AM.φ_ker _).mpr h
  let e1 := (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).trans ψ.symm)
  exact ⟨hnorm, AM.K, inferInstance, inferInstance, AM.glob.card, ⟨e1⟩⟩

theorem case_line_false (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) (hH : E1Hyp M Q Z B t)
    (hF : M1FittingTrivialStatement) (AM : ActionModel M Q Z) {βC : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hββ : ∀ e, βC (βC e) = 0)
    (hlineC : ∀ g ∈ Cgrp AM (E1Xpre M Q B t), ∃ c : AM.K, ∀ e, g e = e + c • βC e)
    (hP1 : ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ E1Xpre M Q B t, s * x * s⁻¹ ∈ E1Xpre M Q B t)
    (hNY : Nt M (LB M Q B) t ≤ thY hc t) : False := by
  have hYH : thY hc t ≤ H0 M Z := fun y hy => Lgen_le_H0 hc (thY_le_Lgen hc hy)
  have hline : ∀ a (ha : a ∈ thY hc t), ∃ c : AM.K,
      ∀ e, AM.φ ⟨a, hYH ha⟩ e = e + c • βC e := fun a ha =>
    hlineC _ (thY_phi_mem_cent hc AM ha)
  have hquot := quotSat_nilpotent_of_line hc AM hYH (Q_le_thY hc ht) hββ hline
  have hYQ : thY hc t = Q := hF _ M Q Z B t hH (thY hc t) (Q_le_thY hc ht) (thY_le_Lgen hc)
    (fun s hs => conjSubgroup_eq_of_normal (thY_normal hc ht hP1) hs) hquot
  have hNQ : Nt M (LB M Q B) t ≤ Q := fun n hn => by
    have := hNY hn
    rwa [hYQ] at this
  have hle := Subgroup.card_le_of_le hNQ
  rw [hH.case.2.1] at hle
  have hq4 := hc.hyp.q4
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have h4 : Nat.card Q * 4 ≤ Nat.card Q * Nat.card Z := Nat.mul_le_mul_left _ hq4
  omega

end Phi

section LayerSetup

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem H0_normal_conj (hc : Ctx M Q Z B) {s a : G} (hs : s ∈ M) (ha : a ∈ H0 M Z) :
    s * a * s⁻¹ ∈ H0 M Z := by
  have ha2 : a ∈ Subgroup.centralizer (Z : Set G) := ha.2
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hs ha.1) (inv_mem hs), ?_⟩
  show s * a * s⁻¹ ∈ Subgroup.centralizer (Z : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : s⁻¹ * z * s⁻¹⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (inv_mem hs)) z).mp hz
  have hc1 := (Subgroup.mem_centralizer_iff.mp ha2) _ hz'
  calc z * (s * a * s⁻¹) = s * ((s⁻¹ * z * s⁻¹⁻¹) * a) * s⁻¹ := by group
    _ = s * (a * (s⁻¹ * z * s⁻¹⁻¹)) * s⁻¹ := by rw [hc1]
    _ = s * a * s⁻¹ * z := by group

theorem conj_H0_eq (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) : conjSubgroup m (H0 M Z) = H0 M Z :=
  conjSubgroup_eq_of_normal (fun s hs a ha => H0_normal_conj hc hs ha) hm

end LayerSetup

section LayerAut

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Q_normal_subgroupOf_H0 (hc : Ctx M Q Z B) : (Q.subgroupOf (H0 M Z)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer fun _ hx => hc.hyp.Q_normal.2 hx.1

@[expose] def barA (M Q Z : Subgroup G) [(Q.subgroupOf (H0 M Z)).Normal] (S : Subgroup G) :
    Subgroup (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) :=
  (S.subgroupOf (H0 M Z)).map (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)))

theorem mem_barA (M Q Z : Subgroup G) [(Q.subgroupOf (H0 M Z)).Normal] {S : Subgroup G}
    {a : ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)} :
    a ∈ barA M Q Z S ↔ ∃ x : ↥(H0 M Z), (x : G) ∈ S ∧
      (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) x : _) = a := by
  unfold barA
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

@[expose] def eH (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) : ↥(H0 M Z) ≃* ↥(H0 M Z) :=
  ((MulAut.conj m).subgroupMap (H0 M Z)).trans (MulEquiv.subgroupCongr (conj_H0_eq hc hm))

theorem eH_coe (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) (x : ↥(H0 M Z)) :
    ((eH hc hm x : ↥(H0 M Z)) : G) = m * (x : G) * m⁻¹ := rfl

theorem eH_map (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    (Q.subgroupOf (H0 M Z)).map (eH hc hm).toMonoidHom = Q.subgroupOf (H0 M Z) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [MulEquiv.coe_toMonoidHom, eH_coe]
    exact Q_conj_mem_of hc hm hx
  · intro hy
    refine ⟨(eH hc hm).symm y, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have h1 := eH_coe hc hm ((eH hc hm).symm y)
      rw [MulEquiv.apply_symm_apply] at h1
      have h2 : (((eH hc hm).symm y : ↥(H0 M Z)) : G) = m⁻¹ * (y : G) * m⁻¹⁻¹ := by
        rw [h1]
        group
      rw [h2]
      exact Q_conj_mem_of hc (inv_mem hm) (Subgroup.mem_subgroupOf.mp hy)
    · exact (eH hc hm).apply_symm_apply y

@[expose] def autA [(Q.subgroupOf (H0 M Z)).Normal] (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) ≃* (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) :=
  QuotientGroup.congr (Q.subgroupOf (H0 M Z)) (Q.subgroupOf (H0 M Z)) (eH hc hm) (eH_map hc hm)

theorem autA_mk [(Q.subgroupOf (H0 M Z)).Normal] (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M)
    (x : ↥(H0 M Z)) :
    autA hc hm (QuotientGroup.mk x) = QuotientGroup.mk (eH hc hm x) :=
  QuotientGroup.congr_mk _ _ _ _ x

end LayerAut

section LayerAssembly

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}

theorem barA_Lgen_normal [(Q.subgroupOf (H0 M Z)).Normal] (hc : Ctx M Q Z B) :
    (barA M Q Z (Lgen M (LB M Q B))).Normal := by
  refine ⟨fun n hn a => ?_⟩
  obtain ⟨x, hx, rfl⟩ := mem_barA M Q Z |>.mp hn
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf (H0 M Z)) a
  have hyM : (y : G) ∈ M := y.2.1
  have hxy : (y : G) * (x : G) * (y : G)⁻¹ ∈ Lgen M (LB M Q B) :=
    (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B) hyM) x).mp hx
  rw [mem_barA M Q Z]
  refine ⟨y * x * y⁻¹, hxy, ?_⟩
  simp [map_mul, map_inv]

theorem barA_normal_of [(Q.subgroupOf (H0 M Z)).Normal] {S : Subgroup G}
    (hS : ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ S, s * x * s⁻¹ ∈ S) :
    ((barA M Q Z S).subgroupOf (barA M Q Z (Lgen M (LB M Q B)))).Normal := by
  refine ⟨fun x hx n => ?_⟩
  obtain ⟨z, hzS, hzx⟩ := (mem_barA M Q Z).mp (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨g, hgL, hgn⟩ := (mem_barA M Q Z).mp n.2
  rw [Subgroup.mem_subgroupOf, mem_barA M Q Z]
  refine ⟨g * z * g⁻¹, hS g hgL z hzS, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hzx, ← hgn]
  simp [map_mul, map_inv]

theorem barA_mono [(Q.subgroupOf (H0 M Z)).Normal] {S T : Subgroup G} (h : S ≤ T) :
    barA M Q Z S ≤ barA M Q Z T :=
  Subgroup.map_mono (fun x hx => h hx)

theorem layer_barA_of_quot [(Q.subgroupOf (H0 M Z)).Normal] {S : Subgroup G} (hS : S ≤ H0 M Z)
    [(Q.subgroupOf S).Normal] (hq : CFSG.layer (↥S ⧸ Q.subgroupOf S) = ⊤) :
    CFSG.layer ↥(barA M Q Z S) = ⊤ := by
  have hr := quotIncl_range (Q := Q) hS
  let e : (↥S ⧸ Q.subgroupOf S) ≃* ↥(barA M Q Z S) :=
    (MonoidHom.ofInjective (quotIncl_injective (Q := Q) hS)).trans (MulEquiv.subgroupCongr hr)
  exact layer_eq_top_of_mulEquiv e hq

theorem layer_barA_sub [(Q.subgroupOf (H0 M Z)).Normal] {S : Subgroup G} (hS : S ≤ H0 M Z)
    [(Q.subgroupOf S).Normal] (hq : CFSG.layer (↥S ⧸ Q.subgroupOf S) = ⊤)
    {N : Subgroup (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z))} (hle : barA M Q Z S ≤ N) :
    CFSG.layer ↥((barA M Q Z S).subgroupOf N) = ⊤ :=
  layer_eq_top_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
    (layer_barA_of_quot hS hq)

theorem centralizer_barA_eq_bot [(Q.subgroupOf (H0 M Z)).Normal] (hc : Ctx M Q Z B)
    (hcent : CentTrivial M Q Z (Lgen M (LB M Q B))) :
    Subgroup.centralizer ((barA M Q Z (Lgen M (LB M Q B)) : Subgroup _) :
      Set (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z))) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  induction y using QuotientGroup.induction_on with
  | H h =>
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine hcent h.1 h.2 fun x hx => ?_
    have hxN : (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨x, Lgen_le_H0 hc hx⟩ :
        ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) ∈ barA M Q Z (Lgen M (LB M Q B)) :=
      (mem_barA M Q Z).mpr ⟨⟨x, Lgen_le_H0 hc hx⟩, hx, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hy _ hxN
    have h1 : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⁅h, ⟨x, Lgen_le_H0 hc hx⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa [commutatorElement_def] using h1

theorem barA_hC [(Q.subgroupOf (H0 M Z)).Normal] (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) :
    ∀ n ∈ barA M Q Z (Lgen M (LB M Q B)), (∀ x ∈ barA M Q Z (E1Xpre M Q B t), ⁅n, x⁆ = 1) →
      n ∈ barA M Q Z (thY hc t) := by
  intro n hn hcomm
  obtain ⟨g, hg, rfl⟩ := (mem_barA M Q Z).mp hn
  have hgY : (g : G) ∈ thY hc t := by
    refine ⟨hg, fun x hx => ?_⟩
    have hxH : x ∈ H0 M Z := Lgen_le_H0 hc (E1Xpre_le_Lgen hc ht hx)
    have hxX : (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨x, hxH⟩ :
        ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) ∈ barA M Q Z (E1Xpre M Q B t) :=
      (mem_barA M Q Z).mpr ⟨⟨x, hxH⟩, hx, rfl⟩
    have h1 := hcomm _ hxX
    rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    simpa [commutatorElement_def] using h1
  exact (mem_barA M Q Z).mpr ⟨⟨g, Lgen_le_H0 hc hg⟩, hgY, rfl⟩

theorem barA_Lgen_le_autA [(Q.subgroupOf (H0 M Z)).Normal] (hc : Ctx M Q Z B) :
    barA M Q Z (Lgen M (LB M Q B)) ≤
      ⨆ α ∈ {α : (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) ≃* (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) |
        ∃ (m : G) (hm : m ∈ M), α = autA hc hm}, (barA M Q Z (LB M Q B)).map α.toMonoidHom := by
  set 𝒜 : Set ((↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) ≃* (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z))) :=
    {α | ∃ (m : G) (hm : m ∈ M), α = autA hc hm} with h𝒜
  set T : Subgroup (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) :=
    ⨆ α ∈ 𝒜, (barA M Q Z (LB M Q B)).map α.toMonoidHom with hT
  let K : Subgroup G :=
    { carrier := {x | ∃ h : x ∈ H0 M Z, (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨x, h⟩ :
        ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) ∈ T}
      one_mem' := ⟨(H0 M Z).one_mem, by
        show (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) (1 : ↥(H0 M Z))) ∈ T
        rw [map_one]
        exact T.one_mem⟩
      mul_mem' := by
        rintro x y ⟨hx, hxT⟩ ⟨hy, hyT⟩
        refine ⟨(H0 M Z).mul_mem hx hy, ?_⟩
        have e : (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨x * y, (H0 M Z).mul_mem hx hy⟩ :
            ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) =
            QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨x, hx⟩ *
              QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨y, hy⟩ := by
          rw [← map_mul]
          rfl
        rw [e]
        exact T.mul_mem hxT hyT
      inv_mem' := by
        rintro x ⟨hx, hxT⟩
        refine ⟨(H0 M Z).inv_mem hx, ?_⟩
        have e : (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨x⁻¹, (H0 M Z).inv_mem hx⟩ :
            ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) =
            (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨x, hx⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [e]
        exact T.inv_mem hxT }
  have hK : Lgen M (LB M Q B) ≤ K := by
    unfold Lgen
    refine iSup₂_le fun m hm => ?_
    intro x hx
    have hxLg : x ∈ Lgen M (LB M Q B) :=
      le_iSup₂ (f := fun m (_ : m ∈ M) => conjSubgroup m (LB M Q B)) m hm hx
    have hxH0 : x ∈ H0 M Z := Lgen_le_H0 hc hxLg
    refine ⟨hxH0, ?_⟩
    rw [mem_conjSubgroup] at hx
    have hy0 : m⁻¹ * x * m ∈ H0 M Z := Lgen_le_H0 hc (le_Lgen_self M (LB M Q B) hx)
    have hyL : (⟨m⁻¹ * x * m, hy0⟩ : ↥(H0 M Z)) ∈ (LB M Q B).subgroupOf (H0 M Z) := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    have hmem : (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨m⁻¹ * x * m, hy0⟩ :
        ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) ∈ barA M Q Z (LB M Q B) :=
      (mem_barA M Q Z).mpr ⟨⟨m⁻¹ * x * m, hy0⟩, hx, rfl⟩
    have key : (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨x, hxH0⟩ :
        ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) =
        autA hc hm (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨m⁻¹ * x * m, hy0⟩) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, autA_mk]
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      rw [eH_coe]
      group
    have hα : autA hc hm ∈ 𝒜 := ⟨m, hm, rfl⟩
    have hTle : (barA M Q Z (LB M Q B)).map (autA hc hm).toMonoidHom ≤ T :=
      le_iSup₂ (f := fun α (_ : α ∈ 𝒜) => (barA M Q Z (LB M Q B)).map α.toMonoidHom)
        (autA hc hm) hα
    rw [key]
    exact hTle (Subgroup.mem_map_of_mem _ hmem)
  intro a ha
  obtain ⟨g, hg, rfl⟩ := (mem_barA M Q Z).mp ha
  exact (hK hg).2

end LayerAssembly


section CentreFacts

@[expose] def CentreTriv (W : Type) [Group W] : Prop :=
  ∀ w : W, (∀ g : W, g * w = w * g) → w = 1

theorem centreTriv_of_mulEquiv {W W' : Type} [Group W] [Group W'] (e : W ≃* W')
    (h : CentreTriv W') : CentreTriv W := by
  intro w hw
  have h1 : e w = 1 := by
    apply h
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hw g']
  exact e.injective (by rw [h1, map_one])

theorem centreTriv_statedSL_two (K : Type) [Field K] [Finite K] [CharP K 2] :
    CentreTriv ↥(StatedSL 2 K) := by
  intro w hw
  have hmem : w ∈ Subgroup.center ↥(StatedSL 2 K) := Subgroup.mem_center_iff.mpr hw
  rw [center_statedSL_two_bot K] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem centreTriv_prod {A B : Type} [Group A] [Group B] (hA : CentreTriv A) (hB : CentreTriv B) :
    CentreTriv (A × B) := by
  intro w hw
  have hA' : w.1 = 1 := hA _ fun g => by
    have := hw (g, 1)
    exact congrArg Prod.fst this
  have hB' : w.2 = 1 := hB _ fun g => by
    have := hw (1, g)
    exact congrArg Prod.snd this
  exact Prod.ext hA' hB'

theorem centreTriv_statedOmega_plus_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) : CentreTriv ↥(StatedOmega (StatedQuadPlus 2 K)) := by
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  exact centreTriv_of_mulEquiv e (centreTriv_prod (centreTriv_statedSL_two K)
    (centreTriv_statedSL_two K))

open CFSG.ComponentClassification.RankTwoClassical.ORigid in
theorem centreTriv_statedOmega_minus_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CentreTriv ↥(StatedOmega (StatedQuadMinus 2 K b c)) := by
  haveI := isSimpleGroup_statedOmega_quadMinus_of_two_le (le_refl 2) hirr
  intro w hw
  by_contra hne
  have hcen : Subgroup.center ↥(StatedOmega (StatedQuadMinus 2 K b c)) ≠ ⊥ := fun h => by
    apply hne
    have hwc : w ∈ Subgroup.center ↥(StatedOmega (StatedQuadMinus 2 K b c)) :=
      Subgroup.mem_center_iff.mpr hw
    rw [h] at hwc
    exact Subgroup.mem_bot.mp hwc
  have htop : Subgroup.center ↥(StatedOmega (StatedQuadMinus 2 K b c)) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hcen
  have hcomm : ⁅(⊤ : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))),
      (⊤ : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c)))⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun u _ v _ => ?_
    have hu : u ∈ Subgroup.center ↥(StatedOmega (StatedQuadMinus 2 K b c)) := by
      rw [htop]
      exact Subgroup.mem_top u
    have huv := Subgroup.mem_center_iff.mp hu v
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact huv.symm
  have hcommutator := commutator_statedOmega_quadMinus_eq_top (le_refl 2) hirr
  have h2 : (⊤ : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) = ⊥ := by
    rw [← hcommutator]
    exact hcomm
  exact bot_ne_top h2.symm

end CentreFacts

section Assembly2

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}

theorem thY_inf_eq [(Q.subgroupOf (E1Xpre M Q B t)).Normal] (hc : Ctx M Q Z B)
    (ht : t ∈ LB M Q B) (hZ : CentreTriv (↥(E1Xpre M Q B t) ⧸ Q.subgroupOf (E1Xpre M Q B t))) :
    thY hc t ⊓ E1Xpre M Q B t = Q := by
  apply le_antisymm
  · rintro y ⟨hyY, hyX⟩
    have hz := hZ (QuotientGroup.mk' (Q.subgroupOf (E1Xpre M Q B t)) ⟨y, hyX⟩) (fun g => by
      induction g using QuotientGroup.induction_on with
      | H x =>
        have h1 : QuotientGroup.mk' (Q.subgroupOf (E1Xpre M Q B t)) ⁅x, ⟨y, hyX⟩⁆ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          have h2 : ⁅(y : G), (x : G)⁆ ∈ Q := (mem_thY hc).mp hyY |>.2 x x.2
          have h3 : ⁅(y : G), (x : G)⁆⁻¹ ∈ Q := Q.inv_mem h2
          rw [commutatorElement_inv] at h3
          exact h3
        have h2 := map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf (E1Xpre M Q B t))) x
          ⟨y, hyX⟩
        rw [h1] at h2
        exact (commutatorElement_eq_one_iff_mul_comm.mp h2.symm))
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hz
    exact hz
  · exact le_inf (Q_le_thY hc ht) le_sup_right

theorem thY_normalizes_X (hc : Ctx M Q Z B) (hP1 : ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ E1Xpre M Q B t,
    s * x * s⁻¹ ∈ E1Xpre M Q B t) :
    thY hc t ≤ Subgroup.normalizer (E1Xpre M Q B t : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hP1 y (thY_le_Lgen hc hy) x hx
  · intro hx
    have h1 := hP1 y⁻¹ (inv_mem (thY_le_Lgen hc hy)) _ hx
    have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
    rw [e] at h1
    exact h1

theorem thY_sup_eq (hc : Ctx M Q Z B) [(Q.subgroupOf (H0 M Z)).Normal]
    [(Q.subgroupOf (E1Xpre M Q B t)).Normal] [(Q.subgroupOf (thY hc t)).Normal] (ht : t ∈ LB M Q B)
    (hP1 : ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ E1Xpre M Q B t, s * x * s⁻¹ ∈ E1Xpre M Q B t)
    (hLB : LB M Q B ≤ thY hc t ⊔ E1Xpre M Q B t)
    (hcent : CentTrivial M Q Z (Lgen M (LB M Q B)))
    (hXl : CFSG.layer (↥(E1Xpre M Q B t) ⧸ Q.subgroupOf (E1Xpre M Q B t)) = ⊤)
    (hYl : CFSG.layer (↥(thY hc t) ⧸ Q.subgroupOf (thY hc t)) = ⊤) :
    thY hc t ⊔ E1Xpre M Q B t = Lgen M (LB M Q B) := by
  have hX0 : E1Xpre M Q B t ≤ H0 M Z := fun x hx => Lgen_le_H0 hc (E1Xpre_le_Lgen hc ht hx)
  have hY0 : thY hc t ≤ H0 M Z := fun y hy => Lgen_le_H0 hc (thY_le_Lgen hc hy)
  have hYn := thY_normalizes_X (t := t) hc hP1
  have hN := barA_Lgen_normal (M := M) (Q := Q) (Z := Z) (B := B) hc
  have hXN : barA M Q Z (E1Xpre M Q B t) ≤ barA M Q Z (Lgen M (LB M Q B)) :=
    barA_mono (E1Xpre_le_Lgen hc ht)
  have hYN : barA M Q Z (thY hc t) ≤ barA M Q Z (Lgen M (LB M Q B)) :=
    barA_mono (thY_le_Lgen hc)
  have hX : ((barA M Q Z (E1Xpre M Q B t)).subgroupOf (barA M Q Z (Lgen M (LB M Q B)))).Normal :=
    barA_normal_of hP1
  have hY : ((barA M Q Z (thY hc t)).subgroupOf (barA M Q Z (Lgen M (LB M Q B)))).Normal :=
    barA_normal_of (thY_normal hc ht hP1)
  have hXl' : CFSG.layer ↥((barA M Q Z (E1Xpre M Q B t)).subgroupOf
      (barA M Q Z (Lgen M (LB M Q B)))) = ⊤ :=
    layer_barA_sub hX0 hXl hXN
  have hYl' : CFSG.layer ↥((barA M Q Z (thY hc t)).subgroupOf
      (barA M Q Z (Lgen M (LB M Q B)))) = ⊤ :=
    layer_barA_sub hY0 hYl hYN
  have hYnorm : barA M Q Z (thY hc t) ≤
      Subgroup.normalizer ((barA M Q Z (E1Xpre M Q B t) : Subgroup _) : Set _) := by
    have hconj : ∀ n ∈ barA M Q Z (Lgen M (LB M Q B)), ∀ a ∈ barA M Q Z (E1Xpre M Q B t),
        n * a * n⁻¹ ∈ barA M Q Z (E1Xpre M Q B t) := fun n hn a ha =>
      Subgroup.mem_subgroupOf.mp (hX.conj_mem ⟨a, hXN ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨n, hn⟩)
    intro yb hyb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact fun ha => hconj yb (hYN hyb) a ha
    · intro ha
      have h1 := hconj yb⁻¹ (inv_mem (hYN hyb)) _ ha
      have e : yb⁻¹ * (yb * a * yb⁻¹) * yb⁻¹⁻¹ = a := by group
      rw [e] at h1
      exact h1
  have hLXY : barA M Q Z (LB M Q B) ≤ barA M Q Z (E1Xpre M Q B t) ⊔ barA M Q Z (thY hc t) := by
    intro a ha
    obtain ⟨l, hl, rfl⟩ := (mem_barA M Q Z).mp ha
    obtain ⟨y, hy, x, hx, hlyx⟩ := exists_mul_of_sup_of_le_normalizer' hYn (hLB hl)
    have hyH : y ∈ H0 M Z := Lgen_le_H0 hc (thY_le_Lgen hc hy)
    have hxH : x ∈ H0 M Z := Lgen_le_H0 hc (E1Xpre_le_Lgen hc ht hx)
    have e : (QuotientGroup.mk' (Q.subgroupOf (H0 M Z))
        ⟨l, Lgen_le_H0 hc (le_Lgen_self M (LB M Q B) hl)⟩ :
        ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) =
        QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨y, hyH⟩ *
          QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨x, hxH⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hlyx
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup ((mem_barA M Q Z).mpr ⟨⟨y, hyH⟩, hy, rfl⟩)
      ((mem_barA M Q Z).mpr ⟨⟨x, hxH⟩, hx, rfl⟩)
  have hC := barA_hC (t := t) hc ht
  have hcentN := centralizer_barA_eq_bot hc hcent
  have hsup := sup_eq_of_layer (barA M Q Z (Lgen M (LB M Q B))) (barA M Q Z (E1Xpre M Q B t))
    (barA M Q Z (thY hc t)) (barA M Q Z (LB M Q B)) hN hXN hYN hLXY hX hY hXl' hYl' hC hcentN _
    (barA_Lgen_le_autA hc)
  apply le_antisymm (sup_le (thY_le_Lgen hc) (E1Xpre_le_Lgen hc ht))
  intro g hg
  have hgN : (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨g, Lgen_le_H0 hc hg⟩ :
      ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) ∈ barA M Q Z (Lgen M (LB M Q B)) :=
    (mem_barA M Q Z).mpr ⟨⟨g, Lgen_le_H0 hc hg⟩, hg, rfl⟩
  rw [hsup, sup_comm] at hgN
  obtain ⟨yb, hyb, xb, hxb, hgeq⟩ := exists_mul_of_sup_of_le_normalizer' hYnorm hgN
  obtain ⟨y, hy, rfl⟩ := (mem_barA M Q Z).mp hyb
  obtain ⟨x, hx, rfl⟩ := (mem_barA M Q Z).mp hxb
  have e : (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) (y * x : ↥(H0 M Z))) =
      QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨g, Lgen_le_H0 hc hg⟩ := by
    rw [map_mul]
    exact hgeq.symm
  have hq : ((y : G) * (x : G))⁻¹ * g ∈ Q := by
    have h1 := QuotientGroup.eq.mp e
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hQX : Q ≤ E1Xpre M Q B t := le_sup_right
  have hxq : (x : G) * (((y : G) * (x : G))⁻¹ * g) ∈ E1Xpre M Q B t :=
    (E1Xpre M Q B t).mul_mem hx (hQX hq)
  have hg' : g = (y : G) * ((x : G) * (((y : G) * (x : G))⁻¹ * g)) := by group
  have key := Subgroup.mul_mem_sup hy hxq
  rwa [← hg'] at key

end Assembly2

theorem centreTriv_of_isOmegaPlus_two {q k : ℕ} (hq : 4 ≤ q) (hk : q = 2 ^ k) {W : Type}
    [Group W] (h : IsOmegaPlus 2 q W) : CentreTriv W := by
  obtain ⟨K, _, _, hK, ⟨eB⟩⟩ := h
  haveI : CharP K 2 := charP_two_of_natCard_pow_two (hK.trans hk)
  exact centreTriv_of_mulEquiv eB (centreTriv_statedOmega_plus_two (hK ▸ hq))

theorem centreTriv_of_isOmegaMinus_two {q k : ℕ} (hq : 4 ≤ q) (hk : q = 2 ^ k) {W : Type}
    [Group W] (h : IsOmegaMinus 2 q W) : CentreTriv W := by
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨eB⟩⟩ := h
  haveI : CharP K 2 := charP_two_of_natCard_pow_two (hK.trans hk)
  exact centreTriv_of_mulEquiv eB (centreTriv_statedOmega_minus_two hirr)

theorem theoremR_of (hLC : LemmaCStatement) (hKF6 : SL2RootStatement)
    (hSplit : RtSplitStatement) (hNK : E1NaturalKStatement) (hLine : NtLineStatement)
    (_hCt : CtStructureStatement) (hF : M1FittingTrivialStatement) : TheoremRStatement := by
  intro G _ _ M Q Z B t hH hP1
  have hc : Ctx M Q Z B := hH.ctx
  have ht : t ∈ LB M Q B := hH.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨n0, -, hn0, -⟩ := hc.hyp.cp
  obtain ⟨hNL, -, -, -, -, hLB6, -, hPlus, hMinus⟩ := hSplit G M Q Z B t hH
  obtain ⟨AM⟩ := ActionModel.nonempty hc.hyp
  obtain ⟨β, hβ, hβr, hβn, -⟩ := hLine G M Q Z B t hH AM
  have hNY : Nt M (LB M Q B) t ≤ thY hc t := Nt_le_thY hc ht hNL AM hβr hβn
  obtain ⟨βC, hβC, -, -, hdich⟩ := lemmaC_concl hLC hNK hLine hH AM
  have hββC : ∀ e, βC (βC e) = 0 := fun e => hβC.kills _ (hβC.range e)
  haveI := Q_normal_subgroupOf_H0 hc
  rcases hdich with hline | hnon
  · exact (case_line_false hc ht hH hF AM hββC hline hP1 hNY).elim
  · obtain ⟨ψ⟩ := hnon
    have hsurj := actImage_thY_eq_of_alt hc ht hH hF hKF6 hNL hP1 AM hβ hβn hNY ψ
    have hYSL : QuotSat (thY hc t) Q (IsSLModel 2 (Nat.card Z)) := quotSat_thY_SL hc AM ψ hsurj
    obtain ⟨hNYi, hYSLp⟩ := hYSL
    haveI := hNYi
    have hYl : CFSG.layer (↥(thY hc t) ⧸ Q.subgroupOf (thY hc t)) = ⊤ :=
      layer_eq_top_of_isSLModel_two hq4 hYSLp
    have hXpair : QuotSat (E1Xpre M Q B t) Q (fun W _ => CFSG.layer W = ⊤) := by
      rcases (caseE1_iff M Q Z B t).mp hH.case with hP | hM
      · obtain ⟨hN, hW⟩ := hPlus hP
        exact ⟨hN, layer_eq_top_of_isOmegaPlus_two hq4 hn0 hW⟩
      · obtain ⟨hN, hW⟩ := hMinus hM
        exact ⟨hN, layer_eq_top_of_isOmegaMinus_two hq4 hn0 hW⟩
    have hXcent : QuotSat (E1Xpre M Q B t) Q (fun W _ => CentreTriv W) := by
      rcases (caseE1_iff M Q Z B t).mp hH.case with hP | hM
      · obtain ⟨hN, hW⟩ := hPlus hP
        exact ⟨hN, centreTriv_of_isOmegaPlus_two hq4 hn0 hW⟩
      · obtain ⟨hN, hW⟩ := hMinus hM
        exact ⟨hN, centreTriv_of_isOmegaMinus_two hq4 hn0 hW⟩
    obtain ⟨hNXi, hXlay⟩ := hXpair
    obtain ⟨hNXc, hXc⟩ := hXcent
    have hinf : thY hc t ⊓ E1Xpre M Q B t = Q := by
      haveI := hNXc
      exact thY_inf_eq hc ht hXc
    have hLBle : LB M Q B ≤ thY hc t ⊔ E1Xpre M Q B t :=
      hLB6.le.trans (sup_le_sup hNY inf_le_right)
    have hsup : thY hc t ⊔ E1Xpre M Q B t = Lgen M (LB M Q B) := by
      haveI := hNXi
      exact thY_sup_eq hc ht hP1 hLBle hH.cent hXlay hYl
    exact ⟨thY hc t, Q_le_thY hc ht, thY_le_Lgen hc, thY_normal hc ht hP1, hinf, hsup,
      fun y hy x hx => ((mem_thY hc).mp hy).2 x hx, ⟨hNYi, hYSLp⟩⟩

end CFSG.RankThree.GF2n.Smith81.Smith23E1

module

public import CFSG.Quasithin.MS93.S512LGrp
public import CFSG.Quasithin.MS93.S512NS0
public import CFSG.Quasithin.MS93.S45Vtx
public import CFSG.Quasithin.MS93.S38EInst
public import CFSG.Quasithin.MS93.S512TBad
public import CFSG.Quasithin.MS93.S512NV

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512L

section Index

variable {Γ : Type*} [Group Γ]

theorem relIndex_ne_zero_of_finite (H K : Subgroup Γ) [Finite ↥K] : H.relIndex K ≠ 0 := by
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_ne_zero_of_le {H K X : Subgroup Γ} [Finite ↥X] (hK : K ≤ X) :
    H.relIndex K ≠ 0 := by
  have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective hK)
  exact relIndex_ne_zero_of_finite H K

theorem relIndex_le_of_le_sup {V W Q B X : Subgroup Γ} [Finite ↥X] (hV : V ≤ W ⊔ B)
    (hWB : W ≤ Subgroup.normalizer (B : Set Γ)) (hX : W ⊔ B ≤ X) :
    ((W ⊓ Q) ⊔ B).relIndex V ≤ Q.relIndex W := by
  set H := (W ⊓ Q) ⊔ B with hH
  have hBH : B ≤ H := le_sup_right
  have hHWB : H ≤ W ⊔ B := sup_le_sup_right inf_le_left B
  have h1 : H.relIndex V ≤ H.relIndex (W ⊔ B) :=
    Subgroup.relIndex_le_of_le_right hV (relIndex_ne_zero_of_le hX)
  have h2 : B.relIndex H * H.relIndex (W ⊔ B) = B.relIndex (W ⊔ B) :=
    Subgroup.relIndex_mul_relIndex B H (W ⊔ B) hBH hHWB
  have h3 : B.relIndex (W ⊔ B) = B.relIndex W := S38E.relIndex_sup_of_le_normalizer hWB
  have h4 : B.relIndex H = B.relIndex (W ⊓ Q) :=
    S38E.relIndex_sup_of_le_normalizer (inf_le_left.trans hWB)
  have h5 : B.relIndex (Q ⊓ W) * Q.relIndex W = (B ⊓ Q).relIndex W :=
    Subgroup.relIndex_inf_mul_relIndex B Q W
  have h6 : Q.relIndex (B ⊓ W) * B.relIndex W = (Q ⊓ B).relIndex W :=
    Subgroup.relIndex_inf_mul_relIndex Q B W
  rw [inf_comm Q B, ← h5, inf_comm Q W] at h6
  rw [h4, h3] at h2
  have hWX : W ⊓ Q ≤ X := inf_le_left.trans (le_sup_left.trans hX)
  have hBWX : B ⊓ W ≤ X := inf_le_right.trans (le_sup_left.trans hX)
  have hpos : 0 < B.relIndex (W ⊓ Q) := Nat.pos_of_ne_zero (relIndex_ne_zero_of_le hWX)
  have hpos' : 0 < Q.relIndex (B ⊓ W) := Nat.pos_of_ne_zero (relIndex_ne_zero_of_le hBWX)
  have h7 : H.relIndex (W ⊔ B) * Q.relIndex (B ⊓ W) = Q.relIndex W := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc B.relIndex (W ⊓ Q) * (H.relIndex (W ⊔ B) * Q.relIndex (B ⊓ W))
        = (B.relIndex (W ⊓ Q) * H.relIndex (W ⊔ B)) * Q.relIndex (B ⊓ W) := by ring
      _ = B.relIndex W * Q.relIndex (B ⊓ W) := by rw [h2]
      _ = Q.relIndex (B ⊓ W) * B.relIndex W := by ring
      _ = B.relIndex (W ⊓ Q) * Q.relIndex W := h6
  calc H.relIndex V ≤ H.relIndex (W ⊔ B) := h1
    _ ≤ H.relIndex (W ⊔ B) * Q.relIndex (B ⊓ W) := Nat.le_mul_of_pos_right _ hpos'
    _ = Q.relIndex W := h7

end Index


section Base

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem stab_le_normalizer_vv (h : PUHyp M T L) :
    stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (Vv _ (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) :=
  stab_le_normalizer_of_smul _ (fun g ρ => vi_smul _ g ρ 2) _

theorem voSub_le_vv (h : PUHyp M T L) :
    S5.voSub h.le L (baseA _) ≤ Vv _ (baseA (puAmalgam h.le)) :=
  commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L _).trans (stab_le_normalizer_vv h))

theorem stab_le_normalizer_voSub (h : PUHyp M T L) :
    stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (S5.voSub h.le L (baseA _) : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  exact le_normalizer_commutator (stab_le_normalizer_vv h) (stab_le_normalizer_puTrans h.le hLn _)

theorem commutator_voSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le)) :
    ⁅S5.voSub h.le L (baseA _), puTrans h.le L (baseA (puAmalgam h.le))⁆ =
      S5.voSub h.le L (baseA _) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hn : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer
      ((⁅S5.voSub h.le L (baseA _), puTrans h.le L (baseA (puAmalgam h.le))⁆ : Subgroup _) :
        Set (puAmalgam h.le).Universal) :=
    le_normalizer_commutator (stab_le_normalizer_voSub h) (stab_le_normalizer_puTrans h.le hLn _)
  have hVst : Vv _ (baseA (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
    (S310.vv_le_qv_baseA h hb).trans (qv_le_stab _ _)
  refine le_antisymm (commutator_le_left_of_le_normalizer
    ((puTrans_le_stab h.le L _).trans (stab_le_normalizer_voSub h))) ?_
  exact S5B.commutator_le_of_perfect (S512N.perfect_puTrans h) (hVst.trans hn)
    ((puTrans_le_stab h.le L _).trans hn) le_rfl le_rfl

theorem bSub_le_vv (h : PUHyp M T L) :
    S5.bSub h.le L (baseA _) ≤ Vv _ (baseA (puAmalgam h.le)) :=
  (Subgroup.closure_le _).2 fun _ hv => hv.1

theorem vv_inf_dSub_le_bSub (h : PUHyp M T L) :
    Vv _ (baseA (puAmalgam h.le)) ⊓ S5.dSub h.le L (baseA _) ≤ S5.bSub h.le L (baseA _) := by
  rintro v ⟨hv, hvD⟩
  refine Subgroup.subset_closure ⟨hv, fun y hy => ?_⟩
  have hc : y * v = v * y := Subgroup.mem_centralizer_iff.1 hvD.2 y hy
  have e : ⁅v, y⁆ = 1 := by
    rw [commutatorElement_def, ← hc, mul_inv_cancel_right, mul_inv_cancel]
  rw [e]
  exact one_mem _

theorem mem_bSub_of_forall (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {v : (puAmalgam h.le).Universal} (hv : v ∈ Vv _ (baseA (puAmalgam h.le)))
    (hB : ∀ l ∈ puTrans h.le L (baseA _), ⁅v, l⁆ ∈ S5.bSub h.le L (baseA _)) :
    v ∈ S5.bSub h.le L (baseA _) := by
  have hvst : v ∈ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab _ _ (S310.vv_le_qv_baseA h hb hv)
  have hZ := S512N.commutator_mem_of_perfect (S512N.perfect_puTrans h)
    ((puTrans_le_stab h.le L _).trans (stab_le_normalizer_zm _ _))
    (Subgroup.commutator_le.2 fun x hx l hl =>
      S5B.commutator_mem_zm_of_mem_bSub h hb (isMVtx_baseA _) hx hl)
    (S310.stab_le_normalizer_bSub h _ hvst) (stab_le_normalizer_zm _ _ hvst) hB
  exact Subgroup.subset_closure ⟨hv, hZ⟩

theorem voSub_le_sup_bSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hone : S5.OneNoncentral (stab _ (baseA (puAmalgam h.le))) (puTrans h.le L (baseA _))
      (Vv _ (baseA (puAmalgam h.le))) (ZM _ (baseA (puAmalgam h.le))))
    {Y : Subgroup (puAmalgam h.le).Universal} (hYV : Y ≤ Vv _ (baseA (puAmalgam h.le)))
    (hYn : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (Y : Set _))
    (hYB : ¬ Y ≤ S5.bSub h.le L (baseA _)) :
    S5.voSub h.le L (baseA _) ≤ Y ⊔ S5.bSub h.le L (baseA _) := by
  have hBn := S310.stab_le_normalizer_bSub h (baseA (puAmalgam h.le))
  rcases hone.2 _ _ _ (S310.zm_le_bSub h (isMVtx_baseA _)) le_sup_right
      (sup_le hYV (bSub_le_vv h)) le_rfl hBn (le_normalizer_sup hYn hBn)
      (stab_le_normalizer_vv h) with h1 | h1
  · exact absurd (fun y hy => mem_bSub_of_forall h hb (hYV hy) fun l hl =>
      h1 (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hy) hl)) hYB
  · exact h1

theorem secHyp_voSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    (hne : ¬ ⁅Vv _ (baseA (puAmalgam h.le)), puTrans h.le L (baseA _)⁆ ≤
      ZM _ (baseA (puAmalgam h.le))) :
    S512N.SecHyp h (S5.voSub h.le L (baseA _)) := by
  have hVQ := S310.vv_le_qv_baseA h hb
  have hVV : ⁅Vv _ (baseA (puAmalgam h.le)), Vv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.bSub h.le L (baseA _) :=
    (le_inf (commutator_le_of_le le_rfl le_rfl)
      ((Subgroup.commutator_mono le_rfl hVQ).trans hv)).trans (vv_inf_dSub_le_bSub h)
  have e : Vv _ (baseA (puAmalgam h.le)) = ⨆ ρ : ↥{ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≤ 2}, Zv _ (ρ : Vtx (puAmalgam h.le)) :=
    iSup_subtype'
  refine ⟨hb, voSub_le_vv h, stab_le_normalizer_voSub h,
    (Subgroup.commutator_mono (voSub_le_vv h) (voSub_le_vv h)).trans hVV, fun v hv => ?_,
    fun hle => hne ?_⟩
  · rw [e] at hVV
    have hv' : v ∈ ⨆ ρ : ↥{ρ : Vtx (puAmalgam h.le) |
        (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≤ 2}, Zv _ (ρ : Vtx (puAmalgam h.le)) := by
      rw [← e]
      exact voSub_le_vv h hv
    exact S512N.sq_mem_of_iSup (fun ρ x hx =>
      (S45.isElemAbelian_zv _ h.hyp20 h.critDist_pos _).2 x hx) hVV v hv'
  · have h1 : ⁅S5.voSub h.le L (baseA _), puTrans h.le L (baseA (puAmalgam h.le))⁆ ≤
        ZM _ (baseA (puAmalgam h.le)) :=
      Subgroup.commutator_le.2 fun x hx l hl =>
        S5B.commutator_mem_zm_of_mem_bSub h hb (isMVtx_baseA _) (hle hx) hl
    rw [commutator_voSub h hb] at h1
    exact h1

theorem eq_top_of_isInv (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hone : S5.OneNoncentral (stab _ (baseA (puAmalgam h.le))) (puTrans h.le L (baseA _))
      (Vv _ (baseA (puAmalgam h.le))) (ZM _ (baseA (puAmalgam h.le))))
    {V : Subgroup (puAmalgam h.le).Universal} (hVo : V ≤ S5.voSub h.le L (baseA _))
    {S : Type} [CommGroup S] {p : ↥V →* S}
    {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)
    {S₁ : Subgroup S} (hne : S₁ ≠ ⊥) (hS₁ : S512N.IsInv ρ S₁) : S₁ = ⊤ := by
  have hmemP : ∀ a : ↥V, (a : (puAmalgam h.le).Universal) ∈ (S₁.comap p).map V.subtype ↔
      p a ∈ S₁ := by
    intro a
    constructor
    · rintro ⟨a', ha', he⟩
      have : a' = a := Subtype.ext he
      rw [← this]
      exact ha'
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hPV : (S₁.comap p).map V.subtype ≤ V := Subgroup.map_subtype_le _
  have hBn := S310.stab_le_normalizer_bSub h (baseA (puAmalgam h.le))
  have hPn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (((S₁.comap p).map V.subtype : Subgroup _) : Set _) := by
    have key : ∀ g ∈ stab _ (baseA (puAmalgam h.le)), ∀ x ∈ (S₁.comap p).map V.subtype,
        g * x * g⁻¹ ∈ (S₁.comap p).map V.subtype := by
      intro g hg x hx
      have hxV := hPV hx
      have hgx : g * x * g⁻¹ ∈ V := S36E.conj_mem hs.hMA hg hxV
      have h1 := (hmemP ⟨x, hxV⟩).1 hx
      refine (hmemP ⟨_, hgx⟩).2 ?_
      rw [← hs.conj ⟨g, hg⟩ ⟨x, hxV⟩ hgx]
      exact hS₁ ⟨g, hg⟩ _ h1
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key g hg x, fun hx => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hPB : ¬ (S₁.comap p).map V.subtype ≤ S5.bSub h.le L (baseA _) := by
    intro hle
    apply hne
    rw [eq_bot_iff]
    intro s hs1
    obtain ⟨a, rfl⟩ := hs.surj s
    rw [Subgroup.mem_bot, hs.ker]
    exact ⟨a.2, hle ((hmemP a).2 hs1)⟩
  have hVle := voSub_le_sup_bSub h hb hone ((hPV.trans hVo).trans (voSub_le_vv h)) hPn hPB
  rw [eq_top_iff]
  intro s _
  obtain ⟨a, rfl⟩ := hs.surj s
  have ha := hVle (hVo a.2)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (((hPV.trans hVo).trans (voSub_le_vv h)).trans ((S310.vv_le_qv_baseA h hb).trans
      ((qv_le_stab _ _).trans hBn)))] at ha
  obtain ⟨x, hx, b, hbB, hab⟩ := ha
  have hxV := hPV hx
  have hbV : b ∈ V := by
    have e : b = x⁻¹ * a := by rw [← hab]; group
    rw [e]
    exact mul_mem (inv_mem hxV) a.2
  have e : p a = p ⟨x, hxV⟩ * p ⟨b, hbV⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hab.symm
  rw [e, (hs.ker ⟨b, hbV⟩).2 ⟨hbV, hbB⟩, mul_one]
  exact (hmemP ⟨x, hxV⟩).1 hx

theorem index_fixV_le (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {V : Subgroup (puAmalgam h.le).Universal} (hVV : V ≤ Vv _ (baseA (puAmalgam h.le)))
    {S : Type} [CommGroup S] {p : ↥V →* S}
    {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)
    {W E : Subgroup (puAmalgam h.le).Universal} {δ : Vtx (puAmalgam h.le)}
    (hWst : W ≤ stab _ (baseA (puAmalgam h.le)))
    (hVW : V ≤ W ⊔ S5.bSub h.le L (baseA _))
    (hEst : E ≤ stab _ (baseA (puAmalgam h.le)))
    (hpair : ⁅W ⊓ Qv _ δ, E⁆ ≤ ZM _ (baseA (puAmalgam h.le))) :
    (fixV ((E.subgroupOf (stab _ (baseA (puAmalgam h.le)))).map ρ)).index ≤
      (Qv _ δ).relIndex W := by
  have := S310.finite_stab_of_isMVtx h (isMVtx_baseA (puAmalgam h.le))
  have hBn := S310.stab_le_normalizer_bSub h (baseA (puAmalgam h.le))
  have hBst : S5.bSub h.le L (baseA _) ≤ stab _ (baseA (puAmalgam h.le)) :=
    (bSub_le_vv h).trans ((S310.vv_le_qv_baseA h hb).trans (qv_le_stab _ _))
  have hVst : V ≤ stab _ (baseA (puAmalgam h.le)) :=
    hVV.trans ((S310.vv_le_qv_baseA h hb).trans (qv_le_stab _ _))
  have hAB : V ≤ Subgroup.normalizer ((V ⊓ S5.bSub h.le L (baseA _) : Subgroup _) :
      Set (puAmalgam h.le).Universal) :=
    hVst.trans (S310.le_normalizer_inf hs.hMA hBn)
  rw [hs.index_fixV hEst hAB]
  have hsub : V ⊓ ((W ⊓ Qv _ δ) ⊔ S5.bSub h.le L (baseA _)) ≤
      S36E.fixSec V (V ⊓ S5.bSub h.le L (baseA _)) E hAB := by
    intro x hx
    have hxV : x ∈ V := hx.1
    have hxH : x ∈ (W ⊓ Qv _ δ) ⊔ S5.bSub h.le L (baseA _) := hx.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      ((inf_le_left.trans hWst).trans hBn)] at hxH
    obtain ⟨w, hw, c, hc, rfl⟩ := hxH
    refine ⟨hxV, fun e he => Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
    · exact mul_mem (S36E.conj_mem hs.hMA (hEst he) hxV) (inv_mem hxV)
    · have e1 : e * (w * c) * e⁻¹ * (w * c)⁻¹ =
          ⁅e, w⁆ * (w * (e * c * e⁻¹ * c⁻¹) * w⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      refine mul_mem ?_ (S36E.conj_mem hBn (hWst hw.1) (mul_mem
        (S36E.conj_mem hBn (hEst he) hc) (inv_mem hc)))
      have h1 : ⁅e, w⁆ ∈ ⁅W ⊓ Qv _ δ, E⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator he hw
      exact S310.zm_le_bSub h (isMVtx_baseA _) (hpair h1)
  calc (S36E.fixSec V (V ⊓ S5.bSub h.le L (baseA _)) E hAB).relIndex V ≤
        (V ⊓ ((W ⊓ Qv _ δ) ⊔ S5.bSub h.le L (baseA _))).relIndex V :=
        Subgroup.relIndex_le_of_le_left hsub (relIndex_ne_zero_of_le hVst)
    _ = ((W ⊓ Qv _ δ) ⊔ S5.bSub h.le L (baseA _)).relIndex V := Subgroup.inf_relIndex_left _ _
    _ ≤ (Qv _ δ).relIndex W := relIndex_le_of_le_sup hVW (hWst.trans hBn) (sup_le hWst hBst)

theorem card_map_eq (h : PUHyp M T L)
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    {V : Subgroup (puAmalgam h.le).Universal} (hVV : V ≤ Vv _ (baseA (puAmalgam h.le)))
    (hsec : S512N.SecHyp h V)
    {S : Type} [CommGroup S] {p : ↥V →* S}
    {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)
    (hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤)
    {E : Subgroup (puAmalgam h.le).Universal} (hEst : E ≤ stab _ (baseA (puAmalgam h.le)))
    (hE2 : IsPGroup 2 E) :
    Nat.card ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ) =
      (Qv _ (baseA (puAmalgam h.le))).relIndex E := by
  have := hsec.finite_S hs
  have hS₀ : S512N.IsInv ρ (⊤ : Subgroup S) := fun _ _ _ => Subgroup.mem_top _
  have htop : (⊤ : Subgroup S) ≠ ⊥ := by
    have := hsec.nontrivial_S hs
    exact top_ne_bot
  have hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ ≤ ⊤ → S₁ = ⊤ :=
    fun S₁ h1 h2 _ => hirr S₁ h1 h2
  have hQ1 : ∀ g : ↥(stab (puAmalgam h.le) (baseA _)),
      (g : (puAmalgam h.le).Universal) ∈ Qv _ (baseA (puAmalgam h.le)) → ρ g = 1 := by
    intro g hg
    refine (hs.rho_eq_one_iff g).2 fun x hx => Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mul_mem (S36E.conj_mem hs.hMA g.2 hx) (inv_mem hx)
    · have h1 : (g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹ * x⁻¹ ∈
          ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ := by
        rw [Subgroup.commutator_comm, ← commutatorElement_def]
        exact Subgroup.commutator_mem_commutator hg (hVV hx)
      refine vv_inf_dSub_le_bSub h (Subgroup.mem_inf.2 ⟨?_, hv h1⟩)
      exact mul_mem (S36E.conj_mem (stab_le_normalizer_vv h) g.2 (hVV hx)) (inv_mem (hVV hx))
  have hker : ρ.ker ⊓ E.subgroupOf (stab (puAmalgam h.le) (baseA _)) =
      (Qv _ (baseA (puAmalgam h.le))).subgroupOf (stab (puAmalgam h.le) (baseA _)) ⊓
        E.subgroupOf (stab (puAmalgam h.le) (baseA _)) := by
    ext g
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨hg, hgE⟩
      refine ⟨hsec.mem_qv_of_restrict_eq_one hs hS₀ htop hmin ?_ ?_, hgE⟩
      · ext s
        simp [S512N.coe_restrict_apply, hg]
      · obtain ⟨e, he⟩ := hE2 ⟨g, hgE⟩
        exact ⟨e, by simpa using congrArg Subtype.val he⟩
    · rintro ⟨hgQ, hgE⟩
      exact ⟨hQ1 g hgQ, hgE⟩
  rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, hker, Subgroup.inf_relIndex_right,
    Subgroup.relIndex_subgroupOf hEst]

omit [Finite G] in
theorem sq_eq_one_of_mem_qLine {F : Type} [Field F] [CharP F 2] {l : Submodule F (MSP.V4 F)}
    (hl : MSP.IsLine l) {x : MSP.Sp4 F} (hx : x ∈ MSP.qLine l) : x ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := MSP.exists_map_ln₀_eq hl
  rw [MSP.qLine_map_eq, MSP.mem_map_conj] at hx
  have h1 := MSP.Q₁_sq hx
  have e : x ^ 2 = g * (g⁻¹ * x * g) ^ 2 * g⁻¹ := by simp only [sq]; group
  rw [e, h1, mul_one, mul_inv_cancel]

theorem commutator_mem_qv_of_le_qLine {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    {x y : (puAmalgam h.le).Universal} (hx : x ∈ Qv _ (baseB (puAmalgam h.le)))
    (hy : y ∈ Qv _ (baseB (puAmalgam h.le))) :
    ⁅x, y⁆ ∈ Qv _ (baseA (puAmalgam h.le)) ∧ x ^ 2 ∈ Qv _ (baseA (puAmalgam h.le)) := by
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  have hTl' := S512T.imSp_le_of_imM_le_vPre h.le (by rw [← puAmalgam.qv_baseB]; exact hTl)
  rw [puAmalgam.qv_baseB] at hx hy
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨t', ht', rfl⟩ := hy
  have hat : a t ∈ MSP.qLine l := hTl' ⟨t, ht, rfl⟩
  have hat' : a t' ∈ MSP.qLine l := hTl' ⟨t', ht', rfl⟩
  have h2 : ∀ m : ↥M, (m : G) ∈ T → ∃ e : ℕ, (m : G) ^ 2 ^ e = 1 := fun m hm => by
    obtain ⟨e, he⟩ := h.isPGroup ⟨m, hm⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
  have ht'T : (t' : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'
  rw [S5B.qv_baseA_eq h]
  constructor
  · rw [← map_commutatorElement]
    refine (S512N.ofA_mem_imM_iff h.le _).2 (S5B.mem_pCoreOf_of_ker h hd ?_ (h2 _ ?_))
    · rw [map_commutatorElement, commutatorElement_def, S5.qLine_comm hl hat hat',
        mul_inv_cancel_right, mul_inv_cancel]
    · have := commutatorElement_mem htT ht'T
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
      exact this
  · rw [← map_pow]
    refine (S512N.ofA_mem_imM_iff h.le _).2 (S5B.mem_pCoreOf_of_ker h hd ?_ (h2 _ ?_))
    · rw [map_pow]
      exact sq_eq_one_of_mem_qLine hl hat
    · simpa using pow_mem htT 2

end Base

end S512L

end CFSG.Quasithin.MS93

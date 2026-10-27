module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem17B
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsTen
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem16E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem rconj_eq_conjSubgroup_ch617 (X : Subgroup G) (g : G) : rconj X g = conjSubgroup X g := by
  ext x
  rw [mem_rconj, mem_conjSubgroup_iff]

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem uA_eq_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    L128A.uA (ch6ZS T L V) (zCh611 T) = uCh611 T L V := by
  show conjClosure (ch6ZS T L V) (Subgroup.normalizer (zCh611 T : Set G)) = uCh611 T L V
  rw [h.normalizer_Z_eq_ch617 h331 h432 h512 h614 h615]

theorem X_eq_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {l : G}
    (hl : l ∈ Subgroup.normalizer (ch6ZS T L V : Set G)) :
    rconj (L128A.wA (ch6ZS T L V) (zCh611 T)) l =
      conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  ext x
  rw [rconj_eq_conjSubgroup_ch617, mem_conjSubgroup_iff, Subgroup.mem_inf, Subgroup.mem_inf,
    mem_conjSubgroup_iff, h.uA_eq_ch617 h331 h432 h512 h614 h615]
  apply and_congr_right
  intro _
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc s hs
    have hs' : l * s * l⁻¹ ∈ ch6ZS T L V := (Subgroup.mem_normalizer_iff.mp hl s).mp hs
    have h1 := hc _ hs'
    calc s * x = l⁻¹ * ((l * s * l⁻¹) * (l * x * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * x * l⁻¹) * (l * s * l⁻¹)) * l := by rw [h1]
      _ = x * s := by group
  · intro hc s hs
    have hs' : l⁻¹ * s * l ∈ ch6ZS T L V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hl) s).mp hs
      simpa using this
    have h1 := hc _ hs'
    calc s * (l * x * l⁻¹) = l * ((l⁻¹ * s * l) * x) * l⁻¹ := by group
      _ = l * (x * (l⁻¹ * s * l)) * l⁻¹ := by rw [h1]
      _ = l * x * l⁻¹ * s := by group

theorem E_eq_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {l : G}
    (hg : L128A.Good (zCh611 T) (lsCh617 T L V) l) :
    L128A.wA (ch6ZS T L V) (zCh611 T) ⊓ rconj (L128A.wA (ch6ZS T L V) (zCh611 T)) l =
      uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) l := by
  have S := h.setting_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  rw [S.wA_inf_rconj_eq hg, rconj_eq_conjSubgroup_ch617, h.uA_eq_ch617 h331 h432 h512 h614 h615]

theorem good_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {l : G} (hl : l ∈ lsCh617 T L V)
    (hlH : l ∉ hCh611 T) : L128A.Good (zCh611 T) (lsCh617 T L V) l :=
  ⟨hl, by rw [h.normalizer_Z_eq_ch617 h331 h432 h512 h614 h615]; exact hlH⟩

theorem V_le_ls_ch617 : V ≤ lsCh617 T L V := by
  classical
  obtain ⟨d, hdLS, -, -, hfix⟩ := h.exists_diag_ch617
  have hV := h.toHyp611.isElemAbelian
  have hdN : d ∈ Subgroup.normalizer (V : Set G) :=
    h.toHyp611.L_le_normalizer (ls_le_ch617 hdLS).1
  let f : ↥V → ↥V := fun w => ⟨w * d * (w : G)⁻¹ * d⁻¹, by
    have : d * (w : G)⁻¹ * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hdN _).mp (V.inv_mem w.2)
    have e : (w : G) * d * (w : G)⁻¹ * d⁻¹ = w * (d * (w : G)⁻¹ * d⁻¹) := by group
    rw [e]
    exact V.mul_mem w.2 this⟩
  have hinj : Function.Injective f := by
    intro w w' hww
    have h1 : (w : G) * d * (w : G)⁻¹ * d⁻¹ = (w' : G) * d * (w' : G)⁻¹ * d⁻¹ :=
      congrArg Subtype.val hww
    have hx : (w' : G)⁻¹ * w ∈ V := V.mul_mem (V.inv_mem w'.2) w.2
    have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
      B2F.isElemAbelian_comm hV ha hb
    have hfixw : d * ((w' : G)⁻¹ * w) * d⁻¹ = (w' : G)⁻¹ * w := by
      have hdw : d * (w : G)⁻¹ * d⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp hdN _).mp (V.inv_mem w.2)
      have hdw' : d * (w' : G)⁻¹ * d⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp hdN _).mp (V.inv_mem w'.2)
      have h2 : (w : G) * (d * (w : G)⁻¹ * d⁻¹) = (w' : G) * (d * (w' : G)⁻¹ * d⁻¹) := by
        calc (w : G) * (d * (w : G)⁻¹ * d⁻¹) = (w : G) * d * (w : G)⁻¹ * d⁻¹ := by group
          _ = (w' : G) * d * (w' : G)⁻¹ * d⁻¹ := h1
          _ = _ := by group
      have h3 : (w' : G)⁻¹ * w = (d * (w' : G)⁻¹ * d⁻¹) * (d * (w : G)⁻¹ * d⁻¹)⁻¹ := by
        calc (w' : G)⁻¹ * w = (w' : G)⁻¹ * (w * (d * (w : G)⁻¹ * d⁻¹)) *
              (d * (w : G)⁻¹ * d⁻¹)⁻¹ := by group
          _ = (w' : G)⁻¹ * ((w' : G) * (d * (w' : G)⁻¹ * d⁻¹)) * (d * (w : G)⁻¹ * d⁻¹)⁻¹ := by
              rw [h2]
          _ = _ := by group
      calc d * ((w' : G)⁻¹ * w) * d⁻¹ =
            (d * (w' : G)⁻¹ * d⁻¹) * (d * (w : G)⁻¹ * d⁻¹)⁻¹ := by group
        _ = (w' : G)⁻¹ * w := h3.symm
    have := hfix _ hx hfixw
    exact Subtype.ext (by
      calc (w : G) = (w' : G) * ((w' : G)⁻¹ * w) := by group
        _ = w' := by rw [this, mul_one])
  have hsurj := Finite.surjective_of_injective hinj
  intro v hv
  obtain ⟨w, hw⟩ := hsurj ⟨v, hv⟩
  have e : v = (w * d * (w : G)⁻¹) * d⁻¹ := by
    have := congrArg Subtype.val hw
    simp only [f] at this
    rw [← this]
  rw [e]
  have hwd : (w : G) * d * (w : G)⁻¹ ∈ lsCh617 T L V :=
    (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_ls_ch617 (h.toHyp611.le_T w.2)) d).mp hdLS
  exact (lsCh617 T L V).mul_mem hwd ((lsCh617 T L V).inv_mem hdLS)

theorem one_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {l : G}
    (hl : l ∈ lsCh617 T L V) (hlH : l ∉ hCh611 T) :
    centerOf (uCh611 T L V) ⊓ conjSubgroup (centerOf (uCh611 T L V)) l = ⊥ := by
  have S := h.setting_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hg := h.good_ch617 h331 h432 h512 h614 h615 hl hlH
  have hU := h.uA_eq_ch617 h331 h432 h512 h614 h615
  have h2 := S.ten_two hg
  have h9 := S.V₁_inf_rconj_centerOf hg
  rw [hU, rconj_eq_conjSubgroup_ch617] at h2 h9
  by_contra hne
  have hN : centerOf (lsCh617 T L V ⊔ L128A.uA (ch6ZS T L V) (zCh611 T)) ≠ ⊥ := by
    rw [hU, ← h2]
    exact hne
  apply S.omegaOneCenter_inf_centerOf_ne_bot hg hN
  rw [eq_bot_iff]
  rintro x ⟨hxZ, hxI⟩
  rw [hU, ← h2] at hxI
  have : x ∈ zCh611 T ⊓ conjSubgroup (centerOf (uCh611 T L V)) l := ⟨hxZ, hxI.2⟩
  rw [h9] at this
  exact this

theorem two_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {l : G}
    (hl : l ∈ lsCh617 T L V) (hlH : l ∉ hCh611 T) :
    centerOf (uCh611 T L V) ⊓ conjSubgroup (uCh611 T L V) l =
      (centerOf (uCh611 T L V) ⊓ conjSubgroup (centerOf (uCh611 T L V)) l) ⊔ zCh611 T := by
  have S := h.setting_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hg := h.good_ch617 h331 h432 h512 h614 h615 hl hlH
  have h1 := S.ten_one hg
  rw [h.uA_eq_ch617 h331 h432 h512 h614 h615, rconj_eq_conjSubgroup_ch617,
    rconj_eq_conjSubgroup_ch617] at h1
  exact h1

theorem wA_eq_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    L128A.wA (ch6ZS T L V) (zCh611 T) =
      uCh611 T L V ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  show L128A.uA (ch6ZS T L V) (zCh611 T) ⊓ _ = _
  rw [h.uA_eq_ch617 h331 h432 h512 h614 h615]

theorem nine_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {l : G}
    (hl : l ∈ lsCh617 T L V) (hlH : l ∉ hCh611 T) :
    V ≤ (conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
      centralizerMod (centerOf (uCh611 T L V)) (hCh611 T) (uCh611 T L V) := by
  have S := h.setting_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hg := h.good_ch617 h331 h432 h512 h614 h615 hl hlH
  have hU := h.uA_eq_ch617 h331 h432 h512 h614 h615
  have hP := (S.pCoreOf_sup_eq_wA_sup hg).1
  rw [h.X_eq_ch617 h331 h432 h512 h614 h615 (ls_le_ch617 hl).2,
    h.wA_eq_ch617 h331 h432 h512 h614 h615, hU] at hP
  have hVP : V ≤ pCoreOf 2 (lsCh617 T L V ⊔ uCh611 T L V) := by
    refine le_pCoreOf_of_le_normalizer 2 (h.V_le_ls_ch617.trans le_sup_left) (sup_le ?_ ?_)
      (B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian)
    · exact fun x hx => h.toHyp611.L_le_normalizer (ls_le_ch617 hx).1
    · exact fun x hx => h.toHyp611.T_le_normalizer (h.uCh611_le_T h331 h432 h512 h614 h615 hx)
  rw [hP] at hVP
  refine hVP.trans (sup_le ?_ le_sup_left)
  exact inf_le_left.trans ((h.U_le_CH_ch616 h331 h432 h512 h614 h615).trans le_sup_right)

end Hyp6Sec2

end CFSG.Quasithin.H13

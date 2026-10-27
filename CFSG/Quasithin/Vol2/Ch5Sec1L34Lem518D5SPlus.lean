module

public import CFSG.Quasithin.H13.F112PlusDefs
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5S
public import CFSG.Quasithin.Background.C2PushY
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Setting

variable {G : Type} [Group G]

namespace Setting518D5

variable [Finite G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem false_of_pCoreOf_eq_bot_plus (hF : L2TorusFact) (h311 : Theorem311Stmt)
    (h5114 : Stmt5_1_14_first) (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hDSC : DSCStatementPlus) {U : Subgroup G} (hU : ParData518 T H B D U)
    (hO : pCoreOf 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  have hh := h.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  set S := s518 T H B D with hSdef
  set Y := sd5 T L H B D D₅ with hYdef
  obtain ⟨hST, -, hTKS, hOMS, hOMpS, hSN⟩ := s.S_facts h510 h331 hR
  obtain ⟨-, hUTK, hUN, φ, hφs, hφk⟩ := hU
  have hTK := h.isSylowTwoOf_inf_K
  have hTKN : T ⊓ K ≤ Subgroup.normalizer (U : Set G) := hTKS.trans (le_sup_right.trans hUN)
  obtain ⟨hL2K₂, hnsK₂, -, hTK₂, hBorK₂⟩ := oTwoUpper_parabolic_facts rfl hTK hUTK hTKN φ hφs hφk
  set K₂ := oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)) with hK₂def
  have hK₂K : K₂ ≤ K := (oTwoUpper_le _).trans inf_le_left
  have hTMp := h.T_le_Mp
  have hSMp : S ≤ Subgroup.normalizer (K : Set G) := hST.trans hTMp
  have hSK₂ : S ≤ Subgroup.normalizer (K₂ : Set G) := fun x hx =>
    Hyp5_1_14.mem_normalizer_oTwoUpper_inf (hSMp hx) (hUN (Subgroup.mem_sup_right hx))
  have hSK₂eq : S ⊓ K₂ = T ⊓ K₂ :=
    le_antisymm (inf_le_inf_right _ hST)
      (le_inf ((inf_le_inf_left T hK₂K).trans hTKS) inf_le_right)
  obtain ⟨hSY, -, hiso⟩ := s.sd5_facts hF h311 h5114 h510 h331 hR
  have hborY := s.borelOf_sd5 hF h311 h5114 h510 h331 hR
  have hSYle : S ≤ Y := le_sup_right
  have hSYeq : S ⊓ Y = S := inf_eq_left.mpr hSYle
  obtain ⟨-, -, hBorel, hBhall, -⟩ := h510 G T M L H B D n h.hyp h.notation59
  have hMK := h.hyp.borel_eq hBorel
  have hTKM : IsSylowTwoOf (T ⊓ K) (M ⊓ K) :=
    A4.isSylowTwoOf_mono hTK (inf_le_inf_right _ hh.T_le) inf_le_right
  have hMKeq : B ⊔ (T ⊓ K) = M ⊓ K := sup_eq_of_isHall_isSylow hBhall hTKM
  have hYN : M ⊓ K ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← hMKeq]
    refine sup_le ?_ ?_
    · exact le_normalizer_sup_of_le (s.B_le_normalizer_z518 hF h331 hR)
        ((le_sup_right.trans le_sup_left).trans hSN)
    · exact inf_le_left.trans (le_normalizer_sup_of_le (s.T_le_normalizer_z518 hF)
        (le_sup_right.trans hSN))
  have hBorK₂M : borelOf K₂ S ≤ M ⊓ K := by
    intro x hx
    have hx2 : x ∈ Subgroup.normalizer ((T ⊓ K₂ : Subgroup G) : Set G) := by
      have hx' := hx.2
      rw [hSK₂eq] at hx'
      exact hx'
    rw [hMK]
    exact ⟨hK₂K hx.1, hBorK₂ ⟨hx.1, hx2⟩⟩
  have hcharM : CharTwo M :=
    charTwo_of_inH' hh.qtke hh.sylow ⟨hh.T_le, pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1⟩
  have hcharMp := h.charTwo_Mp h5114
  have hDM : D₅ ≤ M := s.D₅_le.trans (s.hyp.notation59.2.1.1.trans (inf_le_left.trans hh.L_le))
  have hYM : Y ≤ M :=
    sup_le (sup_le (inf_le_left.trans hh.T_le) hDM) (hST.trans hh.T_le)
  have hc1 : CharTwo (K₂ ⊔ S ⊔ borelOf Y S) := by
    rw [hborY]
    refine C2Push.charTwo_of_pCoreOf_le hcharMp (hOMpS.trans (le_sup_right.trans le_sup_left)) ?_
    exact sup_le (sup_le (hK₂K.trans Subgroup.le_normalizer) hSMp) hSMp
  have hc2 : CharTwo (Y ⊔ S ⊔ borelOf K₂ S) :=
    C2Push.charTwo_of_pCoreOf_le hcharM (hOMS.trans (le_sup_right.trans le_sup_left))
      (sup_le (sup_le hYM (hST.trans hh.T_le)) (hBorK₂M.trans inf_le_left))
  have hlistK₂ : IsRankOneListed (oTwoQuot ↥K₂) := Or.inl ⟨2, by norm_num, hL2K₂⟩
  have hiso' : Nonempty (oTwoQuot ↥Y ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥Y ≃* ↥(Sz 0)) :=
    hiso
  have hlistY : IsRankOneListed (oTwoQuot ↥Y) := by
    rcases hiso' with h1 | h1
    · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))
    · exact Or.inr (Or.inl ⟨0, h1⟩)
  have hhyp : Hyp111 K₂ Y S := by
    refine ⟨⟨inferInstance, pCoreOf_isPGroup 2 _, hSK₂, by rw [hSK₂eq]; exact hTK₂, hlistK₂, ?_,
      hc1⟩, ⟨inferInstance, pCoreOf_isPGroup 2 _, hSYle.trans Subgroup.le_normalizer,
        by rw [hSYeq]; exact hSY, hlistY, hBorK₂M.trans hYN, hc2⟩, ?_⟩
    · rw [hborY]
      exact hSK₂
    · rw [sup_eq_left.mpr (hSYle.trans le_sup_right)]
      exact hO
  have hqt : IsQuasithinSub (K₂ ⊔ Y ⊔ S) := by
    intro p hp hp2 R _ hR' hR2
    exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
      (pRank_le_two_of_isTwoLocal hh.qtke hp hp2 ⟨R, hR', hR2, rfl⟩)
  have hnorm : (S.subgroupOf (S ⊔ borelOf Y S)).Normal := by
    rw [hborY, sup_idem, Subgroup.subgroupOf_self]
    infer_instance
  have hcen : centerOf (K₂ ⊔ S ⊔ borelOf Y S) ≠ ⊥ := by
    rw [hborY, sup_assoc, sup_idem]
    have hZne : quasithinOmegaOneCenter T ≠ ⊥ :=
      CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot hh.sylow.1 hh.T_ne_bot
    have hZT := quasithinOmegaOneCenter_le_inf T
    have hOMT : pCoreOf 2 M ≤ T := F7.isSylowTwoOf_pCoreOf_le (hh.isSylowTwoOf hh.T_le)
    have hZH := (h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34).2.1.1
    have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
    have hTH : T ≤ H := h.hyp.hStar.1.1
    have hle : quasithinOmegaOneCenter T ≤ centerOf (K₂ ⊔ S) := by
      intro z hz
      have hzT := hZT hz
      refine ⟨Subgroup.mem_sup_right (hOMS (hcharM ⟨hh.T_le hzT.1, ?_⟩)), ?_⟩
      · exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hOMT) hzT.2
      · exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
          (sup_le (hK₂K.trans (oTwoUpper_le H)) (hST.trans hTH))) (hZC hz)
    intro hbot
    exact hZne (le_bot_iff.mp (hle.trans hbot.le))
  exact hDSC G K₂ Y S hhyp hqt (Or.inr hnorm) hnsK₂ hcen hSYle hiso'

end Setting518D5

end Setting

end CFSG.Quasithin.H13

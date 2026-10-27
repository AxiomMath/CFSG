module

public import CFSG.Quasithin.Vol2.Ch4Sec3C57Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalMain

public section

namespace CFSG.Quasithin.H13.Ch4.C57

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {H M₀ R K : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_D {g : G} (hgR : g ∈ Subgroup.normalizer (R : Set G))
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((baum R ⊓ Subgroup.centralizer (blockU K : Set G) ⊓
      Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
  C5.mem_normalizer_inf
    (C5.mem_normalizer_inf (normalizer_le_normalizer_baum R hgR)
      (C5.mem_normalizer_centralizer (C1.mem_normalizer_blockU hgK)))
    (C5.mem_normalizer_centralizer hgK)

omit [Finite G] in
theorem mem_normalizer_Q {g : G} (hgR : g ∈ Subgroup.normalizer (R : Set G))
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((baum R ⊓ Subgroup.centralizer (blockU K : Set G) : Subgroup G) :
      Set G) :=
  C5.mem_normalizer_inf (normalizer_le_normalizer_baum R hgR)
    (C5.mem_normalizer_centralizer (C1.mem_normalizer_blockU hgK))

namespace Setup

variable (h : Setup H M₀ R K)
include h

theorem relIndex_eq_two_of_lin (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type K n) ∨ IsAltType K 3) :
    (M₀ ⊓ Subgroup.normalizer (K : Set G)).relIndex M₀ = 2 := by
  have hLsh := h.short
  have hRN := h.R_le_normalizer_K
  have hmin := h.isMinimalParabolic
  obtain ⟨hBN, hBsyl⟩ := C56.baumann_single hmin h.block hL h.thompson h.H_eq hRN
  obtain ⟨q, W, hq2, hWU, hidxQ, hidxW, hcent, hcomm, hZ, hgen, -⟩ :=
    naturalModuleStructure G R H K hmin h.charTwo h.block hL h.thompson h.H_eq hRN
  set B := baum R with hBdef
  set U := blockU K with hUdef
  set Q := B ⊓ Subgroup.centralizer (U : Set G) with hQdef
  have hBR : B ≤ R := inf_le_left
  have hB2 : IsPGroup 2 B := h.isPGroup_R.to_le hBR
  have hBU : B ≤ Subgroup.normalizer (U : Set G) := fun _ hb => C1.mem_normalizer_blockU (hBN hb)
  set X := K ⊔ B with hXdef
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hBN
  have hC111X : X ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 X :=
    C1.inf_centralizer_blockU_eq hLsh le_sup_left hXN fun _ hg =>
      C1.exists_pow_mem_of_mem_sup hB2 hBN hg
  have hQX : Q = pCoreOf 2 X := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · have : g ∈ X ⊓ Subgroup.centralizer (U : Set G) := ⟨(le_sup_right : B ≤ X) hg.1, hg.2⟩
      rwa [hC111X] at this
    · have h1 : g ∈ X ⊓ Subgroup.centralizer (U : Set G) := by rw [hC111X]; exact hg
      exact ⟨hBsyl.pCoreOf_le hg, h1.2⟩
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQX]
    exact le_sup_left.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X)
  have hUQ : U ≤ Q := by
    rw [hQX]
    exact (C1.blockU_le_blockQ hLsh).trans
      (C1.le_pCoreOf_of_normalized ((C1.blockQ_le K).trans le_sup_left)
        (fun _ hg => C1.mem_normalizer_blockQ (hXN hg)) (C1.blockQ_isPGroup K))
  have hR1 : C5.Rank1 B Q U W q :=
    { U_le_Q := hUQ
      Q_le_B := inf_le_left
      B_le_normQ := fun _ hb => C5.mem_normalizer_inf (Subgroup.le_normalizer hb)
        (C5.mem_normalizer_centralizer (hBU hb))
      B_le_normU := hBU
      Q_eq := rfl
      W_le_U := hWU
      idx_Q := hidxQ
      idx_W := hidxW
      q_ne_zero := by omega
      cent_y := hcent
      comm_UB := hcomm
      U_comm := (C1.elemAb2_blockU hLsh).1 }
  obtain ⟨x, hx, hx1P⟩ := h.exists_conj_not_le
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := h.normal_R hx
  have hxB : x ∈ Subgroup.normalizer (B : Set G) := normalizer_le_normalizer_baum R hxR
  have hQP : Q ≤ pCoreOf 2 H := by
    rw [← h.R_inf_centralizer_eq]
    exact inf_le_inf_right _ hBR
  have hx1 : ¬ conjSubgroup U x ≤ Q := fun hle => hx1P (hle.trans hQP)
  have hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q := fun hle => h.conj_inv_not_le hx hx1P (hle.trans hQP)
  have hxK : x ∉ Subgroup.normalizer (K : Set G) := h.not_mem_normalizer hx1P
  have hUK : U ≤ K := (C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le K)
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := C1.blockU_sq hLsh
  obtain ⟨hD, hDx⟩ := hR1.Q_eq_sup_centralizer hxB hx1 hUK hKQ hZ (hgen x hxB hx1 hx2)
  set D := Q ⊓ Subgroup.centralizer (K : Set G) with hDdef
  have hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u := fun u hu a ha =>
    Subgroup.mem_centralizer_iff.mp ha.2 u (hUK hu)
  have hDR : D ≤ R := inf_le_left.trans (inf_le_left.trans hBR)
  have hsq : C5.sqSub D = ⊥ := by
    refine h.eq_bot hx hxK (C5.sqSub_le_self.trans hDR) ?_ ?_ ?_ ?_
    · intro k hk
      refine conjSubgroup_eq_iff_mem_normalizer.mp (C5.conjSubgroup_sqSub_of_mem_normalizer ?_)
      exact C5.le_normalizer_of_commute (U := K) (D := D)
        (fun k' hk' a ha => Subgroup.mem_centralizer_iff.mp ha.2 k' hk') hk
    · intro r hr
      exact conjSubgroup_eq_iff_mem_normalizer.mp (C5.conjSubgroup_sqSub_of_mem_normalizer
        (mem_normalizer_D (Subgroup.le_normalizer hr) (hRN hr)))
    · intro g hg
      exact conjSubgroup_eq_iff_mem_normalizer.mp (C5.conjSubgroup_sqSub_of_mem_normalizer
        (mem_normalizer_D (h.normal_R hg.1) hg.2))
    · exact conjSubgroup_eq_iff_mem_normalizer.mp (hR1.conj_sqSub hU2 hD hDc hxB hx1 hx2)
  have hD2 : C5.ElemAb2 D :=
    ⟨C5.comm_of_sq_eq_one (C5.sqSub_eq_bot_iff.mp hsq), C5.sqSub_eq_bot_iff.mp hsq⟩
  have hA : ∀ A, IsMaxElemAbelian R A → A ≤ B := fun A hA =>
    (GammaExtra.le_thompsonJ hA).trans (C5.thompsonJ_le_baum' R)
  obtain ⟨hQmax, -, -, hall, -, -⟩ :=
    hR1.A_R_structure hBR hA hq2 hU2 hxB hx1 hx2 hD hDc hD2 hDx
  refine relIndex_eq_two h.maxN (fun g hg => mem_normalizer_Q (h.normal_R hg.1) hg.2) hx
    (fun hxQ => hx1 ((C5.conjSubgroup_mono hUQ x).trans (le_of_eq hxQ))) fun m hm => ?_
  exact (hall _).mp (C56.isMaxElemAbelian_conjSubgroup hQmax (h.normal_R hm))

end Setup

end CFSG.Quasithin.H13.Ch4.C57

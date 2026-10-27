module

public import CFSG.Quasithin.MS93.S4A432N
public import CFSG.Quasithin.MS93.S4A432M
public import CFSG.Quasithin.MS93.S4AInputs

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Concl

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L) {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  (hH : Hyp40 h φ) (hC : CentHyp (puAmalgam h.le)) (h42 : S42) (h431A : S431A)
  (h431B : S431B)
include h hfull hH hC h42 h431A h431B

omit hC h42 h431A h431B in
theorem zm_inf_dloc_le_zloc {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) :
    ZM (puAmalgam h.le) μ ⊓ Dloc h.le L μ ≤ Zloc h.le L μ := by
  have hUD : Uloc h.le L μ ⊓ Dloc h.le L μ = ⊥ := by
    have hUD' : Uq M T L ⊓ Dq M L = ⊥ := by
      rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq, inf_comm]
      exact hH.2.2.2.2.2.1
    rw [Uloc, Dloc, ← puTrans_inf, hUD', puTrans, Subgroup.bot_subgroupOf, transN_bot]
  have hZs : ZM (puAmalgam h.le) μ ≤ stab _ μ :=
    (zm_le_qv_self _ hμ h.critDist_pos).trans (qv_le_stab _ μ)
  have hWn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Zloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    le_normalizer_of_le_centralizer
      (Subgroup.le_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hμ))
  rintro z ⟨hz, hzD⟩
  have hz' : z ∈ ((Uloc h.le L μ ⊔ Zloc h.le L μ : Subgroup _) :
      Set (puAmalgam h.le).Universal) := by
    rw [← zm_eq_uloc_sup_zloc h hfull hμ]
    exact hz
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (((uloc_le_zm h hfull hμ).trans hZs).trans hWn)] at hz'
  obtain ⟨u, hu, w, hw, rfl⟩ := hz'
  have huD : u ∈ Dloc h.le L μ := by
    have := Subgroup.mul_mem _ hzD (Subgroup.inv_mem _ (zloc_le_dloc h μ hw))
    simpa using this
  have hu1 : u = 1 := by
    have : u ∈ Uloc h.le L μ ⊓ Dloc h.le L μ := ⟨hu, huD⟩
    rw [hUD] at this
    exact this
  subst hu1
  simpa using hw

theorem concl432_of_le {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α')
    (hi : ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Dloc h.le L α) :
    Concl432 h.le L α := by
  have hα := hs.1.1
  have hb := hH.2.1
  refine ⟨hi, fun δ hδ => ⟨?_, commutator_zm_qv_eq_of_star h hH h431B hs hα hδ⟩⟩
  obtain ⟨hδM, hZδV⟩ := zm_le_vv_of_mem_nablaSet h hα hδ
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  set N := ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) α⁆ with hNdef
  have hNZ : N ≤ Zloc h.le L α := by
    refine (le_inf ((Subgroup.commutator_mono hZδV le_rfl).trans
      (commutator_vv_qv_le_zm_of_star h hfull hH hC h42 h431A h431B hs hα))
      ((Subgroup.commutator_mono hZδV le_rfl).trans hi)).trans
      (zm_inf_dloc_le_zloc h hfull hH hα)
  have hNn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) :=
    le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp
      ((hNZ.trans (zloc_le_centralizer_stab h hfull hα))))
  have hHN : Hloc h.le L α ≤ N := by
    rw [Hloc]
    refine (Subgroup.commutator_mono (vcirc_le_conjCl_of_star h hH h431A hs hα hδ) le_rfl).trans ?_
    exact commutator_conjCl_le hNn (stab_le_normalizer_qv _ α) ((hZδV.trans hVs).trans hNn) le_rfl
  have hανδ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α δ 1) δ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := δ) (i := 1) (by rw [hδ.1]; omega)
    rwa [geo_of_le _ (show (puAmalgam h.le).treeGraph.dist α δ ≤ 1 + 1 by rw [hδ.1])] at this
  have hNq : Nat.card ↥N = Fintype.card F ^ 2 := by
    rw [hNdef, commutator_zm_qv_eq_of_star h hH h431B hs hα hδ,
      card_usup_of_star h hC hH.2.2 hb hs hδM hανδ.symm, Nat.card_eq_fintype_card]
  have hfinN : Finite ↥N := by
    have hNs : N ≤ stab (puAmalgam h.le) α := (Subgroup.commutator_mono (hZδV.trans hVs)
      (qv_le_stab _ α)).trans (Subgroup.commutator_le_self _)
    have := finite_stab h hα
    exact Finite.of_injective _ (Subgroup.inclusion_injective hNs)
  have hHq := (h431B G M T L h F inferInstance inferInstance φ hH α α' hs).2.1
  exact Subgroup.eq_of_le_of_card_ge hHN (by rw [hNq]; exact hHq)

end Concl

end CFSG.Quasithin.MS93.S4A

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem s432_of (h32 : S32) (h431A : S431A) (h431B : S431B) (h5 : S432Dual5) : S432 := by
  intro G _ _ M T L h F _ _ φ hH α α' hs
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hH.2.2⟩
  have hC := centHyp_of_S32 h32 h
  have h42 := s42_of h32
  have hb6 := (h431A G M T L h F inferInstance inferInstance φ hH α α' hs).2.2.2.2.2
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  refine concl432_of_le h hfull hH hC h42 h431A h431B hs ?_
  by_contra hCH
  have hCHall : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
      ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ := by
    intro μ hμ
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ hs.1.1 hμ
    rwa [commutator_vv_qv_le_dloc_smul_iff h]
  obtain ⟨d, hd⟩ := exists_kindAt h hfull hH.2.1 hs.1.1 hH.2.2
    (isC1_of_star h hH h431A hs hs.1.1)
  have hkall : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ → KindAt h.le L F d μ := by
    intro μ hμ
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ hs.1.1 hμ
    exact kindAt_smul h hd g
  cases d
  · exact false_of_kindAt_false h hfull hH hC h42 h431A h431B ms17i_holds hb hs hkall hCHall
  · have hb6' := h5 G M T L h F inferInstance inferInstance φ hH hb α α' hs hkall hCHall
    exact D432.Ctx.false_of_ctx ⟨hfull, hH, hC, h42, h431A, h431B, hb, hs, hkall, hCHall⟩ hb6'

theorem s432Dual5_of (h32 : S32) (h431A : S431A) (h431B : S431B) (hR : S432Dual5R) :
    S432Dual5 := by
  intro G _ _ M T L h F _ _ φ hH hb α α' hs hkall hCHall
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hH.2.2⟩
  have hb6 := (h431A G M T L h F inferInstance inferInstance φ hH α α' hs).2.2.2.2.2
  have c : D432.Ctx h φ α α' :=
    ⟨hfull, hH, centHyp_of_S32 h32 h, s42_of h32, h431A, h431B, hb, hs, hkall, hCHall⟩
  by_contra hle
  exact c.false_of_six (by omega) fun α₁ α₁' hs₁ h4 =>
    hR G M T L h F inferInstance inferInstance φ hH (by omega) α₁ α₁' hs₁ h4 hkall hCHall

end CFSG.Quasithin.MS93.S4A

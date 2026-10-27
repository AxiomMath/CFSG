module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NormLbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NotConcl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

theorem s16c1610_conj_mem_center_map {A : Type} [Group A] {F : Subgroup A} {m : A}
    (hm : ∀ h : A, h ∈ F ↔ m * h * m⁻¹ ∈ F) {x : A}
    (hx : x ∈ (Subgroup.center ↥F).map F.subtype) :
    m * x * m⁻¹ ∈ (Subgroup.center ↥F).map F.subtype := by
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
  have hmem : m * (x' : A) * m⁻¹ ∈ F := (hm x').1 x'.2
  refine Subgroup.mem_map.mpr ⟨⟨m * (x' : A) * m⁻¹, hmem⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : m⁻¹ * (g : A) * m⁻¹⁻¹ ∈ F := by
    have e : m * (m⁻¹ * (g : A) * m⁻¹⁻¹) * m⁻¹ = (g : A) := by group
    rw [hm, e]
    exact g.2
  have hc := Subgroup.mem_center_iff.mp hx' ⟨_, hg⟩
  have hc' : (m⁻¹ * (g : A) * m⁻¹⁻¹) * (x' : A) = (x' : A) * (m⁻¹ * (g : A) * m⁻¹⁻¹) :=
    congrArg Subtype.val hc
  apply Subtype.ext
  show (g : A) * (m * (x' : A) * m⁻¹) = (m * (x' : A) * m⁻¹) * (g : A)
  calc (g : A) * (m * (x' : A) * m⁻¹)
      = m * ((m⁻¹ * (g : A) * m⁻¹⁻¹) * (x' : A)) * m⁻¹ := by group
    _ = m * ((x' : A) * (m⁻¹ * (g : A) * m⁻¹⁻¹)) * m⁻¹ := by rw [hc']
    _ = (m * (x' : A) * m⁻¹) * (g : A) := by group

section Certified

variable {G : Type} [Group G] [Finite G]


theorem s16c1610_out10_of_case3 (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h : Case168_3 D V₀ V hV L) :
    Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hnorm := s16c1610_mbar_le_normalizer_lbar D hV hc h
  obtain ⟨hEx, hcard, hσ⟩ := h.1.1, h.1.2.1, h.2.2
  haveI : CFSG.IsExtraspecial 3 ↥(lBar V₀ V hV L) := hEx
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := by
    unfold lBar Mbar
    exact barSub_mono V₀ V hV hc.setting.hyp151.le
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV, ∀ n : MulAut (Vtil V₀ V hV),
      n ∈ lBar V₀ V hV L ↔ g * n * g⁻¹ ∈ lBar V₀ V hV L := fun g hg n =>
    Subgroup.mem_normalizer_iff.mp (hnorm hg) n
  have hXcard : Nat.card
      ((Subgroup.center ↥(lBar V₀ V hV L)).map (lBar V₀ V hV L).subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (lBar V₀ V hV L).subtype_injective]
    exact CFSG.IsExtraspecial.center_order_p 3 ↥(lBar V₀ V hV L)
  have hrk : rk (Vtil V₀ V hV) = 6 := by
    have h6 := h.2.1
    rwa [rk_top] at h6
  have hLcard : Nat.card (lBar V₀ V hV L) = 27 := by rw [hcard]; norm_num
  have hGL : ¬ Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) ∣
      Nat.card (lBar V₀ V hV L) := by
    rw [hLcard]
    exact s16c1610_not_dvd_card_GL_two (m := 3) (K := 27) (by norm_num) (by norm_num)
  have hSL : ¬ Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∣
      Nat.card (lBar V₀ V hV L) := by
    rw [hLcard]
    exact s16c1610_not_dvd_card_SL_four (m := 3) (K := 27) (by norm_num) (by norm_num)
      (by norm_num)
  have h6 : ¬ Nat.card (lBar V₀ V hV L) ∣ 6 := by rw [hLcard]; norm_num
  have h9 : ¬ Nat.card (lBar V₀ V hV L) ∣ 9 := by rw [hLcard]; norm_num
  have h6c : 3 = 3 → (Subgroup.center ↥(lBar V₀ V hV L)).map (lBar V₀ V hV L).subtype ≤
      lBar V₀ V hV L ∧ (Nat.card (lBar V₀ V hV L) = 3 * Nat.card
        ((Subgroup.center ↥(lBar V₀ V hV L)).map (lBar V₀ V hV L).subtype) ∨
      Nat.card (lBar V₀ V hV L) = 9 * Nat.card
        ((Subgroup.center ↥(lBar V₀ V hV L)).map (lBar V₀ V hV L).subtype)) := fun _ =>
    ⟨Subgroup.map_subtype_le _, Or.inr (by rw [hLcard, hXcard])⟩
  have hnot : ¬ Concl614 (Vtil V₀ V hV) (Mbar D.M V₀ V hV)
      ((Subgroup.center ↥(lBar V₀ V hV L)).map (lBar V₀ V hV L).subtype) := by
    refine s16c1610_not_concl614_of_normal (m := 3) (N := lBar V₀ V hV L) (by omega) le_rfl hLM ?_
      (fun g hg n hn => (hLn g hg n).1 hn) h6 hGL h9 hSL h6c
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx' ⟨n, hn⟩)).symm
  exact s16c1610_out10_of_normal_prime D hin.hx hin.h61 hin.h127 hin.h1114 hin.h1214 hin.h162
    hin.h139 h125 (Or.inl rfl)
    (s16c1610_k_lt_dParam_three D hin.hSg hin.h1219 (by rw [hσ]; simp))
    ((Subgroup.map_subtype_le _).trans hLM) hXcard
    (fun m hm x hx => s16c1610_conj_mem_center_map (hLn m hm) hx)
    (by rw [s16c1610_dParam_three, hrk]; omega) hnot

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

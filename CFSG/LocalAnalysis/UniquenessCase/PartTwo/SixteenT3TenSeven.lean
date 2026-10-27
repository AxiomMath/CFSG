module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3ElevInv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10OutFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16t_ten_stab_seven {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    {X A : Subgroup (MulAut T)} {Y : Fin 4 → Subgroup T}
    (hAn : ∀ m ∈ X, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hAcard : Nat.card ↥A = 7 ^ 3)
    (hY : S16tTenBlocks X A Y 7) :
    ∀ φ ∈ X, φ ^ 2 = 1 → ∀ i, (Y i).map φ.toMonoidHom = Y i → ∀ y ∈ Y i, φ y = y := by
  intro φ hφ hφ2 i hφi
  have hY8 : Nat.card ↥(Y i) = 8 := by
    rw [card_eq_two_pow hT (Y i), hY.blocks.rank i, s16c1610_dParam_seven]
    norm_num
  have hAst : A ≤ stabSub (Y i) := fun a ha =>
    s16n9b_mem_stabSub_of_map_eq (hY.norm a ha i)
  have hA7 : Nat.card (autSub A (Y i)) = 7 := by
    have h := card_autSub_mul hAst
    rw [hY.card_ker i, hAcard] at h
    have h49 : (0 : ℕ) < 7 ^ 2 := by norm_num
    have h' : Nat.card (autSub A (Y i)) * 7 ^ 2 = 7 * 7 ^ 2 := by
      rw [h]
      norm_num
    exact Nat.eq_of_mul_eq_mul_right h49 h'
  exact s16t_elev_fix_block hT hY8 hAst hA7 (s16n9b_mem_stabSub_of_map_eq hφi) hφ2
    (s16t_ten_map_conj_eq hAn hφ)

variable {G : Type} [Group G] [Finite G]

theorem s16t_two_lt_mBar_of_case168_10_seven (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h10 : Case168_10At D V₀ V hV L 7) : 2 < mBar D.M V₀ V hV := by
  obtain ⟨Y, hY⟩ := s16t_ten_blocks_of_case168_10 D h1217 hc (Or.inr rfl) h10
  have hAcard : Nat.card ↥(fstarBar D.M V₀ V hV) = 7 ^ 3 :=
    s16c167_card_isElemAbelianOfRank h10.2.2.2.2
  have h3 := s16t_le_mParam_of_blocks (s15_Infra_vtil_sq_eq_one V₀ V hV) hY.blocks
    (s16t_ten_stab_seven (s15_Infra_vtil_sq_eq_one V₀ V hV)
      (fun m hm a ha => s16t_fstarBar_conj_mem D hV hm ha) hAcard hY)
  rw [s16c1610_dParam_seven] at h3
  unfold mBar
  omega

section Certified


theorem s16t_no_calOStar_of_case168_10_seven (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h10 : Case168_10At D V₀ V hV L 7) (g : G) : ¬ InCalOStar D.k D.M V₀ V g := by
  intro hO
  obtain ⟨Ut, B, hBM, hB1, hB2, hUt, hk, hA3, hA4, -⟩ :=
    s16c1610_directData_of_calOStar D hc.setting.hyp16.hyp125 hO
  obtain ⟨Y, hY⟩ := s16t_ten_blocks_of_case168_10 D h1217 hc (Or.inr rfl) h10
  have hAcard : Nat.card ↥(fstarBar D.M V₀ V hV) = 7 ^ 3 :=
    s16c167_card_isElemAbelianOfRank h10.2.2.2.2
  have hk2 := s16c167_k_le_two D
  refine s16t_false_of_blocks_odd (s15_Infra_vtil_sq_eq_one V₀ V hV) hY.blocks
    (s16t_ten_stab_seven (s15_Infra_vtil_sq_eq_one V₀ V hV)
      (fun m hm a ha => s16t_fstarBar_conj_mem D hV hm ha) hAcard hY) hBM hB1 hB2 hUt ?_ hA3 hA4
  rw [s16c1610_dParam_seven]
  omega

end Certified

section CertifiedOut


theorem s16t_out10_of_case168_10_seven (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h10 : Case168_10At D V₀ V hV L 7) : Out10 D V₀ V hV := by
  have h2 := s16t_two_lt_mBar_of_case168_10_seven D h1217 hc h10
  have hk := s16c167_k_le_two D
  exact s16c1610_out10_of_no_calOStar D hin.hx hin.h61 hin.h127 hin.h1114 hin.h162
    hc.setting.hyp16.hyp125 (by omega)
    (fun _ g => s16t_no_calOStar_of_case168_10_seven D h1217 hc h10 g)

end CertifiedOut

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

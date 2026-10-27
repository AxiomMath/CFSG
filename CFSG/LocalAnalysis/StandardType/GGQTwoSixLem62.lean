module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixLem62Model

public section
namespace CFSG.StandardType.QTwo.SixPoint
open Matrix CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.GH74.Uniqueness.SU.SU5
variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem coe_word (hK : Nat.card K = 4) (w : List Bool) :
    qTwoSixLem62_coeHom (qTwoSixLem62_evalG
      (qTwoSixLem62_gen hK false) (qTwoSixLem62_gen hK true) w) =
      (qTwoSixLem62_eval qTwoSixLem62_g0 qTwoSixLem62_g1 w).map (f4cEmb hK) := by
  rw [qTwoSixLem62_map_evalG, qTwoSixLem62_coe_gen, qTwoSixLem62_coe_gen]
  exact qTwoSixLem62_map_matrix_eval (f4cEmb hK) _ _ _

private theorem image_word (hK : Nat.card K = 4) (α : Su K 2 1 3 ≃* Su K 2 1 3)
    (i j : Fin 216)
    (hi : qTwoSixLem62_coeHom (α (qTwoSixLem62_gen hK false)) =
      (qTwoSixLem62_element i).map (f4cEmb hK))
    (hj : qTwoSixLem62_coeHom (α (qTwoSixLem62_gen hK true)) =
      (qTwoSixLem62_element j).map (f4cEmb hK)) (w : List Bool) :
    qTwoSixLem62_coeHom (α (qTwoSixLem62_evalG
      (qTwoSixLem62_gen hK false) (qTwoSixLem62_gen hK true) w)) =
      (qTwoSixLem62_eval (qTwoSixLem62_element i) (qTwoSixLem62_element j) w).map
        (f4cEmb hK) := by
  rw [show α (qTwoSixLem62_evalG _ _ w) = qTwoSixLem62_evalG
    (α (qTwoSixLem62_gen hK false)) (α (qTwoSixLem62_gen hK true)) w from
    qTwoSixLem62_map_evalG α.toMonoidHom _ _ w,
    qTwoSixLem62_map_evalG, hi, hj]
  exact qTwoSixLem62_map_matrix_eval (f4cEmb hK) _ _ w

private theorem power_image_iff (hK : Nat.card K = 4)
    (α : Su K 2 1 3 ≃* Su K 2 1 3) (u : Su K 2 1 3) (M N : qTwoSixLem62_Mat)
    (hu : qTwoSixLem62_coeHom u = M.map (f4cEmb hK))
    (hv : qTwoSixLem62_coeHom (α u) = N.map (f4cEmb hK)) (n : ℕ) :
    N ^ n = 1 ↔ M ^ n = 1 := by
  have hc (v : Su K 2 1 3) : qTwoSixLem62_coeHom v ^ n = 1 ↔ v ^ n = 1 := by
    calc qTwoSixLem62_coeHom v ^ n = 1 ↔
        qTwoSixLem62_coeHom (v ^ n) = qTwoSixLem62_coeHom (1 : Su K 2 1 3) := by
          simp only [map_pow, map_one]
      _ ↔ v ^ n = 1 := (qTwoSixLem62_coe_injective (K := K)).eq_iff
  calc N ^ n = 1 ↔ (N.map (f4cEmb hK)) ^ n = 1 :=
        (qTwoSixLem62_map_pow_one hK N n).symm
    _ ↔ qTwoSixLem62_coeHom (α u) ^ n = 1 := by rw [hv]
    _ ↔ (α u) ^ n = 1 := hc _
    _ ↔ u ^ n = 1 := by
      calc (α u) ^ n = 1 ↔ α (u ^ n) = α 1 := by simp only [map_pow, map_one]
        _ ↔ u ^ n = 1 := α.injective.eq_iff
    _ ↔ qTwoSixLem62_coeHom u ^ n = 1 := (hc _).symm
    _ ↔ (M.map (f4cEmb hK)) ^ n = 1 := by rw [hu]
    _ ↔ M ^ n = 1 := qTwoSixLem62_map_pow_one hK M n

private theorem support_image (hK : Nat.card K = 4)
    (α : Su K 2 1 3 ≃* Su K 2 1 3) (J : Finset (Fin 3))
    (hJ : (coordBlockSU K 2 1 J).map α.toMonoidHom = coordBlockSU K 2 1 J)
    (u : Su K 2 1 3) (M N : qTwoSixLem62_Mat)
    (hu : qTwoSixLem62_coeHom u = M.map (f4cEmb hK))
    (hv : qTwoSixLem62_coeHom (α u) = N.map (f4cEmb hK))
    (hM : qTwoSixLem62_support J M) : qTwoSixLem62_support J N := by
  have hum : u ∈ coordBlockSU K 2 1 J := by
    rw [mem_coordBlockSU_iff]
    change ∀ i j, (i ∉ J ∨ j ∉ J) → qTwoSixLem62_coeHom u i j = _
    rw [hu]
    exact (qTwoSixLem62_map_support hK J M).2 hM
  have hvm : α u ∈ coordBlockSU K 2 1 J := by
    rw [← hJ]
    exact ⟨u, hum, rfl⟩
  rw [mem_coordBlockSU_iff] at hvm
  apply (qTwoSixLem62_map_support hK J N).1
  change ∀ i j, (i ∉ J ∨ j ∉ J) → qTwoSixLem62_coeHom (α u) i j = _ at hvm
  rwa [hv] at hvm

set_option maxHeartbeats 400000 in
theorem qTwoSix_lem62 (hK : Nat.card K = 4) (α : Su K 2 1 3 ≃* Su K 2 1 3)
    (h01 : (coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3))).map α.toMonoidHom =
      coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)))
    (h12 : (coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3))).map α.toMonoidHom =
      coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3))) :
    ∃ (d : Fin 3 → Kˣ) (σ : K ≃+* K), ∀ u : Su K 2 1 3,
      (((α u : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (fun i => (d i : K)) *
          (((u : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ *
          diagonal (fun i => (((d i)⁻¹ : Kˣ) : K)) := by
  obtain ⟨i, hi⟩ := qTwoSixLem62_enum_surjective hK (α (qTwoSixLem62_gen hK false))
  obtain ⟨j, hj⟩ := qTwoSixLem62_enum_surjective hK (α (qTwoSixLem62_gen hK true))
  have him : qTwoSixLem62_coeHom (α (qTwoSixLem62_gen hK false)) =
      (qTwoSixLem62_element i).map (f4cEmb hK) := by
    rw [← hi, qTwoSixLem62_coe_enum]
  have hjm : qTwoSixLem62_coeHom (α (qTwoSixLem62_gen hK true)) =
      (qTwoSixLem62_element j).map (f4cEmb hK) := by
    rw [← hj, qTwoSixLem62_coe_enum]
  have hp0 := power_image_iff hK α (qTwoSixLem62_gen hK false)
    qTwoSixLem62_g0 (qTwoSixLem62_element i) (qTwoSixLem62_coe_gen hK false) him
  have hp1 := power_image_iff hK α (qTwoSixLem62_gen hK true)
    qTwoSixLem62_g1 (qTwoSixLem62_element j) (qTwoSixLem62_coe_gen hK true) hjm
  obtain ⟨hg04, hg02, hg112, hg16, hg14, hn⟩ := qTwoSixLem62_original_conditions
  have hnodes : qTwoSixLem62_nodes (qTwoSixLem62_element i) (qTwoSixLem62_element j) := by
    unfold qTwoSixLem62_nodes at hn ⊢
    obtain ⟨ha, ha3, ha1, hp, hp2, hp1', hb, hb3, hb1, hq, hq2, hq1⟩ := hn
    have hw := image_word hK α i j him hjm
    have pw (w : List Bool) := power_image_iff hK α
      (qTwoSixLem62_evalG (qTwoSixLem62_gen hK false) (qTwoSixLem62_gen hK true) w)
      _ _ (coe_word hK w) (hw w)
    refine ⟨support_image hK α _ h01 _ _ _ (coe_word hK _) (hw _) ha,
      (pw _ 3).2 ha3, fun h => ha1 (by simpa only [pow_one] using (pw _ 1).1 (by simpa only [pow_one] using h)),
      support_image hK α _ h01 _ _ _ (coe_word hK _) (hw _) hp,
      (pw _ 2).2 hp2, fun h => hp1' (by simpa only [pow_one] using (pw _ 1).1 (by simpa only [pow_one] using h)),
      support_image hK α _ h12 _ _ _ (coe_word hK _) (hw _) hb,
      (pw _ 3).2 hb3, fun h => hb1 (by simpa only [pow_one] using (pw _ 1).1 (by simpa only [pow_one] using h)),
      support_image hK α _ h12 _ _ _ (coe_word hK _) (hw _) hq,
      (pw _ 2).2 hq2, fun h => hq1 (by simpa only [pow_one] using (pw _ 1).1 (by simpa only [pow_one] using h))⟩
  obtain ⟨a, b, c, hA, hB⟩ := qTwoSixLem62_pair_classification i j
    ((hp0 4).2 hg04) (fun h => hg02 ((hp0 2).1 h))
    ((hp1 12).2 hg112) (fun h => hg16 ((hp1 6).1 h))
    (fun h => hg14 ((hp1 4).1 h)) hnodes
  let d := qTwoSixLem62_diag hK a b
  let σ := qTwoSixLem62_sigma hK c
  let δ := qTwoSixExt_diagField hK d σ
  have hgen (bit : Bool) : α (qTwoSixLem62_gen hK bit) = δ (qTwoSixLem62_gen hK bit) := by
    apply qTwoSixLem62_coe_injective
    have hδ (v : Su K 2 1 3) : qTwoSixLem62_coeHom (δ v) =
        diagonal (fun l => (d l : K)) * (qTwoSixLem62_coeHom v).map σ *
          diagonal (fun l => (((d l)⁻¹ : Kˣ) : K)) :=
      qTwoSixExt_diagField_matrix hK d σ v
    rw [hδ, qTwoSixLem62_coe_gen]
    cases bit
    · rw [him, hA, qTwoSixLem62_action_map]
      rfl
    · rw [hjm, hB, qTwoSixLem62_action_map]
      rfl
  refine ⟨d, σ, fun u => ?_⟩
  obtain ⟨k, rfl⟩ := qTwoSixLem62_enum_surjective hK u
  have he : α (qTwoSixLem62_enum hK k) = δ (qTwoSixLem62_enum hK k) := by
    unfold qTwoSixLem62_enum
    rw [show α (qTwoSixLem62_evalG _ _ _) = _ from
      qTwoSixLem62_map_evalG α.toMonoidHom _ _ _,
      show δ (qTwoSixLem62_evalG _ _ _) = _ from
      qTwoSixLem62_map_evalG δ.toMonoidHom _ _ _]
    change qTwoSixLem62_evalG (α (qTwoSixLem62_gen hK false))
      (α (qTwoSixLem62_gen hK true)) _ = qTwoSixLem62_evalG
      (δ (qTwoSixLem62_gen hK false)) (δ (qTwoSixLem62_gen hK true)) _
    rw [hgen false, hgen true]
  rw [he]
  exact qTwoSixExt_diagField_matrix hK d σ _

end CFSG.StandardType.QTwo.SixPoint
end

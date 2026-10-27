module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Tspec
public import CFSG.Quasithin.Background.E3MParamAttained

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_z3_exists_j_of_mParam {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A L L₂ : Subgroup (MulAut W)} {x : MulAut W}
    (hB : s16h_Z3Blocks A L L₂ x) (hL : Nat.card ↥L = 3)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥) (hev : Even (Nat.card ↥A))
    (hm : E3.mParam A ≤ 2) :
    ∃ j ∈ A, j ^ 2 = 1 ∧ j ≠ 1 ∧ j ∈ centSub (commSub (⊤ : Subgroup W) L₂) ∧
      ∀ l ∈ L, j * l = l * j := by
  obtain ⟨i, hiA, hord, hri⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam A hev
  have hi2 : i ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one i
  have hi1 : i ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hri' : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers i)) ≤ 2 := by
    rw [rkIdx_fixV_zpowers, commV_eq_commSub] at hri
    omega
  have hiN : i ∈ normalizer (L : Set (MulAut W)) := by
    by_contra hni
    have hLne : L.map (MulAut.conj i).toMonoidHom ≠ L := fun h =>
      hni ((Subgroup.mem_normalizer_iff_map_conj_eq (H := L) (g := i)).mpr h)
    have hLmap : L.map (MulAut.conj i).toMonoidHom = L₂ := by
      rcases hB.perm i hiA with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 hLne
      · exact h1
    have hmap : (commSub (⊤ : Subgroup W) L).map i.toMonoidHom ≤
        commSub (⊤ : Subgroup W) L₂ := by
      rintro _ ⟨u, hu, rfl⟩
      exact commSub_top_map151b (X := L) (Y := L₂) (g := i) (fun y hy => by
        have hy' : (MulAut.conj i).toMonoidHom y ∈ L.map (MulAut.conj i).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hy
        rw [hLmap] at hy'
        simpa [MulAut.conj_apply] using hy') u hu
    have hdis : commSub (⊤ : Subgroup W) L ⊓
        (commSub (⊤ : Subgroup W) L).map i.toMonoidHom = ⊥ := by
      have hle : commSub (⊤ : Subgroup W) L ⊓
          (commSub (⊤ : Subgroup W) L).map i.toMonoidHom ≤
          commSub (⊤ : Subgroup W) L ⊓ commSub (⊤ : Subgroup W) L₂ :=
        inf_le_inf_left _ hmap
      rw [hB.inf] at hle
      exact le_bot_iff.mp hle
    have hr := s16h_bl_rk_le_of_inf_eq_bot (U := commSub (⊤ : Subgroup W) L) (t := i) hdis
    rw [hrk] at hr
    omega
  have hL₂N : i ∈ normalizer (L₂ : Set (MulAut W)) := by
    have hiLmap : L.map (MulAut.conj i).toMonoidHom = L :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := L) (g := i)).mp hiN
    have hmap₂ : L₂.map (MulAut.conj i).toMonoidHom = L₂ := by
      rcases hB.perm i hiA with ⟨-, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exfalso
        apply hB.ne
        rw [← h1, hiLmap]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := L₂) (g := i)).mpr hmap₂
  have hcommL : ∀ l ∈ L, i * l = l * i :=
    s16h_z3_commute_of_rk_le_two hW hL hrk hfix hiN hri'
  have hcommL₂ : ∀ l ∈ L₂, i * l = l * i :=
    s16h_z3_commute_of_rk_le_two hW (hB.card_eq.trans hL) (hB.rk_eq.trans hrk)
      (hB.fix_iff.mpr hfix) hL₂N hri'
  rcases s16h_z3_cent_block_of_commute hW hB hL hfix hcommL hcommL₂ hri' with hiU | hiU₂
  · obtain ⟨hjcent, hjcomm⟩ := s16h_z3_conj_inv hB hiU hcommL₂
    have hjA : x * i * x⁻¹ ∈ A := A.mul_mem (A.mul_mem hB.mem hiA) (A.inv_mem hB.mem)
    have hj2 : (x * i * x⁻¹) ^ 2 = 1 := by
      have h : (x * i * x⁻¹) * (x * i * x⁻¹) = x * (i * i) * x⁻¹ := by group
      rw [pow_two, h, ← pow_two, hi2]
      group
    have hj1 : x * i * x⁻¹ ≠ 1 := by
      intro h
      apply hi1
      have hconj : x⁻¹ * (x * i * x⁻¹) * x = i := by group
      rw [h] at hconj
      simpa using hconj.symm
    exact ⟨x * i * x⁻¹, hjA, hj2, hj1, hjcent, hjcomm⟩
  · exact ⟨i, hiA, hi2, hi1, hiU₂, hcommL⟩

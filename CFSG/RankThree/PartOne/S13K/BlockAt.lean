module

public import CFSG.RankThree.PartOne.S13K.BlockGen
public import CFSG.RankThree.PartOne.S13K.KFLiftRows

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem kfAt_of_block_gen (h : Sec12Hyp G p A c L E) (t : MulAut E) (hct : c ∈ autFixedInG E t)
    {B : Subgroup G} {z : G} {f : ℕ} (hBL : B ≤ L)
    (hBX : B ≤ Subgroup.centralizer (autFixedInG E t : Set G))
    (hBnorm : ∀ y ∈ L ⊓ Subgroup.centralizer (autFixedInG E t : Set G), ∀ b ∈ B, y * b * y⁻¹ ∈ B)
    (hBmodel : StatedClassicalModel ↥B .PSL 2 2 f) (hzB : z ∈ B) (hzE : z ∈ E) (hz1 : z ≠ 1)
    (hE : ∀ e ∈ E, ∃ u ∈ autFixedInG E t, ∃ i : ℤ, e = u * z ^ i)
    (hmov : autMovedInG E t ≤ B)
    (hlift : ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)), k ∈ B ∧
      E.normalizerMonoidHom ⟨k, hk⟩ = t) :
    KFAt p E f t ∧ kZero p E t = B := by
  obtain ⟨hBqs, hBc⟩ := isQuasisimple_and_center_of_model_psl_two hBmodel
  have hK : kZero p E t = B :=
    kZero_eq_of_block_gen h t hct hBL hBX hBnorm hBqs hBc hzB hzE hz1 hE
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hK⟩
  · rintro ⟨f', -, -, hf'⟩
    rw [hK] at hf'
    exact not_psu_three_quotient_of_psl_two hBmodel hBc hf'
  · rw [hK]
    exact hBmodel
  · rw [hK]
    ext e
    constructor
    · rintro ⟨heE, heC⟩
      obtain ⟨u, hu, i, rfl⟩ := hE e heE
      have hzi : ∀ b ∈ B, b * z ^ i = z ^ i * b := by
        intro b hb
        have hub : u * b = b * u := (Subgroup.mem_centralizer_iff.mp (hBX hb) u hu)
        have h1 : b * (u * z ^ i) = u * z ^ i * b := Subgroup.mem_centralizer_iff.mp heC b hb
        have h2 : u * (b * z ^ i) = u * (z ^ i * b) := by
          calc u * (b * z ^ i) = (u * b) * z ^ i := by rw [mul_assoc]
            _ = (b * u) * z ^ i := by rw [hub]
            _ = b * (u * z ^ i) := by rw [mul_assoc]
            _ = u * z ^ i * b := h1
            _ = u * (z ^ i * b) := by rw [mul_assoc]
        exact mul_left_cancel h2
      have hzc : (⟨z ^ i, B.zpow_mem hzB i⟩ : ↥B) ∈ Subgroup.center ↥B := by
        rw [Subgroup.mem_center_iff]
        intro b
        apply Subtype.ext
        exact hzi b b.2
      rw [hBc, Subgroup.mem_bot] at hzc
      have hz1' : z ^ i = 1 := congrArg Subtype.val hzc
      rw [hz1', mul_one]
      exact hu
    · intro he
      refine Subgroup.mem_inf.mpr ⟨Subgroup.map_subtype_le _ he, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (Subgroup.mem_centralizer_iff.mp (hBX hb) e he).symm
  · rw [hK]
    exact hmov
  · obtain ⟨k, hk, hkB, hkt⟩ := hlift
    exact ⟨k, hk, by rw [hK]; exact hkB, hkt⟩

end CFSG.RankThree.PartOne.S13K


module

public import CFSG.Monster.B.TwoA.Base.PetersenABase

public import CFSG.Monster.B.TwoA.Base.Par45B

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert

open scoped IsMulCommutative

theorem flats_eq_orbit
    {E : Subgroup Dfull} [CFSG.IsElementaryAbelian 2 E]
    (hsurj : Function.Surjective (conjE E)) (h3 : E3 ≤ E) :
    {F : Subgroup Dfull | (∃ g ∈ Shat, F = conjSub g E) ∧ E3 ≤ F} =
      {F | ∃ k ∈ K3, F = conjSub k E} := by
  ext F
  constructor
  · rintro ⟨⟨g, -, rfl⟩, hF⟩
    obtain ⟨h, hh, he⟩ := exists_normalizer_conjSub_eq hsurj h3 hF
    exact ⟨h, hh, he⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, K3_le_Shat hk, rfl⟩, ?_⟩
    have h1 := conjSub_mono (g := k) h3
    rwa [conjSub_eq_self_iff.2 hk] at h1

theorem X4_eq :
    X4 = {F | ∃ k ∈ K3, F = conjSub k E4} :=
  flats_eq_orbit conjE_E4_surjective E3_le_E4

theorem X5_eq :
    X5 = {F | ∃ k ∈ K3, F = conjSub k E5} :=
  flats_eq_orbit conjE_E5_surjective (E3_le_E4.trans E4_le_E5)

theorem E4_mem_X4 :
    E4 ∈ X4 := by
  rw [X4_eq]
  exact ⟨1, K3.one_mem, (conjSub_one _).symm⟩

theorem E5_mem_X5 :
    E5 ∈ X5 := by
  rw [X5_eq]
  exact ⟨1, K3.one_mem, (conjSub_one _).symm⟩

theorem conjSub_mem_X4
    {k : Dfull} (hk : k ∈ K3) {F : Subgroup Dfull} (hF : F ∈ X4) :
    conjSub k F ∈ X4 := by
  rw [X4_eq] at hF ⊢
  obtain ⟨k', hk', rfl⟩ := hF
  exact ⟨k * k', K3.mul_mem hk hk', (conjSub_mul _ _ _).symm⟩

theorem conjSub_mem_X5
    {k : Dfull} (hk : k ∈ K3) {F : Subgroup Dfull} (hF : F ∈ X5) :
    conjSub k F ∈ X5 := by
  rw [X5_eq] at hF ⊢
  obtain ⟨k', hk', rfl⟩ := hF
  exact ⟨k * k', K3.mul_mem hk hk', (conjSub_mul _ _ _).symm⟩

theorem natCard_K3_inf_K4 :
    Nat.card ↥(K3 ⊓ K4) = 46179488366592 := by
  have h := (chain_flags 3 4 (by norm_num) (by norm_num) (by norm_num)).2
  rw [natCard_subspaceDim_fin (by norm_num), show qBinom 2 4 3 = 15 by decide] at h
  have h1 := ((K3 ⊓ K4).subgroupOf K4).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : K3 ⊓ K4 ≤ K4)).toEquiv,
    natCard_K4] at h1
  have h2 : Nat.card ↥(K3 ⊓ K4) * 15 = 692692325498880 := (congrArg _ h.symm).trans h1
  omega

theorem natCard_K3_inf_K5 :
    Nat.card ↥(K3 ⊓ K5) = 69269232549888 := by
  have h := (chain_flags 3 5 (by norm_num) (by norm_num) (by norm_num)).2
  rw [natCard_subspaceDim_fin (by norm_num), show qBinom 2 5 3 = 155 by decide] at h
  have h1 := ((K3 ⊓ K5).subgroupOf K5).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : K3 ⊓ K5 ≤ K5)).toEquiv,
    natCard_K5] at h1
  have h2 : Nat.card ↥(K3 ⊓ K5) * 155 = 10736731045232640 := (congrArg _ h.symm).trans h1
  omega

theorem natCard_X4 :
    Nat.card X4 = 15 := by
  rw [Nat.card_coe_set_eq, X4_eq, ncard_conjSub_orbit, subgroupOf_K3_eq]
  exact index_eq_of_natCard inf_le_left natCard_K3_inf_K4 natCard_K3 (by norm_num) (by norm_num)

theorem natCard_X5 :
    Nat.card X5 = 10 := by
  rw [Nat.card_coe_set_eq, X5_eq, ncard_conjSub_orbit, subgroupOf_K3_eq]
  exact index_eq_of_natCard inf_le_left natCard_K3_inf_K5 natCard_K3 (by norm_num) (by norm_num)

theorem incident_eq_conj
    {F G : Subgroup Dfull} (hF : F ∈ X4) (hG : G ∈ X5) (hFG : F ≤ G) :
    ∃ k ∈ K3, F = conjSub k E4 ∧ G = conjSub k E5 := by
  have hcF : Nat.card F = 2 ^ 4 := by
    obtain ⟨⟨g, -, rfl⟩, -⟩ := hF
    rw [natCard_conjSub, natCard_E4]
  rw [X5_eq] at hG
  obtain ⟨k, hk, rfl⟩ := hG
  set F' := conjSub k⁻¹ F with hF'
  have hF'5 : F' ≤ E5 := by
    have h1 := conjSub_mono (g := k⁻¹) hFG
    rwa [conjSub_inv_conjSub] at h1
  have hF'3 : E3 ≤ F' := by
    have h1 := conjSub_mono (g := k⁻¹) hF.2
    rwa [conjSub_eq_self_iff.2 (K3.inv_mem hk)] at h1
  have hcF' : Nat.card F' = 2 ^ 4 := by rw [natCard_conjSub, hcF]
  have h35 : E3 ≤ E5 := E3_le_E4.trans E4_le_E5
  obtain ⟨e, he3, he4⟩ := exists_linearEquiv_fix_map_eq (subOf_mono (E := E5) E3_le_E4)
    (subOf_mono (E := E5) hF'3)
    ((finrank_subOf E5 E4_le_E5 natCard_E4).trans (finrank_subOf E5 hF'5 hcF').symm)
  obtain ⟨h, hh⟩ := linConj_surjective E5 conjE_E5_surjective e
  have hh3 : (h : Dfull) ∈ K3 := by
    rw [← map_linConj_eq_iff E5 h35 h, hh]
    exact he3
  have hh4 : conjSub (h : Dfull) E4 = F' := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [hcF', natCard_conjSub, natCard_E4])
    obtain ⟨f, hf, rfl⟩ := hx
    have h1 : (linConj E5 h : Additive E5 →ₗ[ZMod 2] Additive E5)
        (Additive.ofMul ⟨f, E4_le_E5 hf⟩) ∈ subOf E5 F' := by
      rw [← he4, hh]
      exact ⟨_, hf, rfl⟩
    exact h1
  refine ⟨k * h, K3.mul_mem hk hh3, ?_, ?_⟩
  · rw [conjSub_mul, hh4, hF', conjSub_conjSub_inv]
  · rw [conjSub_mul, conjSub_eq_self_iff.2 h.2]

theorem incident_transitive
    {F G F' G' : Subgroup Dfull} (hF : F ∈ X4) (hG : G ∈ X5)
    (hFG : F ≤ G) (hF' : F' ∈ X4) (hG' : G' ∈ X5) (hFG' : F' ≤ G') :
    ∃ k ∈ K3, conjSub k F = F' ∧ conjSub k G = G' := by
  obtain ⟨a, ha, rfl, rfl⟩ := incident_eq_conj hF hG hFG
  obtain ⟨b, hb, rfl, rfl⟩ := incident_eq_conj hF' hG' hFG'
  refine ⟨b * a⁻¹, K3.mul_mem hb (K3.inv_mem ha), ?_, ?_⟩
  · rw [conjSub_mul, conjSub_inv_conjSub]
  · rw [conjSub_mul, conjSub_inv_conjSub]

end CFSG.Monster.B.TwoA

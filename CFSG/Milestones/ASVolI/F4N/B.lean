module

public import CFSG.Milestones.ASVolI.F4N.BAmal
public import CFSG.Milestones.ASVolI.F4N.BGeo

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF4nB_q_eq {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (h1 : (M₁ ⊓ M₂).relIndex M₁ = 3) (h2 : (M₁ ⊓ M₂).relIndex M₂ = 3) :
    (RankTwoAmalgam.ofSubgroups M₁ M₂).qOne = 2 ∧ (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo = 2 := by
  refine ⟨?_, ?_⟩
  · show (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range.index - 1 = 2
    rw [show (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range = (M₁ ⊓ M₂).subgroupOf M₁ from
      Subgroup.inclusion_range (inf_le_left : M₁ ⊓ M₂ ≤ M₁)]
    show (M₁ ⊓ M₂).relIndex M₁ - 1 = 2
    rw [h1]
  · show (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range.index - 1 = 2
    rw [show (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range = (M₁ ⊓ M₂).subgroupOf M₂ from
      Subgroup.inclusion_range (inf_le_right : M₁ ⊓ M₂ ≤ M₂)]
    show (M₁ ⊓ M₂).relIndex M₂ - 1 = 2
    rw [h2]

set_option linter.unusedSectionVars false


theorem burnsideF4nB_F420_G2d (h46 : F_4_6) (h419 : F_4_19) :
    ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ → κ = .G2d →
      ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
        ∀ cc ∈ CosetGeom.nbrs β.xv, cc ≠ β.lv →
        ∀ y ∈ CosetGeom.nbrs β.lv, y ≠ β.xv →
        ∀ y' ∈ CosetGeom.nbrs cc, y' ≠ β.xv →
          Set.ncard (N1set β κ cc y) = 4 ∧ Set.ncard (N2set β κ cc y y') = 4 ∧
          Set.ncard (Pset β κ cc y y') = 8 ∧
          ∀ s ∈ N1set β κ cc y, ∀ s' ∈ N1set β κ cc y,
            ∃ g ∈ Qu p Gp β β.lv ⊓ Qu p Gp β cc, g * s * g⁻¹ = s' := by
  intro κ p f E _ Gp M₁ M₂ hyp hGp hκ Y _ β hβ hsmall cc hcc hccl y hy hyx y' hy' hy'x
  subst hGp
  subst hκ
  haveI : Finite E := hyp.finite
  obtain ⟨hp2, -, -⟩ := hyp.model
  subst hp2
  obtain ⟨hi1, hi2, Z, hZ12, hZQ, hZc, hinv⟩ := burnsideF4nB_E_facts hyp
  obtain ⟨hq1, hq2⟩ := burnsideF4nB_q_eq hi1 hi2
  have F : β.Facts46 6 := burnsideF4a_facts46 h46 hyp ⟨by omega, by omega⟩ β hβ
  have hs : β.IsSmall 6 := hsmall
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  haveI : Finite Y := burnsideF4b_finite_of_small F hs
  have hval : ∀ u : β.Γ, Nat.card (CosetGeom.nbrs u) = 3 := by
    intro u
    rw [card_nbrs hβ u]
    unfold RankTwoAmalgam.qv
    split_ifs <;> omega
  have hTits : GLKind.G2d ≠ GLKind.Tits := by decide
  have hN1 : N1set β GLKind.G2d cc y = burnsideF4nB_N1 β y := by
    unfold N1set
    rw [if_neg hTits]
    rfl
  obtain ⟨b₀, hb₀, hb₀T⟩ := burnsideF4nB_exists_b₀ β hβ hy hyx
  have hN1card : (burnsideF4nB_N1 β y).ncard = 4 :=
    burnsideF4nB_ncard_N1 β hβ b₀ hb₀ hyx ((hinv _ (burnsideF4nB_v2_mem b₀) hb₀T).1)
  obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq
    (CosetGeom.adj_γ₀_γ₁ : β.graph.Adj β.xv β.lv) (hcc : β.graph.Adj β.xv cc)
  obtain ⟨a₀, rfl⟩ := stv_xv_le_range_f1 β (MulAction.mem_stabilizer_iff.mpr hg1)
  subst hg2
  have hN2 : N2set β GLKind.G2d (f1 (c := β) a₀ • β.lv) y y' =
      (fun s => f1 (c := β) a₀ * s * (f1 (c := β) a₀)⁻¹) ''
        burnsideF4nB_N1 β ((f1 (c := β) a₀)⁻¹ • y') := by
    unfold N2set
    rw [if_neg hTits]
    exact burnsideF4nB_N2_eq β a₀ y'
  have hy'' : (f1 (c := β) a₀)⁻¹ • y' ∈ CosetGeom.nbrs β.lv := by
    have h := (CosetGeom.smul_adj (f1 (c := β) a₀)⁻¹).mpr (hy' : β.graph.Adj _ y')
    rwa [inv_smul_smul] at h
  have hy''x : (f1 (c := β) a₀)⁻¹ • y' ≠ β.xv := by
    intro h
    apply hy'x
    rw [← smul_inv_smul (f1 (c := β) a₀) y', h, f1_smul_xv]
  obtain ⟨b₁, hb₁, hb₁T⟩ := burnsideF4nB_exists_b₀ β hβ hy'' hy''x
  have hN2card : (burnsideF4nB_N1 β ((f1 (c := β) a₀)⁻¹ • y')).ncard = 4 :=
    burnsideF4nB_ncard_N1 β hβ b₁ hb₁ hy''x ((hinv _ (burnsideF4nB_v2_mem b₁) hb₁T).1)
  have hbij := h419 GLKind.G2d 2 _ E ⊤ M₁ M₂ hyp rfl (Or.inl rfl) Y β hβ hsmall
    (f1 (c := β) a₀ • β.lv) hcc hccl y hy hyx y' hy' hy'x
  have hP : (Pset β GLKind.G2d (f1 (c := β) a₀ • β.lv) y y').ncard =
      (Bset β GLKind.G2d (f1 (c := β) a₀ • β.lv) y y').ncard := by
    rw [← hbij.image_eq, Set.InjOn.ncard_image hbij.injOn]
  let w : β.graph.Walk y' y :=
    SimpleGraph.Walk.cons (hy' : β.graph.Adj (f1 (c := β) a₀ • β.lv) y').symm
      (SimpleGraph.Walk.cons (hcc : β.graph.Adj β.xv (f1 (c := β) a₀ • β.lv)).symm
        (SimpleGraph.Walk.cons (CosetGeom.adj_γ₀_γ₁ : β.graph.Adj β.xv β.lv)
          (SimpleGraph.Walk.cons (hy : β.graph.Adj β.lv y) SimpleGraph.Walk.nil)))
  let π : GPath β.graph 4 := GPath.ofWalk w
  have hπ0 : π 0 = y' := rfl
  have hπ1 : π 1 = f1 (c := β) a₀ • β.lv := rfl
  have hπ2 : π 2 = β.xv := rfl
  have hπ3 : π 3 = β.lv := rfl
  have hπ4 : π 4 = y := rfl
  have hπnb : π.NoBack := by
    intro i hi
    have hi2 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi2 with rfl | rfl | rfl
    · rw [hπ0, hπ2]; exact hy'x
    · rw [hπ1, hπ3]; exact hccl
    · rw [hπ2, hπ4]; exact fun h => hyx h.symm
  have hB : Bset β GLKind.G2d (f1 (c := β) a₀ • β.lv) y y' =
      {S : Set β.Γ | β.IsApartment 6 S ∧ ∀ i ≤ 4, π i ∈ S} := by
    unfold Bset
    ext S
    simp only [Set.mem_setOf_eq, if_neg hTits, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · rintro ⟨hS, h0, h1, h2, h3, h4⟩
      refine ⟨hS, fun i hi => ?_⟩
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
      · rw [hπ0]; exact h0
      · rw [hπ1]; exact h1
      · rw [hπ2]; exact h2
      · rw [hπ3]; exact h3
      · rw [hπ4]; exact h4
    · rintro ⟨hS, h⟩
      refine ⟨hS, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hπ0]; exact h 0 (by norm_num)
      · rw [← hπ1]; exact h 1 (by norm_num)
      · rw [← hπ2]; exact h 2 (by norm_num)
      · rw [← hπ3]; exact h 3 (by norm_num)
      · rw [← hπ4]; exact h 4 le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hN1]
    exact hN1card
  · rw [hN2, Set.ncard_image_of_injective _ (fun s t h => by simpa using h)]
    exact hN2card
  · rw [hP, hB]
    exact burnsideF4nB_ncard_apart F hs hval π hπnb
  · intro s hs s' hs'
    rw [hN1, burnsideF4nB_N1_eq β hβ b₀ hb₀ hyx] at hs hs'
    obtain ⟨m, hm, rfl⟩ := hs
    obtain ⟨m', hm', rfl⟩ := hs'
    obtain ⟨d, hdZ, hdm⟩ := (hinv _ (burnsideF4nB_v2_mem b₀) hb₀T).2 _ hm _ hm'
    have hd1 : d ∈ M₁ := (hZ12 hdZ).1
    have hd2 : d ∈ M₂ := (hZ12 hdZ).2
    refine ⟨f1 (c := β) (burnsideF4nB_mk1 M₁ M₂ d hd1),
      burnsideF4nB_Z_le_Qu hyp β a₀ hd1 hd2 (hZQ hdZ) (hZc d hdZ), ?_⟩
    have hdd : f1 (c := β) (burnsideF4nB_mk1 M₁ M₂ d hd1) =
        f2 (c := β) (burnsideF4nB_mk2 M₁ M₂ d hd2) :=
      burnsideF4nB_f1_alpha1 β (burnsideF4nB_mk12 M₁ M₂ d (Subgroup.mem_inf.2 ⟨hd1, hd2⟩))
    rw [hdd, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply burnsideF4nB_v2_injective
    rw [map_mul, map_mul, map_inv]
    exact hdm

theorem burnsideF4nB_F420_G2d' (_h45 : F_4_5) (h46 : F_4_6) (h419 : F_4_19) :
    ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ → κ = .G2d →
      ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
        ∀ cc ∈ CosetGeom.nbrs β.xv, cc ≠ β.lv →
        ∀ y ∈ CosetGeom.nbrs β.lv, y ≠ β.xv →
        ∀ y' ∈ CosetGeom.nbrs cc, y' ≠ β.xv →
          Set.ncard (N1set β κ cc y) = 4 ∧ Set.ncard (N2set β κ cc y y') = 4 ∧
          Set.ncard (Pset β κ cc y y') = 8 ∧
          ∀ s ∈ N1set β κ cc y, ∀ s' ∈ N1set β κ cc y,
            ∃ g ∈ Qu p Gp β β.lv ⊓ Qu p Gp β cc, g * s * g⁻¹ = s' :=
  burnsideF4nB_F420_G2d h46 h419

end CFSG.ASVolI

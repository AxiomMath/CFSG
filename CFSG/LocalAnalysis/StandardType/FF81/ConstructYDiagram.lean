module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23 B12_sup_B23)
open scoped MatrixGroups

theorem A2System.subgroupOf {G : Type} [Group G] {m : ℕ} {adj : Fin m → Fin m → Prop}
    {U : Fin m → Subgroup G} {X : Subgroup G} (h : A2System adj U X) :
    A2System adj (fun i => (U i).subgroupOf X) ⊤ := by
  obtain ⟨hiso, hsup, hcomm, hpair⟩ := h
  have hle : ∀ i, U i ≤ X := fun i => hsup ▸ le_iSup U i
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · obtain ⟨e⟩ := hiso i
    exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe (hle i)).symm⟩
  · apply Subgroup.map_injective X.subtype_injective
    have hinf : ∀ i, U i ⊓ X = U i := fun i => inf_of_le_left (hle i)
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp only [Subgroup.subgroupOf_map_subtype, hinf]
    exact hsup
  · intro i j hij hadj a ha c hc
    exact Subtype.ext (hcomm i j hij hadj a ha c hc)
  · intro i j hadj
    obtain ⟨W, θ, c, hrange, hker, himg⟩ := hpair i j hadj
    have htop : (B12 (ZMod 2)).map (MulAut.conj c⁻¹).toMonoidHom ⊔
        (B23 (ZMod 2)).map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
      rw [← Subgroup.map_sup, B12_sup_B23,
        Subgroup.map_top_of_surjective _ (MulAut.conj c⁻¹).surjective]
    have hθX : ∀ y, θ y ∈ X := by
      intro y
      have hy : θ y ∈ ((B12 (ZMod 2)).map (MulAut.conj c⁻¹).toMonoidHom ⊔
          (B23 (ZMod 2)).map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
        Subgroup.mem_map_of_mem θ (htop ▸ Subgroup.mem_top y)
      rw [Subgroup.map_sup] at hy
      rcases himg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hy
        exact sup_le (hle i) (hle j) hy
      · rw [h1, h2] at hy
        exact sup_le (hle j) (hle i) hy
    have hmap : ∀ H : Subgroup SL(3, ZMod 2),
        H.map (θ.codRestrict X hθX) = (H.map θ).subgroupOf X := by
      intro H
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        exact ⟨y, hy, Subtype.ext hyx⟩
    refine ⟨(θ.codRestrict X hθX).range, θ.codRestrict X hθX, c, rfl, ?_, ?_⟩
    · rw [MonoidHom.ker_codRestrict]
      exact hker
    · rw [hmap, hmap]
      rcases himg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
      · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

variable {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G} {K : ℕ → Subgroup G}
  {t : G}

theorem FrameSystem.le_L (hF : FrameSystem n b L K t) {i : ℕ} (hi2 : 2 ≤ i) (hi : i < n + 2) :
    K i ≤ L := by
  have h : K ((i - 2) + 2) ≤ L :=
    hF.sysL.2.1 ▸ le_iSup (fun j : Fin n => K ((j : ℕ) + 2)) ⟨i - 2, by omega⟩
  rwa [Nat.sub_add_cancel hi2] at h

theorem FrameSystem.commute_one_succ (hF : FrameSystem n b L K t) (hn : 2 ≤ n) :
    ∀ a ∈ K 1, ∀ c ∈ K (n + 1), a * c = c * a := by
  obtain ⟨g, -, hgL, hgc⟩ := hF.tau
  intro a ha c hc
  have haL : a ∈ L.map (MulAut.conj g).toMonoidHom :=
    hgL ▸ le_iSup (fun j : Fin n => K (j : ℕ)) ⟨1, by omega⟩ ha
  exact (hgc c hc a haL).symm

theorem FrameSystem.a2System_of_commute (hF : FrameSystem n b L K t) (hn : 3 ≤ n)
    (h1n : ∀ a ∈ K 1, ∀ c ∈ K n, a * c = c * a) :
    A2System adjA (fun i : Fin (n + 2) => K (i : ℕ)) (⨆ i : Fin (n + 2), K (i : ℕ)) := by
  obtain ⟨hisoL, -, hcommL, hpairL⟩ := hF.sysL
  obtain ⟨hisoL', -, hcommL', hpairL'⟩ := hF.sysL'
  have h1s := hF.commute_one_succ (by omega)
  have key : ∀ i j : ℕ, i < j → j < n + 2 → i + 1 ≠ j →
      ∀ a ∈ K i, ∀ c ∈ K j, a * c = c * a := by
    intro i j hij hj hadj a ha c hc
    by_cases hjn : j < n
    · exact hcommL' ⟨i, by omega⟩ ⟨j, hjn⟩ (fun h => by rw [Fin.mk.injEq] at h; omega)
        (by unfold adjA; simp only; omega) a ha c hc
    · by_cases hi2 : 2 ≤ i
      · have h' : ∀ a ∈ K ((i - 2) + 2), ∀ c ∈ K ((j - 2) + 2), a * c = c * a :=
          hcommL ⟨i - 2, by omega⟩ ⟨j - 2, by omega⟩ (fun h => by rw [Fin.mk.injEq] at h; omega)
            (by unfold adjA; simp only; omega)
        rw [Nat.sub_add_cancel hi2, Nat.sub_add_cancel (by omega : 2 ≤ j)] at h'
        exact h' a ha c hc
      · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
        · exact hF.comm_L a ha c (hF.le_L (by omega) hj hc)
        · obtain rfl | rfl : j = n ∨ j = n + 1 := by omega
          · exact h1n a ha c hc
          · exact h1s a ha c hc
  refine ⟨fun i => ?_, rfl, ?_, ?_⟩
  · by_cases hi : (i : ℕ) < n
    · exact hisoL' ⟨i, hi⟩
    · have h' : Nonempty (SL(2, ZMod 2) ≃* ↥(K (((i : ℕ) - 2) + 2))) :=
        hisoL ⟨(i : ℕ) - 2, by omega⟩
      rwa [Nat.sub_add_cancel (by omega : 2 ≤ (i : ℕ))] at h'
  · intro i j hij hnadj a ha c hc
    have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key i j h j.2 (fun h' => hnadj (Or.inl h')) a ha c hc
    · exact (key j i h i.2 (fun h' => hnadj (Or.inr h')) c hc a ha).symm
  · intro i j hadj
    have hadj' : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i := hadj
    by_cases hlt : (i : ℕ) < n ∧ (j : ℕ) < n
    · exact hpairL' ⟨i, hlt.1⟩ ⟨j, hlt.2⟩ hadj'
    · have hi2 : 2 ≤ (i : ℕ) := by omega
      have hj2 : 2 ≤ (j : ℕ) := by omega
      have h' : ∃ W, LinearBlockStandardPair (ZMod 2) W (K (((i : ℕ) - 2) + 2))
          (K (((j : ℕ) - 2) + 2)) :=
        hpairL ⟨(i : ℕ) - 2, by omega⟩ ⟨(j : ℕ) - 2, by omega⟩
          (by unfold adjA; simp only; omega)
      rwa [Nat.sub_add_cancel hi2, Nat.sub_add_cancel hj2] at h'

theorem FrameSystem.lieModel_of_commute (hC : CurtisA2) (hF : FrameSystem n b L K t)
    (hn : 3 ≤ n) (h1n : ∀ a ∈ K 1, ∀ c ∈ K n, a * c = c * a) :
    CFSG.IsQuasisimple ↥(⨆ i : Fin (n + 2), K (i : ℕ)) ∧
      CFSG.Blueprint.LieModel (↥(⨆ i : Fin (n + 2), K (i : ℕ)) ⧸
        Subgroup.center ↥(⨆ i : Fin (n + 2), K (i : ℕ)))
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 3) 2 1 :=
  hC.1 (n + 2) (by omega) _ _ (hF.a2System_of_commute hn h1n).subgroupOf

end CFSG.StandardType.FF81

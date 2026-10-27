module

public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup

theorem mem_of_commute_of_isStronglyPEmbedded {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {M : Subgroup G} (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    {x : G} (hx : x ∈ M) (hxp : orderOf x = p) {g : G} (hg : Commute g x) : g ∈ M := by
  by_contra hgM
  apply hM.2.2 g hgM
  have hxg : x ∈ M.map (MulAut.conj g).toMonoidHom := by
    refine ⟨x, hx, ?_⟩
    simp [MulAut.conj_apply, hg.eq]
  rw [← hxp]
  exact Subgroup.orderOf_dvd_natCard _ (show x ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom from
    ⟨hx, hxg⟩)

theorem forall_commute_mem_map {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {r : ℕ}
    {M : Subgroup G} (hM : ∀ x ∈ M, orderOf x = r → ∀ g : G, Commute g x → g ∈ M) :
    ∀ x ∈ M.map φ.toMonoidHom, orderOf x = r → ∀ g : H, Commute g x →
      g ∈ M.map φ.toMonoidHom := by
  intro x hx hxr g hg
  rw [Subgroup.mem_map_equiv] at hx ⊢
  exact hM _ hx ((orderOf_injective φ.symm.toMonoidHom φ.symm.injective x).trans hxr) _
    (hg.map φ.symm)

theorem exists_mulAut_of_not_le {X : Type} [Group X] [Finite X] (L B ML : Subgroup X)
    [L.Normal] (hCL : centralizer (L : Set X) = ⊥) (hB5 : Nat.card B = 5) (hBL : ¬ B ≤ L)
    (hNB : L ⊓ normalizer (B : Set X) ≤ ML) :
    ∃ θ : MulAut L, orderOf θ = 5 ∧ θ ∉ (MulAut.conj : L →* MulAut L).range ∧
      ∀ y : L, θ y = y → y ∈ ML.subgroupOf L := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨b, hbB, hbL⟩ := SetLike.not_le_iff_exists.mp hBL
  have hb1 : b ≠ 1 := fun h => hbL (h ▸ L.one_mem)
  have hb5 : b ^ 5 = 1 := by
    have h := pow_card_eq_one' (G := B) (x := ⟨b, hbB⟩)
    rw [hB5] at h
    simpa using congrArg Subtype.val h
  have hcent : ∀ x : X, (∀ y ∈ L, x * y * x⁻¹ = y) → x = 1 := by
    intro x hx
    have hxC : x ∈ centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (mul_inv_eq_iff_eq_mul.mp (hx y hy)).symm
    rw [hCL] at hxC
    exact Subgroup.mem_bot.mp hxC
  refine ⟨MulAut.conjNormal b, orderOf_eq_prime ?_ ?_, ?_, ?_⟩
  · rw [← map_pow, hb5, map_one]
  · intro h
    apply hb1
    apply hcent
    intro y hy
    have h' := congrArg (fun θ : MulAut L => ((θ ⟨y, hy⟩ : L) : X)) h
    simpa [MulAut.conjNormal_apply] using h'
  · rintro ⟨y, hy⟩
    apply hbL
    have h1 : (y : X)⁻¹ * b = 1 := by
      apply hcent
      intro z hz
      have hz' : (y : X) * z * (y : X)⁻¹ = b * z * b⁻¹ := by
        have h' := congrArg (fun θ : MulAut L => ((θ ⟨z, hz⟩ : L) : X)) hy
        simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using h'
      calc (y : X)⁻¹ * b * z * ((y : X)⁻¹ * b)⁻¹ = (y : X)⁻¹ * (b * z * b⁻¹) * y := by group
        _ = (y : X)⁻¹ * ((y : X) * z * (y : X)⁻¹) * y := by rw [hz']
        _ = z := by group
    rw [← inv_mul_eq_one.mp h1]
    exact y.2
  · intro y hy
    rw [Subgroup.mem_subgroupOf]
    apply hNB
    refine ⟨y.2, Subgroup.centralizer_le_normalizer (B : Set X) ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hyb : b * y * b⁻¹ = y := by
      have h' := congrArg Subtype.val hy
      simpa [MulAut.conjNormal_apply] using h'
    have hcomm : Commute b (y : X) := mul_inv_eq_iff_eq_mul.mp hyb
    have hbne : (⟨b, hbB⟩ : B) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card (G := B) hB5 (g' := ⟨w, hw⟩) hbne)
    have hwk : b ^ k = w := by simpa using congrArg Subtype.val hk
    rw [← hwk]
    exact (hcomm.zpow_left k).eq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

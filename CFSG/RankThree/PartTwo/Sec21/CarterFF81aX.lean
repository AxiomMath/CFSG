module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aTau

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

noncomputable def FF81X (B : Subgroup G) : Subgroup (MulAut ↥B) :=
  (Subgroup.normalizerMonoidHom (H := B)).range

theorem mem_FF81X_iff {B : Subgroup G} {σ : MulAut ↥B} :
    σ ∈ FF81X B ↔ ∃ n : ↥(Nor B), Subgroup.normalizerMonoidHom (H := B) n = σ := by
  rw [FF81X, MonoidHom.mem_range]

theorem FF81Hyp.tau_mem_normalizer (h : FF81Hyp b L)
    {τ b₁ b₂ b₃ : G} (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹) :
    τ ∈ Nor (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) := by
  refine mem_nor_of_gen ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h
  · rw [h, hb]
    exact Subgroup.subset_closure (by simp)
  · rw [h, hinv.1]
    exact (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)).inv_mem
      (Subgroup.subset_closure (by simp))
  · rw [h, hinv.2.1]
    exact (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)).inv_mem
      (Subgroup.subset_closure (by simp))
  · rw [h, hinv.2.2]
    exact (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)).inv_mem
      (Subgroup.subset_closure (by simp))

noncomputable def FF81X.tau {B : Subgroup G} {τ : G} (hτN : τ ∈ Nor B) : MulAut ↥B :=
  Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩

theorem FF81Hyp.cen_X_tau_maps_b (h : FF81Hyp b L)
    {τ b₁ b₂ b₃ : G} (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hτ2 : orderOf τ = 2) (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    {σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (hσX : σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hcomm : σ * (FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv)) =
      (FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv)) * σ) :
    Subgroup.map σ (Subgroup.zpowers
      (⟨b, hbB⟩ : ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))) =
      Subgroup.zpowers (⟨b, hbB⟩ : ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) := by
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let bB : ↥B := ⟨b, hbB⟩
  let τN : ↥(Nor B) :=
    ⟨τ, FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv⟩
  let τX : MulAut ↥B := Subgroup.normalizerMonoidHom (H := B) τN
  have hcomm' : σ * τX = τX * σ := hcomm
  have hτXcoe : ∀ x : ↥B, (τX x : G) = τ * (x : G) * τ⁻¹ := by
    intro x
    change ((Subgroup.normalizerMonoidHom (H := B) τN) x : G) = τ * (x : G) * τ⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hfix : ∀ x : ↥B, τX x = x ↔ x ∈ Subgroup.zpowers bB := by
    intro x
    constructor
    · intro hx
      have hcoe : (x : G) = τ * (x : G) * τ⁻¹ := by
        have h := congrArg Subtype.val hx
        rw [hτXcoe x] at h
        exact h.symm
      have hxcen : (x : G) ∈ Cen τ := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (x : G) * τ = (τ * (x : G) * τ⁻¹) * τ :=
              congrArg (fun z : G => z * τ) hcoe
          _ = τ * (x : G) := by group
      have hxboth : (x : G) ∈ B ⊓ Cen τ := ⟨x.2, hxcen⟩
      rw [FF81Hyp.cen_B_inverting_involution h hτL hτ2 hb₁ hb₂ hb₃ hE hinv] at hxboth
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxboth
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_zpow]
      simpa using hk
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hbBfix : τX bB = bB := by
        refine Subtype.ext ?_
        rw [hτXcoe bB]
        simpa using hb
      rw [← hk]
      calc τX (bB ^ k) = (τX bB) ^ k := map_zpow τX bB k
        _ = bB ^ k := by rw [hbBfix]
  have hττ : τ * τ = 1 := by
    simpa [hτ2, pow_two] using pow_orderOf_eq_one τ
  have hτN2 : τN * τN = 1 := Subtype.ext hττ
  have hτX2 : τX * τX = 1 := by
    change Subgroup.normalizerMonoidHom (H := B) τN *
      Subgroup.normalizerMonoidHom (H := B) τN = 1
    rw [← map_mul, hτN2, map_one]
  have hτXinv : τX⁻¹ = τX :=
    inv_eq_of_mul_eq_one_right hτX2
  have hcomm_inv : τX * σ⁻¹ = σ⁻¹ * τX := by
    have h := congrArg Inv.inv hcomm'
    rw [mul_inv_rev, mul_inv_rev, hτXinv] at h
    exact h
  have hmap_le : Subgroup.map σ (Subgroup.zpowers bB) ≤ Subgroup.zpowers bB := by
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    refine (hfix (σ y)).mp ?_
    calc τX (σ y) = (τX * σ) y := rfl
      _ = (σ * τX) y := by rw [← hcomm']
      _ = σ (τX y) := rfl
      _ = σ y := by rw [(hfix y).mpr hy]
  have hmap_ge : Subgroup.zpowers bB ≤ Subgroup.map σ (Subgroup.zpowers bB) := by
    intro y hy
    refine Subgroup.mem_map.mpr ⟨σ⁻¹ y, ?_, ?_⟩
    · refine (hfix (σ⁻¹ y)).mp ?_
      calc τX (σ⁻¹ y) = (τX * σ⁻¹) y := rfl
        _ = (σ⁻¹ * τX) y := by rw [hcomm_inv]
        _ = σ⁻¹ (τX y) := rfl
        _ = σ⁻¹ y := by rw [(hfix y).mpr hy]
    · exact MulAut.apply_inv_self (M := ↥B) σ y
  exact le_antisymm hmap_le hmap_ge

end CFSG.RankThree.PartTwo.Sec21.FF81

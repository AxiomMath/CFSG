module

public import Mathlib.GroupTheory.Sylow

@[expose] public section

open scoped Pointwise

namespace CFSG.WeakClosureFusion

private lemma smul_subgroup_eq_map_conj {G : Type*} [Group G] {H : Subgroup G} (g : G) :
    MulAut.conj g • H = H.map (MulAut.conj g : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  congr 1

private lemma map_subtype_conj {G : Type*} [Group G] (C : Subgroup G) (c : C) (H : Subgroup C) :
    (H.map C.subtype).map (MulAut.conj (c : G)) = (H.map (MulAut.conj c)).map C.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private lemma map_conj_mul {G : Type*} [Group G] (x y : G) (H : Subgroup G) :
    (H.map (MulAut.conj x)).map (MulAut.conj y : G →* G)
      = H.map (MulAut.conj (y * x) : G →* G) := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

private lemma mem_normalizer_of_map_conj_le {G : Type*} [Group G] {W : Subgroup G} [Finite W]
    {h : G} (hmap : W.map (MulAut.conj h) ≤ W) : h ∈ Subgroup.normalizer W := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hmap
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj h).injective).symm)

theorem exists_mem_normalizer_conj_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {W : Subgroup G} (hWP : W ≤ P)
    (hwc : ∀ g : G, (∀ x ∈ W, g * x * g⁻¹ ∈ (P : Subgroup G)) → ∀ x ∈ W, g * x * g⁻¹ ∈ W)
    {a : G} (ha : ∀ x ∈ W, x * a = a * x) {g : G}
    (hg : ∀ x ∈ W, x * (g * a * g⁻¹) = (g * a * g⁻¹) * x) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), n * a * n⁻¹ = g * a * g⁻¹ := by
  classical
  set a' : G := g * a * g⁻¹ with ha'
  set C : Subgroup G := Subgroup.centralizer ({a'} : Set G) with hC
  have hWC : W ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ha']
    exact hg x hx
  have hW'C : W.map (MulAut.conj g) ≤ C := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ha']
    calc
      MulAut.conj g x * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by
        simp only [MulAut.conj_apply]; group
      _ = g * (a * x) * g⁻¹ := by rw [ha x hx]
      _ = (g * a * g⁻¹) * MulAut.conj g x := by
        simp only [MulAut.conj_apply]; group
  have hWp : IsPGroup p W := P.isPGroup'.to_le hWP
  have hW'p : IsPGroup p (W.map (MulAut.conj g : G →* G)) :=
    hWp.map (MulAut.conj g : G →* G)
  obtain ⟨Q₀, hQ₀⟩ := IsPGroup.exists_le_sylow (hWp.comap_subtype (K := C))
  obtain ⟨Q₁, hQ₁⟩ := IsPGroup.exists_le_sylow (hW'p.comap_subtype (K := C))
  have hWQ₀ : W ≤ (Q₀ : Subgroup C).map C.subtype := by
    intro y hy
    have hyC : y ∈ C := hWC hy
    have hy' : (⟨y, hyC⟩ : C) ∈ Subgroup.comap C.subtype W := hy
    simpa using Subgroup.mem_map_of_mem C.subtype (hQ₀ hy')
  have hW'Q₁ : W.map (MulAut.conj g : G →* G) ≤ (Q₁ : Subgroup C).map C.subtype := by
    intro y hy
    have hyC : y ∈ C := hW'C hy
    have hy' : (⟨y, hyC⟩ : C) ∈
        Subgroup.comap C.subtype (W.map (MulAut.conj g : G →* G)) := hy
    simpa using Subgroup.mem_map_of_mem C.subtype (hQ₁ hy')
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q₁ Q₀
  have hcsub : (Q₁ : Subgroup C).map (MulAut.conj c) = (Q₀ : Subgroup C) := by
    have h1 : MulAut.conj c • (Q₁ : Subgroup C) = (Q₀ : Subgroup C) := by
      have h2 := congrArg (fun S : Sylow p C => (S : Subgroup C)) hc
      rwa [Sylow.coe_subgroup_smul] at h2
    rwa [smul_subgroup_eq_map_conj] at h1
  have hW'Q₀ : (W.map (MulAut.conj g)).map (MulAut.conj (c : G) : G →* G)
      ≤ (Q₀ : Subgroup C).map C.subtype := by
    calc
      (W.map (MulAut.conj g)).map (MulAut.conj (c : G) : G →* G)
          ≤ ((Q₁ : Subgroup C).map C.subtype).map (MulAut.conj (c : G) : G →* G) :=
        Subgroup.map_mono hW'Q₁
      _ = ((Q₁ : Subgroup C).map (MulAut.conj c)).map C.subtype :=
        map_subtype_conj C c (Q₁ : Subgroup C)
      _ = (Q₀ : Subgroup C).map C.subtype := by rw [hcsub]
  have hQ₀p : IsPGroup p ((Q₀ : Subgroup C).map C.subtype) := Q₀.isPGroup'.map C.subtype
  obtain ⟨S, hQ₀S⟩ := IsPGroup.exists_le_sylow hQ₀p
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G P S
  let h : G := k⁻¹
  have hh : h • S = P := by
    show k⁻¹ • S = P
    rw [← hk, inv_smul_smul]
  have hQ₀Sh : ((Q₀ : Subgroup C).map C.subtype).map (MulAut.conj h) ≤ (P : Subgroup G) := by
    calc
      ((Q₀ : Subgroup C).map C.subtype).map (MulAut.conj h)
          ≤ (S : Subgroup G).map (MulAut.conj h) := Subgroup.map_mono hQ₀S
      _ = ((h • S : Sylow p G) : Subgroup G) := by
        rw [Sylow.coe_subgroup_smul, smul_subgroup_eq_map_conj]
      _ = (P : Subgroup G) := by rw [hh]
  have hmapW : W.map (MulAut.conj h) ≤ (P : Subgroup G) :=
    le_trans (Subgroup.map_mono hWQ₀) hQ₀Sh
  have hmapW2 : W.map (MulAut.conj (h * (c : G) * g)) ≤ (P : Subgroup G) := by
    calc
      W.map (MulAut.conj (h * (c : G) * g))
          = ((W.map (MulAut.conj g)).map (MulAut.conj (c : G) : G →* G)).map
              (MulAut.conj h) := by
        rw [map_conj_mul, map_conj_mul]
      _ ≤ ((Q₀ : Subgroup C).map C.subtype).map (MulAut.conj h) := Subgroup.map_mono hW'Q₀
      _ ≤ (P : Subgroup G) := hQ₀Sh
  have hP1 : ∀ x ∈ W, h * x * h⁻¹ ∈ (P : Subgroup G) := by
    intro x hx
    simpa [MulAut.conj_apply] using
      hmapW (Subgroup.mem_map_of_mem (MulAut.conj h : G →* G) hx)
  have hWN : h ∈ Subgroup.normalizer W :=
    mem_normalizer_of_map_conj_le (h := h) (by
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      simpa [MulAut.conj_apply] using hwc h hP1 x hx)
  have hP2 : ∀ x ∈ W, (h * (c : G) * g) * x * (h * (c : G) * g)⁻¹ ∈ (P : Subgroup G) := by
    intro x hx
    simpa [MulAut.conj_apply, mul_assoc] using
      hmapW2 (Subgroup.mem_map_of_mem (MulAut.conj (h * (c : G) * g) : G →* G) hx)
  have hhcgN : h * (c : G) * g ∈ Subgroup.normalizer W :=
    mem_normalizer_of_map_conj_le (h := h * (c : G) * g) (by
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      simpa [MulAut.conj_apply, mul_assoc] using hwc (h * (c : G) * g) hP2 x hx)
  refine ⟨(c : G) * g, ?_, ?_⟩
  · have hcn : (c : G) * g = h⁻¹ * (h * (c : G) * g) := by group
    rw [hcn]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hWN) hhcgN
  · have hcC : (c : G) ∈ Subgroup.centralizer ({a'} : Set G) := c.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hcC
    have hconj : ((c : G) * g) * a * ((c : G) * g)⁻¹ = (c : G) * a' * (c : G)⁻¹ := by
      show ((c : G) * g) * a * ((c : G) * g)⁻¹ = (c : G) * (g * a * g⁻¹) * (c : G)⁻¹
      group
    rw [hconj, hcC, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.WeakClosureFusion

end

module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameOrbit
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoords

public section

namespace CFSG.StandardType.SpFrame

open CFSG.StandardType CFSG.StandardType.SpJoin CFSG.Open

theorem zpowers_eq_of_frame {G : Type} [Group G] [Finite G] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 3 ≤ m) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hrank : Nat.card Bs = p ^ (m + 1)) {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A)
    {Hx Hy Hz : Subgroup (MulAut ↥Bs)} (hHx : Hx ≤ A) (hHy : Hy ≤ A) (hHz : Hz ≤ A)
    {x y z : G} (hx : x ∈ Bs) (hy : y ∈ Bs) (hz : z ∈ Bs)
    (hfx : ∀ ψ ∈ Hx, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x)
    (hfy : ∀ ψ ∈ Hy, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = y)
    (hfz : ∀ ψ ∈ Hz, ((ψ ⟨z, hz⟩ : ↥Bs) : G) = z)
    (hcx : 2 ^ m * m.factorial ≤ Nat.card Hx) (hcy : 2 ^ m * m.factorial ≤ Nat.card Hy)
    (hcz : 2 ^ m * m.factorial ≤ Nat.card Hz)
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) (hzx : z ∉ Subgroup.zpowers x)
    (hzD : z ∈ Subgroup.closure ({x, y} : Set G)) :
    Subgroup.zpowers z = Subgroup.zpowers y := by
  obtain ⟨Φ, hΦ⟩ := exists_frame_iso_of_weyl hp hp2 hBs (by omega : 1 ≤ m) hrank hA
  let X : Fin (m + 1) → Multiplicative (ZMod p) := Φ.symm ⟨x, hx⟩
  let Y : Fin (m + 1) → Multiplicative (ZMod p) := Φ.symm ⟨y, hy⟩
  let Z : Fin (m + 1) → Multiplicative (ZMod p) := Φ.symm ⟨z, hz⟩
  have hX : Φ X = ⟨x, hx⟩ := Φ.apply_symm_apply _
  have hY : Φ Y = ⟨y, hy⟩ := Φ.apply_symm_apply _
  have hZ : Φ Z = ⟨z, hz⟩ := Φ.apply_symm_apply _
  have hXax : ∀ i j, i ≠ j → X i = 1 ∨ X j = 1 :=
    fun i j hij => coord_eq_one_of_fixed hp hp2 hm hA Φ hΦ hHx hx hfx hcx hij
  have hYax : ∀ i j, i ≠ j → Y i = 1 ∨ Y j = 1 :=
    fun i j hij => coord_eq_one_of_fixed hp hp2 hm hA Φ hΦ hHy hy hfy hcy hij
  have hZax : ∀ i j, i ≠ j → Z i = 1 ∨ Z j = 1 :=
    fun i j hij => coord_eq_one_of_fixed hp hp2 hm hA Φ hΦ hHz hz hfz hcz hij
  have hX1 : X ≠ 1 := by
    intro hXeq
    have hsub : (⟨x, hx⟩ : ↥Bs) = 1 := by
      rw [← hX, hXeq, map_one]
    have : (x : G) = 1 := by
      have := congrArg (fun b : ↥Bs => (b : G)) hsub
      simpa using this
    exact hx1 this
  have hYX : Y ∉ Subgroup.zpowers X := by
    intro hmem
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    apply hyx
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    have h1 : (⟨x, hx⟩ : ↥Bs) ^ k = ⟨y, hy⟩ := by
      have h2 : (Φ X) ^ k = Φ Y := by rw [← hk, map_zpow]
      rwa [hX, hY] at h2
    have := congrArg (fun b : ↥Bs => (b : G)) h1
    simpa using this
  have hZX : Z ∉ Subgroup.zpowers X := by
    intro hmem
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    apply hzx
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    have h1 : (⟨x, hx⟩ : ↥Bs) ^ k = ⟨z, hz⟩ := by
      have h2 : (Φ X) ^ k = Φ Z := by rw [← hk, map_zpow]
      rwa [hX, hZ] at h2
    have := congrArg (fun b : ↥Bs => (b : G)) h1
    simpa using this
  have hzB : (⟨z, hz⟩ : ↥Bs) ∈ Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs) := by
    have hle : Subgroup.closure ({x, y} : Set G) ≤
        (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs)).map (Bs.subtype : ↥Bs →* G) := by
      rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hwx | hwy
      · rw [hwx]
        exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.subset_closure (by simp), rfl⟩
      · rw [hwy]
        exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, Subgroup.subset_closure (by simp), rfl⟩
    obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.mp (hle hzD)
    have : b = ⟨z, hz⟩ := Subtype.ext (by simpa using hbz)
    rwa [this] at hb
  have hZD : Z ∈ Subgroup.closure ({X, Y} : Set (Fin (m + 1) → Multiplicative (ZMod p))) := by
    have himg : (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs)).map
        (Φ.symm : ↥Bs →* (Fin (m + 1) → Multiplicative (ZMod p))) =
        Subgroup.closure ({X, Y} : Set (Fin (m + 1) → Multiplicative (ZMod p))) := by
      rw [MonoidHom.map_closure]
      congr 1
      rw [Set.image_pair]
      rfl
    rw [← himg]
    exact Subgroup.mem_map.mpr ⟨⟨z, hz⟩, hzB, rfl⟩
  have hZY : Subgroup.zpowers Z = Subgroup.zpowers Y :=
    zpowers_eq_of_coords hp hXax hYax hZax hX1 hYX hZX hZD
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    have hmem : Z ∈ Subgroup.zpowers Y := by rw [← hZY]; exact Subgroup.mem_zpowers Z
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    have h1 : (⟨y, hy⟩ : ↥Bs) ^ k = ⟨z, hz⟩ := by
      have h2 : (Φ Y) ^ k = Φ Z := by rw [← hk, map_zpow]
      rwa [hY, hZ] at h2
    have := congrArg (fun b : ↥Bs => (b : G)) h1
    simpa using this
  · rw [Subgroup.zpowers_le]
    have hmem : Y ∈ Subgroup.zpowers Z := by rw [hZY]; exact Subgroup.mem_zpowers Y
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    have h1 : (⟨z, hz⟩ : ↥Bs) ^ k = ⟨y, hy⟩ := by
      have h2 : (Φ Z) ^ k = Φ Y := by rw [← hk, map_zpow]
      rwa [hZ, hY] at h2
    have := congrArg (fun b : ↥Bs => (b : G)) h1
    simpa using this

end CFSG.StandardType.SpFrame

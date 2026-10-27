module

public import CFSG.LocalAnalysis.WeakClosure81.FiveNineQuot
import all CFSG.LocalAnalysis.WeakClosure81.FiveDefs
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def kerQuotLift (M H : Subgroup G) (Y : Subgroup (KerQuot M H)) : Subgroup G :=
  (Y.comap (kerQuotMk M H)).map H.subtype

theorem mem_kerQuotLift_iff {M H : Subgroup G} {Y : Subgroup (KerQuot M H)} {x : G} :
    x ∈ kerQuotLift M H Y ↔ ∃ hx : x ∈ H, kerQuotMk M H ⟨x, hx⟩ ∈ Y := by
  unfold kerQuotLift
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem kerQuotLift_le (M H : Subgroup G) (Y : Subgroup (KerQuot M H)) :
    kerQuotLift M H Y ≤ H :=
  Subgroup.map_subtype_le _

theorem kerMOf_le_kerQuotLift (M H : Subgroup G) (Y : Subgroup (KerQuot M H)) :
    kerMOf M H ≤ kerQuotLift M H Y := by
  intro x hx
  have hxH : x ∈ H := kerMOf_le_group M H hx
  rw [mem_kerQuotLift_iff]
  refine ⟨hxH, ?_⟩
  have hker : (⟨x, hxH⟩ : ↥H) ∈ (kerQuotMk M H).ker := by
    rw [ker_kerQuotMk]
    exact hx
  rw [MonoidHom.mem_ker.1 hker]
  exact Y.one_mem

theorem le_kerQuotLift_iff {M H X : Subgroup G} {Y : Subgroup (KerQuot M H)} (hXH : X ≤ H) :
    X ≤ kerQuotLift M H Y ↔ kerQuotImg M H X ≤ Y := by
  constructor
  · intro h q hq
    obtain ⟨y, hy, rfl⟩ := hq
    obtain ⟨hx, hmem⟩ := mem_kerQuotLift_iff.1 (h hy)
    exact hmem
  · intro h x hx
    rw [mem_kerQuotLift_iff]
    exact ⟨hXH hx, h ⟨⟨x, hXH hx⟩, hx, rfl⟩⟩

theorem kerQuotImg_kerQuotLift (M H : Subgroup G) (Y : Subgroup (KerQuot M H)) :
    kerQuotImg M H (kerQuotLift M H Y) = Y := by
  refine le_antisymm ((le_kerQuotLift_iff (kerQuotLift_le M H Y)).1 le_rfl) ?_
  intro q hq
  obtain ⟨y, rfl⟩ := kerQuotMk_surjective M H q
  have hy : (y : G) ∈ kerQuotLift M H Y := mem_kerQuotLift_iff.2 ⟨y.2, hq⟩
  exact ⟨y, hy, rfl⟩

theorem kerQuotLift_kerQuotImg {M H X : Subgroup G} (hXH : X ≤ H) :
    kerQuotLift M H (kerQuotImg M H X) = X ⊔ kerMOf M H := by
  refine le_antisymm ?_ (sup_le ((le_kerQuotLift_iff hXH).2 le_rfl)
    (kerMOf_le_kerQuotLift M H _))
  intro x hx
  obtain ⟨hxH, hmem⟩ := mem_kerQuotLift_iff.1 hx
  obtain ⟨y, hy, hyx⟩ := hmem
  have hk : y⁻¹ * ⟨x, hxH⟩ ∈ (kerQuotMk M H).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  rw [ker_kerQuotMk] at hk
  have hxy : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [hxy]
  exact Subgroup.mul_mem_sup hy hk

theorem kerQuotLift_kerQuotImg_of_le {M H K : Subgroup G} (hKH : K ≤ H)
    (hJK : kerMOf M H ≤ K) : kerQuotLift M H (kerQuotImg M H K) = K := by
  rw [kerQuotLift_kerQuotImg hKH]
  exact sup_eq_left.2 hJK

theorem kerQuotLift_mono {M H : Subgroup G} {Y Z : Subgroup (KerQuot M H)} (h : Y ≤ Z) :
    kerQuotLift M H Y ≤ kerQuotLift M H Z :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem kerQuotLift_le_kerQuotLift_iff {M H : Subgroup G} {Y Z : Subgroup (KerQuot M H)} :
    kerQuotLift M H Y ≤ kerQuotLift M H Z ↔ Y ≤ Z := by
  refine ⟨fun h => ?_, kerQuotLift_mono⟩
  have := kerQuotImg_mono (M := M) (H := H) h
  rwa [kerQuotImg_kerQuotLift, kerQuotImg_kerQuotLift] at this

theorem kerQuotLift_kerQuotImg_left (M H : Subgroup G) :
    kerQuotLift M H (kerQuotImg M H M) = M ⊓ H := by
  have h1 : kerQuotImg M H M = kerQuotImg M H (M ⊓ H) := by
    unfold kerQuotImg
    rw [Subgroup.inf_subgroupOf_right]
  rw [h1, kerQuotLift_kerQuotImg inf_le_right]
  exact sup_eq_left.2 (le_inf (kerMOf_le_left M H) (kerMOf_le_group M H))

theorem kerQuotLift_inf {M H : Subgroup G} (Y Z : Subgroup (KerQuot M H)) :
    kerQuotLift M H (Y ⊓ Z) = kerQuotLift M H Y ⊓ kerQuotLift M H Z := by
  ext x
  simp only [Subgroup.mem_inf, mem_kerQuotLift_iff]
  constructor
  · rintro ⟨hx, h1, h2⟩
    exact ⟨⟨hx, h1⟩, ⟨hx, h2⟩⟩
  · rintro ⟨⟨hx, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hx, h1, h2⟩

theorem kerQuotLift_sup {M H : Subgroup G} (Y Z : Subgroup (KerQuot M H)) :
    kerQuotLift M H (Y ⊔ Z) = kerQuotLift M H Y ⊔ kerQuotLift M H Z := by
  refine le_antisymm ?_ (sup_le (kerQuotLift_mono le_sup_left) (kerQuotLift_mono le_sup_right))
  set L := kerQuotLift M H Y ⊔ kerQuotLift M H Z with hL
  have hLH : L ≤ H := sup_le (kerQuotLift_le M H Y) (kerQuotLift_le M H Z)
  have hJL : kerMOf M H ≤ L := (kerMOf_le_kerQuotLift M H Y).trans le_sup_left
  rw [← kerQuotLift_kerQuotImg_of_le hLH hJL, kerQuotLift_le_kerQuotLift_iff]
  refine sup_le ?_ ?_
  · calc Y = kerQuotImg M H (kerQuotLift M H Y) := (kerQuotImg_kerQuotLift M H Y).symm
      _ ≤ kerQuotImg M H L := kerQuotImg_mono le_sup_left
  · calc Z = kerQuotImg M H (kerQuotLift M H Z) := (kerQuotImg_kerQuotLift M H Z).symm
      _ ≤ kerQuotImg M H L := kerQuotImg_mono le_sup_right

theorem isMaxSubgroupIn_kerQuotLift {M H : Subgroup G} {Y N : Subgroup (KerQuot M H)} :
    IsMaxSubgroupIn (kerQuotLift M H Y) (kerQuotLift M H N) ↔ IsMaxSubgroupIn Y N := by
  have hlt : ∀ {Y N : Subgroup (KerQuot M H)}, kerQuotLift M H N < kerQuotLift M H Y ↔ N < Y := by
    intro Y N
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, kerQuotLift_le_kerQuotLift_iff,
      kerQuotLift_le_kerQuotLift_iff]
  unfold IsMaxSubgroupIn
  refine and_congr hlt.symm.symm ?_
  constructor
  · intro h K hNK hKY
    have h1 := h (kerQuotLift M H K) (hlt.2 hNK) (kerQuotLift_mono hKY)
    exact le_antisymm hKY (kerQuotLift_le_kerQuotLift_iff.1 h1.ge)
  · intro h K hNK hKY
    have hKH : K ≤ H := hKY.trans (kerQuotLift_le M H Y)
    have hJK : kerMOf M H ≤ K := (kerMOf_le_kerQuotLift M H N).trans hNK.le
    have hK : K = kerQuotLift M H (kerQuotImg M H K) := (kerQuotLift_kerQuotImg_of_le hKH hJK).symm
    rw [hK] at hNK hKY ⊢
    have h1 := h (kerQuotImg M H K) (hlt.1 hNK) (kerQuotLift_le_kerQuotLift_iff.1 hKY)
    rw [h1]

theorem mem_normalizer_kerQuotLift {M H : Subgroup G} {Y : Subgroup (KerQuot M H)} {x : G}
    (hx : x ∈ H) (hq : kerQuotMk M H ⟨x, hx⟩ ∈ normalizer (Y : Set (KerQuot M H))) :
    x ∈ normalizer (kerQuotLift M H Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxinv : x⁻¹ ∈ H := H.inv_mem hx
  constructor
  · intro hy
    obtain ⟨hyH, hmem⟩ := mem_kerQuotLift_iff.1 hy
    have hxyH : x * y * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hx hyH) hxinv
    refine mem_kerQuotLift_iff.2 ⟨hxyH, ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 hq (kerQuotMk M H ⟨y, hyH⟩)).1 hmem
    have h2 : kerQuotMk M H ⟨x * y * x⁻¹, hxyH⟩ =
        kerQuotMk M H ⟨x, hx⟩ * kerQuotMk M H ⟨y, hyH⟩ * (kerQuotMk M H ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h2]
    exact h1
  · intro hy
    obtain ⟨hxyH, hmem⟩ := mem_kerQuotLift_iff.1 hy
    have hyH : y ∈ H := by
      have : x⁻¹ * (x * y * x⁻¹) * x ∈ H := H.mul_mem (H.mul_mem hxinv hxyH) hx
      simpa [mul_assoc] using this
    refine mem_kerQuotLift_iff.2 ⟨hyH, ?_⟩
    have h2 : kerQuotMk M H ⟨x * y * x⁻¹, hxyH⟩ =
        kerQuotMk M H ⟨x, hx⟩ * kerQuotMk M H ⟨y, hyH⟩ * (kerQuotMk M H ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h2] at hmem
    exact (Subgroup.mem_normalizer_iff.1 hq (kerQuotMk M H ⟨y, hyH⟩)).2 hmem

theorem kerQuotImg_conjSub {M H X : Subgroup G} {x : G} (hx : x ∈ H) :
    kerQuotImg M H (A1b.conjSub x X) =
      A1b.conjSub (kerQuotMk M H ⟨x, hx⟩) (kerQuotImg M H X) := by
  ext q
  obtain ⟨y, rfl⟩ := kerQuotMk_surjective M H q
  rw [A1b.mem_conjSub_iff]
  constructor
  · rintro ⟨y', hy', hy'q⟩
    have hy'' : (x⁻¹ * (y' : G) * x) ∈ X := by
      have := A1b.mem_conjSub_iff.1 hy'
      exact this
    refine ⟨⟨x⁻¹ * (y' : G) * x, H.mul_mem (H.mul_mem (H.inv_mem hx) y'.2) hx⟩, hy'', ?_⟩
    have : (⟨x⁻¹ * (y' : G) * x, H.mul_mem (H.mul_mem (H.inv_mem hx) y'.2) hx⟩ : ↥H) =
        (⟨x, hx⟩ : ↥H)⁻¹ * y' * ⟨x, hx⟩ := rfl
    rw [this, map_mul, map_mul, map_inv, hy'q]
  · rintro ⟨z, hz, hzq⟩
    refine ⟨⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, A1b.mem_conjSub_iff]
      have : (x⁻¹ * ((⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹ : ↥H) : G) * x) = (z : G) := by
        simp [mul_assoc]
      rw [this]
      exact hz
    · rw [map_mul, map_mul, map_inv, hzq]
      group

end CFSG.LocalAnalysis.WeakClosure81

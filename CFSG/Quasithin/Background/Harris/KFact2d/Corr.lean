module

public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.Background.E2TwoProofY

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2P

variable {G : Type} [Group G]

@[expose] noncomputable def pre (M H : Subgroup G) (B : Subgroup (E2.StarQuot M H)) : Subgroup G :=
  (B.comap (starMap M H)).map H.subtype

theorem mem_pre {M H : Subgroup G} {B : Subgroup (E2.StarQuot M H)} {x : G} :
    x ∈ pre M H B ↔ ∃ hx : x ∈ H, starMap M H ⟨x, hx⟩ ∈ B := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem pre_le {M H : Subgroup G} (B : Subgroup (E2.StarQuot M H)) : pre M H B ≤ H := fun _ hx =>
  (mem_pre.mp hx).1

theorem pre_mono {M H : Subgroup G} {B B' : Subgroup (E2.StarQuot M H)} (h : B ≤ B') :
    pre M H B ≤ pre M H B' := fun _ hx =>
  let ⟨hxH, hB⟩ := mem_pre.mp hx
  mem_pre.mpr ⟨hxH, h hB⟩

theorem star_pre {M H : Subgroup G} (B : Subgroup (E2.StarQuot M H)) :
    E2.star M H (pre M H B) = B := by
  rw [star_def]
  ext b
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyH, hB⟩ := mem_pre.mp (Subgroup.mem_subgroupOf.mp hy)
    exact hB
  · intro hb
    obtain ⟨y, rfl⟩ := starMap_surjective M H b
    refine ⟨y, Subgroup.mem_subgroupOf.mpr (mem_pre.mpr ⟨y.2, hb⟩), rfl⟩

theorem pre_star {M H X : Subgroup G} (hXH : X ≤ H) (hJX : kerIn M H ≤ X) :
    pre M H (E2.star M H X) = X := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxH, y, hy, hxy⟩ := mem_pre.mp hx
    have hker : y⁻¹ * ⟨x, hxH⟩ ∈ (starMap M H).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [ker_starMap] at hker
    have h1 : (y : G)⁻¹ * x ∈ kerIn M H := Subgroup.mem_subgroupOf.mp hker
    have h2 : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    have := X.mul_mem h2 (hJX h1)
    simpa using this
  · intro x hx
    exact mem_pre.mpr ⟨hXH hx, ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩⟩

theorem star_mono {M H X Y : Subgroup G} (h : X ≤ Y) : E2.star M H X ≤ E2.star M H Y :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono H h)

theorem le_pre_star {M H X : Subgroup G} (hXH : X ≤ H) : X ≤ pre M H (E2.star M H X) := fun x hx =>
  mem_pre.mpr ⟨hXH hx, ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩⟩

end CFSG.Quasithin.Background.Harris.KFact2d

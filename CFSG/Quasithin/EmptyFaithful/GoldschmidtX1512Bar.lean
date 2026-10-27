module

public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace X1512

variable {G : Type} [Group G]

open Classical in
noncomputable def bar (H : Subgroup G) (g : G) : OTwoQuot H :=
  if h : g ∈ H then QuotientGroup.mk (⟨g, h⟩ : ↥H) else 1

theorem bar_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) :
    bar H g = QuotientGroup.mk (⟨g, hg⟩ : ↥H) := by simp [bar, hg]

theorem bar_mul {H : Subgroup G} {g h : G} (hg : g ∈ H) (hh : h ∈ H) :
    bar H (g * h) = bar H g * bar H h := by
  rw [bar_of_mem (H.mul_mem hg hh), bar_of_mem hg, bar_of_mem hh, ← QuotientGroup.mk_mul]
  rfl

theorem bar_inv {H : Subgroup G} {g : G} (hg : g ∈ H) : bar H g⁻¹ = (bar H g)⁻¹ := by
  rw [bar_of_mem (H.inv_mem hg), bar_of_mem hg, ← QuotientGroup.mk_inv]
  rfl

theorem bar_pow {H : Subgroup G} {g : G} (hg : g ∈ H) (n : ℕ) : bar H (g ^ n) = bar H g ^ n := by
  rw [bar_of_mem (H.pow_mem hg n), bar_of_mem hg, ← QuotientGroup.mk_pow]
  rfl

theorem bar_one (H : Subgroup G) : bar H 1 = 1 := by
  rw [bar_of_mem H.one_mem]
  rfl

theorem bar_surjective (H : Subgroup G) (z : OTwoQuot H) : ∃ g ∈ H, bar H g = z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  exact ⟨g, g.2, bar_of_mem g.2⟩

theorem pCoreOf_subgroupOf (H : Subgroup G) :
    (pCoreOf 2 H).subgroupOf H = CFSG.Open.pCore 2 ↥H := by
  unfold pCoreOf Subgroup.subgroupOf
  exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _

theorem bar_eq_one_iff {H : Subgroup G} {g : G} (hg : g ∈ H) :
    bar H g = 1 ↔ g ∈ pCoreOf 2 H := by
  rw [bar_of_mem hg, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf, Subgroup.mem_subgroupOf]

theorem bar_eq_iff {H : Subgroup G} {g h : G} (hg : g ∈ H) (hh : h ∈ H) :
    bar H g = bar H h ↔ g⁻¹ * h ∈ pCoreOf 2 H := by
  rw [← bar_eq_one_iff (H.mul_mem (H.inv_mem hg) hh), bar_mul (H.inv_mem hg) hh, bar_inv hg,
    inv_mul_eq_one, eq_comm]

@[expose] def preimBar (H : Subgroup G) (Y : Subgroup (OTwoQuot H)) : Subgroup G :=
  (Y.comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map H.subtype

theorem mem_preimBar {H : Subgroup G} {Y : Subgroup (OTwoQuot H)} {g : G} :
    g ∈ preimBar H Y ↔ g ∈ H ∧ bar H g ∈ Y := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    refine ⟨g'.2, ?_⟩
    show bar H (g' : G) ∈ Y
    rw [bar_of_mem g'.2]
    exact hg'
  · rintro ⟨hg, hY⟩
    exact ⟨⟨g, hg⟩, by rw [bar_of_mem hg] at hY; exact hY, rfl⟩

theorem preimBar_le (H : Subgroup G) (Y : Subgroup (OTwoQuot H)) : preimBar H Y ≤ H := by
  intro g hg
  exact (mem_preimBar.mp hg).1

theorem pCoreOf_le_preimBar (H : Subgroup G) (Y : Subgroup (OTwoQuot H)) :
    pCoreOf 2 H ≤ preimBar H Y := by
  intro g hg
  have hgH : g ∈ H := pCoreOf_le 2 H hg
  refine mem_preimBar.mpr ⟨hgH, ?_⟩
  rw [(bar_eq_one_iff hgH).mpr hg]
  exact Y.one_mem

@[expose] def imBar (H S : Subgroup G) : Subgroup (OTwoQuot H) := imageOTwoQuot H S

theorem mem_imBar {H S : Subgroup G} {z : OTwoQuot H} :
    z ∈ imBar H S ↔ ∃ g, g ∈ H ∧ g ∈ S ∧ bar H g = z := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, g.2, Subgroup.mem_subgroupOf.mp hg, bar_of_mem g.2⟩
  · rintro ⟨g, hgH, hgS, rfl⟩
    exact ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hgS, (bar_of_mem hgH).symm⟩

theorem bar_mem_imBar {H S : Subgroup G} {g : G} (hH : g ∈ H) (hS : g ∈ S) :
    bar H g ∈ imBar H S :=
  mem_imBar.mpr ⟨g, hH, hS, rfl⟩

end X1512

end CFSG.Quasithin

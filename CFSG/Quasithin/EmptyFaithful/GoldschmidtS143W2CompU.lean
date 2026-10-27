module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

section Conj

variable {G : Type} [Group G] [Finite G] {H L L' : Subgroup G}

omit [Finite G] in
theorem map_conj_eq_iff {c : G} :
    L.map (MulAut.conj c).toMonoidHom = L ↔ c ∈ Subgroup.normalizer (L : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← h]; exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← h] at hy
      obtain ⟨l, hl, hly⟩ := hy
      have : l = y := by
        have : c * l * c⁻¹ = c * y * c⁻¹ := hly
        simpa using this
      rwa [this] at hl
  · intro h
    ext y
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp h l).mp hl
    · intro hy
      refine ⟨c⁻¹ * y * c, ?_, by simp [MulAut.conj_apply]; group⟩
      have e : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
      exact (Subgroup.mem_normalizer_iff.mp h (c⁻¹ * y * c)).mpr (by rw [e]; exact hy)

omit [Finite G] in
theorem isComponentIn_conj (hL : IsComponentIn L H) {c : G} (hc : c ∈ H) :
    IsComponentIn (L.map (MulAut.conj c).toMonoidHom) H := by
  have hK := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (⟨c, hc⟩ : ↥H)) hL.2
  have hmap : ((L.subgroupOf H).map (MulAut.conj (⟨c, hc⟩ : ↥H)).toMonoidHom).map H.subtype =
      L.map (MulAut.conj c).toMonoidHom := by
    ext y
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, Subgroup.mem_subgroupOf.mp hk, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨_, ⟨⟨l, hL.1 hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, rfl⟩
  rw [← hmap]
  exact isComponentIn_map hK

theorem commute_of_isComponentIn_ne (hL : IsComponentIn L H) (hL' : IsComponentIn L' H)
    (hne : L ≠ L') {a b : G} (ha : a ∈ L) (hb : b ∈ L') : a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute hL.2 hL'.2 with h | h
  · exact absurd (Subgroup.subgroupOf_inj.mp h |> fun e => by
      have e1 : L ⊓ H = L := inf_eq_left.mpr hL.1
      have e2 : L' ⊓ H = L' := inf_eq_left.mpr hL'.1
      rw [e1, e2] at e; exact e) hne
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    have ha' : (⟨a, hL.1 ha⟩ : ↥H) ∈ L.subgroupOf H := Subgroup.mem_subgroupOf.mpr ha
    have hb' : (⟨b, hL'.1 hb⟩ : ↥H) ∈ L'.subgroupOf H := Subgroup.mem_subgroupOf.mpr hb
    have := Subgroup.mem_centralizer_iff.mp (h ha') _ hb'
    exact (congrArg Subtype.val this).symm

omit [Finite G] in
theorem map_conj_inf_centralizer {c : G} (hc : c ∈ H) :
    (H ⊓ Subgroup.centralizer (L : Set G)).map (MulAut.conj c).toMonoidHom =
      H ⊓ Subgroup.centralizer ((L.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
  ext y
  constructor
  · rintro ⟨k, ⟨hkH, hkC⟩, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem hc hkH) (H.inv_mem hc), Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hkC l hl
    show c * l * c⁻¹ * (c * k * c⁻¹) = c * k * c⁻¹ * (c * l * c⁻¹)
    calc c * l * c⁻¹ * (c * k * c⁻¹) = c * (l * k) * c⁻¹ := by group
      _ = c * (k * l) * c⁻¹ := by rw [this]
      _ = c * k * c⁻¹ * (c * l * c⁻¹) := by group
  · rintro ⟨hyH, hyC⟩
    refine ⟨c⁻¹ * y * c, ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩,
      by simp [MulAut.conj_apply]; group⟩
    · exact H.mul_mem (H.mul_mem (H.inv_mem hc) hyH) hc
    · intro l hl
      have := Subgroup.mem_centralizer_iff.mp hyC (c * l * c⁻¹) ⟨l, hl, rfl⟩
      calc l * (c⁻¹ * y * c) = c⁻¹ * ((c * l * c⁻¹) * y) * c := by group
        _ = c⁻¹ * (y * (c * l * c⁻¹)) * c := by rw [this]
        _ = (c⁻¹ * y * c) * l := by group

omit [Finite G] in
theorem conj_mem_inf_centralizer' {H' : Subgroup G} (hHH' : H' ≤ H)
    (hLN : H' ≤ Subgroup.normalizer (L : Set G)) {u k : G} (hu : u ∈ H')
    (hk : k ∈ H ⊓ Subgroup.centralizer (L : Set G)) :
    u * k * u⁻¹ ∈ H ⊓ Subgroup.centralizer (L : Set G) := by
  refine ⟨H.mul_mem (H.mul_mem (hHH' hu) hk.1) (H.inv_mem (hHH' hu)),
    Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro l hl
  have hl' : u⁻¹ * l * u ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hLN (H'.inv_mem hu)) l).mp hl
    simpa using this
  have := Subgroup.mem_centralizer_iff.mp hk.2 _ hl'
  calc l * (u * k * u⁻¹) = u * ((u⁻¹ * l * u) * k) * u⁻¹ := by group
    _ = u * (k * (u⁻¹ * l * u)) * u⁻¹ := by rw [this]
    _ = (u * k * u⁻¹) * l := by group

end Conj

end InspW2

end S143

end CFSG.Quasithin

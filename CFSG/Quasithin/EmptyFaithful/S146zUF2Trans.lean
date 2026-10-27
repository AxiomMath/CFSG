module

public import CFSG.Quasithin.EmptyFaithful.S146zUF0Num
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.S146zU.UF2

section Transport

variable {Gam X X' : Type} [Group Gam] [CommGroup X] [CommGroup X']

@[expose] def transport (ρ : Gam →* MulAut X) (ρ' : Gam →* MulAut X')
    (A : Subgroup (MulAut X)) : Subgroup (MulAut X') :=
  (A.comap ρ).map ρ'

theorem mem_transport {ρ : Gam →* MulAut X} {ρ' : Gam →* MulAut X'} {A : Subgroup (MulAut X)}
    {x : MulAut X'} : x ∈ transport ρ ρ' A ↔ ∃ g, ρ g ∈ A ∧ ρ' g = x := by
  simp [transport]

theorem transport_le_range (ρ : Gam →* MulAut X) (ρ' : Gam →* MulAut X')
    (A : Subgroup (MulAut X)) : transport ρ ρ' A ≤ ρ'.range := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := mem_transport.mp hx
  exact ⟨g, rfl⟩

theorem exists_lift (ρ : Gam →* MulAut X) (ρ' : Gam →* MulAut X')
    (hk : ∀ g, ρ g = 1 → ρ' g = 1) :
    ∃ ψ : ↥ρ.range →* MulAut X', ∀ g, ψ (ρ.rangeRestrict g) = ρ' g := by
  refine ⟨MonoidHom.liftOfSurjective ρ.rangeRestrict ρ.rangeRestrict_surjective ⟨ρ', ?_⟩,
    fun g => ?_⟩
  · intro g hg
    have h1 : ρ g = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      simpa using this
    exact MonoidHom.mem_ker.mpr (hk g h1)
  · simp

variable {ρ : Gam →* MulAut X} {ρ' : Gam →* MulAut X'}

theorem card_transport (hk : ∀ g, ρ g = 1 → ρ' g = 1) (hk' : ∀ g, ρ' g = 1 → ρ g = 1)
    {A : Subgroup (MulAut X)} (hA : A ≤ ρ.range) :
    Nat.card ↥(transport ρ ρ' A) = Nat.card ↥A := by
  obtain ⟨ψ, hψ⟩ := exists_lift ρ ρ' hk
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨g, rfl⟩ := ρ.rangeRestrict_surjective a
    rw [hψ] at ha
    exact Subtype.ext (by simpa using hk' g ha)
  have heq : transport ρ ρ' A = (A.subgroupOf ρ.range).map ψ := by
    ext x
    rw [mem_transport, Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨ρ.rangeRestrict g, Subgroup.mem_subgroupOf.mpr hg, hψ g⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨g, rfl⟩ := ρ.rangeRestrict_surjective a
      exact ⟨g, Subgroup.mem_subgroupOf.mp ha, (hψ g).symm⟩
  rw [heq, Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem transport_ne_bot (hk' : ∀ g, ρ' g = 1 → ρ g = 1) {A : Subgroup (MulAut X)}
    (hA : A ≤ ρ.range) (hA1 : A ≠ ⊥) : transport ρ ρ' A ≠ ⊥ := by
  intro h
  apply hA1
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨g, rfl⟩ := hA ha
  have h1 : ρ' g ∈ transport ρ ρ' A := mem_transport.mpr ⟨g, ha, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact hk' g h1

theorem isElemAbelian2_transport (hk : ∀ g, ρ g = 1 → ρ' g = 1) {A : Subgroup (MulAut X)}
    (hA : IsElemAbelian2 A) : IsElemAbelian2 (transport ρ ρ' A) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := mem_transport.mp hx
    obtain ⟨h, hh, rfl⟩ := mem_transport.mp hy
    rw [← map_mul, ← map_mul]
    have h1 : ρ (g * h) = ρ (h * g) := by
      rw [map_mul, map_mul]
      exact hA.1 _ hg _ hh
    have h2 : ρ' ((g * h) * (h * g)⁻¹) = 1 :=
      hk _ (by rw [map_mul, map_inv, h1, mul_inv_cancel])
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2
  · obtain ⟨g, hg, rfl⟩ := mem_transport.mp hx
    rw [← map_pow]
    exact hk _ (by rw [map_pow]; exact hA.2 _ hg)

theorem mem_fixV_transport_iff {ι : X' →* X} (hι : Function.Injective ι)
    (hιρ : ∀ g v, ι (ρ' g v) = ρ g (ι v)) {A : Subgroup (MulAut X)} (hA : A ≤ ρ.range)
    {v : X'} : ι v ∈ fixV A ↔ v ∈ fixV (transport ρ ρ' A) := by
  rw [mem_fixV, mem_fixV]
  constructor
  · intro h x hx
    obtain ⟨g, hg, rfl⟩ := mem_transport.mp hx
    apply hι
    rw [hιρ, h _ hg]
  · intro h a ha
    obtain ⟨g, rfl⟩ := hA ha
    rw [← hιρ, h _ (mem_transport.mpr ⟨g, ha, rfl⟩)]

theorem mem_cF_ker_iff {Z : Type} [CommGroup Z] {ρ'' : Gam →* MulAut Z} {q : X →* Z}
    (hqρ : ∀ g y, q (ρ g y) = ρ'' g (q y)) {A : Subgroup (MulAut X)} (hA : A ≤ ρ.range)
    {y : X} : y ∈ cF A q.ker ↔ q y ∈ fixV (transport ρ ρ'' A) := by
  rw [UF0.mem_cF, mem_fixV]
  constructor
  · intro h x hx
    obtain ⟨g, hg, rfl⟩ := mem_transport.mp hx
    have h1 := h _ hg
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqρ, mul_inv_eq_one] at h1
    exact h1
  · intro h a ha
    obtain ⟨g, rfl⟩ := hA ha
    have h1 := h _ (mem_transport.mpr ⟨g, ha, rfl⟩)
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqρ, h1, mul_inv_cancel]

theorem ncard_orbit_le [Finite X] {ι : X' →* X} (hι : Function.Injective ι)
    (hιρ : ∀ g v, ι (ρ' g v) = ρ g (ι v)) (A : Subgroup (MulAut X)) (s : X') :
    (Set.range fun x : ↥(transport ρ ρ' A) => (x : MulAut X') s).ncard ≤
      (Set.range fun a : ↥A => (a : MulAut X) (ι s)).ncard := by
  have hsub : ι '' (Set.range fun x : ↥(transport ρ ρ' A) => (x : MulAut X') s) ⊆
      Set.range fun a : ↥A => (a : MulAut X) (ι s) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨g, hg, hgx⟩ := mem_transport.mp x.2
    refine ⟨⟨ρ g, hg⟩, ?_⟩
    show ρ g (ι s) = ι ((x : MulAut X') s)
    rw [← hgx, hιρ]
  rw [← Set.ncard_image_of_injective _ hι]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

end Transport

section Counting

variable {X Z : Type} [CommGroup X] [CommGroup Z]

theorem card_eq_card_ker_mul [Finite X] {q : X →* Z} (hq : Function.Surjective q) :
    Nat.card X = Nat.card ↥q.ker * Nat.card Z := by
  have h3 := Subgroup.card_mul_index q.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hq, Subgroup.card_top] at h3
  exact h3.symm

theorem card_comap_of_surjective [Finite X] {q : X →* Z} (hq : Function.Surjective q)
    (S : Subgroup Z) : Nat.card ↥(S.comap q) = Nat.card ↥q.ker * Nat.card ↥S := by
  have : Finite Z := Finite.of_surjective _ hq
  have h1 := Subgroup.card_mul_index (S.comap q)
  have h2 := Subgroup.card_mul_index S
  rw [Subgroup.index_comap_of_surjective S hq] at h1
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card ↥(S.comap q) * S.index = Nat.card X := h1
    _ = Nat.card ↥q.ker * Nat.card Z := card_eq_card_ker_mul hq
    _ = Nat.card ↥q.ker * (Nat.card ↥S * S.index) := by rw [h2]
    _ = Nat.card ↥q.ker * Nat.card ↥S * S.index := by ring

theorem card_range_of_injective {W : Type} [Group W] {Y : Type} [Group Y] {ι : W →* Y}
    (hι : Function.Injective ι) : Nat.card ↥ι.range = Nat.card W :=
  Nat.card_congr (MonoidHom.ofInjective hι).toEquiv.symm

end Counting

section Orbit

variable {X : Type} [CommGroup X]

theorem four_le_ncard_range [Finite X] (A : Subgroup (MulAut X)) (s : X)
    (h : 4 * Nat.card ↥(A ⊓ MulAction.stabilizer (MulAut X) s) ≤ Nat.card ↥A) :
    4 ≤ (Set.range fun a : ↥A => (a : MulAut X) s).ncard := by
  refine UF0.four_le_ncard_of_stabilizer A s ?_
  have hcard : Nat.card ↥(MulAction.stabilizer ↥A s) =
      Nat.card ↥(A ⊓ MulAction.stabilizer (MulAut X) s) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : MulAut X), a.1.2, ?_⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun a => rfl
        right_inv := fun x => rfl }
    · exact MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp a.2)
    · exact MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp x.2.2)
  rwa [hcard]

end Orbit

end CFSG.Quasithin.S146zU.UF2

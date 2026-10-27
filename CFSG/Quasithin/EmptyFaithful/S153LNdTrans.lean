module

public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace S153L

section Transfer

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
private theorem trans_prod_fixed {g : MulAut V} (O : Finset V) (hg : ∀ y, y ∈ O ↔ g y ∈ O) :
    g (∏ y ∈ O, y) = ∏ y ∈ O, y := by
  rw [map_prod]
  refine Finset.prod_nbij' (fun y => g y) (fun y => g⁻¹ y) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact (hg a).1 ha
  · intro a ha
    refine (hg _).2 ?_
    simpa using ha
  · intro a ha
    simp
  · intro a ha
    simp
  · intro a ha
    rfl

omit [Finite V] in
private theorem trans_mem_normalizer {X L : Subgroup (MulAut V)}
    (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) : X ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
  fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨hLn x hx l, fun h => ?_⟩
    simpa [mul_assoc] using hLn x⁻¹ (X.inv_mem hx) _ h

theorem exists_split_of_fixed (hV : ∀ v : V, v ^ 2 = 1)
    {X L S : Subgroup (MulAut V)} (hLX : L ≤ X) (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hS : IsSylowTwoOf S X) (hXLS : X ≤ L ⊔ S) {z : V} (hz : ∀ s ∈ S, (s : MulAut V) z = z) :
    ∃ u w : V, z = u * w ∧ u ∈ commV L ∧ (∀ g ∈ X, (g : MulAut V) w = w) ∧
      ∀ s ∈ S, (s : MulAut V) u = u := by
  classical
  have := Fintype.ofFinite V
  set O : Finset V := Finset.univ.filter fun y => ∃ g ∈ L, (g : MulAut V) z = y with hO
  have hmemO : ∀ y, y ∈ O ↔ ∃ g ∈ L, (g : MulAut V) z = y := fun y => by simp [hO]
  set w : V := ∏ y ∈ O, y with hw
  have hSX : ∀ s ∈ S, s ∈ X := fun s hs => hS.1 hs
  have hLw : ∀ g ∈ L, (g : MulAut V) w = w := by
    intro g hg
    refine trans_prod_fixed O fun y => ?_
    constructor
    · rintro hy
      obtain ⟨h, hh, rfl⟩ := (hmemO y).1 hy
      exact (hmemO _).2 ⟨g * h, L.mul_mem hg hh, by simp [MulAut.mul_apply]⟩
    · intro hy
      obtain ⟨h, hh, hhy⟩ := (hmemO _).1 hy
      refine (hmemO y).2 ⟨g⁻¹ * h, L.mul_mem (L.inv_mem hg) hh, ?_⟩
      have : (g⁻¹ * h : MulAut V) z = g⁻¹ (g y) := by
        rw [MulAut.mul_apply, hhy]
      rw [this]
      simp
  have hSw : ∀ s ∈ S, (s : MulAut V) w = w := by
    intro s hs
    have hsn := hLn s (hSX s hs)
    have hsn' := hLn s⁻¹ (X.inv_mem (hSX s hs))
    have hzs : (s⁻¹ : MulAut V) z = z := by
      have := hz s hs
      calc (s⁻¹ : MulAut V) z = s⁻¹ (s z) := by rw [this]
        _ = z := by simp
    refine trans_prod_fixed O fun y => ?_
    constructor
    · rintro hy
      obtain ⟨h, hh, rfl⟩ := (hmemO y).1 hy
      refine (hmemO _).2 ⟨s * h * s⁻¹, hsn h hh, ?_⟩
      simp only [MulAut.mul_apply, hzs]
    · intro hy
      obtain ⟨h, hh, hhy⟩ := (hmemO _).1 hy
      refine (hmemO y).2 ⟨s⁻¹ * h * s, by simpa using hsn' h hh, ?_⟩
      have : (s⁻¹ * h * s : MulAut V) z = s⁻¹ (h z) := by
        simp only [MulAut.mul_apply, hz s hs]
      rw [this, hhy]
      simp
  have hXw : ∀ g ∈ X, (g : MulAut V) w = w := by
    let F : Subgroup (MulAut V) := MulAction.stabilizer (MulAut V) w
    have hLF : L ≤ F := fun g hg => hLw g hg
    have hSF : S ≤ F := fun g hg => hSw g hg
    have hXF : X ≤ F := hXLS.trans (sup_le hLF hSF)
    exact fun g hg => hXF hg
  have hodd : Odd O.card := by
    have hB : IsSylowTwoOf (S ⊓ L) L :=
      B6.isSylowTwoOf_inf_normal hS hLX (trans_mem_normalizer hLn)
    have hset : (O : Set V) = MulAction.orbit ↥L z := by
      ext y
      rw [Finset.mem_coe, hmemO, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨g, hg⟩, rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨g, g.2, rfl⟩
    have hcard : O.card = Nat.card ↥(MulAction.orbit ↥L z) := by
      rw [← hset]
      exact (Nat.card_eq_finsetCard O).symm
    have hidx : (MulAction.stabilizer ↥L z).index = O.card := by
      rw [MulAction.index_stabilizer, hcard, Nat.card_coe_set_eq]
    have hle : (S ⊓ L).subgroupOf L ≤ MulAction.stabilizer ↥L z := by
      intro g hg
      rw [MulAction.mem_stabilizer_iff]
      have hgS : (g : MulAut V) ∈ S := (Subgroup.mem_subgroupOf.mp hg).1
      exact hz _ hgS
    have hdvd := Subgroup.index_dvd_of_le hle
    have h2 : ¬ 2 ∣ O.card := fun h => hB.2.2 (h.trans (hidx ▸ hdvd))
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hz2 : (z⁻¹) ^ 2 = 1 := by rw [inv_pow, hV z, inv_one]
  have hpow : (z⁻¹) ^ O.card = z⁻¹ := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, hz2, one_pow, one_mul]
  have hprod : (∏ y ∈ O, (y * z⁻¹)) ∈ commV L := by
    refine Subgroup.prod_mem _ fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := (hmemO y).1 hy
    exact Subgroup.subset_closure ⟨g, hg, z, rfl⟩
  rw [Finset.prod_mul_distrib, Finset.prod_const, hpow] at hprod
  refine ⟨z * w⁻¹, w, by simp, ?_, hXw, ?_⟩
  · have : z * w⁻¹ = (w * z⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [this]
    exact (commV L).inv_mem hprod
  · intro s hs
    rw [map_mul, map_inv, hz s hs, hSw s hs]

end Transfer

end S153L

end CFSG.Quasithin

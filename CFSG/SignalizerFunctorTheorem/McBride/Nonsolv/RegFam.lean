module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G]

structure IsRegFam (A H : Subgroup G) (Ω : Set (Subgroup G)) (N : Subgroup G) : Prop where
  isDirectProduct : IsDirectProduct Ω H
  nonempty : Ω.Nonempty
  ne_bot : ∀ L ∈ Ω, L ≠ ⊥
  map_conj_mem : ∀ a ∈ A, ∀ L ∈ Ω, L.map (MulAut.conj a).toMonoidHom ∈ Ω
  transitive : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ a ∈ A, L' = L.map (MulAut.conj a).toMonoidHom
  stabilizer : ∀ L ∈ Ω, A ⊓ Subgroup.normalizer (L : Set G) = N

namespace IsRegFam

variable {A H N : Subgroup G} {Ω : Set (Subgroup G)}

theorem map_conj_ne (hΩ : IsRegFam A H Ω N) {a : G} (ha : a ∈ A) (haN : a ∉ N) {L : Subgroup G}
    (hL : L ∈ Ω) : L.map (MulAut.conj a).toMonoidHom ≠ L := by
  intro hLa
  apply haN
  rw [← hΩ.stabilizer L hL]
  exact Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLa⟩

theorem le_left (hΩ : IsRegFam A H Ω N) : N ≤ A := by
  obtain ⟨L, hL⟩ := hΩ.nonempty
  rw [← hΩ.stabilizer L hL]
  exact inf_le_left

private theorem map_conj_one (L : Subgroup G) : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
  ext x
  simp

private theorem map_conj_map_conj (L : Subgroup G) (a b : G) :
    (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj (b * a)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, by simp [mul_assoc]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, by simp [mul_assoc]⟩

theorem card_mul_card [Finite G] (hΩ : IsRegFam A H Ω N) :
    Nat.card Ω * Nat.card N = Nat.card A := by
  obtain ⟨L₀, hL₀⟩ := hΩ.nonempty
  let _ : MulAction A Ω :=
    { smul := fun a L => ⟨L.1.map (MulAut.conj (a : G)).toMonoidHom,
        hΩ.map_conj_mem a a.2 L.1 L.2⟩
      one_smul := fun L => Subtype.ext (map_conj_one L.1)
      mul_smul := fun a b L => Subtype.ext (map_conj_map_conj L.1 (b : G) (a : G)).symm }
  let x : Ω := ⟨L₀, hL₀⟩
  have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A x)
  rw [Nat.card_prod] at h1
  let e1 : MulAction.orbit A x ≃ Ω :=
    Equiv.ofBijective (fun y => y.1) ⟨Subtype.val_injective, fun L => by
      obtain ⟨a, ha, h⟩ := hΩ.transitive L₀ hL₀ L.1 L.2
      exact ⟨⟨L, MulAction.mem_orbit_iff.mpr ⟨⟨a, ha⟩, Subtype.ext h.symm⟩⟩, rfl⟩⟩
  let e2 : MulAction.stabilizer A x ≃ N :=
    { toFun := fun v => ⟨v.1, by
        rw [← hΩ.stabilizer L₀ hL₀]
        exact Subgroup.mem_inf.mpr ⟨v.1.2, Subgroup.mem_normalizer_iff_map_conj_eq.mpr
          (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp v.2))⟩⟩
      invFun := fun g => ⟨⟨g, hΩ.le_left g.2⟩, MulAction.mem_stabilizer_iff.mpr (Subtype.ext (by
        have hg : (g : G) ∈ A ⊓ Subgroup.normalizer (L₀ : Set G) := by
          rw [hΩ.stabilizer L₀ hL₀]
          exact g.2
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.mem_inf.mp hg).2))⟩
      left_inv := fun v => rfl
      right_inv := fun g => rfl }
  rw [← Nat.card_congr e1, ← Nat.card_congr e2]
  exact h1

theorem card_eq_pow [Finite G] (hΩ : IsRegFam A H Ω N) {m : ℕ}
    (hm : ∀ L ∈ Ω, Nat.card L = m) : Nat.card H = m ^ Nat.card Ω := by
  obtain ⟨e, -⟩ := hΩ.isDirectProduct.exists_mulEquiv
  have : Fintype Ω := Fintype.ofFinite Ω
  rw [← Nat.card_congr e.toEquiv, Nat.card_pi]
  have h : ∀ J : Ω, Nat.card (J : Subgroup G) = m := fun J => hm J.1 J.2
  simp only [h, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

end IsRegFam

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

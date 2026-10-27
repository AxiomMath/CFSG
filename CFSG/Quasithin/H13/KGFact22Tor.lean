module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.KG22

open CFSG.QuasithinUnique

@[expose] def TorusOut {X : Type*} [Group X] (S : Subgroup X) (n : ℕ) : Prop :=
  ∃ (Y Y' : Subgroup X) (w : X),
    Y ≤ Subgroup.normalizer (S : Set X) ∧ Y' ≤ Subgroup.normalizer (S : Set X) ∧
    Subgroup.normalizer (S : Set X) ≤ Y ⊔ Y' ⊔ S ∧
    IsCyclic ↥Y ∧ IsCyclic ↥Y' ∧ Nat.card Y = 2 ^ n - 1 ∧
    (∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a) ∧
    w ∉ Subgroup.normalizer (S : Set X) ∧
    (∀ y ∈ Y, w * y * w⁻¹ = y⁻¹) ∧ ∀ y ∈ Y', w * y * w⁻¹ = y

section Hom

variable {G X : Type*} [Group G] [Group X]

theorem map_le_normalizer_map (f : G →* X) {A H : Subgroup G}
    (h : A ≤ Subgroup.normalizer (H : Set G)) :
    A.map f ≤ Subgroup.normalizer ((H.map f : Subgroup X) : Set X) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.1 (h ha) y).1 hy, by simp⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨a⁻¹ * y * a, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (h (A.inv_mem ha)) y).1 hy
      simpa using this
    · rw [map_mul, map_mul, hyx, map_inv]
      group

theorem isCyclic_map (f : G →* X) {Y : Subgroup G} (hY : IsCyclic ↥Y) : IsCyclic ↥(Y.map f) :=
  isCyclic_of_surjective (f.subgroupMap Y) (f.subgroupMap_surjective Y)

theorem card_map_of_injOn (f : G →* X) {Y : Subgroup G} (h : ∀ y ∈ Y, f y = 1 → y = 1) :
    Nat.card (Y.map f) = Nat.card Y := by
  refine (Nat.card_congr (Equiv.ofBijective (f.subgroupMap Y)
    ⟨?_, f.subgroupMap_surjective Y⟩)).symm
  rw [injective_iff_map_eq_one]
  intro y hy
  exact Subtype.ext (h y y.2 (congrArg Subtype.val hy))

theorem torusOut_of_hom (π : G →* X) {U B Y₀ Y₀' : Subgroup G} {w₀ : G} {n : ℕ}
    (hY₀ : Y₀ ≤ Subgroup.normalizer (U : Set G)) (hY₀' : Y₀' ≤ Subgroup.normalizer (U : Set G))
    (hN : Subgroup.normalizer ((U.map π : Subgroup X) : Set X) ≤ B.map π)
    (hB : B ≤ Y₀ ⊔ Y₀' ⊔ U) (hc : IsCyclic ↥Y₀) (hc' : IsCyclic ↥Y₀')
    (hinj : ∀ y ∈ Y₀, π y = 1 → y = 1) (hcard : Nat.card Y₀ = 2 ^ n - 1)
    (hcomm : ∀ a ∈ Y₀, ∀ b ∈ Y₀', a * b = b * a) (hw : π w₀ ∉ B.map π)
    (hinv : ∀ y ∈ Y₀, w₀ * y * w₀⁻¹ = y⁻¹) (hcen : ∀ y ∈ Y₀', w₀ * y * w₀⁻¹ = y) :
    TorusOut (U.map π) n := by
  refine ⟨Y₀.map π, Y₀'.map π, π w₀, map_le_normalizer_map π hY₀, map_le_normalizer_map π hY₀',
    ?_, isCyclic_map π hc, isCyclic_map π hc', (card_map_of_injOn π hinj).trans hcard, ?_,
    fun h => hw (hN h), ?_, ?_⟩
  · refine hN.trans ((Subgroup.map_mono hB).trans ?_)
    rw [Subgroup.map_sup, Subgroup.map_sup]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, hinv y hy, map_inv]
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, hcen y hy]

end Hom

section Equiv

variable {X X' : Type*} [Group X] [Group X']

theorem map_map_symm (e : X ≃* X') (H : Subgroup X) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  ext x
  simp

theorem TorusOut.map (e : X ≃* X') {S : Subgroup X} {n : ℕ} (h : TorusOut S n) :
    TorusOut (S.map e.toMonoidHom) n := by
  obtain ⟨Y, Y', w, hY, hY', hN, hc, hc', hcard, hcomm, hw, hinv, hcen⟩ := h
  have hN' : Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup X') : Set X') ≤
      (Subgroup.normalizer (S : Set X)).map e.toMonoidHom := by
    intro x hx
    have h1 := map_le_normalizer_map e.symm.toMonoidHom (le_refl _) ⟨x, hx, rfl⟩
    rw [map_map_symm] at h1
    exact ⟨e.symm x, h1, by simp⟩
  refine ⟨Y.map e.toMonoidHom, Y'.map e.toMonoidHom, e w,
    map_le_normalizer_map _ hY, map_le_normalizer_map _ hY', ?_, isCyclic_map _ hc,
    isCyclic_map _ hc', ?_, ?_, fun h => hw ?_, ?_, ?_⟩
  · refine hN'.trans ((Subgroup.map_mono hN).trans ?_)
    rw [Subgroup.map_sup, Subgroup.map_sup]
  · rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · obtain ⟨x, hx, hxw⟩ := hN' h
    have : x = w := e.injective hxw
    rwa [← this]
  · rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hinv y hy, map_inv]
  · rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hcen y hy]

theorem exists_sylow_of_isSylowTwoOf {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  exact ⟨hS.2.1.toSylow hi, rfl⟩

theorem isSylowTwoOf_of_sylow [Finite X] (P : Sylow 2 X) : IsSylowTwoOf (P : Subgroup X) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [show ((P : Subgroup X).subgroupOf ⊤).index = (P : Subgroup X).index from
    Subgroup.relIndex_top_right _]
  exact P.not_dvd_index

theorem torusOut_of_sylow [Finite X] {n : ℕ} (S₀ : Sylow 2 X) (h : TorusOut (S₀ : Subgroup X) n)
    {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) : TorusOut S n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, rfl⟩ := exists_sylow_of_isSylowTwoOf hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₀ P
  have h1 := h.map (MulAut.conj g)
  have h2 : (S₀ : Subgroup X).map (MulAut.conj g).toMonoidHom = (P : Subgroup X) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  rwa [h2] at h1

theorem torusOut_of_equiv [Finite X] (e : X ≃* X') {n : ℕ}
    (h : ∀ S' : Subgroup X', IsSylowTwoOf S' ⊤ → TorusOut S' n) {S : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) : TorusOut S n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, rfl⟩ := exists_sylow_of_isSylowTwoOf hS
  have hsurj : Function.Surjective (e.toMonoidHom : X → X') := e.surjective
  have : Finite X' := Finite.of_surjective e e.surjective
  have h1 := h _ (isSylowTwoOf_of_sylow (P.mapSurjective hsurj))
  rw [Sylow.coe_mapSurjective] at h1
  have h2 := h1.map e.symm
  rwa [map_map_symm] at h2

end Equiv

end CFSG.Quasithin.H13.KG22

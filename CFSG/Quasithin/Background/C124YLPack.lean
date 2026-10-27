module

public import CFSG.Quasithin.Background.C124YLBase
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationOffender

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups

variable {W : Type*} [CommGroup W]

structure Package (Pk Ls : Subgroup (MulAut W)) (U Z : Subgroup W)
    (K Y : Subgroup (MulAut W)) : Prop where
  K_le : K ≤ Ls
  woff : WOff U Z K
  tight : Nat.card U = Nat.card K * Nat.card (liftFix U Z K)
  cent : ∀ x ∈ Pk, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ Subgroup.normalizer (K : Set (MulAut W)) →
    (∀ u ∈ liftFix U Z K, x u * u⁻¹ ∈ Z) → x ∈ K
  Y_le : Y ≤ Ls
  sylow : IsSylowTwoOf K Y
  sl2 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧ Nonempty (↥Y ≃* SL(2, F))
  moves : ∃ u ∈ liftFix U Z K, ∃ y ∈ Y, y u * u⁻¹ ∉ Z
  gen : Ls = Y ⊔ (Ls ⊓ Subgroup.normalizer (K : Set (MulAut W)))

section Conj

variable {Pk Ls : Subgroup (MulAut W)} {U Z : Subgroup W} {K Y : Subgroup (MulAut W)}

theorem normalizer_conjAut {x l : MulAut W} (h : x ∈ Subgroup.normalizer
    ((B1.conjAut l K : Subgroup (MulAut W)) : Set (MulAut W))) :
    l⁻¹ * x * l ∈ Subgroup.normalizer (K : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro k
  have h1 := h (l * k * l⁻¹)
  rw [B1.mem_conjAut, B1.mem_conjAut] at h1
  have e1 : l⁻¹ * (l * k * l⁻¹) * l = k := by group
  have e2 : l⁻¹ * (x * (l * k * l⁻¹) * x⁻¹) * l = (l⁻¹ * x * l) * k * (l⁻¹ * x * l)⁻¹ := by
    group
  rw [e1, e2] at h1
  exact h1

theorem isSylowTwoOf_conjAut {l : MulAut W} (h : IsSylowTwoOf K Y) :
    IsSylowTwoOf (B1.conjAut l K) (B1.conjAut l Y) := by
  refine ⟨?_, ?_, ?_⟩
  · exact B1.conjAut_le_iff.2 h.1
  · intro ⟨x, hx⟩
    have hx' : l⁻¹ * x * l ∈ K := B1.mem_conjAut.1 hx
    obtain ⟨k, hk⟩ := h.2.1 ⟨l⁻¹ * x * l, hx'⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h2 : (l⁻¹ * x * l) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : (l⁻¹ * x * l) ^ 2 ^ k = l⁻¹ * x ^ 2 ^ k * l := by
      simpa using conj_pow (a := l⁻¹) (b := x) (i := 2 ^ k)
    rw [h3] at h2
    have h4 : x ^ 2 ^ k = 1 := by
      have := congrArg (fun t => l * t * l⁻¹) h2
      simpa [mul_assoc] using this
    exact h4
  · have h2 := h.2.2
    show ¬ 2 ∣ ((B1.conjAut l K).relIndex (B1.conjAut l Y))
    have : (B1.conjAut l K).relIndex (B1.conjAut l Y) = K.relIndex Y := by
      rw [conjAut_eq_map, conjAut_eq_map]
      exact Subgroup.relIndex_map_map_of_injective K Y (MulAut.conj l).injective
    rw [this]
    exact h2

theorem Package.conj (P : Package Pk Ls U Z K Y) {l : MulAut W} (hl : l ∈ Ls)
    (hU : ∀ u, u ∈ U ↔ l u ∈ U) (hZ : ∀ z, z ∈ Z ↔ l z ∈ Z)
    (hPk : ∀ x ∈ Pk, l⁻¹ * x * l ∈ Pk) :
    Package Pk Ls U Z (B1.conjAut l K) (B1.conjAut l Y) := by
  have hZinv : ∀ z ∈ Z, l⁻¹ z ∈ Z := fun z hz => (hZ _).2 (by simpa using hz)
  refine ⟨B1.conjAut_le hl P.K_le, P.woff.conj l hU hZ, ?_, ?_, B1.conjAut_le hl P.Y_le,
    isSylowTwoOf_conjAut P.sylow, ?_, ?_, ?_⟩
  · rw [card_liftFix_conjAut U Z l hU hZ, B1.card_conjAut]
    exact P.tight
  · intro x hx h2 hn hfix
    have hx' := hPk x hx
    have hn' := normalizer_conjAut hn
    have h2' : ∃ k : ℕ, (l⁻¹ * x * l) ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := h2
      refine ⟨k, ?_⟩
      have h3 : (l⁻¹ * x * l) ^ 2 ^ k = l⁻¹ * x ^ 2 ^ k * l := by
        simpa using conj_pow (a := l⁻¹) (b := x) (i := 2 ^ k)
      rw [h3, hk]
      simp
    have hfix' : ∀ u ∈ liftFix U Z K, (l⁻¹ * x * l) u * u⁻¹ ∈ Z := by
      intro u hu
      have hlu : l u ∈ liftFix U Z (B1.conjAut l K) := by
        rw [liftFix_conjAut U Z l hU hZ K]
        exact ⟨u, hu, rfl⟩
      have h5 := hZinv _ (hfix (l u) hlu)
      have e : (l⁻¹ * x * l) u * u⁻¹ = l⁻¹ (x (l u) * (l u)⁻¹) := by
        simp [MulAut.mul_apply]
      rw [e]
      exact h5
    exact B1.mem_conjAut.2 (P.cent _ hx' h2' hn' hfix')
  · obtain ⟨F, i1, i2, hF, ⟨e⟩⟩ := P.sl2
    refine ⟨F, i1, i2, hF, ⟨?_⟩⟩
    have hmap : B1.conjAut l Y = Y.map (MulAut.conj l).toMonoidHom := conjAut_eq_map l Y
    exact ((MulEquiv.subgroupCongr hmap).trans
      (Y.equivMapOfInjective _ (MulAut.conj l).injective).symm).trans e
  · obtain ⟨u, hu, y, hy, hyu⟩ := P.moves
    refine ⟨l u, ?_, l * y * l⁻¹, B1.mem_conjAut.2 (by simpa [mul_assoc] using hy), ?_⟩
    · rw [liftFix_conjAut U Z l hU hZ K]
      exact ⟨u, hu, rfl⟩
    · intro h
      apply hyu
      have : l (y u * u⁻¹) = (l * y * l⁻¹) (l u) * (l u)⁻¹ := by
        simp [MulAut.mul_apply]
      exact (hZ _).2 (this ▸ h)
  · apply le_antisymm _ (sup_le (B1.conjAut_le hl P.Y_le) inf_le_left)
    intro x hx
    have hx' : l⁻¹ * x * l ∈ Ls := Ls.mul_mem (Ls.mul_mem (Ls.inv_mem hl) hx) hl
    rw [P.gen] at hx'
    have hmem : x ∈ B1.conjAut l (Y ⊔ (Ls ⊓ Subgroup.normalizer (K : Set (MulAut W)))) :=
      B1.mem_conjAut.2 hx'
    have hsup : B1.conjAut l (Y ⊔ (Ls ⊓ Subgroup.normalizer (K : Set (MulAut W)))) =
        B1.conjAut l Y ⊔ B1.conjAut l (Ls ⊓ Subgroup.normalizer (K : Set (MulAut W))) := by
      simp only [conjAut_eq_map]
      exact Subgroup.map_sup _ _ _
    rw [hsup] at hmem
    have hle : B1.conjAut l Y ⊔ B1.conjAut l (Ls ⊓ Subgroup.normalizer (K : Set (MulAut W))) ≤
        B1.conjAut l Y ⊔ (Ls ⊓ Subgroup.normalizer
          ((B1.conjAut l K : Subgroup (MulAut W)) : Set (MulAut W))) := by
      refine sup_le_sup_left ?_ _
      intro z hz
      have hz' := B1.mem_conjAut.1 hz
      refine ⟨?_, ?_⟩
      · have := Ls.mul_mem (Ls.mul_mem hl hz'.1) (Ls.inv_mem hl)
        simpa [mul_assoc] using this
      · refine Subgroup.mem_normalizer_iff.2 fun k => ?_
        have hk := (Subgroup.mem_normalizer_iff.1 hz'.2) (l⁻¹ * k * l)
        rw [B1.mem_conjAut, B1.mem_conjAut]
        have e1 : l⁻¹ * (z * k * z⁻¹) * l =
            (l⁻¹ * z * l) * (l⁻¹ * k * l) * (l⁻¹ * z * l)⁻¹ := by group
        rw [e1]
        exact hk
    exact hle hmem

end Conj

section Classify

variable [Finite W] {Ls P0 K0 : Subgroup (MulAut W)} {U Z : Subgroup W}

theorem isPGroup_of_isElemAbelian2 {B : Subgroup (MulAut W)} (h : IsElemAbelian2 B) :
    IsPGroup 2 ↥B := by
  intro ⟨x, hx⟩
  refine ⟨1, Subtype.ext ?_⟩
  simpa using h.2 x hx

theorem classify_of_sylow (hP0 : IsSylowTwoOf P0 Ls) (hK0 : ∀ B ≤ P0, WOff U Z B → B = K0)
    (hU : ∀ l ∈ Ls, ∀ u, u ∈ U ↔ l u ∈ U) (hZ : ∀ l ∈ Ls, ∀ z, z ∈ Z ↔ l z ∈ Z)
    {B : Subgroup (MulAut W)} (hBL : B ≤ Ls) (hB : WOff U Z B) :
    ∃ l ∈ Ls, B = B1.conjAut l K0 := by
  obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf hP0 hBL (isPGroup_of_isElemAbelian2 hB.2.1)
  have hle' : B1.conjAut h B ≤ P0 := by rwa [conjAut_eq_map]
  have hW := hB.conj h (hU h hh) (hZ h hh)
  have heq := hK0 _ hle' hW
  refine ⟨h⁻¹, Ls.inv_mem hh, ?_⟩
  rw [← heq, B1.conjAut_inv_conjAut]

theorem unique_of_sylow (hP0 : IsSylowTwoOf P0 Ls) (hK0 : ∀ B ≤ P0, WOff U Z B → B = K0)
    (hU : ∀ l ∈ Ls, ∀ u, u ∈ U ↔ l u ∈ U) (hZ : ∀ l ∈ Ls, ∀ z, z ∈ Z ↔ l z ∈ Z)
    {B B' : Subgroup (MulAut W)} (hBL : B ≤ Ls) (hB'L : B' ≤ Ls) (hB : WOff U Z B)
    (hB' : WOff U Z B') (h2 : IsPGroup 2 ↥(B ⊔ B')) : B = B' := by
  obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf hP0 (sup_le hBL hB'L) h2
  have h1 : B1.conjAut h B ≤ P0 := by
    rw [conjAut_eq_map]
    exact (Subgroup.map_mono le_sup_left).trans hle
  have h1' : B1.conjAut h B' ≤ P0 := by
    rw [conjAut_eq_map]
    exact (Subgroup.map_mono le_sup_right).trans hle
  have e1 := hK0 _ h1 (hB.conj h (hU h hh) (hZ h hh))
  have e2 := hK0 _ h1' (hB'.conj h (hU h hh) (hZ h hh))
  rw [← B1.conjAut_inv_conjAut h B, ← B1.conjAut_inv_conjAut h B', e1, e2]

end Classify

end CFSG.Quasithin.C124.YL

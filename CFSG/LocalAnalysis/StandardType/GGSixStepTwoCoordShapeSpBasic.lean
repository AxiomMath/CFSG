module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeAlign
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpComp

public section

open Matrix Multiplicative CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt mat_elt E)

namespace CFSG.StandardType

namespace CoordSp

open CoordShape

section Joint

variable {F : Type} [Field F] {n p : ℕ} [Fact p.Prime] {T : Set (Fin n → ZMod p)}

theorem spAligned_of_zero_one (hp2 : p ≠ 2) {β : Fin n → ZMod p}
    (hβ : ∀ i, β i = 0 ∨ β i = 1) : SpAligned β := by
  intro i j hij
  rcases hβ i with h | h
  · exact h
  · exfalso
    rcases hβ j with h' | h'
    · rw [h, h'] at hij
      exact (one_ne_zero : (1 : ZMod p) ≠ 0) (hij.trans neg_zero)
    · rw [h, h'] at hij
      exact ne_neg_self hp2 one_ne_zero hij

theorem eq_zero_of_eq_neg_joint (hp2 : p ≠ 2) (hal : JointAligned (signs p) T) {i j : Fin n}
    (h : ∀ t ∈ T, t i = -t j) : ∀ t ∈ T, t i = 0 ∧ t j = 0 := by
  have h1 := hal i j (-1) (mem_signs.mpr (Or.inr rfl)) fun t ht => by
    rw [Units.val_neg, Units.val_one, neg_one_mul]
    exact h t ht
  intro t ht
  have h2 : t j = -t j := (h1 t ht).symm.trans (h t ht)
  have htj : t j = 0 := by
    by_contra hne
    exact ne_neg_self hp2 hne h2
  exact ⟨by rw [h1 t ht, htj], htj⟩

theorem wtPres_of_joint (hp2 : p ≠ 2) (hal : JointAligned (signs p) T)
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hM : ∀ t ∈ T, WtPres t M)
    {β : Fin n → ZMod p} (hβ0 : ∀ i, (∀ t ∈ T, t i = 0) → β i = 0)
    (hβc : ∀ i j, (∀ t ∈ T, t i = t j) → β i = β j) : WtPres β M := by
  intro a b hab
  by_contra hne
  have hw : ∀ t ∈ T, spWt t a = spWt t b := fun t ht => by
    by_contra h
    exact hne (hM t ht a b h)
  apply hab
  rcases a with i | i <;> rcases b with j | j
  · exact hβc i j fun t ht => by simpa using hw t ht
  · have h0 := eq_zero_of_eq_neg_joint hp2 hal (i := i) (j := j) fun t ht => hw t ht
    show β i = -β j
    rw [hβ0 i fun t ht => (h0 t ht).1, hβ0 j fun t ht => (h0 t ht).2]
    exact neg_zero.symm
  · have h0 := eq_zero_of_eq_neg_joint hp2 hal (i := j) (j := i) fun t ht => (hw t ht).symm
    show -β i = β j
    rw [hβ0 i fun t ht => (h0 t ht).2, hβ0 j fun t ht => (h0 t ht).1]
    exact neg_zero
  · simp only [spWt_inr]
    rw [hβc i j fun t ht => by simpa using hw t ht]

theorem offDiag_eq_zero_of_comm_blocks_joint (hp2 : p ≠ 2) (hal : JointAligned (signs p) T)
    {u : StatedSp n F} (hu : ∀ t ∈ T, WtPres t (mat n F u))
    (hZ : ∀ M ∈ suppGroup (planeSet (spClass (jointSupp T) 0)), u * M = M * u)
    (hC : ∀ j, (∃ t ∈ T, t j ≠ 0) →
      ∀ M ∈ (classHom (F := F) (spClass (jointClass T j) 1)).range, u * M = M * u) :
    ∀ a b, a ≠ b → mat n F u a b = 0 := by
  intro a b hab
  by_cases hw : ∀ t ∈ T, spWt t a = spWt t b
  swap
  · push Not at hw
    obtain ⟨t, ht, hne⟩ := hw
    exact hu t ht a b hne
  have hcomm : ∀ M : StatedSp n F, u * M = M * u →
      mat n F u * mat n F M = mat n F M * mat n F u := fun M h => by
    rw [← map_mul, ← map_mul, h]
  rcases b with i | i
  · by_cases h0 : ∀ t ∈ T, t i = 0
    · have h := hcomm _ (hZ _ (elt_long_mem_zeroBlock (jointSupp_eq_zero_iff.mpr h0)).1)
      rw [mat_elt_positiveLong_one] at h
      exact col_eq_zero_of_commute_single h hab
    · have hi : ∃ t ∈ T, t i ≠ 0 := by
        push Not at h0
        exact h0
      rcases a with j | j
      · have hji : j ≠ i := fun h => hab (by rw [h])
        have hjX : jointClass T i j = 1 := jointClass_eq_one_iff.mpr fun t ht => by
          simpa using hw t ht
        have hiX : jointClass T i i = 1 := jointClass_eq_one_iff.mpr fun _ _ => rfl
        have h := hcomm _ (hC i hi _ (elt_diff_mem_classBlock hp2 one_ne_zero hji.symm hiX hjX))
        rw [mat_elt_difference_one] at h
        exact (col_eq_zero_of_commute_diff Sum.inl_ne_inr h hab Sum.inl_ne_inr).1
      · exfalso
        refine h0 fun t ht => (eq_zero_of_eq_neg_joint hp2 hal (i := i) (j := j) (fun t ht => ?_)
          t ht).1
        have h := hw t ht
        simp only [spWt_inl, spWt_inr] at h
        exact h.symm
  · by_cases h0 : ∀ t ∈ T, t i = 0
    · have h := hcomm _ (hZ _ (elt_long_mem_zeroBlock (jointSupp_eq_zero_iff.mpr h0)).2)
      rw [mat_elt_negativeLong_one] at h
      exact col_eq_zero_of_commute_single h hab
    · have hi : ∃ t ∈ T, t i ≠ 0 := by
        push Not at h0
        exact h0
      rcases a with j | j
      · exfalso
        refine h0 fun t ht => (eq_zero_of_eq_neg_joint hp2 hal (i := j) (j := i) (fun t ht => ?_)
          t ht).2
        have h := hw t ht
        simp only [spWt_inl, spWt_inr] at h
        exact h
      · have hji : j ≠ i := fun h => hab (by rw [h])
        have hjX : jointClass T i j = 1 := jointClass_eq_one_iff.mpr fun t ht => by
          have h := hw t ht
          simp only [spWt_inr, neg_inj] at h
          exact h
        have hiX : jointClass T i i = 1 := jointClass_eq_one_iff.mpr fun _ _ => rfl
        have h := hcomm _ (hC i hi _ (elt_diff_mem_classBlock hp2 one_ne_zero hji hjX hiX))
        rw [mat_elt_difference_one] at h
        exact (col_eq_zero_of_commute_diff Sum.inl_ne_inr h Sum.inr_ne_inl hab).2

theorem commute_of_comm_blocks_joint (hp2 : p ≠ 2) (hal : JointAligned (signs p) T)
    {u v : StatedSp n F} (hu : ∀ t ∈ T, WtPres t (mat n F u))
    (hv : ∀ t ∈ T, WtPres t (mat n F v))
    (hZu : ∀ M ∈ suppGroup (planeSet (spClass (jointSupp T) 0)), u * M = M * u)
    (hZv : ∀ M ∈ suppGroup (planeSet (spClass (jointSupp T) 0)), v * M = M * v)
    (hCu : ∀ j, (∃ t ∈ T, t j ≠ 0) →
      ∀ M ∈ (classHom (F := F) (spClass (jointClass T j) 1)).range, u * M = M * u)
    (hCv : ∀ j, (∃ t ∈ T, t j ≠ 0) →
      ∀ M ∈ (classHom (F := F) (spClass (jointClass T j) 1)).range, v * M = M * v) :
    u * v = v * u := by
  apply mat_injective
  rw [map_mul, map_mul]
  exact mul_comm_of_offDiag_eq_zero (offDiag_eq_zero_of_comm_blocks_joint hp2 hal hu hZu hCu)
    (offDiag_eq_zero_of_comm_blocks_joint hp2 hal hv hZv hCv)

end Joint

section Flip

variable {G : Type} [Group G] {F : Type} [Field F] {n p : ℕ} [NeZero p] {ζ : Fˣ}

@[expose] def flipSign (sw : Fin n → Bool) (i : Fin n) : (ZMod p)ˣ :=
  if sw i then -1 else 1

theorem frameHom_flipSign [CharP F 2] (ψ : StatedSp n F →* G) (A₀ : StatedSp n F)
    (hζ : ζ ^ p = 1) (sw : Fin n → Bool) (t : Fin n → ZMod p) :
    frameHom ψ (A₀ * (spPerm sw (Equiv.refl (Fin n)))⁻¹) hζ
        (ofAdd fun i => ((flipSign sw i : (ZMod p)ˣ) : ZMod p) * t i) =
      frameHom ψ A₀ hζ (ofAdd t) := by
  set P := spPerm (F := F) sw (Equiv.refl (Fin n)) with hP
  have key : P⁻¹ * spDiag (fun i => ζ ^ (((flipSign sw i : (ZMod p)ˣ) : ZMod p) * t i).val) * P =
      spDiag fun i => ζ ^ (t i).val := by
    rw [hP, spPerm_conj_spDiag]
    congr 1
    funext i
    simp only [Equiv.refl_apply]
    by_cases h : sw i = true
    · have hη : ((flipSign sw i : (ZMod p)ˣ) : ZMod p) * t i = -t i := by simp [flipSign, h]
      rw [ite_eq_left h, hη, pow_val_neg hζ, inv_inv]
    · have hη : ((flipSign sw i : (ZMod p)ˣ) : ZMod p) * t i = t i := by simp [flipSign, h]
      rw [ite_eq_right h, hη]
  change ψ ((A₀ * P⁻¹) * spDiag (fun i => ζ ^ (((flipSign sw i : (ZMod p)ˣ) : ZMod p) * t i).val) *
      (A₀ * P⁻¹)⁻¹) = ψ (A₀ * spDiag (fun i => ζ ^ (t i).val) * A₀⁻¹)
  rw [← key]
  congr 1
  group

omit [NeZero p] in
theorem eq_flipSign {η : Fin n → (ZMod p)ˣ} (hη : ∀ i, η i ∈ signs p) (i : Fin n) :
    η i = flipSign (fun i => decide (η i ≠ 1)) i := by
  unfold flipSign
  by_cases h1 : η i = 1
  · simp [h1]
  · simp only [h1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    exact (mem_signs.mp (hη i)).resolve_left h1

theorem centralizer_eq_map_joint {ψ : StatedSp n F →* G} (hψ : Function.Injective ψ)
    (A₀ : StatedSp n F) (hζ : ζ ^ p = 1) {E : Subgroup G}
    (hE : E ≤ (frameHom ψ A₀ hζ).range) :
    ψ.range ⊓ Subgroup.centralizer (E : Set G) =
      (Subgroup.centralizer {Y | ∃ t : Fin n → ZMod p, frameHom ψ A₀ hζ (ofAdd t) ∈ E ∧
        Y = torusElt ζ t}).map (frameConj ψ A₀) := by
  rw [← range_frameConj ψ A₀]
  ext x
  constructor
  · rintro ⟨⟨y, rfl⟩, hc⟩
    refine ⟨y, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
    rintro _ ⟨t, ht, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ ht
    rw [frameHom_eq_frameConj] at h1
    exact frameConj_injective hψ A₀ (by rw [map_mul, map_mul, h1])
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    obtain ⟨a, rfl⟩ := hE he
    have h1 := Subgroup.mem_centralizer_iff.mp hy _ ⟨toAdd a, he, rfl⟩
    change frameConj ψ A₀ (torusElt ζ (toAdd a)) * frameConj ψ A₀ y =
      frameConj ψ A₀ y * frameConj ψ A₀ (torusElt ζ (toAdd a))
    rw [← map_mul, ← map_mul, h1]

end Flip

end CoordSp

end CFSG.StandardType

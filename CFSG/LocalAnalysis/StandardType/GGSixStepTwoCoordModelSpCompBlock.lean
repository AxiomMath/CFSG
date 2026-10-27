module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpCompBasic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLevi
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple

public section

open Matrix Multiplicative CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt mat_elt E)

namespace CFSG.StandardType

namespace CoordSp

section Classes

variable {F : Type} [Field F] {n p : ℕ}

@[expose] def SpAligned (β : Fin n → ZMod p) : Prop :=
  ∀ i j, β i = -β j → β i = 0

@[expose] def spClass (β : Fin n → ZMod p) (c : ZMod p) : Finset (Fin n) :=
  Finset.univ.filter fun i => β i = c

@[simp] theorem mem_spClass {β : Fin n → ZMod p} {c : ZMod p} {i : Fin n} :
    i ∈ spClass β c ↔ β i = c := by
  simp [spClass]

theorem spClass_enum (β : Fin n → ZMod p) (c : ZMod p) (k : Fin (spClass β c).card) :
    β (enum (spClass β c) k) = c :=
  mem_spClass.mp (enum_mem _ k)

theorem ne_neg_self [Fact p.Prime] (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0) : c ≠ -c := by
  intro h
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h0')
  have h3 : (2 : ZMod p) * c = 0 := by
    calc (2 : ZMod p) * c = c + c := two_mul c
      _ = c + -c := by rw [← h]
      _ = 0 := add_neg_cancel c
  exact hc ((mul_eq_zero.mp h3).resolve_left h2)

theorem eq_inl_of_spWt_eq {β : Fin n → ZMod p} (hal : SpAligned β) {c : ZMod p} (hc : c ≠ 0)
    {i₀ : Fin n} (hi₀ : β i₀ = c) {x : Fin n ⊕ Fin n} (hx : spWt β x = c) :
    ∃ i, x = Sum.inl i ∧ β i = c := by
  rcases x with i | i
  · exact ⟨i, rfl, hx⟩
  · exfalso
    rw [spWt_inr] at hx
    have h1 : β i = -β i₀ := by rw [hi₀, ← hx, neg_neg]
    exact hc (by rw [← hx, hal i i₀ h1, neg_zero])

theorem mem_planeSet_zero_iff {β : Fin n → ZMod p} {x : Fin n ⊕ Fin n} :
    x ∈ planeSet (spClass β 0) ↔ spWt β x = 0 := by
  rcases x with i | i
  · simp
  · simp [neg_eq_zero]

theorem planeSet_zero_union (β : Fin n → ZMod p) (a b : Fin n ⊕ Fin n)
    (h : spWt β a = spWt β b) :
    a ∈ planeSet (spClass β 0) ↔ b ∈ planeSet (spClass β 0) := by
  rw [mem_planeSet_zero_iff, mem_planeSet_zero_iff, h]

theorem planeSet_class_union {β : Fin n → ZMod p} (hal : SpAligned β) (c : ZMod p)
    (a b : Fin n ⊕ Fin n) (h : spWt β a = spWt β b) :
    a ∈ planeSet (spClass β c) ↔ b ∈ planeSet (spClass β c) := by
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [spWt_inl, spWt_inr, inl_mem_planeSet, inr_mem_planeSet, mem_spClass] at h ⊢
  · rw [h]
  · have h1 := hal i j h
    have h2 : β j = 0 := by rw [← neg_eq_zero, ← h, h1]
    rw [h1, h2]
  · have h1 := hal j i h.symm
    have h2 : β i = 0 := by rw [← neg_eq_zero, h, h1]
    rw [h1, h2]
  · rw [neg_inj.mp h]

end Classes

section EBlock

variable {F : Type} [Field F] {n p : ℕ}

@[expose] def eBlock (s : Finset (Fin n)) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :
    Matrix (Fin s.card) (Fin s.card) F :=
  M.submatrix (fun k => Sum.inl (enum s k)) fun k => Sum.inl (enum s k)

omit [Field F] in
theorem eBlock_apply (s : Finset (Fin n)) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (k l : Fin s.card) : eBlock s M k l = M (Sum.inl (enum s k)) (Sum.inl (enum s l)) :=
  rfl

theorem inl_enum_injective (s : Finset (Fin n)) :
    Function.Injective fun k : Fin s.card => (Sum.inl (enum s k) : Fin n ⊕ Fin n) :=
  fun _ _ h => enum_injective s (Sum.inl_injective h)

theorem eBlock_one (s : Finset (Fin n)) :
    eBlock s (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 :=
  submatrix_one _ (inl_enum_injective s)

theorem eBlock_mul {β : Fin n → ZMod p} (hal : SpAligned β) {c : ZMod p} (hc : c ≠ 0)
    {U V : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hU : WtPres β U) :
    eBlock (spClass β c) (U * V) = eBlock (spClass β c) U * eBlock (spClass β c) V := by
  ext k l
  simp only [eBlock_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (fun k' => (Sum.inl (enum (spClass β c) k') : Fin n ⊕ Fin n))
    (inl_enum_injective _) _ _ (fun x hx => ?_) fun k' => rfl
  by_cases hw : spWt β (Sum.inl (enum (spClass β c) k)) = spWt β x
  · exfalso
    have hk := spClass_enum β c k
    obtain ⟨i, rfl, hi⟩ := eq_inl_of_spWt_eq hal hc hk (hw.symm.trans hk)
    obtain ⟨k', rfl⟩ := exists_enum_eq (mem_spClass.mpr hi)
    exact hx ⟨k', rfl⟩
  · rw [hU _ _ hw, zero_mul]

theorem prod_pow_val [NeZero p] {M : Type*} [CommMonoid M] {x : M} (hx : x ^ p = 1)
    {ι : Type*} (s : Finset ι) (f : ι → ZMod p) :
    ∏ i ∈ s, x ^ (f i).val = x ^ (∑ i ∈ s, f i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, CoordSL.pow_val_add hx]

theorem sum_enum (s : Finset (Fin n)) {M : Type*} [AddCommMonoid M] (f : Fin n → M) :
    ∑ k, f (enum s k) = ∑ i ∈ s, f i := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ s rfl]
  rw [Finset.sum_map]
  rfl

end EBlock

section ClassHom

variable {F : Type} [Field F] {n p : ℕ}

@[expose] noncomputable def classHom (s : Finset (Fin n)) :
    Matrix.SpecialLinearGroup (Fin s.card) F →* StatedSp n F :=
  (blockSp s).comp (leviEmbedSL F s.card)

theorem classHom_injective (s : Finset (Fin n)) : Function.Injective (classHom (F := F) s) :=
  (blockSp_injective s).comp leviEmbedSL_injective

theorem classHom_mem_suppGroup (s : Finset (Fin n))
    (A : Matrix.SpecialLinearGroup (Fin s.card) F) :
    classHom s A ∈ suppGroup (planeSet s) :=
  blockSp_mem_suppGroup s _

theorem mat_classHom_apply (s : Finset (Fin n)) (A : Matrix.SpecialLinearGroup (Fin s.card) F)
    (x y : Fin s.card ⊕ Fin s.card) :
    mat n F (classHom s A) (Sum.map (enum s) (enum s) x) (Sum.map (enum s) (enum s) y) =
      fromBlocks (A : Matrix (Fin s.card) (Fin s.card) F) 0 0
        ((A⁻¹ : Matrix.SpecialLinearGroup (Fin s.card) F) :
          Matrix (Fin s.card) (Fin s.card) F)ᵀ x y := by
  change mat n F (blockSp s (leviEmbedSL F s.card A)) _ _ = _
  rw [mat_blockSp_apply_image, mat_leviEmbedSL]

theorem eBlock_classHom (s : Finset (Fin n)) (A : Matrix.SpecialLinearGroup (Fin s.card) F) :
    eBlock s (mat n F (classHom s A)) = A := by
  ext k l
  exact mat_classHom_apply s A (Sum.inl k) (Sum.inl l)

theorem wtPres_classHom (β : Fin n → ZMod p) (c : ZMod p)
    (A : Matrix.SpecialLinearGroup (Fin (spClass β c).card) F) :
    WtPres β (mat n F (classHom (spClass β c) A)) := by
  intro a b hab
  have hk : ∀ k, β (enum (spClass β c) k) = c := spClass_enum β c
  by_cases hin : a ∈ planeSet (spClass β c) ∧ b ∈ planeSet (spClass β c)
  · obtain ⟨ha, hb⟩ := hin
    rw [← range_sumMap_enum] at ha hb
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    rw [mat_classHom_apply]
    rcases x with k | k <;> rcases y with l | l
    · exact (hab (by simp [hk])).elim
    · rfl
    · rfl
    · exact (hab (by simp [hk])).elim
  · rw [(mem_suppGroup.mp (classHom_mem_suppGroup _ A)) a b hin,
      Matrix.one_apply_ne fun h => hab (congrArg (spWt β) h)]

theorem mem_range_classHom [Fact p.Prime] (hp2 : p ≠ 2) {β : Fin n → ZMod p} {c : ZMod p}
    (hc : c ≠ 0) {M : StatedSp n F} (hM : WtPres β (mat n F M))
    (hS : M ∈ suppGroup (planeSet (spClass β c)))
    (hdet : (eBlock (spClass β c) (mat n F M)).det = 1) :
    M ∈ (classHom (F := F) (spClass β c)).range := by
  have hcc := ne_neg_self hp2 hc
  have hk : ∀ k, β (enum (spClass β c) k) = c := spClass_enum β c
  rw [← range_blockSp] at hS
  obtain ⟨M', rfl⟩ := hS
  have hent : ∀ x y, mat (spClass β c).card F M' x y =
      mat n F (blockSp (spClass β c) M') (Sum.map (enum (spClass β c)) (enum (spClass β c)) x)
        (Sum.map (enum (spClass β c)) (enum (spClass β c)) y) :=
    fun x y => (mat_blockSp_apply_image _ M' x y).symm
  have hwl : ∀ k, spWt β (Sum.map (enum (spClass β c)) (enum (spClass β c)) (Sum.inl k)) = c :=
    hk
  have hwr : ∀ k, spWt β (Sum.map (enum (spClass β c)) (enum (spClass β c)) (Sum.inr k)) = -c :=
    fun k => by
      change -β (enum (spClass β c) k) = -c
      rw [hk k]
  have h12 : ∀ k l, mat (spClass β c).card F M' (Sum.inl k) (Sum.inr l) = 0 := fun k l => by
    rw [hent]
    exact hM _ _ (by rw [hwl, hwr]; exact hcc)
  have h21 : ∀ k l, mat (spClass β c).card F M' (Sum.inr k) (Sum.inl l) = 0 := fun k l => by
    rw [hent]
    exact hM _ _ (by rw [hwl, hwr]; exact hcc.symm)
  set A : Matrix (Fin (spClass β c).card) (Fin (spClass β c).card) F :=
    Matrix.of fun k l => mat (spClass β c).card F M' (Sum.inl k) (Sum.inl l) with hA
  set D : Matrix (Fin (spClass β c).card) (Fin (spClass β c).card) F :=
    Matrix.of fun k l => mat (spClass β c).card F M' (Sum.inr k) (Sum.inr l) with hD
  have hM' : mat (spClass β c).card F M' = fromBlocks A 0 0 D := by
    ext x y
    rcases x with k | k <;> rcases y with l | l
    · rfl
    · exact h12 k l
    · exact h21 k l
    · rfl
  have hdetA : A.det = 1 := by
    have hAe : A = eBlock (spClass β c) (mat n F (blockSp (spClass β c) M')) := by
      ext k l
      exact hent (Sum.inl k) (Sum.inl l)
    rw [hAe]
    exact hdet
  have hsymp := mat_transpose_mul_gram_mul M'
  rw [hM', CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply] at hsymp
  have hAD : Aᵀ * D = 1 := by
    have h := (fromBlocks_inj.mp hsymp).2.1
    simpa using h
  let A' : Matrix.SpecialLinearGroup (Fin (spClass β c).card) F := ⟨A, hdetA⟩
  refine ⟨A', ?_⟩
  change blockSp (spClass β c) (leviEmbedSL F _ A') = blockSp (spClass β c) M'
  congr 1
  apply mat_injective
  rw [mat_leviEmbedSL, hM']
  have hinv : ((A'⁻¹ : Matrix.SpecialLinearGroup (Fin (spClass β c).card) F) :
      Matrix (Fin (spClass β c).card) (Fin (spClass β c).card) F)ᵀ = D := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    have hadj : adjugate A = A⁻¹ := by
      rw [Matrix.inv_def, hdetA, Ring.inverse_one, one_smul]
    change (adjugate A)ᵀ = D
    rw [hadj, Matrix.transpose_nonsing_inv, Matrix.inv_eq_right_inv hAD]
  rw [hinv]

theorem conj_mem_range_classHom [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Fˣ} (hζ : ζ ^ p = 1)
    (hζo : orderOf ζ = p) {β : Fin n → ZMod p} (hal : SpAligned β) {c : ZMod p} (hc : c ≠ 0)
    {u M : StatedSp n F} (hu : u * torusElt ζ β = torusElt ζ β * u)
    (hM : M ∈ (classHom (F := F) (spClass β c)).range) :
    u * M * u⁻¹ ∈ (classHom (F := F) (spClass β c)).range := by
  obtain ⟨A, rfl⟩ := hM
  have hU := (commute_torusElt_iff hζ hζo β u).mp hu
  have hU' := (commute_torusElt_iff hζ hζo β u⁻¹).mp (commute_torusElt_inv hu)
  have hMw := wtPres_classHom β c A
  refine mem_range_classHom hp2 hc ?_ ?_ ?_
  · rw [map_mul, map_mul]
    exact (hU.mul hMw).mul hU'
  · rw [mem_suppGroup, map_mul, map_mul]
    exact isSupp_conj (planeSet_class_union hal c) hU hU'
      (by rw [← map_mul, mul_inv_cancel, map_one]) (classHom_mem_suppGroup _ A)
  · rw [map_mul, map_mul, eBlock_mul hal hc (hU.mul hMw), eBlock_mul hal hc hU, eBlock_classHom,
      det_mul, det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one, ← det_mul,
      ← eBlock_mul hal hc hU, ← map_mul, mul_inv_cancel, map_one, eBlock_one, det_one]

end ClassHom

section Torus

variable {F : Type} [Field F] {n p : ℕ}

theorem wtPres_torusElt [NeZero p] {ζ : Fˣ} (hζ : ζ ^ p = 1) (β t : Fin n → ZMod p) :
    WtPres β (mat n F (torusElt ζ t)) := by
  rw [mat_torusElt hζ]
  exact wtPres_diagonal β _

theorem torusElt_mem_suppGroup [NeZero p] {ζ : Fˣ} (hζ : ζ ^ p = 1) {s : Finset (Fin n)}
    {t : Fin n → ZMod p} (ht : ∀ i, i ∉ s → t i = 0) :
    torusElt ζ t ∈ suppGroup (planeSet s) := by
  rw [mem_suppGroup, mat_torusElt hζ]
  intro r r' hrr
  by_cases h : r = r'
  · subst h
    have hr : r ∉ planeSet s := fun hr => hrr ⟨hr, hr⟩
    rw [diagonal_apply_eq, Matrix.one_apply_eq]
    rcases r with i | i
    · rw [spWt_inl, ht i hr, ZMod.val_zero, pow_zero, Units.val_one]
    · rw [spWt_inr, ht i hr, neg_zero, ZMod.val_zero, pow_zero, Units.val_one]
  · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem eBlock_torusElt [NeZero p] {ζ : Fˣ} (hζ : ζ ^ p = 1) (s : Finset (Fin n))
    (t : Fin n → ZMod p) :
    eBlock s (mat n F (torusElt ζ t)) =
      diagonal fun k => ((ζ ^ (t (enum s k)).val : Fˣ) : F) := by
  rw [mat_torusElt hζ, eBlock, submatrix_diagonal _ _ (inl_enum_injective s)]
  rfl

theorem torusElt_mem_range_classHom [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Fˣ} (hζ : ζ ^ p = 1)
    {β : Fin n → ZMod p} {c : ZMod p} (hc : c ≠ 0) {t : Fin n → ZMod p}
    (ht : ∀ i, β i ≠ c → t i = 0) (hsum : ∑ i, t i = 0) :
    torusElt ζ t ∈ (classHom (F := F) (spClass β c)).range := by
  refine mem_range_classHom hp2 hc (wtPres_torusElt hζ β t)
    (torusElt_mem_suppGroup hζ fun i hi => ht i fun h => hi (mem_spClass.mpr h)) ?_
  rw [eBlock_torusElt hζ, det_diagonal, ← Units.coe_prod, prod_pow_val hζ, sum_enum]
  have hs : ∑ i ∈ spClass β c, t i = ∑ i, t i :=
    Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ht i fun h => hi (mem_spClass.mpr h)
  rw [hs, hsum, ZMod.val_zero, pow_zero, Units.val_one]

theorem torusElt_comm_zeroBlock [NeZero p] {ζ : Fˣ} (hζ : ζ ^ p = 1) {β t : Fin n → ZMod p}
    (ht : ∀ i, β i = 0 → t i = 0) {M : StatedSp n F}
    (hM : M ∈ suppGroup (planeSet (spClass β 0))) :
    torusElt ζ t * M = M * torusElt ζ t := by
  apply mat_injective
  rw [map_mul, map_mul, mat_torusElt hζ]
  apply diagonal_mul_comm
  intro a b hab
  by_cases hin : a ∈ planeSet (spClass β 0) ∧ b ∈ planeSet (spClass β 0)
  · have h1 : ∀ x ∈ planeSet (spClass β 0), spWt t x = 0 := by
      intro x hx
      rcases x with i | i
      · exact ht i (mem_spClass.mp (inl_mem_planeSet.mp hx))
      · rw [spWt_inr, ht i (mem_spClass.mp (inr_mem_planeSet.mp hx)), neg_zero]
    rw [h1 a hin.1, h1 b hin.2]
  · rw [(mem_suppGroup.mp hM) a b hin] at hab
    have hab' : a = b := by
      by_contra h
      exact hab (Matrix.one_apply_ne h)
    rw [hab']

theorem torusElt_comm_classBlock [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Fˣ} (hζ : ζ ^ p = 1)
    {β t : Fin n → ZMod p} {c : ZMod p} (hc : c ≠ 0)
    (ht : ∀ i j, β i = c → β j = c → t i = t j) {M : StatedSp n F}
    (hMw : WtPres β (mat n F M)) (hM : M ∈ suppGroup (planeSet (spClass β c))) :
    torusElt ζ t * M = M * torusElt ζ t := by
  have hcc := ne_neg_self hp2 hc
  apply mat_injective
  rw [map_mul, map_mul, mat_torusElt hζ]
  apply diagonal_mul_comm
  intro a b hab
  by_cases hin : a ∈ planeSet (spClass β c) ∧ b ∈ planeSet (spClass β c)
  · have hw : spWt β a = spWt β b := by
      by_contra h
      exact hab (hMw a b h)
    obtain ⟨ha, hb⟩ := hin
    rcases a with i | i <;> rcases b with j | j
    · have hi := mem_spClass.mp (inl_mem_planeSet.mp ha)
      have hj := mem_spClass.mp (inl_mem_planeSet.mp hb)
      rw [spWt_inl, spWt_inl, ht i j hi hj]
    · exfalso
      have hi := mem_spClass.mp (inl_mem_planeSet.mp ha)
      have hj := mem_spClass.mp (inr_mem_planeSet.mp hb)
      rw [spWt_inl, spWt_inr, hi, hj] at hw
      exact hcc hw
    · exfalso
      have hi := mem_spClass.mp (inr_mem_planeSet.mp ha)
      have hj := mem_spClass.mp (inl_mem_planeSet.mp hb)
      rw [spWt_inr, spWt_inl, hi, hj] at hw
      exact hcc hw.symm
    · have hi := mem_spClass.mp (inr_mem_planeSet.mp ha)
      have hj := mem_spClass.mp (inr_mem_planeSet.mp hb)
      rw [spWt_inr, spWt_inr, ht i j hi hj]
  · rw [(mem_suppGroup.mp hM) a b hin] at hab
    have hab' : a = b := by
      by_contra h
      exact hab (Matrix.one_apply_ne h)
    rw [hab']

end Torus

section RootBlocks

variable {F : Type} [Field F] {n p : ℕ}

theorem mat_elt_positiveLong_one (i : Fin n) :
    mat n F (elt (.positiveLong i) 1) = 1 + single (Sum.inl i) (Sum.inr i) 1 := by
  rw [mat_elt, one_smul]
  rfl

theorem mat_elt_negativeLong_one (i : Fin n) :
    mat n F (elt (.negativeLong i) 1) = 1 + single (Sum.inr i) (Sum.inl i) 1 := by
  rw [mat_elt, one_smul]
  rfl

theorem mat_elt_difference_one (i j : Fin n) (hij : i ≠ j) :
    mat n F (elt (.difference i j hij) 1) =
      1 + (single (Sum.inl i) (Sum.inl j) 1 - single (Sum.inr j) (Sum.inr i) 1) := by
  rw [mat_elt, one_smul]
  rfl

theorem elt_long_mem_zeroBlock {β : Fin n → ZMod p} {i : Fin n} (hi : β i = 0) :
    elt (.positiveLong i) (1 : F) ∈ suppGroup (planeSet (spClass β 0)) ∧
      elt (.negativeLong i) (1 : F) ∈ suppGroup (planeSet (spClass β 0)) := by
  have hl : (Sum.inl i : Fin n ⊕ Fin n) ∈ planeSet (spClass β 0) :=
    inl_mem_planeSet.mpr (mem_spClass.mpr hi)
  have hr : (Sum.inr i : Fin n ⊕ Fin n) ∈ planeSet (spClass β 0) :=
    inr_mem_planeSet.mpr (mem_spClass.mpr hi)
  constructor
  · rw [mem_suppGroup, mat_elt_positiveLong_one]
    intro r t hrt
    rw [Matrix.add_apply, single_apply, ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hrt ⟨hl, hr⟩
  · rw [mem_suppGroup, mat_elt_negativeLong_one]
    intro r t hrt
    rw [Matrix.add_apply, single_apply, ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hrt ⟨hr, hl⟩

theorem elt_diff_mem_classBlock [Fact p.Prime] (hp2 : p ≠ 2) {β : Fin n → ZMod p} {c : ZMod p}
    (hc : c ≠ 0) {i j : Fin n} (hij : i ≠ j) (hi : β i = c) (hj : β j = c) :
    elt (.difference i j hij) (1 : F) ∈ (classHom (F := F) (spClass β c)).range := by
  have hm := mat_elt_difference_one (F := F) i j hij
  refine mem_range_classHom hp2 hc ?_ ?_ ?_
  · rw [hm]
    intro a b hab
    have hne : a ≠ b := fun h => hab (congrArg (spWt β) h)
    rw [Matrix.add_apply, Matrix.sub_apply, single_apply, single_apply, Matrix.one_apply_ne hne,
      zero_add, ite_eq_right, ite_eq_right, sub_zero]
    all_goals
      rintro ⟨rfl, rfl⟩
      exact hab (by simp [hi, hj])
  · rw [mem_suppGroup, hm]
    intro r t hrt
    rw [Matrix.add_apply, Matrix.sub_apply, single_apply, single_apply, ite_eq_right,
      ite_eq_right, sub_zero, add_zero]
    all_goals
      rintro ⟨rfl, rfl⟩
      exact hrt ⟨by simp [hi, hj], by simp [hi, hj]⟩
  · obtain ⟨k, hk⟩ := exists_enum_eq (mem_spClass.mpr hi)
    obtain ⟨l, hl⟩ := exists_enum_eq (mem_spClass.mpr hj)
    have hkl : k ≠ l := fun h => hij (by rw [← hk, ← hl, h])
    have he : eBlock (spClass β c) (mat n F (elt (.difference i j hij) 1)) =
        Matrix.transvection k l 1 := by
      rw [hm]
      ext k' l'
      simp only [eBlock_apply, Matrix.add_apply, Matrix.sub_apply, single_apply,
        Matrix.transvection, Matrix.one_apply, Sum.inl.injEq, reduceCtorEq, false_and,
        ite_false, sub_zero, ← hk, ← hl, (enum_injective _).eq_iff]
    rw [he]
    exact Matrix.det_transvection_of_ne (h := hkl) ..

theorem offDiag_eq_zero_of_comm_blocks [Fact p.Prime] (hp2 : p ≠ 2) {β : Fin n → ZMod p}
    (hal : SpAligned β) {u : StatedSp n F} (hu : WtPres β (mat n F u))
    (hZ : ∀ M ∈ suppGroup (planeSet (spClass β 0)), u * M = M * u)
    (hC : ∀ c, c ≠ 0 → ∀ M ∈ (classHom (F := F) (spClass β c)).range, u * M = M * u) :
    ∀ a b, a ≠ b → mat n F u a b = 0 := by
  intro a b hab
  by_cases hw : spWt β a = spWt β b
  swap
  · exact hu a b hw
  have hcomm : ∀ M : StatedSp n F, u * M = M * u →
      mat n F u * mat n F M = mat n F M * mat n F u := fun M h => by
    rw [← map_mul, ← map_mul, h]
  rcases b with i | i
  · by_cases h0 : β i = 0
    · have h := hcomm _ (hZ _ (elt_long_mem_zeroBlock h0).1)
      rw [mat_elt_positiveLong_one] at h
      exact col_eq_zero_of_commute_single h hab
    · obtain ⟨j, rfl, hj⟩ := eq_inl_of_spWt_eq hal h0 rfl hw
      have hji : j ≠ i := fun h => hab (by rw [h])
      have h := hcomm _ (hC _ h0 _ (elt_diff_mem_classBlock hp2 h0 hji.symm rfl hj))
      rw [mat_elt_difference_one] at h
      exact (col_eq_zero_of_commute_diff Sum.inl_ne_inr h hab Sum.inl_ne_inr).1
  · by_cases h0 : β i = 0
    · have h := hcomm _ (hZ _ (elt_long_mem_zeroBlock h0).2)
      rw [mat_elt_negativeLong_one] at h
      exact col_eq_zero_of_commute_single h hab
    · rcases a with j | j
      · exfalso
        rw [spWt_inl, spWt_inr] at hw
        exact h0 (neg_eq_zero.mp (hw.symm.trans (hal j i hw)))
      · rw [spWt_inr, spWt_inr, neg_inj] at hw
        have hji : j ≠ i := fun h => hab (by rw [h])
        have h := hcomm _ (hC _ h0 _ (elt_diff_mem_classBlock hp2 h0 hji hw rfl))
        rw [mat_elt_difference_one] at h
        exact (col_eq_zero_of_commute_diff Sum.inl_ne_inr h Sum.inr_ne_inl hab).2

theorem commute_of_comm_blocks [Fact p.Prime] (hp2 : p ≠ 2) {β : Fin n → ZMod p}
    (hal : SpAligned β) {u v : StatedSp n F} (hu : WtPres β (mat n F u))
    (hv : WtPres β (mat n F v))
    (hZu : ∀ M ∈ suppGroup (planeSet (spClass β 0)), u * M = M * u)
    (hZv : ∀ M ∈ suppGroup (planeSet (spClass β 0)), v * M = M * v)
    (hCu : ∀ c, c ≠ 0 → ∀ M ∈ (classHom (F := F) (spClass β c)).range, u * M = M * u)
    (hCv : ∀ c, c ≠ 0 → ∀ M ∈ (classHom (F := F) (spClass β c)).range, v * M = M * v) :
    u * v = v * u := by
  apply mat_injective
  rw [map_mul, map_mul]
  exact mul_comm_of_offDiag_eq_zero (offDiag_eq_zero_of_comm_blocks hp2 hal hu hZu hCu)
    (offDiag_eq_zero_of_comm_blocks hp2 hal hv hZv hCv)

end RootBlocks

end CoordSp

end CFSG.StandardType

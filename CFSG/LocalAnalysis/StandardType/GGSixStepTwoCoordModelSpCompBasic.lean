module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSp
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs

public section

open Matrix Multiplicative CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

namespace CFSG.StandardType

namespace CoordSp

section Weights

variable {F : Type} [Field F] {n p : ℕ}

@[expose] def spWt (β : Fin n → ZMod p) : Fin n ⊕ Fin n → ZMod p :=
  Sum.elim β fun i => -β i

@[simp] theorem spWt_inl (β : Fin n → ZMod p) (i : Fin n) : spWt β (Sum.inl i) = β i :=
  rfl

@[simp] theorem spWt_inr (β : Fin n → ZMod p) (i : Fin n) : spWt β (Sum.inr i) = -β i :=
  rfl

@[expose] noncomputable def torusElt (ζ : Fˣ) (β : Fin n → ZMod p) : StatedSp n F :=
  spDiag fun i => ζ ^ (β i).val

theorem mat_spDiag (u : Fin n → Fˣ) :
    mat n F (spDiag u) = diagonal fun x => ((TableBSymp.pairedUnits u x : Fˣ) : F) := by
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_spDiag, TauCeti.diagGL_coe]

theorem mat_torusElt [NeZero p] {ζ : Fˣ} (hζ : ζ ^ p = 1) (β : Fin n → ZMod p) :
    mat n F (torusElt ζ β) = diagonal fun x => ((ζ ^ (spWt β x).val : Fˣ) : F) := by
  rw [torusElt, mat_spDiag]
  congr 1
  funext x
  rcases x with i | i
  · rfl
  · change (((ζ ^ (β i).val)⁻¹ : Fˣ) : F) = ((ζ ^ (-β i).val : Fˣ) : F)
    rw [pow_val_neg hζ]

theorem frameHom_eq_torusElt {G : Type} [Group G] [NeZero p] (ψ : StatedSp n F →* G)
    (A₀ : StatedSp n F) {ζ : Fˣ} (hζ : ζ ^ p = 1) (t : Fin n → ZMod p) :
    frameHom ψ A₀ hζ (ofAdd t) = ψ (A₀ * torusElt ζ t * A₀⁻¹) :=
  rfl

theorem eq_of_pow_val_eq [NeZero p] {ζ : Fˣ} (hζo : orderOf ζ = p) {a b : ZMod p}
    (h : ζ ^ a.val = ζ ^ b.val) : a = b := by
  have h1 := pow_eq_pow_iff_modEq.mp h
  rw [hζo] at h1
  have h2 : a.val % p = b.val % p := h1
  rw [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h2
  exact ZMod.val_injective p h2

@[expose] def WtPres (β : Fin n → ZMod p) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :
    Prop :=
  ∀ a b, spWt β a ≠ spWt β b → M a b = 0

theorem WtPres.mul {β : Fin n → ZMod p} {U V : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hU : WtPres β U) (hV : WtPres β V) : WtPres β (U * V) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : spWt β a = spWt β x
  · rw [hV x b fun h => hab (hx.trans h), mul_zero]
  · rw [hU a x hx, zero_mul]

theorem wtPres_diagonal (β : Fin n → ZMod p) (d : Fin n ⊕ Fin n → F) :
    WtPres β (diagonal d) := fun _ _ hab =>
  diagonal_apply_ne _ fun h => hab (h ▸ rfl)

theorem commute_torusElt_iff [NeZero p] {ζ : Fˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (β : Fin n → ZMod p) (u : StatedSp n F) :
    u * torusElt ζ β = torusElt ζ β * u ↔ WtPres β (mat n F u) := by
  rw [← mat_injective.eq_iff, map_mul, map_mul, mat_torusElt hζ]
  constructor
  · intro h a b hab
    have e := congrFun (congrFun h a) b
    rw [mul_diagonal, diagonal_mul] at e
    by_contra hne
    exact hab
      (eq_of_pow_val_eq hζo (Units.ext (mul_left_cancel₀ hne (e.trans (mul_comm _ _))))).symm
  · intro h
    ext a b
    rw [mul_diagonal, diagonal_mul]
    by_cases hab : spWt β a = spWt β b
    · rw [hab, mul_comm]
    · rw [h a b hab, zero_mul, mul_zero]

theorem commute_torusElt_inv {ζ : Fˣ} {β : Fin n → ZMod p} {u : StatedSp n F}
    (hu : u * torusElt ζ β = torusElt ζ β * u) :
    u⁻¹ * torusElt ζ β = torusElt ζ β * u⁻¹ := by
  calc u⁻¹ * torusElt ζ β = u⁻¹ * (torusElt ζ β * u) * u⁻¹ := by group
    _ = u⁻¹ * (u * torusElt ζ β) * u⁻¹ := by rw [hu]
    _ = torusElt ζ β * u⁻¹ := by group

theorem torusElt_mul_comm (ζ : Fˣ) (β t : Fin n → ZMod p) :
    torusElt ζ t * torusElt ζ β = torusElt ζ β * torusElt ζ t := by
  rw [torusElt, torusElt, ← spDiag_mul, ← spDiag_mul, mul_comm]

theorem diagonal_mul_comm {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → F}
    {M : Matrix ι ι F} (h : ∀ a b, M a b ≠ 0 → d a = d b) :
    diagonal d * M = M * diagonal d := by
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases hab : M a b = 0
  · rw [hab, zero_mul, mul_zero]
  · rw [h a b hab, mul_comm]

theorem mul_comm_of_offDiag_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Matrix ι ι F} (hU : ∀ a b, a ≠ b → U a b = 0) (hV : ∀ a b, a ≠ b → V a b = 0) :
    U * V = V * U := by
  have e : ∀ W : Matrix ι ι F, (∀ a b, a ≠ b → W a b = 0) → W = diagonal fun a => W a a := by
    intro W hW
    ext a b
    by_cases h : a = b
    · subst h
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ h, hW a b h]
  rw [e U hU, e V hV, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

end Weights

section Supports

variable {F : Type} [Field F] {n p : ℕ}

theorem isSupp_conj {β : Fin n → ZMod p} {T : Set (Fin n ⊕ Fin n)}
    (hT : ∀ a b, spWt β a = spWt β b → (a ∈ T ↔ b ∈ T))
    {U U' M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hU : WtPres β U) (hU' : WtPres β U')
    (hUU' : U * U' = 1) (hM : IsSupp T M) : IsSupp T (U * M * U') := by
  intro r t hrt
  rw [not_and_or] at hrt
  rcases hrt with hr | ht
  · have h1 : ∀ x, U r x * (M * U') x t = U r x * U' x t := by
      intro x
      by_cases hx : U r x = 0
      · rw [hx, zero_mul, zero_mul]
      · have hxT : x ∉ T := fun h =>
          hr ((hT r x (not_not.mp fun h' => hx (hU r x h'))).mpr h)
        have hrow : ∀ y, M x y = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y :=
          fun y => hM x y fun h => hxT h.1
        congr 1
        rw [Matrix.mul_apply]
        simp only [hrow]
        rw [← Matrix.mul_apply, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_congr rfl fun x _ => h1 x,
      ← Matrix.mul_apply, hUU']
  · have h2 : ∀ y, (U * M) r y * U' y t = U r y * U' y t := by
      intro y
      by_cases hy : U' y t = 0
      · rw [hy, mul_zero, mul_zero]
      · have hyT : y ∉ T := fun h =>
          ht ((hT y t (not_not.mp fun h' => hy (hU' y t h'))).mp h)
        have hcol : ∀ x, M x y = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y :=
          fun x => hM x y fun h => hyT h.2
        congr 1
        rw [Matrix.mul_apply]
        simp only [hcol]
        rw [← Matrix.mul_apply, Matrix.mul_one]
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun y _ => h2 y, ← Matrix.mul_apply, hUU']

theorem conj_mem_suppGroup [NeZero p] {ζ : Fˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    {β : Fin n → ZMod p} {T : Set (Fin n ⊕ Fin n)}
    (hT : ∀ a b, spWt β a = spWt β b → (a ∈ T ↔ b ∈ T)) {u M : StatedSp n F}
    (hu : u * torusElt ζ β = torusElt ζ β * u) (hM : M ∈ suppGroup T) :
    u * M * u⁻¹ ∈ suppGroup T := by
  rw [mem_suppGroup, map_mul, map_mul]
  exact isSupp_conj hT ((commute_torusElt_iff hζ hζo β u).mp hu)
    ((commute_torusElt_iff hζ hζo β u⁻¹).mp (commute_torusElt_inv hu))
    (by rw [← map_mul, mul_inv_cancel, map_one]) hM

@[expose] def planeOf : Fin n ⊕ Fin n → Fin n :=
  Sum.elim id id

@[expose] def planeSet (s : Finset (Fin n)) : Set (Fin n ⊕ Fin n) :=
  {x | planeOf x ∈ s}

@[simp] theorem inl_mem_planeSet {s : Finset (Fin n)} {i : Fin n} :
    (Sum.inl i : Fin n ⊕ Fin n) ∈ planeSet s ↔ i ∈ s :=
  Iff.rfl

@[simp] theorem inr_mem_planeSet {s : Finset (Fin n)} {i : Fin n} :
    (Sum.inr i : Fin n ⊕ Fin n) ∈ planeSet s ↔ i ∈ s :=
  Iff.rfl

@[expose] def enum (s : Finset (Fin n)) : Fin s.card → Fin n :=
  s.orderEmbOfFin rfl

theorem enum_injective (s : Finset (Fin n)) : Function.Injective (enum s) :=
  (s.orderEmbOfFin rfl).injective

theorem enum_mem (s : Finset (Fin n)) (k : Fin s.card) : enum s k ∈ s :=
  s.orderEmbOfFin_mem rfl k

theorem exists_enum_eq {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) : ∃ k, enum s k = i := by
  have h : i ∈ Set.range (s.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hi
  exact h

theorem range_sumMap_enum (s : Finset (Fin n)) :
    Set.range (Sum.map (enum s) (enum s)) = planeSet s := by
  ext x
  constructor
  · rintro ⟨y | y, rfl⟩
    · exact inl_mem_planeSet.mpr (enum_mem s y)
    · exact inr_mem_planeSet.mpr (enum_mem s y)
  · intro hx
    rcases x with i | i
    · obtain ⟨k, rfl⟩ := exists_enum_eq (inl_mem_planeSet.mp hx)
      exact ⟨Sum.inl k, rfl⟩
    · obtain ⟨k, rfl⟩ := exists_enum_eq (inr_mem_planeSet.mp hx)
      exact ⟨Sum.inr k, rfl⟩

@[expose] noncomputable def blockSp (s : Finset (Fin n)) : StatedSp s.card F →* StatedSp n F :=
  spEmbed (enum s) (enum_injective s)

theorem blockSp_injective (s : Finset (Fin n)) : Function.Injective (blockSp (F := F) s) :=
  spEmbed_injective (enum_injective s)

theorem range_blockSp (s : Finset (Fin n)) :
    (blockSp (F := F) s).range = suppGroup (planeSet s) := by
  rw [blockSp, range_spEmbed, range_sumMap_enum]

theorem blockSp_mem_suppGroup (s : Finset (Fin n)) (g : StatedSp s.card F) :
    blockSp s g ∈ suppGroup (planeSet s) := by
  rw [← range_blockSp]
  exact ⟨g, rfl⟩

theorem mat_blockSp_apply_image (s : Finset (Fin n)) (g : StatedSp s.card F)
    (x y : Fin s.card ⊕ Fin s.card) :
    mat n F (blockSp s g) (Sum.map (enum s) (enum s) x) (Sum.map (enum s) (enum s) y) =
      mat s.card F g x y := by
  rw [blockSp, mat_spEmbed, spEmbedMat_apply_image (enum_injective s)]

end Supports

section RootElements

variable {F : Type} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem col_eq_zero_of_commute_single {U : Matrix ι ι F} {a b : ι}
    (h : U * (1 + single a b 1) = (1 + single a b 1) * U) {x : ι} (hx : x ≠ a) : U x a = 0 := by
  have h' : U * single a b 1 = single a b 1 * U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  have e := congrFun (congrFun h' x) b
  rwa [mul_single_apply_same, single_mul_apply_of_ne (h := hx), mul_one] at e

theorem col_eq_zero_of_commute_diff {U : Matrix ι ι F} {a b a' b' : ι} (hbb : b ≠ b')
    (h : U * (1 + (single a b 1 - single a' b' 1)) = (1 + (single a b 1 - single a' b' 1)) * U)
    {x : ι} (hx : x ≠ a) (hx' : x ≠ a') : U x a = 0 ∧ U x a' = 0 := by
  have h' : U * (single a b 1 - single a' b' 1) = (single a b 1 - single a' b' 1) * U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  rw [Matrix.mul_sub, Matrix.sub_mul] at h'
  have e1 := congrFun (congrFun h' x) b
  have e2 := congrFun (congrFun h' x) b'
  simp only [Matrix.sub_apply] at e1 e2
  rw [mul_single_apply_same, mul_single_apply_of_ne (hbj := hbb), single_mul_apply_of_ne (h := hx),
    single_mul_apply_of_ne (h := hx'), mul_one, sub_zero, sub_zero] at e1
  rw [mul_single_apply_of_ne (hbj := hbb.symm), mul_single_apply_same,
    single_mul_apply_of_ne (h := hx), single_mul_apply_of_ne (h := hx'), mul_one, zero_sub,
    sub_zero, neg_eq_zero] at e2
  exact ⟨e1, e2⟩

end RootElements

end CoordSp

end CFSG.StandardType

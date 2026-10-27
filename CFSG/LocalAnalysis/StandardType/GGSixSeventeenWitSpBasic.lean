module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCores
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.LieType.Universal.Symplectic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.StandardType

namespace WitSp

open Matrix hiding gram gram_apply
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {n : ℕ}

@[expose] def swapCoord (S : Finset (Fin n)) : Fin n ⊕ Fin n → Fin n ⊕ Fin n
  | Sum.inl i => if i ∈ S then Sum.inr i else Sum.inl i
  | Sum.inr i => if i ∈ S then Sum.inl i else Sum.inr i

theorem swapCoord_swapCoord (S : Finset (Fin n)) (a : Fin n ⊕ Fin n) :
    swapCoord S (swapCoord S a) = a := by
  rcases a with i | i <;> by_cases hi : i ∈ S <;> simp [swapCoord, hi]

theorem swapCoord_par (S : Finset (Fin n)) (a : Fin n ⊕ Fin n) :
    swapCoord S (par a) = par (swapCoord S a) := by
  rcases a with i | i <;> by_cases hi : i ∈ S <;> simp [swapCoord, hi]

@[expose] def swapMat (S : Finset (Fin n)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.of fun a b => if b = swapCoord S a then 1 else 0

theorem swapMat_apply (S : Finset (Fin n)) (a b : Fin n ⊕ Fin n) :
    swapMat (K := K) S a b = if b = swapCoord S a then 1 else 0 := rfl

theorem swapMat_mul_apply (S : Finset (Fin n)) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (a b : Fin n ⊕ Fin n) : (swapMat (K := K) S * M) a b = M (swapCoord S a) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (swapCoord S a)]
  · rw [swapMat_apply, ite_eq_left rfl, one_mul]
  · intro c _ hc
    rw [swapMat_apply, ite_eq_right hc, zero_mul]
  · simp

theorem mul_swapMat_apply (S : Finset (Fin n)) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (a b : Fin n ⊕ Fin n) : (M * swapMat (K := K) S) a b = M a (swapCoord S b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (swapCoord S b)]
  · rw [swapMat_apply, swapCoord_swapCoord, ite_eq_left rfl, mul_one]
  · intro c _ hc
    rw [swapMat_apply, ite_eq_right (fun h => hc (by rw [h, swapCoord_swapCoord])), mul_zero]
  · simp

theorem swapMat_mul_swapMat (S : Finset (Fin n)) : swapMat (K := K) S * swapMat S = 1 := by
  ext a b
  rw [swapMat_mul_apply, swapMat_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp [swapCoord_swapCoord]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', swapCoord_swapCoord]))]

theorem transpose_swapMat (S : Finset (Fin n)) : (swapMat (K := K) S)ᵀ = swapMat S := by
  ext a b
  rw [transpose_apply, swapMat_apply, swapMat_apply]
  by_cases h : a = swapCoord S b
  · rw [ite_eq_left h, ite_eq_left (by rw [h, swapCoord_swapCoord])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', swapCoord_swapCoord]))]

theorem swapMat_symplectic [CharP K 2] (S : Finset (Fin n)) :
    (swapMat (K := K) S)ᵀ * gram K n * swapMat S = gram K n := by
  have hsgn : ∀ a : Fin n ⊕ Fin n, sgn K a = 1 := by
    intro a
    rcases a with i | i
    · rfl
    · rw [sgn_inr, CharTwo.neg_eq]
  ext a b
  rw [transpose_swapMat, mul_swapMat_apply, swapMat_mul_apply, gram_apply, gram_apply, hsgn,
    hsgn]
  have : (swapCoord S b = par (swapCoord S a)) ↔ (b = par a) := by
    constructor
    · intro h
      rw [← swapCoord_swapCoord S b, h, ← swapCoord_par, swapCoord_swapCoord]
    · intro h
      rw [h, swapCoord_par]
  simp only [this]

@[expose] noncomputable def swapSp [CharP K 2] (S : Finset (Fin n)) : StatedSp n K :=
  ofSymplecticMat (swapMat (K := K) S) (swapMat_symplectic S)

theorem mat_swapSp [CharP K 2] (S : Finset (Fin n)) :
    mat n K (swapSp (K := K) S) = swapMat S :=
  rfl

theorem mat_swapSp_inv [CharP K 2] (S : Finset (Fin n)) :
    mat n K (swapSp (K := K) S)⁻¹ = swapMat S := by
  have h1 : mat n K (swapSp (K := K) S)⁻¹ * mat n K (swapSp S) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc mat n K (swapSp (K := K) S)⁻¹ =
      mat n K (swapSp (K := K) S)⁻¹ * (swapMat S * swapMat S) := by
        rw [swapMat_mul_swapMat, Matrix.mul_one]
    _ = (mat n K (swapSp (K := K) S)⁻¹ * mat n K (swapSp S)) * swapMat S := by
        rw [mat_swapSp, Matrix.mul_assoc]
    _ = swapMat S := by rw [h1, Matrix.one_mul]

@[expose] def flipU (S : Finset (Fin n)) (t : Fin n → Kˣ) : Fin n → Kˣ :=
  fun k => if k ∈ S then (t k)⁻¹ else t k

theorem flipU_flipU (S : Finset (Fin n)) (t : Fin n → Kˣ) : flipU S (flipU S t) = t := by
  funext k
  by_cases hk : k ∈ S <;> simp [flipU, hk]

theorem diagSpEntry_flipU (S : Finset (Fin n)) (t : Fin n → Kˣ) (a : Fin n ⊕ Fin n) :
    diagSpEntry (flipU S t) a = diagSpEntry t (swapCoord S a) := by
  rcases a with i | i <;> by_cases hi : i ∈ S <;> simp [flipU, swapCoord, hi]

theorem swapSp_conj_diagSp [CharP K 2] (S : Finset (Fin n)) (t : Fin n → Kˣ) :
    swapSp S * diagSp K n t * (swapSp S)⁻¹ = diagSp K n (flipU S t) := by
  apply mat_injective
  rw [map_mul, map_mul, mat_swapSp, mat_swapSp_inv, mat_diagSp, mat_diagSp]
  ext a b
  rw [mul_swapMat_apply, swapMat_mul_apply, diagonal_apply, diagonal_apply,
    diagSpEntry_flipU]
  by_cases h : a = b
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right (fun h' => h (by rw [← swapCoord_swapCoord S a, h', swapCoord_swapCoord])),
      ite_eq_right h]

theorem eq_one_of_mul_self_eq_one [CharP K 2] {u : Kˣ} (h : u * u = 1) : u = 1 := by
  have h' : ((u : K) + 1) * ((u : K) + 1) = 0 := by
    rw [CharTwo.add_mul_self, ← Units.val_mul, h, Units.val_one, one_mul,
      CharTwo.add_self_eq_zero]
  have h0 : (u : K) + 1 = 0 := mul_self_eq_zero.mp h'
  apply Units.ext
  rw [Units.val_one, ← CharTwo.neg_eq (1 : K)]
  exact eq_neg_of_add_eq_zero_left h0

@[expose] def Aligned (t : Fin n → Kˣ) : Prop := ∀ i j, t i * t j = 1 → t i = 1

theorem exists_aligned [Finite K] [CharP K 2] (t : Fin n → Kˣ) :
    ∃ S : Finset (Fin n), Aligned (flipU S t) := by
  classical
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin Kˣ
  let code : Kˣ → ℕ := fun u => (e u : ℕ)
  have hcode : Function.Injective code := fun u v h => e.injective (Fin.ext h)
  refine ⟨Finset.univ.filter fun k => code (t k)⁻¹ < code (t k), ?_⟩
  set S := Finset.univ.filter fun k => code (t k)⁻¹ < code (t k) with hS
  have hle : ∀ k, code (flipU S t k) ≤ code (flipU S t k)⁻¹ := by
    intro k
    by_cases hk : k ∈ S
    · have hk' := (Finset.mem_filter.mp hk).2
      simp only [flipU, hk, ↓reduceIte, inv_inv]
      exact hk'.le
    · have hk' : ¬ code (t k)⁻¹ < code (t k) := fun h => hk (Finset.mem_filter.mpr ⟨by simp, h⟩)
      simp only [flipU, hk, ↓reduceIte]
      omega
  intro i j hij
  have hj : flipU S t j = (flipU S t i)⁻¹ := eq_inv_of_mul_eq_one_right hij
  have h1 := hle i
  have h2 := hle j
  rw [hj, inv_inv] at h2
  have heq : flipU S t i = (flipU S t i)⁻¹ := hcode (by omega)
  exact eq_one_of_mul_self_eq_one (by
    calc flipU S t i * flipU S t i = flipU S t i * (flipU S t i)⁻¹ := by rw [← heq]
      _ = 1 := mul_inv_cancel _)

@[expose] def oneSet (t : Fin n → Kˣ) : Set (Fin n ⊕ Fin n) := {a | diagSpEntry t a = 1}

theorem mem_oneSet_inl {t : Fin n → Kˣ} {i : Fin n} : Sum.inl i ∈ oneSet t ↔ t i = 1 := by
  simp [oneSet, diagSpEntry_inl, Units.val_eq_one]

theorem mem_oneSet_inr {t : Fin n → Kˣ} {i : Fin n} : Sum.inr i ∈ oneSet t ↔ t i = 1 := by
  simp [oneSet, diagSpEntry_inr, Units.val_eq_one]

theorem parClosed_oneSet (t : Fin n → Kˣ) : ParClosed (oneSet t) := by
  intro a ha
  rcases a with i | i
  · exact mem_oneSet_inr.mpr (mem_oneSet_inl.mp ha)
  · exact mem_oneSet_inl.mpr (mem_oneSet_inr.mp ha)

@[expose] def oneBlock (t : Fin n → Kˣ) : Subgroup (StatedSp n K) := suppGroup (oneSet t)

theorem commute_diagSp_of_mem_oneBlock {t : Fin n → Kˣ} {g : StatedSp n K}
    (hg : g ∈ oneBlock t) : Commute g (diagSp K n t) :=
  commute_diagSp_of_mem_suppGroup (fun a ha b hb => by rw [ha, hb]) hg

theorem conj_mem_oneBlock {t : Fin n → Kˣ} {c g : StatedSp n K} (hc : Commute c (diagSp K n t))
    (hg : g ∈ oneBlock t) : c * g * c⁻¹ ∈ oneBlock t := by
  have hc' : Commute c⁻¹ (diagSp K n t) := hc.inv_left
  have hz := (commute_diagSp_iff c t).1 hc
  have hz' := (commute_diagSp_iff c⁻¹ t).1 hc'
  have hcc : mat n K c * mat n K c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [oneBlock, mem_suppGroup_iff (parClosed_oneSet t)] at hg ⊢
  intro y hy r
  rw [map_mul, map_mul, Matrix.mul_apply, ← hcc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : diagSpEntry t v = diagSpEntry t y
  · have hvS : v ∉ oneSet t := fun h => hy (by
      change diagSpEntry t y = 1
      rw [← hv]
      exact h)
    rw [Matrix.mul_apply, Finset.sum_eq_single v]
    · rw [hg v hvS v, Matrix.one_apply_eq, mul_one]
    · intro u _ hu
      rw [hg v hvS u, Matrix.one_apply_ne hu, mul_zero]
    · simp
  · rw [hz' v y hv, mul_zero, mul_zero]

theorem coords_subset_oneSet {t : Fin n → Kˣ} {k : Fin n} (hk : t k = 1) :
    coords k ⊆ oneSet t := by
  intro a ha
  rcases mem_coords.1 ha with rfl | rfl
  · exact mem_oneSet_inl.mpr hk
  · exact mem_oneSet_inr.mpr hk

@[expose] noncomputable def oneIdx (t : Fin n → Kˣ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k => t k = 1

theorem mem_oneIdx {t : Fin n → Kˣ} {k : Fin n} : k ∈ oneIdx t ↔ t k = 1 := by
  classical
  simp [oneIdx]

@[expose] noncomputable def oneEnum (t : Fin n → Kˣ) : Fin (oneIdx t).card → Fin n :=
  fun k => ((oneIdx t).equivFin.symm k : Fin n)

theorem oneEnum_injective (t : Fin n → Kˣ) : Function.Injective (oneEnum t) :=
  Subtype.val_injective.comp (oneIdx t).equivFin.symm.injective

theorem oneSet_eq_range (t : Fin n → Kˣ) :
    oneSet t = Set.range (Sum.map (oneEnum t) (oneEnum t)) := by
  have hmem : ∀ i, (∃ k, oneEnum t k = i) ↔ t i = 1 := by
    intro i
    constructor
    · rintro ⟨k, rfl⟩
      exact mem_oneIdx.mp ((oneIdx t).equivFin.symm k).2
    · intro hi
      refine ⟨(oneIdx t).equivFin ⟨i, mem_oneIdx.mpr hi⟩, ?_⟩
      simp [oneEnum]
  ext a
  rcases a with i | i
  · rw [mem_oneSet_inl, ← hmem]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨Sum.inl k, by simp [hk]⟩
    · rintro ⟨b, hb⟩
      rcases b with k | k
      · exact ⟨k, by simpa using hb⟩
      · simp at hb
  · rw [mem_oneSet_inr, ← hmem]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨Sum.inr k, by simp [hk]⟩
    · rintro ⟨b, hb⟩
      rcases b with k | k
      · simp at hb
      · exact ⟨k, by simpa using hb⟩

theorem oneBlock_eq_range (t : Fin n → Kˣ) :
    oneBlock t = (spEmbed (K := K) (oneEnum t) (oneEnum_injective t)).range := by
  rw [range_spEmbed, oneBlock, oneSet_eq_range]

theorem isQuasisimple_oneBlock (h4 : 4 ≤ Nat.card K) {t : Fin n → Kˣ} {i₀ : Fin n}
    (hi₀ : t i₀ = 1) : CFSG.IsQuasisimple ↥(oneBlock (K := K) t) := by
  have hk : 1 ≤ (oneIdx t).card := Finset.card_pos.mpr ⟨i₀, mem_oneIdx.mpr hi₀⟩
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple _ K hk (Or.inl (Or.inr h4))
  rw [oneBlock_eq_range]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (spEmbed_injective (oneEnum_injective t))) hq

theorem mem_siegelLeviGL_of_entries {x : StatedSp n K}
    (hz : ∀ i j, mat n K x (Sum.inl i) (Sum.inr j) = 0 ∧ mat n K x (Sum.inr i) (Sum.inl j) = 0) :
    x ∈ siegelLeviGL K n := by
  set M := mat n K x with hM
  have h12 : M.toBlocks₁₂ = 0 := by
    ext i j
    exact (hz i j).1
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    exact (hz i j).2
  have hMb : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [h12, h21]
  have hsym := mat_transpose_mul_gram_mul x
  rw [← hM, hMb, ClassicalInvolution.Models.SymplecticPairs.gram, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply] at hsym
  have hAD : (M.toBlocks₁₁)ᵀ * M.toBlocks₂₂ = 1 := by
    have := congrArg Matrix.toBlocks₁₂ hsym
    simpa using this
  have hDA : (M.toBlocks₂₂)ᵀ * M.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.transpose hAD
    simpa [Matrix.transpose_mul] using this
  refine ⟨⟨M.toBlocks₁₁, (M.toBlocks₂₂)ᵀ, mul_eq_one_comm.1 hDA, hDA⟩, mat_injective ?_⟩
  rw [mat_leviEmbedGL, ← hM]
  conv_rhs => rw [hMb]
  congr 1

theorem mem_siegelLeviGL_of_aligned (h4 : 4 ≤ Nat.card K) {t : Fin n → Kˣ} (ht : Aligned t)
    {c : StatedSp n K} (hc : Commute c (diagSp K n t))
    (hcN : ∀ g ∈ oneBlock t, Commute c g) : c ∈ siegelLeviGL K n := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le h4
  have hκ1 : κ ≠ 1 := units_ne_one_of_mul_self_ne_one hκ
  have hκi : (κ : K) ≠ ((κ⁻¹ : Kˣ) : K) := fun e => hκ (by
    have e' : κ = κ⁻¹ := Units.ext e
    calc κ * κ = κ * κ⁻¹ := by rw [← e']
      _ = 1 := mul_inv_cancel κ)
  have hκi1 : (1 : K) ≠ ((κ⁻¹ : Kˣ) : K) := fun e => hκ1 (by
    have e' : (1 : Kˣ) = κ⁻¹ := Units.ext (by rw [Units.val_one]; exact e)
    rw [← inv_inv κ, ← e', inv_one])
  have hz := (commute_diagSp_iff c t).1 hc
  have hroot : ∀ j, t j = 1 → ∀ a b, diagSpEntry (Pi.mulSingle j κ) a ≠
      diagSpEntry (Pi.mulSingle j κ) b → mat n K c a b = 0 := fun j hj =>
    (commute_diagSp_iff c (Pi.mulSingle j κ)).1
      (hcN _ (suppGroup_mono (coords_subset_oneSet hj) (isSupp_rootTorusHom j κ)))
  refine mem_siegelLeviGL_of_entries fun i j => ⟨?_, ?_⟩
  · by_cases h : diagSpEntry t (Sum.inl i) = diagSpEntry t (Sum.inr j)
    · have hij : t i * t j = 1 := by
        have h' : t i = (t j)⁻¹ := Units.ext h
        rw [h', inv_mul_cancel]
      have hi1 : t i = 1 := ht i j hij
      have hj1 : t j = 1 := by rw [hi1, one_mul] at hij; exact hij
      refine hroot j hj1 _ _ ?_
      rw [diagSpEntry_mulSingle_inr_self]
      by_cases hij' : i = j
      · subst hij'
        rw [diagSpEntry_mulSingle_inl_self]
        exact hκi
      · rw [diagSpEntry_mulSingle_of_not_mem j κ (fun hm => hij' (by
          rcases mem_coords.1 hm with h1 | h1
          · exact Sum.inl_injective h1
          · exact absurd h1 Sum.inl_ne_inr))]
        exact hκi1
    · exact hz _ _ h
  · by_cases h : diagSpEntry t (Sum.inr i) = diagSpEntry t (Sum.inl j)
    · have hji : t j * t i = 1 := by
        have h' : t j = (t i)⁻¹ := (Units.ext h).symm
        rw [h', inv_mul_cancel]
      have hj1 : t j = 1 := ht j i hji
      have hi1 : t i = 1 := by rw [hj1, one_mul] at hji; exact hji
      refine hroot i hi1 _ _ ?_
      rw [diagSpEntry_mulSingle_inr_self]
      by_cases hij' : j = i
      · subst hij'
        rw [diagSpEntry_mulSingle_inl_self]
        exact hκi.symm
      · rw [diagSpEntry_mulSingle_of_not_mem i κ (fun hm => hij' (by
          rcases mem_coords.1 hm with h1 | h1
          · exact Sum.inl_injective h1
          · exact absurd h1 Sum.inl_ne_inr))]
        exact hκi1.symm
    · exact hz _ _ h

end WitSp

end CFSG.StandardType

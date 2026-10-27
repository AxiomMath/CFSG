module

public import CFSG.Quasithin.Vol2.Ch9Sec3Sp4Gen
public import CFSG.RankThree.SubgroupLists.SymplecticRegulus

public section

namespace CFSG.Quasithin.H13.Ch9.Sp4B

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem tGL_inj {M N : Matrix (Fin 2) (Fin 2) K} (h : tGL M = tGL N) : M = N := by
  have := congrArg (fun g : GL V₄ K => (g : Matrix V₄ V₄ K).toBlocks₁₂) h
  simpa [coe_tGL] using this

theorem exists_eq_tGL_of_fix {x : GL V₄ K} (hxS : x ∈ StatedSp 2 K)
    (hx : ∀ v ∈ lagInl, (x : Matrix V₄ V₄ K) *ᵥ v = v) :
    ∃ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S ∧ x = tGL S := by
  classical
  set X := (x : Matrix V₄ V₄ K) with hX
  have hcol : ∀ j r, X r (Sum.inl j) = (Pi.single (Sum.inl j) 1 : V₄ → K) r := by
    intro j r
    rw [← mulVec_single_one_apply X (Sum.inl j) r, hX, hx _ (single_inl_mem_lagInl j)]
  have hcol' : ∀ i j, X (Sum.inr i) (Sum.inr j) = if i = j then 1 else 0 := by
    intro i j
    have h := spForm_mulVec hxS (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1)
    rw [hx _ (single_inl_mem_lagInl i), spForm_apply, spForm_apply] at h
    simp [Pi.single_apply] at h
    simpa [eq_comm] using h
  set S : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => X (Sum.inl i) (Sum.inr j) with hS
  have hXS : X = fromBlocks 1 S 0 1 := by
    ext r c
    rcases r with i | i <;> rcases c with j | j
    · rw [hcol j]; simp [Pi.single_apply, Matrix.one_apply]
    · simp [hS]
    · rw [hcol j]; simp
    · rw [hcol']; simp [Matrix.one_apply]
  refine ⟨S, ?_, Units.ext hXS⟩
  ext i j
  have h := spForm_mulVec hxS (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inr j) 1)
  rw [← hX, hXS] at h
  rw [eq_mkV (Pi.single (Sum.inr i) 1 : V₄ → K), eq_mkV (Pi.single (Sum.inr j) 1 : V₄ → K),
    fromBlocks_mulVec_mkV, fromBlocks_mulVec_mkV, spForm_mkV, spForm_mkV] at h
  simp [Pi.single_apply, dotProduct] at h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> linear_combination h

theorem entry_inr_inl_eq_zero {l : GL V₄ K}
    (hl : ∀ v ∈ lagInl, (l : Matrix V₄ V₄ K) *ᵥ v ∈ lagInl) (i j : Fin 2) :
    (l : Matrix V₄ V₄ K) (Sum.inr i) (Sum.inl j) = 0 := by
  have h := mem_lagInl.mp (hl _ (single_inl_mem_lagInl (K := K) j)) i
  rwa [mulVec_single_one_apply] at h

theorem transpose_mul_eq_one {l : GL V₄ K} (hlS : l ∈ StatedSp 2 K)
    (h21 : ∀ i j, (l : Matrix V₄ V₄ K) (Sum.inr i) (Sum.inl j) = 0) :
    ((l : Matrix V₄ V₄ K).toBlocks₁₁)ᵀ * (l : Matrix V₄ V₄ K).toBlocks₂₂ = 1 := by
  ext p q
  have h := spGram_entry hlS (Sum.inl p) (Sum.inr q)
  simp only [h21, zero_mul, sub_zero] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.of_apply]
  rw [h]
  simp [spGram, Matrix.one_apply]

theorem mul_tGL {l : GL V₄ K} (h21 : ∀ i j, (l : Matrix V₄ V₄ K) (Sum.inr i) (Sum.inl j) = 0)
    (had : ((l : Matrix V₄ V₄ K).toBlocks₁₁)ᵀ * (l : Matrix V₄ V₄ K).toBlocks₂₂ = 1)
    (S : Matrix (Fin 2) (Fin 2) K) :
    l * tGL S = tGL ((l : Matrix V₄ V₄ K).toBlocks₁₁ * S *
      ((l : Matrix V₄ V₄ K).toBlocks₁₁)ᵀ) * l := by
  apply Units.ext
  set L := (l : Matrix V₄ V₄ K) with hL
  have hb : L.toBlocks₂₁ = 0 := by
    ext i j
    exact h21 i j
  rw [Units.val_mul, Units.val_mul, coe_tGL, coe_tGL, ← hL, ← Matrix.fromBlocks_toBlocks L, hb,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_one,
    Matrix.mul_zero, add_zero, Matrix.zero_mul, Matrix.one_mul, zero_add]
  congr 1
  rw [Matrix.mul_assoc (L.toBlocks₁₁ * S), had, Matrix.mul_one, add_comm]

omit [Field K] in
theorem transpose_two (a b c d : K) : !![a, b; c, d]ᵀ = !![a, c; b, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [Field K] in
theorem of_eq1 {α : Type*} {P : α → Prop} {A B : α} (h : P A) (hAB : A = B) : P B :=
  hAB ▸ h

theorem sym_all [Fintype K] (hK : Fintype.card K = 4) (P : Matrix (Fin 2) (Fin 2) K → Prop)
    (hadd : ∀ S T, P S → P T → P (S + T)) (hneg : ∀ S, P S → P (-S))
    (hconj : ∀ S, P S → ∀ m : SL(2, K),
      P ((m : Matrix (Fin 2) (Fin 2) K) * S * (m : Matrix (Fin 2) (Fin 2) K)ᵀ))
    {S₀ : Matrix (Fin 2) (Fin 2) K} (hS₀ : P S₀) (hsym : S₀ᵀ = S₀)
    (hdiag : S₀ 0 0 ≠ 0 ∨ S₀ 1 1 ≠ 0) : ∀ x z y : K, P !![x, z; z, y] := by
  have := charP_two_of_card_four hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one_of_card_four hK
  let u : K → SL(2, K) := fun t => ⟨!![1, t; 0, 1], by simp [det_fin_two_of]⟩
  let d : SL(2, K) := ⟨!![μ, 0; 0, μ⁻¹], by simp [det_fin_two_of, hμ0]⟩
  let w : SL(2, K) := ⟨!![0, 1; 1, 0], by simp [det_fin_two_of]; linear_combination -h2⟩
  have hsub : ∀ S T, P S → P T → P (S + -T) := fun S T hS hT => hadd _ _ hS (hneg _ hT)
  have core : ∀ x₀ z₀ y₀ : K, y₀ ≠ 0 → P !![x₀, z₀; z₀, y₀] → ∀ x z y : K,
      P !![x, z; z, y] := by
    intro x₀ z₀ y₀ hy h₀
    have hT : ∀ t : K, P !![t ^ 2 * y₀, t * y₀; t * y₀, 0] := by
      intro t
      refine of_eq1 (hsub _ _ (hconj _ h₀ (u t)) h₀) ?_
      change !![1, t; 0, 1] * !![x₀, z₀; z₀, y₀] * !![1, t; 0, 1]ᵀ + -!![x₀, z₀; z₀, y₀] = _
      rw [transpose_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;>
        first | ring1 | linear_combination (t * z₀) * h2
    have hA : ∀ c : K, P !![0, c; c, 0] := by
      intro c
      have h1mu : (1 - μ) * y₀ ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hμ1)) hy
      set t := c / ((1 - μ) * y₀) with ht
      have htc : t * y₀ - μ * t * y₀ = c := by
        rw [ht]
        field_simp
      refine of_eq1 (hsub _ _ (hconj _ (hT t) d) (hT (μ * t))) ?_
      change !![μ, 0; 0, μ⁻¹] * !![t ^ 2 * y₀, t * y₀; t * y₀, 0] * !![μ, 0; 0, μ⁻¹]ᵀ +
        -!![(μ * t) ^ 2 * y₀, μ * t * y₀; μ * t * y₀, 0] = _
      rw [transpose_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
        first | ring1 | linear_combination htc
    have hE : ∀ a : K, P !![a, 0; 0, 0] := by
      intro a
      set t := (a / y₀) ^ 2 with ht
      have hta : t ^ 2 * y₀ = a := by
        have h4 : (a / y₀) ^ 4 = a / y₀ := by
          rw [← hK]
          exact FiniteField.pow_card (a / y₀)
        rw [ht, ← pow_mul, show 2 * 2 = 4 from rfl, h4]
        field_simp
      refine of_eq1 (hsub _ _ (hT t) (hA (t * y₀))) ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hta]
    have hF : ∀ a : K, P !![0, 0; 0, a] := by
      intro a
      refine of_eq1 (hconj _ (hE a) w) ?_
      change !![0, 1; 1, 0] * !![a, 0; 0, 0] * !![0, 1; 1, 0]ᵀ = _
      rw [transpose_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    intro x z y
    refine of_eq1 (hadd _ _ (hadd _ _ (hE x) (hA z)) (hF y)) ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hS₀' : S₀ = !![S₀ 0 0, S₀ 0 1; S₀ 0 1, S₀ 1 1] := by
    have h10 : S₀ 1 0 = S₀ 0 1 := by
      rw [← Matrix.transpose_apply S₀ 0 1, hsym]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10]
  rcases hdiag with h | h
  · by_cases h11 : S₀ 1 1 = 0
    · refine core (S₀ 1 1) (S₀ 0 1) (S₀ 0 0) h (of_eq1 (hconj _ hS₀ w) ?_)
      change !![0, 1; 1, 0] * S₀ * !![0, 1; 1, 0]ᵀ = _
      rw [hS₀', transpose_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · exact core _ _ _ h11 (hS₀' ▸ hS₀)
  · exact core _ _ _ h (hS₀' ▸ hS₀)

theorem mul_alt_mul_transpose [CharP K 2] (m : SL(2, K)) (c : K) :
    (m : Matrix (Fin 2) (Fin 2) K) * !![0, c; c, 0] * (m : Matrix (Fin 2) (Fin 2) K)ᵀ =
      !![0, c; c, 0] := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hdet := m.2
  rw [det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination ((m : Matrix (Fin 2) (Fin 2) K) 0 0 * (m : Matrix (Fin 2) (Fin 2) K) 0 1 *
      c) * h2
  · linear_combination c * hdet + ((m : Matrix (Fin 2) (Fin 2) K) 0 1 *
      (m : Matrix (Fin 2) (Fin 2) K) 1 0 * c) * h2
  · linear_combination c * hdet + ((m : Matrix (Fin 2) (Fin 2) K) 0 1 *
      (m : Matrix (Fin 2) (Fin 2) K) 1 0 * c) * h2
  · linear_combination ((m : Matrix (Fin 2) (Fin 2) K) 1 0 * (m : Matrix (Fin 2) (Fin 2) K) 1 1 *
      c) * h2

theorem commute_of_fix_lagInl [Fintype K] (hK : Fintype.card K = 4)
    {Lb Wb : Subgroup (GL V₄ K)} (hLS : Lb ≤ StatedSp 2 K) (hWS : Wb ≤ StatedSp 2 K)
    (hperf : ⁅Lb, Lb⁆ = Lb)
    (h60 : ∀ N : Subgroup (GL V₄ K), N ≤ Lb → Lb ≤ Subgroup.normalizer (N : Set (GL V₄ K)) →
      IsPGroup 2 N → 60 ≤ N.relIndex Lb)
    (hW16 : Nat.card Wb ≤ 16) (hLW : Lb ≤ Subgroup.normalizer (Wb : Set (GL V₄ K)))
    (hL : ∀ l ∈ Lb, ∀ v ∈ lagInl, (l : Matrix V₄ V₄ K) *ᵥ v ∈ lagInl)
    (hW : ∀ w ∈ Wb, ∀ v ∈ lagInl, (w : Matrix V₄ V₄ K) *ᵥ v = v) :
    ∀ w ∈ Wb, ∀ l ∈ Lb, w * l = l * w := by
  have := charP_two_of_card_four hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h21 : ∀ l : ↥Lb, ∀ i j, ((l : GL V₄ K) : Matrix V₄ V₄ K) (Sum.inr i) (Sum.inl j) = 0 :=
    fun l => entry_inr_inl_eq_zero (hL l l.2)
  have had : ∀ l : ↥Lb, (((l : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₁₁)ᵀ *
      ((l : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₂₂ = 1 :=
    fun l => transpose_mul_eq_one (hLS l.2) (h21 l)
  have hmul : ∀ l l' : ↥Lb, (((l * l' : ↥Lb) : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₁₁ =
      ((l : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₁₁ *
        ((l' : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₁₁ := by
    intro l l'
    ext i j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Subgroup.coe_mul, Units.val_mul,
      Matrix.mul_apply, Fintype.sum_sum_type, h21 l', mul_zero, Finset.sum_const_zero, add_zero]
  let blkMon : ↥Lb →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun l => ((l : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₁₁
      map_one' := by
        ext i j
        simp [Matrix.toBlocks₁₁, Matrix.one_apply]
      map_mul' := hmul }
  have hdet : ∀ l : ↥Lb, (blkMon l).det = 1 := by
    intro l
    have h := eq_one_of_perfect hperf ((Matrix.detMonoidHom.comp blkMon).toHomUnits) l
    have h' := congrArg (fun u : Kˣ => (u : K)) h
    simpa using h'
  let blk : ↥Lb →* SL(2, K) :=
    { toFun := fun l => ⟨blkMon l, hdet l⟩
      map_one' := Subtype.ext blkMon.map_one
      map_mul' := fun l l' => Subtype.ext (blkMon.map_mul l l') }
  have hblk : ∀ l : ↥Lb, ((blk l : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      ((l : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₁₁ := fun l => rfl
  have hker : IsPGroup 2 blk.ker := by
    rintro ⟨l, hl⟩
    refine ⟨1, ?_⟩
    have ha : ((l : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₁₁ = 1 := by
      rw [← hblk, MonoidHom.mem_ker.mp hl, Matrix.SpecialLinearGroup.coe_one]
    have hd : ((l : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₂₂ = 1 := by
      have := had l
      rwa [ha, Matrix.transpose_one, Matrix.one_mul] at this
    have hb : ((l : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₂₁ = 0 := by
      ext i j
      exact h21 l i j
    have hlt : (l : GL V₄ K) = tGL (((l : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₁₂) := by
      apply Units.ext
      rw [coe_tGL]
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks ((l : GL V₄ K) : Matrix V₄ V₄ K)]
      rw [ha, hb, hd]
    apply Subtype.ext
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [pow_two, hlt, tGL_add, ← two_smul K, h2, zero_smul, tGL_zero]
  have hsurj : Function.Surjective blk :=
    surjective_of_isPGroup_ker h60 blk hker (by rw [card_sl2_of_card_four hK])
  have hWt : ∀ w ∈ Wb, ∃ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S ∧ w = tGL S :=
    fun w hw => exists_eq_tGL_of_fix (hWS hw) (hW w hw)
  set P : Matrix (Fin 2) (Fin 2) K → Prop := fun S => tGL S ∈ Wb with hP
  have hadd : ∀ S T, P S → P T → P (S + T) := by
    intro S T hS hT
    have := Wb.mul_mem hS hT
    rwa [tGL_add] at this
  have hneg : ∀ S, P S → P (-S) := by
    intro S hS
    have := Wb.inv_mem hS
    rwa [tGL_inv] at this
  have hconj : ∀ S, P S → ∀ m : SL(2, K),
      P ((m : Matrix (Fin 2) (Fin 2) K) * S * (m : Matrix (Fin 2) (Fin 2) K)ᵀ) := by
    intro S hS m
    obtain ⟨l, rfl⟩ := hsurj m
    have hc := (Subgroup.mem_normalizer_iff.mp (hLW l.2) _).mp hS
    rw [mul_tGL (h21 l) (had l), mul_inv_cancel_right] at hc
    rw [hP]
    simp only [hblk]
    exact hc
  have hdiag : ∀ S, Sᵀ = S → P S → S 0 0 = 0 ∧ S 1 1 = 0 := by
    intro S hsym hS
    by_contra hne
    have hne' : S 0 0 ≠ 0 ∨ S 1 1 ≠ 0 := by tauto
    have hall := sym_all hK P hadd hneg hconj hS hsym hne'
    have hinj : Function.Injective (fun x : K × K × K => (⟨tGL !![x.1, x.2.1; x.2.1, x.2.2],
        hall x.1 x.2.1 x.2.2⟩ : ↥Wb)) := by
      rintro ⟨x, z, y⟩ ⟨x', z', y'⟩ he
      have h := tGL_inj (congrArg Subtype.val he)
      have e00 := congrFun (congrFun h 0) 0
      have e01 := congrFun (congrFun h 0) 1
      have e11 := congrFun (congrFun h 1) 1
      simp at e00 e01 e11
      simp [e00, e01, e11]
    have hc := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, hK] at hc
    omega
  intro w hw l hl
  obtain ⟨S, hsym, rfl⟩ := hWt w hw
  obtain ⟨h00, h11⟩ := hdiag S hsym hw
  have hS : S = !![0, S 0 1; S 0 1, 0] := by
    have h10 : S 1 0 = S 0 1 := by
      rw [← Matrix.transpose_apply S 0 1, hsym]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h10]
  have hc := mul_tGL (h21 ⟨l, hl⟩) (had ⟨l, hl⟩) S
  rw [← hblk ⟨l, hl⟩, hS, mul_alt_mul_transpose, ← hS] at hc
  exact hc.symm

end CFSG.Quasithin.H13.Ch9.Sp4B

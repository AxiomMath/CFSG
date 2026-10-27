module

public import CFSG.RankThree.SubgroupLists.SymplecticTransvections
public import CFSG.ClassicalGroups.Alternating.Transvections

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def spE : V₄ → K := Pi.single (Sum.inl 0) 1

theorem spForm_spE_left (y : V₄ → K) : spForm 2 K spE y = y (Sum.inr 0) := by
  simp [spForm_apply, spE, Pi.single_apply]

theorem spForm_spE_right (x : V₄ → K) : spForm 2 K x spE = - x (Sum.inr 0) := by
  simp [spForm_apply, spE, Pi.single_apply]

@[expose] def heisMat (α β γ : K) : Matrix V₄ V₄ K :=
  fromBlocks !![1, α; 0, 1] !![γ, β; β, 0] 0 !![1, 0; -α, 1]

theorem heisMat_mul (α β γ α' β' γ' : K) :
    heisMat α β γ * heisMat α' β' γ' =
      heisMat (α + α') (β + β') (γ + γ' + α * β' - α' * β) := by
  rw [heisMat, heisMat, heisMat, fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring

theorem heisMat_zero : heisMat (0 : K) 0 0 = 1 := by
  rw [heisMat, ← fromBlocks_one]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

@[expose] def heis (α β γ : K) : GL V₄ K where
  val := heisMat α β γ
  inv := heisMat (-α) (-β) (-γ)
  val_inv := by rw [heisMat_mul]; ring_nf; exact heisMat_zero
  inv_val := by rw [heisMat_mul]; ring_nf; exact heisMat_zero

theorem coe_heis (α β γ : K) :
    ((heis α β γ : GL V₄ K) : Matrix V₄ V₄ K) = heisMat α β γ :=
  rfl

theorem heis_mul (α β γ α' β' γ' : K) :
    heis α β γ * heis α' β' γ' = heis (α + α') (β + β') (γ + γ' + α * β' - α' * β) :=
  Units.ext (heisMat_mul α β γ α' β' γ')

theorem heis_inv (α β γ : K) : (heis α β γ)⁻¹ = heis (-α) (-β) (-γ) := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [heis_mul]
  apply Units.ext
  rw [coe_heis, Units.val_one]
  ring_nf
  exact heisMat_zero

theorem heis_mem_statedSp (α β γ : K) : heis α β γ ∈ StatedSp 2 K := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, coe_heis,
    heisMat, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem heis_mulVec (α β γ : K) (v : V₄ → K) :
    ((heis α β γ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v =
      v + (α * v (Sum.inl 1) + β * v (Sum.inr 1) + γ * v (Sum.inr 0)) • spE +
        (β * v (Sum.inr 0)) • Pi.single (Sum.inl 1) 1 -
          (α * v (Sum.inr 0)) • Pi.single (Sum.inr 1) 1 := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [coe_heis, heisMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      fromBlocks, spE] <;> ring

theorem heis_mulVec_of_mem (α β γ : K) {v : V₄ → K} (hv : v (Sum.inr 0) = 0) :
    ((heis α β γ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v =
      v + (α * v (Sum.inl 1) + β * v (Sum.inr 1)) • spE := by
  rw [heis_mulVec, hv]
  simp

theorem heis_mulVec_spE (α β γ : K) :
    ((heis α β γ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE = spE := by
  rw [heis_mulVec_of_mem _ _ _ (by simp [spE])]
  simp [spE]

theorem heis_zero_zero (γ : K) : heis 0 0 γ = spTrans spE (-γ) := by
  apply gl_ext_mulVec
  intro v
  rw [heis_mulVec, spTrans_mulVec, spForm_spE_right]
  simp only [zero_mul, zero_add, zero_smul, sub_zero, add_zero]
  congr 2
  ring

theorem heis_commutator (α β γ α' β' γ' : K) :
    heis α β γ * heis α' β' γ' * (heis α β γ)⁻¹ * (heis α' β' γ')⁻¹ =
      heis 0 0 (2 * (α * β' - α' * β)) := by
  rw [heis_inv, heis_inv, heis_mul, heis_mul, heis_mul]
  congr 1 <;> ring

theorem spGram_entry {g : GL V₄ K} (hg : g ∈ StatedSp 2 K) (i j : V₄) :
    ∑ m : Fin 2, ((g : Matrix V₄ V₄ K) (Sum.inl m) i * (g : Matrix V₄ V₄ K) (Sum.inr m) j -
      (g : Matrix V₄ V₄ K) (Sum.inr m) i * (g : Matrix V₄ V₄ K) (Sum.inl m) j) =
      spGram 2 K i j := by
  have h := congrFun (congrFun (transpose_mul_spGram_mul hg) i) j
  rw [← h]
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply, spGram,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply]
  simp [Fin.sum_univ_two]
  ring

theorem entry_eq_zero_of_mulVec_eq_smul {g : GL V₄ K} {l : K}
    (hl : (g : Matrix V₄ V₄ K) *ᵥ spE = l • spE) {i : V₄} (hi : i ≠ Sum.inl 0) :
    (g : Matrix V₄ V₄ K) i (Sum.inl 0) = 0 := by
  have h := congrFun hl i
  simp [Matrix.mulVec, dotProduct, spE, Pi.single_apply, hi] at h
  exact h

theorem entry_inl_zero_of_mulVec_eq_smul {g : GL V₄ K} {l : K}
    (hl : (g : Matrix V₄ V₄ K) *ᵥ spE = l • spE) :
    (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 0) = l := by
  have h := congrFun hl (Sum.inl 0)
  simp [Matrix.mulVec, dotProduct, spE, Pi.single_apply] at h
  exact h

theorem entry_inr_zero_eq_zero {g : GL V₄ K} (hg : g ∈ StatedSp 2 K) {l : K}
    (hl : (g : Matrix V₄ V₄ K) *ᵥ spE = l • spE) {j : V₄} (hj : j ≠ Sum.inr 0) :
    (g : Matrix V₄ V₄ K) (Sum.inr 0) j = 0 := by
  have hl0 : l ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v => ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) hl
    simp only [gl_inv_mulVec_mulVec, h0, zero_smul, mulVec_zero] at h1
    have := congrFun h1 (Sum.inl 0)
    simp [spE] at this
  have h := spGram_entry hg (Sum.inl 0) j
  have hcol : ∀ m : Fin 2, (g : Matrix V₄ V₄ K) (Sum.inr m) (Sum.inl 0) = 0 := fun m =>
    entry_eq_zero_of_mulVec_eq_smul hl (by simp)
  have hcol1 : (g : Matrix V₄ V₄ K) (Sum.inl 1) (Sum.inl 0) = 0 :=
    entry_eq_zero_of_mulVec_eq_smul hl (by decide)
  simp only [Fin.sum_univ_two] at h
  rw [entry_inl_zero_of_mulVec_eq_smul hl] at h
  simp only [hcol, hcol1, zero_mul, sub_zero, add_zero] at h
  have hJ : spGram 2 K (Sum.inl 0) j = 0 := by
    rcases j with j | j
    · simp [spGram]
    · have : j ≠ 0 := fun h => hj (by rw [h])
      simp [spGram, Ne.symm this]
  rw [hJ] at h
  exact (mul_eq_zero.mp h).resolve_left hl0

@[expose] def spBlock (g : Matrix V₄ V₄ K) : Matrix (Fin 2) (Fin 2) K :=
  !![g (Sum.inl 1) (Sum.inl 1), g (Sum.inl 1) (Sum.inr 1);
     g (Sum.inr 1) (Sum.inl 1), g (Sum.inr 1) (Sum.inr 1)]

theorem spBlock_mul {g h : GL V₄ K} (hh : h ∈ StatedSp 2 K) {l m : K}
    (hgl : (g : Matrix V₄ V₄ K) *ᵥ spE = l • spE)
    (hhm : (h : Matrix V₄ V₄ K) *ᵥ spE = m • spE) :
    spBlock ((g * h : GL V₄ K) : Matrix V₄ V₄ K) =
      spBlock (g : Matrix V₄ V₄ K) * spBlock (h : Matrix V₄ V₄ K) := by
  have hg1 : (g : Matrix V₄ V₄ K) (Sum.inl 1) (Sum.inl 0) = 0 :=
    entry_eq_zero_of_mulVec_eq_smul hgl (by decide)
  have hg2 : (g : Matrix V₄ V₄ K) (Sum.inr 1) (Sum.inl 0) = 0 :=
    entry_eq_zero_of_mulVec_eq_smul hgl (by simp)
  have hh1 : (h : Matrix V₄ V₄ K) (Sum.inr 0) (Sum.inl 1) = 0 :=
    entry_inr_zero_eq_zero hh hhm (by simp)
  have hh2 : (h : Matrix V₄ V₄ K) (Sum.inr 0) (Sum.inr 1) = 0 :=
    entry_inr_zero_eq_zero hh hhm (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spBlock, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      hg1, hg2, hh1, hh2]

theorem det_spBlock {g : GL V₄ K} (hg : g ∈ StatedSp 2 K) {l : K}
    (hl : (g : Matrix V₄ V₄ K) *ᵥ spE = l • spE) :
    (spBlock (g : Matrix V₄ V₄ K)).det = 1 := by
  have h := spGram_entry hg (Sum.inl 1) (Sum.inr 1)
  have h1 : (g : Matrix V₄ V₄ K) (Sum.inr 0) (Sum.inl 1) = 0 :=
    entry_inr_zero_eq_zero hg hl (by simp)
  have h2 : (g : Matrix V₄ V₄ K) (Sum.inr 0) (Sum.inr 1) = 0 :=
    entry_inr_zero_eq_zero hg hl (by decide)
  simp only [Fin.sum_univ_two, h1, h2, zero_mul, mul_zero, sub_zero] at h
  rw [spBlock, Matrix.det_fin_two_of]
  have hJ : spGram 2 K (Sum.inl 1) (Sum.inr 1) = 1 := by simp [spGram]
  rw [hJ] at h
  linear_combination h

theorem eq_heis_of_fix {g : GL V₄ K} (hg : g ∈ StatedSp 2 K)
    (he : (g : Matrix V₄ V₄ K) *ᵥ spE = spE) (hb : spBlock (g : Matrix V₄ V₄ K) = 1) :
    g = heis ((g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 1))
      ((g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 1))
      ((g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 0)) := by
  have he' : (g : Matrix V₄ V₄ K) *ᵥ spE = (1 : K) • spE := by rw [one_smul]; exact he
  have hb11 := congrFun (congrFun hb 0) 0
  have hb12 := congrFun (congrFun hb 0) 1
  have hb21 := congrFun (congrFun hb 1) 0
  have hb22 := congrFun (congrFun hb 1) 1
  simp [spBlock] at hb11 hb12 hb21 hb22
  have c00 := entry_inl_zero_of_mulVec_eq_smul he'
  have c10 : (g : Matrix V₄ V₄ K) (Sum.inl 1) (Sum.inl 0) = 0 :=
    entry_eq_zero_of_mulVec_eq_smul he' (by decide)
  have c20 : (g : Matrix V₄ V₄ K) (Sum.inr 0) (Sum.inl 0) = 0 :=
    entry_eq_zero_of_mulVec_eq_smul he' (by simp)
  have c30 : (g : Matrix V₄ V₄ K) (Sum.inr 1) (Sum.inl 0) = 0 :=
    entry_eq_zero_of_mulVec_eq_smul he' (by simp)
  have r1 : (g : Matrix V₄ V₄ K) (Sum.inr 0) (Sum.inl 1) = 0 :=
    entry_inr_zero_eq_zero hg he' (by simp)
  have r3 : (g : Matrix V₄ V₄ K) (Sum.inr 0) (Sum.inr 1) = 0 :=
    entry_inr_zero_eq_zero hg he' (by decide)
  have d22 := spGram_entry hg (Sum.inl 0) (Sum.inr 0)
  simp only [Fin.sum_univ_two, c00, c10, c20, c30, zero_mul, sub_zero] at d22
  have e1 := spGram_entry hg (Sum.inl 1) (Sum.inr 0)
  have e3 := spGram_entry hg (Sum.inr 1) (Sum.inr 0)
  simp only [Fin.sum_univ_two, hb11, hb21, r1, hb12, hb22, r3, zero_mul, sub_zero, one_mul,
    zero_sub] at e1 e3
  have hd : (g : Matrix V₄ V₄ K) (Sum.inr 0) (Sum.inr 0) = 1 := by simpa [spGram] using d22
  have he1 : (g : Matrix V₄ V₄ K) (Sum.inr 1) (Sum.inr 0) =
      -(g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 1) := by
    have := e1
    simp [spGram, hd] at this
    linear_combination this
  have he3 : (g : Matrix V₄ V₄ K) (Sum.inl 1) (Sum.inr 0) =
      (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 1) := by
    have := e3
    simp [spGram, hd] at this
    linear_combination -this
  apply Units.ext
  rw [coe_heis]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [heisMat, fromBlocks, c00, c10, c20, c30, r1, r3, hb11, hb12, hb21, hb22, hd, he1, he3]

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Alternating in
theorem exists_mem_statedSp_mulVec_eq {u v : V₄ → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ h ∈ StatedSp 2 K, (h : Matrix V₄ V₄ K) *ᵥ u = v := by
  obtain ⟨g, hg, hgu⟩ :=
    (alternating_transvection_vector_transitivity spForm_isAlt spForm_nondegenerate).2 u v hu hv
  rw [← alternating_transvection_generation spForm_isAlt spForm_nondegenerate] at hg
  refine ⟨(Matrix.GeneralLinearGroup.toLin (n := V₄) (R := K)).symm g, ?_, ?_⟩
  · rw [mem_statedSp_iff_toLin, MulEquiv.apply_symm_apply]
    exact hg
  · have := congrArg (fun f : V₄ → K => f) hgu
    rw [← this]
    conv_rhs => rw [← (Matrix.GeneralLinearGroup.toLin (n := V₄) (R := K)).apply_symm_apply g]
    rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]

@[expose] def IsHeisAt (z : V₄ → K) (g : GL V₄ K) : Prop :=
  g ∈ StatedSp 2 K ∧ (g : Matrix V₄ V₄ K) *ᵥ z = z ∧
    ∀ v, spForm 2 K z v = 0 → ∃ c : K, (g : Matrix V₄ V₄ K) *ᵥ v = v + c • z

theorem isHeisAt_heis (α β γ : K) : IsHeisAt spE (heis α β γ) := by
  refine ⟨heis_mem_statedSp α β γ, heis_mulVec_spE α β γ, fun v hv => ?_⟩
  rw [spForm_spE_left] at hv
  exact ⟨_, heis_mulVec_of_mem α β γ hv⟩

theorem exists_eq_heis_of_isHeisAt {g : GL V₄ K} (hg : IsHeisAt spE g) :
    ∃ α β γ : K, g = heis α β γ := by
  obtain ⟨hS, he, hv⟩ := hg
  have h1 := hv (Pi.single (Sum.inl 1) 1) (by rw [spForm_spE_left]; simp)
  have h3 := hv (Pi.single (Sum.inr 1) 1) (by rw [spForm_spE_left]; simp)
  obtain ⟨c₁, hc₁⟩ := h1
  obtain ⟨c₃, hc₃⟩ := h3
  have hb : spBlock (g : Matrix V₄ V₄ K) = 1 := by
    have a1 := congrFun hc₁ (Sum.inl 1)
    have a2 := congrFun hc₁ (Sum.inr 1)
    have a3 := congrFun hc₃ (Sum.inl 1)
    have a4 := congrFun hc₃ (Sum.inr 1)
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, spE] at a1 a2 a3 a4
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spBlock, a1, a2, a3, a4]
  exact ⟨_, _, _, eq_heis_of_fix hS he hb⟩

theorem IsHeisAt.conj {z : V₄ → K} {g h : GL V₄ K} (hg : IsHeisAt z g)
    (hh : h ∈ StatedSp 2 K) : IsHeisAt ((h : Matrix V₄ V₄ K) *ᵥ z) (h * g * h⁻¹) := by
  obtain ⟨hS, hz, hv⟩ := hg
  refine ⟨mul_mem (mul_mem hh hS) (inv_mem hh), ?_, fun v hv' => ?_⟩
  · rw [gl_mulVec_mul, gl_mulVec_mul, gl_inv_mulVec_mulVec, hz]
  · have hw : spForm 2 K z (((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) = 0 := by
      rw [← spForm_mulVec hh, gl_mulVec_inv_mulVec]
      exact hv'
    obtain ⟨c, hc⟩ := hv _ hw
    refine ⟨c, ?_⟩
    rw [gl_mulVec_mul, gl_mulVec_mul, hc, mulVec_add, mulVec_smul, gl_mulVec_inv_mulVec]

theorem exists_commutator_eq_spTrans {z : V₄ → K} (h2 : (2 : K) ≠ 0) (hz : z ≠ 0)
    {g g' : GL V₄ K} (hg : IsHeisAt z g) (hg' : IsHeisAt z g') (hgg' : g * g' ≠ g' * g) :
    ∃ c : K, c ≠ 0 ∧ g * g' * g⁻¹ * g'⁻¹ = spTrans z c := by
  obtain ⟨h, hh, hhz⟩ := exists_mem_statedSp_mulVec_eq hz
    (show (spE : V₄ → K) ≠ 0 from fun h0 => by simpa [spE] using congrFun h0 (Sum.inl 0))
  obtain ⟨α, β, γ, hgh⟩ := exists_eq_heis_of_isHeisAt (hhz ▸ hg.conj hh)
  obtain ⟨α', β', γ', hgh'⟩ := exists_eq_heis_of_isHeisAt (hhz ▸ hg'.conj hh)
  have hconj : h * (g * g' * g⁻¹ * g'⁻¹) * h⁻¹ =
      (h * g * h⁻¹) * (h * g' * h⁻¹) * (h * g * h⁻¹)⁻¹ * (h * g' * h⁻¹)⁻¹ := by group
  rw [hgh, hgh', heis_commutator, heis_zero_zero] at hconj
  set c := -(2 * (α * β' - α' * β)) with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hgg'
    have hω : α * β' - α' * β = 0 := by
      have : (2 : K) * (α * β' - α' * β) = 0 := by linear_combination -h0
      exact (mul_eq_zero.mp this).resolve_left h2
    have hcomm : (h * g * h⁻¹) * (h * g' * h⁻¹) = (h * g' * h⁻¹) * (h * g * h⁻¹) := by
      rw [hgh, hgh', heis_mul, heis_mul]
      congr 1
      · ring
      · ring
      · linear_combination 2 * hω
    have := congrArg (fun x => h⁻¹ * x * h) hcomm
    simpa [mul_assoc] using this
  refine ⟨c, hc0, ?_⟩
  have hback : h⁻¹ * (h * (g * g' * g⁻¹ * g'⁻¹) * h⁻¹) * h = h⁻¹ * spTrans spE c * h := by
    rw [hconj]
  have hz' : z = ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE := by
    rw [← hhz, gl_inv_mulVec_mulVec]
  have key := conj_spTrans (inv_mem hh) spE c
  rw [inv_inv, ← hz'] at key
  rw [← key, ← hback]
  group

end CFSG.RankThree.SubgroupLists

module

public import CFSG.RankThree.PartTwo.Sec21.Item233RootsL44
public import CFSG.RankThree.PartTwo.Sec21.Hering233iOrbit
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open Matrix hiding ext
open CFSG.RankThree.PartTwo.Sec21.TablesL44 CFSG.RankThree.PartTwo.KFacts.KS21.L44
  CFSG.RankThree.PartTwo.Sec21.Tables

@[expose] def vA : Fin 3 → ZMod 3 := ![0, 0, 1]

@[expose] def vB' : Fin 3 → ZMod 3 := ![1, 1, 2]

@[expose] def vC3 : Fin 3 → ZMod 3 := ![1, 1, 0]

@[expose] def vC4 : Fin 3 → ZMod 3 := ![2, 2, 2]

@[expose] def repV : Fin 4 → (Fin 3 → ZMod 3) := ![vA, vB', vC3, vC4]

theorem cover_vec : ∀ v : Fin 3 → ZMod 3, (∀ m : Fin 3, v ≠ (m : ℕ) • std 0) →
    ∃ i : Fin 4, ∃ m n : Fin 3, repV i = (m : ℕ) • std 0 + (n : ℕ) • v := by
  decide

theorem cover_M {h : M} (hh : h ∈ A0)
    (hnot : h ∉ Subgroup.zpowers (δ (Multiplicative.ofAdd (std 0)))) :
    ∃ (i : Fin 4) (m n : ℕ), δ (Multiplicative.ofAdd (repV i)) =
      δ (Multiplicative.ofAdd (std 0)) ^ m * h ^ n := by
  obtain ⟨y, rfl⟩ := hh
  have hv : ∀ m : Fin 3, Multiplicative.toAdd y ≠ (m : ℕ) • std 0 := by
    intro m hm
    apply hnot
    have : δ y = δ (Multiplicative.ofAdd (std 0)) ^ (m : ℕ) := by
      rw [← map_pow, ← ofAdd_nsmul, ← hm]
      rfl
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  obtain ⟨i, m, n, hmn⟩ := cover_vec _ hv
  refine ⟨i, m, n, ?_⟩
  rw [hmn, ofAdd_add, map_mul, ofAdd_nsmul, ofAdd_nsmul, map_pow, map_pow]
  rfl

theorem ext_neg : ∀ v : Fin 3 → ZMod 3, ext (-v) = -ext v := by
  decide

theorem δ_inv (v : Fin 3 → ZMod 3) :
    (δ (Multiplicative.ofAdd v))⁻¹ = δ (Multiplicative.ofAdd (-v)) := by
  rw [← map_inv]
  rfl

theorem eq_one_of_sq_F4 (c : F4) (h : c ^ 2 = 1) : c = 1 := by
  have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
  have h1 : (c + 1) ^ 2 = 0 := by linear_combination h + (1 + c) * h2
  have h3 : c + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
  linear_combination h3 - h2

theorem entry_zero_of_inv {v : Fin 3 → ZMod 3} {y : M}
    (hyb : y * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd (-v)) * y) {i j : Fin 4}
    (hij : ext v i + ext v j ≠ 0) : (y : Matrix (Fin 4) (Fin 4) F4) i j = 0 := by
  by_contra hne
  apply hij
  have h := congrArg (fun z : M => (z : Matrix (Fin 4) (Fin 4) F4)) hyb
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_δ] at h
  have h1 := congrFun₂ h i j
  rw [dg, dg, Matrix.mul_diagonal, Matrix.diagonal_mul, ext_neg] at h1
  rw [mul_comm] at h1
  have h2 := eω_injective (mul_right_cancel₀ hne h1)
  simp only [Pi.neg_apply] at h2
  rw [h2]
  exact add_neg_cancel _

@[expose] noncomputable def Qmat (p : F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![0, p, 0, 0; p⁻¹, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem inv_eq_Qmat {F : Set (Fin 4)} (hF : 2 ∉ F ∨ 3 ∉ F) {y : M} (hyF : y ∈ blockSub F)
    (h2 : y * y = 1) (hb : y * δ (Multiplicative.ofAdd (std 0)) =
      δ (Multiplicative.ofAdd (-std 0)) * y) :
    (y : Matrix (Fin 4) (Fin 4) F4) = Qmat ((y : Matrix (Fin 4) (Fin 4) F4) 0 1) := by
  have hz : ∀ i j : Fin 4, ext (std 0) i + ext (std 0) j ≠ 0 →
      (y : Matrix (Fin 4) (Fin 4) F4) i j = 0 := fun i j h => entry_zero_of_inv hb h
  have h00 := hz 0 0 (by decide)
  have h11 := hz 1 1 (by decide)
  have h02 := hz 0 2 (by decide)
  have h03 := hz 0 3 (by decide)
  have h12 := hz 1 2 (by decide)
  have h13 := hz 1 3 (by decide)
  have h20 := hz 2 0 (by decide)
  have h21 := hz 2 1 (by decide)
  have h30 := hz 3 0 (by decide)
  have h31 := hz 3 1 (by decide)
  have hyy : (y : Matrix (Fin 4) (Fin 4) F4) * (y : Matrix (Fin 4) (Fin 4) F4) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, h2, Matrix.SpecialLinearGroup.coe_one]
  have e00 := congrFun₂ hyy 0 0
  have e22 := congrFun₂ hyy 2 2
  have e33 := congrFun₂ hyy 3 3
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply_eq] at e00 e22 e33
  rw [h00, h02, h03] at e00
  have h23 : (y : Matrix (Fin 4) (Fin 4) F4) 2 3 = 0 := by
    rcases hF with h | h
    · rw [mem_blockSub] at hyF
      rw [hyF 2 3 (Or.inl h)]
      exact Matrix.one_apply_ne (by decide)
    · rw [mem_blockSub] at hyF
      rw [hyF 2 3 (Or.inr h)]
      exact Matrix.one_apply_ne (by decide)
  have h32 : (y : Matrix (Fin 4) (Fin 4) F4) 3 2 = 0 := by
    rcases hF with h | h
    · rw [mem_blockSub] at hyF
      rw [hyF 3 2 (Or.inr h)]
      exact Matrix.one_apply_ne (by decide)
    · rw [mem_blockSub] at hyF
      rw [hyF 3 2 (Or.inl h)]
      exact Matrix.one_apply_ne (by decide)
  rw [h20, h21, h23, h32] at e22
  rw [h30, h31, h32, h23] at e33
  have h22 : (y : Matrix (Fin 4) (Fin 4) F4) 2 2 = 1 := by
    apply eq_one_of_sq_F4
    simp only [zero_mul, add_zero, zero_add] at e22
    rw [sq]
    exact e22
  have h33 : (y : Matrix (Fin 4) (Fin 4) F4) 3 3 = 1 := by
    apply eq_one_of_sq_F4
    simp only [zero_mul, add_zero, zero_add, mul_zero] at e33
    rw [sq]
    exact e33
  have h10 : (y : Matrix (Fin 4) (Fin 4) F4) 1 0 = ((y : Matrix (Fin 4) (Fin 4) F4) 0 1)⁻¹ := by
    simp only [zero_mul, add_zero, zero_add, mul_zero] at e00
    exact eq_inv_of_mul_eq_one_right e00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qmat, h00, h11, h02, h03, h12, h13, h20, h21, h30, h31,
    h22, h33, h23, h32, h10]

theorem count_inv {F : Set (Fin 4)} (hF : 2 ∉ F ∨ 3 ∉ F) :
    (invSet (blockSub F) (δ (Multiplicative.ofAdd (std 0)))).ncard ≤ 4 := by
  have key : ∀ y ∈ invSet (blockSub F) (δ (Multiplicative.ofAdd (std 0))),
      (y : Matrix (Fin 4) (Fin 4) F4) = Qmat ((y : Matrix (Fin 4) (Fin 4) F4) 0 1) := by
    rintro y ⟨hyF, h2, hb⟩
    rw [δ_inv] at hb
    exact inv_eq_Qmat hF hyF h2 (mul_inv_eq_iff_eq_mul.mp hb)
  have h := Set.ncard_le_ncard_of_injOn (s := invSet (blockSub F)
    (δ (Multiplicative.ofAdd (std 0)))) (t := (Set.univ : Set F4))
    (fun y : M => (y : Matrix (Fin 4) (Fin 4) F4) 0 1) (fun _ _ => Set.mem_univ _)
    (fun y₁ hy₁ y₂ hy₂ h12 => by
      apply Subtype.ext
      rw [key y₁ hy₁, key y₂ hy₂]
      exact congrArg Qmat h12) Set.finite_univ
  rw [Set.ncard_univ, card_F4] at h
  exact h

noncomputable abbrev LM (v : Fin 3 → ZMod 3) : Subgroup M :=
  layerCent (⊤ : Subgroup M) (Subgroup.zpowers (δ (Multiplicative.ofAdd v)))

theorem block_le_LM {v : Fin 3 → ZMod 3} (hv : v ≠ 0) {κ : ZMod 3}
    (hbig : ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ) :
    blockSub {i : Fin 4 | ext v i = κ} ≤ LM v :=
  block_le_layer (fun x => mem_blockSub) (isQuasisimple_blockSub_fibre hv hbig)

theorem LM_le_block {v : Fin 3 → ZMod 3} (hv : v ≠ 0) {κ₀ : ZMod 3}
    (hκ : ∀ κ : ZMod 3, (∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ) → κ = κ₀) :
    LM v ≤ blockSub {i : Fin 4 | ext v i = κ₀} := by
  change layerCent (⊤ : Subgroup M) (Subgroup.zpowers (δ (Multiplicative.ofAdd v))) ≤ _
  rw [layerCent_top_zpowers]
  change (CFSG.layer (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M))).map _ ≤ _
  rw [Subgroup.map_le_iff_le_comap, CFSG.layer.eq_sSup]
  refine sSup_le fun K hK => ?_
  have hmem : K ∈ {Z : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)) |
      CFSG.IsComponent Z} := hK
  rw [components_big hv] at hmem
  obtain ⟨κ, rfl⟩ := hmem
  show (blockSub {i : Fin 4 | ext v i = κ.1}).subgroupOf _ ≤ _
  rw [hκ κ.1 κ.2]
  exact le_rfl

theorem LM_le_cent (v : Fin 3 → ZMod 3) :
    LM v ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M) :=
  layerCent_le_centralizer_δ v

theorem cent_le_normalizer_block (v : Fin 3 → ZMod 3) (κ : ZMod 3) :
    Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M) ≤
      Subgroup.normalizer (blockSub {i : Fin 4 | ext v i = κ} : Set M) :=
  (block_normal (v := v) (κ := κ) (S := blockSub {i : Fin 4 | ext v i = κ})
    (fun x => mem_blockSub)).2

@[expose] noncomputable def wM : M := permSL (Equiv.swap 0 1)

theorem wM_mul_self : wM * wM = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wM, permSL, permMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply,
      Equiv.swap_apply_def]

theorem wM_ne_one : wM ≠ 1 := by
  intro h
  have := congrFun₂ (congrArg (fun z : M => (z : Matrix (Fin 4) (Fin 4) F4)) h) 0 0
  simp [wM, permSL, permMat, Matrix.one_apply, Equiv.swap_apply_def] at this

theorem wM_mem_block : wM ∈ blockSub {i : Fin 4 | i = 0 ∨ i = 1} := by
  rw [mem_blockSub]
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [wM, permSL, permMat, Matrix.one_apply, Equiv.swap_apply_def]

theorem wM_conj : wM * δ (Multiplicative.ofAdd (std 0)) * wM⁻¹ =
    (δ (Multiplicative.ofAdd (std 0)))⁻¹ := by
  rw [wM, permSL_conj, reindexSL_δ, δ_inv]
  have h : res (ext (std 0) ∘ ⇑(Equiv.swap (0 : Fin 4) 1)) = -std 0 := by decide
  rw [h]

theorem δ_mem_block {c : Set (Fin 4)} {w : Fin 3 → ZMod 3} (hw : ∀ i, i ∉ c → ext w i = 0) :
    δ (Multiplicative.ofAdd w) ∈ blockSub c :=
  mem_blockSub.mpr (isIdOutside_δ hw)

theorem isSimpleGroup_block01 : IsSimpleGroup (blockSub {i : Fin 4 | i = 0 ∨ i = 1}) := by
  haveI := isSimpleGroup_SL2
  rw [blockSub_01_eq]
  exact (MonoidHom.ofInjective ι01_injective).symm.isSimpleGroup

theorem card_block01 : Nat.card (blockSub {i : Fin 4 | i = 0 ∨ i = 1}) = 60 := by
  rw [blockSub_01_eq, ← Nat.card_congr (MonoidHom.ofInjective ι01_injective).toEquiv]
  exact card_SL2

theorem block_comm {x y : M} (hx : x ∈ blockSub {i : Fin 4 | i = 2 ∨ i = 3})
    (hy : y ∈ blockSub {i : Fin 4 | i = 0 ∨ i = 1}) : x * y = y * x := by
  have hd : Disjoint {i : Fin 4 | i = 2 ∨ i = 3} {i : Fin 4 | i = 0 ∨ i = 1} :=
    Set.disjoint_left.mpr (by
      intro i hi hj
      fin_cases i <;> simp_all)
  have h := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp.commute
    (M := (x : Matrix (Fin 4) (Fin 4) F4)) (N := (y : Matrix (Fin 4) (Fin 4) F4))
    (mem_blockSub.mp hx) (mem_blockSub.mp hy) hd
  exact Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_mul] using h.eq)

@[expose] def UniqueSixty (v : Fin 3 → ZMod 3) : Prop :=
  ∃ Y : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)),
    CFSG.IsComponent Y ∧ (∀ Y', CFSG.IsComponent Y' → Y' = Y) ∧ Nat.card Y = 60

theorem isComponent_block {v : Fin 3 → ZMod 3} (hv : v ≠ 0) {κ : ZMod 3}
    (hbig : ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ) :
    CFSG.IsComponent ((blockSub {i : Fin 4 | ext v i = κ}).subgroupOf
      (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M))) := by
  have hmem : (blockSub {i : Fin 4 | ext v i = κ}).subgroupOf
      (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)) ∈
      {K : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)) |
        CFSG.IsComponent K} := by
    rw [components_big hv]
    exact ⟨⟨κ, hbig⟩, rfl⟩
  exact hmem

theorem not_uniqueSixty_of_two_blocks {v : Fin 3 → ZMod 3} (hv : v ≠ 0) {κ₁ κ₂ : ZMod 3}
    (h₁ : ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ₁ ∧ ext v j = κ₁)
    (h₂ : ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ₂ ∧ ext v j = κ₂)
    (hne : blockSub {i : Fin 4 | ext v i = κ₁} ≠ blockSub {i : Fin 4 | ext v i = κ₂}) :
    ¬ UniqueSixty v := by
  rintro ⟨Y, -, hY, -⟩
  have e1 := hY _ (isComponent_block hv h₁)
  have e2 := hY _ (isComponent_block hv h₂)
  apply hne
  have e := congrArg (Subgroup.map (Subgroup.centralizer
    ({δ (Multiplicative.ofAdd v)} : Set M)).subtype) (e1.trans e2.symm)
  rwa [Subgroup.map_subgroupOf_eq_of_le (block_normal (v := v) (κ := κ₁)
    (S := blockSub {i : Fin 4 | ext v i = κ₁}) (fun x => mem_blockSub)).1,
    Subgroup.map_subgroupOf_eq_of_le (block_normal (v := v) (κ := κ₂)
    (S := blockSub {i : Fin 4 | ext v i = κ₂}) (fun x => mem_blockSub)).1] at e

theorem not_uniqueSixty_of_large {v : Fin 3 → ZMod 3} (hv : v ≠ 0) {κ : ZMod 3}
    (hκ : ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ)
    (hsub : blockSub {i : Fin 4 | i = 0 ∨ i = 1} ≤ blockSub {i : Fin 4 | ext v i = κ})
    {z : M} (hz : z ∈ blockSub {i : Fin 4 | ext v i = κ})
    (hz' : z ∉ blockSub {i : Fin 4 | i = 0 ∨ i = 1}) : ¬ UniqueSixty v := by
  rintro ⟨Y, -, hY, h60⟩
  have e := hY _ (isComponent_block hv hκ)
  have hcard : Nat.card (blockSub {i : Fin 4 | ext v i = κ}) = 60 := by
    rw [← h60, ← e]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (block_normal (v := v) (κ := κ)
      (S := blockSub {i : Fin 4 | ext v i = κ}) (fun x => mem_blockSub)).1).toEquiv).symm
  have heq := Subgroup.eq_of_le_of_card_ge hsub (by rw [card_block01, hcard])
  exact hz' (heq ▸ hz)

theorem δ_not_mem_block01 {w : Fin 3 → ZMod 3} {k : Fin 4} (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hw : ext w k ≠ 0) : δ (Multiplicative.ofAdd w) ∉ blockSub {i : Fin 4 | i = 0 ∨ i = 1} := by
  intro h
  rw [mem_blockSub] at h
  have h1 := h k k (Or.inl (by simp [hk0, hk1]))
  rw [coe_δ, dg, diagonal_apply_eq, Matrix.one_apply_eq] at h1
  apply hw
  have : eω (ext w k) = eω 0 := by rw [h1, eω_zero]
  exact eω_injective this

theorem not_uniqueSixty_std1 : ¬ UniqueSixty (std 1) := by
  refine not_uniqueSixty_of_two_blocks (v := std 1) (κ₁ := 1) (κ₂ := 2) (by decide)
    ⟨0, 1, by decide, by decide, by decide⟩ ⟨2, 3, by decide, by decide, by decide⟩ ?_
  intro h
  have hz : δ (Multiplicative.ofAdd vA) ∈ blockSub {i : Fin 4 | ext (std 1) i = 2} :=
    δ_mem_block (by decide)
  rw [← h] at hz
  have hs : {i : Fin 4 | ext (std 1) i = 1} = {i : Fin 4 | i = 0 ∨ i = 1} := by
    ext i
    fin_cases i <;> decide
  rw [hs] at hz
  exact δ_not_mem_block01 (k := 2) (by decide) (by decide) (by decide) hz

theorem not_uniqueSixty_std2 : ¬ UniqueSixty (std 2) := by
  refine not_uniqueSixty_of_large (v := std 2) (κ := 1) (by decide)
    ⟨0, 1, by decide, by decide, by decide⟩ ?_ (z := δ (Multiplicative.ofAdd (std 2)))
    (δ_mem_block (by decide)) (δ_not_mem_block01 (k := 2) (by decide) (by decide) (by decide))
  exact blockSub_mono (by
    intro i hi
    rcases hi with rfl | rfl <;> decide)

theorem not_uniqueSixty_C3 : ¬ UniqueSixty vC3 := by
  refine not_uniqueSixty_of_large (v := vC3) (κ := 1) (by decide)
    ⟨0, 1, by decide, by decide, by decide⟩ ?_ (z := δ (Multiplicative.ofAdd vC3))
    (δ_mem_block (by decide)) (δ_not_mem_block01 (k := 3) (by decide) (by decide) (by decide))
  exact blockSub_mono (by
    intro i hi
    rcases hi with rfl | rfl <;> decide)

theorem not_uniqueSixty_C4 : ¬ UniqueSixty vC4 := by
  refine not_uniqueSixty_of_large (v := vC4) (κ := 2) (by decide)
    ⟨0, 1, by decide, by decide, by decide⟩ ?_ (z := δ (Multiplicative.ofAdd vC4))
    (δ_mem_block (by decide)) (δ_not_mem_block01 (k := 2) (by decide) (by decide) (by decide))
  exact blockSub_mono (by
    intro i hi
    rcases hi with rfl | rfl <;> decide)

end CFSG.RankThree.PartTwo.Sec21.Hering233i

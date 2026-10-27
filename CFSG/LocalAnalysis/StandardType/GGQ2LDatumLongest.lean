module

public import CFSG.LocalAnalysis.StandardType.GGQ2LabelCartan
public import CFSG.LocalAnalysis.StandardType.GGForkIndefLattice
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2LD_single_cast {p : ℕ} {N : Type} [DecidableEq N] (k i : N) :
    (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) =
      (Pi.single k (1 : ZMod p) : N → ZMod p) i := by
  rw [Pi.single_apply, Pi.single_apply]
  by_cases h : i = k
  · rw [if_pos h, if_pos h]; exact Int.cast_one
  · rw [if_neg h, if_neg h]; exact Int.cast_zero

private theorem ggQ2LD_single_smul_sum {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {N : Type} [Fintype N] [DecidableEq N] (k : N) (v : N → V) :
    ∑ i, ((Pi.single k (1 : ZMod p) : N → ZMod p) i) • v i = v k := by
  refine (Fintype.sum_eq_single k ?_).trans ?_
  · intro i hi
    rw [Pi.single_apply, if_neg hi, zero_smul]
  · rw [Pi.single_apply, if_pos rfl, one_smul]

private theorem ggQ2LD_neg_single_smul_sum {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {N : Type} [Fintype N] [DecidableEq N] (k : N) (v : N → V) :
    ∑ i, (((-Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) • v i = -v k := by
  have hcast : ∀ i, (((-Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) =
      -((Pi.single k (1 : ZMod p) : N → ZMod p) i) := by
    intro i
    rw [Pi.neg_apply, Int.cast_neg, ggQ2LD_single_cast]
  simp only [hcast, neg_smul]
  rw [Finset.sum_neg_distrib, ggQ2LD_single_smul_sum]

private theorem ggQ2LD_lin_comb {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) (j : M.Λ) (m : M.Λ → ℤ) :
    ggLin (p := p) M.model (M.simple j) (∑ i, ((m i : ℤ) : ZMod p) • M.coroot i)
      = ∑ i, ((ggSRefl M.cartan j m i : ℤ) : ZMod p) • M.coroot i := by
  set C : ZMod p := ∑ i, ((M.cartan j i : ℤ) : ZMod p) * ((m i : ℤ) : ZMod p) with hC
  have hα : M.root j (∑ i, ((m i : ℤ) : ZMod p) • M.coroot i) = C := by
    rw [hC, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul, M.pairing j i]
    exact mul_comm _ _
  have hstep : (∑ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : M.Λ → ZMod p) i)) •
      M.coroot i) = (∑ i, ((m i : ℤ) : ZMod p) • M.coroot i) - C • M.coroot j := by
    have h1 : ∀ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : M.Λ → ZMod p) i)) •
        M.coroot i
        = ((m i : ℤ) : ZMod p) • M.coroot i -
          (C * ((Pi.single j (1 : ZMod p) : M.Λ → ZMod p) i)) • M.coroot i :=
      fun i => sub_smul _ _ _
    simp only [h1]
    rw [Finset.sum_sub_distrib]
    congr 1
    calc ∑ i, (C * ((Pi.single j (1 : ZMod p) : M.Λ → ZMod p) i)) • M.coroot i
        = ∑ i, C • (((Pi.single j (1 : ZMod p) : M.Λ → ZMod p) i) • M.coroot i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [mul_smul]
      _ = C • ∑ i, ((Pi.single j (1 : ZMod p) : M.Λ → ZMod p) i) • M.coroot i :=
          (Finset.smul_sum).symm
      _ = C • M.coroot j := by rw [ggQ2LD_single_smul_sum]
  have hcoef : ∀ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : M.Λ → ZMod p) i))
      = ((ggSRefl M.cartan j m i : ℤ) : ZMod p) := by
    intro i
    have hgg : ggSRefl M.cartan j m i =
        m i - (∑ k, M.cartan j k * m k) * ((Pi.single j (1 : ℤ) : M.Λ → ℤ) i) := by
      simp [ggSRefl]
    have hsingle : (((Pi.single j (1 : ℤ) : M.Λ → ℤ) i : ℤ) : ZMod p) =
        (Pi.single j (1 : ZMod p) : M.Λ → ZMod p) i :=
      ggQ2LD_single_cast j i
    have hsum : ((∑ k, M.cartan j k * m k : ℤ) : ZMod p) = C := by
      rw [hC, Int.cast_sum]
      exact Finset.sum_congr rfl (fun k _ => Int.cast_mul (M.cartan j k) (m k))
    rw [hgg, Int.cast_sub, Int.cast_mul, hsingle, hsum]
  calc ggLin (p := p) M.model (M.simple j) (∑ i, ((m i : ℤ) : ZMod p) • M.coroot i)
      = (∑ i, ((m i : ℤ) : ZMod p) • M.coroot i) - C • M.coroot j := by
          rw [M.simple_apply j, hα]
    _ = ∑ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : M.Λ → ZMod p) i)) •
          M.coroot i := hstep.symm
    _ = ∑ i, ((ggSRefl M.cartan j m i : ℤ) : ZMod p) • M.coroot i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hcoef i]

theorem ggQ2LD_word_coroot {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) (ψ : List M.Λ) (k : M.Λ) :
    ggLin (p := p) M.model ((ψ.map M.simple).prod) (M.coroot k) =
      ∑ i, ((ggSWord M.cartan ψ (Pi.single k 1) i : ℤ) : ZMod p) • M.coroot i := by
  induction ψ with
  | nil =>
      show ggLin (p := p) M.model (1 : MulAut ↥Bs) (M.coroot k) =
        ∑ i, (((Pi.single k (1 : ℤ) : M.Λ → ℤ) i : ℤ) : ZMod p) • M.coroot i
      rw [map_one]
      rw [show (1 : M.V ≃ₗ[ZMod p] M.V) (M.coroot k) = M.coroot k from rfl]
      calc M.coroot k =
            ∑ i, ((Pi.single k (1 : ZMod p) : M.Λ → ZMod p) i) • M.coroot i :=
              (ggQ2LD_single_smul_sum k M.coroot).symm
        _ = ∑ i, (((Pi.single k (1 : ℤ) : M.Λ → ℤ) i : ℤ) : ZMod p) • M.coroot i := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [ggQ2LD_single_cast]
  | cons j ψ ih =>
      rw [List.map_cons, List.prod_cons, map_mul, LinearEquiv.mul_apply]
      rw [ih]
      rw [ggQ2LD_lin_comb M j]
      rfl

theorem ggSWord_reindex {N N' : Type} [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']
    (e : N ≃ N') {X : Matrix N' N' ℤ} {X₀ : Matrix N N ℤ} (hX : ∀ i j, X (e i) (e j) = X₀ i j)
    (ψ : List N) (m : N → ℤ) :
    ggSWord X (ψ.map e) (m ∘ e.symm) = ggSWord X₀ ψ m ∘ e.symm := by
  induction ψ with
  | nil => rfl
  | cons j ψ ih =>
      have hstep : ggSRefl X (e j) (ggSWord X₀ ψ m ∘ e.symm) =
          ggSRefl X₀ j (ggSWord X₀ ψ m) ∘ e.symm := by
        funext x
        have hsum : (∑ i' : N', X (e j) i' * ggSWord X₀ ψ m (e.symm i'))
            = ∑ i, X₀ j i * ggSWord X₀ ψ m i := by
          rw [← Equiv.sum_comp e.symm (fun i => X₀ j i * ggSWord X₀ ψ m i)]
          refine Finset.sum_congr rfl (fun i' _ => ?_)
          rw [← hX j (e.symm i'), e.apply_symm_apply]
        have hsingle : (Pi.single (e j) (1 : ℤ) : N' → ℤ) x =
            (Pi.single j (1 : ℤ) : N → ℤ) (e.symm x) := by
          rw [Pi.single_apply, Pi.single_apply]
          by_cases h : x = e j
          · rw [if_pos h, if_pos (e.symm_apply_eq.mpr h)]
          · rw [if_neg h, if_neg (fun h' => h (e.symm_apply_eq.mp h'))]
        simp only [ggSRefl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
        rw [hsum, hsingle]
      rw [List.map_cons]
      show ggSRefl X (e j) (ggSWord X (List.map e ψ) (m ∘ e.symm)) =
        ggSWord X₀ (j :: ψ) m ∘ e.symm
      rw [ih, hstep]
      rfl

theorem ggQ2LD_neg_of_word {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) {n : ℕ} {C₀ : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j) (ψ : List (Fin n))
    (hψ : ∀ k, ggSWord C₀ ψ (Pi.single k 1) = -Pi.single k 1) :
    ∃ φ ∈ ggAutomizer L Bs, ∀ i, ggLin (p := p) M.model φ (M.coroot i) = -M.coroot i := by
  refine ⟨((ψ.map e).map M.simple).prod, ?_, ?_⟩
  · rw [M.automizer_L]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
    exact Subgroup.subset_closure (Set.mem_range_self k)
  · intro i
    obtain ⟨k, hk⟩ : ∃ k : Fin n, e k = i := ⟨e.symm i, e.apply_symm_apply i⟩
    rw [← hk]
    rw [ggQ2LD_word_coroot M (ψ.map e) (e k)]
    have hsingle_comp : (Pi.single k (1 : ℤ) : Fin n → ℤ) ∘ e.symm =
        (Pi.single (e k) (1 : ℤ) : M.Λ → ℤ) := by
      funext i'
      simp only [Function.comp_apply, Pi.single_apply, e.symm_apply_eq]
    have hcoe : ggSWord M.cartan (ψ.map e) (Pi.single (e k) (1 : ℤ)) =
        ggSWord C₀ ψ (Pi.single k (1 : ℤ)) ∘ e.symm := by
      rw [← hsingle_comp]
      exact ggSWord_reindex e hC ψ (Pi.single k 1)
    have hcoe' : ggSWord M.cartan (ψ.map e) (Pi.single (e k) (1 : ℤ)) =
        -Pi.single (e k) (1 : ℤ) := by
      rw [hcoe, hψ k]
      funext i'
      simp only [Function.comp_apply, Pi.neg_apply]
      congr 1
      exact congrFun hsingle_comp i'
    rw [hcoe']
    exact ggQ2LD_neg_single_smul_sum (e k) M.coroot

private theorem ggQLD_models_of_reindex {n : ℕ} {Λ : Type} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (e : Fin n ≃ Λ) {C : Matrix Λ Λ ℤ}
    (h : C = Matrix.reindex e e C₀ ∨ C = (Matrix.reindex e e C₀).transpose) :
    (∀ i j, C (e i) (e j) = C₀ i j) ∨ (∀ i j, C (e i) (e j) = C₀ j i) := by
  rcases h with h | h
  · left
    intro i j
    simp only [h, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  · right
    intro i j
    simp only [h, Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply]

theorem ggQ2_label_cartan_F4 {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (htag : labL.tag = .F4) :
    ∃ e : Fin 4 ≃ M.Λ, (∀ i j, M.cartan (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, M.cartan (e i) (e j) = CartanMatrix.F₄ j i) := by
  simp only [GGQ2LabelWeyl, htag] at hW
  obtain ⟨e, hcox⟩ := hW
  refine ⟨e, ?_⟩
  have hC := M.isCartan
  rw [hcox] at hC
  rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.F₄) e
    (hC.eq_or_eq_transpose (ggIntCartan_F₄.reindex e)
      (ggAtMostOneMultipleEdge_F₄.reindex e)) with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem ggQ2LD_word_check_B4 :
    ∀ k : Fin 4,
      ggSWord (CartanMatrix.B 4) [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]
        (Pi.single k 1) = -Pi.single k 1 := by
  decide

private theorem ggQ2LD_word_check_C4 :
    ∀ k : Fin 4,
      ggSWord (CartanMatrix.C 4) [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]
        (Pi.single k 1) = -Pi.single k 1 := by
  decide

private theorem ggQ2LD_word_check_D4 :
    ∀ k : Fin 4,
      ggSWord (CartanMatrix.D 4) [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]
        (Pi.single k 1) = -Pi.single k 1 := by
  decide

private theorem ggQ2LD_word_check_F4 :
    ∀ k : Fin 4,
      ggSWord CartanMatrix.F₄
        [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]
        (Pi.single k 1) = -Pi.single k 1 := by
  decide

private theorem ggQ2LD_word_check_F4_transpose :
    ∀ k : Fin 4,
      ggSWord CartanMatrix.F₄.transpose
        [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]
        (Pi.single k 1) = -Pi.single k 1 := by
  decide

theorem ggQ2LD_negW_of_rankFour {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (h4 : Fintype.card M.Λ = 4) (hA : labL.tag ≠ .twA) :
    ∃ φ ∈ ggAutomizer L Bs, ∀ i, ggLin (p := 3) M.model φ (M.coroot i) = -M.coroot i := by
  have hcard := ggQ2LD_card_lie hW hlab
  rw [h4] at hcard
  rcases labL with ⟨tag, rank, n⟩
  unfold GGQ2TBLabel at hlab
  rcases hlab with ⟨htag, -⟩ | ⟨htag | htag, -⟩ | ⟨htag, -, -⟩ | ⟨htag, hodd, -⟩ |
    htag | htag | htag | htag
  · exact absurd htag hA
  ·
    have htag' : tag = .B := htag
    have hrank : rank = 4 := by simpa [GGQ2LieRank, htag'] using hcard.symm
    subst rank
    simp only [GGQ2LabelWeyl, htag'] at hW
    obtain ⟨e, hcox⟩ := hW
    have hC := M.isCartan
    rw [hcox] at hC
    rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.B 4) e
      (hC.eq_or_eq_transpose (ggIntCartan_B 4 |>.reindex e)
        (ggAtMostOneMultipleEdge_B 4 |>.reindex e)) with he | he
    · exact ggQ2LD_neg_of_word M e he _ ggQ2LD_word_check_B4
    · exact ggQ2LD_neg_of_word M e
        (fun i j => (he i j).trans (congrFun (congrFun (CartanMatrix.B_transpose 4) i) j))
        _ ggQ2LD_word_check_C4
  ·
    have htag' : tag = .C := htag
    have hrank : rank = 4 := by simpa [GGQ2LieRank, htag'] using hcard.symm
    subst rank
    simp only [GGQ2LabelWeyl, htag'] at hW
    obtain ⟨e, hcox⟩ := hW
    have hC := M.isCartan
    rw [hcox] at hC
    rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.B 4) e
      (hC.eq_or_eq_transpose (ggIntCartan_B 4 |>.reindex e)
        (ggAtMostOneMultipleEdge_B 4 |>.reindex e)) with he | he
    · exact ggQ2LD_neg_of_word M e he _ ggQ2LD_word_check_B4
    · exact ggQ2LD_neg_of_word M e
        (fun i j => (he i j).trans (congrFun (congrFun (CartanMatrix.B_transpose 4) i) j))
        _ ggQ2LD_word_check_C4
  ·
    have htag' : tag = .D := htag
    have hrank : rank = 4 := by simpa [GGQ2LieRank, htag'] using hcard.symm
    subst rank
    simp only [GGQ2LabelWeyl, htag'] at hW
    obtain ⟨e, hcox⟩ := hW
    have hC := M.isCartan
    rw [hcox] at hC
    rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.D 4) e
      (hC.eq_or_eq_transpose (ggIntCartan_D 4 |>.reindex e)
        (ggAtMostOneMultipleEdge_D 4 |>.reindex e)) with he | he
    · exact ggQ2LD_neg_of_word M e he _ ggQ2LD_word_check_D4
    · exact ggQ2LD_neg_of_word M e
        (fun i j => (he i j).trans (congrFun (congrFun (CartanMatrix.D_transpose 4) i) j))
        _ ggQ2LD_word_check_D4
  ·
    have htag' : tag = .twD := htag
    have hrank : rank = 4 := by simpa [GGQ2LieRank, htag'] using hcard.symm
    subst rank
    have hodd4 : Odd (4 : ℕ) := hodd
    obtain ⟨m, hm⟩ := hodd4
    omega
  ·
    rcases ggQ2_label_cartan_F4 M hW htag with ⟨e, he | he⟩
    · exact ggQ2LD_neg_of_word M e he _ ggQ2LD_word_check_F4
    · exact ggQ2LD_neg_of_word M e he _ ggQ2LD_word_check_F4_transpose
  ·
    have htag' : tag = .twE6 := htag
    simp only [GGQ2LieRank, htag'] at hcard
    omega
  ·
    have htag' : tag = .E7 := htag
    simp only [GGQ2LieRank, htag'] at hcard
    omega
  ·
    have htag' : tag = .E8 := htag
    simp only [GGQ2LieRank, htag'] at hcard
    omega

private theorem ggQ2LD_A4_kernel :
    ∀ κ : Fin 4 → ZMod 3,
      (∀ i : Fin 4, ∑ j : Fin 4, ((CartanMatrix.A 4 i j : ℤ) : ZMod 3) * κ j = 0) →
        κ = 0 := by
  decide

theorem ggQ2LD_cartanKer_A4 {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (htag : labL.tag = .twA) (h4 : labL.rank = 4) :
    ∀ κ : M.Λ → ZMod 3, (∀ i, ∑ j, (M.cartan i j : ZMod 3) * κ j = 0) → κ = 0 := by
  intro κ hκ
  rcases labL with ⟨tag, rank, n⟩
  have h4' : rank = 4 := h4
  have htag' : tag = .twA := htag
  subst rank
  simp only [GGQ2LabelWeyl, htag'] at hW
  obtain ⟨e, hcox⟩ := hW
  have hC := M.isCartan
  rw [hcox] at hC
  have he' : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 4 i j := by
    rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.A 4) e
      (hC.eq_or_eq_transpose (ggIntCartan_A 4 |>.reindex e)
        (ggAtMostOneMultipleEdge_A 4 |>.reindex e)) with he | he
    · exact he
    · intro i j
      exact (he i j).trans (congrFun (congrFun (CartanMatrix.A_transpose 4) i) j)
  have hκ' : ∀ i : Fin 4,
      ∑ j : Fin 4, ((CartanMatrix.A 4 i j : ℤ) : ZMod 3) * (κ ∘ e) j = 0 := by
    intro i
    have h := hκ (e i)
    rw [← Equiv.sum_comp e (fun j => (M.cartan (e i) j : ZMod 3) * κ j)] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Function.comp_apply, he' i j]
  have hzero : κ ∘ e = 0 := ggQ2LD_A4_kernel (κ ∘ e) hκ'
  funext i
  have h := congrFun hzero (e.symm i)
  simpa [Function.comp_apply] using h

private theorem ggQ2LD_shapeC_ker {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hC : M.ShapeC) :
    ∃ κ : M.Λ → ZMod 3, κ ≠ 0 ∧ ∀ i, ∑ j, (M.cartan i j : ZMod 3) * κ j = 0 := by
  have hdep : ¬ LinearIndependent (ZMod 3) M.coroot := by
    intro hLI
    have hco : Module.finrank (ZMod 3) M.coSpan = Fintype.card M.Λ := by
      rw [GGQ2LDatum.coSpan]
      exact finrank_span_eq_card hLI
    have h1 := hC.2.1
    omega
  obtain ⟨κ, hsum, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨κ, fun h0 => hi (congrFun h0 i), fun i => ?_⟩
  have h := congrArg (M.root i) hsum
  rw [map_zero] at h
  simp only [map_sum, map_smul, smul_eq_mul, M.pairing] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

private theorem ggQ2LD_ker_reindex {n : ℕ} {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (e : Fin n ≃ M.Λ) {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (he : ∀ i j, M.cartan (e i) (e j) = C₀ i j) {κ : M.Λ → ZMod 3}
    (hκ : ∀ i, ∑ j, (M.cartan i j : ZMod 3) * κ j = 0)
    (hk : ∀ κ' : Fin n → ZMod 3,
      (∀ i, ∑ j, ((C₀ i j : ℤ) : ZMod 3) * κ' j = 0) → κ' = 0) :
    κ = 0 := by
  have hκ' : ∀ i : Fin n,
      ∑ j : Fin n, ((C₀ i j : ℤ) : ZMod 3) * (κ ∘ e) j = 0 := by
    intro i
    have h := hκ (e i)
    rw [← Equiv.sum_comp e (fun j => (M.cartan (e i) j : ZMod 3) * κ j)] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Function.comp_apply, he i j]
  have hzero := hk (κ ∘ e) hκ'
  funext i
  have h := congrFun hzero (e.symm i)
  simpa [Function.comp_apply] using h

private theorem ggQ2LD_B4_kernel :
    ∀ κ : Fin 4 → ZMod 3,
      (∀ i : Fin 4, ∑ j : Fin 4, ((CartanMatrix.B 4 i j : ℤ) : ZMod 3) * κ j = 0) →
        κ = 0 := by
  decide

private theorem ggQ2LD_C4_kernel :
    ∀ κ : Fin 4 → ZMod 3,
      (∀ i : Fin 4, ∑ j : Fin 4, ((CartanMatrix.C 4 i j : ℤ) : ZMod 3) * κ j = 0) →
        κ = 0 := by
  decide

private theorem ggQ2LD_B5_kernel :
    ∀ κ : Fin 5 → ZMod 3,
      (∀ i : Fin 5, ∑ j : Fin 5, ((CartanMatrix.B 5 i j : ℤ) : ZMod 3) * κ j = 0) →
        κ = 0 := by
  decide +kernel

private theorem ggQ2LD_C5_kernel :
    ∀ κ : Fin 5 → ZMod 3,
      (∀ i : Fin 5, ∑ j : Fin 5, ((CartanMatrix.C 5 i j : ℤ) : ZMod 3) * κ j = 0) →
        κ = 0 := by
  decide +kernel

private theorem ggQ2LD_D4_kernel :
    ∀ κ : Fin 4 → ZMod 3,
      (∀ i : Fin 4, ∑ j : Fin 4, ((CartanMatrix.D 4 i j : ℤ) : ZMod 3) * κ j = 0) →
        κ = 0 := by
  decide

private theorem ggQ2LD_D5_kernel :
    ∀ κ : Fin 5 → ZMod 3,
      (∀ i : Fin 5, ∑ j : Fin 5, ((CartanMatrix.D 5 i j : ℤ) : ZMod 3) * κ j = 0) →
        κ = 0 := by
  decide +kernel

private theorem ggQ2LD_F4_kernel :
    ∀ κ : Fin 4 → ZMod 3,
      (∀ i : Fin 4, ∑ j : Fin 4, ((CartanMatrix.F₄ i j : ℤ) : ZMod 3) * κ j = 0) →
        κ = 0 := by
  decide

private theorem ggQ2LD_F4T_kernel :
    ∀ κ : Fin 4 → ZMod 3,
      (∀ i : Fin 4, ∑ j : Fin 4, ((CartanMatrix.F₄.transpose i j : ℤ) : ZMod 3) * κ j = 0) →
        κ = 0 := by
  decide

theorem ggQ2LD_shapeC_card {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (hC : M.ShapeC) :
    6 ≤ Fintype.card M.Λ ∨ (labL.tag = .twA ∧ labL.rank = 5) := by
  obtain ⟨κ, hκ0, hκ⟩ := ggQ2LD_shapeC_ker M hC
  have hcard := ggQ2LD_card_lie hW hlab
  by_cases h6 : 6 ≤ Fintype.card M.Λ
  · exact Or.inl h6
  right
  have hle : Fintype.card M.Λ ≤ 5 := by omega
  rcases labL with ⟨tag, rank, n⟩
  have hlab' : GGQ2TBLabel ⟨tag, rank, n⟩ := hlab
  unfold GGQ2TBLabel at hlab
  rcases hlab with ⟨htag, h4⟩ | ⟨htag | htag, h4⟩ | ⟨htag, heven, h4⟩ |
    ⟨htag, hodd, h4⟩ | htag | htag | htag | htag
  ·
    have htag' : tag = .twA := htag
    have hcard' : Fintype.card M.Λ = rank := by
      simpa [GGQ2LieRank, htag'] using hcard
    have h5 : rank ≤ 5 := by omega
    interval_cases rank
    · exfalso
      exact hκ0 (ggQ2LD_cartanKer_A4 M hW hlab' htag' rfl κ hκ)
    · exact ⟨htag', rfl⟩
  ·
    have htag' : tag = .B := htag
    have hcard' : Fintype.card M.Λ = rank := by
      simpa [GGQ2LieRank, htag'] using hcard
    have h5 : rank ≤ 5 := by omega
    interval_cases rank
    · simp only [GGQ2LabelWeyl, htag'] at hW
      obtain ⟨e, hcox⟩ := hW
      have hc := M.isCartan
      rw [hcox] at hc
      rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.B 4) e
        (hc.eq_or_eq_transpose (ggIntCartan_B 4 |>.reindex e)
          (ggAtMostOneMultipleEdge_B 4 |>.reindex e)) with he | he
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex M e he hκ ggQ2LD_B4_kernel)
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex (C₀ := CartanMatrix.C 4) M e
          (fun i j => (he i j).trans (congrFun (congrFun (CartanMatrix.B_transpose 4) i) j))
          hκ ggQ2LD_C4_kernel)
    · simp only [GGQ2LabelWeyl, htag'] at hW
      obtain ⟨e, hcox⟩ := hW
      have hc := M.isCartan
      rw [hcox] at hc
      rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.B 5) e
        (hc.eq_or_eq_transpose (ggIntCartan_B 5 |>.reindex e)
          (ggAtMostOneMultipleEdge_B 5 |>.reindex e)) with he | he
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex M e he hκ ggQ2LD_B5_kernel)
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex (C₀ := CartanMatrix.C 5) M e
          (fun i j => (he i j).trans (congrFun (congrFun (CartanMatrix.B_transpose 5) i) j))
          hκ ggQ2LD_C5_kernel)
  ·
    have htag' : tag = .C := htag
    have hcard' : Fintype.card M.Λ = rank := by
      simpa [GGQ2LieRank, htag'] using hcard
    have h5 : rank ≤ 5 := by omega
    interval_cases rank
    · simp only [GGQ2LabelWeyl, htag'] at hW
      obtain ⟨e, hcox⟩ := hW
      have hc := M.isCartan
      rw [hcox] at hc
      rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.B 4) e
        (hc.eq_or_eq_transpose (ggIntCartan_B 4 |>.reindex e)
          (ggAtMostOneMultipleEdge_B 4 |>.reindex e)) with he | he
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex M e he hκ ggQ2LD_B4_kernel)
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex (C₀ := CartanMatrix.C 4) M e
          (fun i j => (he i j).trans (congrFun (congrFun (CartanMatrix.B_transpose 4) i) j))
          hκ ggQ2LD_C4_kernel)
    · simp only [GGQ2LabelWeyl, htag'] at hW
      obtain ⟨e, hcox⟩ := hW
      have hc := M.isCartan
      rw [hcox] at hc
      rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.B 5) e
        (hc.eq_or_eq_transpose (ggIntCartan_B 5 |>.reindex e)
          (ggAtMostOneMultipleEdge_B 5 |>.reindex e)) with he | he
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex M e he hκ ggQ2LD_B5_kernel)
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex (C₀ := CartanMatrix.C 5) M e
          (fun i j => (he i j).trans (congrFun (congrFun (CartanMatrix.B_transpose 5) i) j))
          hκ ggQ2LD_C5_kernel)
  ·
    have htag' : tag = .D := htag
    have hcard' : Fintype.card M.Λ = rank := by
      simpa [GGQ2LieRank, htag'] using hcard
    have h5 : rank ≤ 5 := by omega
    obtain ⟨m, hm⟩ := heven
    interval_cases rank
    · simp only [GGQ2LabelWeyl, htag'] at hW
      obtain ⟨e, hcox⟩ := hW
      have hc := M.isCartan
      rw [hcox] at hc
      rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.D 4) e
        (hc.eq_or_eq_transpose (ggIntCartan_D 4 |>.reindex e)
          (ggAtMostOneMultipleEdge_D 4 |>.reindex e)) with he | he
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex M e he hκ ggQ2LD_D4_kernel)
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex (C₀ := CartanMatrix.D 4) M e
          (fun i j => (he i j).trans (congrFun (congrFun (CartanMatrix.D_transpose 4) i) j))
          hκ ggQ2LD_D4_kernel)
    · exfalso
      have hm' : (5 : ℕ) = m + m := hm
      omega
  ·
    have htag' : tag = .twD := htag
    have hcard' : Fintype.card M.Λ = rank := by
      simpa [GGQ2LieRank, htag'] using hcard
    have h5 : rank ≤ 5 := by omega
    obtain ⟨m, hm⟩ := hodd
    interval_cases rank
    · exfalso
      have hm' : (4 : ℕ) = 2 * m + 1 := hm
      omega
    · simp only [GGQ2LabelWeyl, htag'] at hW
      obtain ⟨e, hcox⟩ := hW
      have hc := M.isCartan
      rw [hcox] at hc
      rcases ggQLD_models_of_reindex (C₀ := CartanMatrix.D 5) e
        (hc.eq_or_eq_transpose (ggIntCartan_D 5 |>.reindex e)
          (ggAtMostOneMultipleEdge_D 5 |>.reindex e)) with he | he
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex M e he hκ ggQ2LD_D5_kernel)
      · exfalso
        exact hκ0 (ggQ2LD_ker_reindex (C₀ := CartanMatrix.D 5) M e
          (fun i j => (he i j).trans (congrFun (congrFun (CartanMatrix.D_transpose 5) i) j))
          hκ ggQ2LD_D5_kernel)
  ·
    have htag' : tag = .F4 := htag
    rcases ggQ2_label_cartan_F4 M hW htag' with ⟨e, he | he⟩
    · exfalso
      exact hκ0 (ggQ2LD_ker_reindex M e he hκ ggQ2LD_F4_kernel)
    · exfalso
      refine hκ0 (ggQ2LD_ker_reindex (C₀ := CartanMatrix.F₄.transpose) M e ?_ hκ
        ggQ2LD_F4T_kernel)
      intro i j
      rw [Matrix.transpose_apply]
      exact he i j
  ·
    have htag' : tag = .twE6 := htag
    have hcard' : Fintype.card M.Λ = 6 := by
      simpa [GGQ2LieRank, htag'] using hcard
    exfalso
    omega
  ·
    have htag' : tag = .E7 := htag
    have hcard' : Fintype.card M.Λ = 7 := by
      simpa [GGQ2LieRank, htag'] using hcard
    exfalso
    omega
  ·
    have htag' : tag = .E8 := htag
    have hcard' : Fintype.card M.Λ = 8 := by
      simpa [GGQ2LieRank, htag'] using hcard
    exfalso
    omega

end CFSG.StandardType

end

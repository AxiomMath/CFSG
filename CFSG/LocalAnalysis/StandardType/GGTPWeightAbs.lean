module

public import CFSG.LocalAnalysis.StandardType.GGTPWeightDefs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.Perm
public import CFSG.SignalizerFunctorTheorem.NonLocal.Weights
public import Mathlib

public section

open scoped BigOperators

namespace CFSG.StandardType

private def ggTP_pair (c : Fin 6 → ZMod 3) (x : Fin 6 → Multiplicative (ZMod 3)) : ZMod 3 :=
  ∑ i, c i * (x i).toAdd

private lemma ggTP_toAdd_prod {ι : Type*} (s : Finset ι) (f : ι → Multiplicative (ZMod 3)) :
    (s.prod f).toAdd = s.sum (fun i => (f i).toAdd) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, toAdd_mul, ih]

private lemma ggTP_pair_mul (c : Fin 6 → ZMod 3) (x y : Fin 6 → Multiplicative (ZMod 3)) :
    ggTP_pair c (x * y) = ggTP_pair c x + ggTP_pair c y := by
  simp only [ggTP_pair, Pi.mul_apply, toAdd_mul, mul_add, Finset.sum_add_distrib]

private def ggTP_charOf (c : Fin 6 → ZMod 3) :
    (Fin 6 → Multiplicative (ZMod 3)) →* Multiplicative (ZMod 3) where
  toFun x := Multiplicative.ofAdd (ggTP_pair c x)
  map_one' := by simp [ggTP_pair]
  map_mul' x y := by rw [ggTP_pair_mul, ofAdd_add]

private def ggTP_charS (c : Fin 6 → ZMod 3) : GGTPTorus →* Multiplicative (ZMod 3) :=
  (ggTP_charOf c).comp GGTPTorus.subtype

private lemma ggTP_sum_toAdd (x : GGTPTorus) : ∑ i, (x.1 i).toAdd = 0 := by
  have h := congrArg Multiplicative.toAdd x.2
  rw [ggTP_toAdd_prod] at h
  simpa using h

private lemma ggTP_pair_sub_const (c : Fin 6 → ZMod 3) (k : ZMod 3)
    (x : Fin 6 → Multiplicative (ZMod 3)) (hx : ∑ i, (x i).toAdd = 0) :
    ggTP_pair (fun i => c i - k) x = ggTP_pair c x := by
  simp only [ggTP_pair]
  calc
    (∑ i, (c i - k) * (x i).toAdd)
        = ∑ i, (c i * (x i).toAdd - k * (x i).toAdd) :=
          Finset.sum_congr rfl fun i _ => by ring
    _ = (∑ i, c i * (x i).toAdd) - ∑ i, k * (x i).toAdd :=
          Finset.sum_sub_distrib (f := fun i => c i * (x i).toAdd)
            (g := fun i => k * (x i).toAdd)
    _ = (∑ i, c i * (x i).toAdd) - k * ∑ i, (x i).toAdd := by
          rw [Finset.mul_sum (s := Finset.univ)]
    _ = (∑ i, c i * (x i).toAdd) - k * 0 := by rw [hx]
    _ = (∑ i, c i * (x i).toAdd) := by simp

private lemma ggTP_charS_perm (c : Fin 6 → ZMod 3) (σ : Equiv.Perm (Fin 6)) :
    (ggTP_charS c).comp (ggTPPermAct σ) =
      ggTP_charS (fun i => c (σ i)) := by
  ext x
  show ggTP_pair c (fun i => x.1 (σ⁻¹ i)) = ggTP_pair (fun i => c (σ i)) x.1
  simp only [ggTP_pair]
  rw [show (∑ i, c i * (x.1 (σ⁻¹ i)).toAdd) =
      ∑ i, (fun j => c (σ j) * (x.1 j).toAdd) (σ⁻¹ i) from by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp]
  rw [Equiv.sum_comp σ⁻¹ (fun j => c (σ j) * (x.1 j).toAdd)]

private lemma ggTP_charS_sub_const (c : Fin 6 → ZMod 3) (k : ZMod 3) :
    ggTP_charS (fun i => c i - k) = ggTP_charS c := by
  ext x
  show ggTP_pair (fun i => c i - k) x.1 = ggTP_pair c x.1
  exact ggTP_pair_sub_const c k x.1 (ggTP_sum_toAdd x)

private def ggTP_cnt (v : ZMod 3) (x : Fin 6 → ZMod 3) : ℕ :=
  (Finset.univ.filter (fun i => x i = v)).card

private def ggTP_Y (c : Fin 6 → ZMod 3) : Finset (Fin 6 → ZMod 3) :=
  Finset.univ.filter
    (fun y => y 0 = 0 ∧ ∃ k : ZMod 3, ∀ v : ZMod 3, ggTP_cnt v y = ggTP_cnt (v + k) c)

private def ggTP_shape (c : Fin 6 → ZMod 3) : ℕ × ℕ × ℕ :=
  (ggTP_cnt 0 c, ggTP_cnt 1 c, ggTP_cnt 2 c)

private def ggTP_v0 : Fin 6 → ZMod 3 := ![0, 0, 0, 1, 1, 1]
private def ggTP_v1 : Fin 6 → ZMod 3 := ![1, 1, 1, 2, 2, 2]
private def ggTP_v2 : Fin 6 → ZMod 3 := ![0, 0, 0, 2, 2, 2]
private def ggTP_v3 : Fin 6 → ZMod 3 := ![0, 0, 0, 0, 1, 2]
private def ggTP_v4 : Fin 6 → ZMod 3 := ![0, 1, 1, 1, 1, 2]
private def ggTP_v5 : Fin 6 → ZMod 3 := ![0, 1, 2, 2, 2, 2]
private def ggTP_v6 : Fin 6 → ZMod 3 := ![0, 0, 1, 1, 2, 2]

private def ggTP_reps : Finset (Fin 6 → ZMod 3) :=
  {ggTP_v0, ggTP_v1, ggTP_v2, ggTP_v3, ggTP_v4, ggTP_v5, ggTP_v6}

private lemma ggTP_shape_reps :
    ∀ (c : Fin 6 → ZMod 3), (∑ i, c i = 0) → (¬ ∃ k, ∀ i, c i = k) →
      ∃ v ∈ ggTP_reps, ggTP_shape v = ggTP_shape c := by
  decide +kernel

private lemma ggTP_Y_reps_ge : ∀ v ∈ ggTP_reps, 20 ≤ (ggTP_Y v).card := by
  decide +kernel

private lemma ggTP_Y_eq_of_shape {c v : Fin 6 → ZMod 3}
    (h : ∀ w : ZMod 3, ggTP_cnt w v = ggTP_cnt w c) : ggTP_Y v = ggTP_Y c := by
  refine Finset.filter_congr ?_
  intro y _
  have hiff : (∃ k : ZMod 3, ∀ w : ZMod 3, ggTP_cnt w y = ggTP_cnt (w + k) v) ↔
      (∃ k : ZMod 3, ∀ w : ZMod 3, ggTP_cnt w y = ggTP_cnt (w + k) c) := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, fun w => by rw [← h (w + k)]; exact hk w⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, fun w => by rw [h (w + k)]; exact hk w⟩
  simp only [hiff]

private lemma ggTP_Y_ge (c : Fin 6 → ZMod 3) (hsum : ∑ i, c i = 0)
    (hnc : ¬ ∃ k, ∀ i, c i = k) : 20 ≤ (ggTP_Y c).card := by
  obtain ⟨v, hv, hshape⟩ := ggTP_shape_reps c hsum hnc
  have hvc : ∀ w : ZMod 3, ggTP_cnt w v = ggTP_cnt w c := by
    have h0 : ggTP_cnt 0 v = ggTP_cnt 0 c := congrArg Prod.fst hshape
    have h1 : ggTP_cnt 1 v = ggTP_cnt 1 c :=
      congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) hshape
    have h2 : ggTP_cnt 2 v = ggTP_cnt 2 c :=
      congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) hshape
    intro w
    fin_cases w
    · exact h0
    · exact h1
    · exact h2
  rw [← ggTP_Y_eq_of_shape hvc]
  exact ggTP_Y_reps_ge v hv

private lemma ggTP_ofAdd_pow (a : ZMod 3) (n : ℕ) :
    (Multiplicative.ofAdd a) ^ n = Multiplicative.ofAdd (n • a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← ofAdd_add, succ_nsmul]

private lemma ggTP_ofAdd_prod {ι : Type*} (s : Finset ι) (a : ι → ZMod 3) :
    s.prod (fun i => Multiplicative.ofAdd (a i)) = Multiplicative.ofAdd (s.sum a) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ofAdd_add]

private lemma ggTP_pi_char (ψ : (Fin 5 → Multiplicative (ZMod 3)) →* Multiplicative (ZMod 3)) :
    ∃ d : Fin 5 → ZMod 3, ∀ g, ψ g = Multiplicative.ofAdd (∑ i, d i * (g i).toAdd) := by
  refine ⟨fun i => (ψ (Function.update 1 i (Multiplicative.ofAdd 1))).toAdd, fun g => ?_⟩
  set d : Fin 5 → ZMod 3 :=
    fun i => (ψ (Function.update 1 i (Multiplicative.ofAdd 1))).toAdd with hd
  have hg : g = ∏ i, Function.update (1 : Fin 5 → Multiplicative (ZMod 3)) i (g i) := by
    funext j
    rw [Finset.prod_apply]
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hi
      rw [Function.update_of_ne (Ne.symm hi)]
      rfl
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hterm : ∀ i, ψ (Function.update (1 : Fin 5 → Multiplicative (ZMod 3)) i (g i)) =
      Multiplicative.ofAdd (d i * (g i).toAdd) := by
    intro i
    have hupd : Function.update (1 : Fin 5 → Multiplicative (ZMod 3)) i (g i) =
        (Function.update (1 : Fin 5 → Multiplicative (ZMod 3)) i
          (Multiplicative.ofAdd 1)) ^ ((g i).toAdd).val := by
      funext j
      by_cases h : j = i
      · subst h
        rw [Function.update_self, Pi.pow_apply, Function.update_self, ggTP_ofAdd_pow,
          nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
        rfl
      · rw [Function.update_of_ne h, Pi.pow_apply, Function.update_of_ne h]; simp
    rw [hupd, map_pow, show ψ (Function.update 1 i (Multiplicative.ofAdd 1)) =
      Multiplicative.ofAdd (d i) from rfl, ggTP_ofAdd_pow]
    show Multiplicative.ofAdd (((g i).toAdd).val • d i) =
      Multiplicative.ofAdd (d i * (g i).toAdd)
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  conv_lhs => rw [hg]
  rw [map_prod]
  simp_rw [hterm]
  rw [ggTP_ofAdd_prod]

private def ggTP_emb : GGTPTorus →* (Fin 5 → Multiplicative (ZMod 3)) where
  toFun x := fun i => x.1 (Fin.castSucc i)
  map_one' := rfl
  map_mul' _ _ := rfl

private def ggTP_snoc (g : Fin 5 → Multiplicative (ZMod 3)) : Fin 6 → Multiplicative (ZMod 3) :=
  Fin.snoc g ((∏ i, g i)⁻¹)

private lemma ggTP_snoc_mem (g : Fin 5 → Multiplicative (ZMod 3)) :
    ggTP_snoc g ∈ GGTPTorus := by
  show (∏ i, ggTP_snoc g i) = 1
  rw [Fin.prod_univ_castSucc]
  have h1 : (∏ i : Fin 5, ggTP_snoc g (Fin.castSucc i)) = ∏ i, g i := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ggTP_snoc, Fin.snoc_castSucc]
  rw [h1, ggTP_snoc, Fin.snoc_last]
  exact mul_inv_cancel _

private def ggTP_invEmb (g : Fin 5 → Multiplicative (ZMod 3)) : GGTPTorus :=
  ⟨ggTP_snoc g, ggTP_snoc_mem g⟩

private lemma ggTP_emb_invEmb (g : Fin 5 → Multiplicative (ZMod 3)) :
    ggTP_emb (ggTP_invEmb g) = g := by
  funext i
  show ggTP_snoc g (Fin.castSucc i) = g i
  rw [ggTP_snoc, Fin.snoc_castSucc]

private lemma ggTP_invEmb_emb (x : GGTPTorus) : ggTP_invEmb (ggTP_emb x) = x := by
  apply Subtype.ext
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · show ggTP_snoc (ggTP_emb x) (Fin.castSucc j) = x.1 (Fin.castSucc j)
    rw [ggTP_snoc, Fin.snoc_castSucc]
    rfl
  · show (∏ i, ggTP_emb x i)⁻¹ = x.1 (Fin.last 5)
    have hx : ∏ i, x.1 i = 1 := x.2
    rw [Fin.prod_univ_castSucc] at hx
    rw [show (∏ i, ggTP_emb x i) = ∏ i : Fin 5, x.1 (Fin.castSucc i) from rfl]
    exact inv_eq_of_mul_eq_one_right hx

private noncomputable def ggTP_embEquiv : GGTPTorus ≃* (Fin 5 → Multiplicative (ZMod 3)) :=
  MulEquiv.ofBijective ggTP_emb
    ⟨fun x y h => by
        have := congrArg ggTP_invEmb h
        simpa [ggTP_invEmb_emb] using this,
     fun g => ⟨ggTP_invEmb g, ggTP_emb_invEmb g⟩⟩

private lemma ggTP_embEquiv_apply (x : GGTPTorus) (i : Fin 5) :
    ggTP_embEquiv x i = x.1 (Fin.castSucc i) := rfl

private lemma ggTP_structure (ψ : GGTPTorus →* Multiplicative (ZMod 3)) :
    ∃ c : Fin 6 → ZMod 3, ψ = ggTP_charS c := by
  obtain ⟨d, hd⟩ := ggTP_pi_char (ψ.comp ggTP_embEquiv.symm)
  refine ⟨Fin.snoc (α := fun _ => ZMod 3) d (0 : ZMod 3), ?_⟩
  ext x
  have h : ψ x = Multiplicative.ofAdd (∑ i, d i * (x.1 (Fin.castSucc i)).toAdd) := by
    have hh := hd (ggTP_embEquiv x)
    simp only [MonoidHom.comp_apply] at hh
    have hsym : (ggTP_embEquiv.symm) (ggTP_embEquiv x) = x :=
      MulEquiv.symm_apply_apply ggTP_embEquiv x
    have hh' := hsym ▸ hh
    simpa only [ggTP_embEquiv_apply] using hh'
  rw [h]
  show Multiplicative.ofAdd (∑ i, d i * (x.1 (Fin.castSucc i)).toAdd) =
    Multiplicative.ofAdd (∑ j, (Fin.snoc (α := fun _ => ZMod 3) d (0 : ZMod 3)) j * (x.1 j).toAdd)
  congr 1
  conv_rhs => rw [Fin.sum_univ_castSucc]
  rw [Fin.snoc_last]
  simp [Fin.snoc_castSucc]

private def ggTP_cst : GGTPTorus :=
  ⟨fun _ => Multiplicative.ofAdd 1, by
    show (∏ _i : Fin 6, (Multiplicative.ofAdd 1 : Multiplicative (ZMod 3))) = 1
    rw [Finset.prod_const]
    show (Multiplicative.ofAdd 1 : Multiplicative (ZMod 3)) ^ 6 = 1
    rw [ggTP_ofAdd_pow]
    decide⟩

private lemma ggTP_cst_mem_const :
    (ggTP_cst : Fin 6 → Multiplicative (ZMod 3)) ∈ GGTPTorusConst := fun _ _ => rfl

private lemma ggTP_charS_cst (c : Fin 6 → ZMod 3) :
    ggTP_charS c ggTP_cst = Multiplicative.ofAdd (∑ i, c i) := by
  simp only [ggTP_charS, ggTP_charOf, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
    ggTP_pair, ggTP_cst]
  congr 1
  simp

private lemma ggTP_exists_perm_of_fibers {α β : Type*} [Fintype α] [DecidableEq β]
    {f g : α → β}
    (h : ∀ b, (Finset.univ.filter (fun a => f a = b)).card =
        (Finset.univ.filter (fun a => g a = b)).card) :
    ∃ σ : Equiv.Perm α, ∀ a, f (σ a) = g a := by
  have hcard : ∀ b, Fintype.card {a // g a = b} = Fintype.card {a // f a = b} := by
    intro b
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact (h b).symm
  let e : ∀ b, {a // g a = b} ≃ {a // f a = b} := fun b => Fintype.equivOfCardEq (hcard b)
  refine ⟨Equiv.ofFiberEquiv (f := g) (g := f) e, fun a => ?_⟩
  exact Equiv.ofFiberEquiv_map (f := g) (g := f) e a

private def ggTP_raw (c : Fin 6 → ZMod 3) : Finset (Fin 6 → ZMod 3) :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin 6) => fun i => c (σ i))

private def ggTP_norm (x : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 := fun i => x i - x 0

private lemma ggTP_norm_image_eq_Y (c : Fin 6 → ZMod 3) :
    (ggTP_raw c).image ggTP_norm = ggTP_Y c := by
  ext y
  constructor
  · intro hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    rw [ggTP_raw, Finset.mem_image] at hx
    obtain ⟨σ, -, rfl⟩ := hx
    rw [ggTP_Y, Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
    rw [← hyx]
    refine ⟨by simp [ggTP_norm], c (σ 0), fun v => ?_⟩
    have hpred : (Finset.univ.filter (fun i => ggTP_norm (fun j => c (σ j)) i = v)) =
        Finset.univ.filter (fun i => c (σ i) = v + c (σ 0)) := by
      refine Finset.filter_congr fun i _ => ?_
      simp only [ggTP_norm]
      rw [sub_eq_iff_eq_add]
    simp only [ggTP_cnt]
    rw [hpred, ← Fintype.card_subtype (fun i => c (σ i) = v + c (σ 0)),
      ← Fintype.card_subtype (fun j => c j = v + c (σ 0))]
    exact Fintype.card_congr (Equiv.subtypeEquiv σ fun _ => Iff.rfl)
  · intro hy
    simp only [ggTP_Y, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨hy0, k, hk⟩ := hy
    have hshape : ∀ b, ggTP_cnt b (fun i => y i + k) = ggTP_cnt b c := by
      intro b
      have hpred : (Finset.univ.filter (fun i => y i + k = b)) =
          Finset.univ.filter (fun i => y i = b - k) := by
        refine Finset.filter_congr fun i _ => ?_
        constructor <;> intro h
        · rw [← h, add_sub_cancel_right]
        · rw [h, sub_add_cancel]
      have hthis := hk (b - k)
      simp only [ggTP_cnt] at hthis ⊢
      rw [hpred]
      simpa [sub_add_cancel] using hthis
    obtain ⟨σ, hσ⟩ := ggTP_exists_perm_of_fibers (fun b => (hshape b).symm)
    rw [Finset.mem_image]
    refine ⟨fun i => c (σ i), ?_, ?_⟩
    · rw [ggTP_raw]
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
    · funext i
      simp only [ggTP_norm]
      rw [hσ i, hσ 0]
      simp [hy0]

private def ggTP_b (j : Fin 6) : Fin 6 → Multiplicative (ZMod 3) :=
  Function.update
    (Function.update (1 : Fin 6 → Multiplicative (ZMod 3)) 0 (Multiplicative.ofAdd (-1)))
    j (Multiplicative.ofAdd 1)

private lemma ggTP_b_self (j : Fin 6) : ggTP_b j j = Multiplicative.ofAdd 1 :=
  Function.update_self ..

private lemma ggTP_b_zero (j : Fin 6) (hj : j ≠ 0) :
    ggTP_b j 0 = Multiplicative.ofAdd (-1) := by
  rw [ggTP_b, Function.update_of_ne (Ne.symm hj), Function.update_self]

private lemma ggTP_b_of_ne (j i : Fin 6) (hi : i ≠ j) (hi0 : i ≠ 0) : ggTP_b j i = 1 := by
  rw [ggTP_b, Function.update_of_ne hi, Function.update_of_ne hi0]
  rfl

private lemma ggTP_b_mem (j : Fin 6) (hj : j ≠ 0) : ggTP_b j ∈ GGTPTorus := by
  show (∏ i, ggTP_b j i) = 1
  rw [← Finset.prod_erase_mul (Finset.univ) (ggTP_b j) (Finset.mem_univ (0 : Fin 6))]
  rw [ggTP_b_zero j hj]
  have h1 : (∏ i ∈ Finset.univ.erase (0 : Fin 6), ggTP_b j i) = Multiplicative.ofAdd 1 := by
    rw [Finset.prod_eq_single j]
    · rw [ggTP_b_self]
    · intro i hi hij
      exact ggTP_b_of_ne j i hij (Finset.mem_erase.mp hi).1
    · intro hj'
      exact absurd (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) hj'
  rw [h1]
  rfl

private lemma ggTP_pair_b (y : Fin 6 → ZMod 3) (j : Fin 6) (hj : j ≠ 0) :
    ggTP_pair y (ggTP_b j) = y j - y 0 := by
  simp only [ggTP_pair]
  rw [← Finset.sum_erase_add (Finset.univ) (fun i => y i * (ggTP_b j i).toAdd)
    (Finset.mem_univ (0 : Fin 6))]
  have h0 : y 0 * (ggTP_b j 0).toAdd = - y 0 := by
    rw [ggTP_b_zero j hj, toAdd_ofAdd]
    exact mul_neg_one (y 0)
  rw [h0]
  have h1 : (∑ i ∈ Finset.univ.erase (0 : Fin 6), y i * (ggTP_b j i).toAdd) = y j := by
    rw [Finset.sum_eq_single j]
    · rw [ggTP_b_self]; simp
    · intro i hi hij
      rw [ggTP_b_of_ne j i hij (Finset.mem_erase.mp hi).1]; simp
    · intro hj'
      exact absurd (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) hj'
  rw [h1, sub_eq_add_neg]
  rfl

private lemma ggTP_charS_apply (y : Fin 6 → ZMod 3) (z : GGTPTorus) :
    ggTP_charS y z = Multiplicative.ofAdd (ggTP_pair y z.1) := rfl

private lemma ggTP_charS_injOn_zero : Set.InjOn ggTP_charS {y : Fin 6 → ZMod 3 | y 0 = 0} := by
  intro y hy y' hy' h
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [hy, hy']
  · have hb := congrArg
      (fun φ : GGTPTorus →* Multiplicative (ZMod 3) => φ ⟨ggTP_b j, ggTP_b_mem j hj⟩) h
    rw [ggTP_charS_apply, ggTP_charS_apply, ggTP_pair_b y j hj, ggTP_pair_b y' j hj] at hb
    have hb' := congrArg Multiplicative.toAdd hb
    rw [hy, hy'] at hb'
    simpa using hb'



private lemma ggTP_pow_three (x : GGTPTorus) : x ^ 3 = 1 := by
  apply Subtype.ext
  funext i
  show ((x.1 i) ^ 3) = 1
  rw [show x.1 i = Multiplicative.ofAdd ((x.1 i).toAdd) from rfl, ggTP_ofAdd_pow]
  rw [show (3 : ℕ) • ((x.1 i).toAdd) = 0 by
    rw [nsmul_eq_mul, show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]]
  rfl

private lemma ggTP_charS_const (k : ZMod 3) :
    ggTP_charS (fun _ : Fin 6 => k) = 1 := by
  ext x
  show Multiplicative.ofAdd (∑ i, k * (x.1 i).toAdd) = 1
  have hk : (∑ i, k * (x.1 i).toAdd) = 0 := by
    calc
      (∑ i, k * (x.1 i).toAdd) = k * ∑ i, (x.1 i).toAdd := by
        rw [Finset.mul_sum]
      _ = k * 0 := by rw [ggTP_sum_toAdd]
      _ = 0 := by simp
  rw [hk]
  rfl

private noncomputable instance ggTP_decEqHom : DecidableEq (GGTPTorus →* Multiplicative (ZMod 3)) :=
  Classical.decEq _

private lemma ggTP_orbit_ge (c : Fin 6 → ZMod 3) (hsum : ∑ i, c i = 0)
    (hnc : ¬ ∃ k, ∀ i, c i = k) :
    20 ≤ (Finset.univ.image (fun σ : Equiv.Perm (Fin 6) =>
      (ggTP_charS c).comp (ggTPPermAct σ))).card := by
  classical
  have h1 : (Finset.univ.image (fun σ : Equiv.Perm (Fin 6) =>
      (ggTP_charS c).comp (ggTPPermAct σ))) = (ggTP_raw c).image ggTP_charS := by
    rw [ggTP_raw, Finset.image_image]
    refine Finset.image_congr ?_
    intro σ _
    exact ggTP_charS_perm c σ
  rw [h1]
  have h2 : (ggTP_raw c).image ggTP_charS =
      ((ggTP_raw c).image ggTP_norm).image ggTP_charS := by
    rw [Finset.image_image]
    refine Finset.image_congr ?_
    intro x _
    exact (ggTP_charS_sub_const x (x 0)).symm
  rw [h2, ggTP_norm_image_eq_Y]
  rw [Finset.card_image_of_injOn (fun a ha b hb hab => by
    refine ggTP_charS_injOn_zero ?_ ?_ hab
    · exact (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2.1
    · exact (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.1)]
  exact ggTP_Y_ge c hsum hnc

private lemma ggTP_orbit_ge' (ψ : GGTPTorus →* Multiplicative (ZMod 3))
    (hψC : ∀ c : GGTPTorus,
      (c : Fin 6 → Multiplicative (ZMod 3)) ∈ GGTPTorusConst → ψ c = 1)
    (hψ1 : ψ ≠ 1) :
    20 ≤ (Finset.univ.image (fun σ : Equiv.Perm (Fin 6) =>
      ψ.comp (ggTPPermAct σ))).card := by
  classical
  obtain ⟨c₀, hc⟩ := ggTP_structure ψ
  rw [hc] at hψC hψ1 ⊢
  have hsum : ∑ i, c₀ i = 0 := by
    have h := hψC ggTP_cst ggTP_cst_mem_const
    rw [ggTP_charS_cst] at h
    have := congrArg Multiplicative.toAdd h
    simpa using this
  have hnc : ¬ ∃ k, ∀ i, c₀ i = k := by
    rintro ⟨k, hk⟩
    apply hψ1
    have hc' : c₀ = fun _ => k := funext hk
    rw [hc', ggTP_charS_const]
  exact ggTP_orbit_ge c₀ hsum hnc

private noncomputable def ggTP_phi (K : Type*) [Field K] (ω : K)
    (hω : IsPrimitiveRoot ω 3) : Multiplicative (ZMod 3) →* Kˣ where
  toFun a := Units.mk0 (ω ^ a.toAdd.val) (pow_ne_zero _ (hω.ne_zero (by norm_num)))
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    rw [show (a * b).toAdd = a.toAdd + b.toAdd from rfl, ZMod.val_add]
    rw [pow_eq_pow_of_modEq (Nat.mod_modEq _ 3) hω.pow_eq_one, pow_add]

private lemma ggTP_phi_injective (K : Type*) [Field K] (ω : K)
    (hω : IsPrimitiveRoot ω 3) : Function.Injective (ggTP_phi K ω hω) := by
  intro a b h
  let u : Kˣ := (hω.isUnit (by norm_num)).unit
  have hu : IsPrimitiveRoot u 3 := hω.isUnit_unit (by norm_num)
  have hcoe : (u : K) = ω := IsUnit.unit_spec _
  have h' : ω ^ a.toAdd.val = ω ^ b.toAdd.val := by
    have := congrArg (fun v : Kˣ => (v : K)) h
    simpa [ggTP_phi] using this
  have h'u : u ^ a.toAdd.val = u ^ b.toAdd.val := by
    apply Units.ext
    simpa [hcoe] using h'
  have hmod := (pow_eq_pow_iff_modEq (x := u)).mp h'u
  rw [← hu.eq_orderOf] at hmod
  have hv : a.toAdd.val = b.toAdd.val := by
    rw [Nat.ModEq] at hmod
    have ha := ZMod.val_lt a.toAdd
    have hb := ZMod.val_lt b.toAdd
    omega
  apply Multiplicative.toAdd.injective
  exact ZMod.val_injective _ hv

private lemma ggTP_cube_root_eq (K : Type*) [Field K] (ω : K)
    (hω : IsPrimitiveRoot ω 3) {z : K} (hz : z ^ 3 = 1) :
    z = 1 ∨ z = ω ∨ z = ω ^ 2 := by
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr (hω.ne_one (by norm_num))
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      rw [show (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 by ring]
      rw [hω3]; ring
    exact (mul_eq_zero.mp this).resolve_left hne
  have hfac : (z - 1) * (z - ω) * (z - ω ^ 2) = z ^ 3 - 1 := by
    calc
      (z - 1) * (z - ω) * (z - ω ^ 2)
          = z ^ 3 - z ^ 2 * (1 + ω + ω ^ 2) + z * (ω + ω ^ 2 + ω ^ 3) - ω ^ 3 := by ring
      _ = z ^ 3 - 1 := by
        rw [show 1 + ω + ω ^ 2 = 0 by linear_combination hω2]
        rw [show ω + ω ^ 2 + ω ^ 3 = 0 by rw [hω3]; linear_combination hω2]
        rw [hω3]; ring
  have h0 : (z - 1) * (z - ω) * (z - ω ^ 2) = 0 := by rw [hfac, hz]; ring
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

private lemma ggTP_phi_range (K : Type*) [Field K] (ω : K) (hω : IsPrimitiveRoot ω 3) :
    (ggTP_phi K ω hω).range = {z : Kˣ | z ^ 3 = 1} := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    show (ggTP_phi K ω hω a) ^ 3 = 1
    rw [← map_pow]
    have ha : a ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [show (a ^ 3).toAdd = 3 • a.toAdd from rfl, nsmul_eq_mul,
        show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
      rfl
    rw [ha, map_one]
  · intro hz
    have hz3 : (z : K) ^ 3 = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hz
      simpa using this
    rcases ggTP_cube_root_eq K ω hω hz3 with h | h | h
    · exact ⟨1, by apply Units.ext; simp [ggTP_phi, h]⟩
    · exact ⟨Multiplicative.ofAdd 1, by
        apply Units.ext
        rw [h]
        change ω ^ (Multiplicative.ofAdd (1 : ZMod 3)).toAdd.val = ω
        rw [show (Multiplicative.ofAdd (1 : ZMod 3)).toAdd.val = 1 by decide]
        exact pow_one _⟩
    · exact ⟨Multiplicative.ofAdd 2, by
        apply Units.ext
        rw [h]
        change ω ^ (Multiplicative.ofAdd (2 : ZMod 3)).toAdd.val = ω ^ 2
        rw [show (Multiplicative.ofAdd (2 : ZMod 3)).toAdd.val = 2 by decide]⟩

theorem ggTPWeight_abstract {X : Type} [Group X] {F : Type} [Field F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : X →* LinearMap.GeneralLinearGroup F V) (hρ : Function.Injective ρ)
    (θ : GGTPTorus →* X)
    (hθ : ∀ x : GGTPTorus, θ x = 1 ↔ (x : Fin 6 → Multiplicative (ZMod 3)) ∈ GGTPTorusConst)
    (hperm : ∀ σ : Equiv.Perm (Fin 6), ∃ g : X, ∀ x : GGTPTorus,
      g * θ x * g⁻¹ = θ (ggTPPermAct σ x)) :
    20 ≤ Module.finrank F V := by
  classical
  let x0val : Fin 6 → Multiplicative (ZMod 3) :=
    fun i => if i = 0 then Multiplicative.ofAdd 1
             else if i = 1 then Multiplicative.ofAdd 2 else 1
  have hx0mem : x0val ∈ GGTPTorus := by
    show (∏ i, x0val i) = 1
    decide +kernel
  let x0 : GGTPTorus := ⟨x0val, hx0mem⟩
  have hx0notC : (x0 : Fin 6 → Multiplicative (ZMod 3)) ∉ GGTPTorusConst := by
    intro h
    exact (by decide : x0val 0 ≠ x0val 1) (h 0 1)
  have hθx0 : θ x0 ≠ 1 := fun h => hx0notC ((hθ x0).mp h)
  let Fb := AlgebraicClosure F
  let Vb := TensorProduct F Fb V
  haveI : CharP Fb 2 := inferInstance
  haveI hFree : Module.Free F V := Module.Free.of_divisionRing F V
  haveI hFlat : Module.Flat F V := Module.Flat.of_free
  haveI : FaithfulSMul F Fb := inferInstance
  haveI hfinVb : Module.Finite Fb Vb :=
    Module.Finite.of_basis ((Module.finBasis F V).baseChange Fb)
  haveI hfdVb : FiniteDimensional Fb Vb := hfinVb
  have hfr : Module.finrank Fb Vb = Module.finrank F V := Module.finrank_baseChange
  let ρb : X →* Module.End Fb Vb :=
    { toFun := fun g => LinearMap.baseChange Fb (ρ g : V →ₗ[F] V)
      map_one' := by
        have h : (ρ 1 : V →ₗ[F] V) = 1 := by rw [map_one]; rfl
        rw [h, LinearMap.baseChange_one]
      map_mul' := fun g h => by
        have hm : (ρ (g * h) : V →ₗ[F] V) = (ρ g : V →ₗ[F] V) * (ρ h : V →ₗ[F] V) := by
          rw [map_mul]; rfl
        rw [hm, LinearMap.baseChange_mul] }
  have hρb : Function.Injective ρb := by
    intro g h hgh
    have hinj : Function.Injective (LinearMap.baseChangeHom F Fb V V) :=
      LinearMap.baseChangeHom_injective (R := F) (M := V) (S := Fb)
    have hlin : (ρ g : V →ₗ[F] V) = (ρ h : V →ₗ[F] V) := hinj hgh
    exact hρ (Units.ext hlin)
  let A : Subgroup X := θ.range
  haveI hfinA : Finite A := by
    apply Finite.of_surjective (fun x : GGTPTorus => (⟨θ x, ⟨x, rfl⟩⟩ : A))
    intro a
    obtain ⟨x, hx⟩ := a.2
    exact ⟨x, Subtype.ext hx⟩
  have hAcomm : IsMulCommutative A := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    show (a : X) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm x y]
  have hAdvd : Nat.card A ∣ 3 ^ 6 := by
    have h1 : Nat.card A ∣ Nat.card GGTPTorus := Subgroup.card_range_dvd θ
    have h2 : Nat.card GGTPTorus ∣ 3 ^ 6 := by
      have h3 : Nat.card GGTPTorus ∣ Nat.card (Fin 6 → Multiplicative (ZMod 3)) :=
        Subgroup.card_subgroup_dvd_card GGTPTorus
      simpa using h3
    exact h1.trans h2
  have hinv : (Nat.card A : Fb) ≠ 0 := by
    intro h2
    rw [CharP.cast_eq_zero_iff Fb 2] at h2
    have : (2 : ℕ) ∣ 3 ^ 6 := h2.trans hAdvd
    omega
  have hAne : ρb (θ x0) ≠ 1 := by
    intro h
    apply hθx0
    apply hρb
    rw [h, map_one]
  have hTne : ρb (θ x0) - 1 ≠ 0 := sub_ne_zero.mpr hAne
  obtain ⟨χ, w, hχ, hTw⟩ :=
    CFSG.SignalizerFunctorTheorem.NonLocal.exists_jointEigenvector_apply_ne_zero
      ρb A hAcomm hinv (ρb (θ x0) - 1) hTne
  have hw0 : w ≠ 0 := by
    intro h
    apply hTw
    rw [h]
    simp
  have hχx0 : χ ⟨θ x0, ⟨x0, rfl⟩⟩ ≠ 1 := by
    intro h
    apply hTw
    have hh := hχ ⟨θ x0, ⟨x0, rfl⟩⟩
    rw [h, one_smul] at hh
    have h1 : (ρb (θ x0) - 1) w = 0 := by
      rw [LinearMap.sub_apply]
      rw [show ρb (θ x0) w = w from hh]
      simp
    exact h1
  have hχne : ∀ a : A, χ a ≠ 0 := by
    intro a ha
    have h1 : ρb a w = 0 := by rw [hχ, ha, zero_smul]
    have hunit : ρb a⁻¹ * ρb a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : w = 0 := by
      have := congrArg (fun T : Module.End Fb Vb => T w) hunit
      change ρb a⁻¹ (ρb a w) = w at this
      rw [h1, map_zero] at this
      exact this.symm
    exact hw0 h2
  have hχone : χ 1 = 1 := by
    have h := hχ 1
    rw [show ((1 : A) : X) = 1 from rfl, map_one] at h
    have hw : w = χ 1 • w := by simpa using h
    have h2 : (1 - χ 1) • w = 0 := by
      rw [show (1 - χ 1) • w = (1 : Fb) • w - χ 1 • w from sub_smul 1 (χ 1) w]
      rw [one_smul, ← hw, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw0)).symm
  have hχmul : ∀ a b : A, χ (a * b) = χ a * χ b := by
    intro a b
    have h := hχ (a * b)
    rw [show ((a * b : A) : X) = (a : X) * (b : X) from rfl, map_mul] at h
    have h2 : (ρb a * ρb b) w = (χ a * χ b) • w := by
      change ρb a (ρb b w) = (χ a * χ b) • w
      rw [hχ b, map_smul, hχ a, smul_smul, mul_comm]
    have h3 : (χ a * χ b) • w = χ (a * b) • w := by rw [← h2]; exact h
    have h4 : (χ a * χ b - χ (a * b)) • w = 0 := by
      rw [show (χ a * χ b - χ (a * b)) • w =
        (χ a * χ b) • w - χ (a * b) • w from sub_smul (χ a * χ b) (χ (a * b)) w]
      rw [h3, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hw0)).symm
  let χu : A →* Fbˣ :=
    { toFun := fun a => Units.mk0 (χ a) (hχne a)
      map_one' := by ext; simp [hχone]
      map_mul' := fun a b => by ext; simp [hχmul] }
  haveI h3F : NeZero (3 : F) := ⟨by
    intro h
    have h' : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp h
    omega⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Fb, IsPrimitiveRoot ω 3 := HasEnoughRootsOfUnity.exists_primitiveRoot Fb 3
  have ha3 : ∀ a : A, a ^ 3 = 1 := by
    intro a
    obtain ⟨x, hx⟩ := a.2
    apply Subtype.ext
    show ((a : X)) ^ 3 = 1
    rw [← hx, ← map_pow, ggTP_pow_three, map_one]
  have hχu3 : ∀ a : A, (χu a) ^ 3 = 1 := by
    intro a
    rw [← map_pow, ha3, map_one]
  have hχurange : ∀ a : A, χu a ∈ (ggTP_phi Fb ω hω).range := by
    intro a
    change χu a ∈ ((ggTP_phi Fb ω hω).range : Set Fbˣ)
    rw [ggTP_phi_range Fb ω hω]
    exact hχu3 a
  let φ := ggTP_phi Fb ω hω
  have hφinj : Function.Injective φ := ggTP_phi_injective Fb ω hω
  let e := MonoidHom.ofInjective hφinj
  let ψ0 : A →* Multiplicative (ZMod 3) :=
    (e.symm : φ.range →* Multiplicative (ZMod 3)).comp (χu.codRestrict φ.range hχurange)
  have hψ0 : ∀ a : A, φ (ψ0 a) = χu a := by
    intro a
    have h1 : e (ψ0 a) = χu.codRestrict φ.range hχurange a := by
      simp [ψ0]
    exact congrArg Subtype.val h1
  let ψS0 : GGTPTorus →* Multiplicative (ZMod 3) :=
    { toFun := fun x => ψ0 ⟨θ x, ⟨x, rfl⟩⟩
      map_one' := by
        have h : (⟨θ 1, ⟨(1 : GGTPTorus), rfl⟩⟩ : A) = 1 := Subtype.ext (map_one θ)
        show ψ0 ⟨θ 1, ⟨(1 : GGTPTorus), rfl⟩⟩ = 1
        rw [h, map_one]
      map_mul' := fun x y => by
        show ψ0 ⟨θ (x * y), _⟩ = ψ0 ⟨θ x, _⟩ * ψ0 ⟨θ y, _⟩
        rw [← map_mul]
        exact congrArg ψ0 (Subtype.ext (map_mul θ x y)) }
  have hψS0_C : ∀ c : GGTPTorus,
      (c : Fin 6 → Multiplicative (ZMod 3)) ∈ GGTPTorusConst → ψS0 c = 1 := by
    intro c hc
    have hθc : θ c = 1 := (hθ c).mpr hc
    show ψ0 ⟨θ c, ⟨c, rfl⟩⟩ = 1
    have hsub : (⟨θ c, ⟨c, rfl⟩⟩ : A) = 1 := Subtype.ext hθc
    rw [hsub, map_one]
  have hψS01 : ψS0 ≠ 1 := by
    intro h1
    have h2 : ψ0 ⟨θ x0, ⟨x0, rfl⟩⟩ = 1 := by
      have := congrFun (congrArg
        (fun f : GGTPTorus →* Multiplicative (ZMod 3) => (f : GGTPTorus → _)) h1) x0
      simpa [ψS0] using this
    have h3 : χu ⟨θ x0, ⟨x0, rfl⟩⟩ = 1 := by
      rw [← hψ0 ⟨θ x0, ⟨x0, rfl⟩⟩, h2, map_one]
    have h4 : χ ⟨θ x0, ⟨x0, rfl⟩⟩ = 1 := by
      have := congrArg (fun u : Fbˣ => (u : Fb)) h3
      simpa [χu] using this
    exact hχx0 h4
  let orbit : Finset (GGTPTorus →* Multiplicative (ZMod 3)) :=
    Finset.univ.image (fun σ : Equiv.Perm (Fin 6) => ψS0.comp (ggTPPermAct σ))
  have horbit : 20 ≤ orbit.card := ggTP_orbit_ge' ψS0 hψS0_C hψS01
  haveI hFintypeOrbit : Fintype ↥orbit := Finset.fintypeCoeSort orbit
  let πOf (ψ : ↥orbit) : Equiv.Perm (Fin 6) :=
    Classical.choose (Finset.mem_image.mp ψ.2)
  have hπOf (ψ : ↥orbit) : ψS0.comp (ggTPPermAct (πOf ψ)) = ψ.1 :=
    (Classical.choose_spec (Finset.mem_image.mp ψ.2)).2
  let gOf (ψ : ↥orbit) : X := Classical.choose (hperm (πOf ψ)⁻¹)
  have hgOf (ψ : ↥orbit) :
      ∀ x : GGTPTorus, gOf ψ * θ x * (gOf ψ)⁻¹ = θ (ggTPPermAct (πOf ψ)⁻¹ x) :=
    Classical.choose_spec (hperm (πOf ψ)⁻¹)
  let wOf (ψ : ↥orbit) : Vb := ρb (gOf ψ) w
  have hwOf : ∀ ψ : ↥orbit, wOf ψ ≠ 0 := by
    intro ψ h
    have h1 : ρb (gOf ψ) w = 0 := h
    have hunit : ρb (gOf ψ)⁻¹ * ρb (gOf ψ) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : w = 0 := by
      have := congrArg (fun T : Module.End Fb Vb => T w) hunit
      change ρb (gOf ψ)⁻¹ (ρb (gOf ψ) w) = w at this
      rw [h1, map_zero] at this
      exact this.symm
    exact hw0 h2
  let χOf (ψ : ↥orbit) : (⊤ : Subgroup GGTPTorus) → Fb :=
    fun a => (φ (ψ.1 (a : GGTPTorus)) : Fb)
  have hχOf_inj : Function.Injective χOf := by
    intro ψ₁ ψ₂ h
    apply Subtype.ext
    ext x
    have h1 := congrFun h ⟨x, trivial⟩
    simp only [χOf] at h1
    have h2 : φ (ψ₁.1 x) = φ (ψ₂.1 x) := Units.ext h1
    exact hφinj h2
  have hev : ∀ (ψ : ↥orbit) (a : (⊤ : Subgroup GGTPTorus)),
      (ρb.comp θ) (a : GGTPTorus) (wOf ψ) = χOf ψ a • wOf ψ := by
    intro ψ a
    set x : GGTPTorus := (a : GGTPTorus)
    set π : Equiv.Perm (Fin 6) := πOf ψ with hπdef
    set g : X := gOf ψ with hgdef
    have hπ : ψS0.comp (ggTPPermAct π) = ψ.1 := hπOf ψ
    have hg2 : g * θ (ggTPPermAct π x) * g⁻¹ = θ x := by
      have h := hgOf ψ (ggTPPermAct π x)
      rw [show ggTPPermAct (πOf ψ)⁻¹ (ggTPPermAct π x) = x by
        apply Subtype.ext
        funext i
        simp [ggTPPermAct, hπdef]] at h
      exact h
    have hg' : θ (ggTPPermAct π x) = g⁻¹ * θ x * g := by
      calc θ (ggTPPermAct π x) = g⁻¹ * (g * θ (ggTPPermAct π x) * g⁻¹) * g := by group
        _ = g⁻¹ * θ x * g := by rw [hg2]
    have harg : θ x * g = g * θ (ggTPPermAct π x) := by
      rw [hg']
      group
    have h1 : ρb (θ x) (ρb g w) = ρb g (ρb (θ (ggTPPermAct π x)) w) := by
      rw [← Module.End.mul_apply, ← map_mul, harg, map_mul, Module.End.mul_apply]
    change ρb (θ x) (ρb g w) = χOf ψ a • ρb g w
    rw [h1]
    rw [show ρb (θ (ggTPPermAct π x)) w =
      χ ⟨θ (ggTPPermAct π x), ⟨ggTPPermAct π x, rfl⟩⟩ • w from
        hχ ⟨θ (ggTPPermAct π x), ⟨ggTPPermAct π x, rfl⟩⟩]
    rw [map_smul]
    congr 1
    have hψ : ψ.1 x = ψS0 (ggTPPermAct π x) := by
      have := congrFun (congrArg
        (fun f : GGTPTorus →* Multiplicative (ZMod 3) => (f : GGTPTorus → _)) hπ) x
      simpa using this.symm
    show χ ⟨θ (ggTPPermAct π x), ⟨ggTPPermAct π x, rfl⟩⟩ = χOf ψ a
    rw [show χOf ψ a = (φ (ψ.1 x) : Fb) from rfl, hψ]
    rw [show ψS0 (ggTPPermAct π x) =
      ψ0 ⟨θ (ggTPPermAct π x), ⟨ggTPPermAct π x, rfl⟩⟩ from rfl, hψ0]
    rfl
  have hLI : LinearIndependent Fb (fun ψ : ↥orbit => wOf ψ) :=
    CFSG.SignalizerFunctorTheorem.NonLocal.linearIndependent_of_distinct_weights
      (ρb.comp θ) (⊤ : Subgroup GGTPTorus)
      ⟨⟨fun a b => Subtype.ext (mul_comm (a : GGTPTorus) (b : GGTPTorus))⟩⟩
      (fun ψ => wOf ψ) χOf hwOf hev hχOf_inj
  have hcard_le : Fintype.card ↥orbit ≤ Module.finrank Fb Vb :=
    hLI.fintype_card_le_finrank
  have hcard_eq : Fintype.card ↥orbit = orbit.card := Fintype.card_coe orbit
  calc 20 ≤ orbit.card := horbit
    _ = Fintype.card ↥orbit := hcard_eq.symm
    _ ≤ Module.finrank Fb Vb := hcard_le
    _ = Module.finrank F V := hfr

end CFSG.StandardType

end

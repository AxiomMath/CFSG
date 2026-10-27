module

public import CFSG.Monster.Code.Weights
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.Monster.Code

open Finset

private theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact .inl rfl
  · exact .inr rfl

private theorem zmod2_eq_one {c : ZMod 2} (h : c ≠ 0) : c = 1 := (zmod2_cases c).resolve_left h

private theorem val_add_of_imp : ∀ a b : ZMod 2, (a ≠ 0 → b ≠ 0) → (a + b).val = b.val - a.val := by
  decide

private theorem val_le_of_imp : ∀ a b : ZMod 2, (a ≠ 0 → b ≠ 0) → a.val ≤ b.val := by
  decide

theorem hammingNorm_add_of_supp_subset {e f : Fin 24 → ZMod 2} (h : ∀ i, e i ≠ 0 → f i ≠ 0) :
    hammingNorm (e + f) = hammingNorm f - hammingNorm e := by
  rw [hammingNorm_eq_sum_val, hammingNorm_eq_sum_val, hammingNorm_eq_sum_val,
    ← Finset.sum_tsub_distrib _ fun i _ => val_le_of_imp _ _ (h i)]
  exact Finset.sum_congr rfl fun i _ => val_add_of_imp _ _ (h i)

theorem eq_of_supp_subset_of_hammingNorm_le {e f : Fin 24 → ZMod 2}
    (h : ∀ i, e i ≠ 0 → f i ≠ 0) (hc : hammingNorm f ≤ hammingNorm e) : e = f := by
  have h0 : hammingNorm (e + f) = 0 := by
    rw [hammingNorm_add_of_supp_subset h]
    omega
  have h1 : e + f = 0 := hammingNorm_eq_zero.1 h0
  funext i
  have := congrFun h1 i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  rcases zmod2_cases (e i) with h2 | h2 <;> rcases zmod2_cases (f i) with h3 | h3 <;>
    rw [h2, h3] at this ⊢ <;> first | rfl | exact absurd this (by decide)

theorem mul_eq_zero_iff_supp {d z : Fin 24 → ZMod 2} : d * z = 0 ↔ ∀ i, z i ≠ 0 → d i = 0 := by
  constructor
  · intro h i hz
    have := congrFun h i
    simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_right hz
  · intro h
    funext i
    simp only [Pi.mul_apply, Pi.zero_apply]
    by_cases hz : z i = 0
    · rw [hz, mul_zero]
    · rw [h i hz, zero_mul]

theorem word_add_self (x : Fin 24 → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmod2_cases (x i) with h | h <;> rw [h] <;> rfl

theorem word_mul_self (d : Fin 24 → ZMod 2) : d * d = d := by
  funext i
  simp only [Pi.mul_apply]
  rcases zmod2_cases (d i) with h | h <;> rw [h] <;> rfl

variable {d : Fin 24 → ZMod 2}

theorem eq_zero_or_eq_of_supp_subset (hw : hammingNorm d = 8) {e : Fin 24 → ZMod 2} (he : e ∈ C)
    (hs : ∀ i, e i ≠ 0 → d i ≠ 0) : e = 0 ∨ e = d := by
  by_cases h0 : e = 0
  · exact .inl h0
  · refine .inr (eq_of_supp_subset_of_hammingNorm_le hs ?_)
    rw [hw]
    exact eight_le_wt he h0

@[expose] def CJc (d : Fin 24 → ZMod 2) : Submodule (ZMod 2) (Fin 24 → ZMod 2) where
  carrier := {a | a ∈ C ∧ ∀ i, a i ≠ 0 → d i = 0}
  add_mem' {a b} ha hb := ⟨C.add_mem ha.1 hb.1, fun i hi => by
    by_contra hd
    have h1 : a i = 0 := not_not.1 (mt (ha.2 i) hd)
    have h2 : b i = 0 := not_not.1 (mt (hb.2 i) hd)
    exact hi (by simp [h1, h2])⟩
  zero_mem' := ⟨C.zero_mem, fun _ hi => absurd rfl hi⟩
  smul_mem' c a ha := ⟨C.smul_mem c ha.1, fun i hi => ha.2 i fun h => hi (by simp [h])⟩

theorem mem_CJc {a : Fin 24 → ZMod 2} : a ∈ CJc d ↔ a ∈ C ∧ ∀ i, a i ≠ 0 → d i = 0 := Iff.rfl

theorem CJc_le_C : CJc d ≤ C := fun _ ha => ha.1

theorem Ω_add_mem_CJc (hd : d ∈ C) : Ω + d ∈ CJc d := by
  refine ⟨C.add_mem Ω_mem_C hd, fun i hi => ?_⟩
  by_contra h
  apply hi
  simp only [Pi.add_apply, Ω, zmod2_eq_one h]
  rfl

theorem Ω_add_apply_of_eq_zero {i : Fin 24} (hi : d i = 0) : (Ω + d) i = 1 := by
  simp [Ω, hi]

theorem hammingNorm_of_mem_CJc (hd : d ∈ C) (hw : hammingNorm d = 8) {a : Fin 24 → ZMod 2}
    (ha : a ∈ CJc d) (h0 : a ≠ 0) (hΩ : a ≠ Ω + d) : hammingNorm a = 8 := by
  have hsub : ∀ i, a i ≠ 0 → (Ω + d) i ≠ 0 := fun i hi => by
    rw [Ω_add_apply_of_eq_zero (ha.2 i hi)]
    exact one_ne_zero
  have hΩd : hammingNorm (Ω + d) = 16 := by
    have := hammingNorm_add_of_supp_subset (e := d) (f := Ω) fun i _ => by simp [Ω]
    rw [add_comm] at this
    rw [this, hw]
    rfl
  have hle : hammingNorm a ≤ 16 := by
    have := hammingNorm_add_of_supp_subset hsub
    by_contra hlt
    have h' : hammingNorm (Ω + d) ≤ hammingNorm a := by omega
    exact hΩ (eq_of_supp_subset_of_hammingNorm_le hsub h')
  have hmem := wt_mem ha.1
  have hne : hammingNorm a ≠ 0 := hammingNorm_ne_zero_iff.2 h0
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h
  · exact absurd h hne
  · exact h
  ·
    exfalso
    have hs := hammingNorm_add_of_supp_subset hsub
    rw [hΩd, h] at hs
    have hC : a + (Ω + d) ∈ C := C.add_mem ha.1 (C.add_mem Ω_mem_C hd)
    have hne' : a + (Ω + d) ≠ 0 := fun h' => by rw [h', hammingNorm_zero] at hs; omega
    have := eight_le_wt hC hne'
    omega
  · exact absurd (eq_of_supp_subset_of_hammingNorm_le hsub (by omega)) hΩ
  · omega

private def mulD (d : Fin 24 → ZMod 2) : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun x := d * x
  map_add' := mul_add d
  map_smul' c x := mul_smul_comm c d x

private theorem mulD_apply (x : Fin 24 → ZMod 2) : mulD d x = d * x := rfl

private theorem CJc_eq : CJc d = C ⊓ LinearMap.ker (mulD d) := by
  ext a
  rw [Submodule.mem_inf, LinearMap.mem_ker, mulD_apply, mul_eq_zero_iff_supp]
  rfl

private def kerEquiv (d : Fin 24 → ZMod 2) :
    LinearMap.ker (mulD d) ≃ₗ[ZMod 2] ({i // d i = 0} → ZMod 2) where
  toFun z i := (z : Fin 24 → ZMod 2) i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨fun j => if h : d j = 0 then y ⟨j, h⟩ else 0, by
    rw [LinearMap.mem_ker, mulD_apply, mul_eq_zero_iff_supp]
    intro i hi
    by_contra h
    exact hi (by simp [h])⟩
  left_inv z := by
    refine Subtype.ext (funext fun j => ?_)
    have hz := (mul_eq_zero_iff_supp.1 (LinearMap.mem_ker.1 z.2)) j
    by_cases h : d j = 0
    · simp only [h, dite_true]
    · simp only [h, dite_false]
      by_contra h'
      exact h (hz (Ne.symm h'))
  right_inv y := by
    funext i
    simp only [i.2, dite_true]

private theorem card_zero_coords (d : Fin 24 → ZMod 2) :
    Fintype.card {i // d i = 0} = 24 - hammingNorm d := by
  have h := Fintype.card_subtype_compl (fun i => d i ≠ 0)
  simp only [not_not, Fintype.card_fin] at h
  rw [h, Fintype.card_subtype]
  rfl

private theorem finrank_ker_mulD (d : Fin 24 → ZMod 2) :
    Module.finrank (ZMod 2) (LinearMap.ker (mulD d)) = 24 - hammingNorm d := by
  rw [(kerEquiv d).finrank_eq, Module.finrank_fintype_fun_eq_card, card_zero_coords]

private theorem comap_mulD_eq (hd : d ∈ C) (hw : hammingNorm d = 8) :
    C.comap (mulD d) = LinearMap.ker (mulD d) ⊔ Submodule.span (ZMod 2) {d} := by
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_comap, mulD_apply] at hz
    rcases eq_zero_or_eq_of_supp_subset hw hz (fun i hi => by
      intro h; apply hi; simp [h]) with h | h
    · exact Submodule.mem_sup_left (LinearMap.mem_ker.2 h)
    · have hz' : z - d ∈ LinearMap.ker (mulD d) := by
        rw [LinearMap.mem_ker, mulD_apply, mul_sub, h, word_mul_self, sub_self]
      rw [show z = (z - d) + d by abel]
      exact Submodule.add_mem_sup hz' (Submodule.mem_span_singleton_self d)
  · refine sup_le (fun z hz => ?_) ?_
    · rw [Submodule.mem_comap, LinearMap.mem_ker.1 hz]
      exact C.zero_mem
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap,
        mulD_apply, word_mul_self]
      exact hd

private theorem ne_zero_of_hammingNorm (hw : hammingNorm d = 8) : d ≠ 0 := by
  rintro rfl
  rw [hammingNorm_zero] at hw
  exact absurd hw (by decide)

private theorem finrank_comap_mulD (hd : d ∈ C) (hw : hammingNorm d = 8) :
    Module.finrank (ZMod 2) (C.comap (mulD d)) = 17 := by
  have hdisj : LinearMap.ker (mulD d) ⊓ Submodule.span (ZMod 2) {d} = ⊥ := by
    rw [eq_bot_iff]
    intro z ⟨hz, hz'⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz'
    rw [Submodule.mem_bot]
    rcases zmod2_cases c with rfl | rfl
    · exact zero_smul _ _
    · exfalso
      rw [SetLike.mem_coe, LinearMap.mem_ker, mulD_apply, one_smul, word_mul_self] at hz
      exact ne_zero_of_hammingNorm hw hz
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (mulD d))
    (Submodule.span (ZMod 2) {d})
  rw [hdisj, finrank_bot, finrank_span_singleton (ne_zero_of_hammingNorm hw),
    finrank_ker_mulD, hw] at h
  rw [comap_mulD_eq hd hw]
  omega

private theorem dotProductBilin_nondegenerate' :
    (dotProductBilin (ZMod 2) (ZMod 2) :
      LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2)).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · funext i
    have := hx (Pi.single i 1)
    simpa [dotProductBilin_apply_apply, dotProduct_single] using this
  · funext i
    have := hx (Pi.single i 1)
    simpa [dotProductBilin_apply_apply, single_dotProduct] using this

private theorem orthogonal_map_mulD :
    LinearMap.BilinForm.orthogonal (dotProductBilin (ZMod 2) (ZMod 2) :
      LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2)) (C.map (mulD d)) = C.comap (mulD d) := by
  ext z
  rw [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_comap, mulD_apply,
    mem_C_iff_forall_dotProduct]
  constructor
  · intro h x hx
    have := h (d * x) ⟨x, hx, rfl⟩
    rw [dotProductBilin_apply_apply] at this
    rw [← this]
    simp only [dotProduct, Pi.mul_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rintro h _ ⟨x, hx, rfl⟩
    rw [dotProductBilin_apply_apply, ← h x hx]
    simp only [dotProduct, mulD_apply, Pi.mul_apply]
    exact Finset.sum_congr rfl fun i _ => by ring

private theorem finrank_map_mulD (hd : d ∈ C) (hw : hammingNorm d = 8) :
    Module.finrank (ZMod 2) (C.map (mulD d)) = 7 := by
  have h := LinearMap.BilinForm.finrank_orthogonal dotProductBilin_nondegenerate'
    (C.map (mulD d))
  rw [orthogonal_map_mulD, finrank_comap_mulD hd hw, Module.finrank_fin_fun] at h
  have hle : Module.finrank (ZMod 2) (C.map (mulD d)) ≤ 24 := by
    have := Submodule.finrank_le (C.map (mulD d))
    rwa [Module.finrank_fin_fun] at this
  omega

theorem finrank_CJc (hd : d ∈ C) (hw : hammingNorm d = 8) :
    Module.finrank (ZMod 2) (CJc d) = 5 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((mulD d).domRestrict C)
  rw [LinearMap.range_domRestrict, finrank_map_mulD hd hw, finrank_C, LinearMap.ker_domRestrict]
    at h
  have e : Submodule.comap C.subtype (LinearMap.ker (mulD d)) =
      Submodule.comap C.subtype (CJc d) := by
    rw [CJc_eq, Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  rw [e, (Submodule.comapSubtypeEquivOfLe CJc_le_C).finrank_eq] at h
  omega

private def chi (t : ZMod 2) : ℤ := if t = 0 then 1 else -1

private theorem chi_add : ∀ a b : ZMod 2, chi (a + b) = chi a * chi b := by decide

private theorem sum_chi_dot : ∀ y : Fin 4 → ZMod 2,
    ∑ s : Fin 4 → ZMod 2, chi (s ⬝ᵥ y) = if y = 0 then 16 else 0 := by decide

private theorem chi_eq (t : ZMod 2) : chi t = 1 - 2 * (t.val : ℤ) := by
  revert t; decide

private theorem sum_chi (x : Fin 24 → ZMod 2) : ∑ i, chi (x i) = 24 - 2 * (hammingNorm x : ℤ) := by
  rw [hammingNorm_eq_sum_val]
  simp only [chi_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum]
  push_cast
  ring

private theorem bijective_of_sum_chi {S : Type*} [Fintype S] [DecidableEq S]
    (hS : Fintype.card S = 16) (lab : S → Fin 4 → ZMod 2)
    (h : ∀ s : Fin 4 → ZMod 2, s ≠ 0 → ∑ i, chi (s ⬝ᵥ lab i) = 0) : Function.Bijective lab := by
  have hT : ∀ s : Fin 4 → ZMod 2, ∑ i, chi (s ⬝ᵥ lab i) = if s = 0 then 16 else 0 := by
    intro s
    split_ifs with hs
    · subst hs
      simp [chi, hS]
    · exact h s hs
  have hN : ∀ x : Fin 4 → ZMod 2, (#{i | lab i = x} : ℤ) * 16 = 16 := by
    intro x
    have e1 : (#{i | lab i = x} : ℤ) * 16 = ∑ i, ∑ s : Fin 4 → ZMod 2, chi (s ⬝ᵥ (lab i + x)) := by
      rw [Finset.natCast_card_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_chi_dot]
      have : lab i + x = 0 ↔ lab i = x := by
        constructor
        · intro hx
          funext k
          have := congrFun hx k
          simp only [Pi.add_apply, Pi.zero_apply] at this
          rcases zmod2_cases (lab i k) with h1 | h1 <;> rcases zmod2_cases (x k) with h2 | h2 <;>
            rw [h1, h2] at this ⊢ <;> first | rfl | exact absurd this (by decide)
        · rintro rfl
          funext k
          simp only [Pi.add_apply, Pi.zero_apply]
          rcases zmod2_cases (lab i k) with h1 | h1 <;> rw [h1] <;> rfl
      by_cases hx : lab i = x
      · rw [ite_eq_left hx, ite_eq_left (this.2 hx), one_mul]
      · rw [ite_eq_right hx, ite_eq_right (mt this.1 hx), zero_mul]
    rw [e1]
    simp only [dotProduct_add, chi_add]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hT]
    rw [Finset.sum_eq_single 0 (fun s _ hs => by simp [hs]) (by simp)]
    simp [chi]
  have hN' : ∀ x : Fin 4 → ZMod 2, #{i | lab i = x} = 1 := by
    intro x
    have := hN x
    omega
  refine ⟨fun i j hij => ?_, fun x => ?_⟩
  · have hc := hN' (lab i)
    exact Finset.card_le_one.1 hc.le i (by simp) j (by simp [hij])
  · obtain ⟨i, hi⟩ := Finset.card_pos.1 (by rw [hN' x]; norm_num)
    exact ⟨i, (Finset.mem_filter.1 hi).2⟩

private theorem sum_smul_apply (c : Fin 4 → Fin 24 → ZMod 2) (s : Fin 4 → ZMod 2) (i : Fin 24) :
    (∑ k, s k • c k) i = s ⬝ᵥ fun k => c k i := by
  simp [Finset.sum_apply, dotProduct]

theorem span_cons_eq_CJc (hd : d ∈ C) (hw : hammingNorm d = 8) {c : Fin 4 → Fin 24 → ZMod 2}
    (hc : ∀ k, c k ∈ CJc d)
    (hli : LinearIndependent (ZMod 2) (Fin.cons (Ω + d) c : Fin 5 → Fin 24 → ZMod 2)) :
    Submodule.span (ZMod 2) (Set.range (Fin.cons (Ω + d) c : Fin 5 → Fin 24 → ZMod 2)) =
      CJc d := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa using Ω_add_mem_CJc hd
    · simpa using hc k
  · rw [finrank_span_eq_card hli, Fintype.card_fin, finrank_CJc hd hw]

theorem affine_of_linearIndependent (hd : d ∈ C) (hw : hammingNorm d = 8)
    {c : Fin 4 → Fin 24 → ZMod 2} (hc : ∀ k, c k ∈ CJc d)
    (hli : LinearIndependent (ZMod 2) (Fin.cons (Ω + d) c : Fin 5 → Fin 24 → ZMod 2)) :
    Function.Bijective (fun (i : {i // d i = 0}) (k : Fin 4) => c k i) ∧
    ∀ a : Fin 24 → ZMod 2, a ∈ CJc d ↔ (∀ i, a i ≠ 0 → d i = 0) ∧
      ∃ (c₀ : ZMod 2) (t : Fin 4 → ZMod 2), ∀ i : {i // d i = 0}, a i = c₀ + ∑ k, t k * c k i := by
  classical
  refine ⟨?_, fun a => ⟨fun ha => ?_, fun ⟨hs, c₀, t, ht⟩ => ?_⟩⟩
  ·
    refine bijective_of_sum_chi ?_ _ fun s hs => ?_
    · rw [card_zero_coords, hw]
    set w : Fin 24 → ZMod 2 := ∑ k, s k • c k with hwdef
    have hwK : w ∈ CJc d := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hc k)
    have hcomb : ∀ μ₀ : ZMod 2, μ₀ • (Ω + d) + w ≠ 0 := by
      intro μ₀ h0
      have := (Fintype.linearIndependent_iff.1 hli) (Fin.cons μ₀ s) (by
        rw [Fin.sum_univ_succ]
        simpa [hwdef] using h0)
      apply hs
      funext k
      simpa using this k.succ
    have hw0 : w ≠ 0 := by simpa using hcomb 0
    have hwΩ : w ≠ Ω + d := by
      intro h
      apply hcomb 1
      rw [h, one_smul, word_add_self]
    have hwt := hammingNorm_of_mem_CJc hd hw hwK hw0 hwΩ
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i => d i = 0) (fun i => chi (w i))
    have hoff : ∑ i : {i // ¬ d i = 0}, chi (w i) = 8 := by
      have : ∀ i : {i // ¬ d i = 0}, chi (w i) = 1 := by
        intro i
        have : w i = 0 := by
          by_contra h
          exact i.2 (hwK.2 i h)
        simp [this, chi]
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_const, Finset.card_univ]
      have h := Fintype.card_subtype (fun i => ¬ d i = 0)
      simp only [nsmul_eq_mul, mul_one]
      rw [h]
      have : #{i | ¬ d i = 0} = hammingNorm d := rfl
      rw [this, hw]
      rfl
    rw [sum_chi, hwt, hoff] at hsplit
    push_cast at hsplit
    have : ∑ i : {i // d i = 0}, chi (w i) = 0 := by linarith
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwdef, sum_smul_apply]
  ·
    refine ⟨ha.2, ?_⟩
    rw [← span_cons_eq_CJc hd hw hc hli, Submodule.mem_span_range_iff_exists_fun] at ha
    obtain ⟨μ, rfl⟩ := ha
    refine ⟨μ 0, fun k => μ k.succ, fun i => ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Ω_add_apply_of_eq_zero i.2, mul_one]
  ·
    have hmem : c₀ • (Ω + d) + ∑ k, t k • c k ∈ CJc d :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (Ω_add_mem_CJc hd))
        (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hc k))
    convert hmem using 1
    funext i
    by_cases hi : d i = 0
    · rw [ht ⟨i, hi⟩]
      simp [Finset.sum_apply, hi, Ω]
    · have h1 : a i = 0 := by
        by_contra h
        exact hi (hs i h)
      have h2 := mt (hmem.2 i) hi
      rw [h1, not_not.1 h2]

theorem octad_complement_affine_code (hd : d ∈ C) (hw : hammingNorm d = 8) :
    Module.finrank (ZMod 2) (CJc d) = 5 ∧
    (Ω + d ∈ CJc d ∧ ∀ i, d i = 0 → (Ω + d) i = 1) ∧
    (∀ a ∈ CJc d, a ≠ 0 → a ≠ Ω + d → hammingNorm a = 8) ∧
    ∀ b : Module.Basis (Fin 5) (ZMod 2) (CJc d), (b 0 : Fin 24 → ZMod 2) = Ω + d →
      Function.Bijective (fun (i : {i // d i = 0}) (k : Fin 4) => (b k.succ : Fin 24 → ZMod 2) i) ∧
      ∀ a : Fin 24 → ZMod 2, a ∈ CJc d ↔ (∀ i, a i ≠ 0 → d i = 0) ∧
        ∃ (c₀ : ZMod 2) (t : Fin 4 → ZMod 2), ∀ i : {i // d i = 0},
          a i = c₀ + ∑ k, t k * (b k.succ : Fin 24 → ZMod 2) i := by
  refine ⟨finrank_CJc hd hw, ⟨Ω_add_mem_CJc hd, fun i hi => Ω_add_apply_of_eq_zero hi⟩,
    fun a ha h0 hΩ => hammingNorm_of_mem_CJc hd hw ha h0 hΩ, fun b hb => ?_⟩
  have hcons : (Fin.cons (Ω + d) (fun k => (b k.succ : Fin 24 → ZMod 2)) :
      Fin 5 → Fin 24 → ZMod 2) = fun j => (b j : Fin 24 → ZMod 2) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [hb]
    · simp
  have hli : LinearIndependent (ZMod 2) (Fin.cons (Ω + d) (fun k => (b k.succ : Fin 24 → ZMod 2)) :
      Fin 5 → Fin 24 → ZMod 2) := by
    rw [hcons]
    exact b.linearIndependent.map' (CJc d).subtype (Submodule.ker_subtype _)
  exact affine_of_linearIndependent hd hw (fun k => (b k.succ).2) hli

end CFSG.Monster.Code

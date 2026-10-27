module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroF4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroF4Dual
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab

public section

namespace CFSG.StandardType

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}

private lemma ggCZsign_1mmm (k : Fin 4) :
    (![1, -1, -1, -1] : Fin 4 → ZMod p) k = 1 ∨
      (![1, -1, -1, -1] : Fin 4 → ZMod p) k = -1 := by
  fin_cases k <;> first | left; rfl | right; rfl

private lemma ggCZsum_1mmm_e :
    (∑ k, (![1, -1, -1, -1] : Fin 4 → ZMod p) k • e k) = e 0 - e 1 - e 2 - e 3 := by
  rw [Fin.sum_univ_four]
  have h0 : (![1, -1, -1, -1] : Fin 4 → ZMod p) 0 = 1 := rfl
  have h1 : (![1, -1, -1, -1] : Fin 4 → ZMod p) 1 = -1 := rfl
  have h2 : (![1, -1, -1, -1] : Fin 4 → ZMod p) 2 = -1 := rfl
  have h3 : (![1, -1, -1, -1] : Fin 4 → ZMod p) 3 = -1 := rfl
  have hneg (x : V) : (-1 : ZMod p) • x = -x := by
    have h := neg_smul (1 : ZMod p) x
    rwa [one_smul] at h
  rw [h0, h1, h2, h3, one_smul, hneg, hneg, hneg, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]

private lemma ggCZsum_1mmm_phi (v : V) :
    (∑ k, (![1, -1, -1, -1] : Fin 4 → ZMod p) k * φ k v) =
      φ 0 v - φ 1 v - φ 2 v - φ 3 v := by
  rw [Fin.sum_univ_four]
  have h0 : (![1, -1, -1, -1] : Fin 4 → ZMod p) 0 = 1 := rfl
  have h1 : (![1, -1, -1, -1] : Fin 4 → ZMod p) 1 = -1 := rfl
  have h2 : (![1, -1, -1, -1] : Fin 4 → ZMod p) 2 = -1 := rfl
  have h3 : (![1, -1, -1, -1] : Fin 4 → ZMod p) 3 = -1 := rfl
  have hneg (a : ZMod p) : (-1 : ZMod p) * a = -a := neg_one_mul a
  rw [h0, h1, h2, h3, one_mul, hneg, hneg, hneg, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]

theorem ggCZWF4_eq_closure (hp2 : p ≠ 2) (hd : GGCZDual e φ) :
    ggCZWF4 p e φ = Subgroup.closure (ggCZRD e φ ∪ ggCZS e φ ∪ ggCZH e φ) := by
  refine le_antisymm ?_ ((Subgroup.closure_le (K := ggCZWF4 p e φ)).mpr
    (ggCZ_subset_ggCZWF4 hp2 hd))
  rw [ggCZWF4, Subgroup.closure_le]
  rintro r ⟨i, hi⟩
  fin_cases i <;> simp only [GGCZGensF4] at hi
  · refine Subgroup.subset_closure (Or.inl (Or.inl ⟨1, 2, by decide, 1, Or.inl rfl, ?_⟩))
    intro v
    rw [hi v]
    simp
  · refine Subgroup.subset_closure (Or.inl (Or.inl ⟨2, 3, by decide, 1, Or.inl rfl, ?_⟩))
    intro v
    rw [hi v]
    simp
  · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨3, hi⟩))
  · exact Subgroup.subset_closure (Or.inr ⟨![1, -1, -1, -1], ggCZsign_1mmm, fun v => by
      rw [hi v, ggCZsum_1mmm_phi v, ggCZsum_1mmm_e]⟩)

private lemma ggCZGensF4_conj (g : V ≃ₗ[ZMod p] V) {r : V ≃ₗ[ZMod p] V} {i : Fin 4}
    (hr : GGCZGensF4 e φ i r) :
    GGCZGensF4 (fun j => g.symm (e j)) (fun j => (φ j).comp (g : V →ₗ[ZMod p] V)) i
      (MulAut.conj g⁻¹ r) := by
  fin_cases i <;> simp only [GGCZGensF4] at hr ⊢ <;> intro v <;>
    rw [MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, inv_inv, hr (g v)] <;>
    simp [LinearMap.comp_apply]

private lemma ggCZGensF4_conj_inv (g : V ≃ₗ[ZMod p] V) {r : V ≃ₗ[ZMod p] V} {i : Fin 4}
    (hr : GGCZGensF4 (fun j => g.symm (e j)) (fun j => (φ j).comp (g : V →ₗ[ZMod p] V)) i r) :
    GGCZGensF4 e φ i (MulAut.conj g r) := by
  fin_cases i <;> simp only [GGCZGensF4] at hr ⊢ <;> intro v <;>
    rw [MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hr (g⁻¹ v)] <;>
    simp [LinearMap.comp_apply]

theorem ggCZWF4_coords_transport (hd : GGCZDual e φ) {g : V ≃ₗ[ZMod p] V}
    (hg : g ∈ ggCZWF4 p e φ) :
    GGCZDual (fun i => g.symm (e i)) (fun i => (φ i).comp (g : V →ₗ[ZMod p] V)) ∧
      ggCZWF4 p (fun i => g.symm (e i)) (fun i => (φ i).comp (g : V →ₗ[ZMod p] V)) =
        ggCZWF4 p e φ := by
  have hdual : GGCZDual (fun i => g.symm (e i)) (fun i => (φ i).comp (g : V →ₗ[ZMod p] V)) := by
    intro i j
    change φ i (g (g.symm (e j))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hd i j
  refine ⟨hdual, ?_⟩
  have hgen : {r' | ∃ i, GGCZGensF4 (fun j => g.symm (e j))
      (fun j => (φ j).comp (g : V →ₗ[ZMod p] V)) i r'} =
      (MulAut.conj g⁻¹) '' {r | ∃ i, GGCZGensF4 e φ i r} := by
    ext r'
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨MulAut.conj g r', ⟨i, ggCZGensF4_conj_inv g hi⟩, ?_⟩
      simp only [MulAut.conj_apply]
      group
    · rintro ⟨r, ⟨i, hi⟩, rfl⟩
      exact ⟨i, ggCZGensF4_conj g hi⟩
  have hconj : (ggCZWF4 p e φ).map (MulAut.conj g⁻¹).toMonoidHom = ggCZWF4 p e φ := by
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp
      (Subgroup.le_normalizer ((ggCZWF4 p e φ).inv_mem hg))
  rw [ggCZWF4, ggCZWF4, hgen]
  rw [show Subgroup.closure ((MulAut.conj g⁻¹) '' {r | ∃ i, GGCZGensF4 e φ i r}) =
      Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
        (Subgroup.closure {r | ∃ i, GGCZGensF4 e φ i r}) from by
    rw [MonoidHom.map_closure]; rfl]
  exact hconj

private theorem ggCZ_exists_coords_sgn_three_short [Finite V] (hp2 : p ≠ 2) (hd : GGCZDual e φ)
    {T : V ≃ₗ[ZMod p] V} (hT : T ∈ ggCZS e φ ∪ ggCZH e φ) :
    ∃ (e' : Fin 4 → V) (φ' : Fin 4 → Module.Dual (ZMod p) V), GGCZDual e' φ' ∧
      ggCZWF4 p e' φ' = ggCZWF4 p e φ ∧ ∀ v, T v = v - (2 * φ' 3 v) • e' 3 := by
  let r' : V ≃ₗ[ZMod p] V := Module.reflection (f := 2 • φ 3) (x := e 3) (by
    rw [LinearMap.smul_apply, hd 3 3]
    norm_num)
  have hr' : r' ∈ ggCZS e φ ∪ ggCZH e φ := by
    refine Or.inl ⟨3, fun v => ?_⟩
    rw [Module.reflection_apply]
    simp [LinearMap.smul_apply]
  obtain ⟨g, hgW, hgconj⟩ := ggCZWF4_conj_short hp2 hd hT hr'
  obtain ⟨hd', hW'⟩ := ggCZWF4_coords_transport hd hgW
  refine ⟨fun i => g.symm (e i), fun i => (φ i).comp (g : V →ₗ[ZMod p] V), hd', hW', fun v => ?_⟩
  have hgT : T = g.symm * r' * g := by
    rw [← hgconj]
    ext w
    simp [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]
  rw [hgT]
  simp only [LinearEquiv.mul_apply]
  rw [Module.reflection_apply]
  simp [LinearMap.smul_apply]

theorem ggCZ_exists_coords_sgn_three [Finite V] (hp2 : p ≠ 2) (hd : GGCZDual e φ)
    {T : V ≃ₗ[ZMod p] V} (hT : T ∈ ggCZWF4 p e φ) (hr : GGLinRefl T) :
    ∃ (e' : Fin 4 → V) (φ' : Fin 4 → Module.Dual (ZMod p) V), GGCZDual e' φ' ∧
      ggCZWF4 p e' φ' = ggCZWF4 p e φ ∧ ∀ v, T v = v - (2 * φ' 3 v) • e' 3 := by
  rcases ggCZWF4_refl hp2 hd hT hr with (hRD | hS) | hH
  ·
    obtain ⟨e'', φ'', hd'', -, hRD'', hSH''⟩ := ggCZ_F4_dual hp2 hd
    have hW : ggCZWF4 p e'' φ'' = ggCZWF4 p e φ := by
      rw [ggCZWF4_eq_closure hp2 hd, ggCZWF4_eq_closure hp2 hd'']
      congr 1
      rw [Set.union_assoc, hSH'', hRD'']
      ext x
      simp only [Set.mem_union]
      tauto
    obtain ⟨e', φ', hd', hW', hT'⟩ :=
      ggCZ_exists_coords_sgn_three_short hp2 hd'' (by rw [hSH'']; exact hRD)
    exact ⟨e', φ', hd', hW'.trans hW, hT'⟩
  · exact ggCZ_exists_coords_sgn_three_short hp2 hd (Or.inl hS)
  · exact ggCZ_exists_coords_sgn_three_short hp2 hd (Or.inr hH)

private lemma ggCZAdapt_repr_eq_phi {b : Module.Basis (Fin 4) (ZMod p) V} (hd : GGCZDual e φ)
    (hb : ∀ i, b i = e i) (i : Fin 4) (v : V) : b.repr v i = φ i v := by
  have hcoord : b.coord i = φ i := by
    refine Module.Basis.ext b fun j => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hb j, hd i j]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  rw [← Module.Basis.coord_apply, hcoord]

theorem GGCZDual.exists_basis (hd : GGCZDual e φ) (h4 : Module.finrank (ZMod p) V = 4) :
    ∃ b : Module.Basis (Fin 4) (ZMod p) V, (∀ i, b i = e i) ∧ ∀ i v, b.repr v i = φ i v := by
  have hlin : LinearIndependent (ZMod p) e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (φ i) hg
    simp only [map_sum, map_smul, smul_eq_mul, map_zero, hd i, mul_ite, mul_one, mul_zero] at h
    rwa [Fintype.sum_ite_eq] at h
  have hcard : Fintype.card (Fin 4) = Module.finrank (ZMod p) V := by
    rw [h4]
    simp
  have hb : ∀ i, basisOfLinearIndependentOfCardEqFinrank hlin hcard i = e i :=
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin hcard) i
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hlin hcard, hb,
    fun i v => ggCZAdapt_repr_eq_phi hd hb i v⟩

variable {b : Module.Basis (Fin 4) (ZMod p) V}

private lemma permMap_swap_apply (hd : GGCZDual e φ) (hb : ∀ i, b i = e i)
    {i j : Fin 4} (hij : i ≠ j) (v : V) :
    ZS.permMap p b (Equiv.swap i j) v = v - (φ i v - φ j v) • (e i - e j) := by
  have hL : (ZS.permMap p b (Equiv.swap i j) : V →ₗ[ZMod p] V) =
      LinearMap.id - (LinearMap.smulRight (φ i) (e i - e j) -
        LinearMap.smulRight (φ j) (e i - e j)) := by
    have hbasic : ∀ k, (ZS.permMap p b (Equiv.swap i j) : V →ₗ[ZMod p] V) (b k) =
        b (Equiv.swap i j k) := by
      intro k
      change ZS.permMap p b (Equiv.swap i j) (b k) = b (Equiv.swap i j k)
      rw [ZS.permMap_apply_basis]
    refine Module.Basis.ext b fun k => ?_
    rw [hbasic k]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, hb]
    by_cases hki : k = i
    · rw [hki, Equiv.swap_apply_left]
      simp only [hd i i, hd j i, if_neg (Ne.symm hij), if_true, one_smul]
      module
    · by_cases hkj : k = j
      · rw [hkj, Equiv.swap_apply_right]
        simp only [hd i j, hd j j, if_neg hij, if_true, one_smul]
        module
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
        simp only [hd i k, hd j k, if_neg (Ne.symm hki), if_neg (Ne.symm hkj), sub_self,
          zero_smul, sub_zero]
  change (ZS.permMap p b (Equiv.swap i j) : V →ₗ[ZMod p] V) v = _
  rw [hL]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
  rw [← sub_smul]

private lemma permMap_swap_mem (hp2 : p ≠ 2) (hd : GGCZDual e φ) (hb : ∀ i, b i = e i)
    {i j : Fin 4} (hij : i ≠ j) : ZS.permMap p b (Equiv.swap i j) ∈ ggCZWF4 p e φ := by
  refine ggCZ_subset_ggCZWF4 hp2 hd ?_
  refine Or.inl (Or.inl ⟨i, j, hij, 1, Or.inl rfl, ?_⟩)
  intro v
  rw [permMap_swap_apply hd hb hij v]
  simp

theorem ggCZWF4_permMap_mem (hp2 : p ≠ 2) (hd : GGCZDual e φ) (hb : ∀ i, b i = e i)
    (σ : Equiv.Perm (Fin 4)) : ZS.permMap p b σ ∈ ggCZWF4 p e φ := by
  refine Equiv.Perm.swap_induction_on
    (motive := fun σ => ZS.permMap p b σ ∈ ggCZWF4 p e φ) σ ?_ ?_
  · rw [ZS.permMap_one]
    exact Subgroup.one_mem _
  · intro f x y hxy hf
    rw [← ZS.permMap_mul]
    exact Subgroup.mul_mem _ (permMap_swap_mem hp2 hd hb hxy) hf

private lemma diagMap_sgn_apply (hd : GGCZDual e φ) (hb : ∀ i, b i = e i) (i : Fin 4) (v : V) :
    ZS.diagMap p b (fun j => if j = i then -1 else 1) v = v - (2 * φ i v) • e i := by
  have hL : (ZS.diagMap p b (fun j => if j = i then -1 else 1) : V →ₗ[ZMod p] V) =
      LinearMap.id - LinearMap.smulRight ((2 : ZMod p) • φ i) (e i) := by
    have hbasic : ∀ k, (ZS.diagMap p b (fun j => if j = i then -1 else 1) :
        V →ₗ[ZMod p] V) (b k) = ((if k = i then -1 else 1 : (ZMod p)ˣ) : ZMod p) • b k := by
      intro k
      change ZS.diagMap p b (fun j => if j = i then -1 else 1) (b k) = _
      rw [ZS.diagMap_apply_basis]
    refine Module.Basis.ext b fun k => ?_
    rw [hbasic k]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, smul_eq_mul, hb]
    by_cases hki : k = i
    · rw [hki]
      simp only [hd i i, if_true, mul_one, Units.val_neg, Units.val_one]
      module
    · rw [if_neg hki]
      simp only [hd i k, if_neg (Ne.symm hki), mul_zero, zero_smul, sub_zero,
        Units.val_one, one_smul]
  change (ZS.diagMap p b (fun j => if j = i then -1 else 1) : V →ₗ[ZMod p] V) v = _
  rw [hL]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, smul_eq_mul]

theorem ggCZWF4_sgnMap_mem (hp2 : p ≠ 2) (hd : GGCZDual e φ) (hb : ∀ i, b i = e i)
    (i : Fin 4) : ZS.diagMap p b (fun j => if j = i then -1 else 1) ∈ ggCZWF4 p e φ := by
  refine ggCZ_subset_ggCZWF4 hp2 hd (Or.inl (Or.inr ⟨i, ?_⟩))
  exact diagMap_sgn_apply hd hb i

private def ggCZHalfW : Fin 4 → ZMod p
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => -1

private noncomputable def ggCZHalfVec (e : Fin 4 → V) : V := ∑ k, ggCZHalfW (p := p) k • e k

private noncomputable def ggCZHalfForm (φ : Fin 4 → Module.Dual (ZMod p) V) :
    Module.Dual (ZMod p) V := (2 : ZMod p)⁻¹ • ∑ k, ggCZHalfW (p := p) k • φ k

private lemma ggCZHalfForm_apply (φ : Fin 4 → Module.Dual (ZMod p) V) (v : V) :
    ggCZHalfForm (p := p) φ v =
      (2 : ZMod p)⁻¹ * ∑ k, ggCZHalfW (p := p) k * φ k v := by
  simp only [ggCZHalfForm, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    Finset.mul_sum]

private lemma ggCZHalfVec_phi (hd : GGCZDual e φ) (k : Fin 4) :
    φ k (ggCZHalfVec (p := p) e) = ggCZHalfW (p := p) k := by
  have h1 : ∀ j, ggCZHalfW (p := p) j * φ k (e j) =
      if k = j then ggCZHalfW (p := p) j else 0 := by
    intro j
    rw [hd k j]
    split_ifs <;> simp
  simp only [ggCZHalfVec, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => h1 j, Fintype.sum_ite_eq]

private lemma ggCZHalfForm_pairing (hp2 : p ≠ 2) (hd : GGCZDual e φ) :
    ggCZHalfForm (p := p) φ (ggCZHalfVec (p := p) e) = 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hw2 : ∀ k, ggCZHalfW (p := p) k * ggCZHalfW (p := p) k = 1 := by
    intro k
    fin_cases k <;> simp [ggCZHalfW]
  have hsum : (∑ k : Fin 4, ggCZHalfW (p := p) k * φ k (ggCZHalfVec (p := p) e)) = 4 := by
    simp only [ggCZHalfVec_phi hd, hw2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    norm_num
  rw [ggCZHalfForm_apply, hsum]
  rw [show (4 : ZMod p) = 2 * 2 by ring, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]

private noncomputable def ggCZHalfRefl (hp2 : p ≠ 2) (hd : GGCZDual e φ) :
    V ≃ₗ[ZMod p] V :=
  Module.reflection (ggCZHalfForm_pairing hp2 hd)

private lemma ggCZHalfRefl_mem (hp2 : p ≠ 2) (hd : GGCZDual e φ) :
    ggCZHalfRefl hp2 hd ∈ ggCZWF4 p e φ := by
  refine ggCZ_subset_ggCZWF4 hp2 hd (Or.inr ⟨ggCZHalfW, ?_, ?_⟩)
  · intro k
    fin_cases k <;> first | left; rfl | right; rfl
  · intro v
    change Module.reflection (ggCZHalfForm_pairing hp2 hd) v =
      v - ((2 : ZMod p)⁻¹ * ∑ k, ggCZHalfW (p := p) k * φ k v) •
        ggCZHalfVec (p := p) e
    rw [Module.reflection_apply, ggCZHalfForm_apply]

private lemma ggCZHalfForm_e_one (hd : GGCZDual e φ) :
    ggCZHalfForm (p := p) φ (e 1) = -((2 : ZMod p)⁻¹) := by
  rw [ggCZHalfForm_apply, Finset.sum_eq_single 1]
  · simp only [hd 1 1, ggCZHalfW, if_true, mul_neg, mul_one]
  · intro k _ hk
    simp [hd k 1, hk]
  · intro h
    exact absurd (Finset.mem_univ 1) h

private lemma ggCZHalfRefl_e_one (hp2 : p ≠ 2) (hd : GGCZDual e φ) (hb : ∀ i, b i = e i) :
    ggCZHalfRefl hp2 hd (b 1) =
      e 1 - ((2 : ZMod p)⁻¹ * ggCZHalfW (p := p) 1) • ggCZHalfVec (p := p) e := by
  change Module.reflection (ggCZHalfForm_pairing hp2 hd) (b 1) = _
  rw [Module.reflection_apply, hb 1, ggCZHalfForm_e_one hd]
  rw [show (2 : ZMod p)⁻¹ * ggCZHalfW (p := p) 1 = -((2 : ZMod p)⁻¹) by
    simp only [ggCZHalfW, mul_neg, mul_one]]

private lemma ggCZHalfRefl_phi_e_one (hp2 : p ≠ 2) (hd : GGCZDual e φ) (hb : ∀ i, b i = e i)
    (k : Fin 4) :
    φ k (ggCZHalfRefl hp2 hd (b 1)) =
      (if k = 1 then 1 else 0) + (2 : ZMod p)⁻¹ * ggCZHalfW (p := p) k := by
  rw [ggCZHalfRefl_e_one hp2 hd hb, map_sub, map_smul, ggCZHalfVec_phi hd, hd k 1,
    show ggCZHalfW (p := p) 1 = -1 by simp [ggCZHalfW]]
  ring_nf

private lemma ggCZHalfRefl_phi_e_one_ne (hp2 : p ≠ 2) (hd : GGCZDual e φ)
    (hb : ∀ i, b i = e i) (k : Fin 4) :
    φ k (ggCZHalfRefl hp2 hd (b 1)) ≠ 0 := by
  rw [ggCZHalfRefl_phi_e_one hp2 hd hb k]
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hinv : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2
  have hmul : (2 : ZMod p)⁻¹ * -1 = -2⁻¹ := by rw [mul_neg, mul_one]
  have h1m : (1 : ZMod p) - 2⁻¹ = 2⁻¹ := by
    have h : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    rw [← h]
    ring
  have h1 : (1 : ZMod p) + -2⁻¹ = 2⁻¹ := by
    rw [← sub_eq_add_neg]
    exact h1m
  have h0 : (0 : ZMod p) + 2⁻¹ * -1 = -2⁻¹ := by rw [zero_add, hmul]
  fin_cases k
  · simpa [ggCZHalfW] using hinv
  · simpa [ggCZHalfW, h1] using hinv
  · simpa [ggCZHalfW, h0] using neg_ne_zero.mpr hinv
  · simpa [ggCZHalfW, h0] using neg_ne_zero.mpr hinv

theorem ggCZWF4_exists_not_monomial (hp2 : p ≠ 2) (hd : GGCZDual e φ) (hb : ∀ i, b i = e i) :
    ∃ r ∈ ggCZWF4 p e φ, ¬ ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, r (b i) = c i • b (σ i) := by
  classical
  refine ⟨ggCZHalfRefl hp2 hd, ggCZHalfRefl_mem hp2 hd, ?_⟩
  rintro ⟨σ, c, hc, hmon⟩
  have hrepr : ∀ k, b.repr (ggCZHalfRefl hp2 hd (b 1)) k = if σ 1 = k then c 1 else 0 := by
    intro k
    rw [hmon 1, map_smul, Module.Basis.repr_self]
    by_cases hk : σ 1 = k
    · subst hk
      simp
    · simp [hk]
  have hnz : ∀ k, b.repr (ggCZHalfRefl hp2 hd (b 1)) k ≠ 0 := by
    intro k
    rw [ggCZAdapt_repr_eq_phi hd hb k]
    exact ggCZHalfRefl_phi_e_one_ne hp2 hd hb k
  let k : Fin 4 := if σ 1 = 0 then 1 else 0
  have hkne : k ≠ σ 1 := by
    dsimp [k]
    split_ifs with h
    · rw [h]
      decide
    · exact fun hk => h hk.symm
  have hzero : b.repr (ggCZHalfRefl hp2 hd (b 1)) k = 0 := by
    rw [hrepr k, if_neg (Ne.symm hkne)]
  exact hnz k hzero

private def ggCZSignVec (i : Fin 4) : Fin 4 → (ZMod p)ˣ :=
  fun k => if k = i then -1 else 1

private noncomputable def ggCZB3 (b : Module.Basis (Fin 4) (ZMod p) V) :
    Subgroup (V ≃ₗ[ZMod p] V) :=
  Subgroup.closure {ZS.permMap p b (Equiv.swap 0 1), ZS.permMap p b (Equiv.swap 1 2),
    ZS.diagMap p b (ggCZSignVec 2)}

private lemma ggCZB3_perm01 : ZS.permMap p b (Equiv.swap 0 1) ∈ ggCZB3 (p := p) b :=
  Subgroup.subset_closure (by simp)

private lemma ggCZB3_perm12 : ZS.permMap p b (Equiv.swap 1 2) ∈ ggCZB3 (p := p) b :=
  Subgroup.subset_closure (by simp)

private lemma ggCZB3_sgn2 : ZS.diagMap p b (ggCZSignVec 2) ∈ ggCZB3 (p := p) b :=
  Subgroup.subset_closure (by simp)

private lemma ggCZB3_perm02 : ZS.permMap p b (Equiv.swap 0 2) ∈ ggCZB3 (p := p) b := by
  have hswap : Equiv.swap (0 : Fin 4) 2 = Equiv.swap 1 2 * Equiv.swap 0 1 * Equiv.swap 1 2 := by
    ext k
    fin_cases k <;> decide
  rw [hswap, ← ZS.permMap_mul, ← ZS.permMap_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ggCZB3_perm12 ggCZB3_perm01) ggCZB3_perm12

private lemma phi_weight_sum (hd : GGCZDual e φ) (w : Fin 4 → ZMod p) (k : Fin 4) :
    φ k (∑ j, w j • e j) = w k := by
  have h1 : ∀ j, w j * φ k (e j) = if k = j then w j else 0 := by
    intro j
    rw [hd k j]
    split_ifs <;> simp
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => h1 j, Fintype.sum_ite_eq]

private lemma sum_weight_phi_e (hd : GGCZDual e φ) (w : Fin 4 → ZMod p) (k : Fin 4) :
    (∑ j, w j * φ j (e k)) = w k := by
  have h1 : ∀ j, w j * φ j (e k) = if j = k then w j else 0 := by
    intro j
    rw [hd j k]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  rw [Finset.sum_ite_eq']
  simp

private lemma ggCZB3_perm_swap {i j : Fin 4} (hij : i ≠ j) (hi : i ≠ 3) (hj : j ≠ 3) :
    ZS.permMap p b (Equiv.swap i j) ∈ ggCZB3 (p := p) b := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i <;> simp_all
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
    fin_cases j <;> simp_all
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
  · exact absurd rfl hij
  · exact ggCZB3_perm01
  · exact ggCZB3_perm02
  · rw [Equiv.swap_comm]; exact ggCZB3_perm01
  · exact absurd rfl hij
  · exact ggCZB3_perm12
  · rw [Equiv.swap_comm]; exact ggCZB3_perm02
  · rw [Equiv.swap_comm]; exact ggCZB3_perm12
  · exact absurd rfl hij

private lemma ggCZB3_perm_i2 {i : Fin 4} (hi : i ≠ 3) :
    ZS.permMap p b (Equiv.swap i 2) ∈ ggCZB3 (p := p) b := by
  by_cases hi2 : i = 2
  · subst hi2
    rw [Equiv.swap_self]
    change ZS.permMap p b (1 : Equiv.Perm (Fin 4)) ∈ ggCZB3 (p := p) b
    rw [ZS.permMap_one]
    exact Subgroup.one_mem _
  · exact ggCZB3_perm_swap hi2 hi (by decide : (2 : Fin 4) ≠ 3)

private lemma ggCZB3_sgn {i : Fin 4} (hi : i ≠ 3) :
    ZS.diagMap p b (ggCZSignVec i) ∈ ggCZB3 (p := p) b := by
  have hσ : ZS.permMap p b (Equiv.swap i 2) ∈ ggCZB3 (p := p) b := ggCZB3_perm_i2 hi
  have hconj : ZS.permMap p b (Equiv.swap i 2) * ZS.diagMap p b (ggCZSignVec 2) *
      (ZS.permMap p b (Equiv.swap i 2))⁻¹ ∈ ggCZB3 (p := p) b :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ ggCZB3_sgn2) (Subgroup.inv_mem _ hσ)
  have hd : ggCZSignVec (p := p) 2 ∘ (Equiv.swap i 2).symm = ggCZSignVec (p := p) i := by
    funext k
    simp only [Function.comp_apply, ggCZSignVec]
    by_cases hk : k = i
    · subst hk
      simp
    · have h : (Equiv.swap i 2) k ≠ 2 := by
        intro h
        have h' : k = i := by
          have := congrArg (Equiv.swap i 2) h
          simpa using this
        exact hk h'
      simp [hk, h]
  rw [ZS.permMap_mul_diagMap_mul_inv, hd] at hconj
  exact hconj

private lemma ggCZB3_signed_swap (hp2 : p ≠ 2) {i j : Fin 4} {ε : ZMod p} (hij : i ≠ j)
    (hε : ε = 1 ∨ ε = -1) (hi : i ≠ 3) (hj : j ≠ 3) :
    ZS.diagMap p b (fun k => if k = i ∨ k = j then (if ε = 1 then 1 else -1) else 1) *
      ZS.permMap p b (Equiv.swap i j) ∈ ggCZB3 (p := p) b := by
  have hperm : ZS.permMap p b (Equiv.swap i j) ∈ ggCZB3 (p := p) b :=
    ggCZB3_perm_swap hij hi hj
  rcases hε with rfl | rfl
  · have hd : (fun k => if k = i ∨ k = j then
        (if (1 : ZMod p) = 1 then (1 : (ZMod p)ˣ) else -1) else 1) =
        (1 : Fin 4 → (ZMod p)ˣ) := by
      funext k
      simp
    rw [hd, ZS.diagMap_one, one_mul]
    exact hperm
  · have : Fact (2 < p) := ⟨(Fact.out : p.Prime).two_le.lt_of_ne' hp2⟩
    have hneg : (-1 : ZMod p) ≠ 1 := ZMod.neg_one_ne_one
    have hd : ZS.diagMap p b (fun k => if k = i ∨ k = j then (-1 : (ZMod p)ˣ) else 1) =
        ZS.diagMap p b (ggCZSignVec i) * ZS.diagMap p b (ggCZSignVec j) := by
      rw [ZS.diagMap_mul]
      congr 1
      funext k
      simp only [Pi.mul_apply, ggCZSignVec]
      by_cases hki : k = i
      · rw [hki]
        simp [hij]
      · by_cases hkj : k = j
        · rw [hkj]
          simp [Ne.symm hij]
        · simp [hki, hkj]
    simp only [if_neg hneg]
    rw [hd]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ggCZB3_sgn hi) (ggCZB3_sgn hj)) hperm

private lemma RD_indices_ne_three (hd : GGCZDual e φ) (hb : ∀ i, b i = e i)
    {i j : Fin 4} {ε : ZMod p} (hij : i ≠ j) (hε : ε = 1 ∨ ε = -1)
    {r : V ≃ₗ[ZMod p] V}
    (hrw : ∀ v, r v = v - (φ i v - ε * φ j v) • (e i - ε • e j))
    (hfix : r (b 3) = b 3) : i ≠ 3 ∧ j ≠ 3 := by
  have hcoord : φ 3 (r (b 3)) = 1 := by
    rw [hfix, hb 3, hd 3 3, if_pos rfl]
  constructor
  · intro hi
    subst hi
    have hzero : φ 3 (r (b 3)) = 0 := by
      simp only [hb 3, hrw (e 3), map_sub, map_smul, hd 3 3, hd 3 j, if_neg hij,
        hd j 3, if_neg (Ne.symm hij), if_true]
      ring
    rw [hzero] at hcoord
    exact one_ne_zero hcoord.symm
  · intro hj
    subst hj
    have hzero : φ 3 (r (b 3)) = 0 := by
      simp only [hb 3, hrw (e 3), map_sub, map_smul, hd 3 3, hd 3 i,
        if_neg (Ne.symm hij), hd i 3, if_neg hij, if_true]
      rcases hε with rfl | rfl <;> ring
    rw [hzero] at hcoord
    exact one_ne_zero hcoord.symm

private lemma ggCZB3_of_S (hp2 : p ≠ 2) (hd : GGCZDual e φ) (hb : ∀ i, b i = e i)
    {r : V ≃ₗ[ZMod p] V} {i : Fin 4}
    (hrw : ∀ v, r v = v - (2 * φ i v) • e i) (hfix : r (b 3) = b 3) :
    r ∈ ggCZB3 (p := p) b := by
  have hi3 : i ≠ 3 := by
    intro hi
    subst hi
    have hcoord : φ 3 (r (b 3)) = 1 := by
      rw [hfix, hb 3, hd 3 3, if_pos rfl]
    have hzero : φ 3 (r (b 3)) = -1 := by
      simp only [hb 3, hrw (e 3), map_sub, map_smul, hd 3 3]
      norm_num
    rw [hzero] at hcoord
    have : Fact (2 < p) := ⟨(Fact.out : p.Prime).two_le.lt_of_ne' hp2⟩
    exact ZMod.neg_one_ne_one hcoord
  have hr_eq : r = ZS.diagMap p b (ggCZSignVec i) := by
    refine b.ext' fun k => ?_
    rw [ZS.diagMap_apply_basis]
    rw [hb k, hrw (e k)]
    by_cases hki : k = i
    · rw [hki]
      simp only [hd i i, ggCZSignVec, if_true]
      module
    · rw [hd i k, if_neg (Ne.symm hki)]
      simp [ggCZSignVec, hki]
  rw [hr_eq]
  exact ggCZB3_sgn hi3

private lemma ggCZB3_of_RD (hp2 : p ≠ 2) (hd : GGCZDual e φ) (hb : ∀ i, b i = e i)
    {i j : Fin 4} {ε : ZMod p} (hij : i ≠ j) (hε : ε = 1 ∨ ε = -1)
    {r : V ≃ₗ[ZMod p] V}
    (hrw : ∀ v, r v = v - (φ i v - ε * φ j v) • (e i - ε • e j))
    (hfix : r (b 3) = b 3) :
    r ∈ ggCZB3 (p := p) b := by
  obtain ⟨hi3, hj3⟩ := RD_indices_ne_three hd hb hij hε hrw hfix
  have : Fact (2 < p) := ⟨(Fact.out : p.Prime).two_le.lt_of_ne' hp2⟩
  have hneg : (-1 : ZMod p) ≠ 1 := ZMod.neg_one_ne_one
  have hr_eq : r = ZS.diagMap p b
      (fun k => if k = i ∨ k = j then (if ε = 1 then 1 else -1) else 1) *
      ZS.permMap p b (Equiv.swap i j) := by
    refine b.ext' fun k => ?_
    rw [LinearEquiv.mul_apply, ZS.permMap_apply_basis, ZS.diagMap_apply_basis]
    simp only [hb]
    rw [hrw (e k)]
    by_cases hki : k = i
    · rw [hki, Equiv.swap_apply_left]
      simp only [hd i i, hd j i, if_neg (Ne.symm hij)]
      rcases hε with rfl | rfl <;> simp [hneg]
    · by_cases hkj : k = j
      · rw [hkj, Equiv.swap_apply_right]
        simp only [hd i j, hd j j, if_neg hij]
        rcases hε with rfl | rfl <;> simp [hneg]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, hd i k, hd j k,
          if_neg (Ne.symm hki), if_neg (Ne.symm hkj)]
        simp [hki, hkj]
  rw [hr_eq]
  exact ggCZB3_signed_swap hp2 hij hε hi3 hj3

private lemma ggCZ_not_H (hp2 : p ≠ 2) (hd : GGCZDual e φ) (hb : ∀ i, b i = e i)
    {w : Fin 4 → ZMod p} (hw : ∀ k, w k = 1 ∨ w k = -1) {r : V ≃ₗ[ZMod p] V}
    (hrw : ∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k, w k * φ k v) • ∑ k, w k • e k)
    (hfix : r (b 3) = b 3) : False := by
  have hw3 : w 3 * w 3 = 1 := by
    rcases hw 3 with h | h <;> rw [h] <;> ring
  have hcoord : φ 3 (r (b 3)) = 1 := by
    rw [hfix, hb 3, hd 3 3, if_pos rfl]
  have hzero : φ 3 (r (b 3)) = 1 - (2 : ZMod p)⁻¹ := by
    rw [hb 3, hrw (e 3), map_sub, map_smul, hd 3 3, if_pos rfl,
      sum_weight_phi_e hd w 3, phi_weight_sum hd w 3, smul_eq_mul]
    rw [show (2 : ZMod p)⁻¹ * w 3 * w 3 = 2⁻¹ by
      calc (2 : ZMod p)⁻¹ * w 3 * w 3 = 2⁻¹ * (w 3 * w 3) := by ring
        _ = 2⁻¹ * 1 := by rw [hw3]
        _ = 2⁻¹ := by ring]
  rw [hzero] at hcoord
  have h2inv : (2 : ZMod p)⁻¹ = 0 := by
    have h1 : (1 : ZMod p) = 1 + 2⁻¹ := sub_eq_iff_eq_add.mp hcoord
    have h1' : (1 : ZMod p) + 0 = 1 + 2⁻¹ := by simpa using h1
    exact (add_left_cancel h1').symm
  exact inv_ne_zero (zmod_two_ne_zero hp2) h2inv

theorem ggCZWF4_refl_fix_mem_closure [Finite V] (hp2 : p ≠ 2) (hd : GGCZDual e φ)
    (hb : ∀ i, b i = e i) {r : V ≃ₗ[ZMod p] V} (hr : r ∈ ggCZWF4 p e φ) (hrr : GGLinRefl r)
    (hfix : r (b 3) = b 3) :
    r ∈ Subgroup.closure {ZS.permMap p b (Equiv.swap 0 1), ZS.permMap p b (Equiv.swap 1 2),
      ZS.diagMap p b (fun j => if j = 2 then -1 else 1)} := by
  classical
  change r ∈ ggCZB3 (p := p) b
  rcases ggCZWF4_refl hp2 hd hr hrr with (hRD | hS) | hH
  · obtain ⟨i, j, hij, ε, hε, hrw⟩ := hRD
    exact ggCZB3_of_RD hp2 hd hb hij hε hrw hfix
  · obtain ⟨i, hrw⟩ := hS
    exact ggCZB3_of_S hp2 hd hb hrw hfix
  · obtain ⟨w, hw, hrw⟩ := hH
    exact (ggCZ_not_H hp2 hd hb hw hrw hfix).elim

end CFSG.StandardType

end

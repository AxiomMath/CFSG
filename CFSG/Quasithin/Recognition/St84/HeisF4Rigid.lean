module

public import CFSG.Quasithin.Recognition.St84.HeisF4
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.F112R.St84.Heis

open CFSG.Fischer
open Classical
open scoped commutatorElement

local instance (priority := high) f4DecEqRigid : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

local instance (priority := high) q1mDecEqRigid : DecidableEq Q1M := Q1M.decEq

local instance (priority := high) mulAutDecEqRigid : DecidableEq (MulAut Q1M) :=
  fun a b => decidable_of_iff (a e1 = b e1 ∧ a e2 = b e2 ∧ a f1 = b f1 ∧ a f2 = b f2) (by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact aut_ext h1 h2 h3 h4
    · rintro rfl
      exact ⟨rfl, rfl, rfl, rfl⟩)

theorem e1_sq : e1 * e1 = 1 := by decide +kernel

theorem f1_sq : f1 * f1 = 1 := by decide +kernel

theorem beta_sq_e1 : βM (βM e1) = e2 := by decide +kernel

theorem beta_f1 : βM f1 = f2 := by decide +kernel

theorem beta_e1 : βM e1 = e1 * e2 := by decide +kernel

theorem beta_e2 : βM e2 = e1 := by decide +kernel

theorem beta_f2 : βM f2 = f1 * f2 := by decide +kernel

theorem e1f1_ne : e1 * f1 ≠ f1 * e1 := by decide +kernel

theorem e1_beta_rel : e1 * βM (βM e1) = βM e1 := by decide +kernel

theorem f1_beta_rel : f1 * βM (βM f1) = βM f1 := by decide +kernel

theorem eq_one_of_ρM_eq : ∀ q : Q1M, ρM q = q → q = 1 := by
  decide +kernel

theorem fix_beta_center : ∀ q : Q1M, βM q = q ↔ q ∈ Subgroup.center Q1M := by
  decide +kernel

theorem fix_conj_beta (g : MulAut Q1M) (q : Q1M) :
    (g * βM * g⁻¹) q = q ↔ q ∈ Subgroup.center Q1M := by
  constructor
  · intro h
    have hqq : g (βM (g⁻¹ q)) = q := by
      simpa [MulAut.mul_apply] using h
    have h' : βM (g⁻¹ q) = g⁻¹ q := by
      have := congrArg (fun z => g⁻¹ z) hqq
      simpa using this
    have hc : g⁻¹ q ∈ Subgroup.center Q1M := (fix_beta_center (g⁻¹ q)).mp h'
    have hmap : q ∈ (Subgroup.center Q1M).map (g : Q1M →* Q1M) :=
      ⟨g⁻¹ q, hc, by simp⟩
    rwa [show (Subgroup.center Q1M).map (g : Q1M →* Q1M) = Subgroup.center Q1M from
      Subgroup.map_center_eq g] at hmap
  · intro hq
    have hc : g⁻¹ q ∈ Subgroup.center Q1M := by
      have hmap : q ∈ (Subgroup.center Q1M).map (g : Q1M →* Q1M) := by
        rwa [show (Subgroup.center Q1M).map (g : Q1M →* Q1M) = Subgroup.center Q1M from
          Subgroup.map_center_eq g]
      obtain ⟨z, hz, hzq⟩ := hmap
      rw [← hzq]
      simpa using hz
    have h' : βM (g⁻¹ q) = g⁻¹ q := (fix_beta_center (g⁻¹ q)).mpr hc
    show g (βM (g⁻¹ q)) = q
    rw [h']
    simp

theorem ajList_commute_beta : ∀ i j : Fin 3, ∀ k : Fin 2,
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ)) * βM =
      βM * (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ)) := by
  decide +kernel

theorem commute_of_mem_AJ {α : MulAut Q1M} (h : α ∈ AJ) : α * βM = βM * α := by
  rw [mem_AJ_iff] at h
  rw [mem_ajList] at h
  obtain ⟨i, j, k, rfl⟩ := h
  exact ajList_commute_beta i j k

theorem check_cent : ∀ x y : Q1M, x * x = 1 → x * βM (βM x) = βM x → y * y = 1 →
    y * βM (βM y) = βM y → x * y ≠ y * x →
    ∃ g ∈ ajList.toFinset, g e1 = x ∧ g f1 = y := by
  decide +kernel

theorem mem_AJ_of_commute {α : MulAut Q1M} (h : α * βM = βM * α) : α ∈ AJ := by
  have hcomm : ∀ q : Q1M, α (βM q) = βM (α q) := by
    intro q
    have := DFunLike.congr_fun h q
    simpa [MulAut.mul_apply] using this
  have hx1 : α e1 * α e1 = 1 := by
    rw [← map_mul, e1_sq, map_one]
  have hx2 : α e1 * βM (βM (α e1)) = βM (α e1) := by
    rw [← hcomm, ← hcomm (βM e1), ← map_mul, e1_beta_rel]
  have hy1 : α f1 * α f1 = 1 := by
    rw [← map_mul, f1_sq, map_one]
  have hy2 : α f1 * βM (βM (α f1)) = βM (α f1) := by
    rw [← hcomm, ← hcomm (βM f1), ← map_mul, f1_beta_rel]
  have hxy : α e1 * α f1 ≠ α f1 * α e1 := by
    intro hxy
    have h' : α (e1 * f1) = α (f1 * e1) := by
      simpa [map_mul] using hxy
    exact e1f1_ne (α.injective h')
  obtain ⟨g, hgFinset, hge1, hgf1⟩ :=
    check_cent (α e1) (α f1) hx1 hx2 hy1 hy2 hxy
  have hgAJ : g ∈ AJ := by
    rw [mem_AJ_iff]
    simpa using hgFinset
  have hgcomm : ∀ q : Q1M, g (βM q) = βM (g q) := by
    intro q
    have := DFunLike.congr_fun (commute_of_mem_AJ hgAJ) q
    simpa [MulAut.mul_apply] using this
  have hge2 : g e2 = α e2 := by
    calc g e2 = g (βM (βM e1)) := by rw [beta_sq_e1]
      _ = βM (g (βM e1)) := hgcomm (βM e1)
      _ = βM (βM (g e1)) := by rw [hgcomm e1]
      _ = βM (βM (α e1)) := by rw [hge1]
      _ = βM (α (βM e1)) := by rw [hcomm e1]
      _ = α (βM (βM e1)) := by rw [hcomm (βM e1)]
      _ = α e2 := by rw [beta_sq_e1]
  have hgf2 : g f2 = α f2 := by
    calc g f2 = g (βM f1) := by rw [beta_f1]
      _ = βM (g f1) := hgcomm f1
      _ = βM (α f1) := by rw [hgf1]
      _ = α (βM f1) := by rw [hcomm f1]
      _ = α f2 := by rw [beta_f1]
  have hgα : g = α := aut_ext hge1 hge2 hgf1 hgf2
  rw [← hgα]
  exact hgAJ

theorem aj3_fix_eq_beta : ∀ i j : Fin 3,
    (∀ q : Q1M, (ρM ^ (i : ℕ) * βM ^ (j : ℕ)) q = q ↔ βM q = q) →
    ρM ^ (i : ℕ) * βM ^ (j : ℕ) = βM ∨
      ρM ^ (i : ℕ) * βM ^ (j : ℕ) = βM * βM := by
  decide +kernel

theorem γM_conj_beta : γM * βM * γM⁻¹ = βM * βM := by decide +kernel

theorem γM_sq : γM * γM = 1 := by decide +kernel

theorem beta_pow_four : βM * βM * βM * βM = βM := by decide +kernel

theorem normalizer_AJ3_le : Subgroup.normalizer (AJ3 : Set (MulAut Q1M)) ≤ AJ' := by
  intro g hg
  have hmem : g * βM * g⁻¹ ∈ AJ3 := by
    have hβ : βM ∈ AJ3 := mem_AJ3_iff.mpr (aj3List_exponents_mem 0 1)
    exact (Subgroup.mem_normalizer_iff.mp hg βM).mp hβ
  rw [mem_AJ3_iff] at hmem
  rw [mem_aj3List] at hmem
  obtain ⟨i, j, hmem_eq⟩ := hmem
  have hfix : ∀ q : Q1M, (ρM ^ (i : ℕ) * βM ^ (j : ℕ)) q = q ↔ βM q = q := by
    intro q
    rw [← hmem_eq, fix_conj_beta g q, fix_beta_center q]
  obtain h | h := aj3_fix_eq_beta i j hfix
  · have hx : g * βM * g⁻¹ = βM := by rw [hmem_eq, h]
    have hcomm : g * βM = βM * g := by
      calc g * βM = (g * βM * g⁻¹) * g := by group
        _ = βM * g := by rw [hx]
    exact AJ_le_AJ' (mem_AJ_of_commute hcomm)
  · have hx : g * βM * g⁻¹ = βM * βM := by rw [hmem_eq, h]
    have hconj : γM * g * βM * (γM * g)⁻¹ = βM := by
      calc γM * g * βM * (γM * g)⁻¹
          = γM * (g * βM * g⁻¹) * γM⁻¹ := by group
        _ = γM * (βM * βM) * γM⁻¹ := by rw [hx]
        _ = (γM * βM * γM⁻¹) * (γM * βM * γM⁻¹) := by group
        _ = (βM * βM) * (βM * βM) := by rw [γM_conj_beta]
        _ = βM := by
            calc (βM * βM) * (βM * βM) = βM * βM * βM * βM := by group
              _ = βM := beta_pow_four
    have hcomm : (γM * g) * βM = βM * (γM * g) := by
      calc (γM * g) * βM = (γM * g * βM * (γM * g)⁻¹) * (γM * g) := by group
        _ = βM * (γM * g) := by rw [hconj]
    have hmem' : γM * g ∈ AJ := mem_AJ_of_commute hcomm
    have hg' : g = γM * (γM * g) := by
      rw [← mul_assoc, γM_sq, one_mul]
    rw [hg']
    exact Subgroup.mul_mem _ (mem_AJ'_iff.mpr (aj'List_exponents_mem 0 0 0 1))
      (AJ_le_AJ' hmem')

theorem check_AJ'_fix : ∀ q : Q1M, ∀ i j : Fin 3, ∀ k l : Fin 2,
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) e1 = MulAut.conj q e1 →
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) e2 = MulAut.conj q e2 →
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) f1 = MulAut.conj q f1 →
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) f2 = MulAut.conj q f2 →
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) e1 = e1 ∧
      (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) e2 = e2 ∧
      (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) f1 = f1 ∧
      (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) f2 = f2 := by
  decide +kernel

theorem conj_eq_one_of_mem_AJ' {q : Q1M} (h : MulAut.conj q ∈ AJ') : MulAut.conj q = 1 := by
  rw [mem_AJ'_iff] at h
  rw [mem_aj'List] at h
  obtain ⟨i, j, k, l, hconj⟩ := h
  have hfix := check_AJ'_fix q i j k l (by rw [hconj]) (by rw [hconj])
    (by rw [hconj]) (by rw [hconj])
  have hlist : (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) = 1 :=
    aut_ext (by simpa using hfix.1) (by simpa using hfix.2.1)
      (by simpa using hfix.2.2.1) (by simpa using hfix.2.2.2)
  rw [hconj]
  exact hlist

@[expose] noncomputable def indexTwoFun (W : Subgroup Q1M) : Q1M → Multiplicative (ZMod 2) := by
  classical
  exact fun q => Multiplicative.ofAdd (if q ∈ W then 0 else 1)

theorem indexTwoFun_apply (W : Subgroup Q1M) (q : Q1M) :
    indexTwoFun W q = Multiplicative.ofAdd (if q ∈ W then 0 else 1) := rfl

@[expose] noncomputable def indexTwoHom {W : Subgroup Q1M} (hW : W.index = 2) :
    Q1M →* Multiplicative (ZMod 2) where
  toFun := indexTwoFun W
  map_one' := by
    rw [indexTwoFun_apply]
    simp
  map_mul' a b := by
    rw [indexTwoFun_apply, indexTwoFun_apply, indexTwoFun_apply]
    by_cases ha : a ∈ W <;> by_cases hb : b ∈ W
    · have hab : a * b ∈ W := W.mul_mem ha hb
      simp [ha, hb, hab]
    · have hab : a * b ∉ W := by
        rw [Subgroup.mul_mem_iff_of_index_two hW]
        exact fun h => hb (h.mp ha)
      simp [ha, hb, hab]
    · have hab : a * b ∉ W := by
        rw [Subgroup.mul_mem_iff_of_index_two hW]
        exact fun h => ha (h.mpr hb)
      simp [ha, hb, hab]
    · have hab : a * b ∈ W := by
        rw [Subgroup.mul_mem_iff_of_index_two hW]
        exact iff_of_false ha hb
      have htwo : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 =
          (1 : Multiplicative (ZMod 2)) := by
        rw [← ofAdd_add]
        decide
      simp [ha, hb, hab, htwo]

theorem indexTwoHom_apply {W : Subgroup Q1M} (hW : W.index = 2) (q : Q1M) :
    indexTwoHom hW q = Multiplicative.ofAdd (if q ∈ W then 0 else 1) := rfl

theorem mem_map_beta_iff {W : Subgroup Q1M} (hβ : W.map βM.toMonoidHom = W) (q : Q1M) :
    βM q ∈ W ↔ q ∈ W := by
  constructor
  · intro h
    have hmap : βM q ∈ W.map βM.toMonoidHom := by rwa [hβ]
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hmap
    exact βM.injective hxy ▸ hy
  · intro h
    have hmap : βM q ∈ W.map βM.toMonoidHom := ⟨q, h, rfl⟩
    rwa [hβ] at hmap

theorem indexTwoHom_comp_beta {W : Subgroup Q1M} (hW : W.index = 2)
    (hβ : W.map βM.toMonoidHom = W) :
    (indexTwoHom hW).comp βM.toMonoidHom = indexTwoHom hW := by
  ext q
  show indexTwoHom hW (βM q) = indexTwoHom hW q
  rw [indexTwoHom_apply, indexTwoHom_apply]
  by_cases h : q ∈ W
  · have hb : βM q ∈ W := (mem_map_beta_iff hβ q).mpr h
    rw [if_pos h, if_pos hb]
  · have hb : βM q ∉ W := fun h' => h ((mem_map_beta_iff hβ q).mp h')
    rw [if_neg h, if_neg hb]

theorem indexTwoHom_eq_one {W : Subgroup Q1M} (hW : W.index = 2)
    (hβ : W.map βM.toMonoidHom = W) : indexTwoHom hW = 1 := by
  have hcomp := indexTwoHom_comp_beta hW hβ
  have h1 := DFunLike.congr_fun hcomp e1
  have h2 := DFunLike.congr_fun hcomp e2
  have h3 := DFunLike.congr_fun hcomp f1
  have h4 := DFunLike.congr_fun hcomp f2
  simp only [MonoidHom.comp_apply, MonoidHom.one_apply] at h1 h2 h3 h4
  change indexTwoHom hW (βM e1) = indexTwoHom hW e1 at h1
  change indexTwoHom hW (βM e2) = indexTwoHom hW e2 at h2
  change indexTwoHom hW (βM f1) = indexTwoHom hW f1 at h3
  change indexTwoHom hW (βM f2) = indexTwoHom hW f2 at h4
  rw [beta_e1, map_mul] at h1
  rw [beta_e2] at h2
  rw [beta_f1] at h3
  rw [beta_f2, map_mul] at h4
  have h12 : indexTwoHom hW e1 = indexTwoHom hW e2 := h2
  have he1 : indexTwoHom hW e1 = 1 := by
    have h := h1
    rw [← h12] at h
    have h' : indexTwoHom hW e1 * indexTwoHom hW e1 =
        1 * indexTwoHom hW e1 := by
      simpa [mul_one, one_mul] using h
    exact mul_right_cancel h'
  have he2 : indexTwoHom hW e2 = 1 := by rw [← h12, he1]
  have h34 : indexTwoHom hW f1 = indexTwoHom hW f2 := h3.symm
  have hf1 : indexTwoHom hW f1 = 1 := by
    have h := h4
    rw [← h34] at h
    have h' : indexTwoHom hW f1 * indexTwoHom hW f1 =
        1 * indexTwoHom hW f1 := by
      simpa [mul_one, one_mul] using h
    exact mul_right_cancel h'
  have hf2 : indexTwoHom hW f2 = 1 := by rw [← h34, hf1]
  apply hom_ext
  · simpa using he1
  · simpa using he2
  · simpa using hf1
  · simpa using hf2

theorem not_index_two {W : Subgroup Q1M} (hW : W.index = 2)
    (hβ : W.map βM.toMonoidHom = W) : False := by
  have hf : indexTwoHom hW = 1 := indexTwoHom_eq_one hW hβ
  have hmem : ∀ q : Q1M, q ∈ W := by
    intro q
    by_contra hq
    have hval : indexTwoHom hW q = 1 := by
      simpa using DFunLike.congr_fun hf q
    have hfun : indexTwoHom hW q = Multiplicative.ofAdd (1 : ZMod 2) := by
      rw [indexTwoHom_apply, if_neg hq]
    have h1 : Multiplicative.ofAdd (1 : ZMod 2) = (1 : Multiplicative (ZMod 2)) := by
      rw [← hfun, hval]
    exact absurd h1 (by rw [ofAdd_eq_one]; norm_num)
  have htop : W = ⊤ := by
    apply le_antisymm le_top
    intro q _
    exact hmem q
  rw [htop] at hW
  simp at hW

theorem mem_AJ3_of_pow_aux : ∀ i j : Fin 3, ∀ k : Fin 2,
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ)) ^ 9 = 1 →
    ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) ∈ aj3List := by
  decide +kernel

theorem mem_AJ3_of_pow {α : MulAut Q1M} (hα : α ∈ AJ) (h9 : α ^ 9 = 1) : α ∈ AJ3 := by
  rw [mem_AJ_iff] at hα
  rw [mem_ajList] at hα
  obtain ⟨i, j, k, rfl⟩ := hα
  exact mem_AJ3_iff.mpr (mem_AJ3_of_pow_aux i j k h9)

theorem ρM_mem_AJ3 : ρM ∈ AJ3 := mem_AJ3_iff.mpr (aj3List_exponents_mem 1 0)

theorem τM_mem_AJ : τM ∈ AJ := mem_AJ_iff.mpr (ajList_exponents_mem 0 0 1)

end CFSG.Quasithin.F112R.St84.Heis

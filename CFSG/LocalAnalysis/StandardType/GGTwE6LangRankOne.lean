module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LangTorus

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6

namespace TwE6Lang


variable {k : Type*} [Field k]

abbrev eOne : Fin (Tag.rank .E6) → ℤ := Pi.single (nd 1) 1

theorem rhoPerm_nd_one : rhoPerm (nd 1) = nd 1 := by decide

variable (k) in
@[expose] noncomputable def rankOne (γ : Fin (Tag.rank .E6) → ℤ) :
    Subgroup (e6Data_valid.minGroup k) :=
  e6Data_valid.rootGroup k γ ⊔ e6Data_valid.rootGroup k (-γ)

variable (k) in
@[expose] noncomputable def langOne (θ : k →+* k) (l : k) : e6Data_valid.minGroup k :=
  e6Data_valid.xm k eOne (l - 1) * e6Data_valid.xm k (-eOne) 1 *
    e6Data_valid.xm k eOne ((l - θ l)⁻¹ - 1)

@[expose] noncomputable def negDelta (θ : k →+* k) {l : k} (hl : θ l ≠ l) : kˣ :=
  Units.mk0 (-(l - θ l)) (neg_ne_zero.2 (sub_ne_zero.2 (Ne.symm hl)))

variable (k) in
@[expose] noncomputable def langM (t : kˣ) : e6Data_valid.minGroup k :=
  e6Data_valid.nm k (nd 1) * e6Data_valid.hm k (nd 1) t

theorem endo_xm_eOne (c : k) :
    e6Data_valid.endo k (e6Data_valid.xm k eOne c) =
      e6Data_valid.blockOp k (nd 1) !![1, c; 0, 1] := by
  rw [MinData.Valid.endo_xm, MinData.Valid.blockOp_upper]

theorem endo_xm_neg_eOne (c : k) :
    e6Data_valid.endo k (e6Data_valid.xm k (-eOne) c) =
      e6Data_valid.blockOp k (nd 1) !![1, 0; c, 1] := by
  rw [MinData.Valid.endo_xm, MinData.Valid.blockOp_lower]

theorem endo_langM (t : kˣ) :
    e6Data_valid.endo k (langM k t) =
      e6Data_valid.blockOp k (nd 1) (!![0, 1; -1, 0] * !![(t : k), 0; 0, ((t⁻¹ : kˣ) : k)]) := by
  rw [langM, MinData.Valid.endo_mul, MinData.Valid.endo_nm, MinData.Valid.endo_hm,
    MinData.Valid.blockOp_mul, MinData.Valid.blockOp_weyl, MinData.Valid.blockOp_diag]

theorem sigma_langOne (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l) :
    sigma k θ (langOne k θ l) = langOne k θ l * langM k (negDelta θ hl) := by
  have hδ : l - θ l ≠ 0 := sub_ne_zero.2 (Ne.symm hl)
  have hs : sigma k θ (langOne k θ l) = e6Data_valid.xm k eOne (θ l - 1) *
      e6Data_valid.xm k (-eOne) 1 * e6Data_valid.xm k eOne ((θ l - l)⁻¹ - 1) := by
    rw [langOne, map_mul, map_mul, sigma_xm_single, sigma_xm_neg_single, sigma_xm_single,
      rhoPerm_nd_one]
    simp only [map_sub, map_one, map_inv₀, hθ]
  rw [hs]
  refine e6Data_valid.endo_injective k ?_
  simp only [langOne, MinData.Valid.endo_mul, endo_xm_eOne, endo_xm_neg_eOne, endo_langM,
    ← MinData.Valid.blockOp_mul]
  congr 1
  have e1 : θ l - l = -(l - θ l) := by ring
  rw [e1]
  simp only [negDelta, Units.val_mk0, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem xm_mem_rankOne (γ : Fin (Tag.rank .E6) → ℤ) (c : k) :
    e6Data_valid.xm k γ c ∈ rankOne k γ :=
  Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k γ c)

theorem xm_neg_mem_rankOne (γ : Fin (Tag.rank .E6) → ℤ) (c : k) :
    e6Data_valid.xm k (-γ) c ∈ rankOne k γ :=
  Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup k (-γ) c)

theorem langOne_mem_rankOne (θ : k →+* k) (l : k) : langOne k θ l ∈ rankOne k eOne :=
  mul_mem (mul_mem (xm_mem_rankOne _ _) (xm_neg_mem_rankOne _ _)) (xm_mem_rankOne _ _)

theorem nt_mem_rankOne (t : kˣ) : e6Data_valid.nt k (nd 1) t ∈ rankOne k eOne :=
  mul_mem (mul_mem (xm_mem_rankOne _ _) (xm_neg_mem_rankOne _ _)) (xm_mem_rankOne _ _)

theorem langM_mem_rankOne (t : kˣ) : langM k t ∈ rankOne k eOne := by
  rw [langM, MinData.Valid.nm, MinData.Valid.hm]
  exact mul_mem (nt_mem_rankOne 1) (mul_mem (nt_mem_rankOne t) (inv_mem (nt_mem_rankOne 1)))

theorem nWord_conj_mem_rankOne (L : List (Fin (Tag.rank .F4))) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) {x : e6Data_valid.minGroup k} (hx : x ∈ rankOne k γ) :
    nWord k L * x * (nWord k L)⁻¹ ∈ rankOne k (wAct L γ) := by
  have h : (rankOne k γ).map (MulAut.conj (nWord k L)).toMonoidHom ≤ rankOne k (wAct L γ) := by
    rw [rankOne, rankOne, Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      exact nWord_conj_mem_rootGroup L hγ hy
    · rw [Subgroup.map_le_iff_le_comap, ← map_neg]
      intro y hy
      exact nWord_conj_mem_rootGroup L (TagRoots.isRoot_neg hγ) hy
  exact h ⟨x, hx, rfl⟩

theorem rootGroup_le_centralizer {γ δ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hδ : IsRoot .E6 δ) (hne : γ + δ ≠ 0) (hnr : ¬ IsRoot .E6 (γ + δ)) :
    e6Data_valid.rootGroup k γ ≤ Subgroup.centralizer (e6Data_valid.rootGroup k δ) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
  obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
  exact (commute_xm hγ hδ hne hnr c d).eq.symm

theorem rankOne_le_centralizer {γ δ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hδ : IsRoot .E6 δ) (h₁ : γ + δ ≠ 0 ∧ ¬ IsRoot .E6 (γ + δ))
    (h₂ : γ + -δ ≠ 0 ∧ ¬ IsRoot .E6 (γ + -δ)) (h₃ : -γ + δ ≠ 0 ∧ ¬ IsRoot .E6 (-γ + δ))
    (h₄ : -γ + -δ ≠ 0 ∧ ¬ IsRoot .E6 (-γ + -δ)) :
    rankOne k γ ≤ Subgroup.centralizer (rankOne k δ) := by
  have key : ∀ γ' δ' : Fin (Tag.rank .E6) → ℤ, IsRoot .E6 γ' → IsRoot .E6 δ' →
      (γ' + δ' ≠ 0 ∧ ¬ IsRoot .E6 (γ' + δ')) → (γ' + -δ' ≠ 0 ∧ ¬ IsRoot .E6 (γ' + -δ')) →
        e6Data_valid.rootGroup k γ' ≤ Subgroup.centralizer (rankOne k δ') := by
    intro γ' δ' hγ' hδ' ha hb
    rw [Subgroup.le_centralizer_iff, rankOne]
    refine sup_le ?_ ?_
    · exact rootGroup_le_centralizer hδ' hγ' (by rw [add_comm]; exact ha.1)
        (by rw [add_comm]; exact ha.2)
    · exact rootGroup_le_centralizer (TagRoots.isRoot_neg hδ') hγ' (by rw [add_comm]; exact hb.1)
        (by rw [add_comm]; exact hb.2)
  rw [rankOne]
  exact sup_le (key γ δ hγ hδ h₁ h₂) (key (-γ) δ (TagRoots.isRoot_neg hγ) hδ h₃ h₄)

theorem commute_of_mem_rankOne {γ δ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hδ : IsRoot .E6 δ) (h₁ : γ + δ ≠ 0 ∧ ¬ IsRoot .E6 (γ + δ))
    (h₂ : γ + -δ ≠ 0 ∧ ¬ IsRoot .E6 (γ + -δ)) (h₃ : -γ + δ ≠ 0 ∧ ¬ IsRoot .E6 (-γ + δ))
    (h₄ : -γ + -δ ≠ 0 ∧ ¬ IsRoot .E6 (-γ + -δ)) {x y : e6Data_valid.minGroup k}
    (hx : x ∈ rankOne k γ) (hy : y ∈ rankOne k δ) : Commute x y :=
  (Subgroup.mem_centralizer_iff.1 (rankOne_le_centralizer hγ hδ h₁ h₂ h₃ h₄ hx) y hy).symm

end TwE6Lang

end CFSG.StandardType

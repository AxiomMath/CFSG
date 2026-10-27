module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus
public import CFSG.LieType.Chevalley.WeylRoots

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Chevalley.ExceptionalCover

namespace TwE6Per

abbrev vb3 : Fin (Tag.rank .E6) → ℤ := ![0, 0, 0, 1, 0, 0]

abbrev vb2 : Fin (Tag.rank .E6) → ℤ := ![0, 0, 1, 1, 1, 0]

abbrev vb1 : Fin (Tag.rank .E6) → ℤ := ![1, 0, 1, 1, 1, 1]

abbrev vth : Fin (Tag.rank .E6) → ℤ := ![1, 2, 2, 3, 2, 1]

theorem vb3_eq : vb3 = Pi.single (nd 3) 1 := by decide

theorem reflect_vb3 : reflect .E6 (nd 2) (reflect .E6 (nd 4) vb3) = vb2 := by decide

theorem reflect_vb2 : reflect .E6 (nd 0) (reflect .E6 (nd 5) vb2) = vb1 := by decide

theorem isRoot_vb3 : IsRoot .E6 vb3 := vb3_eq ▸ IsRoot.basis _

theorem isRoot_vb2 : IsRoot .E6 vb2 :=
  reflect_vb3 ▸ (isRoot_vb3.reflect _).reflect _

theorem isRoot_vb1 : IsRoot .E6 vb1 :=
  reflect_vb2 ▸ (isRoot_vb2.reflect _).reflect _

theorem isRoot_vth : IsRoot .E6 vth := by
  have h : vth = reflect .E6 (nd 1) (reflect .E6 (nd 3) (reflect .E6 (nd 4) (reflect .E6 (nd 2)
      (reflect .E6 (nd 5) (reflect .E6 (nd 0) (reflect .E6 (nd 3) (reflect .E6 (nd 4)
      (reflect .E6 (nd 2) (reflect .E6 (nd 3) (Pi.single (nd 1) 1)))))))))) := by decide
  rw [h]
  repeat' apply IsRoot.reflect
  exact IsRoot.basis _

theorem rho_vth : rho vth = vth := by decide

theorem reflect_neg (i : Fin (Tag.rank .E6)) (v : Fin (Tag.rank .E6) → ℤ) :
    reflect .E6 i (-v) = -reflect .E6 i v := by
  funext j
  simp only [reflect, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, mul_neg,
    Finset.sum_neg_distrib, neg_mul]
  ring


section CharTwo

variable {k : Type} [Field k] [CharP k 2]

theorem nm_conj_xm_two {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (i : Fin (Tag.rank .E6))
    (c : k) : e6Data_valid.nm k i * e6Data_valid.xm k γ c * (e6Data_valid.nm k i)⁻¹ =
      e6Data_valid.xm k (reflect .E6 i γ) c := by
  obtain ⟨σ, hσ, h⟩ := e6Data_valid.nm_conj_xm k hγ i
  rw [h c]
  have h1 : σ = 1 := by
    rcases hσ with h' | h'
    · exact h'
    · rw [h', CharTwo.neg_eq]
  rw [h1, one_mul]

theorem nm_sq_two (i : Fin (Tag.rank .E6)) :
    e6Data_valid.nm k i * e6Data_valid.nm k i = 1 := by
  have h := e6Data_valid.nm_sq k i
  rw [pow_two] at h
  rw [h]
  have h1 : (-1 : kˣ) = 1 := Units.ext (by rw [Units.val_neg, Units.val_one, CharTwo.neg_eq])
  rw [h1, e6Data_valid.hm_one]

theorem xm_mul_self_two (γ : Fin (Tag.rank .E6) → ℤ) (c : k) :
    e6Data_valid.xm k γ c * e6Data_valid.xm k γ c = 1 := by
  rw [← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]

end CharTwo

section RankOne

variable (k : Type) [Field k]

@[expose] noncomputable def rankOne (γ : Fin (Tag.rank .E6) → ℤ) :
    Subgroup (e6Data_valid.minGroup k) :=
  Subgroup.closure {g | ∃ c, g = e6Data_valid.xm k γ c ∨ g = e6Data_valid.xm k (-γ) c}

variable {k}

theorem xm_mem_rankOne (γ : Fin (Tag.rank .E6) → ℤ) (c : k) :
    e6Data_valid.xm k γ c ∈ rankOne k γ :=
  Subgroup.subset_closure ⟨c, Or.inl rfl⟩

theorem xm_neg_mem_rankOne (γ : Fin (Tag.rank .E6) → ℤ) (c : k) :
    e6Data_valid.xm k (-γ) c ∈ rankOne k γ :=
  Subgroup.subset_closure ⟨c, Or.inr rfl⟩

theorem nm_mem_rankOne (i : Fin (Tag.rank .E6)) :
    e6Data_valid.nm k i ∈ rankOne k (Pi.single i 1) := by
  unfold MinData.Valid.nm MinData.Valid.nt
  exact mul_mem (mul_mem (xm_mem_rankOne _ _) (xm_neg_mem_rankOne _ _)) (xm_mem_rankOne _ _)

theorem commute_rankOne {γ δ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (hδ : IsRoot .E6 δ)
    (h1 : γ + δ ≠ 0) (h2 : γ - δ ≠ 0) (h3 : ¬ IsRoot .E6 (γ + δ)) (h4 : ¬ IsRoot .E6 (γ - δ))
    {x y : e6Data_valid.minGroup k} (hx : x ∈ rankOne k γ) (hy : y ∈ rankOne k δ) :
    Commute x y := by
  have hγ' := IsRoot.neg hγ
  have hδ' := IsRoot.neg hδ
  have hc : ∀ {γ' δ' : Fin (Tag.rank .E6) → ℤ}, IsRoot .E6 γ' → IsRoot .E6 δ' → γ' + δ' ≠ 0 →
      ¬ IsRoot .E6 (γ' + δ') → ∀ c d : k,
        Commute (e6Data_valid.xm k γ' c) (e6Data_valid.xm k δ' d) := fun hγ' hδ' hne hnr c d =>
    commutatorElement_eq_one_iff_commute.1 ((e6Data_valid.commutator_xm k hγ' hδ' hne).2 hnr c d)
  have e1 : γ + -δ = γ - δ := (sub_eq_add_neg γ δ).symm
  have e2 : -γ + δ = -(γ - δ) := by abel
  have e3 : -γ + -δ = -(γ + δ) := by abel
  have hgen : ∀ a ∈ {g | ∃ c, g = e6Data_valid.xm k γ c ∨ g = e6Data_valid.xm k (-γ) c},
      ∀ b ∈ {g | ∃ c, g = e6Data_valid.xm k δ c ∨ g = e6Data_valid.xm k (-δ) c}, Commute a b := by
    rintro _ ⟨c, rfl | rfl⟩ _ ⟨d, rfl | rfl⟩
    · exact hc hγ hδ h1 h3 c d
    · exact hc hγ hδ' (by rw [e1]; exact h2) (by rw [e1]; exact h4) c d
    · exact hc hγ' hδ (by rw [e2]; exact neg_ne_zero.2 h2)
        (by rw [e2, isRoot_neg_iff]; exact h4) c d
    · exact hc hγ' hδ' (by rw [e3]; exact neg_ne_zero.2 h1)
        (by rw [e3, isRoot_neg_iff]; exact h3) c d
  have hy' : ∀ a ∈ {g | ∃ c, g = e6Data_valid.xm k γ c ∨ g = e6Data_valid.xm k (-γ) c},
      Commute a y := by
    intro a ha
    have hle : rankOne k δ ≤ Subgroup.centralizer {a} :=
      (Subgroup.closure_le _).2 fun b hb =>
        Subgroup.mem_centralizer_singleton_iff.2 (hgen a ha b hb).eq.symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  have hle : rankOne k γ ≤ Subgroup.centralizer {y} :=
    (Subgroup.closure_le _).2 fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.2 (hy' a ha).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

variable [CharP k 2]

theorem conj_mem_rankOne {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (i : Fin (Tag.rank .E6)) {x : e6Data_valid.minGroup k} (hx : x ∈ rankOne k γ) :
    e6Data_valid.nm k i * x * (e6Data_valid.nm k i)⁻¹ ∈ rankOne k (reflect .E6 i γ) := by
  set n := e6Data_valid.nm k i
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨c, rfl | rfl⟩ := hg
    · rw [nm_conj_xm_two hγ i c]
      exact xm_mem_rankOne _ c
    · rw [nm_conj_xm_two (IsRoot.neg hγ) i c, reflect_neg]
      exact xm_neg_mem_rankOne _ c
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    have e : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

end RankOne

end TwE6Per

end CFSG.StandardType

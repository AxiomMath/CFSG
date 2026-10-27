module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4TensorGL
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open scoped TensorProduct
private def s16t_l4f_a1 : ↥(CFSG.Quasithin.permCore 3) :=
  ⟨![1, 1, 0], by
    show ∑ i, (![1, 1, 0] : Fin 3 → ZMod 2) i = 0
    decide⟩

private def s16t_l4f_a2 : ↥(CFSG.Quasithin.permCore 3) :=
  ⟨![0, 1, 1], by
    show ∑ i, (![0, 1, 1] : Fin 3 → ZMod 2) i = 0
    decide⟩

private def s16t_l4f_sigma0 : Equiv.Perm (Fin 3) := finRotate 3

private lemma s16t_l4f_zmod2_sum_zero (p0 p1 p2 : ZMod 2) (h : p0 + p1 + p2 = 0) :
    p2 = p0 + p1 := by
  revert p0 p1 p2
  decide

private lemma s16t_l4f_zmod2_add_add_cancel (p q : ZMod 2) : p + (p + q) = q := by
  revert p q
  decide

private lemma s16t_l4f_a1a2_span :
    ⊤ ≤ Submodule.span (ZMod 2) (Set.range ![s16t_l4f_a1, s16t_l4f_a2]) := by
  intro x _
  have hx : x = (x : Fin 3 → ZMod 2) 0 • s16t_l4f_a1 +
      ((x : Fin 3 → ZMod 2) 0 + (x : Fin 3 → ZMod 2) 1) • s16t_l4f_a2 := by
    apply Subtype.ext
    funext j
    have hsum : ∑ i, (x : Fin 3 → ZMod 2) i = 0 := x.2
    rw [Fin.sum_univ_three] at hsum
    have h2 := s16t_l4f_zmod2_sum_zero _ _ _ hsum
    fin_cases j <;> simp [s16t_l4f_a1, s16t_l4f_a2, h2, s16t_l4f_zmod2_add_add_cancel]
  rw [hx]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private noncomputable def s16t_l4f_basis :
    Module.Basis (Fin 2) (ZMod 2) ↥(CFSG.Quasithin.permCore 3) :=
  Module.Basis.mk (v := ![s16t_l4f_a1, s16t_l4f_a2])
    (by
      rw [Fintype.linearIndependent_iffₛ]
      intro f g hfg i
      fin_cases i
      · have h0 := congrFun (congrArg Subtype.val hfg) 0
        simpa [Fin.sum_univ_two, s16t_l4f_a1, s16t_l4f_a2] using h0
      · have h0 := congrFun (congrArg Subtype.val hfg) 0
        have h1 := congrFun (congrArg Subtype.val hfg) 1
        simp [Fin.sum_univ_two, s16t_l4f_a1, s16t_l4f_a2] at h0 h1
        rw [h0] at h1
        exact add_left_cancel h1)
    s16t_l4f_a1a2_span

private lemma s16t_l4f_basis_zero : s16t_l4f_basis 0 = s16t_l4f_a1 := by
  simp [s16t_l4f_basis, Module.Basis.mk_apply]

private lemma s16t_l4f_basis_one : s16t_l4f_basis 1 = s16t_l4f_a2 := by
  simp [s16t_l4f_basis, Module.Basis.mk_apply]

private lemma s16t_l4f_permAct_sigma0_a1 :
    CFSG.Quasithin.permAct s16t_l4f_sigma0 (s16t_l4f_a1 : Fin 3 → ZMod 2) =
      (s16t_l4f_a2 : Fin 3 → ZMod 2) := by
  funext i
  fin_cases i <;> decide

private lemma s16t_l4f_permAct_sigma0_a2 :
    CFSG.Quasithin.permAct s16t_l4f_sigma0 (s16t_l4f_a2 : Fin 3 → ZMod 2) =
      (s16t_l4f_a1 : Fin 3 → ZMod 2) + (s16t_l4f_a2 : Fin 3 → ZMod 2) := by
  funext i
  fin_cases i <;> decide

private lemma s16t_l4f_sigma0_pow_three : s16t_l4f_sigma0 ^ 3 = 1 := by
  decide

private lemma s16t_l4f_sigma0_ne_one : s16t_l4f_sigma0 ≠ 1 := by
  decide

private lemma s16t_l4f_basisFun_linearCombination {m : ℕ} (w : Fin m → ZMod 2) :
    Fintype.linearCombination (ZMod 2) (Pi.basisFun (ZMod 2) (Fin m)) w = w := by
  rw [Fintype.linearCombination_apply]
  conv_rhs => rw [← Module.Basis.sum_repr (Pi.basisFun (ZMod 2) (Fin m)) w]
  simp

private lemma s16t_l4f_tensor_decomp {m : ℕ}
    (t : ↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2)) :
    ∃ c₁ c₂ : Fin m → ZMod 2,
      t = s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂ := by
  let b := s16t_l4f_basis
  let std := Pi.basisFun (ZMod 2) (Fin m)
  let bt := b.tensorProduct std
  refine ⟨fun j => bt.repr t (0, j), fun j => bt.repr t (1, j), ?_⟩
  have hb0 : b 0 = s16t_l4f_a1 := by rw [show b = s16t_l4f_basis from rfl, s16t_l4f_basis_zero]
  have hb1 : b 1 = s16t_l4f_a2 := by rw [show b = s16t_l4f_basis from rfl, s16t_l4f_basis_one]
  have h0 : (∑ j : Fin m, bt.repr t (0, j) • bt (0, j)) =
      s16t_l4f_a1 ⊗ₜ[ZMod 2] (fun j => bt.repr t (0, j)) := by
    dsimp only [bt, std]
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Module.Basis.tensorProduct_apply, ← TensorProduct.tmul_smul])]
    rw [← TensorProduct.tmul_sum, ← Fintype.linearCombination_apply,
      s16t_l4f_basisFun_linearCombination, hb0]
  have h1 : (∑ j : Fin m, bt.repr t (1, j) • bt (1, j)) =
      s16t_l4f_a2 ⊗ₜ[ZMod 2] (fun j => bt.repr t (1, j)) := by
    dsimp only [bt, std]
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Module.Basis.tensorProduct_apply, ← TensorProduct.tmul_smul])]
    rw [← TensorProduct.tmul_sum, ← Fintype.linearCombination_apply,
      s16t_l4f_basisFun_linearCombination, hb1]
  conv_lhs => rw [← Module.Basis.sum_repr bt t]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, h0, h1]

private lemma s16t_l4f_zmod2_eq_of_add_eq_zero (p q : ZMod 2) (h : p + q = 0) : p = q := by
  revert p q
  decide

private lemma s16t_l4f_eq_of_add_eq_zero {m : ℕ} {x y : Fin m → ZMod 2} (h : x + y = 0) :
    x = y := by
  funext c
  exact s16t_l4f_zmod2_eq_of_add_eq_zero (x c) (y c) (congrFun h c)

private lemma s16t_l4f_tensor_add_self {m : ℕ}
    (x : ↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2)) : x + x = 0 := by
  rw [← one_smul (ZMod 2) x, ← add_smul, show (1 + 1 : ZMod 2) = 0 by decide, zero_smul]

private lemma s16t_l4f_ofAdd_add {α : Type*} [Add α] (x y : α) :
    Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl

private lemma s16t_l4f_tensor_fix_rank2 {m : ℕ} (c₁ c₂ : Fin m → ZMod 2) :
    s16t_l4f_a2 ⊗ₜ[ZMod 2] (c₁ + c₂) +
        (s16t_l4f_a1 + s16t_l4f_a2) ⊗ₜ[ZMod 2] c₁ =
      s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂ := by
  calc s16t_l4f_a2 ⊗ₜ[ZMod 2] (c₁ + c₂) + (s16t_l4f_a1 + s16t_l4f_a2) ⊗ₜ[ZMod 2] c₁
      = s16t_l4f_a2 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂ +
          (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₁) := by
        rw [TensorProduct.tmul_add, TensorProduct.add_tmul]
    _ = (s16t_l4f_a2 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₁) +
          (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂) := by abel
    _ = 0 + (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂) := by
        rw [s16t_l4f_tensor_add_self]
    _ = s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂ := by rw [zero_add]

private lemma s16t_l4f_fix_rank2 {W : Type} [CommGroup W] {G : Subgroup (MulAut W)} {m : ℕ}
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin m) (ZMod 2))}
    {ψ : W ≃* Multiplicative (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2))}
    (hcompat : ∀ (γ : ↥G) (a a' : ↥(CFSG.Quasithin.permCore 3)) (c c' : Fin m → ZMod 2),
      (a' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      c' = ((φ γ).2 : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c →
        ψ ((γ : MulAut W) (ψ.symm (Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c)))) =
          Multiplicative.ofAdd (a' ⊗ₜ[ZMod 2] c'))
    {c₁ c₂ : Fin m → ZMod 2} {g : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)}
    (hg₁ : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁ = c₁ + c₂)
    (hg₂ : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂ = c₁) {w : W}
    (hw : ψ w = Multiplicative.ofAdd
      (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)) :
    (φ.symm (s16t_l4f_sigma0, g) : MulAut W) w = w := by
  have hφ : φ (φ.symm (s16t_l4f_sigma0, g)) = (s16t_l4f_sigma0, g) :=
    MulEquiv.apply_symm_apply φ _
  have h₁ := hcompat (φ.symm (s16t_l4f_sigma0, g)) s16t_l4f_a1 s16t_l4f_a2 c₁
    ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁)
    (by rw [hφ]; exact s16t_l4f_permAct_sigma0_a1.symm)
    (by rw [hφ])
  have h₂ := hcompat (φ.symm (s16t_l4f_sigma0, g)) s16t_l4f_a2
    (s16t_l4f_a1 + s16t_l4f_a2) c₂ ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)
    (by rw [hφ]; exact s16t_l4f_permAct_sigma0_a2.symm)
    (by rw [hφ])
  have hmain : ψ ((φ.symm (s16t_l4f_sigma0, g) : MulAut W)
      (ψ.symm (Multiplicative.ofAdd
        (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)))) =
      Multiplicative.ofAdd (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂) := by
    calc ψ ((φ.symm (s16t_l4f_sigma0, g) : MulAut W)
          (ψ.symm (Multiplicative.ofAdd
            (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂))))
        = ψ ((φ.symm (s16t_l4f_sigma0, g) : MulAut W)
            (ψ.symm (Multiplicative.ofAdd (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁)) *
              ψ.symm (Multiplicative.ofAdd (s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [s16t_l4f_ofAdd_add, map_mul]
      _ = ψ ((φ.symm (s16t_l4f_sigma0, g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁))) *
            (φ.symm (s16t_l4f_sigma0, g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [map_mul]
      _ = ψ ((φ.symm (s16t_l4f_sigma0, g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁)))) *
            ψ ((φ.symm (s16t_l4f_sigma0, g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [map_mul]
      _ = Multiplicative.ofAdd
            (s16t_l4f_a2 ⊗ₜ[ZMod 2] ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁)) *
            Multiplicative.ofAdd
              ((s16t_l4f_a1 + s16t_l4f_a2) ⊗ₜ[ZMod 2]
                ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)) := by
          rw [h₁, h₂]
      _ = Multiplicative.ofAdd
            (s16t_l4f_a2 ⊗ₜ[ZMod 2] ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁) +
              (s16t_l4f_a1 + s16t_l4f_a2) ⊗ₜ[ZMod 2]
                ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)) := by
          rw [s16t_l4f_ofAdd_add]
      _ = Multiplicative.ofAdd (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ +
            s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂) := by
          rw [hg₁, hg₂, s16t_l4f_tensor_fix_rank2]
  have hmain' : ψ ((φ.symm (s16t_l4f_sigma0, g) : MulAut W) w) = ψ w := by
    have hw' : w = ψ.symm (Multiplicative.ofAdd
        (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)) := by
      rw [← hw, MulEquiv.symm_apply_apply]
    rw [hw', hmain, MulEquiv.apply_symm_apply]
  exact ψ.injective hmain'

private lemma s16t_l4f_zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private lemma s16t_l4f_permAct_one (n : ℕ) (a : Fin n → ZMod 2) :
    CFSG.Quasithin.permAct (1 : Equiv.Perm (Fin n)) a = a := by
  funext i
  simp [CFSG.Quasithin.permAct]

private lemma s16t_l4f_zpowers_le_normalizer_of_commute {H : Type*} [Group H] {a b : H}
    (h : a * b = b * a) :
    Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a) := by
  rw [Subgroup.zpowers_le]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : (a ^ n) * b = b * (a ^ n) := (show Commute a b from h).zpow_left n
    rw [← hn, ← hc, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers a n
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute (a ^ n) b := (show Commute a b from h).zpow_left n
    have hx' : b⁻¹ * a ^ n * b = a ^ n := by
      have h1 : b⁻¹ * a ^ n = a ^ n * b⁻¹ := hc.inv_right.eq.symm
      rw [h1]
      group
    have hxy : x = b⁻¹ * (b * x * b⁻¹) * b := by group
    rw [hxy, ← hn, hx']
    exact Subgroup.zpow_mem_zpowers a n

private lemma s16t_l4f_disjoint_zpowers_of_prime {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    {a b : H} (ha : a ^ p = 1) (ha1 : a ≠ 1) (hain : a ∉ Subgroup.zpowers b) :
    Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b) := by
  rw [Subgroup.disjoint_def]
  intro x hxa hxb
  by_contra hx1
  haveI : Fact p.Prime := ⟨hp⟩
  have hoa : orderOf a = p := orderOf_eq_prime ha ha1
  have hdvd : orderOf x ∣ p := by
    rw [← hoa]
    exact orderOf_dvd_of_mem_zpowers hxa
  have hox : orderOf x = p := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  haveI : Finite (Subgroup.zpowers a) :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, ha⟩).finite_zpowers
  have heq : Subgroup.zpowers x = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxa)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hox])
  have hax : a ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers a
  exact hain (Subgroup.zpowers_le.2 hxb hax)

private lemma s16t_l4f_closure_pair_elemAbelian_nine {H : Type*} [Group H] {q₁ q₂ : H}
    (h₁ : q₁ ^ 3 = 1) (h₂ : q₂ ^ 3 = 1) (hne : q₁ ≠ 1) (hne₂ : q₂ ≠ 1)
    (hcomm : q₁ * q₂ = q₂ * q₁) (hdisj : Disjoint (Subgroup.zpowers q₁) (Subgroup.zpowers q₂)) :
    IsElemAbelian 3 (Subgroup.closure ({q₁, q₂} : Set H)) ∧
      Nat.card (Subgroup.closure ({q₁, q₂} : Set H)) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcomm' : ∀ x ∈ ({q₁, q₂} : Set H), ∀ y ∈ ({q₁, q₂} : Set H), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hcomm
    · exact hcomm.symm
    · rfl
  have hpw : ∀ x ∈ ({q₁, q₂} : Set H), x ^ 3 = 1 := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h₁
    · exact h₂
  refine ⟨IsElemAbelian.closure_of_commute hcomm' hpw, ?_⟩
  have hclosure : Subgroup.closure ({q₁, q₂} : Set H) =
      Subgroup.zpowers q₁ ⊔ Subgroup.zpowers q₂ := by
    rw [show ({q₁, q₂} : Set H) = {q₁} ∪ {q₂} from by ext x; simp [or_comm],
      Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  rw [hclosure,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (s16t_l4f_zpowers_le_normalizer_of_commute hcomm) hdisj,
    Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime h₁ hne, orderOf_eq_prime h₂ hne₂]

private lemma s16t_l4f_fix_two_pure {W : Type} [CommGroup W] {G : Subgroup (MulAut W)} {m : ℕ}
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin m) (ZMod 2))}
    {ψ : W ≃* Multiplicative (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2))}
    (hcompat : ∀ (γ : ↥G) (a a' : ↥(CFSG.Quasithin.permCore 3)) (c c' : Fin m → ZMod 2),
      (a' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      c' = ((φ γ).2 : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c →
        ψ ((γ : MulAut W) (ψ.symm (Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c)))) =
          Multiplicative.ofAdd (a' ⊗ₜ[ZMod 2] c'))
    {c₁ c₂ : Fin m → ZMod 2} {g : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)}
    (hg₁ : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁ = c₁)
    (hg₂ : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂ = c₂) {w : W}
    (hw : ψ w = Multiplicative.ofAdd
      (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)) :
    (φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W) w = w := by
  have hφ : φ (φ.symm ((1 : Equiv.Perm (Fin 3)), g)) = ((1 : Equiv.Perm (Fin 3)), g) :=
    MulEquiv.apply_symm_apply φ _
  have h₁ := hcompat (φ.symm ((1 : Equiv.Perm (Fin 3)), g)) s16t_l4f_a1 s16t_l4f_a1 c₁
    ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁)
    (by rw [hφ]; exact s16t_l4f_permAct_one 3 (s16t_l4f_a1 : Fin 3 → ZMod 2))
    (by rw [hφ])
  have h₂ := hcompat (φ.symm ((1 : Equiv.Perm (Fin 3)), g)) s16t_l4f_a2 s16t_l4f_a2 c₂
    ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)
    (by rw [hφ]; exact s16t_l4f_permAct_one 3 (s16t_l4f_a2 : Fin 3 → ZMod 2))
    (by rw [hφ])
  have hmain : ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
      (ψ.symm (Multiplicative.ofAdd
        (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)))) =
      Multiplicative.ofAdd (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂) := by
    calc ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
          (ψ.symm (Multiplicative.ofAdd
            (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂))))
        = ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
            (ψ.symm (Multiplicative.ofAdd (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁)) *
              ψ.symm (Multiplicative.ofAdd (s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [s16t_l4f_ofAdd_add, map_mul]
      _ = ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁))) *
            (φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [map_mul]
      _ = ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁)))) *
            ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [map_mul]
      _ = Multiplicative.ofAdd
            (s16t_l4f_a1 ⊗ₜ[ZMod 2] ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁)) *
            Multiplicative.ofAdd
              (s16t_l4f_a2 ⊗ₜ[ZMod 2]
                ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)) := by
          rw [h₁, h₂]
      _ = Multiplicative.ofAdd
            (s16t_l4f_a1 ⊗ₜ[ZMod 2] ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁) +
              s16t_l4f_a2 ⊗ₜ[ZMod 2]
                ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)) := by
          rw [s16t_l4f_ofAdd_add]
      _ = Multiplicative.ofAdd (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ +
            s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂) := by
          rw [hg₁, hg₂]
  have hmain' : ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W) w) = ψ w := by
    have hw' : w = ψ.symm (Multiplicative.ofAdd
        (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂)) := by
      rw [← hw, MulEquiv.symm_apply_apply]
    rw [hw', hmain, MulEquiv.apply_symm_apply]
  exact ψ.injective hmain'

private lemma s16t_l4f_fix_closure {W : Type} [CommGroup W] {G : Subgroup (MulAut W)}
    {q₁ q₂ : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))} {w : W}
    (h₁ : (φ.symm q₁ : MulAut W) w = w) (h₂ : (φ.symm q₂ : MulAut W) w = w) :
    ∀ q ∈ Subgroup.closure ({q₁, q₂} : Set _), (φ.symm q : MulAut W) w = w := by
  intro q hq
  have hstab : Subgroup.closure ({φ.symm q₁, φ.symm q₂} : Set ↥G) ≤
      (MulAction.stabilizer (MulAut W) w).comap G.subtype := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact MulAction.mem_stabilizer_iff.mpr h₁
    · exact MulAction.mem_stabilizer_iff.mpr h₂
  have hmem : φ.symm q ∈ Subgroup.closure ({φ.symm q₁, φ.symm q₂} : Set ↥G) := by
    have h : φ.symm q ∈ (Subgroup.closure ({q₁, q₂} : Set _)).map φ.symm.toMonoidHom :=
      ⟨q, hq, rfl⟩
    rwa [MonoidHom.map_closure, Set.image_pair] at h
  exact MulAction.mem_stabilizer_iff.mp (hstab hmem)

private lemma s16t_l4f_transport_e9 {W : Type} [CommGroup W] {G : Subgroup (MulAut W)}
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))}
    {E₀ : Subgroup (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))} {w : W}
    (hE : IsElemAbelian 3 E₀) (hcard : Nat.card E₀ = 9)
    (hfix : ∀ q ∈ E₀, (φ.symm q : MulAut W) w = w) :
    ∃ E : Subgroup (MulAut W), E ≤ G ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ e ∈ E, (e : MulAut W) w = w := by
  refine ⟨E₀.map (G.subtype.comp φ.symm.toMonoidHom), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact (φ.symm q).2
  · exact hE.map (G.subtype.comp φ.symm.toMonoidHom)
  · rw [Subgroup.card_map_of_injective (f := G.subtype.comp φ.symm.toMonoidHom)
      ((Subgroup.subtype_injective G).comp φ.symm.injective)]
    exact hcard
  · rintro _ ⟨q, hq, rfl⟩
    exact hfix q hq

private lemma s16t_l4f_fix_perm_pure {W : Type} [CommGroup W] {G : Subgroup (MulAut W)}
    {m : ℕ}
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin m) (ZMod 2))}
    {ψ : W ≃* Multiplicative (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2))}
    (hcompat : ∀ (γ : ↥G) (a a' : ↥(CFSG.Quasithin.permCore 3)) (c c' : Fin m → ZMod 2),
      (a' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      c' = ((φ γ).2 : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c →
        ψ ((γ : MulAut W) (ψ.symm (Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c)))) =
          Multiplicative.ofAdd (a' ⊗ₜ[ZMod 2] c'))
    {a : ↥(CFSG.Quasithin.permCore 3)} {c : Fin m → ZMod 2} {τ₀ : Equiv.Perm (Fin 3)}
    (hτ : CFSG.Quasithin.permAct τ₀ (a : Fin 3 → ZMod 2) = (a : Fin 3 → ZMod 2)) {w : W}
    (hw : ψ w = Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c)) :
    (φ.symm ((τ₀, 1) : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin m) (ZMod 2))
      : MulAut W) w = w := by
  have hφ : φ (φ.symm ((τ₀, 1) : Equiv.Perm (Fin 3) ×
      Matrix.GeneralLinearGroup (Fin m) (ZMod 2))) =
      ((τ₀, 1) : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) :=
    MulEquiv.apply_symm_apply φ _
  have h := hcompat (φ.symm ((τ₀, 1) : Equiv.Perm (Fin 3) ×
      Matrix.GeneralLinearGroup (Fin m) (ZMod 2))) a a c c
    (by rw [hφ]; exact hτ.symm) (by rw [hφ]; simp)
  rw [← hw] at h
  simp only [MulEquiv.symm_apply_apply] at h
  exact ψ.injective h

private lemma s16t_l4f_exists_eq_coord (a : Fin 3 → ZMod 2) :
    ∃ i j : Fin 3, i ≠ j ∧ a i = a j := by
  revert a
  decide

private lemma s16t_l4f_swap_ne_one {i j : Fin 3} (hij : i ≠ j) :
    Equiv.swap i j ≠ 1 := by
  intro h
  have h1 : (Equiv.swap i j) i = i := by rw [h]; rfl
  rw [Equiv.swap_apply_left] at h1
  exact hij h1.symm

theorem s16t_l4_tensor_fix_or_pure {W : Type} [CommGroup W] {G : Subgroup (MulAut W)}
    (h : IsTensorS3L2 W G 4) {w : W} (hw : w ≠ 1) :
    ∃ φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)),
      (∃ E : Subgroup (MulAut W), E ≤ G ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
          ∀ e ∈ E, (e : MulAut W) w = w) ∨
        ∃ τ : ↥G, τ ≠ 1 ∧ (τ : MulAut W) w = w ∧ (φ τ).2 = 1 := by
  obtain ⟨φ, ψ, hcompat⟩ := h
  let t := Multiplicative.toAdd (ψ w)
  have hwt : ψ w = Multiplicative.ofAdd t := rfl
  have ht : t ≠ 0 := by
    intro h0
    exact hw (ψ.injective (by simp [hwt, h0]))
  obtain ⟨c₁, c₂, hdecomp⟩ := s16t_l4f_tensor_decomp t
  by_cases hind : LinearIndependent (ZMod 2) ![c₁, c₂]
  · obtain ⟨g, k, hg3, hk3, hkne, hcomm_gk, hgc₁, hgc₂, hkc₁, hkc₂⟩ :=
      s16t_l4_gl_pair_of_independent hind
    have hwt' : ψ w = Multiplicative.ofAdd
        (s16t_l4f_a1 ⊗ₜ[ZMod 2] c₁ + s16t_l4f_a2 ⊗ₜ[ZMod 2] c₂) := by
      rw [hwt, hdecomp]
    let q₁ : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
      (s16t_l4f_sigma0, g)
    let q₂ : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) := (1, k)
    have hq₁3 : q₁ ^ 3 = 1 := by
      show (s16t_l4f_sigma0 ^ 3, g ^ 3) = 1
      rw [s16t_l4f_sigma0_pow_three, hg3]
      rfl
    have hq₂3 : q₂ ^ 3 = 1 := by
      show ((1 : Equiv.Perm (Fin 3)) ^ 3, k ^ 3) = 1
      rw [one_pow, hk3]
      rfl
    have hq₁ne : q₁ ≠ 1 := by
      intro hh
      exact s16t_l4f_sigma0_ne_one (congrArg Prod.fst hh)
    have hq₂ne : q₂ ≠ 1 := by
      intro hh
      exact hkne (congrArg Prod.snd hh)
    have hcomm : q₁ * q₂ = q₂ * q₁ := by
      show ((s16t_l4f_sigma0 * 1, g * k) : Equiv.Perm (Fin 3) ×
          Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) =
        (1 * s16t_l4f_sigma0, k * g)
      rw [mul_one, one_mul, hcomm_gk]
    have hq₁_notin : q₁ ∉ Subgroup.zpowers q₂ := by
      intro hmem
      have hmap : (Prod.fst q₁) ∈ (Subgroup.zpowers q₂).map
          (MonoidHom.fst (Equiv.Perm (Fin 3))
            (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))) := ⟨q₁, hmem, rfl⟩
      rw [MonoidHom.map_zpowers] at hmap
      change q₁.1 ∈ Subgroup.zpowers (1 : Equiv.Perm (Fin 3)) at hmap
      rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hmap
      exact s16t_l4f_sigma0_ne_one hmap
    have hdisj := s16t_l4f_disjoint_zpowers_of_prime (by norm_num) hq₁3 hq₁ne hq₁_notin
    have hE := s16t_l4f_closure_pair_elemAbelian_nine hq₁3 hq₂3 hq₁ne hq₂ne hcomm hdisj
    have hfix₁ : (φ.symm q₁ : MulAut W) w = w :=
      s16t_l4f_fix_rank2 hcompat hgc₁ hgc₂ hwt'
    have hfix₂ : (φ.symm q₂ : MulAut W) w = w :=
      s16t_l4f_fix_two_pure hcompat hkc₁ hkc₂ hwt'
    exact ⟨φ, Or.inl (s16t_l4f_transport_e9 hE.1 hE.2
      (s16t_l4f_fix_closure hfix₁ hfix₂))⟩
  · have hdep : c₁ = 0 ∨ c₂ = 0 ∨ c₁ = c₂ := by
      by_contra hcon
      push Not at hcon
      refine hind ((Fintype.linearIndependent_iffₛ (R := ZMod 2) (v := ![c₁, c₂])).mpr
        (fun f g hfg => ?_))
      have hd : (f 0 - g 0) • c₁ + (f 1 - g 1) • c₂ = 0 := by
        have h1 : f 0 • c₁ + f 1 • c₂ = g 0 • c₁ + g 1 • c₂ := by
          simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons] using hfg
        have h2 : (f 0 - g 0) • c₁ + (f 1 - g 1) • c₂ =
            (f 0 • c₁ + f 1 • c₂) - (g 0 • c₁ + g 1 • c₂) := by
          module
        rw [h2, h1, sub_self]
      rcases s16t_l4f_zmod2_eq_zero_or_one (f 0 - g 0) with h0 | h0 <;>
        rcases s16t_l4f_zmod2_eq_zero_or_one (f 1 - g 1) with h1 | h1
      · intro i
        fin_cases i
        · exact sub_eq_zero.mp h0
        · exact sub_eq_zero.mp h1
      · rw [h0, h1, zero_smul, one_smul, zero_add] at hd
        exact (hcon.2.1 hd).elim
      · rw [h0, h1, one_smul, zero_smul, add_zero] at hd
        exact (hcon.1 hd).elim
      · rw [h0, h1, one_smul, one_smul] at hd
        exact (hcon.2.2 (s16t_l4f_eq_of_add_eq_zero hd)).elim
    obtain ⟨a, c, hdecomp'⟩ : ∃ (a : ↥(CFSG.Quasithin.permCore 3)) (c : Fin 4 → ZMod 2),
        t = a ⊗ₜ[ZMod 2] c := by
      rcases hdep with h₁ | h₁ | h₁
      · exact ⟨s16t_l4f_a2, c₂, by simp [hdecomp, h₁]⟩
      · exact ⟨s16t_l4f_a1, c₁, by simp [hdecomp, h₁]⟩
      · exact ⟨s16t_l4f_a1 + s16t_l4f_a2, c₁,
          by rw [hdecomp, h₁, ← TensorProduct.add_tmul]⟩
    have hwt' : ψ w = Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c) := by rw [hwt, hdecomp']
    obtain ⟨i, j, hij, haij⟩ := s16t_l4f_exists_eq_coord (a : Fin 3 → ZMod 2)
    let τ₀ : Equiv.Perm (Fin 3) := Equiv.swap i j
    have hτ : CFSG.Quasithin.permAct τ₀ (a : Fin 3 → ZMod 2) =
        (a : Fin 3 → ZMod 2) := by
      funext l
      show (a : Fin 3 → ZMod 2) (τ₀⁻¹ l) = (a : Fin 3 → ZMod 2) l
      rw [show τ₀⁻¹ = Equiv.swap i j by simp [τ₀]]
      exact Equiv.apply_swap_eq_self haij l
    let q₀ : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) := (τ₀, 1)
    let τ : ↥G := φ.symm q₀
    have hτne : τ ≠ 1 := by
      have hφ' : φ τ = (τ₀, 1) := MulEquiv.apply_symm_apply φ q₀
      intro h1
      have h2 : (τ₀, (1 : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))) = 1 := by
        rw [← hφ', h1, map_one]
      exact s16t_l4f_swap_ne_one hij (congrArg Prod.fst h2)
    have hτfix : (τ : MulAut W) w = w :=
      s16t_l4f_fix_perm_pure hcompat hτ hwt'
    have hφτ2 : (φ τ).2 = 1 := by
      have hφ'' : φ τ = (τ₀, 1) := MulEquiv.apply_symm_apply φ q₀
      simpa using congrArg Prod.snd hφ''
    exact ⟨φ, Or.inr ⟨τ, hτne, hτfix, hφτ2⟩⟩

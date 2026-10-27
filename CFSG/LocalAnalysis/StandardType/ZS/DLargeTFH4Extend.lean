module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFDefs
import CFSG.LocalAnalysis.StandardType.ZS.Monomial
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsOrthGeom
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH4
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases
import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

private def h4PairPolar (i j : Fin 60) : PrimModel.ZAl :=
  dotProduct (PrimModel.h4bTab.coroot i) (PrimModel.h4bTab.root j) *
    dotProduct (PrimModel.h4bTab.coroot j) (PrimModel.h4bTab.root i)

private def h4PairOrd (i j : Fin 60) : ℕ :=
  if h4PairPolar i j = 16 then 1 else if h4PairPolar i j = 0 then 2
    else if h4PairPolar i j = 4 then 3 else 5

private def h4ScaledProd (i j : Fin 60) : Matrix (Fin 4) (Fin 4) PrimModel.ZAl :=
  PrimModel.reflZ (PrimModel.h4bTab.root i) (PrimModel.h4bTab.coroot i) *
    PrimModel.reflZ (PrimModel.h4bTab.root j) (PrimModel.h4bTab.coroot j)

private def h4ScaledPow (e : ℕ) : Matrix (Fin 4) (Fin 4) PrimModel.ZAl :=
  (4 : PrimModel.ZAl) ^ e • (1 : Matrix (Fin 4) (Fin 4) PrimModel.ZAl)

private theorem h4bTab_cls_eq_zero : ∀ i : Fin 60, PrimModel.h4bTab.cls i = 0 := by
  decide +kernel

private theorem h4PairOrd_row_zero : ∀ j : Fin 60,
    h4PairOrd 0 j = 5 ∨ h4PairOrd 0 j = 3 ∨ h4PairOrd 0 j = 2 ∨ h4PairOrd 0 j = 1 := by
  decide +kernel

private theorem h4PairPolar_eq_zero_of_ord :
    ∀ j : Fin 60, h4PairOrd 0 j = 2 → h4PairPolar 0 j = 0 := by
  decide +kernel

private theorem h4ScaledProd_pow_ord : ∀ j : Fin 60,
    h4ScaledProd 0 j ^ h4PairOrd 0 j = h4ScaledPow (h4PairOrd 0 j) := by
  decide +kernel

private def h4PartnerIndex : Fin 60 → Fin 60 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0,
    18, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 18, 0, 18, 0, 30, 46, 33, 0, 0, 0, 0, 21, 21, 21,
    21, 33]

private theorem h4Partner_check : ∀ j : Fin 60, h4PairPolar 0 j = 0 →
    h4ScaledProd (h4PartnerIndex j) 0 ^ 2 = h4ScaledPow 2 ∧
    h4ScaledProd (h4PartnerIndex j) j ^ 3 = h4ScaledPow 3 ∧
    (∃ q : Fin 4 × Fin 4, PrimModel.GoodAl ((h4ScaledProd (h4PartnerIndex j) 0 -
      (4 : PrimModel.ZAl) • (1 : Matrix (Fin 4) (Fin 4) PrimModel.ZAl)) q.1 q.2)) ∧
    (∃ q : Fin 4 × Fin 4, PrimModel.GoodAl ((h4ScaledProd (h4PartnerIndex j) j -
      (4 : PrimModel.ZAl) • (1 : Matrix (Fin 4) (Fin 4) PrimModel.ZAl)) q.1 q.2)) := by
  decide +kernel

private noncomputable abbrev h4Refl (f : Module.Basis (Fin 4) (ZMod p) V) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (i : Fin 60) : V ≃ₗ[ZMod p] V :=
  PrimModel.h4bTab.refl (PrimModel.evalAl hα) f i

private theorem orderOf_refl_mul_dvd_h4PairOrd (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) V) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (j : Fin 60) :
    orderOf (h4Refl f hα 0 * h4Refl f hα j) ∣ h4PairOrd 0 j :=
  orderOf_dvd_of_pow_eq_one (PrimModel.ReflTable.pow_mul_refl_eq_one (T := PrimModel.h4bTab)
    (φ := PrimModel.evalAl hα) (f := f) PrimModel.h4bTab_valid hp (h4ScaledProd_pow_ord j))

private theorem orderOf_conj_mul_conj (a b g : V ≃ₗ[ZMod p] V) :
    orderOf (g * a * g⁻¹ * (g * b * g⁻¹)) = orderOf (a * b) := by
  have h1 : g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  rw [h1]
  exact (SemiconjBy.orderOf_eq g (by unfold SemiconjBy; group)).symm

private theorem orderOf_conj_inv_mul_conj_inv (a b g : V ≃ₗ[ZMod p] V) :
    orderOf (g⁻¹ * a * g * (g⁻¹ * b * g)) = orderOf (a * b) := by
  have h1 : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
  rw [h1]
  exact (SemiconjBy.orderOf_eq g⁻¹ (by unfold SemiconjBy; group)).symm

private theorem reduce_h4_pair_to_row_zero (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) V) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (i k : Fin 60)
    (hxz : orderOf (h4Refl f hα i * h4Refl f hα k) = 2) :
    ∃ (g : V ≃ₗ[ZMod p] V) (k' : Fin 60),
      g ∈ PrimModel.h4bTab.group (PrimModel.evalAl hα) f ∧
      h4Refl f hα 0 = g * h4Refl f hα i * g⁻¹ ∧
      g * h4Refl f hα k * g⁻¹ = h4Refl f hα k' ∧ h4PairPolar 0 k' = 0 := by
  obtain ⟨g, hg, hconj⟩ := PrimModel.ReflTable.exists_conj_of_cls_eq (φ := PrimModel.evalAl hα)
    (f := f) PrimModel.h4bTab_valid hp (j := i) (j' := 0)
      (by rw [h4bTab_cls_eq_zero i, h4bTab_cls_eq_zero 0])
  have hconjR : h4Refl f hα 0 = g * h4Refl f hα i * g⁻¹ := hconj
  let z' : V ≃ₗ[ZMod p] V := g * h4Refl f hα k * g⁻¹
  have hz'G : z' ∈ PrimModel.h4bTab.group (PrimModel.evalAl hα) f := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ hg ?_) (Subgroup.inv_mem _ hg)
    exact PrimModel.ReflTable.refl_mem_group PrimModel.h4bTab_valid hp k
  have hz'r : IsRefl p z' :=
    IsRefl.conj (PrimModel.ReflTable.isRefl_refl PrimModel.h4bTab_valid hp k) g
  have hz'ord : orderOf (h4Refl f hα 0 * z') = 2 := by
    change orderOf (h4Refl f hα 0 * (g * h4Refl f hα k * g⁻¹)) = 2
    rw [hconjR]
    exact (orderOf_conj_mul_conj (h4Refl f hα i) (h4Refl f hα k) g).trans hxz
  obtain ⟨k', hz'eq⟩ := PrimModel.ReflTable.exists_eq_refl PrimModel.h4bTab_valid hp
    (PrimModel.h4b_transvectionFree hp f hα) hz'G hz'r
  have hz'eqR : z' = h4Refl f hα k' := hz'eq
  have h0k' : orderOf (h4Refl f hα 0 * h4Refl f hα k') = 2 := by
    rw [← hz'eqR]; exact hz'ord
  have hq0k' : h4PairPolar 0 k' = 0 := by
    have hd : (2 : ℕ) ∣ h4PairOrd 0 k' := by
      rw [← h0k']; exact orderOf_refl_mul_dvd_h4PairOrd hp f hα k'
    rcases h4PairOrd_row_zero k' with h | h | h | h
    · exfalso; rw [h] at hd; norm_num at hd
    · exfalso; rw [h] at hd; norm_num at hd
    · exact h4PairPolar_eq_zero_of_ord k' h
    · exfalso; rw [h] at hd; norm_num at hd
  exact ⟨g, k', hg, hconjR, hz'eqR, hq0k'⟩

private theorem exists_h4_partner (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) V) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (k' : Fin 60) (hq : h4PairPolar 0 k' = 0) :
    ∃ l : Fin 60, orderOf (h4Refl f hα l * h4Refl f hα 0) = 2 ∧
      orderOf (h4Refl f hα l * h4Refl f hα k') = 3 := by
  obtain ⟨hid0, hidk, hgood0, hgoodk⟩ := h4Partner_check k' hq
  let l : Fin 60 := h4PartnerIndex k'
  have hdvl0 : orderOf (h4Refl f hα l * h4Refl f hα 0) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (PrimModel.ReflTable.pow_mul_refl_eq_one (T := PrimModel.h4bTab)
      (φ := PrimModel.evalAl hα) (f := f) PrimModel.h4bTab_valid hp hid0)
  have hdvlk : orderOf (h4Refl f hα l * h4Refl f hα k') ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (PrimModel.ReflTable.pow_mul_refl_eq_one (T := PrimModel.h4bTab)
      (φ := PrimModel.evalAl hα) (f := f) PrimModel.h4bTab_valid hp hidk)
  obtain ⟨q0, hg0⟩ := hgood0
  obtain ⟨qk, hgk⟩ := hgoodk
  have hnel0 : h4Refl f hα l * h4Refl f hα 0 ≠ 1 :=
    PrimModel.ReflTable.mul_refl_ne_one (T := PrimModel.h4bTab) (φ := PrimModel.evalAl hα)
      (f := f) PrimModel.h4bTab_valid (fun x hx => PrimModel.evalAl_ne_zero hp hα hx) hp
      (i := l) (j := 0) (a := q0.1) (b := q0.2) hg0
  have hnelk : h4Refl f hα l * h4Refl f hα k' ≠ 1 :=
    PrimModel.ReflTable.mul_refl_ne_one (T := PrimModel.h4bTab) (φ := PrimModel.evalAl hα)
      (f := f) PrimModel.h4bTab_valid (fun x hx => PrimModel.evalAl_ne_zero hp hα hx) hp
      (i := l) (j := k') (a := qk.1) (b := qk.2) hgk
  have hordl0' : orderOf (h4Refl f hα l * h4Refl f hα 0) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvl0 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hnel0
    · exact h
  have hordlk' : orderOf (h4Refl f hα l * h4Refl f hα k') = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvlk with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hnelk
    · exact h
  exact ⟨l, hordl0', hordlk'⟩

theorem exists_isRefl_extend_basisClosure_h4BlockMats (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) V) {α : ZMod p} (hα : α ^ 2 = α + 1)
    {x z : V ≃ₗ[ZMod p] V} (hx : x ∈ basisClosure f (h4BlockMats α))
    (hz : z ∈ basisClosure f (h4BlockMats α)) (hxr : IsRefl p x) (hzr : IsRefl p z)
    (hxz : orderOf (x * z) = 2) :
    ∃ w ∈ basisClosure f (h4BlockMats α), IsRefl p w ∧ orderOf (w * x) = 2 ∧
      orderOf (w * z) = 3 := by
  rw [PrimModel.h4b_basisClosure_eq hp f hα] at hx hz ⊢
  obtain ⟨i, rfl⟩ := PrimModel.ReflTable.exists_eq_refl PrimModel.h4bTab_valid hp
    (PrimModel.h4b_transvectionFree hp f hα) hx hxr
  obtain ⟨k, rfl⟩ := PrimModel.ReflTable.exists_eq_refl PrimModel.h4bTab_valid hp
    (PrimModel.h4b_transvectionFree hp f hα) hz hzr
  obtain ⟨g, k', hg, hconj, hk'eq, hq0k'⟩ := reduce_h4_pair_to_row_zero hp f hα i k hxz
  obtain ⟨l, hordl0', hordlk'⟩ := exists_h4_partner hp f hα k' hq0k'
  refine ⟨g⁻¹ * h4Refl f hα l * g, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg)
      (PrimModel.ReflTable.refl_mem_group PrimModel.h4bTab_valid hp l)) hg
  · exact IsRefl.conj (PrimModel.ReflTable.isRefl_refl PrimModel.h4bTab_valid hp l) g⁻¹
  · have hRi : h4Refl f hα i = g⁻¹ * h4Refl f hα 0 * g := by rw [hconj]; group
    change orderOf (g⁻¹ * h4Refl f hα l * g * h4Refl f hα i) = 2
    rw [hRi]
    rw [orderOf_conj_inv_mul_conj_inv]
    exact hordl0'
  · have hRk : h4Refl f hα k = g⁻¹ * h4Refl f hα k' * g := by rw [← hk'eq]; group
    change orderOf (g⁻¹ * h4Refl f hα l * g * h4Refl f hα k) = 3
    rw [hRk]
    rw [orderOf_conj_inv_mul_conj_inv]
    exact hordlk'

private theorem pow_eq_diagMap_mul_permMap {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    ∃ d' : Fin n → (ZMod p)ˣ,
      (diagMap p f d * permMap p f σ) ^ k = diagMap p f d' * permMap p f (σ ^ k) := by
  induction k with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero, diagMap_one, permMap_one, mul_one]⟩
  | succ k ih =>
      obtain ⟨d', hd'⟩ := ih
      refine ⟨d' * (d ∘ (σ ^ k).symm), ?_⟩
      rw [pow_succ, hd', mul_diagMap_permMap, pow_succ]

private theorem perm_pow_eq_one_of_monomial_pow_eq_one {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)) {k : ℕ}
    (h : (diagMap p f d * permMap p f σ) ^ k = 1) : σ ^ k = 1 := by
  obtain ⟨d', hd'⟩ := pow_eq_diagMap_mul_permMap f d σ k
  have key : diagMap p f d' * permMap p f (σ ^ k) = diagMap p f 1 * permMap p f 1 := by
    rw [← hd', h, diagMap_one, permMap_one, mul_one]
  exact (eq_of_diagMap_mul_permMap_eq f key).2

private theorem swap_mul_swap_pow_six {n : ℕ} {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) :
    (Equiv.swap a b * Equiv.swap c d) ^ 6 = 1 := by
  by_cases hca : c = a
  · subst c
    by_cases hdb : d = b
    · subst d; rw [Equiv.swap_mul_self]; simp
    · have h3 : (Equiv.swap a b * Equiv.swap a d) ^ 3 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one,
          (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hcd (Ne.symm hdb)).orderOf]
      rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h3, one_pow]
  · by_cases hda : d = a
    · subst d
      rw [Equiv.swap_comm c a]
      by_cases hcb : c = b
      · subst c; rw [Equiv.swap_mul_self]; simp
      · have h3 : (Equiv.swap a b * Equiv.swap a c) ^ 3 = 1 := by
          rw [← orderOf_dvd_iff_pow_eq_one,
            (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab (Ne.symm hca)
              (Ne.symm hcb)).orderOf]
        rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h3, one_pow]
    · by_cases hcb : c = b
      · subst c
        rw [Equiv.swap_comm a b]
        have h3 : (Equiv.swap b a * Equiv.swap b d) ^ 3 = 1 := by
          rw [← orderOf_dvd_iff_pow_eq_one,
            (Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hab) hcd
              (Ne.symm hda)).orderOf]
        rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h3, one_pow]
      · by_cases hdb : d = b
        · subst d
          rw [Equiv.swap_comm c b, Equiv.swap_comm a b]
          have h3 : (Equiv.swap b a * Equiv.swap b c) ^ 3 = 1 := by
            rw [← orderOf_dvd_iff_pow_eq_one,
              (Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hab) (Ne.symm hcb)
                (Ne.symm hca)).orderOf]
          rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h3, one_pow]
        · have hnodup : [a, b, c, d].Nodup := by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
              List.nodup_nil, and_true]
            tauto
          have hdisj : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d) :=
            Equiv.Perm.disjoint_swap_swap hnodup
          have h2 : orderOf (Equiv.swap a b * Equiv.swap c d) = 2 := by
            rw [hdisj.orderOf, (Equiv.Perm.swap_isSwap_iff.mpr hab).orderOf,
              (Equiv.Perm.swap_isSwap_iff.mpr hcd).orderOf]
            simp
          rw [← orderOf_dvd_iff_pow_eq_one, h2]
          norm_num

private theorem perm_pow_six_of_eq_one_or_isSwap {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (hσ : σ = 1 ∨ σ.IsSwap) (hτ : τ = 1 ∨ τ.IsSwap) : (σ * τ) ^ 6 = 1 := by
  rcases hσ with rfl | hσ
  · rw [one_mul]
    rcases hτ with rfl | hτ
    · simp
    · rw [← orderOf_dvd_iff_pow_eq_one, hτ.orderOf]; norm_num
  · rcases hτ with rfl | hτ
    · rw [mul_one, ← orderOf_dvd_iff_pow_eq_one, hσ.orderOf]; norm_num
    · obtain ⟨a, b, hab, rfl⟩ := hσ
      obtain ⟨c, d, hcd, rfl⟩ := hτ
      exact swap_mul_swap_pow_six hab hcd

private theorem mul_self_of_eq_one_or_isSwap {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : σ = 1 ∨ σ.IsSwap) : σ * σ = 1 := by
  rcases hσ with rfl | hσ
  · simp
  · have h2 : σ ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hσ.orderOf]
    simpa [pow_two] using h2

private theorem perm_eq_of_pow_five {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (hσ : σ = 1 ∨ σ.IsSwap) (hτ : τ = 1 ∨ τ.IsSwap) (h5 : (σ * τ) ^ 5 = 1) : σ = τ := by
  have h6 : (σ * τ) ^ 6 = 1 := perm_pow_six_of_eq_one_or_isSwap hσ hτ
  have h1 : σ * τ = 1 := by
    have h : (σ * τ) ^ 5 * (σ * τ) = 1 := by
      rw [← pow_succ, show (5 + 1 : ℕ) = 6 from rfl, h6]
    simpa [h5] using h
  calc σ = σ * (σ * τ) := by rw [h1, mul_one]
    _ = (σ * σ) * τ := by rw [mul_assoc]
    _ = τ := by rw [mul_self_of_eq_one_or_isSwap hσ, one_mul]

private theorem refl_data_of_monomial (hp : p ≠ 2) {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    {r : V ≃ₗ[ZMod p] V} (hrr : IsRefl p r)
    (hmon : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, r (f i) = c i • f (σ i)) :
    ∃ (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)),
      r = diagMap p f d * permMap p f σ ∧ (σ = 1 ∨ σ.IsSwap) := by
  rcases eq_sign_or_eq_twist_of_isRefl hp f hrr hmon with ⟨k, hk⟩ | ⟨i, j, hij, c, hc⟩
  · exact ⟨fun l => if l = k then (-1 : (ZMod p)ˣ) else 1, 1,
      by rw [permMap_one, mul_one]; exact hk, Or.inl rfl⟩
  · exact ⟨pairUnit p i j c, Equiv.swap i j, hc, Or.inr ⟨i, j, hij, rfl⟩⟩

private theorem sigma_eq_of_h3Triple_monomial {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    {x y z : V ≃ₗ[ZMod p] V} {dx dy dz : Fin n → (ZMod p)ˣ}
    {σx σy σz : Equiv.Perm (Fin n)}
    (hx_eq : x = diagMap p f dx * permMap p f σx)
    (hy_eq : y = diagMap p f dy * permMap p f σy)
    (hz_eq : z = diagMap p f dz * permMap p f σz)
    (hx_perm : σx = 1 ∨ σx.IsSwap) (hy_perm : σy = 1 ∨ σy.IsSwap)
    (hxy5 : (x * y) ^ 5 = 1) (hyz3 : (y * z) ^ 3 = 1) (hxz2 : (x * z) ^ 2 = 1) :
    σx = σy ∧ σy = σz := by
  have hσxy5 : (σx * σy) ^ 5 = 1 := by
    refine perm_pow_eq_one_of_monomial_pow_eq_one f (dx * (dy ∘ σx.symm)) (σx * σy) ?_
    rw [← mul_diagMap_permMap, ← hx_eq, ← hy_eq]
    exact hxy5
  have hσyz3 : (σy * σz) ^ 3 = 1 := by
    refine perm_pow_eq_one_of_monomial_pow_eq_one f (dy * (dz ∘ σy.symm)) (σy * σz) ?_
    rw [← mul_diagMap_permMap, ← hy_eq, ← hz_eq]
    exact hyz3
  have hσxz2 : (σx * σz) ^ 2 = 1 := by
    refine perm_pow_eq_one_of_monomial_pow_eq_one f (dx * (dz ∘ σx.symm)) (σx * σz) ?_
    rw [← mul_diagMap_permMap, ← hx_eq, ← hz_eq]
    exact hxz2
  have hxy_eq : σx = σy := perm_eq_of_pow_five hx_perm hy_perm hσxy5
  have h2 : (σy * σz) ^ 2 = 1 := by rw [← hxy_eq]; exact hσxz2
  have hyz_eq : σy = σz := by
    have hu : σy * σz = 1 := by
      calc σy * σz = (σy * σz) ^ 2 * (σy * σz) := by rw [h2, one_mul]
        _ = (σy * σz) ^ 3 := (pow_succ (σy * σz) 2).symm
        _ = 1 := hσyz3
    calc σy = σy * (σy * σz) := by rw [hu, mul_one]
      _ = (σy * σy) * σz := by rw [mul_assoc]
      _ = σz := by rw [mul_self_of_eq_one_or_isSwap hy_perm, one_mul]
  exact ⟨hxy_eq, hyz_eq⟩

private theorem orderOf_coe_mul {G : Type*} [Group G] {H : Subgroup G} (x y : H) :
    orderOf ((x : G) * (y : G)) = orderOf (x * y) := by
  rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]

private theorem restr_order {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    {B : Subgroup (W ≃ₗ[ZMod p] W)} {l : ℕ} (hs : SplitSupport B l) (u v : B) :
    orderOf (restrictHom B (HardMathSupport.Kantor79.commutatorSpace B)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) u *
      restrictHom B (HardMathSupport.Kantor79.commutatorSpace B)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) v) =
      orderOf ((u : W ≃ₗ[ZMod p] W) * (v : W ≃ₗ[ZMod p] W)) := by
  rw [← map_mul, orderOf_injective _ (restrictHom_injective_of_splitSupport hs),
    ← orderOf_coe_mul u v]

private theorem model_h4_of_dLargeFourModel {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    [Module.Finite (ZMod p) W] {B : Subgroup (W ≃ₗ[ZMod p] W)}
    (hs : SplitSupport B 4) (hD5 : DMax p B 5) (hp2 : p ≠ 2) (hp5 : 5 < p)
    (h4 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) = 4)
    (hL : DLargeFourModel p) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup B))
    (hTF : QTwoLin.TransvectionFree B) (hR : ReflGen p B)
    (hpair : ∃ a ∈ movedGroup B, ∃ b ∈ movedGroup B,
      IsRefl p a ∧ IsRefl p b ∧ 3 < orderOf (a * b)) :
    ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace B)),
      α ^ 2 = α + 1 ∧ movedGroup B = basisClosure f (h4BlockMats α) := by
  let V := HardMathSupport.Kantor79.commutatorSpace B
  let _ : Module.Finite (ZMod p) V := Module.Finite.of_injective V.subtype V.subtype_injective
  have hD5' : DMax p (movedGroup B) 5 := (dmax_movedGroup_iff hs 5).mpr hD5
  rcases hL V (movedGroup B) hp2 h4 (reflGen_movedGroup hR) (absIrred_movedGroup hR hs) hprim
      (transvectionFree_movedGroup hs hTF) hpair with
    hOrth | ⟨hD4, _fN, _t, _ht, _hN4⟩ | ⟨_hp3, hD4, _f4, _hF4⟩ | ⟨_hp5, _hD5, α, f, hα, hH4⟩
  · exfalso
    obtain ⟨a, ha, b, hb, har, hbr, habp⟩ :=
      CFSG.StandardType.ZS.TableFacts.exists_pair_orderOf_eq_of_isOrthType
        (V := V) hp2 (by have h : Module.finrank (ZMod p) V = 4 := h4; omega) hOrth
    exact absurd (hD5'.1 a ha b hb har hbr) (by omega)
  · exfalso
    obtain ⟨a, ha, b, hb, har, hbr, _h5⟩ := hD5'.2
    exact absurd (hD4.1 a ha b hb har hbr) (by omega)
  · exfalso
    obtain ⟨a, ha, b, hb, har, hbr, _h5⟩ := hD5'.2
    exact absurd (hD4.1 a ha b hb har hbr) (by omega)
  · exact ⟨α, f, hα, hH4⟩

private theorem lift_h4_of_dLargeFourModel {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    [Module.Finite (ZMod p) W] {B : Subgroup (W ≃ₗ[ZMod p] W)}
    (hs : SplitSupport B 4) {x z : W ≃ₗ[ZMod p] W} (hx : x ∈ B) (hz : z ∈ B)
    (hxr : IsRefl p x) (hzr : IsRefl p z) (hxz : orderOf (x * z) = 2)
    {α : ZMod p} (hα : α ^ 2 = α + 1)
    {f : Module.Basis (Fin 4) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    (hH4 : movedGroup B = basisClosure f (h4BlockMats α)) (hp2 : p ≠ 2) :
    ∃ w ∈ B, IsRefl p w ∧ orderOf (w * x) = 2 ∧ orderOf (w * z) = 3 := by
  let V := HardMathSupport.Kantor79.commutatorSpace B
  let φ := restrictHom B V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hs
  have hord : ∀ g : B, orderOf (φ g) = orderOf g := fun g => orderOf_injective φ hinj g
  have hxb : IsRefl p (φ ⟨x, hx⟩) :=
    isRefl_restrictHom_of_isRefl (X := B) hs (x := ⟨x, hx⟩) hxr
  have hzb : IsRefl p (φ ⟨z, hz⟩) :=
    isRefl_restrictHom_of_isRefl (X := B) hs (x := ⟨z, hz⟩) hzr
  have hxzV : orderOf (φ ⟨x, hx⟩ * φ ⟨z, hz⟩) = 2 := by
    rw [restr_order hs ⟨x, hx⟩ ⟨z, hz⟩]; simpa using hxz
  have hxb' : φ ⟨x, hx⟩ ∈ basisClosure f (h4BlockMats α) := by
    rw [← hH4]; exact ⟨⟨x, hx⟩, rfl⟩
  have hzb' : φ ⟨z, hz⟩ ∈ basisClosure f (h4BlockMats α) := by
    rw [← hH4]; exact ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨wbar, hwbar_mem, hwbar_refl, howx, howz⟩ :=
    exists_isRefl_extend_basisClosure_h4BlockMats hp2 f hα hxb' hzb' hxb hzb hxzV
  have hwbar_mem' : wbar ∈ movedGroup B := hH4.symm ▸ hwbar_mem
  obtain ⟨wB, hwB_eq⟩ := MonoidHom.mem_range.mp (show wbar ∈ φ.range from hwbar_mem')
  refine ⟨(wB : W ≃ₗ[ZMod p] W), wB.2, ?_, ?_, ?_⟩
  · exact isRefl_of_isRefl_restrictHom (X := B) hs
      (by show IsRefl p (φ wB); rw [hwB_eq]; exact hwbar_refl)
  · change orderOf ((wB : W ≃ₗ[ZMod p] W) * (⟨x, hx⟩ : B)) = 2
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe, ← hord (wB * ⟨x, hx⟩), map_mul, hwB_eq, howx]
  · change orderOf ((wB : W ≃ₗ[ZMod p] W) * (⟨z, hz⟩ : B)) = 3
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe, ← hord (wB * ⟨z, hz⟩), map_mul, hwB_eq, howz]

theorem false_of_isImprimitiveOnV_of_h3Triple (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    {B : Subgroup (V ≃ₗ[ZMod p] V)} (hR : ReflGen p B)
    (hA : AbsIrred p B) (himp : Quasithin.SimsG4.IsImprimitiveOnV B) {x y z : V ≃ₗ[ZMod p] V}
    (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B) (hxr : IsRefl p x) (hyr : IsRefl p y)
    (hzr : IsRefl p z) (hxy : orderOf (x * y) = 5) (hyz : orderOf (y * z) = 3)
    (hxz : orderOf (x * z) = 2) : False := by
  obtain ⟨f₀, hmon₀⟩ := CFSG.StandardType.ggRC_monomial_of_imprimitive
    (V := V) (n := Module.finrank (ZMod p) V) rfl B hA hR himp
  obtain ⟨f, hmon, -, -⟩ := CFSG.StandardType.ggRC_monomial_frame hp f₀ B hA hR hmon₀
  obtain ⟨dx, σx, hx_eq, hx_perm⟩ := refl_data_of_monomial hp f hxr (hmon x hx)
  obtain ⟨dy, σy, hy_eq, hy_perm⟩ := refl_data_of_monomial hp f hyr (hmon y hy)
  obtain ⟨dz, σz, hz_eq, hz_perm⟩ := refl_data_of_monomial hp f hzr (hmon z hz)
  obtain ⟨hxy_eq, hyz_eq⟩ := sigma_eq_of_h3Triple_monomial f hx_eq hy_eq hz_eq hx_perm hy_perm
    (by rw [← hxy, pow_orderOf_eq_one]) (by rw [← hyz, pow_orderOf_eq_one])
    (by rw [← hxz, pow_orderOf_eq_one])
  have hxy_diag : x * y = diagMap p f (dx * (dy ∘ σx.symm)) := by
    rw [hx_eq, hy_eq, mul_diagMap_permMap, ← hxy_eq, mul_self_of_eq_one_or_isSwap hx_perm,
      permMap_one, mul_one]
  have hyz_diag : y * z = diagMap p f (dy * (dz ∘ σy.symm)) := by
    rw [hy_eq, hz_eq, mul_diagMap_permMap, ← hyz_eq, mul_self_of_eq_one_or_isSwap hy_perm,
      permMap_one, mul_one]
  have hcomm : Commute (x * y) (y * z) := by
    show (x * y) * (y * z) = (y * z) * (x * y)
    rw [hxy_diag, hyz_diag, diagMap_mul, diagMap_mul]
    exact congrArg (diagMap p f) (mul_comm _ _)
  have hxz_eq : x * z = (x * y) * (y * z) := by
    rw [mul_assoc, ← mul_assoc y y z, hyr.1, one_mul]
  have hcop : (orderOf (x * y)).Coprime (orderOf (y * z)) := by rw [hxy, hyz]; norm_num
  have hord15 : orderOf ((x * y) * (y * z)) = 15 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hxy, hyz]
  have h15 : orderOf (x * z) = 15 := by rw [hxz_eq, hord15]
  omega

theorem tfH4Extend_of_dLargeFourModel (hL : DLargeFourModel p) : TFH4Extend p := by
  intro W _ _ _ B hp5 hR hTF hs hD5 _hCen x hx y hy z hz hxr hyr hzr hxy hyz hxz
  have hp2 : p ≠ 2 := by omega
  let V := HardMathSupport.Kantor79.commutatorSpace B
  let φ := restrictHom B V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hfour : Module.finrank (ZMod p) V = 4 := hs.2.1
  let _ : Module.Finite (ZMod p) V := Module.Finite.of_injective V.subtype V.subtype_injective
  have hxb : IsRefl p (φ ⟨x, hx⟩) :=
    isRefl_restrictHom_of_isRefl (X := B) hs (x := ⟨x, hx⟩) hxr
  have hyb : IsRefl p (φ ⟨y, hy⟩) :=
    isRefl_restrictHom_of_isRefl (X := B) hs (x := ⟨y, hy⟩) hyr
  have hxyV : orderOf (φ ⟨x, hx⟩ * φ ⟨y, hy⟩) = 5 := by
    rw [restr_order hs ⟨x, hx⟩ ⟨y, hy⟩]; simpa using hxy
  by_cases himp : Quasithin.SimsG4.IsImprimitiveOnV (movedGroup B)
  · refine (false_of_isImprimitiveOnV_of_h3Triple hp2
      (reflGen_movedGroup hR) (absIrred_movedGroup hR hs) himp
      ⟨⟨x, hx⟩, rfl⟩ ⟨⟨y, hy⟩, rfl⟩ ⟨⟨z, hz⟩, rfl⟩ hxb hyb
      (isRefl_restrictHom_of_isRefl (X := B) hs (x := ⟨z, hz⟩) hzr) hxyV ?_ ?_).elim
    · rw [restr_order hs ⟨y, hy⟩ ⟨z, hz⟩]; simpa using hyz
    · rw [restr_order hs ⟨x, hx⟩ ⟨z, hz⟩]; simpa using hxz
  · have hpair : ∃ a ∈ movedGroup B, ∃ b ∈ movedGroup B,
        IsRefl p a ∧ IsRefl p b ∧ 3 < orderOf (a * b) :=
      ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, φ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, hxb, hyb,
        by rw [hxyV]; norm_num⟩
    obtain ⟨α, f5, hα, hH4⟩ := model_h4_of_dLargeFourModel hs hD5 hp2 hp5 hfour hL himp hTF hR hpair
    exact lift_h4_of_dLargeFourModel hs hx hz hxr hzr hxz hα hH4 hp2

end CFSG.StandardType.ZS

end

module

import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars

public section

namespace CFSG.RankThree.GF2n.Stroth80

section OmegaScalars

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix commutatorElement

section Homogeneous

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private def homSubmodule (f : V →+ V) : Submodule K V where
  carrier := {v | ∀ l : K, f (l • v) = l • f v}
  zero_mem' := fun l => by simp
  add_mem' := fun {v w} hv hw l => by
    rw [smul_add, map_add, hv l, hw l, map_add, smul_add]
  smul_mem' := fun c v hv l => by
    rw [smul_smul, hv (l * c), hv c, smul_smul]

private theorem eq_smul_of_basis {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → K) →+ (ι → K)) (a : K)
    (hhom : ∀ k : ι, (Pi.single k (1 : K) : ι → K) ∈ homSubmodule (K := K) f)
    (heig : ∀ k : ι, f (Pi.single k (1 : K)) = a • (Pi.single k (1 : K) : ι → K))
    (v : ι → K) : f v = a • v := by
  have hdec : v = ∑ k, v k • (Pi.single k (1 : K) : ι → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hdec, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hhom k (v k), heig k, smul_comm]

end Homogeneous

section Eichler

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem eq_smul_of_commute_eichler (f : V →+ V) {u w x : V} (hu : Q u = 0)
    (hw : polar Q u w = 0) (hxu : polar Q x u = 0) (hxw : polar Q x w = 1) (l : K)
    (hE : f (eichler Q u (l • w) x) = eichler Q u (l • w) (f x)) :
    f (l • u) = (-(l * polar Q (f x) u)) • w +
      (l * polar Q (f x) w + l ^ 2 * Q w * polar Q (f x) u) • u := by
  have hl : polar Q u (l • w) = 0 := by rw [polar_smul_right_eq, hw, mul_zero]
  rw [eichler_apply hu hl x, eichler_apply hu hl (f x)] at hE
  simp only [hxu, hxw, polar_smul_right_eq, map_smul_eq_sq, zero_smul, add_zero, mul_zero,
    mul_one, map_sub] at hE
  linear_combination (norm := module) (-1 : K) • hE

private theorem mem_homSubmodule_of_commute_eichler (f : V →+ V) {u w₀ w₁ x₀ x₁ : V} (hu : Q u = 0)
    (hw₀ : polar Q u w₀ = 0) (hw₁ : polar Q u w₁ = 0)
    (hx₀u : polar Q x₀ u = 0) (hx₀ : polar Q x₀ w₀ = 1)
    (hx₁u : polar Q x₁ u = 0) (hx₁ : polar Q x₁ w₁ = 1)
    (hind : ∀ a b c : K, a • u + b • w₀ + c • w₁ = 0 → b = 0 ∧ c = 0)
    (hE₀ : ∀ l : K, f (eichler Q u (l • w₀) x₀) = eichler Q u (l • w₀) (f x₀))
    (hE₁ : ∀ l : K, f (eichler Q u (l • w₁) x₁) = eichler Q u (l • w₁) (f x₁)) :
    u ∈ homSubmodule (K := K) f ∧ ∃ γ : K, f u = γ • u := by
  have h0 := fun l : K => eq_smul_of_commute_eichler f hu hw₀ hx₀u hx₀ l (hE₀ l)
  have h1 := fun l : K => eq_smul_of_commute_eichler f hu hw₁ hx₁u hx₁ l (hE₁ l)
  have h0' := h0 1
  have h1' := h1 1
  simp only [one_smul, one_mul, one_pow] at h0' h1'
  have hβ := hind ((polar Q (f x₀) w₀ + Q w₀ * polar Q (f x₀) u) -
      (polar Q (f x₁) w₁ + Q w₁ * polar Q (f x₁) u)) (-polar Q (f x₀) u) (polar Q (f x₁) u)
    (by linear_combination (norm := module) (-1 : K) • h0' + (1 : K) • h1')
  have hb0 : polar Q (f x₀) u = 0 := neg_eq_zero.mp hβ.1
  refine ⟨fun l => ?_, polar Q (f x₀) w₀, ?_⟩
  · have e1 := h0 l
    rw [hb0] at e1 h0'
    rw [e1, h0']
    module
  · rw [hb0] at h0'
    rw [h0']
    module

private theorem exists_perp_polar_eq_one (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {x : V} (hx : x ∈ P.perp) (hx0 : x ≠ 0) : ∃ y ∈ P.perp, polar Q x y = 1 := by
  obtain ⟨y₀, hy₀, hne⟩ := (HypPair.polarNondegOn_perp hQ P).exists_polar_ne_zero hx hx0
  exact ⟨(polar Q x y₀)⁻¹ • y₀, P.perp.smul_mem _ hy₀, by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hne]⟩

private theorem eichler_mem_commutator_of_perp (hQ : (polarBilin Q).Nondegenerate)
    (P : HypPair Q) {u x : V} (hpu : ∀ y ∈ P.perp, polar Q u y = 0) (hx : x ∈ P.perp)
    (hQx : Q x ≠ 0) :
    eichler Q u x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hx0 : x ≠ 0 := fun h => hQx (by rw [h, QuadraticMap.map_zero])
  obtain ⟨y₁, hy₁, hxy₁⟩ := exists_perp_polar_eq_one hQ P hx hx0
  obtain ⟨y, hyP, hxy⟩ : ∃ y ∈ P.perp, polar Q x y = -Q x :=
    ⟨(-Q x) • y₁, P.perp.smul_mem _ hy₁, by rw [polar_smul_right_eq, hxy₁, mul_one]⟩
  have hxu : polar Q x u = 0 := by rw [polar_comm]; exact hpu x hx
  have hgu : reflect Q x u = u := reflect_apply_of_polar_eq_zero hxu
  have hr : reflect Q x y - y = x := by
    rw [reflect_apply hQx, hxy, neg_div, div_self hQx, neg_one_smul]
    abel
  have hc := commutatorElement_eichler (reflect_mem_orthogonalGroup Q x) hgu (hpu y hyP)
  rw [hr] at hc
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q x)
    (eichler_mem_orthogonalGroup Q u y)

private theorem eichler_smul_mem_commutator (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {u w : V} (hpu : ∀ y ∈ P.perp, polar Q u y = 0) (hw : w ∈ P.perp) (hQw : Q w ≠ 0) (l : K) :
    eichler Q u (l • w) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  by_cases hl : l = 0
  · rw [hl, zero_smul, eichler_zero_right]
    exact Subgroup.one_mem _
  · refine eichler_mem_commutator_of_perp hQ P hpu (P.perp.smul_mem l hw) ?_
    rw [map_smul_eq_sq]
    exact mul_ne_zero (pow_ne_zero 2 hl) hQw

private theorem hyp_mem_homSubmodule (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    (f : V →+ V)
    (hf : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, ∀ v, f (g v) = g (f v))
    {w₀ w₁ : V} (hw₀ : w₀ ∈ P.perp) (hw₁ : w₁ ∈ P.perp) (hQ₀ : Q w₀ ≠ 0) (hQ₁ : Q w₁ ≠ 0)
    (hindE : ∀ a b c : K, a • P.e + b • w₀ + c • w₁ = 0 → b = 0 ∧ c = 0)
    (hindF : ∀ a b c : K, a • P.f + b • w₀ + c • w₁ = 0 → b = 0 ∧ c = 0) :
    (P.e ∈ homSubmodule (K := K) f ∧ ∃ γ : K, f P.e = γ • P.e) ∧
      (P.f ∈ homSubmodule (K := K) f ∧ ∃ γ : K, f P.f = γ • P.f) := by
  have hw₀0 : w₀ ≠ 0 := fun h => hQ₀ (by rw [h, QuadraticMap.map_zero])
  have hw₁0 : w₁ ≠ 0 := fun h => hQ₁ (by rw [h, QuadraticMap.map_zero])
  obtain ⟨x₀, hx₀P, hx₀⟩ := exists_perp_polar_eq_one hQ P hw₀ hw₀0
  obtain ⟨x₁, hx₁P, hx₁⟩ := exists_perp_polar_eq_one hQ P hw₁ hw₁0
  have hpe : ∀ y ∈ P.perp, polar Q P.e y = 0 := fun y hy => (HypPair.mem_perp.mp hy).1
  have hpf : ∀ y ∈ P.perp, polar Q P.f y = 0 := fun y hy => (HypPair.mem_perp.mp hy).2
  have hx₀' : polar Q x₀ w₀ = 1 := by rw [polar_comm]; exact hx₀
  have hx₁' : polar Q x₁ w₁ = 1 := by rw [polar_comm]; exact hx₁
  refine ⟨mem_homSubmodule_of_commute_eichler f P.Q_e (hpe _ hw₀) (hpe _ hw₁)
    (by rw [polar_comm]; exact hpe _ hx₀P) hx₀' (by rw [polar_comm]; exact hpe _ hx₁P) hx₁'
    hindE (fun l => hf _ (eichler_smul_mem_commutator hQ P hpe hw₀ hQ₀ l) x₀)
    (fun l => hf _ (eichler_smul_mem_commutator hQ P hpe hw₁ hQ₁ l) x₁),
    mem_homSubmodule_of_commute_eichler f P.Q_f (hpf _ hw₀) (hpf _ hw₁)
    (by rw [polar_comm]; exact hpf _ hx₀P) hx₀' (by rw [polar_comm]; exact hpf _ hx₁P) hx₁'
    hindF (fun l => hf _ (eichler_smul_mem_commutator hQ P hpf hw₀ hQ₀ l) x₀)
    (fun l => hf _ (eichler_smul_mem_commutator hQ P hpf hw₁ hQ₁ l) x₁)⟩

private theorem eq_smul_of_perp (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) (f : V →+ V)
    (hf : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, ∀ v, f (g v) = g (f v))
    (he : P.e ∈ homSubmodule (K := K) f) (hfm : P.f ∈ homSubmodule (K := K) f) {a b : K}
    (hfe : f P.e = a • P.e) (hff : f P.f = b • P.f) {x : V} (hx : x ∈ P.perp)
    (hQx : Q x ≠ 0) : b = a ∧ f x = a • x := by
  have hxe : polar Q P.e x = 0 := (HypPair.mem_perp.mp hx).1
  have hxf : polar Q P.f x = 0 := (HypPair.mem_perp.mp hx).2
  have hpe : ∀ y ∈ P.perp, polar Q P.e y = 0 := fun y hy => (HypPair.mem_perp.mp hy).1
  have hpf : ∀ y ∈ P.perp, polar Q P.f y = 0 := fun y hy => (HypPair.mem_perp.mp hy).2
  have hEe := eichler_mem_commutator_of_perp hQ P hpe hx hQx
  have hEf := eichler_mem_commutator_of_perp hQ P hpf hx hQx
  have hEef : eichler Q P.e x P.f = P.f + x - Q x • P.e := by
    rw [eichler_apply P.Q_e hxe P.f, P.polar_fe, hxf]
    module
  have hEfe : eichler Q P.f x P.e = P.e + x - Q x • P.f := by
    rw [eichler_apply P.Q_f hxf P.e, P.polar_ef, hxe]
    module
  have h1 : f x = b • x + (Q x * (a - b)) • P.e := by
    have h := hf _ hEe P.f
    rw [hEef, hff, map_smul, hEef, map_sub, map_add, hff, he (Q x), hfe] at h
    linear_combination (norm := module) h
  have h2 : f x = a • x + (Q x * (b - a)) • P.f := by
    have h := hf _ hEf P.e
    rw [hEfe, hfe, map_smul, hEfe, map_sub, map_add, hfe, hfm (Q x), hff] at h
    linear_combination (norm := module) h
  have hba : b = a := by
    have e1 : polar Q P.e (f x) = 0 := by
      rw [h1, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxe, P.polar_ee]
      ring
    have e2 : polar Q P.e (f x) = Q x * (b - a) := by
      rw [h2, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxe, P.polar_ef]
      ring
    have e3 : Q x * (b - a) = 0 := by rw [← e2]; exact e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_left hQx)
  refine ⟨hba, ?_⟩
  rw [h1, hba, sub_self, mul_zero, zero_smul, add_zero]

end Eichler

section Dictionary

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private theorem commute_of_mem_derivedOrthogonal {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) (f : (ι → K) →+ (ι → K))
    (hf : ∀ A ∈ StatedOmega Q₀, ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = (A : Matrix ι ι K) *ᵥ f v)
    {g : (ι → K) ≃ₗ[K] (ι → K)}
    (hg : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) (v : ι → K) : f (g v) = g (f v) := by
  obtain ⟨A, hAg⟩ : ∃ A : GL ι K, toLinEquiv ι K A = g :=
    ⟨(toLinEquiv ι K).symm g, (toLinEquiv ι K).apply_symm_apply g⟩
  have hA : A ∈ StatedOmega Q₀ := by
    rw [statedOmega_eq_comap hQ, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hAg]
    exact hg
  have hgA : ∀ w, g w = (A : Matrix ι ι K) *ᵥ w := fun w => by rw [← hAg, toLinEquiv_apply]
  rw [hgA v, hf A hA v, hgA (f v)]

end Dictionary

section Plus

variable {K : Type} [Field K] {m : ℕ}

private def plusAniso (K : Type) [Field K] (j : Fin m) : Fin m ⊕ Fin m → K :=
  Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1

private lemma quadPlus_plusAniso (j : Fin m) : quadPlus m K (plusAniso K j) = 1 := by
  rw [plusAniso, QuadraticMap.map_add (quadPlus m K), quadPlus_single, quadPlus_single,
    polar_single_inl_quadPlus]
  simp

private lemma plusAniso_inl_self (j : Fin m) : plusAniso K j (Sum.inl j) = 1 := by
  simp [plusAniso, Pi.single_apply]

private lemma plusAniso_mem_perp {i j : Fin m} (hij : j ≠ i) :
    plusAniso K j ∈ (plusPair K i).perp := by
  rw [HypPair.mem_perp, plusPair_e, plusPair_f, polar_single_inl_quadPlus,
    polar_single_inr_quadPlus]
  simp [plusAniso, Pi.single_apply, hij, hij.symm]

private def plusAniso2 (K : Type) [Field K] (c : K) (j : Fin m) : Fin m ⊕ Fin m → K :=
  Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) c

private lemma quadPlus_plusAniso2 (c : K) (j : Fin m) :
    quadPlus m K (plusAniso2 K c j) = c := by
  rw [plusAniso2, QuadraticMap.map_add (quadPlus m K), quadPlus_single,
    polar_single_inl_quadPlus, quadPlus_apply]
  simp [Pi.single_apply]

private lemma plusAniso2_mem_perp {i j : Fin m} (c : K) (hij : j ≠ i) :
    plusAniso2 K c j ∈ (plusPair K i).perp := by
  rw [HypPair.mem_perp, plusPair_e, plusPair_f, polar_single_inl_quadPlus,
    polar_single_inr_quadPlus]
  simp [plusAniso2, Pi.single_apply, hij, hij.symm]

private lemma plus_two_hyp_mem_hom (f : (Fin m ⊕ Fin m → K) →+ (Fin m ⊕ Fin m → K))
    (hf : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)⁆, ∀ v, f (g v) = g (f v))
    {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {i j : Fin m} (hji : j ≠ i) :
    ((Pi.single (Sum.inl i) 1 : Fin m ⊕ Fin m → K) ∈ homSubmodule (K := K) f ∧
        ∃ γ : K, f (Pi.single (Sum.inl i) 1) =
          γ • (Pi.single (Sum.inl i) 1 : Fin m ⊕ Fin m → K)) ∧
      ((Pi.single (Sum.inr i) 1 : Fin m ⊕ Fin m → K) ∈ homSubmodule (K := K) f ∧
        ∃ γ : K, f (Pi.single (Sum.inr i) 1) =
          γ • (Pi.single (Sum.inr i) 1 : Fin m ⊕ Fin m → K)) := by
  refine hyp_mem_homSubmodule (nondegenerate_polarBilin_quadPlus m K) (plusPair K i) f hf
    (plusAniso_mem_perp hji) (plusAniso2_mem_perp c hji)
    (by rw [quadPlus_plusAniso]; exact one_ne_zero)
    (by rw [quadPlus_plusAniso2]; exact hc0) ?_ ?_
  · intro a b d h
    have h1 := congrFun h (Sum.inl j)
    have h2 := congrFun h (Sum.inr j)
    simp [plusPair_e, plusAniso, plusAniso2, Pi.single_apply, hji, hji.symm] at h1 h2
    have hd : (c - 1) * d = 0 := by linear_combination h2 - h1
    have hd0 : d = 0 := (mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr hc1)
    exact ⟨by linear_combination h1 - hd0, hd0⟩
  · intro a b d h
    have h1 := congrFun h (Sum.inl j)
    have h2 := congrFun h (Sum.inr j)
    simp [plusPair_f, plusAniso, plusAniso2, Pi.single_apply, hji, hji.symm] at h1 h2
    have hd : (c - 1) * d = 0 := by linear_combination h2 - h1
    have hd0 : d = 0 := (mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr hc1)
    exact ⟨by linear_combination h1 - hd0, hd0⟩

end Plus

theorem addCommutantScalar_statedOmegaPlus_two {K : Type} [Field K]
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) :
    AddCommutantScalar (StatedOmega (StatedQuadPlus 2 K)) := by
  obtain ⟨c, hc0, hc1⟩ := hK
  intro f hf
  have hcomm : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)⁆, ∀ v, f (g v) = g (f v) :=
    fun g hg v => commute_of_mem_derivedOrthogonal (coe_quadPlus 2 K) f hf hg v
  have hnd := nondegenerate_polarBilin_quadPlus 2 K
  have hpair : ∀ i : Fin 2, ∃ a b : K,
      ((Pi.single (Sum.inl i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ homSubmodule (K := K) f ∧
        f (Pi.single (Sum.inl i) 1) = a • (Pi.single (Sum.inl i) 1 : Fin 2 ⊕ Fin 2 → K)) ∧
      ((Pi.single (Sum.inr i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ homSubmodule (K := K) f ∧
        f (Pi.single (Sum.inr i) 1) = b • (Pi.single (Sum.inr i) 1 : Fin 2 ⊕ Fin 2 → K)) := by
    intro i
    obtain ⟨j, hji⟩ := exists_ne i
    obtain ⟨⟨he, a, ha⟩, ⟨hfm, b, hb⟩⟩ := plus_two_hyp_mem_hom f hcomm hc0 hc1 hji
    exact ⟨a, b, ⟨he, ha⟩, ⟨hfm, hb⟩⟩
  choose a b hpe hpf using hpair
  have hK' : ∀ i k : Fin 2, k ≠ i →
      b i = a i ∧ f (plusAniso K k) = a i • plusAniso K k :=
    fun i k hki => eq_smul_of_perp hnd (plusPair K i) f hcomm (hpe i).1 (hpf i).1 (hpe i).2
      (hpf i).2 (plusAniso_mem_perp hki) (by rw [quadPlus_plusAniso]; exact one_ne_zero)
  have hab : ∀ i : Fin 2, b i = a i := fun i => by
    obtain ⟨k, hki⟩ := exists_ne i
    exact (hK' i k hki).1
  have haeq : ∀ i j : Fin 2, a i = a j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have hji : j ≠ i := fun h => hij h.symm
      have h1 := (hK' i j hji).2
      have h2 : f (plusAniso K j) = a j • plusAniso K j := by
        rw [plusAniso, map_add, (hpe j).2, (hpf j).2, hab j, smul_add]
      have h3 := congrFun (h1.symm.trans h2) (Sum.inl j)
      simpa [plusAniso_inl_self] using h3
  refine ⟨a 0, eq_smul_of_basis f (a 0) ?_ ?_⟩
  · rintro (i | i)
    · exact (hpe i).1
    · exact (hpf i).1
  · rintro (i | i)
    · rw [(hpe i).2, haeq i 0]
    · rw [(hpf i).2, hab i, haeq i 0]

end OmegaScalars

end CFSG.RankThree.GF2n.Stroth80

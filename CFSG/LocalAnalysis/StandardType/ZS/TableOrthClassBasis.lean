module

public import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases
public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.LocalAnalysis.StandardType.ZS.OrthClass
import CFSG.LocalAnalysis.StandardType.ZS.TableOrth
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassDim3Aux
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassDim3Aux2
import CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareOrthogonalModel
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddOrthogonal

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma zstqb_reflect_self {Q : QuadraticForm (ZMod p) U} {a : U} (ha : Q a ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a a = -a := by
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply ha,
    CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
    mul_div_cancel_right₀ (2 : ZMod p) ha]
  module

private lemma zstqb_reflect_mul_apply {Q : QuadraticForm (ZMod p) U} {a b x : U}
    (ha : Q a ≠ 0) (hb : Q b ≠ 0) (hab : QuadraticMap.polar Q a b = 0) :
    (CFSG.ClassicalGroups.Orthogonal.reflect Q a *
      CFSG.ClassicalGroups.Orthogonal.reflect Q b) x =
      x - (QuadraticMap.polar Q a x / Q a) • a -
        (QuadraticMap.polar Q b x / Q b) • b := by
  rw [LinearEquiv.mul_apply, CFSG.ClassicalGroups.Orthogonal.reflect_apply hb,
    CFSG.ClassicalGroups.Orthogonal.reflect_apply ha,
    QuadraticMap.polar_sub_right, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
    hab, mul_zero, sub_zero]
  abel

private lemma zstqb_isSquare_mul_of_not_isSquare {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsa : ¬ IsSquare a) (hsb : ¬ IsSquare b) : IsSquare (a * b) := by
  have h1 : quadraticChar (ZMod p) a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hsa
  have h2 : quadraticChar (ZMod p) b = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hsb
  have hmul : quadraticChar (ZMod p) (a * b) = 1 := by
    rw [map_mul, h1, h2]
    norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha hb)).mp hmul

private lemma zstqb_reflect_mem_classRefl (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0) {a : U} (ha : Q a ≠ 0) (hs : IsSquare (Q a / c)) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a ∈ ClassRefl p Q c := by
  rw [mem_classRefl_iff hp hQ hc]
  obtain ⟨r, hr⟩ := hs
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, mul_zero] at hr
    exact (div_ne_zero ha hc) hr
  have hQa : Q a = (r * r) * c := (div_eq_iff hc).mp hr
  refine ⟨r⁻¹ • a, ?_, ?_⟩
  · have h1 : Q (r⁻¹ • a) = (r⁻¹ * r) ^ 2 * c := by
      rw [QuadraticMap.map_smul, smul_eq_mul, hQa]
      ring
    rw [h1, inv_mul_cancel₀ hr0, one_pow, one_mul]
  · exact (CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero (inv_ne_zero hr0) a).symm

private lemma zstqb_reflect_eq_signEquiv_singleton {Q : QuadraticForm (ZMod p) U} {n : ℕ}
    (e : Module.Basis (Fin n) (ZMod p) U)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polarBilin Q (e i) (e j) = 0)
    (i : Fin n) (hi : Q (e i) ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q (e i) =
      CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv e {i} := by
  refine e.ext' fun k => ?_
  rw [CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal.signEquiv_apply_basis]
  by_cases hk : k = i
  · subst hk
    rw [zstqb_reflect_self hi]
    simp
  · rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (by
      rw [← QuadraticMap.polarBilin_apply_apply]
      exact horth i k (Ne.symm hk))]
    simp [Finset.mem_singleton, hk]

private lemma zstqb_reflect_mul_eq_signEquiv_pair {Q : QuadraticForm (ZMod p) U} {n : ℕ}
    (e : Module.Basis (Fin n) (ZMod p) U)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polarBilin Q (e i) (e j) = 0)
    {i j : Fin n} (hij : i ≠ j) (hi : Q (e i) ≠ 0) (hj : Q (e j) ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q (e i) *
      CFSG.ClassicalGroups.Orthogonal.reflect Q (e j) =
      CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv e {i, j} := by
  rw [zstqb_reflect_eq_signEquiv_singleton e horth i hi,
    zstqb_reflect_eq_signEquiv_singleton e horth j hj,
    CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv_mul]
  congr 1
  ext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [Finset.mem_symmDiff]

private lemma zstqb_coeffs {α β : ZMod p} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hsα : ¬ IsSquare α) (hsβ : ¬ IsSquare β) :
    ∃ γ s t : ZMod p, γ ^ 2 = α * β ∧ α * s ^ 2 + β * t ^ 2 = 1 := by
  obtain ⟨γ, hγ⟩ := zstqb_isSquare_mul_of_not_isSquare hα hβ hsα hsβ
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hγ
    exact mul_ne_zero hα hβ hγ
  obtain ⟨x, y, hxy⟩ := ZMod.sq_add_sq p α
  refine ⟨γ, x / α, y / γ, by rw [sq, hγ], ?_⟩
  have h1 : α * (x / α) ^ 2 = x ^ 2 / α := by field_simp
  have h2 : β * (y / γ) ^ 2 = y ^ 2 / α := by
    field_simp [hγ0]
    rw [show γ ^ 2 = α * β by rw [sq, hγ]]
    ring
  rw [h1, h2, ← add_div, hxy, div_self hα]

private lemma zstqb_plane_rel {α β s t : ZMod p} {u v : U}
    (hst : α * s ^ 2 + β * t ^ 2 = 1) :
    u = (s * α) • (s • u + t • v) - t • ((-(t * β)) • u + (s * α) • v) ∧
      v = (t * β) • (s • u + t • v) + s • ((-(t * β)) • u + (s * α) • v) := by
  constructor
  · rw [show (s * α) • (s • u + t • v) - t • ((-(t * β)) • u + (s * α) • v)
        = (α * s ^ 2 + β * t ^ 2) • u by module, hst, one_smul]
  · rw [show (t * β) • (s • u + t • v) + s • ((-(t * β)) • u + (s * α) • v)
        = (β * t ^ 2 + α * s ^ 2) • v by module]
    rw [show β * t ^ 2 + α * s ^ 2 = 1 by linear_combination hst, one_smul]

private lemma zstqb_plane_props {Q : QuadraticForm (ZMod p) U} {c α β s t : ZMod p}
    {u v : U} (hQu : Q u = c * α) (hQv : Q v = c * β) (hst : α * s ^ 2 + β * t ^ 2 = 1)
    (huv : QuadraticMap.polar Q u v = 0) :
    Q (s • u + t • v) = c ∧
      Q ((-(t * β)) • u + (s * α) • v) = c * (α * β) ∧
      QuadraticMap.polarBilin Q (s • u + t • v) ((-(t * β)) • u + (s * α) • v) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, hQu, hQv]
    rw [show QuadraticMap.polar Q (s • u) (t • v) = 0 by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, huv, mul_zero, mul_zero]]
    rw [add_zero, smul_eq_mul, smul_eq_mul]
    linear_combination c * hst
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, hQu, hQv]
    rw [show QuadraticMap.polar Q ((-(t * β)) • u) ((s * α) • v) = 0 by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, huv, mul_zero, mul_zero]]
    rw [add_zero, smul_eq_mul, smul_eq_mul]
    linear_combination (c * α * β) * hst
  · rw [QuadraticMap.polarBilin_apply_apply]
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
    rw [show QuadraticMap.polar Q u u = 2 * Q u from
        CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul Q u,
      show QuadraticMap.polar Q v v = 2 * Q v from
        CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul Q v,
      show QuadraticMap.polar Q v u = 0 by rw [QuadraticMap.polar_comm]; exact huv,
      huv, hQu, hQv]
    simp only [smul_eq_mul]
    ring

private lemma zstqb_plane_orth {Q : QuadraticForm (ZMod p) U} {n : ℕ}
    (e : Module.Basis (Fin n) (ZMod p) U)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polarBilin Q (e i) (e j) = 0)
    {i j : Fin n} {a b0 : U} {s t α β : ZMod p}
    (hadef : a = s • e i + t • e j) (hb0def : b0 = (-(t * β)) • e i + (s * α) • e j) :
    (∀ k, k ≠ i → k ≠ j → QuadraticMap.polar Q a (e k) = 0) ∧
      (∀ k, k ≠ i → k ≠ j → QuadraticMap.polar Q b0 (e k) = 0) := by
  have hik : ∀ k, k ≠ i → QuadraticMap.polar Q (e i) (e k) = 0 := by
    intro k hk
    rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]
    exact horth k i hk
  have hjk : ∀ k, k ≠ j → QuadraticMap.polar Q (e j) (e k) = 0 := by
    intro k hk
    rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]
    exact horth k j hk
  constructor
  · intro k hki hkj
    rw [hadef, QuadraticMap.polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, hik k hki, hjk k hkj, mul_zero,
      mul_zero, add_zero]
  · intro k hki hkj
    rw [hb0def, QuadraticMap.polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, hik k hki, hjk k hkj, mul_zero,
      mul_zero, add_zero]

private lemma zstqb_forbidden_pair_prod {Q : QuadraticForm (ZMod p) U} {n : ℕ}
    (e : Module.Basis (Fin n) (ZMod p) U)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polarBilin Q (e i) (e j) = 0)
    {i j : Fin n} (hij : i ≠ j) {a b0 : U} {s t α β : ZMod p}
    (hqi : Q (e i) ≠ 0) (hqj : Q (e j) ≠ 0) (hQa_ne : Q a ≠ 0) (hQb0_ne : Q b0 ≠ 0)
    (hb0a : CFSG.ClassicalGroups.Orthogonal.reflect Q b0 a = a)
    (hab0 : CFSG.ClassicalGroups.Orthogonal.reflect Q a b0 = b0)
    (hei : e i = (s * α) • a - t • b0) (hej : e j = (t * β) • a + s • b0)
    (hak : ∀ k, k ≠ i → k ≠ j → QuadraticMap.polar Q a (e k) = 0)
    (hb0k : ∀ k, k ≠ i → k ≠ j → QuadraticMap.polar Q b0 (e k) = 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q (e i) *
      CFSG.ClassicalGroups.Orthogonal.reflect Q (e j) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q b0 := by
  refine e.ext' fun k => ?_
  by_cases hki : k = i
  · rw [hki, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hji : CFSG.ClassicalGroups.Orthogonal.reflect Q (e j) (e i) = e i :=
      CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (by
        rw [← QuadraticMap.polarBilin_apply_apply]; exact horth j i (Ne.symm hij))
    rw [hji, zstqb_reflect_self hqi, hei]
    simp only [map_sub, map_smul]
    rw [hb0a, zstqb_reflect_self hQb0_ne]
    simp only [map_neg]
    rw [zstqb_reflect_self hQa_ne, hab0]
    module
  · by_cases hkj : k = j
    · rw [hkj, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      have hij' : CFSG.ClassicalGroups.Orthogonal.reflect Q (e i) (e j) = e j :=
        CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (by
          rw [← QuadraticMap.polarBilin_apply_apply]; exact horth i j hij)
      rw [zstqb_reflect_self hqj, map_neg, hij', hej]
      simp only [map_add, map_smul]
      rw [hb0a, zstqb_reflect_self hQb0_ne]
      simp only [map_neg]
      rw [zstqb_reflect_self hQa_ne, hab0]
      module
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      have hkj' : CFSG.ClassicalGroups.Orthogonal.reflect Q (e j) (e k) = e k :=
        CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (by
          rw [← QuadraticMap.polarBilin_apply_apply]; exact horth j k (Ne.symm hkj))
      rw [hkj',
        CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (by
          rw [← QuadraticMap.polarBilin_apply_apply]; exact horth i k (Ne.symm hki)),
        CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (hb0k k hki hkj),
        CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (hak k hki hkj)]

private lemma zstqb_forbidden_pair_mem (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {n : ℕ} {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0) (e : Module.Basis (Fin n) (ZMod p) U)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polarBilin Q (e i) (e j) = 0)
    {i j : Fin n} (hij : i ≠ j) (hqi : Q (e i) ≠ 0) (hqj : Q (e j) ≠ 0)
    (hsi : ¬ IsSquare (Q (e i) / c)) (hsj : ¬ IsSquare (Q (e j) / c)) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q (e i) *
      CFSG.ClassicalGroups.Orthogonal.reflect Q (e j) ∈
      Subgroup.closure (ClassRefl p Q c) := by
  have hα0 : Q (e i) / c ≠ 0 := div_ne_zero hqi hc
  have hβ0 : Q (e j) / c ≠ 0 := div_ne_zero hqj hc
  set α : ZMod p := Q (e i) / c with hαdef
  set β : ZMod p := Q (e j) / c with hβdef
  have hα0' : α ≠ 0 := by rw [hαdef]; exact hα0
  have hβ0' : β ≠ 0 := by rw [hβdef]; exact hβ0
  have hsi' : ¬ IsSquare α := by rw [hαdef]; exact hsi
  have hsj' : ¬ IsSquare β := by rw [hβdef]; exact hsj
  obtain ⟨γ, s, t, hγ', hst⟩ := zstqb_coeffs hα0' hβ0' hsi' hsj'
  have hQi : Q (e i) = c * α := by rw [hαdef]; field_simp
  have hQj : Q (e j) = c * β := by rw [hβdef]; field_simp
  have hpol : QuadraticMap.polar Q (e i) (e j) = 0 := by
    rw [← QuadraticMap.polarBilin_apply_apply]; exact horth i j hij
  set a : U := s • e i + t • e j with hadef
  set b0 : U := (-(t * β)) • e i + (s * α) • e j with hb0def
  obtain ⟨hQa, hQb0, hab⟩ := zstqb_plane_props hQi hQj hst hpol
  obtain ⟨hei, hej⟩ := zstqb_plane_rel (α := α) (β := β) (u := e i) (v := e j) hst
  rw [← hadef, ← hb0def] at hei hej
  obtain ⟨hak, hb0k⟩ := zstqb_plane_orth e horth hadef hb0def
  have hQa_ne : Q a ≠ 0 := by rw [hQa]; exact hc
  have hQb0_ne : Q b0 ≠ 0 := by
    rw [hQb0]; exact mul_ne_zero hc (mul_ne_zero hα0' hβ0')
  have hb0a : CFSG.ClassicalGroups.Orthogonal.reflect Q b0 a = a :=
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (by
      rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]; exact hab)
  have hab0 : CFSG.ClassicalGroups.Orthogonal.reflect Q a b0 = b0 :=
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (by
      rw [← QuadraticMap.polarBilin_apply_apply]; exact hab)
  rw [zstqb_forbidden_pair_prod e horth hij hqi hqj hQa_ne hQb0_ne hb0a hab0 hei hej
    hak hb0k]
  exact mul_mem (Subgroup.subset_closure (zstqb_reflect_mem_classRefl hp hQ hc hQa_ne
      ⟨1, by rw [hQa, div_self hc, mul_one]⟩))
    (Subgroup.subset_closure (zstqb_reflect_mem_classRefl hp hQ hc hQb0_ne
      ⟨γ, by rw [hQb0, mul_div_cancel_left₀ _ hc, ← sq]; exact hγ'.symm⟩))

private lemma zstqb_commutatorSpace_eq_top (hp : p ≠ 2) {n : ℕ}
    {e : Module.Basis (Fin n) (ZMod p) U} {gen : Fin n → U ≃ₗ[ZMod p] U}
    (hneg : ∀ i, gen i (e i) = - e i) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range gen)) = ⊤ := by
  rw [eq_top_iff, ← e.span_eq, Submodule.span_le]
  rintro v ⟨i, rfl⟩
  have hgi : gen i ∈ Subgroup.closure (Set.range gen) := Subgroup.subset_closure ⟨i, rfl⟩
  have hmem0 : gen i (e i) - e i ∈ HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure (Set.range gen)) := Submodule.subset_span ⟨gen i, hgi, e i, rfl⟩
  have hmem : (-(2 : ZMod p)) • e i ∈ HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure (Set.range gen)) := by
    rw [hneg] at hmem0
    have h : - e i - e i = (-(2 : ZMod p)) • e i := by module
    rwa [h] at hmem0
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hfin := Submodule.smul_mem _ ((-(2 : ZMod p))⁻¹) hmem
  rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h2), one_smul] at hfin

private noncomputable def zstqbGen {n : ℕ} (Q : QuadraticForm (ZMod p) U) (c : ZMod p)
    (e : Module.Basis (Fin n) (ZMod p) U) (partner : Fin n → Fin n) (i : Fin n) :
    U ≃ₗ[ZMod p] U :=
  if _h : IsSquare (Q (e i) / c) then CFSG.ClassicalGroups.Orthogonal.reflect Q (e i)
  else CFSG.ClassicalGroups.Orthogonal.reflect Q (e i) *
    CFSG.ClassicalGroups.Orthogonal.reflect Q (e (partner i))

private lemma zstqbGen_mem_J (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {n : ℕ} {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0) {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hJ : J = Subgroup.closure (ClassRefl p Q c)) (e : Module.Basis (Fin n) (ZMod p) U)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polarBilin Q (e i) (e j) = 0)
    (hQne : ∀ i, Q (e i) ≠ 0) (partner : Fin n → Fin n)
    (hpartner_ne : ∀ i, ¬ IsSquare (Q (e i) / c) → partner i ≠ i)
    (hpartner_forb : ∀ i, ¬ IsSquare (Q (e i) / c) → ¬ IsSquare (Q (e (partner i)) / c)) :
    ∀ i, zstqbGen Q c e partner i ∈ J := by
  intro i
  by_cases hi : IsSquare (Q (e i) / c)
  · rw [hJ]
    simp only [zstqbGen, dif_pos hi]
    exact Subgroup.subset_closure (zstqb_reflect_mem_classRefl hp hQ hc (hQne i) hi)
  · rw [hJ]
    simp only [zstqbGen, dif_neg hi]
    exact zstqb_forbidden_pair_mem hp hQ hc e horth (Ne.symm (hpartner_ne i hi))
      (hQne i) (hQne (partner i)) hi (hpartner_forb i hi)

open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare in
private lemma zstqbGen_mem_signChange {n : ℕ} {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    (e : Module.Basis (Fin n) (ZMod p) U)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polarBilin Q (e i) (e j) = 0)
    (hQne : ∀ i, Q (e i) ≠ 0) (partner : Fin n → Fin n)
    (hpartner_ne : ∀ i, ¬ IsSquare (Q (e i) / c) → partner i ≠ i) :
    ∀ i, zstqbGen Q c e partner i ∈ signChangeSubgroup e := by
  intro i
  by_cases hi : IsSquare (Q (e i) / c)
  · rw [show zstqbGen Q c e partner i = signEquiv e {i} by
      simp only [zstqbGen, dif_pos hi]
      exact zstqb_reflect_eq_signEquiv_singleton e horth i (hQne i)]
    exact signEquiv_mem_signChangeSubgroup e {i}
  · rw [show zstqbGen Q c e partner i = signEquiv e {i, partner i} by
      simp only [zstqbGen, dif_neg hi]
      exact zstqb_reflect_mul_eq_signEquiv_pair e horth (Ne.symm (hpartner_ne i hi))
        (hQne i) (hQne (partner i))]
    exact signEquiv_mem_signChangeSubgroup e {i, partner i}

private lemma zstqbGen_neg {n : ℕ} {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    (e : Module.Basis (Fin n) (ZMod p) U)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polarBilin Q (e i) (e j) = 0)
    (hQne : ∀ i, Q (e i) ≠ 0) (partner : Fin n → Fin n)
    (hpartner_ne : ∀ i, ¬ IsSquare (Q (e i) / c) → partner i ≠ i) :
    ∀ i, zstqbGen Q c e partner i (e i) = - e i := by
  intro i
  by_cases hi : IsSquare (Q (e i) / c)
  · simp only [zstqbGen, dif_pos hi]
    exact zstqb_reflect_self (hQne i)
  · simp only [zstqbGen, dif_neg hi]
    have hpi : CFSG.ClassicalGroups.Orthogonal.reflect Q (e (partner i)) (e i) = e i :=
      CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (by
        rw [← QuadraticMap.polarBilin_apply_apply]
        exact horth (partner i) i (hpartner_ne i hi))
    rw [LinearEquiv.mul_apply, hpi, zstqb_reflect_self (hQne i)]

private lemma zstqb_coprime_card (hp : p ≠ 2) {n : ℕ}
    {e : Module.Basis (Fin n) (ZMod p) U} {D : Subgroup (U ≃ₗ[ZMod p] U)}
    (hD : D ≤ CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signChangeSubgroup e) :
    Nat.Coprime (Nat.card ↥D) p := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hcard : Nat.card
      ↥(CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signChangeSubgroup e) =
      2 ^ Fintype.card (Fin n) :=
    CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow.card_signChangeSubgroup h2 e
  have hdvd : Nat.card ↥D ∣ 2 ^ Fintype.card (Fin n) := by
    rw [← hcard]; exact Subgroup.card_dvd_of_le hD
  have hp2 : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm]
    exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr (by
      intro hdiv
      exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) (by norm_num)).mp hdiv))
  exact Nat.Coprime.of_dvd_left hdvd (hp2.pow_left _)

theorem exists_orthogonal_basis_forbidden (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) :
    ∃ e : Module.Basis (Fin (Module.finrank (ZMod p) U)) (ZMod p) U,
      (∀ i j, i ≠ j → QuadraticMap.polarBilin Q (e i) (e j) = 0) ∧
        ∀ i, IsSquare (Q (e i) / c) ∨ ∃ j, j ≠ i ∧ ¬ IsSquare (Q (e j) / c) := by
  have hodd : Odd (Nat.card (ZMod p)) := owD3_odd_card_zmod (Fact.out : p.Prime) hp
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar
  have hν0 : ν ≠ 0 := by
    intro h
    exact hν (by rw [h]; exact ⟨0, by ring⟩)
  obtain ⟨e, horth, heq, -⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq (K := ZMod p) (V := U) hodd
      (d := Module.finrank (ZMod p) U) rfl (by omega) Q hQ (a := c * ν)
      (mul_ne_zero hc hν0)
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    rw [QuadraticMap.polarBilin_apply_apply]
    exact horth i j hij
  · intro i
    by_cases hi : (i : ℕ) + 1 < Module.finrank (ZMod p) U
    · obtain ⟨j, hji, hjlt⟩ : ∃ j : Fin (Module.finrank (ZMod p) U),
          j ≠ i ∧ (j : ℕ) + 1 < Module.finrank (ZMod p) U := by
        by_cases h0 : (i : ℕ) = 0
        · refine ⟨⟨1, by omega⟩, ?_, by change (1 : ℕ) + 1 < _; omega⟩
          intro h
          have h1 : (1 : ℕ) = (i : ℕ) := congrArg Fin.val h
          omega
        · refine ⟨⟨0, by omega⟩, ?_, by change (0 : ℕ) + 1 < _; omega⟩
          intro h
          exact h0 (congrArg Fin.val h).symm
      exact Or.inr ⟨j, hji, by
        rw [heq j hjlt, mul_div_cancel_left₀ ν hc]
        exact hν⟩
    · refine Or.inr ⟨⟨0, by omega⟩, ?_, ?_⟩
      · intro h
        have h0 : (i : ℕ) = 0 := (congrArg Fin.val h).symm
        exact hi (by omega)
      · rw [heq (⟨0, by omega⟩ : Fin (Module.finrank (ZMod p) U))
            (by change (0 : ℕ) + 1 < _; omega), mul_div_cancel_left₀ ν hc]
        exact hν

open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare in
theorem coprimeWitness_orthClass (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hJ : J = Subgroup.closure (ClassRefl p Q c)) :
    CoprimeWitness p J := by
  classical
  obtain ⟨e, horth, hcond⟩ := exists_orthogonal_basis_forbidden hp h3 hQ hc
  have hQne : ∀ i, Q (e i) ≠ 0 := by
    intro i hi
    have hio : LinearMap.BilinForm.iIsOrtho (QuadraticMap.polarBilin Q) e := horth
    have h := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate hio hQ i
    exact h (by rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hi, smul_zero])
  let partner : Fin (Module.finrank (ZMod p) U) → Fin (Module.finrank (ZMod p) U) := fun i =>
    if h : IsSquare (Q (e i) / c) then i
    else Classical.choose (hcond i |>.resolve_left h)
  have hpartner_ne : ∀ i, ¬ IsSquare (Q (e i) / c) → partner i ≠ i := by
    intro i hi
    simp only [partner, dif_neg hi]
    exact (Classical.choose_spec (hcond i |>.resolve_left hi)).1
  have hpartner_forb : ∀ i, ¬ IsSquare (Q (e i) / c) →
      ¬ IsSquare (Q (e (partner i)) / c) := by
    intro i hi
    simp only [partner, dif_neg hi]
    exact (Classical.choose_spec (hcond i |>.resolve_left hi)).2
  have hgenJ : ∀ i, zstqbGen Q c e partner i ∈ J :=
    zstqbGen_mem_J hp hQ hc hJ e horth hQne partner hpartner_ne hpartner_forb
  have hgenSign : ∀ i, zstqbGen Q c e partner i ∈ signChangeSubgroup e :=
    zstqbGen_mem_signChange e horth hQne partner hpartner_ne
  have hgenNeg : ∀ i, zstqbGen Q c e partner i (e i) = - e i :=
    zstqbGen_neg e horth hQne partner hpartner_ne
  set D : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure (Set.range (zstqbGen Q c e partner)) with hDdef
  have hDsign : D ≤ signChangeSubgroup e := by
    rw [hDdef]
    exact (Subgroup.closure_le _).mpr (by rintro g ⟨i, rfl⟩; exact hgenSign i)
  refine ⟨D, ?_, ?_, ?_⟩
  · rw [hDdef]
    exact (Subgroup.closure_le _).mpr (by rintro g ⟨i, rfl⟩; exact hgenJ i)
  · exact zstqb_coprime_card hp hDsign
  · rw [hDdef]
    exact zstqb_commutatorSpace_eq_top hp hgenNeg

end CFSG.StandardType.ZS

end

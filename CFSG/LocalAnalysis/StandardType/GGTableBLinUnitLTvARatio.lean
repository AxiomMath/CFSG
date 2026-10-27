module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLModPSL

public section

namespace CFSG.StandardType.LinTvA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.Assembly TableB TypeA TypeANbrDvd

variable {d : ℕ} {K : Type} [Field K] {L' : Type} [Group L']

@[expose] def IsRat (φ' : SpecialLinearGroup (Fin d) K →* L') (b : MulAut L')
    (r : Fin d → Fin d → K) : Prop :=
  ∃ t : Fin d → K, ActsDiag φ' b t ∧ ∀ k l, r k l = t k * (t l)⁻¹

variable {φ' : SpecialLinearGroup (Fin d) K →* L'}

theorem IsRat.mul {a b : MulAut L'} {r r' : Fin d → Fin d → K} (ha : IsRat φ' a r)
    (hb : IsRat φ' b r') : IsRat φ' (a * b) fun k l => r k l * r' k l := by
  obtain ⟨t, ht, hrt⟩ := ha
  obtain ⟨u, hu, hru⟩ := hb
  refine ⟨fun k => t k * u k, ht.mul hu, fun k l => ?_⟩
  beta_reduce
  rw [hrt, hru, mul_inv]
  ring

theorem IsRat.inv {b : MulAut L'} {r : Fin d → Fin d → K} (hb : IsRat φ' b r) :
    IsRat φ' b⁻¹ fun k l => (r k l)⁻¹ := by
  obtain ⟨t, ht, hrt⟩ := hb
  refine ⟨fun k => (t k)⁻¹, ht.inv, fun k l => ?_⟩
  beta_reduce
  rw [hrt, mul_inv, inv_inv]

theorem IsRat.unique (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {b : MulAut L'}
    {r r' : Fin d → Fin d → K} (h : IsRat φ' b r) (h' : IsRat φ' b r') : r = r' := by
  obtain ⟨t, ht, hrt⟩ := h
  obtain ⟨t', ht', hrt'⟩ := h'
  funext k l
  rw [hrt, hrt']
  by_cases hkl : k = l
  · rw [hkl, mul_inv_cancel₀ (ht.ne_zero l), mul_inv_cancel₀ (ht'.ne_zero l)]
  · exact ht.ratio hφker ht' hkl

theorem IsRat.eq [CharP K 2] (hd : 0 < d) (hφ's : Function.Surjective φ') {b b' : MulAut L'}
    {r : Fin d → Fin d → K} (h : IsRat φ' b r) (h' : IsRat φ' b' r) : b = b' := by
  obtain ⟨t, ht, hrt⟩ := h
  obtain ⟨t', ht', hrt'⟩ := h'
  set i0 : Fin d := ⟨0, hd⟩
  have hne : t i0 ≠ 0 := ht.ne_zero i0
  have hne' : t' i0 ≠ 0 := ht'.ne_zero i0
  have hc : t' i0 * (t i0)⁻¹ ≠ 0 := mul_ne_zero hne' (inv_ne_zero hne)
  have hmul : ActsDiag φ' b (fun k => t k * (t' i0 * (t i0)⁻¹)) :=
    LinUnitL.ActsDiag.mul_const ht hc
  have heq : (fun k => t k * (t' i0 * (t i0)⁻¹)) = t' := by
    funext k
    have h1 : t k * (t i0)⁻¹ = t' k * (t' i0)⁻¹ := (hrt k i0).symm.trans (hrt' k i0)
    field_simp at h1 ⊢
    linear_combination h1
  rw [heq] at hmul
  exact hmul.unique hφ's ht'

@[expose] def RatAct (φ' : SpecialLinearGroup (Fin d) K →* L') (A : Subgroup (MulAut L'))
    (α : MulAut L') (π : Equiv.Perm (Fin d)) (e : ℕ) : Prop :=
  ∀ b ∈ A, ∀ r, IsRat φ' b r → IsRat φ' (α * b * α⁻¹) fun k l => r (π k) (π l) ^ e

theorem RatAct.mul {A : Subgroup (MulAut L')} {α α' : MulAut L'} {π π' : Equiv.Perm (Fin d)}
    {e e' : ℕ} (hα : ∀ b ∈ A, α * b * α⁻¹ ∈ A) (h : RatAct φ' A α π e)
    (h' : RatAct φ' A α' π' e') : RatAct φ' A (α' * α) (π * π') (e * e') := by
  intro b hb r hr
  obtain ⟨t, ht, hrt⟩ := h' _ (hα b hb) _ (h b hb r hr)
  refine ⟨t, ?_, fun k l => ?_⟩
  · have e1 : α' * α * b * (α' * α)⁻¹ = α' * (α * b * α⁻¹) * α'⁻¹ := by group
    rw [e1]
    exact ht
  · have h1 := hrt k l
    beta_reduce at h1 ⊢
    rw [← h1, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, pow_mul]

theorem RatAct.pow {A : Subgroup (MulAut L')} {α : MulAut L'} {π : Equiv.Perm (Fin d)} {e : ℕ}
    (hα : ∀ b ∈ A, α * b * α⁻¹ ∈ A) (h : RatAct φ' A α π e) :
    ∀ n : ℕ, RatAct φ' A (α ^ n) (π ^ n) (e ^ n)
  | 0 => by
    intro b hb r hr
    simpa using hr
  | n + 1 => by
    have := RatAct.mul hα h (RatAct.pow hα h n)
    rwa [← pow_succ, ← pow_succ', ← pow_succ'] at this

theorem conj_pow_eq_of_fixed {G : Type*} [Group G] (α b : G)
    (hfix : α * (b⁻¹ * (α * b * α⁻¹)) * α⁻¹ = b⁻¹ * (α * b * α⁻¹)) :
    ∀ n : ℕ, α ^ n * b * (α ^ n)⁻¹ = b * (b⁻¹ * (α * b * α⁻¹)) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨u, hu⟩ : ∃ u, u = b⁻¹ * (α * b * α⁻¹) := ⟨_, rfl⟩
    rw [← hu] at hfix ih ⊢
    have hbu : α * b * α⁻¹ = b * u := by rw [hu]; group
    have e1 : α ^ (n + 1) * b * (α ^ (n + 1))⁻¹ = α * (α ^ n * b * (α ^ n)⁻¹) * α⁻¹ := by
      rw [pow_succ']
      group
    have hαu : α * u ^ n * α⁻¹ = u ^ n := by rw [← conj_pow, hfix]
    calc α ^ (n + 1) * b * (α ^ (n + 1))⁻¹ = α * (α ^ n * b * (α ^ n)⁻¹) * α⁻¹ := e1
      _ = α * (b * u ^ n) * α⁻¹ := by rw [ih]
      _ = (α * b * α⁻¹) * (α * u ^ n * α⁻¹) := by group
      _ = (b * u) * u ^ n := by rw [hbu, hαu]
      _ = b * u ^ (n + 1) := by rw [pow_succ', mul_assoc]

theorem conj_pow_prime_eq {A : Subgroup (MulAut L')} {p : ℕ} (hAp : ∀ a ∈ A, a ^ p = 1)
    {α : MulAut L'} (hα : ∀ b ∈ A, α * b * α⁻¹ ∈ A) {b : MulAut L'} (hb : b ∈ A)
    (hfix : α * (b⁻¹ * (α * b * α⁻¹)) * α⁻¹ = b⁻¹ * (α * b * α⁻¹)) :
    α ^ p * b * (α ^ p)⁻¹ = b := by
  rw [conj_pow_eq_of_fixed α b hfix p, hAp _ (A.mul_mem (A.inv_mem hb) (hα b hb)), mul_one]

theorem transvection_data {p : ℕ} (hp : p.Prime) {A : Subgroup (MulAut L')}
    (hA0 : 0 < Nat.card A) {α : Subgroup.normalizer (A : Set (MulAut L'))}
    (hT : GGIsTransvection p (A.normalizerMonoidHom α)) :
    (∀ b ∈ A, (α : MulAut L') * (b⁻¹ * ((α : MulAut L') * b * (α : MulAut L')⁻¹)) *
      (α : MulAut L')⁻¹ = b⁻¹ * ((α : MulAut L') * b * (α : MulAut L')⁻¹)) ∧
    ∃ b ∈ A, (α : MulAut L') * b * (α : MulAut L')⁻¹ ≠ b := by
  refine ⟨fun b hb => ?_, ?_⟩
  · have h1 := congrArg Subtype.val (hT.2 ⟨b, hb⟩)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h1
  · by_contra hcon
    have hfix : ∀ b : A, A.normalizerMonoidHom α b = b := fun b =>
      Subtype.ext (by
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        by_contra h'
        exact hcon ⟨b, b.2, h'⟩)
    have hcard : Nat.card {b : A // A.normalizerMonoidHom α b = b} = Nat.card A :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hfix)
    have h2 := hT.1
    rw [hcard] at h2
    have h3 : p = 1 := by
      have : Nat.card A * p = Nat.card A * 1 := by rw [h2, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hA0 this
    exact hp.one_lt.ne' h3

variable [CharP K 2]

@[expose] noncomputable def heartElt (φ' : SpecialLinearGroup (Fin d) K →* L') {ζ : K}
    (hζ0 : ζ ≠ 0) {i j : Fin d} (hij : i ≠ j) : MulAut L' :=
  MulAut.conj (φ' (LinUnitL.diagSLOf (rootT ζ i j) (prod_rootT hζ0 hij)))

theorem heartElt_actsDiag {ζ : K} (hζ0 : ζ ≠ 0) {i j : Fin d} (hij : i ≠ j) :
    ActsDiag φ' (heartElt φ' hζ0 hij) (rootT ζ i j) :=
  actsDiag_conj (LinUnitL.coe_diagSLOf _ _)

theorem heartElt_mem {p : ℕ} {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) {ζ : K} (hζ0 : ζ ≠ 0) (hζ : ζ ^ p = 1)
    {i j : Fin d} (hij : i ≠ j) : heartElt φ' hζ0 hij ∈ A :=
  conj_mem_of_selfCent hsc hdiag (LinUnitL.coe_diagSLOf _ _) (rootT_pow hζ i j)

end CFSG.StandardType.LinTvA

end

module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdAct
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred

public section

namespace CFSG.StandardType.LineU

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.TypeA

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem exists_pairVec_act (hK : UnitaryFieldData 2 n K) (hp : p.Prime) (hd : 3 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    (hφs : Function.Surjective φ) {A A' : Subgroup (MulAut L')} (hA'A : A' ≤ A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hA'inv : ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ A',
      MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ ∈ A')
    {a₀ : MulAut L'} (ha₀ : a₀ ∈ A') (ha₀1 : a₀ ≠ 1) :
    ∃ (lam : K) (i j : Fin d) (b : MulAut L'), i ≠ j ∧ IsPrimitiveRoot lam p ∧ b ∈ A' ∧
      ActsDiagU φ b (ggPairVec i j lam) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, hat⟩ := hdiag a₀ (hA'A ha₀)
  obtain ⟨i, j, hij⟩ : ∃ i j, t i ≠ t j := by
    by_contra hcon
    push Not at hcon
    exact ha₀1 (ActsDiagU.eq_one_of_const hφs hat ⟨0, by omega⟩ hcon)
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  obtain ⟨lam, hlam⟩ : ∃ lam : K, t i * (t j)⁻¹ = lam := ⟨_, rfl⟩
  have hlam1 : lam ≠ 1 := by
    rw [← hlam]
    intro h
    exact hij ((mul_inv_eq_one₀ (hat.ne_zero j)).mp h)
  have hlamp : lam ^ p = 1 := by
    rw [← hlam]
    exact ActsDiagU.ratio_pow hK hd hφker hat (hAp a₀ (hA'A ha₀)) i j
  have hlamprim : IsPrimitiveRoot lam p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hlamp hlam1)
  set b : MulAut L' := a₀ * (MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a₀ *
    (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹)⁻¹ with hb
  have hbA' : b ∈ A' := A'.mul_mem ha₀ (A'.inv_mem (hA'inv (Equiv.swap i j) a₀ ha₀))
  have hbt : ActsDiagU φ b (ggPairVec i j lam) := by
    have h := hat.mul (ActsDiagU.conj_perm hK hat (Equiv.swap i j)).inv
    rw [Equiv.swap_inv] at h
    rw [mul_inv_comp_swap hat.ne_zero hij', hlam] at h
    exact h
  exact ⟨lam, i, j, b, hij', hlamprim, hbA', hbt⟩

theorem mem_of_actsDiagU_pairVec (hK : UnitaryFieldData 2 n K) (hφs : Function.Surjective φ)
    {A' : Subgroup (MulAut L')}
    (hA'inv : ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ A',
      MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ ∈ A')
    {lam : K} {i j : Fin d} (hij : i ≠ j) {b : MulAut L'} (hbA' : b ∈ A')
    (hb : ActsDiagU φ b (ggPairVec i j lam)) {k l : Fin d} (hkl : k ≠ l) (m : ℕ)
    {c : MulAut L'} (hc : ActsDiagU φ c (ggPairVec k l (lam ^ m))) : c ∈ A' := by
  classical
  obtain ⟨σ, hσk, hσl⟩ := exists_perm_pair hkl hij
  have hpow : ActsDiagU φ (b ^ m) (ggPairVec i j (lam ^ m)) := by
    have h := hb.pow m
    rwa [ggPairVec_pow] at h
  have hfun : (fun k => ggPairVec i j (lam ^ m) (σ k)) = ggPairVec k l (lam ^ m) :=
    ggPairVec_comp_of hσk hσl (lam ^ m)
  have hconj : ActsDiagU φ (MulAut.conj (φ (permSU hK σ⁻¹)) * b ^ m *
      (MulAut.conj (φ (permSU hK σ⁻¹)))⁻¹) (ggPairVec k l (lam ^ m)) := by
    have h := ActsDiagU.conj_perm hK hpow σ⁻¹
    rw [inv_inv] at h
    exact hfun ▸ h
  have hc'A' : MulAut.conj (φ (permSU hK σ⁻¹)) * b ^ m *
      (MulAut.conj (φ (permSU hK σ⁻¹)))⁻¹ ∈ A' :=
    hA'inv σ⁻¹ _ (A'.pow_mem hbA' m)
  exact (ActsDiagU.unique hφs hc hconj) ▸ hc'A'

theorem exists_actsDiagU_of_gen {A : Subgroup (MulAut L')}
    (hfull : ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
      ∃ a ∈ A, ActsDiagU φ a t)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (hd : 0 < d) (P : MulAut L' → Prop)
    (hP1 : P 1) (hPmul : ∀ a ∈ A, ∀ b ∈ A, P a → P b → P (a * b))
    (hPv : ∀ k l : Fin d, k ≠ l → ∀ m : ℕ, ∀ a ∈ A,
      ActsDiagU φ a (ggPairVec k l (ζ ^ m)) → P a)
    {t : Fin d → K} (ht : ∀ i, t i ^ p = 1) (htp : ∏ i, t i = 1) :
    ∃ a ∈ A, P a ∧ ActsDiagU φ a t := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set k₀ : Fin d := ⟨0, hd⟩ with hk₀
  have ht0 : ∀ i, t i ≠ 0 := fun i h0 => by
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at htp
    exact zero_ne_one htp
  have hfac : ∀ k, ∃ a ∈ A, P a ∧ ActsDiagU φ a (ggPairVec k k₀ (t k)) := by
    intro k
    by_cases hk : k = k₀
    · refine ⟨1, A.one_mem, hP1, ?_⟩
      have e : ggPairVec k k₀ (t k) = fun _ => (1 : K) := by
        funext m
        rw [ggPairVec_apply, hk]
        split_ifs <;> simp [mul_inv_cancel₀ (ht0 _)]
      rw [e]
      exact actsDiagU_one φ
    · obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one (ht k)
      obtain ⟨a, haA, ha⟩ := hfull (ggPairVec k k₀ (t k))
        (fun i => pow_ggPairVec (ht k) i) (prod_ggPairVec _ (ht0 k))
      refine ⟨a, haA, hPv k k₀ hk m a haA ?_, ha⟩
      rw [← hm] at ha
      exact ha
  have hprod : ∀ s : Finset (Fin d), ∃ a ∈ A, P a ∧
      ActsDiagU φ a (∏ k ∈ s, ggPairVec k k₀ (t k)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, A.one_mem, hP1, ?_⟩
      rw [Finset.prod_empty]
      exact actsDiagU_one φ
    | insert k s hks ih =>
      obtain ⟨a, haA, hPa, ha⟩ := ih
      obtain ⟨b, hbA, hPb, hb⟩ := hfac k
      refine ⟨b * a, A.mul_mem hbA haA, hPmul b hbA a haA hPb hPa, ?_⟩
      rw [Finset.prod_insert hks]
      exact hb.mul ha
  obtain ⟨a, haA, hPa, ha⟩ := hprod Finset.univ
  refine ⟨a, haA, hPa, ?_⟩
  have hfun : (∏ k ∈ Finset.univ, ggPairVec k k₀ (t k)) = t := by
    funext m
    rw [Finset.prod_apply]
    simp only [ggPairVec_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq Finset.univ m t,
      ite_eq_left (Finset.mem_univ m)]
    by_cases hm : m = k₀
    · simp only [hm, ite_true, Finset.prod_inv_distrib]
      rw [htp, inv_one, mul_one]
    · simp [hm]
  rwa [hfun] at ha

theorem conj_mem_of_invariant_U (hK : UnitaryFieldData 2 n K) (hp : p.Prime) (hd : 3 ≤ d)
    (hpq : p ∣ 2 ^ n + 1)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    (hφs : Function.Surjective φ) {A A' : Subgroup (MulAut L')} (hA'A : A' ≤ A)
    (hsc : GGTorusSelfCent p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    (hAp : ∀ a ∈ A, a ^ p = 1)
    (hA'inv : ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ A',
      MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ ∈ A')
    {a₀ : MulAut L'} (ha₀ : a₀ ∈ A') (ha₀1 : a₀ ≠ 1) {D : ↥(unitarySU 2 n K d)}
    {u : Fin d → K} (hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u)
    (hu : ∀ i, u i ^ p = 1) : MulAut.conj (φ D) ∈ A' := by
  obtain ⟨lam, i, j, b, hij, hlam, hbA', hb⟩ :=
    exists_pairVec_act hK hp hd hφker hφs hA'A hdiag hAp hA'inv ha₀ ha₀1
  have hnorm : ∀ x : K, x ^ p = 1 → x ^ (2 ^ n + 1) = 1 := fun x hx => by
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, hx, one_pow]
  have hDprod : ∏ x, u x = 1 := by
    have h1 := ((mem_unitarySU_iff hK).mp D.2).1
    rwa [show ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u from hD,
      Matrix.det_diagonal] at h1
  have hfull : ∀ v : Fin d → K, (∀ x, v x ^ p = 1) → ∏ x, v x = 1 →
      ∃ a ∈ A, ActsDiagU φ a v := by
    intro v hv hvp
    obtain ⟨E, hE⟩ := exists_diagSU hK (u := v) (fun x => hnorm _ (hv x)) hvp
    exact ⟨_, conj_mem_of_selfCent_U hsc hdiag hE hv, actsDiagU_conj hE⟩
  obtain ⟨c', -, hc'A', hc'⟩ := exists_actsDiagU_of_gen hfull hlam hp (by omega)
    (fun c => c ∈ A') A'.one_mem (fun a _ b _ ha hb => A'.mul_mem ha hb)
    (fun k l hkl m c _ hcact => mem_of_actsDiagU_pairVec hK hφs hA'inv hij hbA' hb hkl m hcact)
    hu hDprod
  rw [ActsDiagU.unique hφs (actsDiagU_conj hD) hc']
  exact hc'A'

end CFSG.StandardType.LineU

end

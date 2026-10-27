module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdCent
public import CFSG.LocalAnalysis.StandardType.GGTDCentFour

public section

namespace CFSG.StandardType.UnitTB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.Assembly

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem isDiag_of_conj_comm [Finite K] (hM : Model φ) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hd : 4 ≤ d) {ζ : K} (hζ : ζ ≠ ζ⁻¹)
    (hDex : ∀ k l : Fin d, k ≠ l → ∃ D : ↥(unitarySU 2 n K d),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (TypeA.ggPairVec k l ζ))
    {s : ↥(unitarySU 2 n K d)}
    (h : ∀ k l : Fin d, k ≠ l → ∀ D : ↥(unitarySU 2 n K d),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (TypeA.ggPairVec k l ζ) →
      MulAut.conj (φ s) * MulAut.conj (φ D) = MulAut.conj (φ D) * MulAut.conj (φ s)) :
    ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
  haveI : CharP K 2 := hM.field.charP
  refine TypeANbrDvd.isDiag_of_mul_diagonal_pairVec_of_four_le ?_ hd hζ fun k l hkl => ?_
  · rw [((mem_unitarySU_iff hM.field).mp s.2).1]
    exact one_ne_zero
  obtain ⟨D, hDm⟩ := hDex k l hkl
  have h1 : MulAut.conj (φ s * φ D) = MulAut.conj (φ D * φ s) := by
    rw [map_mul, map_mul, h k l hkl D hDm]
  set g : ↥(unitarySU 2 n K d) := (D * s)⁻¹ * (s * D) with hg
  have hgφ : φ g = (φ D * φ s)⁻¹ * (φ s * φ D) := by
    rw [hg, map_mul, map_inv, map_mul, map_mul]
  have hgy : ∀ y, φ (g * y * g⁻¹) = φ y := by
    intro y
    have h3 : (φ s * φ D) * φ y * (φ s * φ D)⁻¹ = (φ D * φ s) * φ y * (φ D * φ s)⁻¹ := by
      have := congrArg (fun f : MulAut L' => f (φ y)) h1
      simpa only [MulAut.conj_apply] using this
    rw [map_mul, map_mul, map_inv, hgφ]
    calc (φ D * φ s)⁻¹ * (φ s * φ D) * φ y * ((φ D * φ s)⁻¹ * (φ s * φ D))⁻¹
        = (φ D * φ s)⁻¹ * ((φ s * φ D) * φ y * (φ s * φ D)⁻¹) * (φ D * φ s) := by group
      _ = (φ D * φ s)⁻¹ * ((φ D * φ s) * φ y * (φ D * φ s)⁻¹) * (φ D * φ s) := by rw [h3]
      _ = φ y := by group
  obtain ⟨c, hc⟩ := scalar_of_map_conj_eq hM hK hd hgy
  refine ⟨c, ?_⟩
  have h4 : s * D = D * s * g := by rw [hg]; group
  have h5 := congrArg (fun x : ↥(unitarySU 2 n K d) =>
    ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) h4
  simp only [Subgroup.coe_mul, Units.val_mul] at h5
  rw [hDm] at h5
  rw [h5, hc, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem conj_mem_of_selfCent {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {D : ↥(unitarySU 2 n K d)}
    {u : Fin d → K} (hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u)
    (hu : ∀ i, u i ^ p = 1) : MulAut.conj (φ D) ∈ A := by
  refine hsc (φ D) (fun a ha => ?_) ?_
  · obtain ⟨t, hat⟩ := hdiag a ha
    exact hat.fix_of_diagonal D hD
  · rw [← map_pow]
    have hDp : D ^ p = 1 := by
      apply Subtype.ext
      apply Units.ext
      have e : u ^ p = fun _ => (1 : K) := funext hu
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
      rw [hD, diagonal_pow, e, diagonal_one]
    rw [hDp, map_one]

theorem exists_actsDiagU_of_gen {A : Subgroup (MulAut L')}
    (hfull : ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
      ∃ a ∈ A, ActsDiagU φ a t)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (hd : 0 < d) (P : MulAut L' → Prop)
    (hP1 : P 1) (hPmul : ∀ a ∈ A, ∀ b ∈ A, P a → P b → P (a * b))
    (hPv : ∀ k l : Fin d, k ≠ l → ∀ m : ℕ, ∀ a ∈ A,
      ActsDiagU φ a (TypeA.ggPairVec k l (ζ ^ m)) → P a)
    {t : Fin d → K} (ht : ∀ i, t i ^ p = 1) (htp : ∏ i, t i = 1) :
    ∃ a ∈ A, P a ∧ ActsDiagU φ a t := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set k₀ : Fin d := ⟨0, hd⟩ with hk₀
  have ht0 : ∀ i, t i ≠ 0 := fun i h0 => by
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at htp
    exact zero_ne_one htp
  have hfac : ∀ k, ∃ a ∈ A, P a ∧ ActsDiagU φ a (TypeA.ggPairVec k k₀ (t k)) := by
    intro k
    by_cases hk : k = k₀
    · refine ⟨1, A.one_mem, hP1, ?_⟩
      have e : TypeA.ggPairVec k k₀ (t k) = fun _ => 1 := by
        funext m
        rw [TypeA.ggPairVec_apply, hk]
        split_ifs <;> simp [mul_inv_cancel₀ (ht0 _)]
      rw [e]
      exact actsDiagU_one φ
    · obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one (ht k)
      obtain ⟨a, haA, ha⟩ := hfull (TypeA.ggPairVec k k₀ (t k))
        (fun i => TypeA.pow_ggPairVec (ht k) i) (TypeA.prod_ggPairVec _ (ht0 k))
      exact ⟨a, haA, hPv k k₀ hk m a haA (by rw [hm]; exact ha), ha⟩
  have hprod : ∀ s : Finset (Fin d), ∃ a ∈ A, P a ∧
      ActsDiagU φ a (∏ k ∈ s, TypeA.ggPairVec k k₀ (t k)) := by
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
      exact actsDiagU_mul hb ha
  obtain ⟨a, haA, hPa, ha⟩ := hprod Finset.univ
  refine ⟨a, haA, hPa, ?_⟩
  have e : ∏ k, TypeA.ggPairVec k k₀ (t k) = t := by
    funext m
    rw [Finset.prod_apply]
    simp only [TypeA.ggPairVec_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq Finset.univ m t,
      ite_eq_left (Finset.mem_univ m)]
    by_cases hm : m = k₀
    · simp only [hm, ite_true, Finset.prod_inv_distrib]
      rw [htp, inv_one, mul_one]
    · simp [hm]
  rw [e] at ha
  exact ha

theorem conj_mem_of_invariant [Finite K] (hM : Model φ) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hd : 5 ≤ d) {A A' : Subgroup (MulAut L')} (hA'A : A' ≤ A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hA'inv : ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ A',
      MulAut.conj (φ (permSU hM.field σ)) * a * (MulAut.conj (φ (permSU hM.field σ)))⁻¹ ∈ A')
    {a₀ : MulAut L'} (ha₀ : a₀ ∈ A') (ha₀1 : a₀ ≠ 1) {D : ↥(unitarySU 2 n K d)}
    {u : Fin d → K} (hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u)
    (hu : ∀ i, u i ^ p = 1) : MulAut.conj (φ D) ∈ A' := by
  classical
  have := Fact.mk hp
  have hd3 : 3 ≤ d := by omega
  obtain ⟨t, hat⟩ := hdiag a₀ (hA'A ha₀)
  obtain ⟨i, j, hij⟩ : ∃ i j, t i ≠ t j := by
    by_contra hcon
    push Not at hcon
    exact ha₀1 (hat.eq_one_of_const hM.surj ⟨0, by omega⟩ fun i j => hcon i j)
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  obtain ⟨lam, hlam⟩ : ∃ lam : K, t i * (t j)⁻¹ = lam := ⟨_, rfl⟩
  have hlam1 : lam ≠ 1 := by
    rw [← hlam]
    intro h
    exact hij ((mul_inv_eq_one₀ (hat.ne_zero j)).mp h)
  have hlamp : lam ^ p = 1 := by
    rw [← hlam]
    exact hat.ratio_pow hM.field hd3 hM.ker (hAp a₀ (hA'A ha₀)) i j
  have hlamprim : IsPrimitiveRoot lam p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hlamp hlam1)
  set τ := Equiv.swap i j with hτ
  set b := a₀ * (MulAut.conj (φ (permSU hM.field τ)) * a₀ *
    (MulAut.conj (φ (permSU hM.field τ)))⁻¹)⁻¹ with hb
  have hbA' : b ∈ A' := A'.mul_mem ha₀ (A'.inv_mem (hA'inv τ a₀ ha₀))
  have hbt : ActsDiagU φ b (TypeA.ggPairVec i j lam) := by
    have h1 := hat.conj_perm hM.field τ
    have h2 := actsDiagU_mul hat (actsDiagU_inv h1)
    rw [← hlam, ← TypeA.mul_inv_comp_swap hat.ne_zero hij']
    simpa only [hτ, Equiv.swap_inv] using h2
  have hfull : ∀ v : Fin d → K, (∀ i, v i ^ p = 1) → ∏ i, v i = 1 →
      ∃ a ∈ A, ActsDiagU φ a v := by
    intro v hv hvp
    obtain ⟨E, hE⟩ := exists_diagSU hM.field hpq hv hvp
    exact ⟨_, conj_mem_of_selfCent hsc hdiag hE hv, actsDiagU_conj hE⟩
  have hPv : ∀ k l : Fin d, k ≠ l → ∀ m : ℕ, ∀ c ∈ A,
      ActsDiagU φ c (TypeA.ggPairVec k l (lam ^ m)) → c ∈ A' := by
    intro k l hkl m c _ hcE
    obtain ⟨ρ, hρk, hρl⟩ := TypeA.exists_perm_pair hkl hij'
    have hbm : ActsDiagU φ (b ^ m) (TypeA.ggPairVec i j (lam ^ m)) := by
      have h1 := hbt.pow m
      rwa [TypeA.ggPairVec_pow] at h1
    have hcj := hbm.conj_perm hM.field ρ⁻¹
    rw [inv_inv, show (fun k' => TypeA.ggPairVec i j (lam ^ m) (ρ k')) =
      TypeA.ggPairVec k l (lam ^ m) from TypeA.ggPairVec_comp_of hρk hρl _] at hcj
    rw [actsDiagU_unique hM.surj hcE hcj]
    exact hA'inv ρ⁻¹ _ (A'.pow_mem hbA' m)
  have hDprod : ∏ i, u i = 1 := by
    have h1 := ((mem_unitarySU_iff hM.field).mp D.2).1
    rwa [hD, det_diagonal] at h1
  obtain ⟨c', -, hc'A', hc'E⟩ := exists_actsDiagU_of_gen hfull hlamprim hp (by omega)
    (fun c => c ∈ A') A'.one_mem (fun a _ b _ ha hb => A'.mul_mem ha hb) hPv hu hDprod
  rw [actsDiagU_unique hM.surj (actsDiagU_conj hD) hc'E]
  exact hc'A'

end CFSG.StandardType.UnitTB

end

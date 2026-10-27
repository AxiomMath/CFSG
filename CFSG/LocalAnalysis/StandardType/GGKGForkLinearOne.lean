module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearRow
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeA
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallTypeA
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open TypeANbrDvd

private theorem ggKGOn_permAut_injective {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d)
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ' a t)
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    Function.Injective (TypeANbrDvd.permAut φ' A hN) := by
  refine (injective_iff_map_eq_one (permAut φ' A hN)).mpr fun σ hσ => ?_
  have hcomm : ∀ b ∈ A, NbrInnerWeylA.permConj φ' σ * b * (NbrInnerWeylA.permConj φ' σ)⁻¹ = b := by
    intro b hb
    have h := congrArg (fun f : MulAut ↥A => ((f ⟨b, hb⟩ : ↥A) : MulAut L')) hσ
    rw [permAut_apply, ggConjAut_apply, MulAut.one_apply] at h
    simpa using h
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpK
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  refine inv_eq_one.mp (perm_eq_one_of_pairVec hd hζ1 hζinv (σ := σ.symm) fun k l _ => ?_)
  obtain ⟨m₀, hm₀k, hm₀l⟩ := exists_ne_of_two (by omega : 3 ≤ d) k l
  set v : Fin d → K := ggPairVec k l ζ with hv
  have hvm₀ : v m₀ = 1 := by
    rw [hv, ggPairVec_apply, ite_eq_right hm₀k, ite_eq_right hm₀l, mul_one]
  have hv_ne : ∀ y, v y ≠ 0 := by
    intro y
    rw [hv, ggPairVec_apply]
    split_ifs with h1 h2
    · exact mul_ne_zero hζ0 (inv_ne_zero hζ0)
    · simpa using hζ0
    · simpa using inv_ne_zero hζ0
    · simpa using one_ne_zero
  let D : SpecialLinearGroup (Fin d) K :=
    ⟨diagonal v, by rw [det_diagonal, hv, prod_ggPairVec ζ hζ0]⟩
  have hDm : (D : Matrix (Fin d) (Fin d) K) = diagonal v := rfl
  have hDA : MulAut.conj (φ' D) ∈ A :=
    conj_mem_of_selfCent hsc hdiag hDm (fun i => by rw [hv]; exact pow_ggPairVec hζ.pow_eq_one i)
  have hact : ActsDiag φ' (MulAut.conj (φ' D)) v := actsDiag_conj hDm
  have hperm : MulAut.conj (φ' (permSL σ.symm)) = NbrInnerWeylA.permConj φ' σ := rfl
  have hconj : MulAut.conj (φ' (permSL σ.symm)) * MulAut.conj (φ' D) *
      (MulAut.conj (φ' (permSL σ.symm)))⁻¹ = MulAut.conj (φ' D) := by
    rw [hperm]
    exact hcomm (MulAut.conj (φ' D)) hDA
  have hact' : ActsDiag φ' (MulAut.conj (φ' D)) (v ∘ σ.symm) := by
    have h := hact.conj_perm σ.symm
    rw [hconj] at h
    exact h
  refine ⟨v (σ.symm m₀) * (v m₀)⁻¹, fun m => ?_⟩
  by_cases hm : m = m₀
  · rw [hm]
    simp [hvm₀]
  · have hratio := hact'.ratio hφker hact hm
    rw [Function.comp_apply, Function.comp_apply, hvm₀, inv_one, mul_one] at hratio
    rw [hvm₀, inv_one, mul_one]
    calc v (σ.symm m) = v (σ.symm m) * (v (σ.symm m₀))⁻¹ * v (σ.symm m₀) := by
          rw [mul_assoc, inv_mul_cancel₀ (hv_ne (σ.symm m₀)), mul_one]
      _ = v m * v (σ.symm m₀) := by rw [hratio]
      _ = v (σ.symm m₀) * v m := by rw [mul_comm]

private theorem ggKGOn_isReflection_permSL {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {L' : Type} [Group L'] [Finite L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    {A : Subgroup (MulAut L')} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hM : IsDiagTorusModel p φ A) {i j : Fin d} (hij : i ≠ j) :
    GGIsReflection p (ggConjAut A (conj_permSL_mem_normalizer hM i j)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) fun f g h => by
      ext x
      exact congrFun h x
  haveI : Finite ↥A := Subtype.finite
  have hd0 : 0 < d := by omega
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (K := K) hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  set P : SpecialLinearGroup (Fin d) K := permSL (Equiv.swap i j) with hP
  set g : MulAut L' := MulAut.conj (φ P) with hg
  have hPP : P⁻¹ = P := by rw [hP, permSL_inv, Equiv.swap_inv]
  have hginv : g⁻¹ = g := by rw [hg, ← map_inv, ← map_inv, hPP]
  have hgg : g * g = 1 := by
    nth_rewrite 2 [hginv.symm]
    exact mul_inv_cancel g
  set hN : g ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    conj_permSL_mem_normalizer hM i j with _hNdef
  set f : MulAut ↥A := ggConjAut A hN with hf
  have hf_apply : ∀ b : ↥A, ((f b : ↥A) : MulAut L') = g * (b : MulAut L') * g⁻¹ :=
    fun b => ggConjAut_apply A hN b
  have hf_inv_apply : ∀ b : ↥A, (((f b)⁻¹ : ↥A) : MulAut L') =
      g * (b : MulAut L')⁻¹ * g⁻¹ := by
    intro b
    rw [Subgroup.coe_inv, hf_apply b]
    group
  have hf2' : ggConjAut A hN ^ 2 = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_pow_apply A hN 2 b, pow_two, hgg]
    simp
  have hf2 : f ^ 2 = 1 := by rw [hf]; exact hf2'
  set t₁ : Fin d → K := ggPairVec i j ζ with ht₁
  have ht₁0 : ∀ k, t₁ k ≠ 0 := by
    intro k
    rw [ht₁, ggPairVec_apply]
    split_ifs <;> simp [hζ0]
  have ht₁p : ∀ k, t₁ k ^ p = 1 := fun k => by
    rw [ht₁]
    exact pow_ggPairVec hζ.pow_eq_one k
  have hprod₁ : ∏ k, t₁ k = 1 := by
    rw [ht₁]
    exact prod_ggPairVec ζ hζ0
  set D₁ : SpecialLinearGroup (Fin d) K :=
    ⟨diagonal t₁, by rw [Matrix.det_diagonal]; exact hprod₁⟩ with _hD₁
  have hD₁mat : (D₁ : Matrix (Fin d) (Fin d) K) = diagonal t₁ := rfl
  have hD₁p : D₁ ^ p = 1 := pow_eq_one_of_pow_diagonal hD₁mat ht₁p
  have ht₁i : t₁ i = ζ := by
    rw [ht₁, ggPairVec_apply, ite_eq_left rfl, ite_eq_right hij]
    simp
  have ht₁j : t₁ j = ζ⁻¹ := by
    rw [ht₁, ggPairVec_apply, ite_eq_right hij.symm, ite_eq_left rfl]
    simp
  set a₁ : ↥A := ⟨MulAut.conj (φ D₁), (hM _).mpr ⟨D₁, ⟨t₁, hD₁mat⟩, hD₁p, rfl⟩⟩ with _ha₁
  have ha₁coe : (a₁ : MulAut L') = MulAut.conj (φ D₁) := rfl
  have ha₁p : a₁ ^ p = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, ha₁coe, ← map_pow, ← map_pow, hD₁p, map_one,
      map_one]
  have hAc : ∀ a b : ↥A, a * b = b * a := by
    intro a b
    obtain ⟨D, ⟨t, hD⟩, -, haD⟩ := (hM (a : MulAut L')).mp a.2
    obtain ⟨D', ⟨u, hD'⟩, -, hbD⟩ := (hM (b : MulAut L')).mp b.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, haD, hbD]
    simp only [← map_mul]
    rw [commute_of_diagonal hD hD']
  have hδ : ∀ a : ↥A, ∃ e : ℕ, a * (f a)⁻¹ = a₁ ^ e := by
    intro a
    obtain ⟨D, ⟨t, hD⟩, hDp, haD⟩ := (hM (a : MulAut L')).mp a.2
    have ht : ∀ k, t k ^ p = 1 := fun k => pow_eq_one_of_diagonal hD hDp k
    have ht0 : ∀ k, t k ≠ 0 := fun k => diag_entry_ne_zero hD k
    set E : SpecialLinearGroup (Fin d) K := D * (P * D * P⁻¹)⁻¹ with hE
    have hEmat : (E : Matrix (Fin d) (Fin d) K) =
        diagonal (ggPairVec i j (t i * (t j)⁻¹)) := by
      have hPDPmat : ((P * D * P⁻¹ : SpecialLinearGroup (Fin d) K) :
          Matrix (Fin d) (Fin d) K) = diagonal (t ∘ Equiv.swap i j) := by
        rw [hP]
        exact coe_permSL_conj hD (Equiv.swap i j)
      rw [hE, Matrix.SpecialLinearGroup.coe_mul, coe_inv_SL_of_diagonal hPDPmat, hD,
        diagonal_mul_diagonal]
      simp only [Function.comp_apply]
      rw [mul_inv_comp_swap ht0 hij]
    have hδcoe : (((a * (f a)⁻¹ : ↥A) : MulAut L')) = MulAut.conj (φ E) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hf_apply a, haD, hg, hE]
      simp only [map_mul, map_inv]
    have hμp : (t i * (t j)⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, ht i, ht j, inv_one, one_mul]
    obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one hμp
    have hEeq : E = D₁ ^ e := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_pow, hD₁mat, diagonal_pow, hEmat]
      congr 1
      rw [ht₁, ← he]
      exact (ggPairVec_pow i j ζ e).symm
    refine ⟨e, Subtype.ext ?_⟩
    rw [hδcoe, hEeq, Subgroup.coe_pow, ha₁coe, ← map_pow, ← map_pow]
  set E₁ : SpecialLinearGroup (Fin d) K := D₁ * (P * D₁ * P⁻¹)⁻¹ with hE₁
  have hE₁mat : (E₁ : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec i j (ζ ^ 2)) := by
    have hPDPmat : ((P * D₁ * P⁻¹ : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = diagonal (t₁ ∘ Equiv.swap i j) := by
      rw [hP]
      exact coe_permSL_conj hD₁mat (Equiv.swap i j)
    rw [hE₁, Matrix.SpecialLinearGroup.coe_mul, coe_inv_SL_of_diagonal hPDPmat, hD₁mat,
      diagonal_mul_diagonal]
    simp only [Function.comp_apply]
    rw [mul_inv_comp_swap ht₁0 hij]
    congr 1
    rw [ht₁i, ht₁j, inv_inv, ← pow_two]
  have hδ₁coe : (((a₁ * (f a₁)⁻¹ : ↥A) : MulAut L')) = MulAut.conj (φ E₁) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hf_apply a₁, ha₁coe, hg, hE₁]
    simp only [map_mul, map_inv]
  set E₁ : SpecialLinearGroup (Fin d) K := D₁ * (P * D₁ * P⁻¹)⁻¹ with hE₁
  have hE₁mat : (E₁ : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec i j (ζ ^ 2)) := by
    have hPDPmat : ((P * D₁ * P⁻¹ : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = diagonal (t₁ ∘ Equiv.swap i j) := by
      rw [hP]
      exact coe_permSL_conj hD₁mat (Equiv.swap i j)
    rw [hE₁, Matrix.SpecialLinearGroup.coe_mul, coe_inv_SL_of_diagonal hPDPmat, hD₁mat,
      diagonal_mul_diagonal]
    simp only [Function.comp_apply]
    rw [mul_inv_comp_swap ht₁0 hij]
    congr 1
    rw [ht₁i, ht₁j, inv_inv, ← pow_two]
  have hδ₁coe : (((a₁ * (f a₁)⁻¹ : ↥A) : MulAut L')) = MulAut.conj (φ E₁) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hf_apply a₁, ha₁coe, hg, hE₁]
    simp only [map_mul, map_inv]
  have h₁ : a₁ * (f a₁)⁻¹ ≠ 1 := by
    intro hcontra
    have hconj1 : MulAut.conj (φ E₁) = 1 := by
      rw [← hδ₁coe, hcontra]
      rfl
    have hact : GGActsBy φ 1 E₁ := by
      rw [← hconj1]
      exact ggActsBy_conj_phi φ E₁
    have hker : φ (E₁ * SpecialLinearGroup.transvection hij 1 * E₁⁻¹ *
        (SpecialLinearGroup.transvection hij 1)⁻¹) = 1 := by
      have h := hact (SpecialLinearGroup.transvection hij 1)
      rw [MulAut.one_apply] at h
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have hti : ggPairVec i j (ζ ^ 2) i = ζ ^ 2 := by
      rw [ggPairVec_apply, ite_eq_left rfl, ite_eq_right hij, mul_one]
    have htj : ggPairVec i j (ζ ^ 2) j = (ζ ^ 2)⁻¹ := by
      rw [ggPairVec_apply, ite_eq_right hij.symm, ite_eq_left rfl, one_mul]
    have hconjW : E₁ * SpecialLinearGroup.transvection hij 1 * E₁⁻¹ =
        SpecialLinearGroup.transvection hij (ζ ^ 4) := by
      rw [conj_transvection_of_diagonal hE₁mat hij 1]
      congr 1
      rw [hti, htj, inv_inv]
      ring
    have hW : E₁ * SpecialLinearGroup.transvection hij 1 * E₁⁻¹ *
        (SpecialLinearGroup.transvection hij 1)⁻¹ =
        SpecialLinearGroup.transvection hij (ζ ^ 4 + 1) := by
      rw [hconjW, SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection,
        CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection]
      rw [show (1 : Matrix (Fin d) (Fin d) K) + Matrix.single i j (ζ ^ 4) =
          Matrix.transvection i j (ζ ^ 4) from rfl,
        show (1 : Matrix (Fin d) (Fin d) K) + Matrix.single i j (1 : K) =
          Matrix.transvection i j 1 from rfl,
        show (1 : Matrix (Fin d) (Fin d) K) + Matrix.single i j (ζ ^ 4 + 1) =
          Matrix.transvection i j (ζ ^ 4 + 1) from rfl]
      exact Matrix.transvection_mul_transvection_same i j hij (ζ ^ 4) 1
    obtain ⟨cc, -, hcc⟩ := mem_scalars.mp (hφker _ hker)
    rw [hW] at hcc
    have hentry := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i j) hcc
    rw [CFSG.LinearGroups.coe_transvection] at hentry
    simp [Matrix.single, Matrix.scalar, hij] at hentry
    have hζ4 : ζ ^ 4 = 1 := by
      have h := hentry
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
      exact h
    have hdvd : p ∣ 4 := hζ.dvd_of_pow_eq_one 4 hζ4
    have hdvd2 : p ∣ 2 := by
      have h4 : p ∣ 2 ^ 2 := by norm_num at hdvd ⊢; exact hdvd
      exact hp.dvd_of_dvd_pow h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd2)
  exact ⟨hf2, card_fix_mul_of_le_zpowers hp hAc f ha₁p hδ h₁⟩

theorem ggKGSL_reflection {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) {L' : Type} [Group L'] [Finite L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hsc : GGTorusSelfCent p A) (hM : IsDiagTorusModel p φ A) {φ₀ : MulAut ↥A}
    (h₀ : φ₀ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A) (hrefl : GGIsReflection p φ₀) :
    ∃ i j : Fin d, i ≠ j ∧ φ₀ = ggConjAut A (conj_permSL_mem_normalizer hM i j) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) fun f g h => by
      ext x
      exact congrFun h x
  haveI : Finite ↥A := Subtype.finite
  have hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ a t := by
    intro a ha
    obtain ⟨D, ⟨t, hD⟩, -, rfl⟩ := (hM a).mp ha
    refine ⟨t, SpecialLinearGroup.toGL D, hD, fun s => ?_⟩
    rw [MulAut.conj_apply]
    simp only [← map_mul, ← map_inv]
    congr 1
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      map_mul, map_mul, map_inv]
  have hN : ∀ σ, NbrInnerWeylA.permConj φ σ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => permConj_mem_normalizer_of_selfCent hφs hφker hA.2 hsc hdiag σ
  have hggaux : ∀ x y : Fin d, ggConjAut A (hN (Equiv.swap x y)) =
      ggConjAut A (conj_permSL_mem_normalizer hM x y) := by
    intro x y
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply, ggConjAut_apply]
    have helem : NbrInnerWeylA.permConj φ (Equiv.swap x y) =
        MulAut.conj (φ (permSL (Equiv.swap x y))) := by
      show MulAut.conj (φ (permSL (Equiv.swap x y)⁻¹)) =
        MulAut.conj (φ (permSL (Equiv.swap x y)))
      rw [Equiv.swap_inv]
    rw [helem]
  have hsw : ∀ x y : Fin d, x ≠ y → GGIsReflection p (permAut φ A hN (Equiv.swap x y)) := by
    intro x y hxy
    rw [permAut_apply, hggaux x y]
    exact ggKGOn_isReflection_permSL hp hp2 hpK hφker hM hxy
  have hinj : Function.Injective (permAut φ A hN) :=
    ggKGOn_permAut_injective hp hp2 hpK hd hφker hsc hdiag hN
  have hauto : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      (permAut φ A hN).range :=
    ggAutomizer_eq_range_permAut hp hp2 hpK hφs hφker hA hsc hdiag hN
  have hφ₀ : φ₀ ∈ (permAut φ A hN).range := by
    rw [← hauto]
    exact h₀
  obtain ⟨σ, hσ⟩ := hφ₀
  have hreflE : GGIsReflection p (permAut φ A hN σ) := by
    rw [hσ]
    exact hrefl
  have hisSwap : σ.IsSwap :=
    isSwap_of_ggIsReflection hp2 hA (permAut φ A hN) hinj hsw hreflE
  obtain ⟨i, j, hij, hσij⟩ := hisSwap
  refine ⟨i, j, hij, ?_⟩
  rw [← hσ, hσij, permAut_apply]
  exact hggaux i j

private theorem ggKGOn_coordBlockSL_mono {d : ℕ} {K : Type} [Field K] {J J' : Finset (Fin d)}
    (h : J ⊆ J') :
    CFSG.RankThree.CALinearPlane.coordBlockSL K J ≤
      CFSG.RankThree.CALinearPlane.coordBlockSL K J' := by
  intro g hg
  rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff] at hg ⊢
  intro i j hij
  exact hg i j (by
    rcases hij with h' | h'
    · exact Or.inl fun hi => h' (h hi)
    · exact Or.inr fun hj => h' (h hj))

theorem ggKGSL_layer {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hd : 4 ≤ d)
    (hpd : Nat.Coprime p d) (h4 : 4 ≤ Nat.card K) {L' : Type} [Group L'] [Finite L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hM : IsDiagTorusModel p φ A) {i j : Fin d} (hij : i ≠ j) (a : MulAut L') (ha : a ∈ A)
    (hfix : ggConjAut A (conj_permSL_mem_normalizer hM i j) ⟨a, ha⟩ = ⟨a, ha⟩) :
    φ (permSL (Equiv.swap i j)) ∈ LargeEvenLayer (ggFix a) := by
  by_cases ha1 : a = 1
  · subst ha1
    have hSLq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin d) K) :=
      CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (by omega) h4
    have hcent : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin d) K) := by
      intro g hg
      exact scalars_le_center d K (hφker g (MonoidHom.mem_ker.mp hg))
    have hL'q : CFSG.IsQuasisimple L' :=
      CFSG.LocalCores.isQuasisimple_of_surjective hSLq φ hφs hcent
    have hqtop : CFSG.IsQuasisimple (↥(⊤ : Subgroup L')) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := L')).symm hL'q
    have hqtopA : Assembly.IsQuasisimple (↥(⊤ : Subgroup L')) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hqtop
    have hcompTop : IsComponentOf (⊤ : Subgroup L') ⊤ :=
      ⟨le_top, IsSubnormal.refl ⊤, hqtopA⟩
    have hlayerTop : LargeEvenLayer (⊤ : Subgroup L') = ⊤ :=
      le_antisymm le_top (le_sSup hcompTop)
    have hfix1 : ggFix (1 : MulAut L') = ⊤ := by
      ext x
      simp [ggFix]
    rw [hfix1, hlayerTop]
    exact Subgroup.mem_top _
  · obtain ⟨D, ⟨t, hD⟩, hDp, haD⟩ := (hM a).mp ha
    have hconjPP : MulAut.conj (φ (permSL (Equiv.swap i j))) *
        MulAut.conj (φ (permSL (Equiv.swap i j))) = 1 := by
      rw [← map_mul, ← map_mul, ← NbrInnerWeylA.permSL_mul, Equiv.swap_mul_self,
        NbrInnerWeylA.permSL_one, map_one, map_one]
    have hcomm : MulAut.conj (φ (permSL (Equiv.swap i j))) * MulAut.conj (φ D) =
        MulAut.conj (φ D) * MulAut.conj (φ (permSL (Equiv.swap i j))) := by
      have hfix' : MulAut.conj (φ (permSL (Equiv.swap i j))) * a *
          (MulAut.conj (φ (permSL (Equiv.swap i j))))⁻¹ = a := by
        have h := congrArg (fun x : ↥A => (x : MulAut L')) hfix
        rw [ggConjAut_apply] at h
        exact h
      rw [haD] at hfix'
      calc MulAut.conj (φ (permSL (Equiv.swap i j))) * MulAut.conj (φ D) =
          MulAut.conj (φ (permSL (Equiv.swap i j))) * MulAut.conj (φ D) *
            (MulAut.conj (φ (permSL (Equiv.swap i j))))⁻¹ *
            MulAut.conj (φ (permSL (Equiv.swap i j))) := by group
        _ = MulAut.conj (φ D) * MulAut.conj (φ (permSL (Equiv.swap i j))) := by rw [hfix']
    have htij : t i = t j :=
      (conj_permSL_comm_conj_iff hpd hφker i j hD hDp).mp hcomm
    have hDgl : (SpecialLinearGroup.toGL D : Matrix (Fin d) (Fin d) K) = diagonal t := hD
    have haDgl : ∀ s, a (φ s) =
        φ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K
          (SpecialLinearGroup.toGL D) s) := by
      intro s
      rw [haD, MulAut.conj_apply]
      simp only [← map_mul, ← map_inv]
      congr 1
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
        map_mul, map_mul, map_inv]
    obtain ⟨S, hS, -, -, hJElayer, -⟩ :=
      layer_coordBlockSL_map_le h4 hφs hφker hDgl haDgl ha1 hij htij
    have hiS : i ∈ S := (hS i).mpr rfl
    have hjS : j ∈ S := (hS j).mpr htij.symm
    have hsub : ({i, j} : Finset (Fin d)) ⊆ S := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hiS
      · rw [Finset.mem_singleton.mp hk]
        exact hjS
    exact hJElayer (Subgroup.mem_map_of_mem φ (ggKGOn_coordBlockSL_mono hsub permSL_mem_coordBlockSL))

theorem ggTorusRootSL2_psl_coprime {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d)
    (hpd : Nat.Coprime p d) (hsec : SLHasSections d K) (h4 : 4 ≤ Nat.card K) :
    GGTorusRootSL2 p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, -, hsc⟩ := hA
  obtain ⟨φ, hφs, hφker, hM⟩ :=
    exists_isDiagTorusModel hp hpK hd hpd hsec hψ hker hperf hAe hAI hr
  intro φ₀ hφ₀ hrefl
  obtain ⟨i, j, hij, hφ₀eq⟩ :=
    ggKGSL_reflection hp hp2 hpK hd hφs hφker hAe hsc hM hφ₀ hrefl
  refine ⟨φ (permSL (Equiv.swap i j)), conj_permSL_mem_normalizer hM i j,
    (CFSG.RankThree.CALinearPlane.coordBlockSL K ({i, j} : Finset (Fin d))).map φ,
    ggTorusWeylElt_permSL hM i j,
    hφ₀eq.symm, Subgroup.mem_map_of_mem φ permSL_mem_coordBlockSL, ?_, ?_, ?_⟩
  · rw [ggHypCent_permSL_eq hpd hφs hφker hM i j]
    exact isComponentOf_coordBlockSL_pair hp hp2 hpK h4 hd hφker hij
  · exact dvd_card_coordBlockSL_pair hp hpK (by omega) hφker hij
  · intro a ha hfix
    exact ggKGSL_layer hd hpd h4 hφs hφker hM hij a ha (by rw [← hφ₀eq]; exact hfix)

theorem ggTorusRootSL2_psl_small {d p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hd : 0 < d) (hd3 : d ≤ 3) (hpd : Nat.Coprime p d) :
    GGTorusRootSL2 p 0 (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hA, hAI, -, h3, -⟩ := hA
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hle := card_le_of_subset_conjAut hp hpK hd hpd hX hXI
  rw [hcard] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
  omega

theorem ggKGOn_torusRootSL2_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusRootSL2 p r R' I') :
    GGTorusRootSL2 p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  refine h L' (e.toMonoidHom.comp ψ) A ⟨e.surjective.comp hψ, ?_, hperf, hAe, ?_, hr, h3, hsc⟩
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    exact ⟨MulAut.congr e φ, hI φ hφ, fun l => by simp [MulAut.congr_apply, hφa]⟩

theorem recipeLinear_rootSL2 {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusRootSL2 p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggKGOn_torusRootSL2_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusRootSL2_psl_small hp hpK (by omega) hd3 hpd')⟩
  · have hsec : SLHasSections d K :=
      slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
    exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' hsec),
      ggKGOn_torusRootSL2_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusRootSL2_psl_coprime hp hp2 hpK hd4 hpd' hsec h4)⟩

end TypeA

theorem ggKGOneOn_typeA : GGKGOneOn fun p lab => GGTypeALabel p lab := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases hs with ⟨h, hpn, hpl⟩ | ⟨h, hl3, hpn⟩ | ⟨h, hl2, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact TypeA.recipeLinear_rootSL2 hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl3 hpn
    subst h hl3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine TypeA.recipeLinear_rootSL2 hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl2 hpn
    subst h hl2
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine TypeA.recipeLinear_rootSL2 hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Pred
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Mod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Orth
public import CFSG.ClassicalGroups.SpecialLinear.Transitive
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport
public import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaCForms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

private lemma s16g_conj_mulVec_eq (A b : Matrix.GeneralLinearGroup ι K) (x : ι → K) :
    (((A * b * A⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)) *ᵥ x =
      (A : Matrix ι ι K) *ᵥ ((b : Matrix ι ι K) *ᵥ
        (((A⁻¹ : Matrix.GeneralLinearGroup ι K)) : Matrix ι ι K) *ᵥ x) := by
  rw [Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem s16g_fixNc_of_conj (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) {p : ℕ} (hp : p.Prime)
    (B : Subgroup (Matrix.GeneralLinearGroup ι K)) (hBΓ : B ≤ Γ) (hBc : Nat.card B = p ^ 2)
    (hBe : ∀ x ∈ B, x ^ p = 1) {κ : Type} (w : κ → ι → K)
    (hw : ∀ k, ∀ b ∈ B, (b : Matrix ι ι K) *ᵥ w k = w k)
    (hconj : ∀ a : ι → K, a ≠ 0 → ∃ k, ∃ A ∈ Γ, (A : Matrix ι ι K) *ᵥ w k = a) :
    FixNc Γ p := by
  intro a ha
  have ha' : Multiplicative.toAdd a ≠ 0 := fun h => ha (toAdd_eq_zero.mp h)
  obtain ⟨k, A, hAΓ, hAw⟩ := hconj (Multiplicative.toAdd a) ha'
  let B' : Subgroup (Matrix.GeneralLinearGroup ι K) := B.map (MulAut.conj A).toMonoidHom
  have hB'Γ : B' ≤ Γ := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    change (MulAut.conj A) b ∈ Γ
    rw [MulAut.conj_apply]
    exact Γ.mul_mem (Γ.mul_mem hAΓ (hBΓ hb)) (Γ.inv_mem hAΓ)
  let B'' : Subgroup ↥Γ := B'.subgroupOf Γ
  have hcard : Nat.card ↥B'' = p ^ 2 := by
    have h1 : Nat.card ↥B'' = Nat.card ↥B' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'Γ).toEquiv
    have h2 : Nat.card ↥B' = Nat.card ↥B :=
      (Nat.card_congr (Subgroup.equivMapOfInjective B (MulAut.conj A).toMonoidHom
        (MulAut.conj A).injective).toEquiv).symm
    rw [h1, h2, hBc]
  have hpow : ∀ x : ↥B'', x ^ p = 1 := by
    intro x
    obtain ⟨b, hb, hbx⟩ :=
      Subgroup.mem_map.mp ((Subgroup.mem_subgroupOf).mp x.property)
    have hbpow : (b : Matrix.GeneralLinearGroup ι K) ^ p = 1 := hBe b hb
    have hxpow : (((x : ↥Γ) : Matrix.GeneralLinearGroup ι K)) ^ p = 1 := by
      rw [← hbx, ← map_pow, hbpow, map_one]
    exact Subtype.ext (Subtype.ext (by simpa using hxpow))
  refine ⟨B'', IsPGroup.of_card hcard, ?_, ?_⟩
  · intro hcyc
    obtain ⟨x, hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
    have hxp : x ^ p = 1 := hpow x
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
    rw [hx, hcard] at hdvd
    have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdvd
    have hlt : p < p ^ 2 := by nlinarith [hp.two_le]
    exact (not_lt_of_ge hle) hlt
  · intro y hy
    obtain ⟨b, hb, hby⟩ :=
      Subgroup.mem_map.mp ((Subgroup.mem_subgroupOf).mp hy)
    have hbw : (b : Matrix ι ι K) *ᵥ w k = w k := hw k b hb
    have hAi : (((A⁻¹ : Matrix.GeneralLinearGroup ι K)) : Matrix ι ι K) *ᵥ
        Multiplicative.toAdd a = w k := by
      rw [← hAw, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hyval : ((y : ↥Γ) : Matrix.GeneralLinearGroup ι K) = A * b * A⁻¹ := by
      change (y.val : Matrix.GeneralLinearGroup ι K) = A * b * A⁻¹
      rw [← hby]
      change (MulAut.conj A) b = A * b * A⁻¹
      rw [MulAut.conj_apply]
    have hmat : (((y : ↥Γ) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
        Multiplicative.toAdd a = Multiplicative.toAdd a := by
      rw [hyval, s16g_conj_mulVec_eq, hAi, hbw, hAw]
    rw [natAct, hmat, ofAdd_toAdd]

theorem s16g_fixNc_of_transitive (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) {p : ℕ}
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (htr : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → ∃ A ∈ Γ, (A : Matrix ι ι K) *ᵥ x = y)
    {E : Subgroup (Matrix.GeneralLinearGroup ι K)} (hEΓ : E ≤ Γ) (hE : ∀ x ∈ E, x ^ p = 1)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : p ^ 3 ≤ Nat.card E) : FixNc Γ p := by
  obtain ⟨B, U, _g, hBE, hBcard, _hgE, hUne, _hUinv, hBfix, _hgnofix⟩ :=
    s16g_exists_fixing_space hp hpK E hE hc hcard
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  exact s16g_fixNc_of_conj Γ hp B (hBE.trans hEΓ) hBcard (fun x hx => hE x (hBE hx))
    (fun _ : Unit => u) (fun _ b hb => hBfix b hb u huU)
    (fun a ha => ⟨(), htr u a hu0 ha⟩)

theorem s16g_fixNc_of_orthogonal [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1)
    (hΓQ : ∀ A ∈ Γ, ∀ v : ι → K, Q ((A : Matrix ι ι K) *ᵥ v) = Q v)
    (htr : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → Q x = Q y → ∃ A ∈ Γ, (A : Matrix ι ι K) *ᵥ x = y)
    {E : Subgroup (Matrix.GeneralLinearGroup ι K)} (hEΓ : E ≤ Γ) (hE : ∀ x ∈ E, x ^ p = 1)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : p ^ 3 ≤ Nat.card E) : FixNc Γ p := by
  have hpK : ¬ p ∣ Nat.card K := by
    intro hdvd
    letI := Fintype.ofFinite K
    obtain ⟨n, _hn2, hcardK⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hcardK] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  obtain ⟨B, U, g, hBE, hBcard, hgE, hUne, hUinv, hBfix, hgnofix⟩ :=
    s16g_exists_fixing_space hp hpK E hE hc hcard
  have hgpow : g ^ p = 1 := hE g hgE
  obtain ⟨u, huU, hu0, hQu⟩ := s16g_exists_singular_of_nofix Q hp hp2 hpq g hgpow U hUne
    (fun u hu => hUinv g hgE u hu) (fun u hu => hgnofix u hu)
  have hBp : IsPGroup p ↥B := IsPGroup.of_card hBcard
  have hBQ : ∀ b ∈ B, ∀ v : ι → K, Q ((b : Matrix ι ι K) *ᵥ v) = Q v :=
    fun b hb v => hΓQ b (hEΓ (hBE hb)) v
  have hfixu : ∀ b ∈ B, (b : Matrix ι ι K) *ᵥ u = u := fun b hb => hBfix b hb u huU
  choose w hw using fun c : K =>
    s16g_orth_values_of_singular Q hQ hp hp2 B hBp hBQ hu0 hQu hfixu c
  refine s16g_fixNc_of_conj Γ hp B (hBE.trans hEΓ) hBcard (fun x hx => hE x (hBE hx)) w
    (fun k b hb => (hw k).2.2 b hb) ?_
  intro a ha
  exact ⟨Q a, htr (w (Q a)) a (hw (Q a)).1 ha (hw (Q a)).2.1⟩

theorem s16g_fixNc_statedSL {n : ℕ} (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    {E : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)} (hEΓ : E ≤ StatedSL n K)
    (hE : ∀ x ∈ E, x ^ p = 1) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcard : p ^ 3 ≤ Nat.card E) : FixNc (StatedSL n K) p :=
  s16g_fixNc_of_transitive _ hp hpK
    (fun _ _ hx hy => CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq hn hx hy)
    hEΓ hE hc hcard

theorem s16g_fixNc_statedSp {m : ℕ} {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    {E : Subgroup (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K)} (hEΓ : E ≤ StatedSp m K)
    (hE : ∀ x ∈ E, x ^ p = 1) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcard : p ^ 3 ≤ Nat.card E) : FixNc (StatedSp m K) p :=
  s16g_fixNc_of_transitive _ hp hpK
    (fun _ _ hx hy => CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq hx hy)
    hEΓ hE hc hcard

theorem s16g_fixNc_statedOmegaPlus [CharP K 2] {m : ℕ} (hm : 3 ≤ m) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1)
    {E : Subgroup (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K)}
    (hEΓ : E ≤ StatedOmega (StatedQuadPlus m K)) (hE : ∀ x ∈ E, x ^ p = 1)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : p ^ 3 ≤ Nat.card E) :
    FixNc (StatedOmega (StatedQuadPlus m K)) p :=
  s16g_fixNc_of_orthogonal (CFSG.LieType.Universal.Spin.quadPlus m K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K) _ hp hp2 hpq
    (fun _ hA v => by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
      exact CFSG.RankThree.GF2n.Smith81.Smith23E1.statedOmega_isometry _ hA v)
    (fun _ _ hx hy hxy => CFSG.ClassicalGroups.Orthogonal.statedOmegaPlus_exists_mulVec_eq hm hx hy
      hxy)
    hEΓ hE hc hcard

theorem s16g_fixNc_statedOmegaMinus [CharP K 2] {m : ℕ} (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1)
    {E : Subgroup (Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hEΓ : E ≤ StatedOmega (StatedQuadMinus m K b c)) (hE : ∀ x ∈ E, x ^ p = 1)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : p ^ 3 ≤ Nat.card E) :
    FixNc (StatedOmega (StatedQuadMinus m K b c)) p :=
  s16g_fixNc_of_orthogonal (CFSG.LieType.Universal.Spin.quadMinus m K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K hirr) _ hp hp2
    hpq (fun _ hA v => by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact CFSG.RankThree.GF2n.Smith81.Smith23E1.statedOmega_isometry _ hA v)
    (fun _ _ hx hy hxy =>
      CFSG.ClassicalGroups.Orthogonal.statedOmegaMinus_exists_mulVec_eq hm hirr hx hy hxy)
    hEΓ hE hc hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

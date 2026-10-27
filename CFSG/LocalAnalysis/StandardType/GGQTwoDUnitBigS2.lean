module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS1
import CFSG.ClassicalInvolution.RouteD.TWYType
import CFSG.GroupTheory.WeirSylow.OrthogonalTori

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.QTwo

open CFSG.Open CFSG.RankThree.Classical

private theorem qtwoDB44_s2_zeta_sq_add_one {L : Type} [Field L] [Algebra (ZMod 2) L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ 3) : ζ ^ 2 + ζ + 1 = 0 := by
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hfac : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by
    have h : ζ ^ 3 - 1 = 0 := by rw [h3, sub_self]
    rw [← h]; ring
  exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr (hζ.ne_one (by norm_num)))

private theorem qtwoDB44_s2_zeta_add_sq {L : Type} [Field L] [Algebra (ZMod 2) L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ 3) : ζ + ζ ^ 2 = 1 := by
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
  have h := qtwoDB44_s2_zeta_sq_add_one hζ
  have h1 : ζ ^ 2 + ζ = -1 := by linear_combination h
  rw [add_comm, h1, CharTwo.neg_eq]

private theorem qtwoDB44_s2_beta_symm {L : Type} [Field L] [Algebra (ZMod 2) L]
    {β : LinearMap.BilinForm (ZMod 2) L} (hβalt : β.IsAlt) (u v : L) : β u v = β v u := by
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
  have h := hβalt.neg_eq u v
  rw [CharTwo.neg_eq] at h
  exact h

private theorem qtwoDB44_s2_beta_key {L : Type} [Field L] [Algebra (ZMod 2) L] {ζ : L}
    {β : LinearMap.BilinForm (ZMod 2) L} (hζ : IsPrimitiveRoot ζ 3)
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) (hβalt : β.IsAlt) (u v : L) :
    β u (ζ * v) + β v (ζ * u) = β u v := by
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
  have hsymm : β v (ζ * u) = β u (ζ ^ 2 * v) := by
    have h1 := ChoiceTwo.bilin_pow_mul hζβ 2 v (ζ * u)
    have h2 : ζ ^ 2 * (ζ * u) = u := by
      rw [← mul_assoc, ← pow_succ, hζ.pow_eq_one, one_mul]
    rw [h2] at h1
    rw [← h1, qtwoDB44_s2_beta_symm hβalt (ζ ^ 2 * v) u]
  calc β u (ζ * v) + β v (ζ * u)
      = β u (ζ * v) + β u (ζ ^ 2 * v) := by rw [hsymm]
    _ = β u (ζ * v + ζ ^ 2 * v) := (map_add (β u) (ζ * v) (ζ ^ 2 * v)).symm
    _ = β u ((ζ + ζ ^ 2) * v) := by rw [← add_mul]
    _ = β u (1 * v) := by rw [qtwoDB44_s2_zeta_add_sq hζ]
    _ = β u v := by rw [one_mul]

private theorem qtwoDB44_s2_polar_qL {L : Type} [Field L] [Algebra (ZMod 2) L] {ζ : L}
    {β : LinearMap.BilinForm (ZMod 2) L} (hζ : IsPrimitiveRoot ζ 3)
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) (hβalt : β.IsAlt) (u v : L) :
    QuadraticMap.polar
        (LinearMap.BilinMap.toQuadraticMap (β.compl₂ (LinearMap.mulLeft (ZMod 2) ζ))) u v =
      β u v := by
  have h : QuadraticMap.polar
      (LinearMap.BilinMap.toQuadraticMap (β.compl₂ (LinearMap.mulLeft (ZMod 2) ζ))) u v =
      (β.compl₂ (LinearMap.mulLeft (ZMod 2) ζ)) u v +
      (β.compl₂ (LinearMap.mulLeft (ZMod 2) ζ)) v u := by
    simp only [QuadraticMap.polar, LinearMap.BilinMap.toQuadraticMap_apply, map_add,
      LinearMap.add_apply]
    abel
  rw [h]
  simpa only [LinearMap.compl₂_apply, LinearMap.mulLeft_apply] using
    qtwoDB44_s2_beta_key hζ hζβ hβalt u v

private theorem qtwoDB44_s2_polar_pi {K : Type} [Field K] {ι : Type} [Fintype ι]
    {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (Q : ∀ i, QuadraticForm K (V i)) (x y : ∀ i, V i) :
    QuadraticMap.polar (QuadraticMap.pi Q) x y = ∑ i, QuadraticMap.polar (Q i) (x i) (y i) := by
  simp [QuadraticMap.polar, QuadraticMap.pi_apply, Finset.sum_sub_distrib]

private theorem qtwoDB44_s2_beta_alt {L : Type} [Field L] [Algebra (ZMod 2) L]
    {n : ℕ} {Φ : (Fin n → L) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)}
    {β : LinearMap.BilinForm (ZMod 2) L}
    (form : ∀ d d', spForm n (ZMod 2) (Φ d) (Φ d') = ∑ i, β (d i) (d' i))
    (hn : 1 ≤ n) : β.IsAlt := by
  intro u
  have h := form (Pi.single ⟨0, hn⟩ u) (Pi.single ⟨0, hn⟩ u)
  rw [spForm_isAlt] at h
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)] at h
  · simpa using h.symm
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

private theorem qtwoDB44_s2_beta_nondegenerate {L : Type} [Field L] [Algebra (ZMod 2) L]
    {n : ℕ} {Φ : (Fin n → L) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)}
    {β : LinearMap.BilinForm (ZMod 2) L}
    (form : ∀ d d', spForm n (ZMod 2) (Φ d) (Φ d') = ∑ i, β (d i) (d' i))
    (hβalt : β.IsAlt) (hn : 1 ≤ n) : β.Nondegenerate := by
  have hleft : ∀ u : L, (∀ v, β u v = 0) → u = 0 := by
    intro u hu
    by_contra hu0
    let i : Fin n := ⟨0, hn⟩
    let d : Fin n → L := Pi.single i u
    have hd_ne : Φ d ≠ 0 := by
      intro h
      have hd0 : d = 0 := Φ.injective (by rw [h, map_zero])
      have := congrFun hd0 i
      simp [d, i] at this
      exact hu0 this
    have hzero : ∀ y, spForm n (ZMod 2) (Φ d) y = 0 := by
      intro y
      obtain ⟨d', rfl⟩ := Φ.surjective y
      rw [form]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = i
      · rw [hj]
        simpa [d] using hu (d' i)
      · simp [d, Pi.single_eq_of_ne hj]
    exact hd_ne ((spForm_nondegenerate (r := n) (K := ZMod 2)).1 (Φ d) hzero)
  refine ⟨hleft, fun u hu => hleft u fun v => ?_⟩
  rw [qtwoDB44_s2_beta_symm hβalt u v]
  exact hu v

private theorem qtwoDB44_s2_zeta_notMem {L : Type} [Field L] [Algebra (ZMod 2) L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ 3) : ζ ∉ Set.range (algebraMap (ZMod 2) L) := by
  rintro ⟨c, rfl⟩
  have h := qtwoDB44_s2_zeta_sq_add_one hζ
  have h' : algebraMap (ZMod 2) L (c ^ 2 + c + 1) = 0 := by
    rw [map_add, map_add, map_pow, map_one]
    simpa using h
  have h'' : c ^ 2 + c + 1 = 0 := (algebraMap (ZMod 2) L).injective (by simpa using h')
  revert h''
  fin_cases c <;> decide

private theorem qtwoDB44_s2_qL_not_plus {L : Type} [Field L] [Algebra (ZMod 2) L]
    [Module.Finite (ZMod 2) L] {ζ : L} (hζ : IsPrimitiveRoot ζ 3)
    {β : LinearMap.BilinForm (ZMod 2) L} (hβalt : β.IsAlt) (hβn : β.Nondegenerate)
    (hL : Module.finrank (ZMod 2) L = 2) :
    ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (LinearMap.BilinMap.toQuadraticMap (β.compl₂ (LinearMap.mulLeft (ZMod 2) ζ))) := by
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
  intro hplus
  obtain ⟨W, hW, hWs⟩ := hplus
  have hdimW : Module.finrank (ZMod 2) W = 1 := by omega
  obtain ⟨w, hw0⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < Module.finrank (ZMod 2) W)
  have hw : (w : L) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hqLw : β (w : L) (ζ * (w : L)) = 0 := hWs w w.2
  have hker_dim : Module.finrank (ZMod 2) (LinearMap.ker (β (w : L))) = 1 := by
    rw [show LinearMap.ker (β (w : L)) =
        LinearMap.ker (LinearMap.BilinForm.toLinHomAux₁ β (w : L)) from rfl]
    rw [← LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker (B := β) (x := (w : L)),
      LinearMap.BilinForm.finrank_orthogonal hβn, finrank_span_singleton hw, hL]
  have hw_ker : (w : L) ∈ LinearMap.ker (β (w : L)) := by
    rw [LinearMap.mem_ker]; exact hβalt (w : L)
  have hζw_ker : ζ * (w : L) ∈ LinearMap.ker (β (w : L)) := by
    rw [LinearMap.mem_ker]; exact hqLw
  have hker_eq : LinearMap.ker (β (w : L)) = Submodule.span (ZMod 2) ({(w : L)} : Set L) := by
    have hle : Submodule.span (ZMod 2) ({(w : L)} : Set L) ≤ LinearMap.ker (β (w : L)) := by
      rw [Submodule.span_le]
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hw_ker
    have hfin : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({(w : L)} : Set L)) =
        Module.finrank (ZMod 2) (LinearMap.ker (β (w : L))) := by
      rw [finrank_span_singleton hw, hker_dim]
    exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm
  have hζw_mem : ζ * (w : L) ∈ Submodule.span (ZMod 2) ({(w : L)} : Set L) := by
    rw [← hker_eq]
    exact hζw_ker
  rw [Submodule.mem_span_singleton] at hζw_mem
  obtain ⟨c, hc⟩ := hζw_mem
  have h : (ζ - algebraMap (ZMod 2) L c) * (w : L) = 0 := by
    rw [sub_mul, ← hc, Algebra.smul_def, sub_self]
  have hζ_eq : ζ = algebraMap (ZMod 2) L c :=
    sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hw)
  exact qtwoDB44_s2_zeta_notMem hζ ⟨c, hζ_eq.symm⟩

private noncomputable def qtwoDB44_s2_piSuccIsometry {L : Type} [Field L] [Algebra (ZMod 2) L]
    (Q : QuadraticForm (ZMod 2) L) (n : ℕ) :
    (QuadraticMap.pi (fun _ : Fin (n + 1) => Q)).IsometryEquiv
      (Q.prod (QuadraticMap.pi (fun _ : Fin n => Q))) where
  toLinearEquiv :=
    { toFun := fun d => (d 0, Fin.tail d)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := fun d => Fin.cons_self_tail d
      right_inv := fun p => by
        obtain ⟨a, g⟩ := p
        exact Prod.ext (by simpa using Fin.cons_zero a g) (by simpa using Fin.tail_cons a g)
      map_add' := fun d d' => by
        refine Prod.ext ?_ ?_
        · rfl
        · funext i; rfl
      map_smul' := fun c d => by
        refine Prod.ext ?_ ?_
        · rfl
        · funext i; rfl }
  map_app' := fun d => by
    simp only [QuadraticMap.prod_apply, QuadraticMap.pi_apply, Fin.sum_univ_succ,
      Prod.fst, Prod.snd, Fin.tail]

private theorem qtwoDB44_s2_pi_even {L : Type} [Field L] [Algebra (ZMod 2) L]
    [Module.Finite (ZMod 2) L] (Q : QuadraticForm (ZMod 2) L)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQdim : Module.finrank (ZMod 2) L = 2) (hQnot : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∀ n, CFSG.GroupTheory.WeirSylow.IsPlusType
        (QuadraticMap.pi (fun _ : Fin n => Q)) ↔ Even n := by
  have hdimpi : ∀ n, Module.finrank (ZMod 2) (Fin n → L) = 2 * n := by
    intro n
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      hQdim, smul_eq_mul]
    omega
  have hone : (QuadraticMap.pi (fun _ : Fin 1 => Q)).IsometryEquiv Q :=
    { toLinearEquiv :=
        { toFun := fun d => d 0
          invFun := fun u => fun _ => u
          left_inv := fun d => by funext i; fin_cases i; rfl
          right_inv := fun u => rfl
          map_add' := fun d d' => rfl
          map_smul' := fun c d => rfl }
      map_app' := fun d => by rw [QuadraticMap.pi_apply, Fin.sum_univ_one] }
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => Even.zero, fun _ => ?_⟩
    haveI : Subsingleton (Fin 0 → L) :=
      ⟨fun f g => funext fun i => Fin.elim0 i⟩
    exact CFSG.GroupTheory.WeirSylow.isPlusType_of_subsingleton _
  | succ n ih =>
    cases n with
    | zero =>
      rw [CFSG.GroupTheory.WeirSylow.isPlusType_congr hone,
        show Even 1 ↔ False from by decide]
      exact iff_false_intro hQnot
    | succ m =>
      rw [CFSG.GroupTheory.WeirSylow.isPlusType_congr (qtwoDB44_s2_piSuccIsometry Q (m + 1))]
      rw [CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_prod_iff (a := 1) (b := m + 1) hQ
        (CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_pi fun _ => hQ)
        (by norm_num) (by omega) hQdim (hdimpi (m + 1))]
      rw [ih]
      simp [hQnot, Nat.even_add_one]

theorem qtwoDB44_frameQ {n : ℕ} (hn : 1 ≤ n) {E : Subgroup (StatedSp n (ZMod 2))}
    {L : Type} [Field L] [Algebra (ZMod 2) L] [Module.Finite (ZMod 2) L] {ζ : L}
    (hL : Module.finrank (ZMod 2) L = 2) (hζ : IsPrimitiveRoot ζ 3)
    (F : ChoiceTwo.SpFrame (ZMod 2) n ζ E) (hs : F.s = n) :
    ∃ Q : QuadraticForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2),
      (∀ x y, QuadraticMap.polar Q x y = spForm n (ZMod 2) x y) ∧
      (qtwoDB44_IsPlus Q ↔ Even n) ∧
      (∀ f : Fin F.s → ZMod 3, ∀ x, Q (spEnd (F.tor f) x) = Q x) := by
  obtain ⟨s, Φ, β, σ, form, ζβ, σζ, σσ, σβ, tor, tor_acts, tor_mem, mem_tor⟩ := F
  have hs' : s = n := hs
  subst s
  haveI hCharL : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
  have hβalt : β.IsAlt := qtwoDB44_s2_beta_alt form hn
  have hβn : β.Nondegenerate := qtwoDB44_s2_beta_nondegenerate form hβalt hn
  let qL : QuadraticForm (ZMod 2) L :=
    LinearMap.BilinMap.toQuadraticMap (β.compl₂ (LinearMap.mulLeft (ZMod 2) ζ))
  let Q₀ : QuadraticForm (ZMod 2) (Fin n → L) := QuadraticMap.pi (fun _ : Fin n => qL)
  let Q : QuadraticForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) := Q₀.comp Φ.symm.toLinearMap
  have hqL : ∀ u, qL u = β u (ζ * u) := fun u => rfl
  have hqL_polar : ∀ u v, QuadraticMap.polar qL u v = β u v :=
    qtwoDB44_s2_polar_qL hζ ζβ hβalt
  have hqL_nondeg : (QuadraticMap.polarBilin qL).Nondegenerate := by
    rw [show QuadraticMap.polarBilin qL = β from
      LinearMap.ext fun u => LinearMap.ext fun v => by
        rw [QuadraticMap.polarBilin_apply_apply]; exact hqL_polar u v]
    exact hβn
  have hqL_notplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType qL :=
    qtwoDB44_s2_qL_not_plus hζ hβalt hβn hL
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro x y
    rw [show QuadraticMap.polar Q x y = QuadraticMap.polar Q₀ (Φ.symm x) (Φ.symm y) from by
      simp only [QuadraticMap.polar, Q, QuadraticMap.comp_apply, map_add]
      rfl]
    rw [qtwoDB44_s2_polar_pi]
    rw [show (∑ i, QuadraticMap.polar qL (Φ.symm x i) (Φ.symm y i)) =
        ∑ i, β (Φ.symm x i) (Φ.symm y i) from
      Finset.sum_congr rfl fun i _ => hqL_polar _ _]
    rw [← form (Φ.symm x) (Φ.symm y), Φ.apply_symm_apply, Φ.apply_symm_apply]
  · have htype₀ : CFSG.GroupTheory.WeirSylow.IsPlusType Q₀ ↔ Even n :=
      qtwoDB44_s2_pi_even qL hqL_nondeg hL hqL_notplus n
    have hisoQ : Q.IsometryEquiv Q₀ :=
      { toLinearEquiv := Φ.symm, map_app' := fun v => rfl }
    exact (@CFSG.GroupTheory.WeirSylow.isPlusType_congr (ZMod 2) _
      (Fin n ⊕ Fin n → ZMod 2) _ (Pi.Function.module _ _ _) (Fin n → L) _ _
      Q Q₀ hisoQ).trans htype₀
  · intro f x
    obtain ⟨d, rfl⟩ := Φ.surjective x
    rw [tor_acts f d]
    change Q₀ (Φ.symm (Φ (ChoiceTwo.torE ζ f d))) = Q₀ (Φ.symm (Φ d))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rw [QuadraticMap.pi_apply, QuadraticMap.pi_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ChoiceTwo.torE_apply]
    change qL (ζ ^ (f i).val * d i) = qL (d i)
    rw [hqL, hqL]
    rw [show ζ * (ζ ^ (f i).val * d i) = ζ ^ (f i).val * (ζ * d i) from
      (by rw [← mul_assoc, ← pow_succ', ← mul_assoc, ← pow_succ])]
    rw [ChoiceTwo.bilin_pow_mul ζβ (f i).val (d i) (ζ * d i)]

end CFSG.StandardType.QTwo

end

module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormOrth
public import CFSG.LocalAnalysis.StandardType.GGDRootBaseFour

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace OrthExcEven

open SpCoord Multiplicative

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

noncomputable def stdBilin [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {k : ℕ}
    (b : Module.Basis (Fin k) (ZMod p) V) : LinearMap.BilinForm (ZMod p) V :=
  Matrix.toBilin b 1

theorem stdBilin_apply [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {k : ℕ}
    (b : Module.Basis (Fin k) (ZMod p) V) (x y : V) :
    stdBilin b x y = ∑ a, b.repr x a * b.repr y a := by
  simp only [stdBilin, Matrix.toBilin_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem stdBilin_nondegenerate [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V) : (stdBilin b).Nondegenerate :=
  (Matrix.Nondegenerate.of_det_ne_zero (by simp)).toBilin b

theorem eq_one_or_neg_one_of_linRefl_smul_isometry [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {k : ℕ} (hk : 3 ≤ k)
    (b : Module.Basis (Fin k) (ZMod p) V) {T U : V ≃ₗ[ZMod p] V} (hT : GGLinRefl T)
    (hU : ∀ x y, stdBilin b (U x) (U y) = stdBilin b x y) {c : ZMod p}
    (hc : ∀ v, T v = c • U v) : c = 1 ∨ c = -1 := by
  have h2 : (2 : ZMod p) ≠ 0 := coord_two_ne_zero (Fact.out) hp2
  by_contra hne
  push Not at hne
  have hcc : c * c - 1 ≠ 0 := by
    intro h0
    have : (c - 1) * (c + 1) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hne.1 (by linear_combination h1)
    · exact hne.2 (by linear_combination h1)
  haveI : FiniteDimensional (ZMod p) V := Module.Basis.finiteDimensional_of_finite b
  set F := LinearMap.ker (T.toLinearMap - LinearMap.id) with hF
  have hFr : Module.finrank (ZMod p) F = k - 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (T.toLinearMap - LinearMap.id)
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin, ← hF] at h1
    have h2 : Module.finrank (ZMod p) (LinearMap.range (T.toLinearMap - LinearMap.id)) = 1 :=
      hT.2
    omega
  have hfix : ∀ x ∈ F, T x = x := by
    intro x hx
    have := LinearMap.mem_ker.mp hx
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at this
    exact sub_eq_zero.mp this
  have hiso0 : ∀ x ∈ F, stdBilin b x x = 0 := by
    intro x hx
    have h1 : stdBilin b x x = c * c * stdBilin b x x := by
      calc stdBilin b x x = stdBilin b (T x) (T x) := by rw [hfix x hx]
        _ = c * c * stdBilin b x x := by
          rw [hc]
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hU]
          ring
    have h3 : (c * c - 1) * stdBilin b x x = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left hcc
  have hiso : ∀ x ∈ F, ∀ y ∈ F, stdBilin b x y = 0 := by
    intro x hx y hy
    have hsym : stdBilin b y x = stdBilin b x y := by
      rw [stdBilin_apply, stdBilin_apply]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    have h1 := hiso0 (x + y) (F.add_mem hx hy)
    simp only [map_add, LinearMap.add_apply, hiso0 x hx, hiso0 y hy, hsym, zero_add,
      add_zero] at h1
    have h3 : 2 * stdBilin b x y = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hle : F ≤ (stdBilin b).orthogonal F := by
    intro y hy
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    exact hiso x hx y hy
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal (stdBilin_nondegenerate b), hFr,
    Module.finrank_eq_card_basis b, Fintype.card_fin] at h1
  omega

theorem stdBilin_signedPerm [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {k : ℕ}
    (b : Module.Basis (Fin k) (ZMod p) V) {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) {u : V →ₗ[ZMod p] V} (hu : ∀ a, u (b a) = ε a • b (π a))
    (x y : V) : stdBilin b (u x) (u y) = stdBilin b x y := by
  have hr : ∀ z c, b.repr (u z) c = ε (π.symm c) * b.repr z (π.symm c) := by
    intro z c
    conv_lhs => rw [← b.sum_repr z]
    simp only [map_sum, map_smul, hu, Module.Basis.repr_self, Finsupp.smul_single,
      Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (π.symm c)]
    · simp [mul_comm]
    · intro a _ ha
      rw [ite_eq_right]
      intro h1
      exact ha (by rw [← h1, Equiv.symm_apply_apply])
    · intro h1
      exact absurd (Finset.mem_univ _) h1
  rw [stdBilin_apply, stdBilin_apply, ← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hr, hr, Equiv.symm_apply_apply]
  have h1 := coord_sign_mul_self (hε a)
  linear_combination (b.repr x a * b.repr y a) * h1

theorem stdBilin_repr_functional [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V) (F : V →ₗ[ZMod p] ZMod p) (w : V) :
    stdBilin b (∑ a, F (b a) • b a) w = F w := by
  rw [stdBilin_apply]
  conv_rhs => rw [← b.sum_repr w]
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem exists_diagram_of_dRoot_bases [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V) {Λ : Type} [Fintype Λ]
    (hh : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (T : V ≃ₗ[ZMod p] V)
    {l l' : ZMod p} (hl : l ≠ 0) (hl' : l' ≠ 0) {ρ ρ' : Λ → Fin k → ℤ}
    (hhρ : ∀ i, hh i = l • ∑ a, ((ρ i a : ℤ) : ZMod p) • b a)
    (hαρ : ∀ i v, α i v = l⁻¹ * ∑ a, ((ρ i a : ℤ) : ZMod p) * b.repr v a)
    (hhρ' : ∀ i, T (hh i) = l' • ∑ a, ((ρ' i a : ℤ) : ZMod p) • b a)
    (hαρ' : ∀ i v, α i (T.symm v) = l'⁻¹ * ∑ a, ((ρ' i a : ℤ) : ZMod p) * b.repr v a)
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ℤ} (hε : ∀ a, ε a = 1 ∨ ε a = -1) {σ : Equiv.Perm Λ}
    (hρρ' : ∀ i a, ρ' i (π a) = ε a * ρ (σ i) a)
    (u : V ≃ₗ[ZMod p] V) (hu : ∀ a, u (b a) = ((ε a : ℤ) : ZMod p) • b (π a))
    (hsep : ∀ v : V, (∀ i, α i v = 0) → v = 0) :
    ∃ g : V ≃ₗ[ZMod p] V, g ∈ ggDiagramSet hh α ∧ (∀ v, T v = (l' / l) • u (g v)) ∧
      ∀ x y, stdBilin b (g x) (g y) = stdBilin b x y := by
  have hε' : ∀ a, ((ε a : ℤ) : ZMod p) = 1 ∨ ((ε a : ℤ) : ZMod p) = -1 := by
    intro a
    rcases hε a with h | h <;> rw [h] <;> simp
  set ρh : Λ → V := fun i => ∑ a, ((ρ i a : ℤ) : ZMod p) • b a with hρh
  set ρh' : Λ → V := fun i => ∑ a, ((ρ' i a : ℤ) : ZMod p) • b a with hρh'
  have hαB : ∀ i v, α i v = l⁻¹ * stdBilin b v (ρh i) := by
    intro i v
    rw [hαρ, stdBilin_apply]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show b.repr (ρh i) a = ((ρ i a : ℤ) : ZMod p) from congrFun (b.repr_sum_self _) a,
      mul_comm]
  have hα'B : ∀ i v, α i (T.symm v) = l'⁻¹ * stdBilin b v (ρh' i) := by
    intro i v
    rw [hαρ', stdBilin_apply]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show b.repr (ρh' i) a = ((ρ' i a : ℤ) : ZMod p) from congrFun (b.repr_sum_self _) a,
      mul_comm]
  have hρu : ∀ i, ρh' i = u (ρh (σ i)) := by
    intro i
    simp only [ρh, ρh', map_sum, map_smul, hu, smul_smul]
    rw [← Equiv.sum_comp π]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hρρ', Int.cast_mul, mul_comm]
  have huiso : ∀ x y, stdBilin b (u x) (u y) = stdBilin b x y :=
    stdBilin_signedPerm b hε' (u := u.toLinearMap) hu
  have hll : l / l' ≠ 0 := div_ne_zero hl hl'
  let g : V ≃ₗ[ZMod p] V :=
    (T.trans u.symm).trans (LinearEquiv.smulOfNeZero (ZMod p) V (l / l') hll)
  have hg : ∀ v, g v = (l / l') • u.symm (T v) := fun v => rfl
  have hhρ₁ : ∀ i, hh i = l • ρh i := hhρ
  have hhρ₂ : ∀ i, T (hh i) = l' • ρh' i := hhρ'
  have hgh : ∀ i, g (hh i) = hh (σ i) := by
    intro i
    rw [hg, hhρ₂, map_smul, hρu, LinearEquiv.symm_apply_apply, smul_smul, hhρ₁]
    congr 1
    field_simp
  have hgα : ∀ i v, α (σ i) (g v) = α i v := by
    intro i v
    have h1 : α i v = α i (T.symm (T v)) := by rw [LinearEquiv.symm_apply_apply]
    rw [h1, hα'B, hαB, hg, hρu, LinearMap.map_smul₂, smul_eq_mul]
    have h2 : stdBilin b (u.symm (T v)) (ρh (σ i)) = stdBilin b (T v) (u (ρh (σ i))) := by
      rw [← huiso, LinearEquiv.apply_symm_apply]
    rw [h2]
    field_simp
  refine ⟨g, ⟨σ, fun i => ⟨hgh i, hgα i⟩⟩, fun v => ?_, fun x y => ?_⟩
  · rw [hg, map_smul, LinearEquiv.apply_symm_apply, smul_smul,
      show l' / l * (l / l') = 1 by field_simp, one_smul]
  ·
    let F : V →ₗ[ZMod p] ZMod p :=
      (stdBilin b (g x)).comp g.toLinearMap - stdBilin b x
    have hF : ∀ w, F w = stdBilin b (g x) (g w) - stdBilin b x w := fun w => rfl
    have hz : ∑ a, F (b a) • b a = 0 := by
      refine hsep _ fun i => ?_
      rw [hαB, stdBilin_repr_functional, hF]
      have hgρ : g (ρh i) = ρh (σ i) := by
        have h1 := hgh i
        rw [hhρ₁, hhρ₁, map_smul] at h1
        exact smul_right_injective V hl h1
      rw [hgρ]
      have h2 := hgα i x
      rw [hαB, hαB] at h2
      have h3 : stdBilin b (g x) (ρh (σ i)) = stdBilin b x (ρh i) := by
        have := congrArg (fun z => l * z) h2
        simp only [← mul_assoc, mul_inv_cancel₀ hl, one_mul] at this
        exact this
      rw [h3, sub_self, mul_zero]
    have h1 := stdBilin_repr_functional b F y
    rw [hz, map_zero, LinearMap.zero_apply, hF] at h1
    exact (sub_eq_zero.mp h1.symm)

theorem ggTorusWNormSC_of_evenSignedPermEltSC_four (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedPermEltSC p R (· = 4)) :
    GGTorusWNormSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ hh α
    hM hC hpair hlin hgen ψ' hψ'
  have : (MulAut.conj : L' →* MulAut L').range.Normal :=
    RootCentExc.normal_range_mulAutConj
  have hn := mem_normalizer_ggAutomizer_of_mem_ggInduced_of_normal
    (H := (MulAut.conj : L' →* MulAut L').range) (Bs := A) hψ'
  obtain ⟨k, Θ, hk3, hk4, -, hD, hP, -, hN⟩ :=
    exists_evenSignedPermModelSC hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc
  subst hk4
  set W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A with hWdef
  have hWin : ∀ u : MulAut (Fin 4 → Multiplicative (ZMod p)),
      (∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ u) → MulAut.congr Θ u ∈ W := by
    rintro u ⟨n, hn, hnu⟩
    rw [← hnu]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  set Wc := W.comap (MulAut.congr Θ).toMonoidHom with hWc
  have hWcsp : ∀ u ∈ Wc, IsSignedPerm ⇑u := by
    intro u hu
    obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hu
    have hv' : MulAut.congr Θ u = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
    have h1 := hN n hcN
    rwa [← hv', MulEquiv.symm_apply_apply] at h1
  have hdW : ∀ i j : Fin 4, i ≠ j → sgnAut i * sgnAut j ∈ Wc := fun i j hij =>
    hWin _ (hD i j hij)
  have hpW : ∀ σ : Equiv.Perm (Fin 4), permAut σ ∈ Wc := fun σ => hWin _ (hP σ)
  have htW : ∀ a b : Fin 4, a ≠ b → permAut (Equiv.swap a b) ∈ Wc := fun a b _ => hpW _
  set φ' := (MulAut.congr Θ).symm ψ' with hφ'
  have hφφ' : ψ' = MulAut.congr Θ φ' := (MulEquiv.apply_symm_apply _ _).symm
  have hnorm : ∀ u ∈ Wc, φ' * u * φ'⁻¹ ∈ Wc := fun u hu => by
    show MulAut.congr Θ (φ' * u * φ'⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv, ← hφφ']
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp hu
  have hnorm' : ∀ u ∈ Wc, φ'⁻¹ * u * φ' ∈ Wc := fun u hu => by
    show MulAut.congr Θ (φ'⁻¹ * u * φ') ∈ W
    rw [map_mul, map_mul, map_inv, ← hφφ']
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) _).mp hu
    rwa [inv_inv] at h1
  have hcl : Subgroup.closure (Set.range φ) ≤ (ggHL ι φ hh α).comap (ggLin (p := p) ι) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure (Or.inl (Or.inl (Set.mem_range_self i)))
  have hclosure : ∀ u ∈ Wc, ggLin (p := p) ι (MulAut.congr Θ u) ∈ ggHL ι φ hh α :=
    fun u hu => hcl (hgen ▸ hu)
  have hc_apply : ∀ (w0 : MulAut (Fin 4 → Multiplicative (ZMod p))) (c : ℕ),
      (∀ f, φ' f = (w0 f) ^ c) → ∀ a, ψ' a = (MulAut.congr Θ w0 a) ^ c := by
    intro w0 c hc a
    obtain ⟨f, rfl⟩ := Θ.surjective a
    rw [hφφ', MulAut.congr_apply, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hc, map_pow]
  by_cases hsA : ∃ i₀, sgnAut i₀ ∈ Wc
  ·
    obtain ⟨i₀, hi₀⟩ := hsA
    have hs : ∀ j, sgnAut j ∈ Wc := by
      intro j
      by_cases hj : j = i₀
      · rw [hj]
        exact hi₀
      · have h2 := Wc.mul_mem (hdW j i₀ hj) hi₀
        rwa [mul_assoc, sgnAut_mul_self, mul_one] at h2
    have hall : ∀ u : MulAut (Fin 4 → Multiplicative (ZMod p)), IsSignedPerm ⇑u → u ∈ Wc :=
      fun u hu => mem_of_isSignedPerm hs htW hu
    obtain ⟨w0, hw0, c, hc⟩ := exists_isSignedPerm_pow hp hp2 (by norm_num)
      (fun u hu => hWcsp _ (hnorm u (hall u hu))) (fun u hu => hWcsp _ (hnorm' u (hall u hu)))
    exact ggWNormConcl_of_signed hp2 ι φ hh α (by norm_num) Θ (hclosure _ (hall _ hw0))
      (by simpa only [MulEquiv.symm_apply_apply] using hw0) (hc_apply w0 c hc)
  push Not at hsA
  have hDle : DScalarTorus.evenSignedGroup ≤ Wc := DScalarTorus.evenSignedGroup_le hp2 hdW hpW
  have hDd : ∀ i j : Fin 4, i ≠ j →
      sgnAut i * sgnAut j ∈ DScalarTorus.evenSignedGroup (p := p) (N := 4) :=
    fun i j hij => DScalarTorus.sgnAut_pair_mem_evenSignedGroup hij
  have hDt : ∀ a b : Fin 4, a ≠ b →
      permAut (Equiv.swap a b) ∈ DScalarTorus.evenSignedGroup (p := p) (N := 4) :=
    fun a b _ => DScalarTorus.permAut_mem_evenSignedGroup _
  have hWcD : Wc ≤ DScalarTorus.evenSignedGroup := by
    intro u hu
    by_contra huD
    rcases mem_or_mul_mem_of_isSignedPerm hDd hDt 0 (hWcsp u hu) with h1 | h1
    · exact huD h1
    have h2 := Wc.mul_mem (Wc.inv_mem hu) (hDle h1)
    rw [inv_mul_cancel_left] at h2
    exact hsA 0 h2
  have hφW : ∀ i, (MulAut.congr Θ).symm (φ i) ∈ Wc := fun i => by
    show MulAut.congr Θ ((MulAut.congr Θ).symm (φ i)) ∈ W
    rw [MulEquiv.apply_symm_apply, hgen]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  obtain ⟨b, hδ, hrD, hsep, hcard⟩ := exists_evenSignedDatum_basis hp hp2 ι (by norm_num) Θ φ hh
    α hlin (fun i => hWcD (hφW i)) (fun a a' h => hgen ▸ hWin _ (hD a a' h))
  have hcongr := ggLin_congr_apply_ofMul (p := p) ι Θ
  have hba : ∀ a, b a = ι (Additive.ofMul (Θ (Pi.mulSingle a (ofAdd 1)))) := by
    intro a
    rw [hδ, one_smul]
  obtain ⟨y, gy, hgy, hgyy, hgya⟩ :=
    exists_signChange_mem_ggDiagramSet hp2 b hM hC hh α hpair hrD (by norm_num) hcard
  have hgs : ggLin (p := p) ι (MulAut.congr Θ (sgnAut y)) = gy := by
    refine b.ext' fun a => ?_
    rw [hba, hcongr, ← hba]
    by_cases hay : a = y
    · subst hay
      rw [sgnAut_mulSingle_self, hgyy, ← Pi.mulSingle_inv, ← ofAdd_neg, hδ, neg_one_smul]
    · rw [sgnAut_mulSingle_of_ne hay, hgya a hay, ← hba]
  have hsgn : ∀ w : MulAut (Fin 4 → Multiplicative (ZMod p)), IsSignedPerm ⇑w →
      ggLin (p := p) ι (MulAut.congr Θ w) ∈ ggHL ι φ hh α := by
    intro w hw
    rcases mem_or_mul_mem_of_isSignedPerm hDd hDt y hw with h1 | h1
    · exact hclosure _ (hDle h1)
    · have he : MulAut.congr Θ w = MulAut.congr Θ (w * sgnAut y) * MulAut.congr Θ (sgnAut y) := by
        rw [← map_mul, mul_assoc, sgnAut_mul_self, mul_one]
      rw [he, map_mul, hgs]
      exact Subgroup.mul_mem _ (hclosure _ (hDle h1)) (Subgroup.subset_closure (Or.inr hgy))
  set T := ggLin (p := p) ι ψ' with hT
  have hpair' : ∀ i j, ((α i).comp T.symm.toLinearMap) (T (hh j)) = (C i j : ZMod p) := by
    intro i j
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, hpair]
  have hrD' : ∀ i, ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod p),
      (∀ a, c a = 1 ∨ c a = -1) ∧ ∏ a, c a = 1 ∧
        ∀ a, b a - ((α i).comp T.symm.toLinearMap) (b a) • T (hh i) = c a • b (σ a) := by
    intro i
    have hmem : (MulAut.congr Θ).symm (ψ' * φ i * ψ'⁻¹) ∈ Wc := by
      show MulAut.congr Θ ((MulAut.congr Θ).symm (ψ' * φ i * ψ'⁻¹)) ∈ W
      rw [MulEquiv.apply_symm_apply]
      have h1 : φ i ∈ W := by
        rw [hgen]
        exact Subgroup.subset_closure (Set.mem_range_self i)
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp h1
    obtain ⟨σ, c, hc1, hc2, hu⟩ := hWcD hmem
    refine ⟨σ, c, hc1, hc2, fun a => ?_⟩
    have h1 : b a - ((α i).comp T.symm.toLinearMap) (b a) • T (hh i) =
        ggLin (p := p) ι (ψ' * φ i * ψ'⁻¹) (b a) := by
      rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hT]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      rw [hlin, map_sub, map_smul]
      change _ = T (T.symm (b a)) - (α i) (T.symm (b a)) • T (hh i)
      rw [LinearEquiv.apply_symm_apply]
    rw [h1, hba, ← MulEquiv.apply_symm_apply (MulAut.congr Θ) (ψ' * φ i * ψ'⁻¹), hcongr,
      IsSignedPerm.apply_mulSingle hu, mul_one, hδ]
  obtain ⟨l, ρ, hl, hρ, hgram, hhρ, hαρ⟩ :=
    exists_dRoots_of_evenSignedRefl hp2 b hM hC hh α hpair hrD (by omega)
  obtain ⟨l', ρ', hl', hρ', hgram', hhρ', hαρ'⟩ :=
    exists_dRoots_of_evenSignedRefl hp2 b hM hC (fun i => T (hh i))
      (fun i => (α i).comp T.symm.toLinearMap) hpair' hrD' (by omega)
  obtain ⟨π, ε, σ, hε, -, hρρ'⟩ :=
    exists_signedPerm_of_dRoot_bases_four hM hC ρ ρ' hρ hρ' hgram hgram' hcard
  have hε' : ∀ a, ((ε a : ℤ) : ZMod p) = 1 ∨ ((ε a : ℤ) : ZMod p) = -1 := by
    intro a
    rcases hε a with h1 | h1 <;> rw [h1] <;> simp
  set w1 := (permAut π * diagAut (fun a => ((ε a : ℤ) : ZMod p))
    fun a => coord_sign_mul_self (hε' a) : MulAut (Fin 4 → Multiplicative (ZMod p))) with hw1
  have hw1s : IsSignedPerm ⇑w1 := isSignedPerm_permAut_mul_diagAut π _ hε'
  set u1 := ggLin (p := p) ι (MulAut.congr Θ w1) with hu1
  have hu1b : ∀ a, u1 (b a) = ((ε a : ℤ) : ZMod p) • b (π a) := by
    intro a
    rw [hu1, hba, hcongr, hw1, MulAut.mul_apply, diagAut_mulSingle, permAut_mulSingle, mul_one,
      hδ]
  obtain ⟨g, hgD, hTg, hgiso⟩ := exists_diagram_of_dRoot_bases b hh α T hl hl' hhρ hαρ hhρ'
    (fun i v => hαρ' i v) hε hρρ' u1 hu1b hsep
  have hU : u1 * g ∈ ggHL ι φ hh α :=
    Subgroup.mul_mem _ (hsgn w1 hw1s) (Subgroup.subset_closure (Or.inr hgD))
  have hcne : l' / l ≠ 0 := div_ne_zero hl' hl
  refine ⟨⟨Units.mk0 (l' / l) hcne, u1 * g, hU, fun v => ?_⟩, fun href => ?_⟩
  · rw [Units.val_mk0, LinearEquiv.mul_apply]
    exact hTg v
  · have : Finite V := Finite.of_equiv ↥A (Additive.ofMul.trans ι.toEquiv)
    have hTr := (ggIsReflection_iff_ggLinRefl hp2 ι ψ').mp href
    have hUiso : ∀ x z, OrthExcEven.stdBilin b ((u1 * g) x) ((u1 * g) z) =
        OrthExcEven.stdBilin b x z := by
      intro x z
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      exact (stdBilin_signedPerm b hε' (u := u1.toLinearMap) hu1b (g x) (g z)).trans (hgiso x z)
    rcases eq_one_or_neg_one_of_linRefl_smul_isometry hp2 (by norm_num) b hTr hUiso
      (fun v => by rw [LinearEquiv.mul_apply]; exact hTg v) with hc | hc
    · have he : ggLin (p := p) ι ψ' = u1 * g := by
        ext v
        rw [← hT, hTg, hc, one_smul, LinearEquiv.mul_apply]
      rw [he]
      exact hU
    · have he : ggLin (p := p) ι ψ' = LinearEquiv.neg (ZMod p) * (u1 * g) := by
        ext v
        rw [← hT, hTg, hc, neg_one_smul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          LinearEquiv.neg_apply]
      rw [he]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _))))
        hU

end OrthExcEven

section Certificates


theorem ggTorusWNormSC_omegaPlus_four {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) :
    GGTorusWNormSC p (OrthRest.RPlus K 4) (LargeEvenInnSet _) := by
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by norm_num : 3 ≤ 4)
  exact OrthExcEven.ggTorusWNormSC_of_evenSignedPermEltSC_four hp hp2 subset_rfl hZ hcp
    (ggOrthEvenTorusInput_holds.1 K 4 p le_rfl hp (hpq.imp id fun h => ⟨by decide, h⟩))

theorem largeEvenLabelAll_wnorm_orth_four {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : lab.tag = .D ∧ lab.rank = 4 ∧
      (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, l, n⟩
  obtain ⟨htag, hl, hpq⟩ := hlab
  dsimp only at htag hl hpq ⊢
  subst htag
  subst hl
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [ite_eq_right (by decide)] at hQ ⊢
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_omegaPlus_four hp hp2 (by rw [hK]; exact hpq)

end Certificates

end CFSG.StandardType

end

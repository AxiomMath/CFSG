module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsPairs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.Timmesfeld.ARS.CaseOAWeyl
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.SpecialLinear

abbrev ggOrthA_WA (n : ℕ) : Type := (coxeterMatrix (isFiniteType_A n)).Group

@[expose] def ggOrthA_AReflRoot (n : ℕ) (t : ggOrthA_WA n) (γ : Fin (n + 1) → ℤ) : Prop :=
  ∃ (w : ggOrthA_WA n) (i : Fin n), t = w * (coxeterMatrix (isFiniteType_A n)).simple i * w⁻¹ ∧
    toStd n (weylAction (isFiniteType_A n) w (Pi.single i 1)) = γ

theorem ggOrthA_weylAction_simpleA {n : ℕ} (i : Fin n) :
    weylAction (isFiniteType_A n) ((coxeterMatrix (isFiniteType_A n)).simple i) =
      reflection (CartanMatrix.A n) i := by
  simpa only [CoxeterMatrix.toCoxeterSystem_simple] using weylAction_simple (isFiniteType_A n) i

theorem ggOrthA_ggDReflect_comp {k : ℕ} (π : Equiv.Perm (Fin k)) (γ x : Fin k → ℤ) :
    ggDReflect (γ ∘ π) (x ∘ π) = ggDReflect γ x ∘ π := by
  have h : ggDDot (x ∘ π) (γ ∘ π) = ggDDot x γ := Equiv.sum_comp π fun c => x c * γ c
  funext c
  simp only [ggDReflect_apply, Function.comp_apply, h]

theorem ggOrthA_ggDReflect_sub_swap {k : ℕ} {x y : Fin k} (hxy : x ≠ y) (u : Fin k → ℤ) :
    ggDReflect (Pi.single x 1 - Pi.single y 1) u = u ∘ Equiv.swap x y := by
  rw [sub_eq_add_neg, ← Pi.single_neg, ggDReflect_swap hxy]

theorem ggOrthA_refl_action {n : ℕ} {t : ggOrthA_WA n} {γ : Fin (n + 1) → ℤ} (h : ggOrthA_AReflRoot n t γ)
    (v : Fin n → ℤ) :
    toStd n (weylAction (isFiniteType_A n) t v) = ggDReflect γ (toStd n v) := by
  obtain ⟨w, i, rfl, rfl⟩ := h
  obtain ⟨π, hπ⟩ := CFSG.Timmesfeld.ARS.CaseOA.exists_perm_toStd_weylAction w
  have key : ∀ u, toStd n (weylAction (isFiniteType_A n)
      (w * (coxeterMatrix (isFiniteType_A n)).simple i * w⁻¹) (weylAction (isFiniteType_A n) w u)) =
      ggDReflect (toStd n (weylAction (isFiniteType_A n) w (Pi.single i 1)))
        (toStd n (weylAction (isFiniteType_A n) w u)) := by
    intro u
    rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_inv_apply_apply, hπ, hπ, hπ,
      ggOrthA_weylAction_simpleA, toStd_reflection, toStd_single, ggOrthA_ggDReflect_comp,
      ggOrthA_ggDReflect_sub_swap Fin.castSucc_lt_succ.ne]
  have := key (weylAction (isFiniteType_A n) w⁻¹ v)
  rwa [weylAction_apply_inv_apply] at this

theorem ggOrthA_refl_unique {n : ℕ} {t t' : ggOrthA_WA n} {γ γ' : Fin (n + 1) → ℤ}
    (h : ggOrthA_AReflRoot n t γ) (h' : ggOrthA_AReflRoot n t' γ') (hγ : γ' = γ ∨ γ' = -γ) : t = t' := by
  apply weylAction_injective (isFiniteType_A n)
  refine LinearMap.ext fun v => toStd_injective n ?_
  rw [ggOrthA_refl_action h, ggOrthA_refl_action h']
  rcases hγ with rfl | rfl
  · rfl
  · rw [ggDReflect_neg]

private theorem refl_conj {n : ℕ} {t : ggOrthA_WA n} {γ : Fin (n + 1) → ℤ} (h : ggOrthA_AReflRoot n t γ)
    {g : ggOrthA_WA n} {f : (Fin (n + 1) → ℤ) → Fin (n + 1) → ℤ}
    (hg : ∀ v, toStd n (weylAction (isFiniteType_A n) g v) = f (toStd n v)) :
    ggOrthA_AReflRoot n (g * t * g⁻¹) (f γ) := by
  obtain ⟨w, i, rfl, rfl⟩ := h
  exact ⟨g * w, i, by group, by rw [weylAction_mul_apply, hg]⟩

theorem ggOrthA_refl_mem {n : ℕ} {t : ggOrthA_WA n} {γ : Fin (n + 1) → ℤ} (h : ggOrthA_AReflRoot n t γ) :
    ∃ p q : Fin (n + 1), p ≠ q ∧ γ = Pi.single p 1 - Pi.single q 1 := by
  obtain ⟨w, i, -, rfl⟩ := h
  have hmem : weylAction (isFiniteType_A n) w (Pi.single i 1) ∈ roots (isFiniteType_A n) ∅ :=
    Or.inl ⟨w, i, rfl⟩
  rw [roots_eq n] at hmem
  exact hmem

private theorem exists_perm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    ∃ g : ggOrthA_WA n, ∀ v, toStd n (weylAction (isFiniteType_A n) g v) = toStd n v ∘ σ := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top σ
  induction hσ using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨(coxeterMatrix (isFiniteType_A n)).simple k, fun v => by
      rw [ggOrthA_weylAction_simpleA, toStd_reflection]⟩
  | one => exact ⟨1, fun v => by rw [map_one, Module.End.one_apply]; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨g, hg⟩ := hx
    obtain ⟨g', hg'⟩ := hy
    exact ⟨g' * g, fun v => by rw [weylAction_mul_apply, hg', hg]; rfl⟩

theorem ggOrthA_disj_of_dot {k : ℕ} {p q r s : Fin k} (hpq : p ≠ q) (hrs : r ≠ s)
    (h : ggDDot (Pi.single p 1 - Pi.single q 1 : Fin k → ℤ) (Pi.single r 1 - Pi.single s 1) = 0) :
    p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s := by
  rw [ggDDot_eq_dotProduct, sub_dotProduct, single_dotProduct, single_dotProduct, one_mul,
    one_mul] at h
  simp only [Pi.sub_apply, Pi.single_apply] at h
  split_ifs at h <;> simp_all

theorem ggOrthA_dot_self {k : ℕ} {p q : Fin k} (hpq : p ≠ q) :
    ggDDot (Pi.single p 1 - Pi.single q 1 : Fin k → ℤ) (Pi.single p 1 - Pi.single q 1) = 2 :=
  ggDDot_self_of_mem ⟨p, q, 1, -1, hpq, Or.inl rfl, Or.inr rfl, by
    rw [sub_eq_add_neg, Pi.single_neg]⟩

private theorem sub_comp {k : ℕ} (σ : Equiv.Perm (Fin k)) {a b p q : Fin k} (hσa : σ a = p)
    (hσb : σ b = q) :
    (Pi.single p 1 - Pi.single q 1 : Fin k → ℤ) ∘ σ = Pi.single a 1 - Pi.single b 1 := by
  subst hσa hσb
  rw [Pi.sub_comp, Pi.single_comp_equiv, Pi.single_comp_equiv, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

private theorem exists_perm_four {k : ℕ} {a b c d a' b' c' d' : Fin k} (hab : a ≠ b)
    (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hab' : a' ≠ b')
    (hcd' : c' ≠ d') (hac' : a' ≠ c') (had' : a' ≠ d') (hbc' : b' ≠ c') (hbd' : b' ≠ d') :
    ∃ σ : Equiv.Perm (Fin k), σ a = a' ∧ σ b = b' ∧ σ c = c' ∧ σ d = d' := by
  have := hab.symm; have := hcd.symm; have := hac.symm; have := had.symm; have := hbc.symm
  have := hbd.symm; have := hab'.symm; have := hcd'.symm; have := hac'.symm
  have := had'.symm; have := hbc'.symm; have := hbd'.symm
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ![a, b, c, d] ![a', b', c', d']
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  exact ⟨σ, by simpa using hσ 0, by simpa using hσ 1, by simpa using hσ 2, by simpa using hσ 3⟩

private theorem orth_conj {n : ℕ} {t t' : ggOrthA_WA n} {γ γ' : Fin (n + 1) → ℤ} (ht : ggOrthA_AReflRoot n t γ)
    (ht' : ggOrthA_AReflRoot n t' γ') (hne : t ≠ t') (hcomm : t * t' = t' * t) {a b : Fin n}
    (hab : (CoxeterMatrix.A n).M a b = 2) :
    ∃ w : ggOrthA_WA n, w * (coxeterMatrix (isFiniteType_A n)).simple a * w⁻¹ = t ∧
      w * (coxeterMatrix (isFiniteType_A n)).simple b * w⁻¹ = t' := by
  obtain ⟨p, q, hpq, hγ⟩ := ggOrthA_refl_mem ht
  obtain ⟨r, s, hrs, hγ'⟩ := ggOrthA_refl_mem ht'
  obtain ⟨w, i, -, hw⟩ := id ht
  have key : toStd n (weylAction (isFiniteType_A n) (t * t')
        (weylAction (isFiniteType_A n) w (Pi.single i 1))) =
      toStd n (weylAction (isFiniteType_A n) (t' * t)
        (weylAction (isFiniteType_A n) w (Pi.single i 1))) := by
    rw [hcomm]
  rw [weylAction_mul_apply, weylAction_mul_apply, ggOrthA_refl_action ht, ggOrthA_refl_action ht',
    ggOrthA_refl_action ht', ggOrthA_refl_action ht, hw] at key
  have h2 : ggDDot γ γ = 2 := by rw [hγ]; exact ggOrthA_dot_self hpq
  have h2' : ggDDot γ' γ' = 2 := by rw [hγ']; exact ggOrthA_dot_self hrs
  rcases ggDReflect_comm_dot h2 h2' key with h0 | h0 | h0
  swap
  · exact absurd (ggOrthA_refl_unique ht ht' (Or.inl h0)) hne
  swap
  · exact absurd (ggOrthA_refl_unique ht ht' (Or.inr h0)) hne
  rw [hγ, hγ'] at h0
  obtain ⟨h1, h2, h3, h4⟩ := ggOrthA_disj_of_dot hpq hrs h0
  have hab' : a.val + 1 < b.val ∨ b.val + 1 < a.val := by
    simp only [CoxeterMatrix.A, Matrix.of_apply, Fin.ext_iff] at hab
    split_ifs at hab <;> omega
  obtain ⟨σ, hσp, hσq, hσr, hσs⟩ := exists_perm_four hpq hrs h1 h2 h3 h4
    (Fin.castSucc_lt_succ (i := a)).ne (Fin.castSucc_lt_succ (i := b)).ne
    (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc]; omega))
    (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
    (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
    (Fin.ne_of_val_ne (by simp only [Fin.val_succ]; omega))
  obtain ⟨g, hg⟩ := exists_perm σ
  have hpa : ggOrthA_AReflRoot n (g * (coxeterMatrix (isFiniteType_A n)).simple a * g⁻¹)
      (toStd n (Pi.single a 1) ∘ σ) := refl_conj (f := fun u => u ∘ σ) ⟨1, a, by group, by
        rw [map_one, Module.End.one_apply]⟩ hg
  have hpb : ggOrthA_AReflRoot n (g * (coxeterMatrix (isFiniteType_A n)).simple b * g⁻¹)
      (toStd n (Pi.single b 1) ∘ σ) := refl_conj (f := fun u => u ∘ σ) ⟨1, b, by group, by
        rw [map_one, Module.End.one_apply]⟩ hg
  rw [toStd_single, sub_comp σ hσp hσq] at hpa
  rw [toStd_single, sub_comp σ hσr hσs] at hpb
  exact ⟨g, ggOrthA_refl_unique hpa ht (Or.inl hγ), ggOrthA_refl_unique hpb ht' (Or.inl hγ')⟩

theorem ggOrthA_exists_groupEquiv_of_eq {B : Type} {M N : CoxeterMatrix B} (h : M = N) :
    ∃ φ : M.Group ≃* N.Group, ∀ i, φ (M.simple i) = N.simple i := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ => rfl⟩

theorem ggOrthA_reindex_groupEquiv_A {ι : Type} {n : ℕ} (e : Fin n ≃ ι) :
    ∃ φ : ((CoxeterMatrix.A n).reindex e).Group ≃* ggOrthA_WA n, ∀ x : ι,
      φ (((CoxeterMatrix.A n).reindex e).simple x) =
        (coxeterMatrix (isFiniteType_A n)).simple (e.symm x) := by
  obtain ⟨ψ, hψ⟩ := ggOrthA_exists_groupEquiv_of_eq
    (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_A n) (ggIntCartan_A n)).symm
  exact ⟨((CoxeterMatrix.A n).reindexGroupEquiv e).trans ψ, fun x => by
    rw [MulEquiv.trans_apply, CoxeterMatrix.reindexGroupEquiv_apply_simple, hψ]⟩

theorem ggOrth_conj_A {ι : Type} {M : CoxeterMatrix ι} {n : ℕ} {e : Fin n ≃ ι}
    (hM : M = (CoxeterMatrix.A n).reindex e) {t t' : M.Group}
    (ht : ∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹)
    (ht' : ∃ (w : M.Group) (i : ι), t' = w * M.simple i * w⁻¹) (hne : t ≠ t')
    (hcomm : t * t' = t' * t) {i j : ι} (h2 : M.M i j = 2) :
    ∃ w : M.Group, w * M.simple i * w⁻¹ = t ∧ w * M.simple j * w⁻¹ = t' := by
  subst hM
  obtain ⟨φ, hφ⟩ := ggOrthA_reindex_groupEquiv_A e
  have hrefl : ∀ x : ((CoxeterMatrix.A n).reindex e).Group,
      (∃ w i, x = w * ((CoxeterMatrix.A n).reindex e).simple i * w⁻¹) →
        ∃ γ, ggOrthA_AReflRoot n (φ x) γ := by
    rintro x ⟨w, i, rfl⟩
    exact ⟨_, φ w, e.symm i, by rw [map_mul, map_mul, map_inv, hφ], rfl⟩
  obtain ⟨γ, hγ⟩ := hrefl t ht
  obtain ⟨γ', hγ'⟩ := hrefl t' ht'
  obtain ⟨w, hw, hw'⟩ := orth_conj hγ hγ' (φ.injective.ne hne)
    (by rw [← map_mul, hcomm, map_mul]) (a := e.symm i) (b := e.symm j)
    (by rwa [CoxeterMatrix.reindex_apply] at h2)
  refine ⟨φ.symm w, φ.injective ?_, φ.injective ?_⟩
  · rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hφ, hw]
  · rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hφ, hw']

end CFSG.StandardType

end

module

public import CFSG.Monster.B.GSide.CommutatorTest
public import CFSG.Monster.B.GSide.CompletionSubgroup
public import CFSG.Monster.B.GSide.NativeTrianglePresentation
public import CFSG.Monster.B.GSide.TriangleData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

section Generic

variable {X : Type*} [Group X]

theorem conj_mul_pow_three_eq_inv {a s : X} (ha : a * a = 1) (hs : s * s = 1) :
    a * (a * s) ^ 3 * a⁻¹ = ((a * s) ^ 3)⁻¹ ∧ s * (a * s) ^ 3 * s⁻¹ = ((a * s) ^ 3)⁻¹ ∧
      a * (a * s) ^ 3 = s * a * s * (s * a)⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have haa : ∀ y : X, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, ha', hs', mul_assoc, haa]
  · simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, ha', hs', mul_assoc, hs, mul_one]
  · simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, ha', hs', mul_assoc, haa]

end Generic

section Transport

variable {S Y : Type*} [Group S] [Group Y]

theorem transport_conj_mul {T : Set S} {Ψ : S → Y} {t t' : S} {tY tY' : Y}
    (h : ∀ k ∈ T, t * k * t⁻¹ ∈ T ∧ tY * Ψ k * tY⁻¹ = Ψ (t * k * t⁻¹))
    (h' : ∀ k ∈ T, t' * k * t'⁻¹ ∈ T ∧ tY' * Ψ k * tY'⁻¹ = Ψ (t' * k * t'⁻¹)) :
    ∀ k ∈ T, t * t' * k * (t * t')⁻¹ ∈ T ∧
      tY * tY' * Ψ k * (tY * tY')⁻¹ = Ψ (t * t' * k * (t * t')⁻¹) := by
  intro k hk
  obtain ⟨h1, h2⟩ := h' k hk
  obtain ⟨h3, h4⟩ := h _ h1
  have e : t * t' * k * (t * t')⁻¹ = t * (t' * k * t'⁻¹) * t⁻¹ := by group
  refine ⟨e ▸ h3, ?_⟩
  rw [e, ← h4, ← h2]
  group

theorem transport_conj_pow {T : Set S} {Ψ : S → Y} {t : S} {tY : Y}
    (h : ∀ k ∈ T, t * k * t⁻¹ ∈ T ∧ tY * Ψ k * tY⁻¹ = Ψ (t * k * t⁻¹)) (n : ℕ) :
    ∀ k ∈ T, t ^ n * k * (t ^ n)⁻¹ ∈ T ∧
      tY ^ n * Ψ k * (tY ^ n)⁻¹ = Ψ (t ^ n * k * (t ^ n)⁻¹) := by
  induction n with
  | zero => intro k hk; simpa using hk
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact transport_conj_mul ih h

end Transport

private theorem conj_clabelS
    (t : Shat) (v : CVert) :
    t * clabelS v * t⁻¹ = clabelS (cvMul v t⁻¹) := by
  rw [CFSG.Monster.B.GSide.clabelS_cvMul, inv_inv]

private theorem cvMul_inv_of_eq
    {v w : CVert} {t : Shat} (h : cvMul w t = v) :
    cvMul v t⁻¹ = w := by
  rw [← h, cvMul_inv_cancel]

theorem pow_three_eq_one_of_cycle
    {x y v w u : CVert} (hvw : v ≠ w) (hvu : v ≠ u)
    (h₀ : cvMul v (clabelS x * clabelS y) = w) (h₁ : cvMul w (clabelS x * clabelS y) = u)
    (h₂ : cvMul u (clabelS x * clabelS y) = v) : (clabelS x * clabelS y) ^ 3 = 1 := by
  have h34 := CTIB.commute_or_three_or_four native_coset_graph_diameter_three_rank_five.2.1
    (labelsInput_of_ambient ambientRootOrbitsHyp) x y
  rcases h34 with hc | ⟨-, ho⟩ | ⟨-, ho⟩
  · have h2 := CTIB.sq_clabelS_mul_of_commute hc
    generalize clabelS x * clabelS y = g at h₀ h₁ h2
    have e : cvMul v (g ^ 2) = u := by rw [pow_two, cvMul_mul, h₀, h₁]
    rw [h2, cvMul_one] at e
    exact absurd e hvu
  · rw [← ho]
    exact pow_orderOf_eq_one _
  · have h4 : (clabelS x * clabelS y) ^ 4 = 1 := by
      rw [← ho]
      exact pow_orderOf_eq_one _
    generalize clabelS x * clabelS y = g at h₀ h₁ h₂ h4
    have e : cvMul v (g ^ 4) = w := by
      rw [pow_succ, pow_succ, pow_two, cvMul_mul, cvMul_mul, cvMul_mul, h₀, h₁, h₂, h₀]
    rw [h4, cvMul_one] at e
    exact absurd e hvw

section GSide

variable {G : Type*} [Group G] {d : G}

open _root_.Classical in
private def psiTot
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (k : Shat) : G :=
  if hk : k ∈ vStab cv0 then psiInvHom ψ ⟨k, hk⟩ else 1

variable (ψ : Subgroup.centralizer {d} ≃* vStab cv0)

private theorem psiTot_of_mem {k : Shat} (hk : k ∈ vStab cv0) :
    psiTot ψ k = psiInvHom ψ ⟨k, hk⟩ :=
  dite_eq_left hk

private theorem psiTot_mul {k l : Shat} (hk : k ∈ vStab cv0) (hl : l ∈ vStab cv0) :
    psiTot ψ (k * l) = psiTot ψ k * psiTot ψ l := by
  rw [psiTot_of_mem ψ (mul_mem hk hl), psiTot_of_mem ψ hk, psiTot_of_mem ψ hl, ← map_mul]
  rfl

private theorem psiTot_inv {k : Shat} (hk : k ∈ vStab cv0) :
    psiTot ψ k⁻¹ = (psiTot ψ k)⁻¹ := by
  rw [psiTot_of_mem ψ (inv_mem hk), psiTot_of_mem ψ hk, ← map_inv]
  rfl

private theorem psiTot_one : psiTot ψ 1 = 1 := by
  rw [psiTot_of_mem ψ (one_mem _), ← map_one (psiInvHom ψ)]
  rfl

private theorem psiTot_conj {t k : Shat} (ht : t ∈ vStab cv0) (hk : k ∈ vStab cv0) :
    psiTot ψ t * psiTot ψ k * (psiTot ψ t)⁻¹ = psiTot ψ (t * k * t⁻¹) := by
  rw [psiTot_mul ψ (mul_mem ht hk) (inv_mem ht), psiTot_mul ψ ht hk, psiTot_inv ψ ht]

private theorem psiTot_inj {k l : Shat} (hk : k ∈ vStab cv0) (hl : l ∈ vStab cv0)
    (h : psiTot ψ k = psiTot ψ l) : k = l := by
  rw [psiTot_of_mem ψ hk, psiTot_of_mem ψ hl] at h
  exact congrArg Subtype.val (psiInvHom_injective ψ h)

private theorem psiTot_psi (z : Subgroup.centralizer {d}) : psiTot ψ (ψ z : Shat) = z := by
  rw [psiTot_of_mem ψ (ψ z).2, psiInvHom_apply]
  exact congrArg Subtype.val (ψ.symm_apply_apply z)

omit ψ in
theorem exists_triangleHom_1782
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0)
    (φe : ↥(cvSetStab {cv0, cw0}) →* G)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}),
      psiInvHom ψ ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hDC : ∃ y, ∃ hs : clabelS y ∈ cvSetStab {cv0, cw0},
      IsTriB 0 (clabelS y) ∧ IsConj d (φe ⟨clabelS y, hs⟩)) :
    ∃ φt : ↥(cvSetStab {cv0, cw0, cu 0}) →* G,
      (∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
        psiInvHom ψ ⟨a, ha⟩ = φt ⟨a, hb⟩) ∧
      (∀ a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
        φe ⟨a, ha⟩ = φt ⟨a, hb⟩) := by
  have hA := exists_isTriA_adj
  obtain ⟨x, hx, ha⟩ := hA
  obtain ⟨x', hsE, hb, hsD⟩ := hDC
  have hvw : cv0 ≠ cw0 := cgraph_adj_cv0_cw0.ne
  have hvu : cv0 ≠ cu 0 := (cgraph_adj_cu 0).1.ne
  have hKE : ∀ k ∈ triKer 0, k ∈ cvSetStab {cv0, cw0} := fun k hk => cEdgeFix_le_cEdgeStab hk.1
  have hnorm : ∀ t : Shat, (∀ p, p = cv0 ∨ p = cw0 ∨ p = cu 0 →
      cvMul p t = cv0 ∨ cvMul p t = cw0 ∨ cvMul p t = cu 0) →
      ∀ k ∈ triKer 0, t * k * t⁻¹ ∈ triKer 0 := by
    intro t ht k hk
    have hfix : ∀ q, q = cv0 ∨ q = cw0 ∨ q = cu 0 → cvMul q k = q := by
      rintro q (rfl | rfl | rfl)
      · exact hk.1.1
      · exact hk.1.2
      · exact hk.2
    have key : ∀ p, p = cv0 ∨ p = cw0 ∨ p = cu 0 → cvMul p (t * k * t⁻¹) = p := fun p hp => by
      rw [cvMul_mul, cvMul_mul, hfix _ (ht p hp), cvMul_inv_cancel]
    exact ⟨⟨key _ (Or.inl rfl), key _ (Or.inr (Or.inl rfl))⟩, key _ (Or.inr (Or.inr rfl))⟩
  have hpa : ∀ p, p = cv0 ∨ p = cw0 ∨ p = cu 0 → cvMul p (clabelS x) = cv0 ∨
      cvMul p (clabelS x) = cw0 ∨ cvMul p (clabelS x) = cu 0 := by
    rintro p (rfl | rfl | rfl)
    · exact Or.inl ha.1
    · exact Or.inr (Or.inr ha.2.1)
    · exact Or.inr (Or.inl ha.2.2)
  have hps : ∀ p, p = cv0 ∨ p = cw0 ∨ p = cu 0 → cvMul p (clabelS x') = cv0 ∨
      cvMul p (clabelS x') = cw0 ∨ cvMul p (clabelS x') = cu 0 := by
    rintro p (rfl | rfl | rfl)
    · exact Or.inr (Or.inl hb.1)
    · exact Or.inl hb.2.1
    · exact Or.inr (Or.inr hb.2.2)
  have hcH : clabelS cv0 ∈ vStab cv0 := clabelS_mem_vStab_self cv0
  have heH : clabelS cw0 ∈ vStab cv0 := clabelS_mem_vStab_cv0_of_adj cgraph_adj_cv0_cw0
  have haH : clabelS x ∈ vStab cv0 := clabelS_mem_vStab_cv0_of_adj hx
  have hcube : (clabelS x * clabelS x') ^ 3 = 1 :=
    pow_three_eq_one_of_cycle hvw hvu
      ((cvMul_mul _ _ _).trans ((congrArg (cvMul · (clabelS x')) ha.1).trans hb.1))
      ((cvMul_mul _ _ _).trans ((congrArg (cvMul · (clabelS x')) ha.2.1).trans hb.2.2))
      ((cvMul_mul _ _ _).trans ((congrArg (cvMul · (clabelS x')) ha.2.2).trans hb.2.1))
  have hd : psiTot ψ (clabelS cv0) = d := by
    rw [psiTot_of_mem ψ hcH, psiInvHom_apply]
    exact congrArg Subtype.val ((MulEquiv.symm_apply_eq ψ).2 hψ.symm)
  have hΨE : ∀ k (hk : k ∈ vStab cv0) (hkE : k ∈ cvSetStab {cv0, cw0}),
      φe ⟨k, hkE⟩ = psiTot ψ k := fun k hk hkE => by
    rw [psiTot_of_mem ψ hk]
    exact (hve k hk hkE).symm
  have hφconj : ∀ t (ht : t ∈ cvSetStab {cv0, cw0}) k, k ∈ vStab cv0 →
      k ∈ cvSetStab {cv0, cw0} → t * k * t⁻¹ ∈ vStab cv0 →
      φe ⟨t, ht⟩ * psiTot ψ k * (φe ⟨t, ht⟩)⁻¹ = psiTot ψ (t * k * t⁻¹) := by
    intro t ht k hk hkE hkt
    have e3 : φe (⟨t, ht⟩ * ⟨k, hkE⟩ * ⟨t, ht⟩⁻¹) =
        φe ⟨t, ht⟩ * φe ⟨k, hkE⟩ * (φe ⟨t, ht⟩)⁻¹ :=
      (map_mul φe _ _).trans (congrArg₂ (· * ·) (map_mul φe _ _) (map_inv φe _))
    calc φe ⟨t, ht⟩ * psiTot ψ k * (φe ⟨t, ht⟩)⁻¹
        = φe ⟨t, ht⟩ * φe ⟨k, hkE⟩ * (φe ⟨t, ht⟩)⁻¹ :=
          congrArg (fun z => φe ⟨t, ht⟩ * z * (φe ⟨t, ht⟩)⁻¹) (hΨE k hk hkE).symm
      _ = φe (⟨t, ht⟩ * ⟨k, hkE⟩ * ⟨t, ht⟩⁻¹) := e3.symm
      _ = psiTot ψ (t * k * t⁻¹) :=
        hΨE (t * k * t⁻¹) hkt (mul_mem (mul_mem ht hkE) (inv_mem ht))
  have hQa : ∀ k ∈ ((triKer 0 : Subgroup Shat) : Set Shat),
      clabelS x * k * (clabelS x)⁻¹ ∈ ((triKer 0 : Subgroup Shat) : Set Shat) ∧
      psiTot ψ (clabelS x) * psiTot ψ k * (psiTot ψ (clabelS x))⁻¹ =
        psiTot ψ (clabelS x * k * (clabelS x)⁻¹) :=
    fun k hk => ⟨hnorm _ hpa k hk, psiTot_conj ψ haH hk.1.1⟩
  have hQs : ∀ k ∈ ((triKer 0 : Subgroup Shat) : Set Shat),
      clabelS x' * k * (clabelS x')⁻¹ ∈ ((triKer 0 : Subgroup Shat) : Set Shat) ∧
      φe ⟨clabelS x', hsE⟩ * psiTot ψ k * (φe ⟨clabelS x', hsE⟩)⁻¹ =
        psiTot ψ (clabelS x' * k * (clabelS x')⁻¹) :=
    fun k hk => ⟨hnorm _ hps k hk, hφconj _ hsE k hk.1.1 (hKE k hk) (hnorm _ hps k hk).1.1⟩
  have heD : IsConj d (psiTot ψ (clabelS cw0)) := by
    have hsc : clabelS x' * clabelS cv0 * (clabelS x')⁻¹ = clabelS cw0 := by
      rw [conj_clabelS, cvMul_inv_of_eq hb.2.1]
    refine isConj_iff.2 ⟨φe ⟨clabelS x', hsE⟩, ?_⟩
    calc φe ⟨clabelS x', hsE⟩ * d * (φe ⟨clabelS x', hsE⟩)⁻¹
        = φe ⟨clabelS x', hsE⟩ * psiTot ψ (clabelS cv0) * (φe ⟨clabelS x', hsE⟩)⁻¹ :=
          congrArg (fun z => φe ⟨clabelS x', hsE⟩ * z * (φe ⟨clabelS x', hsE⟩)⁻¹) hd.symm
      _ = psiTot ψ (clabelS x' * clabelS cv0 * (clabelS x')⁻¹) :=
          (hQs _ (clabelS_cv0_mem_triKer 0)).2
      _ = psiTot ψ (clabelS cw0) := congrArg (psiTot ψ) hsc
  have haD : IsConj d (psiTot ψ (clabelS x)) := by
    have hlam : lamW0H ∈ dH ψ := by
      have h := heD
      rw [psiTot_of_mem ψ heH, psiInvHom_apply] at h
      exact h
    have h := mem_dH_of_isConj ψ hlam (RA_isConj lamW0H ⟨clabelS x, haH⟩ lamW0H_mem_RA
      ⟨x, hx, rfl⟩)
    rw [psiTot_of_mem ψ haH, psiInvHom_apply]
    exact h
  have haG2 : psiTot ψ (clabelS x) * psiTot ψ (clabelS x) = 1 := by
    rw [← psiTot_mul ψ haH haH, clabelS_mul_clabelS, psiTot_one]
  have hsG2 : φe ⟨clabelS x', hsE⟩ * φe ⟨clabelS x', hsE⟩ = 1 :=
    (map_mul φe _ _).symm.trans
      ((congrArg φe (Subtype.ext (clabelS_mul_clabelS x'))).trans (map_one φe))
  have hinv := conj_mul_pow_three_eq_inv haG2 hsG2
  have hQ3 := transport_conj_pow (transport_conj_mul hQa hQs) 3
  have hXk : ∀ k ∈ triKer 0,
      (psiTot ψ (clabelS x) * φe ⟨clabelS x', hsE⟩) ^ 3 * psiTot ψ k =
        psiTot ψ k * (psiTot ψ (clabelS x) * φe ⟨clabelS x', hsE⟩) ^ 3 := by
    intro k hk
    have h := (hQ3 k hk).2
    simp only [hcube, one_mul, inv_one, mul_one] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hXd : (psiTot ψ (clabelS x) * φe ⟨clabelS x', hsE⟩) ^ 3 ∈ Subgroup.centralizer {d} := by
    have h := hXk _ (clabelS_cv0_mem_triKer 0)
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((congrArg (_ * ·) hd.symm).trans (h.trans (congrArg (· * _) hd)))
  have hexκ : ∃ κ : vStab cv0, κ = ψ ⟨_, hXd⟩ := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ := hexκ
  have hΨκ : psiTot ψ (κ : Shat) = (psiTot ψ (clabelS x) * φe ⟨clabelS x', hsE⟩) ^ 3 := by
    subst hκ
    exact psiTot_psi ψ ⟨_, hXd⟩
  have hκc : ∀ k ∈ triKer 0, (κ : Shat) * k = k * κ := by
    intro k hk
    refine psiTot_inj ψ (mul_mem κ.2 hk.1.1) (mul_mem hk.1.1 κ.2) ?_
    rw [psiTot_mul ψ κ.2 hk.1.1, psiTot_mul ψ hk.1.1 κ.2, hΨκ]
    exact hXk k hk
  have hκK : (κ : Shat) ∈ triKer 0 :=
    ⟨⟨κ.2, (commute_clabelS_iff cw0 _).1 (hκc _ (clabelS_cw0_mem_triKer 0))⟩,
      (commute_clabelS_iff (cu 0) _).1 (hκc _ (clabelS_cu_mem_triKer 0))⟩
  have hκZ : (κ : Shat) ∈ (Subgroup.center (triKer 0)).map (triKer 0).subtype :=
    ⟨⟨κ, hκK⟩, Subgroup.mem_center_iff.2 fun k => Subtype.ext (hκc k k.2).symm, rfl⟩
  have hκinv : (κ : Shat)⁻¹ = κ := by
    have hlab := mem_triLab_iff.1 (center_triKer_zero ▸ hκZ)
    obtain ⟨i, j, k, hijk⟩ := hlab
    refine inv_eq_of_mul_eq_one_right ?_
    rw [hijk]
    exact triElt_mul_self 0 i j k
  have hκa : (clabelS x)⁻¹ * κ * clabelS x = κ := by
    have h : psiTot ψ (clabelS x * κ * (clabelS x)⁻¹) = psiTot ψ (κ : Shat)⁻¹ :=
      (hQa _ hκK).2.symm.trans
        ((congrArg (fun z => psiTot ψ (clabelS x) * z * (psiTot ψ (clabelS x))⁻¹) hΨκ).trans
          (hinv.1.trans ((congrArg (·⁻¹) hΨκ).symm.trans (psiTot_inv ψ κ.2).symm)))
    have h' := psiTot_inj ψ (hQa _ hκK).1.1.1 (inv_mem κ.2) h
    rw [clabelS_inv] at h' ⊢
    rw [h', hκinv]
  have hκs : (clabelS x')⁻¹ * κ * clabelS x' = κ := by
    have h : psiTot ψ (clabelS x' * κ * (clabelS x')⁻¹) = psiTot ψ (κ : Shat)⁻¹ :=
      (hQs _ hκK).2.symm.trans
        ((congrArg (fun z => φe ⟨clabelS x', hsE⟩ * z * (φe ⟨clabelS x', hsE⟩)⁻¹) hΨκ).trans
          (hinv.2.1.trans ((congrArg (·⁻¹) hΨκ).symm.trans (psiTot_inv ψ κ.2).symm)))
    have h' := psiTot_inj ψ (hQs _ hκK).1.1.1 (inv_mem κ.2) h
    rw [clabelS_inv] at h' ⊢
    rw [h', hκinv]
  have hX : (psiTot ψ (clabelS x) * φe ⟨clabelS x', hsE⟩) ^ 3 = 1 := by
    have hfix := fixed_center_triKer_zero ha hb hκZ hκa hκs
    rcases hfix with h1 | hκg
    · exact hΨκ.symm.trans ((congrArg (psiTot ψ) h1).trans (psiTot_one ψ))
    · exfalso
      have hD : IsConj d
          (psiTot ψ (clabelS x) * (psiTot ψ (clabelS x) * φe ⟨clabelS x', hsE⟩) ^ 3) :=
        hsD.trans (isConj_iff.2 ⟨_, hinv.2.2.symm⟩)
      have e1 : ((ψ.symm ⟨clabelS x, haH⟩ : Subgroup.centralizer {d}) : G) =
          psiTot ψ (clabelS x) := (psiTot_of_mem ψ haH).symm
      have e2 : ((ψ.symm κ : Subgroup.centralizer {d}) : G) =
          (psiTot ψ (clabelS x) * φe ⟨clabelS x', hsE⟩) ^ 3 :=
        (psiTot_of_mem ψ κ.2).symm.trans hΨκ
      have e : ((ψ.symm (⟨clabelS x, haH⟩ * κ) : Subgroup.centralizer {d}) : G) =
          psiTot ψ (clabelS x) * (psiTot ψ (clabelS x) * φe ⟨clabelS x', hsE⟩) ^ 3 :=
        (congrArg Subtype.val (map_mul ψ.symm ⟨clabelS x, haH⟩ κ)).trans
          (congrArg₂ (· * ·) e1 e2)
      have hmemD : (⟨clabelS x, haH⟩ * κ : vStab cv0) ∈ dH ψ := (congrArg (IsConj d) e).mpr hD
      have hκeq : κ = cV0 * lamW0H * lamUH 0 := Subtype.ext hκg
      rw [hκeq] at hmemD
      exact (Set.eq_empty_iff_forall_notMem.1 (RB_inter_dH_eq_empty ψ hψ)) _
        ⟨mem_RB_mul_fourth hx ha, hmemD⟩
  have hexf₁ : ∃ f : ↥(cvSetStab {cv0, cw0, cu 0} ⊓ vStab cv0) →* G,
      ∀ k (hk : k ∈ cvSetStab {cv0, cw0, cu 0} ⊓ vStab cv0), f ⟨k, hk⟩ = psiInvHom ψ ⟨k, hk.2⟩ :=
    ⟨(psiInvHom ψ).comp (Subgroup.inclusion inf_le_right), fun _ _ => rfl⟩
  obtain ⟨f₁, hf₁⟩ := hexf₁
  have hexf₂ : ∃ f : ↥(cvSetStab {cv0, cw0, cu 0} ⊓ cvSetStab {cv0, cw0}) →* G,
      ∀ k (hk : k ∈ cvSetStab {cv0, cw0, cu 0} ⊓ cvSetStab {cv0, cw0}),
        f ⟨k, hk⟩ = φe ⟨k, hk.2⟩ :=
    ⟨φe.comp (Subgroup.inclusion inf_le_right), fun _ _ => rfl⟩
  obtain ⟨f₂, hf₂⟩ := hexf₂
  have hf : ∀ k (h₁ : k ∈ cvSetStab {cv0, cw0, cu 0} ⊓ vStab cv0)
      (h₂ : k ∈ cvSetStab {cv0, cw0, cu 0} ⊓ cvSetStab {cv0, cw0}),
      f₁ ⟨k, h₁⟩ = f₂ ⟨k, h₂⟩ := fun k h₁ h₂ =>
    (hf₁ k h₁).trans ((hve k h₁.2 h₂.2).trans (hf₂ k h₂).symm)
  have hrel : ∀ (h₁ : clabelS x ∈ cvSetStab {cv0, cw0, cu 0} ⊓ vStab cv0)
      (h₂ : clabelS x' ∈ cvSetStab {cv0, cw0, cu 0} ⊓ cvSetStab {cv0, cw0})
      (h₃ : (clabelS x * clabelS x') ^ 3 ∈ cvSetStab {cv0, cw0, cu 0} ⊓ vStab cv0),
      (f₁ ⟨clabelS x, h₁⟩ * f₂ ⟨clabelS x', h₂⟩) ^ 3 =
        f₁ ⟨(clabelS x * clabelS x') ^ 3, h₃⟩ := by
    intro h₁ h₂ h₃
    have e₁ : f₁ ⟨clabelS x, h₁⟩ = psiTot ψ (clabelS x) :=
      (hf₁ _ h₁).trans (psiTot_of_mem ψ h₁.2).symm
    have e₃ : f₁ ⟨(clabelS x * clabelS x') ^ 3, h₃⟩ = 1 :=
      (hf₁ _ h₃).trans ((psiTot_of_mem ψ h₃.2).symm.trans
        ((congrArg (psiTot ψ) hcube).trans (psiTot_one ψ)))
    exact (congrArg (· ^ 3) (congrArg₂ (· * ·) e₁ (hf₂ _ h₂))).trans (hX.trans e₃.symm)
  have hT0 := exists_unique_extend_cvTriangle (isCTriangle_cu 0) f₁ f₂ hf ha hb hrel
  obtain ⟨f, ⟨hf1, hf2⟩, -⟩ := hT0
  exact ⟨f, fun a ha hb => ((hf1 a hb ⟨hb, ha⟩).trans (hf₁ a ⟨hb, ha⟩)).symm,
    fun a ha hb => ((hf2 a hb ⟨hb, ha⟩).trans (hf₂ a ⟨hb, ha⟩)).symm⟩

end GSide

end CFSG.Monster.B.GSide

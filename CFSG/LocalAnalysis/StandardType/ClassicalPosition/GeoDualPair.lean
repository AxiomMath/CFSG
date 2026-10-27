module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj

public section

namespace CFSG.StandardType.ClassicalPosition.Geo

private lemma gDP_inv_mem_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    {S : Set (GL ι F)} (s : GL ι F) (hs : s ∈ S) :
    ((s⁻¹ : GL ι F) : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) := by
  have hsA : (s : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  have hfin : 0 < orderOf s := orderOf_pos s
  have hpow : s ^ (orderOf s - 1) = s⁻¹ := by
    have h1 : s ^ (orderOf s - 1) * s = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hfin, pow_orderOf_eq_one]
    exact eq_inv_of_mul_eq_one_left h1
  rw [← hpow, Units.val_pow_eq_pow_val]
  exact Subalgebra.pow_mem _ hsA _

private lemma gDP_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      Commute a b := by
  intro a ha b hb
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F (Units.val '' S) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rcases hy with ⟨s', hs', rfl⟩
    have h := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) (hS s' hs' s hs).eq
    simpa [Units.val_mul] using h
  have hA : Algebra.adjoin F (Units.val '' S) ≤ Subalgebra.centralizer F (Units.val '' S) :=
    Algebra.adjoin_le hgen
  have ha' : a ∈ Subalgebra.centralizer F (Units.val '' S) := hA ha
  have hgen2 : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h := (Subalgebra.mem_centralizer_iff F).mp ha' (s : Matrix ι ι F) ⟨s, hs, rfl⟩
    exact h.symm
  have hA2 : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := Algebra.adjoin_le hgen2
  have hb' : b ∈ Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := hA2 hb
  exact (Subalgebra.mem_centralizer_iff F).mp hb' a (Set.mem_singleton a)

private lemma gDP_block_scalar {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F}
    (he : IsPrimIdemIn A e) (hdeg : blockDegree A e = 1) {a : Matrix ι ι F} (ha : a ∈ A) :
    ∃ c : F, a * e = c • e := by
  let M : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have hMdeg : Module.finrank F M = 1 := hdeg
  have heM : e ∈ M := ⟨e, he.1, by rw [LinearMap.mulRight_apply, he.2.1.eq]⟩
  have hene : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  have haM : a * e ∈ M := ⟨a, ha, by rw [LinearMap.mulRight_apply]⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, heM⟩ : M) hene).mp hMdeg
    (⟨a * e, haM⟩ : M)
  exact ⟨c, by simpa using congrArg Subtype.val hc.symm⟩

private lemma gDP_formAdj_idem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) {e : Matrix ι ι F}
    (he : IsIdempotentElem e) : IsIdempotentElem (formAdj σ G e) := by
  rw [isIdempotentElem_iff] at he ⊢
  rw [← formAdj_mul σ hG, he]

private lemma gDP_formAdj_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (G : Matrix ι ι F) : formAdj σ G 0 = 0 := by
  unfold formAdj
  rw [Matrix.map_zero σ (map_zero σ), Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]

private lemma gDP_mul_formAdj_eq_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map σ) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (hpair : formAdj σ G e ≠ e) :
    e * formAdj σ G e = 0 ∧ formAdj σ G e * e = 0 := by
  let A := Algebra.adjoin F (Units.val '' S)
  have heA : e ∈ A := he.1
  have hesA : formAdj σ G e ∈ A := formAdj_mem_adjoin σ hG hSU he.1
  have hcomm : Commute e (formAdj σ G e) :=
    gDP_adjoin_comm hS e heA (formAdj σ G e) hesA
  have heidem : IsIdempotentElem e := he.2.1
  have hesidem : IsIdempotentElem (formAdj σ G e) := gDP_formAdj_idem σ hG heidem
  have hxidem : IsIdempotentElem (e * formAdj σ G e) :=
    IsIdempotentElem.mul_of_commute hcomm heidem hesidem
  have hxmem : e * formAdj σ G e ∈ A := Subalgebra.mul_mem A heA hesA
  have hxe : (e * formAdj σ G e) * e = e * formAdj σ G e := by
    rw [Matrix.mul_assoc, hcomm.eq.symm, ← Matrix.mul_assoc, heidem.eq]
  rcases he.2.2.2 (e * formAdj σ G e) hxmem hxidem hxe with hzero | heq
  · refine ⟨hzero, ?_⟩
    rw [← hcomm.eq, hzero]
  · exfalso
    apply hpair
    calc formAdj σ G e = formAdj σ G (e * formAdj σ G e) := by rw [heq]
      _ = formAdj σ G (formAdj σ G e) * formAdj σ G e :=
            formAdj_mul σ hG e (formAdj σ G e)
      _ = e * formAdj σ G e := by rw [formAdj_formAdj σ hσ hG hGh e]
      _ = e := heq

theorem exists_eigen_of_dualPair {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map σ) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e = 1) {s : GL ι F} (hs : s ∈ S) :
    ∃ c : F, c ≠ 0 ∧ (s : Matrix ι ι F) * e = c • e ∧
      (s : Matrix ι ι F) * formAdj σ G e = (σ c)⁻¹ • formAdj σ G e := by
  let A := Algebra.adjoin F (Units.val '' S)
  have hsA : (s : Matrix ι ι F) ∈ A := Algebra.subset_adjoin ⟨s, hs, rfl⟩
  obtain ⟨c, hce⟩ := gDP_block_scalar he hdeg hsA
  have hsinv : ((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcne : c ≠ 0 := by
    intro hc0
    have he0 : e = 0 := by
      calc e = 1 * e := (Matrix.one_mul e).symm
        _ = (((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F)) * e := by rw [hsinv]
        _ = ((s⁻¹ : GL ι F) : Matrix ι ι F) * ((s : Matrix ι ι F) * e) := by
              rw [Matrix.mul_assoc]
        _ = ((s⁻¹ : GL ι F) : Matrix ι ι F) * (c • e) := by rw [hce]
        _ = c • (((s⁻¹ : GL ι F) : Matrix ι ι F) * e) := by rw [Matrix.mul_smul]
        _ = 0 := by rw [hc0, zero_smul F]
    exact he.2.2.1 he0
  have hsinvA : ((s⁻¹ : GL ι F) : Matrix ι ι F) ∈ A := gDP_inv_mem_adjoin s hs
  have hte : ((s⁻¹ : GL ι F) : Matrix ι ι F) * e = c⁻¹ • e := by
    have h1 : e = c • (((s⁻¹ : GL ι F) : Matrix ι ι F) * e) := by
      calc e = ((s⁻¹ : GL ι F) : Matrix ι ι F) * ((s : Matrix ι ι F) * e) := by
              rw [← Matrix.mul_assoc, hsinv, Matrix.one_mul]
        _ = ((s⁻¹ : GL ι F) : Matrix ι ι F) * (c • e) := by rw [hce]
        _ = c • (((s⁻¹ : GL ι F) : Matrix ι ι F) * e) := by rw [Matrix.mul_smul]
    calc ((s⁻¹ : GL ι F) : Matrix ι ι F) * e
        = c⁻¹ • (c • (((s⁻¹ : GL ι F) : Matrix ι ι F) * e)) := by
            rw [inv_smul_smul₀ hcne]
      _ = c⁻¹ • e := by rw [← h1]
  have ht_adj : formAdj σ G ((s⁻¹ : GL ι F) : Matrix ι ι F) = (s : Matrix ι ι F) := by
    rw [← formAdj_eq_inv_of_isometry σ hG s (hSU s hs), formAdj_formAdj σ hσ hG hGh]
  refine ⟨c, hcne, hce, ?_⟩
  have heq : e * ((s⁻¹ : GL ι F) : Matrix ι ι F) = c⁻¹ • e := by
    rw [(gDP_adjoin_comm hS e he.1 ((s⁻¹ : GL ι F) : Matrix ι ι F) hsinvA).eq, hte]
  have happ := congrArg (formAdj σ G) heq
  rw [formAdj_mul σ hG, formAdj_smul, map_inv₀, ht_adj] at happ
  exact happ

theorem exists_eigen_mul_ne_one_of_dualPair {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map σ) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e = 1)
    (hpair : formAdj σ G e ≠ e) :
    ∃ s ∈ S, ∃ c : F, (s : Matrix ι ι F) * e = c • e ∧ σ c * c ≠ 1 := by
  by_contra hcon
  push Not at hcon
  let A := Algebra.adjoin F (Units.val '' S)
  have hclaim : ∀ a ∈ A, ∃ χ : F,
      a * e = χ • e ∧ a * formAdj σ G e = χ • formAdj σ G e := by
    intro a ha
    refine Algebra.adjoin_induction
      (p := fun x _ => ∃ χ : F, x * e = χ • e ∧ x * formAdj σ G e = χ • formAdj σ G e)
      ?_ ?_ ?_ ?_ ha
    · rintro x ⟨s, hs, rfl⟩
      obtain ⟨c, _, hce, hce'⟩ := exists_eigen_of_dualPair σ hσ hG hGh hSU hS he hdeg hs
      have hcc : (σ c)⁻¹ = c := by
        exact (eq_inv_of_mul_eq_one_right (hcon s hs c hce)).symm
      exact ⟨c, hce, by rw [hce', hcc]⟩
    · intro r
      exact ⟨r, by rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul],
        by rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]⟩
    · rintro x y hx hy ⟨χx, hxe, hxe'⟩ ⟨χy, hye, hye'⟩
      exact ⟨χx + χy, by rw [Matrix.add_mul, hxe, hye, add_smul],
        by rw [Matrix.add_mul, hxe', hye', add_smul]⟩
    · rintro x y hx hy ⟨χx, hxe, hxe'⟩ ⟨χy, hye, hye'⟩
      exact ⟨χy * χx, by rw [Matrix.mul_assoc, hye, Matrix.mul_smul, hxe, smul_smul],
        by rw [Matrix.mul_assoc, hye', Matrix.mul_smul, hxe', smul_smul]⟩
  obtain ⟨χ, hχe, hχe'⟩ := hclaim (formAdj σ G e) (formAdj_mem_adjoin σ hG hSU he.1)
  have horth := (gDP_mul_formAdj_eq_zero σ hσ hG hGh hSU hS he hpair).2
  have hχ0 : χ = 0 := by
    rw [horth] at hχe
    exact (smul_eq_zero.mp hχe.symm).resolve_right he.2.2.1
  have hstar0 : formAdj σ G e = 0 := by
    have hidem : formAdj σ G e * formAdj σ G e = formAdj σ G e :=
      (gDP_formAdj_idem σ hG he.2.1).eq
    rw [hχ0, zero_smul F, hidem] at hχe'
    exact hχe'
  have he0 : e = 0 := by
    calc e = formAdj σ G (formAdj σ G e) := (formAdj_formAdj σ hσ hG hGh e).symm
      _ = formAdj σ G 0 := by rw [hstar0]
      _ = 0 := gDP_formAdj_zero σ G
  exact he.2.2.1 he0

theorem mul_formAdj_eq_zero_of_dualPair {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map σ) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (hpair : formAdj σ G e ≠ e) :
    e * formAdj σ G e = 0 ∧ formAdj σ G e * e = 0 :=
  gDP_mul_formAdj_eq_zero σ hσ hG hGh hSU hS he hpair

end CFSG.StandardType.ClassicalPosition.Geo

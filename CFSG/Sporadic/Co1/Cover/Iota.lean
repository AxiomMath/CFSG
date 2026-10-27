module

public import CFSG.Monster.Schur.M24
public import CFSG.Sporadic.Co1.Cover.WordEval
public import CFSG.Sporadic.Co1.Cover.Splitting
public import CFSG.Sporadic.Co1.Cover.Eps
public import CFSG.Sporadic.Co1.Cover.RelChecks

public section

namespace CFSG.Sporadic.Co1.Cover

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.CoverNative
  CFSG.Sporadic.Co1.Module CFSG.Monster.Schur CFSG.Monster.Schur.M24 CFSG.Blueprint Matrix
  SemidirectProduct

abbrev PM24 : Type := TauCeti.SporadicName.M24.Group

attribute [local irreducible] eps0 ga gb regCov rrCov epsRows

@[expose] noncomputable def genCo1 :
    Fin pres.generatorCount → NativeSporadic.Co1 :=
  fun j => if j.val = 0 then ga else gb

theorem relCheck24 :
    mulRows 24 (rrCov 4) (InvNative.invRows (rrCov 4)) = idRows 24 ∧
    mulRows 24 (rrCov 5) (InvNative.invRows (rrCov 5)) = idRows 24 ∧
    ∀ w ∈ pres.relatorLetters, wordRowsAB 24 (rrCov 4) (rrCov 5) (InvNative.invRows (rrCov 4))
      (InvNative.invRows (rrCov 5)) w = idRows 24 := by
  have h := rel24_ok
  simp only [relCheckAB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem matHom_ga_inv :
    matHom ga⁻¹ = rowsMatrix 24 (InvNative.invRows (rrCov 4)) := by
  apply matHom_inv_eq
  rw [matHom_ga, ← rowsMatrix_mulRows, (relCheck24).1, rowsMatrix_idRows]

theorem matHom_gb_inv :
    matHom gb⁻¹ = rowsMatrix 24 (InvNative.invRows (rrCov 5)) := by
  apply matHom_inv_eq
  rw [matHom_gb, ← rowsMatrix_mulRows, (relCheck24).2.1, rowsMatrix_idRows]

theorem map_letters {M : Type*} [Group M] (g₀ g₁ : M) (f : Fin pres.generatorCount → M)
    (hf : ∀ j, f j = if j.val = 0 then g₀ else g₁)
    (w : List (Fin pres.generatorCount × Bool)) :
    (w.map fun x => cond x.2 (f x.1) (f x.1)⁻¹) =
      (w.map fun l => ((l.1.val, l.2) : ℕ × Bool)).map (letterElt g₀ g₁) := by
  rw [List.map_map]
  refine List.map_congr_left fun x _ => ?_
  obtain ⟨j, s⟩ := x
  by_cases h : j.val = 0 <;> cases s <;> simp [letterElt, hf, h]

theorem mem_relatorLetters {w : List (Fin pres.generatorCount × Bool)} (hw : w ∈ pres.relators) :
    (w.map fun l => ((l.1.val, l.2) : ℕ × Bool)) ∈ pres.relatorLetters := by
  rw [TauCeti.GroupPresentation.relatorLetters_def]
  exact List.mem_map_of_mem hw

theorem exists_word_of_mem_relatorSet {r : FreeGroup (Fin pres.generatorCount)}
    (hr : r ∈ pres.relatorSet) : ∃ w ∈ pres.relators, FreeGroup.mk w = r := by
  have hr' : r ∈ pres.relators.map FreeGroup.mk := by
    rw [CFSG.Sporadic.Presentation.relatorSet_eq] at hr
    exact hr
  exact List.mem_map.1 hr'

theorem relator_ι
    (w : List (Fin pres.generatorCount × Bool)) (hw : w ∈ pres.relators) :
    FreeGroup.lift genCo1 (FreeGroup.mk w) = 1 := by
  apply matHom_injective
  have hf : ∀ j, genCo1 j = if j.val = 0 then ga else gb := fun j => rfl
  have h1 := word_matrix matHom ga gb (rrCov 4) (rrCov 5) _ _ matHom_ga matHom_gb matHom_ga_inv
    matHom_gb_inv (w.map fun l => ((l.1.val, l.2) : ℕ × Bool))
  rw [(relCheck24).2.2 _ (mem_relatorLetters hw), rowsMatrix_idRows] at h1
  rw [FreeGroup.lift_mk, map_letters ga gb genCo1 hf, h1, map_one]

@[expose] noncomputable def iota :
    PM24 →* NativeSporadic.Co1 :=
  PresentedGroup.toGroup (f := genCo1) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := exists_word_of_mem_relatorSet hr
    exact relator_ι w hw

theorem iota_gen0 :
    iota (gen 0) = ga := by
  show PresentedGroup.toGroup _ (PresentedGroup.of (idx 0)) = ga
  rw [PresentedGroup.toGroup.of]
  simp [genCo1, idx]

theorem iota_gen1 :
    iota (gen 1) = gb := by
  show PresentedGroup.toGroup _ (PresentedGroup.of (idx 1)) = gb
  rw [PresentedGroup.toGroup.of]
  simp [genCo1, idx]

theorem relCheck11 :
    mulRows 11 Aa Aa = idRows 11 ∧ mulRows 11 Ba (mulRows 11 Ba Ba) = idRows 11 ∧
    ∀ w ∈ pres.relatorLetters, wordRowsAB 11 Aa Ba Aa (mulRows 11 Ba Ba) w = idRows 11 := by
  have h := rel11_ok
  simp only [relCheckAB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem Amat_mul_self : Amat * Amat = 1 := by
  have h := congrArg (rowsMatrix 11) (relCheck11).1
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h

theorem Bmat_pow_three : Bmat * (Bmat * Bmat) = 1 := by
  have h := congrArg (rowsMatrix 11) (relCheck11).2.1
  rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_idRows] at h

@[expose] def gA :
    GL (Fin 11) (ZMod 2) := ⟨Amat, Amat, Amat_mul_self, Amat_mul_self⟩

@[expose] def gB : GL (Fin 11) (ZMod 2) :=
  ⟨Bmat, Bmat * Bmat, Bmat_pow_three, by rw [Matrix.mul_assoc, Bmat_pow_three]⟩

@[expose] def genGL :
    Fin pres.generatorCount → GL (Fin 11) (ZMod 2) :=
  fun j => if j.val = 0 then gA else gB

theorem relator_ρ
    (w : List (Fin pres.generatorCount × Bool)) (hw : w ∈ pres.relators) :
    FreeGroup.lift genGL (FreeGroup.mk w) = 1 := by
  apply Units.ext
  have hf : ∀ j, genGL j = if j.val = 0 then gA else gB := fun j => rfl
  have hBi : Units.coeHom (Matrix (Fin 11) (Fin 11) (ZMod 2)) gB⁻¹ =
      rowsMatrix 11 (mulRows 11 Ba Ba) := by
    rw [rowsMatrix_mulRows]
    rfl
  have h1 := word_matrix (Units.coeHom (Matrix (Fin 11) (Fin 11) (ZMod 2))) gA gB Aa Ba Aa
    (mulRows 11 Ba Ba) rfl rfl rfl hBi (w.map fun l => ((l.1.val, l.2) : ℕ × Bool))
  rw [(relCheck11).2.2 _ (mem_relatorLetters hw), rowsMatrix_idRows] at h1
  rw [FreeGroup.lift_mk, map_letters gA gB genGL hf]
  exact h1

@[expose] noncomputable def rhoGL : PM24 →* GL (Fin 11) (ZMod 2) :=
  PresentedGroup.toGroup (f := genGL) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := exists_word_of_mem_relatorSet hr
    exact relator_ρ w hw

@[expose] noncomputable def rho :
    PM24 →* ((Fin 11 → ZMod 2) ≃ₗ[ZMod 2] (Fin 11 → ZMod 2)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 11 → ZMod 2)).toMonoidHom).comp
    ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp rhoGL)

theorem rho_gen0
    (v : Fin 11 → ZMod 2) : rho (gen 0) v = Amat *ᵥ v := by
  have h : rhoGL (gen 0) = gA := by
    show PresentedGroup.toGroup _ (PresentedGroup.of (idx 0)) = gA
    rw [PresentedGroup.toGroup.of]
    simp [genGL, idx]
  show (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 11 → ZMod 2)
    (Matrix.GeneralLinearGroup.toLin (rhoGL (gen 0)))) v = _
  rw [h]
  rfl

theorem rho_gen1
    (v : Fin 11 → ZMod 2) : rho (gen 1) v = Bmat *ᵥ v := by
  have h : rhoGL (gen 1) = gB := by
    show PresentedGroup.toGroup _ (PresentedGroup.of (idx 1)) = gB
    rw [PresentedGroup.toGroup.of]
    simp [genGL, idx]
  show (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 11 → ZMod 2)
    (Matrix.GeneralLinearGroup.toLin (rhoGL (gen 1)))) v = _
  rw [h]
  rfl

theorem conj_ga
    (x : Multiplicative (Fin 11 → ZMod 2)) :
    ga * epsHom x * ga⁻¹ = epsHom (Multiplicative.ofAdd (Amat *ᵥ Multiplicative.toAdd x)) :=
  conj_of_basis Amat (fun i => basis_conj matHom_ga cov_norm_a i) x

theorem conj_gb
    (x : Multiplicative (Fin 11 → ZMod 2)) :
    gb * epsHom x * gb⁻¹ = epsHom (Multiplicative.ofAdd (Bmat *ᵥ Multiplicative.toAdd x)) :=
  conj_of_basis Bmat (fun i => basis_conj matHom_gb cov_norm_b i) x

theorem iota_conj
    (p : PM24) (x : Multiplicative (Fin 11 → ZMod 2)) :
    iota p * epsHom x * (iota p)⁻¹ =
      epsHom (Multiplicative.ofAdd (rho p (Multiplicative.toAdd x))) := by
  have hmem : p ∈ Subgroup.closure (Set.range gen) := by rw [closure_gen]; trivial
  refine Subgroup.closure_induction
    (p := fun p _ => ∀ x, iota p * epsHom x * (iota p)⁻¹ =
      epsHom (Multiplicative.ofAdd (rho p (Multiplicative.toAdd x)))) ?_ ?_ ?_ ?_ hmem x
  · rintro _ ⟨i, rfl⟩ x
    fin_cases i
    · rw [show gen ⟨0, by norm_num⟩ = gen 0 from rfl, iota_gen0, conj_ga x, rho_gen0]
    · rw [show gen ⟨1, by norm_num⟩ = gen 1 from rfl, iota_gen1, conj_gb x, rho_gen1]
  · intro x
    simp
  · intro p q _ _ hp hq x
    rw [map_mul, map_mul, _root_.mul_inv_rev]
    calc iota p * iota q * epsHom x * ((iota q)⁻¹ * (iota p)⁻¹)
        = iota p * (iota q * epsHom x * (iota q)⁻¹) * (iota p)⁻¹ := by group
      _ = _ := by
        rw [hq x, hp]
        simp only [toAdd_ofAdd]
        rfl
  · intro p _ hp x
    have h := hp (Multiplicative.ofAdd (rho p⁻¹ (Multiplicative.toAdd x)))
    have h2 : rho p (rho p⁻¹ (Multiplicative.toAdd x)) = Multiplicative.toAdd x := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    simp only [toAdd_ofAdd, h2, ofAdd_toAdd] at h
    rw [map_inv, ← h]
    group

abbrev SM24 :
    Type := Multiplicative (Fin 11 → ZMod 2) ⋊[phiOf rho] PM24

@[expose] noncomputable def theta :
    SM24 →* NativeSporadic.Co1 :=
  SemidirectProduct.lift epsHom iota fun p => by
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, phiOf_apply]
    exact (iota_conj p x).symm

theorem theta_inl
    (x : Multiplicative (Fin 11 → ZMod 2)) : theta (inl x) = epsHom x :=
  lift_inl _ _ _ x

theorem theta_inr
    (p : PM24) : theta (inr p) = iota p := lift_inr _ _ _ p

theorem theta_apply
    (s : SM24) : theta s = epsHom s.left * iota s.right := rfl

theorem isSimpleGroup_PM24 :
    IsSimpleGroup PM24 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have : IsSimpleGroup NativeSporadic.M24 := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  exact e.symm.isSimpleGroup

theorem natCard_PM24 :
    Nat.card PM24 = 244823040 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  rw [← Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M24

theorem ga_gb_not_comm :
    ga * gb ≠ gb * ga := by
  intro h
  apply noncomm_ok
  have h2 := congrArg matHom h
  rw [map_mul, map_mul, matHom_ga, matHom_gb, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows] at h2
  exact h2

theorem iota_mem_eps
    (p : PM24) (hp : iota p ∈ epsHom.range) : p = 1 := by
  let N₀ : Subgroup PM24 := Subgroup.comap iota epsHom.range
  have : N₀.Normal := ⟨fun p hp g => by
    obtain ⟨x, hx⟩ := (show iota p ∈ epsHom.range from hp)
    refine ⟨Multiplicative.ofAdd (rho g (Multiplicative.toAdd x)), ?_⟩
    show epsHom (Multiplicative.ofAdd (rho g (Multiplicative.toAdd x))) = iota (g * p * g⁻¹)
    rw [← iota_conj, map_mul, map_mul, map_inv, ← hx]⟩
  have := isSimpleGroup_PM24
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₀ with h | h
  · have hp' : p ∈ N₀ := hp
    rw [h] at hp'
    exact hp'
  · exfalso
    have h0 : iota (gen 0) ∈ epsHom.range := by
      have : gen 0 ∈ N₀ := by rw [h]; trivial
      exact this
    have h1 : iota (gen 1) ∈ epsHom.range := by
      have : gen 1 ∈ N₀ := by rw [h]; trivial
      exact this
    rw [iota_gen0] at h0
    rw [iota_gen1] at h1
    obtain ⟨x, hx⟩ := h0
    obtain ⟨y, hy⟩ := h1
    apply ga_gb_not_comm
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem theta_injective :
    Function.Injective theta := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker, theta_apply] at hs
  have hr : iota s.right ∈ epsHom.range := by
    exact ⟨(s.left)⁻¹, (map_inv epsHom s.left).trans (inv_eq_of_mul_eq_one_right hs)⟩
  have hr1 : s.right = 1 := iota_mem_eps _ hr
  rw [hr1, map_one, mul_one] at hs
  have hl1 : s.left = 1 := epsHom_injective (hs.trans (map_one epsHom).symm)
  exact Subgroup.mem_bot.2 (SemidirectProduct.ext hl1 hr1)

theorem natCard_SM24 :
    Nat.card SM24 = 2 ^ 11 * 244823040 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, natCard_PM24]
  congr 1
  rw [Nat.card_congr (Multiplicative.ofAdd :
    (Fin 11 → ZMod 2) ≃ Multiplicative (Fin 11 → ZMod 2)).symm]
  simp [Nat.card_eq_fintype_card]

theorem theta_index :
    theta.range.index = 8292375 := by
  have h1 := Subgroup.card_mul_index theta.range
  rw [Nat.card_congr (MonoidHom.ofInjective theta_injective).toEquiv.symm, natCard_SM24,
    CFSG.Sporadic.Co1.card_Co1] at h1
  omega

end CFSG.Sporadic.Co1.Cover

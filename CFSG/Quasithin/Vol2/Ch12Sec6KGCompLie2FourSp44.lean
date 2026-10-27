module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2TwoL52
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigSp4
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalSymplecticAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourRoots
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.Open.GLBDefs
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2Two
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.He4 (NoInvCommNine NoInvCommNine.of_mulEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open Matrix

section Sp44

variable {F : Type} [Field F]

@[expose] def spDiagVec (p : Fˣ × Fˣ) : Fin 2 ⊕ Fin 2 → F :=
  Sum.elim ![(p.1 : F), (p.2 : F)] ![((p.1⁻¹ : Fˣ) : F), ((p.2⁻¹ : Fˣ) : F)]

theorem spDiagVec_mul (p q : Fˣ × Fˣ) : spDiagVec (p * q) = spDiagVec p * spDiagVec q := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [spDiagVec, mul_comm]

theorem spDiagVec_one : spDiagVec (1 : Fˣ × Fˣ) = 1 := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [spDiagVec]

@[expose] noncomputable def spDiagGL : Fˣ × Fˣ →* GL (Fin 2 ⊕ Fin 2) F where
  toFun p := ⟨diagonal (spDiagVec p), diagonal (spDiagVec p⁻¹),
    by rw [diagonal_mul_diagonal, show (fun i => spDiagVec p i * spDiagVec p⁻¹ i) =
      spDiagVec (p * p⁻¹) from (spDiagVec_mul p p⁻¹).symm, mul_inv_cancel, spDiagVec_one]
       exact diagonal_one,
    by rw [diagonal_mul_diagonal, show (fun i => spDiagVec p⁻¹ i * spDiagVec p i) =
      spDiagVec (p⁻¹ * p) from (spDiagVec_mul p⁻¹ p).symm, inv_mul_cancel, spDiagVec_one]
       exact diagonal_one⟩
  map_one' := Units.ext (by simp [spDiagVec_one])
  map_mul' p q := Units.ext (by simp [spDiagVec_mul, diagonal_mul_diagonal])

theorem coe_spDiagGL (p : Fˣ × Fˣ) :
    ((spDiagGL p : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      diagonal (spDiagVec p) :=
  rfl

theorem spDiagGL_mem (p : Fˣ × Fˣ) : spDiagGL p ∈ StatedSp 2 F := by
  refine Subgroup.subset_closure ?_
  show (diagonal (spDiagVec p))ᵀ * fromBlocks 0 1 (-1) 0 * diagonal (spDiagVec p) =
    fromBlocks 0 1 (-1) 0
  rw [diagonal_transpose]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spDiagVec, fromBlocks]

@[expose] noncomputable def spDiagHom : Fˣ × Fˣ →* StatedSp 2 F :=
  spDiagGL.codRestrict _ spDiagGL_mem

theorem spDiagHom_injective : Function.Injective (spDiagHom (F := F)) := by
  intro p q h
  have h' := congrArg (fun x : StatedSp 2 F =>
    ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
  simp only [spDiagHom, MonoidHom.codRestrict_apply, coe_spDiagGL] at h'
  have h0 := congrFun (congrFun h' (.inl 0)) (.inl 0)
  have h1 := congrFun (congrFun h' (.inl 1)) (.inl 1)
  simp only [diagonal_apply_eq, spDiagVec, Sum.elim_inl, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

@[expose] noncomputable def spTorus : Subgroup (StatedSp 2 F) := (spDiagHom (F := F)).range

theorem eq_one_of_commute_spDiag [CharP F 2] {ω : Fˣ} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {t : GL (Fin 2 ⊕ Fin 2) F} (ht : t * t = 1)
    (h1 : t * spDiagGL (ω, 1) = spDiagGL (ω, 1) * t)
    (h2 : t * spDiagGL (1, ω) = spDiagGL (1, ω) * t) : t = 1 := by
  have a₁ : (ω : F) ≠ 1 := fun h => hω1 (Units.ext h)
  have a₂ : ((ω⁻¹ : Fˣ) : F) ≠ 1 := fun h => hω1 (inv_eq_one.mp (Units.ext h))
  have a₃ : (ω : F) ≠ ((ω⁻¹ : Fˣ) : F) := by
    intro h
    have h' : ω = ω⁻¹ := Units.ext h
    have h3 : ω * ω = 1 := mul_eq_one_iff_eq_inv.mpr h'
    apply hω1
    calc ω = ω ^ 3 * (ω * ω)⁻¹ := by group
      _ = 1 := by rw [hω3, h3]; group
  have m1 : (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * diagonal (spDiagVec (ω, 1)) =
      diagonal (spDiagVec (ω, 1)) * (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    have := congrArg Units.val h1
    rwa [Units.val_mul, Units.val_mul, coe_spDiagGL] at this
  have m2 : (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * diagonal (spDiagVec (1, ω)) =
      diagonal (spDiagVec (1, ω)) * (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    have := congrArg Units.val h2
    rwa [Units.val_mul, Units.val_mul, coe_spDiagGL] at this
  have e1 : ∀ i j, (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j * spDiagVec (ω, 1) j =
      spDiagVec (ω, 1) i * (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j := fun i j => by
    have := congrFun (congrFun m1 i) j
    rwa [mul_diagonal, diagonal_mul] at this
  have e2 : ∀ i j, (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j * spDiagVec (1, ω) j =
      spDiagVec (1, ω) i * (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j := fun i j => by
    have := congrFun (congrFun m2 i) j
    rwa [mul_diagonal, diagonal_mul] at this
  have hoff : ∀ i j, i ≠ j → (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j = 0 := by
    intro i j hij
    have key : spDiagVec (ω, 1) i ≠ spDiagVec (ω, 1) j ∨
        spDiagVec (1, ω) i ≠ spDiagVec (1, ω) j := by
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp only [spDiagVec, Sum.elim_inl, Sum.elim_inr, Units.val_one, inv_one, ne_eq,
          not_true_eq_false, or_false] <;>
        first
          | exact absurd rfl hij
          | exact a₁ | exact (Ne.symm a₁) | exact a₂ | exact (Ne.symm a₂)
          | exact a₃ | exact (Ne.symm a₃)
          | exact Or.inl a₁ | exact Or.inl (Ne.symm a₁) | exact Or.inr a₁
          | exact Or.inr (Ne.symm a₁) | exact Or.inl a₂ | exact Or.inl (Ne.symm a₂)
          | exact Or.inr a₂ | exact Or.inr (Ne.symm a₂) | exact Or.inl a₃
          | exact Or.inl (Ne.symm a₃) | exact Or.inr a₃ | exact Or.inr (Ne.symm a₃)
    rcases key with hk | hk
    · have h0 : (spDiagVec (ω, 1) j - spDiagVec (ω, 1) i) *
          (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j = 0 := by
        linear_combination e1 i j
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hk))
    · have h0 : (spDiagVec (1, ω) j - spDiagVec (1, ω) i) *
          (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j = 0 := by
        linear_combination e2 i j
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hk))
  have hdiag : (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      diagonal fun i => (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [hoff i j hij, diagonal_apply_ne _ hij]
  have hsq : ∀ i, (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i i = 1 := by
    intro i
    have hm : (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
      have := congrArg Units.val ht
      rwa [Units.val_mul, Units.val_one] at this
    rw [hdiag, diagonal_mul_diagonal] at hm
    have h := congrFun (congrFun hm i) i
    rw [diagonal_apply_eq, one_apply_eq] at h
    have h2 : ((t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i i - 1) *
        ((t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i i - 1) = 0 := by
      linear_combination h + (1 - (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i i) *
        (CharTwo.two_eq_zero : (2 : F) = 0)
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)
  refine Units.ext ?_
  rw [Units.val_one, hdiag]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, hsq, one_apply_eq]
  · rw [diagonal_apply_ne _ hij, one_apply_ne hij]

end Sp44

section Sp44Four

variable {F : Type} [Field F]

theorem card_spTorus (hF : Nat.card F = 4) : Nat.card (spTorus (F := F)) = 9 := by
  rw [spTorus, MonoidHom.range_eq_map, Subgroup.card_map_of_injective spDiagHom_injective,
    Subgroup.card_top, Nat.card_prod, LinearThreeFourOuter.card_units_eq_three hF]

theorem pow_three_of_mem_spTorus (hF : Nat.card F = 4) {x : StatedSp 2 F}
    (hx : x ∈ spTorus (F := F)) : x ^ 3 = 1 := by
  obtain ⟨p, rfl⟩ := hx
  rw [← map_pow, show p ^ 3 = 1 from Prod.ext (LinearThreeFourOuter.units_pow_three hF _)
    (LinearThreeFourOuter.units_pow_three hF _), map_one]

theorem isElemAbelian_spTorus (hF : Nat.card F = 4) : IsElemAbelian 3 (spTorus (F := F)) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => pow_three_of_mem_spTorus hF hx⟩
  obtain ⟨p, hp⟩ := a.2
  obtain ⟨q, hq⟩ := b.2
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, ← hq, ← map_mul, ← map_mul, mul_comm]

theorem card_statedSp_four (hF : Nat.card F = 4) : Nat.card (StatedSp 2 F) = 979200 := by
  have := LinearFieldFour.finite_of_card_eq_four hF
  rw [SymplecticFlag.card_statedSp, hF]
  decide

theorem factorization_card_statedSp_four (hF : Nat.card F = 4) :
    (Nat.card (StatedSp 2 F)).factorization 3 = 2 := by
  rw [card_statedSp_four hF, Nat.factorization_def _ Nat.prime_three,
    show (979200 : ℕ) = 3 ^ 2 * 108800 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem noInvCommNine_sp44 (hF : Nat.card F = 4) : NoInvCommNine (StatedSp 2 F) := by
  have := LinearFieldFour.finite_of_card_eq_four hF
  have := LinearFieldFour.charP_two_of_card_eq_four hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [LinearThreeFourOuter.card_units_eq_three hF]; norm_num)
  obtain ⟨ω, hω1⟩ := exists_ne (1 : Fˣ)
  have hω3 := LinearThreeFourOuter.units_pow_three hF ω
  intro P hP t ht hc
  let SP : Sylow 3 (StatedSp 2 F) :=
    Sylow.ofCard P (by rw [hP, factorization_card_statedSp_four hF]; norm_num)
  let ST : Sylow 3 (StatedSp 2 F) :=
    Sylow.ofCard spTorus (by rw [card_spTorus hF, factorization_card_statedSp_four hF]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 F) SP ST
  have hmap : P.map (MulAut.conj g).toMonoidHom = spTorus := by
    have h1 : ((g • SP : Sylow 3 (StatedSp 2 F)) : Subgroup (StatedSp 2 F)) =
        (ST : Subgroup (StatedSp 2 F)) := by rw [hg]
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
    exact h1
  have hmem : ∀ p : Fˣ × Fˣ, ∃ y ∈ P, g * y * g⁻¹ = spDiagHom p := by
    intro p
    have h1 : spDiagHom p ∈ P.map (MulAut.conj g).toMonoidHom := by
      rw [hmap]
      exact ⟨p, rfl⟩
    obtain ⟨y, hy, hyp⟩ := h1
    exact ⟨y, hy, hyp⟩
  have hcomm : ∀ p : Fˣ × Fˣ, g * t * g⁻¹ * spDiagHom p = spDiagHom p * (g * t * g⁻¹) := by
    intro p
    obtain ⟨y, hy, hyp⟩ := hmem p
    rw [← hyp]
    calc g * t * g⁻¹ * (g * y * g⁻¹) = g * (t * y) * g⁻¹ := by group
      _ = g * (y * t) * g⁻¹ := by rw [hc y hy]
      _ = g * y * g⁻¹ * (g * t * g⁻¹) := by group
  have ht' : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have h1 := eq_one_of_commute_spDiag hω1 hω3 (t := ((g * t * g⁻¹ : StatedSp 2 F) :
      GL (Fin 2 ⊕ Fin 2) F)) (by rw [← Subgroup.coe_mul, ht', Subgroup.coe_one])
    (by rw [show spDiagGL (ω, 1) = ((spDiagHom (ω, 1) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)
      from rfl, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm])
    (by rw [show spDiagGL (1, ω) = ((spDiagHom (1, ω) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)
      from rfl, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm])
  have h2 : g * t * g⁻¹ = 1 := Subtype.ext h1
  calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
    _ = 1 := by rw [h2]; group

variable [CharP F 2]

theorem exists_E9_psp44 (hF : Nat.card F = 4) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 F)), IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  refine ⟨(spTorus (F := F)).map (spProjEquiv (F := F)).toMonoidHom, ?_, ?_⟩
  · have hE := isElemAbelian_spTorus hF
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul]
      exact congrArg (fun w : ↥(spTorus (F := F)) => (spProjEquiv (F := F)).toMonoidHom w)
        (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective (f := (spProjEquiv (F := F)).toMonoidHom)
      (spProjEquiv (F := F)).injective, card_spTorus hF]

theorem center_psp44 (hF : Nat.card F = 4) :
    Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := by
  have := LinearFieldFour.finite_of_card_eq_four hF
  have hs : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 2
      ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩, F, inferInstance, inferInstance,
        by rw [hF]; norm_num, ⟨MulEquiv.refl _⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedProj (StatedSp 2 F)))
    with h | h
  · exact h
  · exfalso
    have hN := NoInvCommNine.of_mulEquiv (spProjEquiv (F := F)).symm (noInvCommNine_sp44 hF)
    obtain ⟨E, -, hE9⟩ := exists_E9_psp44 hF
    have : Finite (StatedProj (StatedSp 2 F)) :=
      Finite.of_equiv _ (spProjEquiv (F := F)).toEquiv
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : 2 ∣ Nat.card (StatedProj (StatedSp 2 F)) := by
      rw [← Nat.card_congr (spProjEquiv (F := F)).toEquiv, card_statedSp_four hF]
      norm_num
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht; norm_num at ht
    refine ht1 (hN E hE9 t (by rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ht]))
      fun p _ => ?_)
    have hpc : p ∈ Subgroup.center (StatedProj (StatedSp 2 F)) := h ▸ Subgroup.mem_top p
    exact (Subgroup.mem_center_iff.mp hpc t).symm

theorem false_of_autConf_sp44 (hF : Nat.card F = 4) {ν : MulAut (StatedProj (StatedSp 2 F))}
    {Lb Pb : Subgroup (MulAut (StatedProj (StatedSp 2 F)))}
    (h : AutConf (StatedProj (StatedSp 2 F)) ν Lb Pb) (hP : Nat.card Pb = 9) : False := by
  have := LinearFieldFour.finite_of_card_eq_four hF
  have := Fintype.ofFinite F
  obtain ⟨S, hS, hSν⟩ := h.sylow
  obtain ⟨x, hx⟩ := CFSG.QuasithinUnique.K1.sylowCentralizingAutInner_statedProj (K := F) S hS ν hSν
  have hν : ν ∈ (MulAut.conj : StatedProj (StatedSp 2 F) →* _).range :=
    ⟨x⁻¹, MulEquiv.ext fun y => by rw [hx, MulAut.conj_apply, inv_inv]⟩
  have hO := (CFSG.QuasithinUnique.Lin2.sp4OutCyclic F 2
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num) (by norm_num)).2
  exact false_of_autConf_of_noInvCommNine (center_psp44 hF)
    (NoInvCommNine.of_mulEquiv (spProjEquiv (F := F)).symm (noInvCommNine_sp44 hF)) h hν
    (fun p hp => CFSG.AGLEmbedding.mem_inner_of_pow_eq_one_of_not_dvd Nat.prime_three
      (by rw [hO]; norm_num) (h.elem.2 p hp)) hP

end Sp44Four

theorem not_psp44 {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) :
    ¬ StatedClassicalModel ↥K .PSp 2 2 2 := fun hK => by
  have := hQ.finite
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have := LinearFieldFour.charP_two_of_card_eq_four hF4
  obtain ⟨E, hE, hE9⟩ := exists_E9_psp44 hF4
  exact false_of_autConf_sp44 hF4 (h.autConf.map e) (h.card_map_rhoP_eq_nine hQ e
    (fun z hz => by rwa [center_psp44 hF4, Subgroup.mem_bot] at hz) hE hE9)

end CFSG.Quasithin.H13.S126C

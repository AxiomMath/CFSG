module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiIdent
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.KFacts.K72OutL3
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open Matrix

section Comm

theorem map_mem_commutator {G H : Type*} [Group G] [Group H] (f : G →* H) {g : G}
    (hg : g ∈ commutator G) : f g ∈ commutator H := by
  have h1 : f g ∈ (commutator G).map f := ⟨g, hg, rfl⟩
  rw [commutator_def, Subgroup.map_commutator] at h1
  rw [commutator_def]
  exact Subgroup.commutator_mono le_top le_top h1

theorem conj_mem_commutator {S : Type*} [Group S] [Group.IsPerfect S] (s : S) :
    MulAut.conj s ∈ commutator (MulAut S) := by
  apply map_mem_commutator MulAut.conj
  rw [Group.IsPerfect.commutator_eq_top]
  exact Subgroup.mem_top s

theorem mul_mul_inv_mul_inv_mem_commutator {G : Type*} [Group G] (σ τ : G) :
    σ * τ * σ⁻¹ * τ⁻¹ ∈ commutator G := by
  rw [← commutatorElement_def, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top σ) (Subgroup.mem_top τ)

theorem mem_inndiag_of_hasKind_inner_or_diagonal {M : Type*} [Group M] {P : PinnedAut M}
    {τ : MulAut M} {k : AutKind} (hk : P.HasKind τ k) (hk' : k = .inner ∨ k = .diagonal) :
    τ ∈ P.inndiag := by
  rcases hk' with rfl | rfl
  · exact P.isInnerDiagonal_of_isInnerAut ((P.hasKind_inner).mp hk)
  · exact ((P.hasKind_diagonal).mp hk).1

end Comm

section Linear

variable {K : Type} [Field K]

theorem commutator_le_linearAutGroup [Finite K] :
    commutator (MulAut (projectiveSL 3 K)) ≤ linearAutGroup 3 K := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [commutatorElement_def]
  exact OuterDerived.commutator_mem_linearAutGroup le_rfl g₁ g₂

theorem slFieldAut_mul_slConjugation_mul_inv (φ : K ≃+* K) (A : GL (Fin 3) K) :
    slFieldAut (Fin 3) K φ * slConjugation 3 K A * (slFieldAut (Fin 3) K φ)⁻¹ =
      slConjugation 3 K (frobGL φ A) := by
  have h1 : (slFieldAut (Fin 3) K φ)⁻¹ = slFieldAut (Fin 3) K φ⁻¹ := (map_inv _ φ).symm
  have h2 : ∀ x : GL (Fin 3) K, frobGL φ (frobGL φ⁻¹ x) = x := fun x => by
    rw [← frobGL_mul_apply, mul_inv_cancel, frobGL_one_apply]
  refine MulEquiv.ext fun g => SpecialLinearGroup.toGL_injective ?_
  calc SpecialLinearGroup.toGL ((slFieldAut (Fin 3) K φ * slConjugation 3 K A *
        (slFieldAut (Fin 3) K φ)⁻¹) g)
      = frobGL φ (A * frobGL φ⁻¹ (SpecialLinearGroup.toGL g) * A⁻¹) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, h1, toGL_slFieldAut, toGL_slConjugation,
          toGL_slFieldAut]
    _ = frobGL φ A * SpecialLinearGroup.toGL g * (frobGL φ A)⁻¹ := by
        rw [map_mul, map_mul, map_inv, h2]
    _ = SpecialLinearGroup.toGL (slConjugation 3 K (frobGL φ A) g) :=
        (toGL_slConjugation 3 K _ _).symm

theorem frobGL_diagUnits_frobenius [Finite K] [CharP K 2] (d : Kˣ) :
    frobGL (frobeniusEquiv K 2) (diagUnits d 1 1) = diagUnits d 1 1 * diagUnits d 1 1 := by
  rw [diagUnits_mul, one_mul]
  apply Units.ext
  rw [coe_frobGL, coe_diagUnits, coe_diagUnits, diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp [frobeniusEquiv_apply, frobenius_def, sq]

theorem slConjugation_diagUnits_mem_commutator [Finite K] [CharP K 2] (d : Kˣ) :
    slConjugation 3 K (diagUnits d 1 1) ∈ commutator (MulAut (SpecialLinearGroup (Fin 3) K)) := by
  have h := mul_mul_inv_mul_inv_mem_commutator (slFieldAut (Fin 3) K (frobeniusEquiv K 2))
    (slConjugation 3 K (diagUnits d 1 1))
  rwa [slFieldAut_mul_slConjugation_mul_inv, frobGL_diagUnits_frobenius, ← map_inv, ← map_mul,
    mul_inv_cancel_right] at h

theorem det_diagUnits (d : Kˣ) : Matrix.GeneralLinearGroup.det (diagUnits d 1 1) = d := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnits, det_diagonal, Fin.prod_univ_three]
  simp

theorem det_diagUnits_inv_mul (A : GL (Fin 3) K) :
    (((diagUnits (Matrix.GeneralLinearGroup.det A) 1 1)⁻¹ * A : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, det_diagUnits, inv_mul_cancel,
    Units.val_one]

theorem slConjugation_mem_commutator [Finite K] [CharP K 2] (A : GL (Fin 3) K) :
    slConjugation 3 K A ∈ commutator (MulAut (SpecialLinearGroup (Fin 3) K)) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  set D := diagUnits (Matrix.GeneralLinearGroup.det A) 1 1 with hD
  set S : SpecialLinearGroup (Fin 3) K := ⟨((D⁻¹ * A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
    det_diagUnits_inv_mul A⟩ with hSdef
  have hS : SpecialLinearGroup.toGL S = D⁻¹ * A := Units.ext rfl
  have hA : A = D * SpecialLinearGroup.toGL S := by rw [hS, mul_inv_cancel_left]
  rw [hA, map_mul]
  refine mul_mem (slConjugation_diagUnits_mem_commutator _) ?_
  have hconj : slConjugation 3 K (SpecialLinearGroup.toGL S) = MulAut.conj S := by
    refine MulEquiv.ext fun g => ?_
    rw [MulAut.conj_apply]
    exact slConjugation_toGL 3 K S g
  rw [hconj]
  exact conj_mem_commutator S

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem commutator_le_psuConj_range (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f) :
    commutator (MulAut (unitaryPSU h 3)) ≤ (psuConj h).range := by
  rw [commutator_def, Subgroup.commutator_le]
  intro σ _ τ _
  rw [commutatorElement_def]
  exact commutator_mem_psuConj_range h hq2 σ τ

theorem suField_mul_suConj_mul_inv (h : UnitaryFieldData p f K) (σ : K ≃+* K)
    (A : unitaryIsom3 h) :
    suField h σ * suConj h A * (suField h σ)⁻¹ =
      suConj h ⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩ := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, coe_suField, coe_suConj, coe_suField,
    coe_suConj, map_mul, map_mul, map_inv, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply,
    Subgroup.coe_inv, map_inv]
  rfl

theorem suConj_diagUnits_mem_commutator [CharP K 2] (h : UnitaryFieldData p f K) {d : Kˣ}
    (hD : diagUnits d 1 1 ∈ unitaryIsom3 h) :
    suConj h ⟨diagUnits d 1 1, hD⟩ ∈ commutator (MulAut (unitarySU p f K 3)) := by
  have := h.finite
  set D : unitaryIsom3 h := ⟨diagUnits d 1 1, hD⟩ with hDdef
  have heq : (⟨glAut (frobeniusEquiv K 2) (D : GL (Fin 3) K),
      glAut_mem_unitaryIsom3 (frobeniusEquiv K 2) D.2⟩ : unitaryIsom3 h) * D⁻¹ = D := by
    apply Subtype.ext
    change glAut (frobeniusEquiv K 2) (diagUnits d 1 1) * (diagUnits d 1 1)⁻¹ = diagUnits d 1 1
    rw [glAut_eq_frobGL, frobGL_diagUnits_frobenius, mul_inv_cancel_right]
  have hc := mul_mul_inv_mul_inv_mem_commutator (suField h (frobeniusEquiv K 2)) (suConj h D)
  rwa [suField_mul_suConj_mul_inv, ← map_inv, ← map_mul, heq] at hc

theorem suConj_mem_commutator [CharP K 2] (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f)
    (A : unitaryIsom3 h) : suConj h A ∈ commutator (MulAut (unitarySU p f K 3)) := by
  have : Group.IsPerfect (unitarySU p f K 3) := isPerfect_unitarySU_three h hq2
  set d : Kˣ := Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) with hd
  have hdnorm : h.bar (d : K) * d = 1 := by
    have h1 := congrArg Matrix.det (mem_unitaryIsom3.mp A.2)
    rw [det_mul, det_transpose, det_one, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← Matrix.GeneralLinearGroup.val_det_apply] at h1
    exact h1
  have hD : diagUnits d 1 1 ∈ unitaryIsom3 h := by
    rw [mem_unitaryIsom3, coe_diagUnits, diagonal_map (map_zero _), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hdnorm]
  set D : unitaryIsom3 h := ⟨diagUnits d 1 1, hD⟩ with hDdef
  have hS : ((D⁻¹ * A : unitaryIsom3 h) : GL (Fin 3) K) ∈ unitarySU p f K 3 :=
    (mem_unitarySU_iff h).mpr ⟨det_diagUnits_inv_mul (A : GL (Fin 3) K),
      mem_unitaryIsom3.mp (D⁻¹ * A).2⟩
  set S : unitarySU p f K 3 := ⟨_, hS⟩ with hSdef
  have hA : A = D * ⟨S, unitarySU_le_unitaryIsom3 S.2⟩ := by
    apply Subtype.ext
    change (A : GL (Fin 3) K) = (D : GL (Fin 3) K) * ((D⁻¹ * A : unitaryIsom3 h) : GL (Fin 3) K)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hA, map_mul]
  refine mul_mem (suConj_diagUnits_mem_commutator h hD) ?_
  have hconj : suConj h ⟨S, unitarySU_le_unitaryIsom3 S.2⟩ = MulAut.conj S := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [coe_suConj, MulAut.conj_apply]
    rfl
  rw [hconj]
  exact conj_mem_commutator S

end Unitary

section Kinds

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_commutator_of_inducesKindSL {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* SpecialLinearGroup (Fin 3) K) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {k : AutKind}
    (hk : (stdPinnedPSL 3 K).HasKind (descendAut 3 K (inducedAutHom L e ⟨x, hx⟩)) k)
    (hk' : k = .inner ∨ k = .diagonal) :
    thetaQuotMulAut L (compAction L ⟨x, hx⟩) ∈
      commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := by
  obtain ⟨A, hA⟩ := exists_eq_slConjugation_of_descendAut_mem
    (mem_inndiag_of_hasKind_inner_or_diagonal hk hk')
  have hβ : inducedAutHom L e ⟨x, hx⟩ ∈ commutator _ := by
    rw [hA]
    exact slConjugation_mem_commutator A
  have := map_mem_commutator (MulAut.congr e).symm.toMonoidHom hβ
  rwa [inducedAutHom_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this

theorem not_mem_commutator_of_inducesKindSL {K : Type} [Field K] [Finite K]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* SpecialLinearGroup (Fin 3) K) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {k : AutKind}
    (hk : (stdPinnedPSL 3 K).HasKind (descendAut 3 K (inducedAutHom L e ⟨x, hx⟩)) k)
    (hk1 : k ≠ .inner) (hk2 : k ≠ .diagonal) :
    thetaQuotMulAut L (compAction L ⟨x, hx⟩) ∉
      commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := by
  intro hmem
  have h1 := map_mem_commutator (MulAut.congr e).toMonoidHom hmem
  have h2 := commutator_le_linearAutGroup (map_mem_commutator (descendAut 3 K) h1)
  exact (stdPinnedPSL_separated (n := 3) (K := K) le_rfl).not_mem_inndiag_of_hasKind hk hk1 hk2
    (by rw [inducedAutHom_apply]; exact h2)

theorem mem_commutator_of_inducesKindSU3 {p f : ℕ} {K : Type} [Field K] [CharP K 2]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {k : AutKind}
    (hk : (stdPinnedPSU3 h).HasKind (MulAut.congr (suCenterEquiv h hq)
      (centerDescend _ (inducedAutHom L e ⟨x, hx⟩))) k)
    (hk' : k = .inner ∨ k = .diagonal) :
    thetaQuotMulAut L (compAction L ⟨x, hx⟩) ∈
      commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := by
  obtain ⟨A, hA⟩ := mem_inndiag_of_hasKind_inner_or_diagonal hk hk'
  have hβA : inducedAutHom L e ⟨x, hx⟩ = suConj h A :=
    eq_of_centerDescend_eq h hq (by rw [congr_centerDescend_suConj, hA])
  have hβ : inducedAutHom L e ⟨x, hx⟩ ∈ commutator _ := by
    rw [hβA]
    exact suConj_mem_commutator h hq A
  have := map_mem_commutator (MulAut.congr e).symm.toMonoidHom hβ
  rwa [inducedAutHom_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this

theorem not_mem_commutator_of_inducesKindSU3 {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {k : AutKind}
    (hk : (stdPinnedPSU3 h).HasKind (MulAut.congr (suCenterEquiv h hq)
      (centerDescend _ (inducedAutHom L e ⟨x, hx⟩))) k)
    (hk1 : k ≠ .inner) (hk2 : k ≠ .diagonal) :
    thetaQuotMulAut L (compAction L ⟨x, hx⟩) ∉
      commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := by
  intro hmem
  have h1 := map_mem_commutator (MulAut.congr e).toMonoidHom hmem
  have h2 := map_mem_commutator (centerDescend (unitarySU p f K 3)) h1
  have h3 := commutator_le_psuConj_range h hq
    (map_mem_commutator (MulAut.congr (suCenterEquiv h hq)).toMonoidHom h2)
  exact (stdPinnedPSU3_separated h).not_mem_inndiag_of_hasKind hk hk1 hk2
    (by rw [inducedAutHom_apply]; exact h3)

end Kinds

theorem exists_inndiag_of_isSLThreePiAt {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {n : ℕ} (hn : 1 ≤ n)
    (hL : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n))) :
    ∃ D : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)),
      (∀ σ τ : MulAut (L ⧸ aschbacherSolvableCore 3 L), σ * τ * σ⁻¹ * τ⁻¹ ∈ D) ∧
      (∀ x : G, ∀ hx : x ∈ Subgroup.normalizer (L : Set G),
        InducesStdKind L x .inner ∨ InducesStdKind L x .diagonal →
          Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hx⟩) ∈ D) ∧
      (∀ x : G, ∀ hx : x ∈ Subgroup.normalizer (L : Set G),
        InducesStdKind L x .field ∨ InducesStdKind L x .graphField →
          Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hx⟩) ∉ D) := by
  have hn3 : 3 ≤ 3 * n := by omega
  have hinner : ∀ x : G, InducesStdKind L x .inner ∨ InducesStdKind L x .diagonal →
      ∃ k, InducesStdKind L x k ∧ (k = .inner ∨ k = .diagonal) := by
    rintro x (hk | hk)
    · exact ⟨_, hk, Or.inl rfl⟩
    · exact ⟨_, hk, Or.inr rfl⟩
  have hfield : ∀ x : G, InducesStdKind L x .field ∨ InducesStdKind L x .graphField →
      ∃ k, InducesStdKind L x k ∧ k ≠ .inner ∧ k ≠ .diagonal := by
    rintro x (hk | hk)
    · exact ⟨_, hk, by decide, by decide⟩
    · exact ⟨_, hk, by decide, by decide⟩
  rcases hL with ⟨K₀, _, _, ⟨hK₀, hq₀, ⟨e₀⟩⟩ | ⟨hK₀, hq₀, ⟨e₀⟩⟩⟩
  ·
    have hIso : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (3 * n) ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) :=
      ⟨K₀, inferInstance, inferInstance, hK₀, ⟨e₀⟩⟩
    refine ⟨commutator _, mul_mul_inv_mul_inv_mem_commutator, fun x hx hk => ?_,
      fun x hx hk => ?_⟩
    · obtain ⟨k, hk, hk'⟩ := hinner x hk
      obtain ⟨K, _, _, hK, e₁, hxN, hkind⟩ := inducesKindSL_of_inducesStdKind hn3 hq₀ hIso hk
      have : CharP K 2 := (show PiField true 2 (3 * n) K from ⟨Nat.prime_two, by omega, hK⟩).charP
      exact mem_commutator_of_inducesKindSL e₁ hxN hkind hk'
    · obtain ⟨k, hk, hk1, hk2⟩ := hfield x hk
      obtain ⟨K, _, _, -, e₁, hxN, hkind⟩ := inducesKindSL_of_inducesStdKind hn3 hq₀ hIso hk
      exact not_mem_commutator_of_inducesKindSL e₁ hxN hkind hk1 hk2
  ·
    have hIso : Sec8.IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) :=
      ⟨K₀, inferInstance, inferInstance, hK₀, ⟨e₀⟩⟩
    have hm3 : 3 ∣ 2 ^ (3 * n) + 1 := by
      generalize 2 ^ (3 * n) = t at hq₀ ⊢
      omega
    refine ⟨commutator _, mul_mul_inv_mul_inv_mem_commutator, fun x hx hk => ?_,
      fun x hx hk => ?_⟩
    · obtain ⟨k, hk, hk'⟩ := hinner x hk
      obtain ⟨K, _, h, hq, e₁, hxN, hkind⟩ := inducesKindSU3_of_inducesStdKind hn3 hm3 hIso hk
      have : CharP K 2 := h.charP
      exact mem_commutator_of_inducesKindSU3 h hq e₁ hxN hkind hk'
    · obtain ⟨k, hk, hk1, hk2⟩ := hfield x hk
      obtain ⟨K, _, h, hq, e₁, hxN, hkind⟩ := inducesKindSU3_of_inducesStdKind hn3 hm3 hIso hk
      exact not_mem_commutator_of_inducesKindSU3 h hq e₁ hxN hkind hk1 hk2

end CFSG.RankThree.PartTwo.KFacts

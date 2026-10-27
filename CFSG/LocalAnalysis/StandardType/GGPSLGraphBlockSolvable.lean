module

public import CFSG.LocalAnalysis.StandardType.GGBlockEmbed
public import CFSG.LocalAnalysis.StandardType.GGPSLGraphDefs
public import CFSG.LocalAnalysis.StandardType.GGGraphNonePrimFamily

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix

private lemma pslB2d_hom_trivial_of_perfect {G A : Type} [Group G] [CommGroup A]
    [Group.IsPerfect G] (f : G →* A) : f = 1 := by
  rw [← MonoidHom.ker_eq_top_iff]
  apply top_le_iff.mp
  rw [← Group.IsPerfect.commutator_eq_top (G := G)]
  change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ f.ker
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, mul_comm (f a) (f b),
    mul_assoc (f b) (f a) ((f a)⁻¹), mul_inv_cancel (f a), mul_one, mul_inv_cancel (f b)]

private lemma pslB2d_SL_nontrivial {F : Type} [Field F] (k : ℕ) (hk : 2 ≤ k) :
    Nontrivial (Matrix.SpecialLinearGroup (Fin k) F) := by
  have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  refine ⟨⟨SpecialLinearGroup.transvection h01 (1 : F), 1, ?_⟩⟩
  intro h
  have hmat := congrArg (fun x : Matrix.SpecialLinearGroup (Fin k) F =>
    (x : Matrix (Fin k) (Fin k) F)) h
  rw [CFSG.LinearGroups.coe_transvection, Matrix.SpecialLinearGroup.coe_one] at hmat
  have hentry : (1 : F) = 0 := by
    have := congrFun (congrFun hmat ⟨0, by omega⟩) ⟨1, by omega⟩
    simpa using this
  exact one_ne_zero hentry

private lemma pslB2d_perfect {F : Type} [Field F] [Finite F] [CharP F 2]
    (k : ℕ) (hk : 2 ≤ k) (hnot : ¬ (k = 2 ∧ Nat.card F = 2)) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F) := by
  refine CFSG.LinearGroups.special_linear_isPerfect hk ?_
  by_cases hk3 : 3 ≤ k
  · exact Or.inl hk3
  · right
    have hk2 : k = 2 := by omega
    haveI : Fintype F := Fintype.ofFinite F
    have hcard_ne : Nat.card F ≠ 2 := fun h => hnot ⟨hk2, h⟩
    have h2 : 2 ≤ Nat.card F := by
      have := Fintype.one_lt_card (α := F)
      rw [Nat.card_eq_fintype_card]
      omega
    have hcard_ne3 : Nat.card F ≠ 3 := by
      intro h3
      have h0 : (Nat.card F : F) = 0 := by
        rw [Nat.card_eq_fintype_card]
        exact Nat.cast_card_eq_zero F
      rw [h3] at h0
      exact (by norm_num : ¬ 2 ∣ 3) ((CharP.cast_eq_zero_iff F 2 3).mp h0)
    have hcard_ge : 4 ≤ Nat.card F := by omega
    have h4 : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hcard_ge
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := Finset.univ) h4
    exact ⟨s, hs⟩

private lemma pslB2d_SL_le_pslBlock {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (k : ℕ),
      Nat.card F = Nat.card K ^ blockDegree (pslAlg B) e ∧
      Matrix.rank e = blockDegree (pslAlg B) e * k ∧ 0 < k ∧
      (Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F) →
        ∃ φ : Matrix.SpecialLinearGroup (Fin k) F →* ↥(pslBlock B e), Function.Injective φ) := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, -, -, hdim, hcard, -, hrank, hpos, hψinj,
    -, hψfix, -, hψB⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Module F (LinearMap.range e.mulVecLin) := hM
  letI : IsScalarTower K F (LinearMap.range e.mulVecLin) := hT
  refine ⟨F, hFld, hFin, hChar, Module.finrank F (LinearMap.range e.mulVecLin), hcard, ?_, hpos, ?_⟩
  · rw [hrank, hdim]
  · intro hperf
    haveI : Module.Finite K (LinearMap.range e.mulVecLin) := Module.Finite.of_finite
    haveI : Module.Finite F (LinearMap.range e.mulVecLin) :=
      Module.Finite.of_restrictScalars_finite K F (LinearMap.range e.mulVecLin)
    let b : Module.Basis (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F
        (LinearMap.range e.mulVecLin) := Module.finBasis F (LinearMap.range e.mulVecLin)
    let A0 : Type := Fin (Module.finrank F (LinearMap.range e.mulVecLin)) → F
    let iotaBar : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →* (A0 ≃ₗ[F] A0) :=
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F A0).toMonoidHom).comp
        ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL))
    have hIotaBar : Function.Injective iotaBar := by
      intro g h hgh
      exact SpecialLinearGroup.toGL_injective
        (Matrix.GeneralLinearGroup.toLin.injective
          ((LinearMap.GeneralLinearGroup.generalLinearEquiv F A0).injective hgh))
    let c : A0 ≃ₗ[F] LinearMap.range e.mulVecLin := b.equivFun.symm
    let conjC : (A0 ≃ₗ[F] A0) ≃*
        (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) :=
      { toFun := fun e => c.symm.trans (e.trans c)
        invFun := fun e => c.trans (e.trans c.symm)
        left_inv := fun e => by
          apply LinearEquiv.ext
          intro w
          simp [LinearEquiv.trans_apply]
        right_inv := fun e => by
          apply LinearEquiv.ext
          intro w
          simp [LinearEquiv.trans_apply]
        map_mul' := fun e f => by
          apply LinearEquiv.ext
          intro w
          simp [LinearEquiv.trans_apply, map_mul] }
    let iota : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
        (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) :=
      conjC.toMonoidHom.comp iotaBar
    have hIo : Function.Injective iota := conjC.injective.comp hIotaBar
    let A : Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
        GL (Fin n) K := ψ.comp iota
    haveI : Group.IsPerfect
        (Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F) :=
      hperf
    have htriv : (Matrix.GeneralLinearGroup.det.comp A) = 1 :=
      pslB2d_hom_trivial_of_perfect (Matrix.GeneralLinearGroup.det.comp A)
    have hdet : ∀ g : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F,
        (A g : Matrix (Fin n) (Fin n) K).det = 1 := by
      intro g
      have h := congrArg (fun f : Matrix.SpecialLinearGroup
          (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →* Kˣ => f g) htriv
      simpa using congrArg Units.val h
    let slgHom : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
        Matrix.SpecialLinearGroup (Fin n) K :=
      { toFun := fun g => ⟨(A g : Matrix (Fin n) (Fin n) K), hdet g⟩
        map_one' := by
          apply Subtype.ext
          rw [Matrix.SpecialLinearGroup.coe_one]
          exact congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) (map_one A)
        map_mul' := fun g h => by
          apply Subtype.ext
          exact congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) (map_mul A g h) }
    have hmemP : ∀ g, slgHom g ∈ pslBlock B e := by
      intro g
      refine Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · rw [Subgroup.mem_centralizer_iff]
        intro hB hBhB
        rw [Set.mem_singleton_iff] at hBhB
        subst hB
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        exact (hψB (iota g)).symm
      · exact hψfix (iota g)
    let φ : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →* ↥(pslBlock B e) :=
      { toFun := fun g => ⟨slgHom g, hmemP g⟩
        map_one' := Subtype.ext (map_one slgHom)
        map_mul' := fun g h => Subtype.ext (map_mul slgHom g h) }
    refine ⟨φ, ?_⟩
    intro g h hgh
    have h1 : slgHom g = slgHom h := congrArg Subtype.val hgh
    have h2 : A g = A h := Units.ext
      (congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h1)
    exact hIo (hψinj h2)

private lemma pslB2d_SL_not_solvable {F : Type} [Field F] [Finite F] [CharP F 2]
    (k : ℕ) (hk : 2 ≤ k) (hnot : ¬ (k = 2 ∧ Nat.card F = 2)) :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin k) F) := by
  haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin k) F) :=
    pslB2d_SL_nontrivial k hk
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F) :=
    pslB2d_perfect k hk hnot
  exact Group.IsPerfect.not_isSolvable _

private lemma pslB2d_not_solvable_of_SL_le {n : ℕ} {K : Type} [Field K]
    {B : GL (Fin n) K} {e : Matrix (Fin n) (Fin n) K}
    {F : Type} [Field F] {k : ℕ}
    (φ : Matrix.SpecialLinearGroup (Fin k) F →* ↥(pslBlock B e))
    (hφ : Function.Injective φ)
    (hns : ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin k) F)) :
    ¬ Group.IsSolvable ↥(pslBlock B e) := by
  intro hsol
  letI : Group.IsSolvable ↥(pslBlock B e) := hsol
  exact hns (solvable_of_solvable_injective hφ)

theorem pslGraph_block_solvable_cases {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    Group.IsSolvable ↥(pslBlock B e) →
      (Matrix.rank e = blockDegree (pslAlg B) e ∨
        (Matrix.rank e = 2 * blockDegree (pslAlg B) e ∧
          Nat.card K ^ blockDegree (pslAlg B) e = 2)) := by
  intro hsol
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hne, hnot2⟩ := hcon
  obtain ⟨F, hFld, hFin, hChar, k, hcard, hrank, hkpos, hφ⟩ := pslB2d_SL_le_pslBlock S P hP e he
  letI := hFld
  letI := hFin
  letI := hChar
  have hk1 : k ≠ 1 := by
    intro hk
    rw [hk, mul_one] at hrank
    exact hne hrank
  have hk2 : 2 ≤ k := by omega
  have hnot : ¬ (k = 2 ∧ Nat.card F = 2) := by
    rintro ⟨hk, hF2⟩
    apply hnot2
    refine ⟨?_, ?_⟩
    · rw [hrank, hk]; ring
    · rw [← hcard]; exact hF2
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F) :=
    pslB2d_perfect k hk2 hnot
  obtain ⟨φ, hφinj⟩ := hφ hperf
  exact pslB2d_not_solvable_of_SL_le φ hφinj (pslB2d_SL_not_solvable k hk2 hnot) hsol

end CFSG.StandardType

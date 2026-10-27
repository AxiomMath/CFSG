module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListThreeTranspCases
import CFSG.OddTranspositions.PartFour.ThirteenThreeRefl
import CFSG.OddTranspositions.PartFour.ThirteenThreeTwo
import CFSG.RankThree.PartOne.S11d.OrthModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

@[expose] def OddTranspListThreeTranspReflSixCoverCard : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2 →
    (∀ d ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
      ∀ e ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
        orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    Subgroup.center X ≠ ⊥ →
    ∀ f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3), (∀ x y, f x y = f y x) →
      (∀ x, (∀ y, f x y = 0) → x = 0) →
      (¬ ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
        ∀ x ∈ T, f x x = 0) →
      fischerCentralQuotientModel {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1) →
      Nat.card (Subgroup.center X) = 3

end CFSG.LocalAnalysis.WeakClosure81

namespace CFSG.OddTranspositions.PartFour

open CFSG.Fischer.Classification CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.WeakClosure81

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section Omega

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem commutator_orthogonalGroup_le_reflGroup (hf : IsF3Form f) (hm : 4 ≤ m)
    (hΩq : CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f)))) :
    commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)) ≤
      ((F3.reflGroup f).map (toLinEquiv (Fin m) (ZMod 3)).toMonoidHom).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)) := by
  have hΩc : CFSG.IsComponent (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f))) :=
    ⟨hΩq, (inferInstance : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f))).Normal).isSubnormal⟩
  have hle := f3ReflectionGroup_le_orthogonalGroup hf.symm (b := f) (n := m)
  have hRn : (((F3.reflGroup f).map (toLinEquiv (Fin m) (ZMod 3)).toMonoidHom).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f))).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact conj_mem_f3ReflectionGroup hf.symm g.2 hx⟩
  have : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)) :=
    Finite.of_injective (fun g => (toLinEquiv (Fin m) (ZMod 3)).symm g.1)
      (fun a b h => Subtype.ext ((toLinEquiv (Fin m) (ZMod 3)).symm.injective h))
  rcases CFSG.LocalCores.component_normal_subgroup hΩc hRn with h | h
  · exact h
  exfalso
  have hpm : ∀ x ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f)),
      (toLinEquiv (Fin m) (ZMod 3)).symm (x : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)) = 1 ∨
        (toLinEquiv (Fin m) (ZMod 3)).symm
          (x : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)) = -1 := by
    intro x hx
    set g := (toLinEquiv (Fin m) (ZMod 3)).symm (x : (Fin m → ZMod 3) ≃ₗ[ZMod 3] _) with hg
    have hgx : toLinEquiv (Fin m) (ZMod 3) g = x := MulEquiv.apply_symm_apply _ _
    have hiso : F3.IsIsom f g := fun a b => by
      rw [F3.act_def, F3.act_def, ← toLinEquiv_apply, ← toLinEquiv_apply, hgx]
      exact bilin_map_of_mem_orthogonalGroup_three hf.symm x.2 a b
    refine F3.eq_one_or_eq_neg_one hf hm hiso fun v hv =>
      F3.act_eq_or_of_commute hiso hv ?_
    have hrO : toLinEquiv (Fin m) (ZMod 3) (F3.refl f v) ∈
        TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f) :=
      hle ⟨F3.refl f v, F3.refl_mem_reflGroup v, rfl⟩
    have hrR : (⟨_, hrO⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup
        (LinearMap.BilinMap.toQuadraticMap f))) ∈
        ((F3.reflGroup f).map (toLinEquiv (Fin m) (ZMod 3)).toMonoidHom).subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)) :=
      Subgroup.mem_subgroupOf.mpr ⟨F3.refl f v, F3.refl_mem_reflGroup v, rfl⟩
    have hc := Subgroup.commutator_mem_commutator hx hrR
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    have hc' := congrArg (fun y : ↥(TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f)) => (toLinEquiv (Fin m) (ZMod 3)).symm
        (y : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3))) hc
    simp only [Subgroup.coe_mul, map_mul, MulEquiv.symm_apply_apply] at hc'
    exact hc'.symm
  obtain ⟨a, b, hab⟩ := hΩq.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  apply (toLinEquiv (Fin m) (ZMod 3)).symm.injective
  have key : ∀ u w : GL (Fin m) (ZMod 3), (u = 1 ∨ u = -1) → u * w = w * u := by
    rintro u w (rfl | rfl)
    · rw [one_mul, mul_one]
    · rw [neg_one_mul, mul_neg_one]
  simp only [Subgroup.coe_mul, map_mul]
  exact key _ _ (hpm a a.2)

end Omega

section Cover

open Matrix

variable {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}

theorem isOrth63Reflection_of_reflSix {X : Type} [Group X] [Finite X] {s : X}
    (hZ3 : Nat.card (Subgroup.center X) = 3) (hf : IsF3Form f)
    (hT : ¬ ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
      ∀ x ∈ T, f x x = 0)
    (φ : X ⧸ Subgroup.center X ≃* R3 f) (hφs : φ (QuotientGroup.mk s) ∈ D3 f) :
    IsOrth63Reflection X s := by
  classical
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hQ : (LinearMap.BilinMap.toQuadraticMap f).polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => hf.nondeg v
      fun w => by
        have := hv w
        rw [LinearMap.BilinMap.polar_toQuadraticMap, hf.symm w v, ← two_mul] at this
        exact (mul_eq_zero.mp this).resolve_left h2
  obtain ⟨b, c, hbc, ⟨e⟩⟩ : ∃ b c : ZMod 3, (∀ t : ZMod 3, t ^ 2 + b * t + c ≠ 0) ∧
      Nonempty ((LinearMap.BilinMap.toQuadraticMap f).IsometryEquiv
        (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 3) b c)) := by
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus
        (LinearMap.BilinMap.toQuadraticMap f) hQ (n := 3) (by norm_num)
        (by rw [Module.finrank_fin_fun]) with he | h
    · exfalso
      obtain ⟨e⟩ := he
      obtain ⟨-, T, hT3, hTQ⟩ :=
        CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := ZMod 3) (n := 3) le_rfl
      refine hT ⟨T.map e.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
      · rw [LinearEquiv.finrank_map_eq]
        exact hT3
      · rintro _ ⟨y, hy, rfl⟩
        have := e.symm.map_app y
        rw [LinearMap.BilinMap.toQuadraticMap_apply] at this
        rw [show (e.symm.toLinearEquiv.toLinearMap y) = e.symm y from rfl, this]
        exact hTQ y hy
    · exact h
  let L : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3) := e.toLinearEquiv
  have hL : ∀ x, CFSG.PGLModel.minusQuadForm 2 b c (L x) = f x x := fun x => by
    have h1 := e.map_app x
    rw [LinearMap.BilinMap.toQuadraticMap_apply,
      CFSG.LieType.Universal.Spin.coe_quadMinus] at h1
    exact h1
  let κ : GL (Fin 6) (ZMod 3) ≃* GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 3) :=
    ((toLinEquiv (Fin 6) (ZMod 3)).trans (CFSG.RankThree.PartOne.linConj L)).trans
      (toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 3)).symm
  have hκ : ∀ (g : GL (Fin 6) (ZMod 3)) (x : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3),
      ((κ g : GL _ (ZMod 3)) : Matrix _ _ (ZMod 3)) *ᵥ x =
        L ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ L.symm x) := fun g x => by
    rw [← toLinEquiv_apply]
    change ((toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 3))
      ((toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 3)).symm
        (CFSG.RankThree.PartOne.linConj L (toLinEquiv (Fin 6) (ZMod 3) g)))) x = _
    rw [MulEquiv.apply_symm_apply, CFSG.RankThree.PartOne.linConj_apply, toLinEquiv_apply]
  have hκinv : ∀ (g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 3)) (x : Fin 6 → ZMod 3),
      ((κ.symm g : GL _ (ZMod 3)) : Matrix _ _ (ZMod 3)) *ᵥ x =
        L.symm ((g : Matrix _ _ (ZMod 3)) *ᵥ L x) := fun g x => by
    have h1 := hκ (κ.symm g) (L x)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
    rw [h1, LinearEquiv.symm_apply_apply]
  have hκO : ∀ g ∈ F3.reflGroup f, κ g ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 3) b c := by
    intro g hg
    have hiso := F3.isIsom_of_mem hf hg
    refine Subgroup.subset_closure (fun v => ?_)
    have hv : v = L (L.symm v) := (L.apply_symm_apply v).symm
    rw [hκ, hL]
    conv_rhs => rw [hv, hL]
    have := hiso (L.symm v) (L.symm v)
    rwa [F3.act_def] at this
  have hΩq := (CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_six_derived
    (K := ZMod 3) (by rw [Nat.card_zmod]; decide) (LinearMap.BilinMap.toQuadraticMap f) hQ
    (by rw [Module.finrank_fin_fun]) fun ⟨T, hT3, hTQ⟩ => hT ⟨T, hT3, fun x hx => by
      have := hTQ x hx
      rwa [LinearMap.BilinMap.toQuadraticMap_apply] at this⟩)
  obtain ⟨-, -, -, -, -, -, -, -, hΩq, -⟩ := hΩq
  have hΩR := commutator_orthogonalGroup_le_reflGroup hf (by norm_num) hΩq
  have hΩκ : ⁅CFSG.PGLModel.orthogonalMinus 2 (ZMod 3) b c,
      CFSG.PGLModel.orthogonalMinus 2 (ZMod 3) b c⁆ ≤ (F3.reflGroup f).map κ.toMonoidHom := by
    intro x hx
    have hOinv : (CFSG.PGLModel.orthogonalMinus 2 (ZMod 3) b c).map κ.symm.toMonoidHom ≤
        Subgroup.closure {A : GL (Fin 6) (ZMod 3) | ∀ v,
          LinearMap.BilinMap.toQuadraticMap f ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) =
            LinearMap.BilinMap.toQuadraticMap f v} := by
      show (Subgroup.closure {A : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 3) | ∀ v,
        CFSG.PGLModel.minusQuadForm 2 b c ((A : Matrix _ _ (ZMod 3)) *ᵥ v) =
          CFSG.PGLModel.minusQuadForm 2 b c v}).map κ.symm.toMonoidHom ≤ _
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨A, hA, rfl⟩ v
      rw [MulEquiv.coe_toMonoidHom, hκinv, LinearMap.BilinMap.toQuadraticMap_apply,
        LinearMap.BilinMap.toQuadraticMap_apply, ← hL, ← hL, LinearEquiv.apply_symm_apply]
      exact hA (L v)
    have hx' : κ.symm x ∈ CFSG.Assembly.LowTwoRank.StatedOmega
        ⇑(LinearMap.BilinMap.toQuadraticMap f) := by
      have hmem : κ.symm x ∈ (⁅CFSG.PGLModel.orthogonalMinus 2 (ZMod 3) b c,
          CFSG.PGLModel.orthogonalMinus 2 (ZMod 3) b c⁆).map κ.symm.toMonoidHom := ⟨x, hx, rfl⟩
      rw [Subgroup.map_commutator] at hmem
      exact Subgroup.commutator_mono hOinv hOinv hmem
    rw [statedOmega_eq_comap rfl, Subgroup.mem_comap] at hx'
    rw [← Subgroup.map_subtype_commutator] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyR := hΩR hy
    rw [Subgroup.mem_subgroupOf] at hyR
    obtain ⟨r, hr, hrx⟩ := hyR
    refine ⟨r, hr, ?_⟩
    apply κ.symm.injective
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    apply (toLinEquiv (Fin 6) (ZMod 3)).injective
    rw [← MulEquiv.coe_toMonoidHom (toLinEquiv (Fin 6) (ZMod 3)), hrx]
    exact hyx
  let N : Subgroup (Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 3)) :=
    ((F3.reflGroup f).map κ.toMonoidHom).map Matrix.ProjGenLinGroup.mk
  let ρ : ↥(F3.reflGroup f) →* ↥N :=
    ((Matrix.ProjGenLinGroup.mk.comp κ.toMonoidHom).comp (F3.reflGroup f).subtype).codRestrict N
      fun r => ⟨κ r, ⟨r, r.2, rfl⟩, rfl⟩
  have hρs : Function.Surjective ρ := by
    rintro ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩⟩
    exact ⟨⟨r, hr⟩, rfl⟩
  have hcen : ∀ g : GL (Fin 6) (ZMod 3),
      κ g ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 3)) ↔
        g ∈ Subgroup.center (GL (Fin 6) (ZMod 3)) := fun g => by
    simp only [Subgroup.mem_center_iff]
    constructor
    · intro h x
      apply κ.injective
      rw [map_mul, map_mul]
      exact h (κ x)
    · intro h y
      obtain ⟨x, rfl⟩ := κ.surjective y
      rw [← map_mul, ← map_mul, h x]
  have hρker : ρ.ker = Subgroup.center ↥(F3.reflGroup f) := by
    ext r
    rw [MonoidHom.mem_ker]
    constructor
    · intro hr
      have h1 : Matrix.ProjGenLinGroup.mk (κ r) = 1 := congrArg Subtype.val hr
      rw [Matrix.ProjGenLinGroup.mk_eq_one, hcen] at h1
      exact Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_center_iff.mp h1 g)
    · intro hr
      apply Subtype.ext
      show Matrix.ProjGenLinGroup.mk (κ r) = 1
      rw [Matrix.ProjGenLinGroup.mk_eq_one, hcen]
      rcases F3.coe_eq_of_mem_center hf (by norm_num) hr with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h, Subgroup.mem_center_iff]
        intro g
        rw [neg_one_mul, mul_neg_one]
  let ρbar : R3 f ≃* ↥N :=
    (QuotientGroup.quotientMulEquivOfEq hρker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)
  let ψ : X →* ↥N :=
    (ρbar.toMonoidHom.comp φ.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center X))
  have hψs : Function.Surjective ψ :=
    ρbar.surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hψker : ψ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    change ρbar (φ (QuotientGroup.mk x)) = 1 ↔ _
    rw [map_eq_one_iff _ ρbar.injective, map_eq_one_iff _ φ.injective, QuotientGroup.eq_one_iff]
  obtain ⟨h, hh, hφh⟩ := hφs
  obtain ⟨v, hv, hvh⟩ := F3.mem_reflSet_iff.mp hh
  have hψ : ((ψ s : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 3)) =
      Matrix.ProjGenLinGroup.mk (κ h) := by
    change ((ρbar (φ (QuotientGroup.mk s)) : ↥N) :
      Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 3)) = _
    rw [hφh]
    rfl
  refine ⟨ZMod 3, inferInstance, inferInstance, Nat.card_zmod 3, b, c, hbc, N,
    Subgroup.map_mono hΩκ,
    Subgroup.map_mono (Subgroup.map_le_iff_le_comap.mpr fun g hg => hκO g hg),
    ψ, hψs, by rw [hψker, hZ3], hψker.le, κ h, hκO h h.2, ?_, hψ⟩
  let β : (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
    (LinearMap.BilinForm.flip f v).comp L.symm.toLinearMap
  have hA : ∀ x, ((κ h : GL _ (ZMod 3)) : Matrix _ _ (ZMod 3)) *ᵥ x = x + β x • L v := by
    intro x
    rw [hκ, ← F3.act_def, ← hvh, F3.act_refl hv, map_add, map_smul, LinearEquiv.apply_symm_apply]
    rfl
  have hLv : L v ≠ 0 := fun h0 => F3.ne_zero_of_norm_one hv (L.injective (h0.trans L.map_zero.symm))
  have hx₀ : β (L v) ≠ 0 := by
    change f (L.symm (L v)) v ≠ 0
    rw [LinearEquiv.symm_apply_apply, hv]
    exact one_ne_zero
  exact rank_sub_one_eq_one_of_transvection β hA hLv hx₀

end Cover

theorem oddTranspListThreeTranspReflSixCover_of_card
    (h : OddTranspListThreeTranspReflSixCoverCard) : OddTranspListThreeTranspReflSixCover := by
  intro X _ _ s hs hodd hncl hO2 hOZ hder h3 hZ f hsym hnd hT hM
  obtain ⟨φ, hφ⟩ := (fischerCentralQuotientModel_iff _).mp hM
  exact Or.inr (Or.inr (Or.inl (isOrth63Reflection_of_reflSix
    (h X s hs hodd hncl hO2 hOZ hder h3 hZ f hsym hnd hT hM) ⟨hsym, hnd⟩ hT φ
    ((hφ _).mp (IsConj.refl _)))))

end CFSG.OddTranspositions.PartFour

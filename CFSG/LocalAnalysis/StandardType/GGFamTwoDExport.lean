module

public import CFSG.LocalAnalysis.StandardType.GGFamTwoDGraph
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighPin
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate13659
public import Certificates.Certificate13660

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE

theorem fam_exists_twoD_export
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hker : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ)
    (hρΨ : ∀ γ ∈ componentRoots χ i, S.ρ γ ∈ componentRoots χ i)
    (h5 : 5 ≤ compRank (componentRoots χ i))
    (hD : (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1))
    (hout : ¬ twistInner (componentRoots χ i) (S.ρ : (Fin τ.rank → ℤ) → _))
    (b : Fin τ.rank → Lˣ) (j : KernelComponent (rootCharHom b))
    (hsel : componentRoots (rootCharHom b) j = componentRoots χ i) :
    ∃ (r e m : ℕ) (_ : Fact r.Prime) (_ : CharP L r) (_ : 5 ≤ m)
      (z : ModGL τ L)
      (ε : simpleRoots (componentRoots χ i) ≃ Fin m)
      (D : GenFixedRootDatum τ r L (SpanQuot (componentRoots χ i))),
      S.D.q = r ^ e ∧ 1 ≤ e ∧ D.e = e ∧
      (rationalComponentM S.ρ S.Γ χ i).map (MulAut.conj z⁻¹).toMonoidHom =
        D.orbitGroup ∧
      D.simpleRootsJ = ((simpleRoots (componentRoots χ i) :
        Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)) ∧
      (∀ β γ : simpleRoots (componentRoots χ i),
        corootPair (β : Fin τ.rank → ℤ) γ =
          CFSG.LieType.Universal.Spin.cartanD m (ε β) (ε γ)) ∧
      (∀ k : Fin m, k.val + 2 < m →
        D.θ (toReal (ε.symm k : Fin τ.rank → ℤ)) =
          toReal (ε.symm k : Fin τ.rank → ℤ)) ∧
      (∀ k l : Fin m, k.val + 2 = m → l.val + 1 = m →
        D.θ (toReal (ε.symm k : Fin τ.rank → ℤ)) =
          toReal (ε.symm l : Fin τ.rank → ℤ) ∧
        D.θ (toReal (ε.symm l : Fin τ.rank → ℤ)) =
          toReal (ε.symm k : Fin τ.rank → ℤ)) := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have := hchar
  set Ψ := componentRoots χ i with hΨdef
  have hΨ : IsRootComponent Ψ := by
    rw [hΨdef]
    exact isRootComponent_componentRoots i
  have hSC : ∀ T : Set (Fin τ.rank → ℤ), torusGroup τ L ⊔ rootSpan τ L T ≤ adjointGroup τ L :=
    fun T => sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  obtain ⟨v, hv, hmaps, hpos, hG, m, hm, ε, hε⟩ :=
    fam_exists_graphTwist_labelled S χ i hρΨ h5 hD hout
  have hmapsΨ : ∀ γ ∈ Ψ, S.rhoTwist v γ ∈ Ψ := by
    rw [hΨdef]
    exact hmaps
  have hposΨ : ∀ γ ∈ posRoots Ψ, S.rhoTwist v γ ∈ posRoots Ψ := by
    rw [hΨdef]
    exact hpos
  have hiso := S.iform_rhoTwist v
  have hinj := injective_of_iform _ hiso
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hf : IsIsometry Ψ (S.rhoTwist v) :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmapsΨ).1 hinj.injOn, fun γ _ δ' _ => hiso γ δ',
      fun γ _ => map_neg _ γ⟩
  have hΔ : ∀ β ∈ simpleRoots Ψ, S.rhoTwist v β ∈ simpleRoots Ψ := fun β hβ =>
    hf.apply_mem_simpleRoots hΨ hposΨ hβ
  have hv' : v ∈ componentWeylGroup (componentRoots (rootCharHom b) j) := by
    rw [hsel]
    exact hv
  have hΔ' : ∀ β ∈ simpleRoots (componentRoots (rootCharHom b) j),
      S.rhoTwist v β ∈ simpleRoots (componentRoots (rootCharHom b) j) := by
    intro β hβ
    rw [hsel] at hβ ⊢
    exact hΔ β hβ
  obtain ⟨y, hyZb, hyM, hyv, hpinb⟩ := S.exists_twoD_pin (a := b) hq j hv' hΔ'
  have hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L Ψ := hsel ▸ hyZb
  obtain ⟨Q, hQT, hQG, hstep⟩ := S.exists_step_frobTwist_adjoint hq
  have hyC : y ∈ adjointGroup τ L := hSC _ hyZ
  have hFc : ∀ g, frobTwistGL τ L r e (y * Q) g = y * S.D.step g * y⁻¹ := by
    intro g
    rw [hstep, frobTwistGL_apply, frobTwistGL_apply]
    group
  have hcT : y * Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    mul_mem (mem_normalizer_torusGroup_of_mem_monomialSubgroup hyM) hQT
  have hcG : (adjointGroup τ L).map (MulAut.conj (y * Q)).toMonoidHom = adjointGroup τ L := by
    have e1 : (MulAut.conj (y * Q)).toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp (MulAut.conj Q).toMonoidHom := by
      ext g
      simp [mul_assoc]
    rw [e1, ← Subgroup.map_map, hQG]
    exact CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hyC)
  have hπ : weylQuotientHom τ L ⟨y, hyM⟩ = v := weylQuotientHom_eq hyv
  have hU : ∀ γ ∈ componentRoots χ i,
      (rootSubgroup τ L γ).map (frobTwistGL τ L r e (y * Q)) =
        rootSubgroup τ L (S.rhoTwist v γ) := by
    intro γ hγ
    have hγr := hΨ.isRoot γ hγ
    have e1 : frobTwistGL τ L r e (y * Q) = (MulAut.conj y).toMonoidHom.comp S.D.step := by
      ext g : 1
      rw [hFc]
      rfl
    rw [e1, ← Subgroup.map_map, S.frob.map_rootSubgroup γ hγr,
      CFSG.RankThree.Lattice.GenFixedRootDatum.map_conj_rootSubgroup_of_mem_monomialSubgroup hyM
        ((S.frob.isRoot_iff γ).2 hγr), hπ]
    rfl
  have hpin' : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ A : SL2 L,
      frobTwistGL τ L r e (y * Q) (rootSL2 τ L β A) =
        rootSL2 τ L (S.rhoTwist v β) (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A) :=
    fun β hβ A => by
    rw [hFc]
    exact hpinb β (by rw [hsel]; exact hβ) A
  let χ₀ : Multiplicative (Fin τ.rank → ℤ) →* SpanQuot Ψ := spanChar Ψ
  obtain ⟨α₀, hα₀⟩ : (simpleRoots Ψ).Nonempty := by
    obtain ⟨⟨γ, hγ⟩, hγi⟩ := Quotient.exists_rep i
    have hγΨ : γ ∈ Ψ := ⟨hγ, hγi⟩
    obtain ⟨w, -, β, hβ, -⟩ := exists_smul_simpleRoot hΨ hγΨ
    exact ⟨β, hβ⟩
  have hα₀k : α₀ ∈ kernelRoots χ₀ := by
    rw [show χ₀ = spanChar (componentRoots χ i) from rfl, kernelRoots_spanChar i]
    exact simpleRoots_subset hα₀
  let j₀ : KernelComponent χ₀ := ⟦⟨α₀, hα₀k⟩⟧
  let A : Set (Fin τ.rank → ℤ) := componentRoots χ₀ j₀
  have hset : A = Ψ := by
    rw [hΨdef]
    exact componentRoots_spanChar i j₀
  have hmaps₀ : ∀ γ ∈ A, S.rhoTwist v γ ∈ A := by
    intro γ hγ
    rw [hset] at hγ ⊢
    exact hmaps γ hγ
  have hpos₀ : ∀ γ ∈ posRoots A, S.rhoTwist v γ ∈ posRoots A := by
    intro γ hγ
    rw [hset] at hγ ⊢
    exact hpos γ hγ
  have hG₀ : IsGraphTwist A (S.rhoTwist v) := by
    rw [hset]
    exact hG
  have hU₀ : ∀ γ ∈ A,
      (rootSubgroup τ L γ).map (frobTwistGL τ L r e (y * Q)) =
        rootSubgroup τ L (S.rhoTwist v γ) := by
    intro γ hγ
    rw [hset] at hγ
    exact hU γ hγ
  have hpin₀ : ∀ β ∈ simpleRoots A, ∀ B : SL2 L,
      frobTwistGL τ L r e (y * Q) (rootSL2 τ L β B) =
        rootSL2 τ L (S.rhoTwist v β)
          (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) B) := by
    intro β hβ B
    rw [hset] at hβ
    exact hpin' β hβ B
  obtain ⟨D, hDe, hDθ, hDs₀, _, hCperf, hCle, hcomm⟩ :=
    CompsPTwoDExport.exists_twoD_datum (M := SpanQuot Ψ) (χ := χ₀) hτ (e := e)
      (by omega : 1 ≤ e) j₀ (S.rhoTwist v) hiso hmaps₀ hpos₀ hG₀ (c := y * Q) hcT hcG hU₀ hpin₀
  have hDs : D.simpleRootsJ = ((simpleRoots A :
      Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)) := hDs₀
  have key : ∃ (r e m : ℕ) (_ : Fact r.Prime) (_ : CharP L r) (_ : 5 ≤ m)
      (z : ModGL τ L)
      (ε : simpleRoots Ψ ≃ Fin m)
      (D : GenFixedRootDatum τ r L (SpanQuot A)),
      S.D.q = r ^ e ∧ 1 ≤ e ∧ D.e = e ∧
      (rationalComponentM S.ρ S.Γ χ i).map (MulAut.conj z⁻¹).toMonoidHom =
        D.orbitGroup ∧
      D.simpleRootsJ = ((simpleRoots A :
        Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)) ∧
      (∀ β γ : simpleRoots Ψ,
        corootPair (β : Fin τ.rank → ℤ) γ =
          CFSG.LieType.Universal.Spin.cartanD m (ε β) (ε γ)) ∧
      (∀ k : Fin m, k.val + 2 < m →
        D.θ (toReal (ε.symm k : Fin τ.rank → ℤ)) =
          toReal (ε.symm k : Fin τ.rank → ℤ)) ∧
      (∀ k l : Fin m, k.val + 2 = m → l.val + 1 = m →
        D.θ (toReal (ε.symm k : Fin τ.rank → ℤ)) =
          toReal (ε.symm l : Fin τ.rank → ℤ) ∧
        D.θ (toReal (ε.symm l : Fin τ.rank → ℤ)) =
          toReal (ε.symm k : Fin τ.rank → ℤ)) := by
    set C : Subgroup (ModGL τ L) := D.orbitGroup with hCdef
    have hyZ' : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) :=
      (sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hyZ
    obtain ⟨z, hzZ, hz1⟩ := exists_lang_torus_sup_kernelRoots S Nat.one_pos
      (fun γ hγ => by rw [Function.iterate_one]; exact hker γ hγ) hyZ'
    have hz : S.D.step z = z * y := by
      simpa only [iterHom_eq_iterate, Function.iterate_one] using hz1
    have hzC : z ∈ adjointGroup τ L := hSC _ hzZ
    have hnorm : z ∈ Subgroup.normalizer (rootSpan τ L Ψ : Set (ModGL τ L)) :=
      Subgroup.mem_normalizer_iff.2 fun g => mem_componentRootSpan_iff_conj_of_mem hzZ i g
    set φ : ModGL τ L →* ModGL τ L := (MulAut.conj z⁻¹).toMonoidHom with hφ
    have hφinj : Function.Injective φ := (MulAut.conj z⁻¹).injective
    have hφapp : ∀ g, φ g = z⁻¹ * g * z := fun g => by
      rw [hφ]
      simp
    set M' : Subgroup (ModGL τ L) :=
      adjointGroup τ L ⊓ (frobTwistGL τ L r e (y * Q)).eqLocus (MonoidHom.id _) with hM'
    have hstepz : ∀ g, frobTwistGL τ L r e (y * Q) (z⁻¹ * g * z) = z⁻¹ * S.D.step g * z := by
      intro g
      rw [hFc, map_mul, map_mul, map_inv, hz]
      group
    have hMap : S.D.model.map φ = M' := by
      ext g
      constructor
      · rintro ⟨x, ⟨hxC, hxF⟩, rfl⟩
        have hxs : S.D.step x = x := hxF
        rw [hφapp]
        refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hzC) hxC) hzC, ?_⟩
        change frobTwistGL τ L r e (y * Q) (z⁻¹ * x * z) = z⁻¹ * x * z
        rw [hstepz, hxs]
      · rintro ⟨hgC, hgF⟩
        have hgF' : frobTwistGL τ L r e (y * Q) g = g := hgF
        refine ⟨z * g * z⁻¹, Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hzC hgC) (inv_mem hzC), ?_⟩, ?_⟩
        · change S.D.step (z * g * z⁻¹) = z * g * z⁻¹
          have h1 := hstepz (z * g * z⁻¹)
          have e2 : z⁻¹ * (z * g * z⁻¹) * z = g := by group
          rw [e2, hgF'] at h1
          calc S.D.step (z * g * z⁻¹) = z * (z⁻¹ * S.D.step (z * g * z⁻¹) * z) * z⁻¹ := by group
            _ = z * g * z⁻¹ := by rw [← h1]
        · rw [hφapp]
          group
    have hrr : rationalRootsM S.ρ χ i = A := by
      rw [hset, hΨdef]
      ext γ
      constructor
      · rintro ⟨k, δ, hδ, rfl⟩
        induction k generalizing δ with
        | zero => exact hδ
        | succ k ih =>
          rw [Function.iterate_succ_apply]
          exact ih (S.ρ δ) (hρΨ δ hδ)
      · intro hγ
        exact ⟨0, γ, hγ, rfl⟩
    have hspanΨ : (rootSpan τ L Ψ).map φ = rootSpan τ L Ψ :=
      CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (inv_mem hnorm)
    have hspanA : (rootSpan τ L A).map φ = rootSpan τ L A := by
      rw [hset]
      exact hspanΨ
    have hRmap : (rationalComponentM S.ρ S.Γ χ i).map φ =
        ⁅rootSpan τ L A ⊓ ⁅M', M'⁆, rootSpan τ L A ⊓ ⁅M', M'⁆⁆ := by
      rw [rationalComponentM, rationalSpanM, hrr, Subgroup.map_commutator,
        Subgroup.map_inf_eq _ _ _ hφinj, hspanA]
      change ⁅_ ⊓ (⁅S.D.model, S.D.model⁆).map φ, _ ⊓ (⁅S.D.model, S.D.model⁆).map φ⁆ = _
      rw [Subgroup.map_commutator, hMap]
    have hRC : (rationalComponentM S.ρ S.Γ χ i).map φ = C := by
      rw [hRmap]
      have hCC : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 hCperf
      have hle : rootSpan τ L A ⊓ ⁅M', M'⁆ ≤ rootSpan τ L A ⊓ M' :=
        inf_le_inf_left _ (Subgroup.commutator_le_self M')
      refine le_antisymm (le_trans (Subgroup.commutator_mono hle hle) hcomm) ?_
      have hCM : C ≤ M' := hCle.trans inf_le_right
      have hCle' : C ≤ rootSpan τ L A ⊓ ⁅M', M'⁆ := by
        refine le_inf (hCle.trans inf_le_left) ?_
        rw [← hCC]
        exact Subgroup.commutator_mono hCM hCM
      calc C = ⁅C, C⁆ := hCC.symm
        _ ≤ _ := Subgroup.commutator_mono hCle' hCle'
    refine ⟨r, e, m, ⟨hr⟩, hchar, hm, z, ε, D, hq, he, hDe, hRC, hDs, hε.1, fun k hk => ?_,
      fun k l hk hl => ?_⟩
    · rw [hDθ, latticeRealExt_toReal, hε.2.1 k hk]
    · obtain ⟨h1, h2⟩ := hε.2.2 k l hk hl
      rw [hDθ, latticeRealExt_toReal, latticeRealExt_toReal, h1, h2]
      exact ⟨rfl, rfl⟩

  exact hset ▸ key
end CFSG.StandardType.TableCRes

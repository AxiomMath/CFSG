module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallPiece

public section

namespace CFSG.StandardType

namespace SevOmSmall

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 SevOm

theorem isSolvable_SL_two {E : Type} [Field E] [Finite E] (hE : Nat.card E = 2) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) := by
  have : Fintype E := Fintype.ofFinite E
  have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) E) = 6 := by
    rw [Matrix.card_SL_field, Fin.prod_univ_two, Fintype.card_eq_nat_card, hE]
    simp
  have : Finite (Matrix.SpecialLinearGroup (Fin 2) E) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [hc, show (6 : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  decide

section Main

open CFSG.LocalAnalysis.ComponentInitial LayerCores LayerFacts OmNonsplit
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem exists_witness_orth_small (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hKp : (Nat.card K = 2 ∧ p = 3) ∨ (Nat.card K = 4 ∧ p = 5))
    (hAΩ : A ≤ orthDerived Q) (F : Frame Q p A r) (hr : 4 ≤ r)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hR : RestrClosed Q A) (s₀ : Multiplicative (Fin r → ZMod p)) {L : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L (orthDerived Q ⊓ Subgroup.centralizer {F.ι s₀}))
    (hpL : p ∣ Nat.card L) :
    (∃ e ∈ L, e ∈ A ∧ e ≠ 1 ∧ ∃ L₂ : Subgroup (V ≃ₗ[K] V),
      CFSG.Assembly.IsComponentOf L₂ (orthDerived Q ⊓ Subgroup.centralizer {e}) ∧
      Nat.card (A ⊓ Subgroup.centralizer (L₂ : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p ^ 2) ∨
    Nat.card (A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p ^ 2 ∨
    (p = 5 ∧ ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 4 ∧
      Nonempty (↥L ≃* SL(2, E))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpq : p ∣ Nat.card K + 1 := by
    rcases hKp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  obtain ⟨s, hsL, hs1, j, j', hs⟩ := exists_small_supp hQ hp hp2 hAΩ F hmax s₀ hL hpL
  obtain ⟨k, k', hkk, hkj, hkj', hk'j, hk'j'⟩ := exists_two_ne hr j j'
  have hz : ∀ i, i ≠ j → i ≠ j' → toAdd s i = 0 := fun i hij hij' => by
    by_contra h0
    rcases hs i h0 with h | h
    · exact hij h
    · exact hij' h
  have hUk := F.le_fixedSpace (hz k hkj hkj')
  have hUk' := F.le_fixedSpace (hz k' hk'j hk'j')
  have h4 := F.finrank_add_le hkk hUk hUk'
  have h2k := F.two_le_finrank k
  have h2k' := F.two_le_finrank k'
  by_cases hsp : SplitFour (Q.comp (fixedSpace (F.ι s)).subtype)
  swap
  · exact Or.inl ⟨F.ι s, hsL, F.mem s, hs1, direct_of_supp hQ hp hp2 hAΩ F hs (by omega) hsp⟩
  have hfix4 : finrank K (fixedSpace (F.ι s)) = 4 := hsp.1
  have hthree : ∀ i₁ i₂ i₃ : Fin r, i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ → toAdd s i₁ = 0 →
      toAdd s i₂ = 0 → toAdd s i₃ = 0 → False := by
    intro i₁ i₂ i₃ h12 h13 h23 h1 h2 h3
    have := F.finrank_add_add_le h12 h13 h23 (F.le_fixedSpace h1) (F.le_fixedSpace h2)
      (F.le_fixedSpace h3)
    have := F.two_le_finrank i₁
    have := F.two_le_finrank i₂
    have := F.two_le_finrank i₃
    omega
  have hsj : toAdd s j ≠ 0 := fun h0 =>
    hthree j k k' (Ne.symm hkj) (Ne.symm hk'j) hkk h0 (hz k hkj hkj') (hz k' hk'j hk'j')
  have hsj' : toAdd s j' ≠ 0 := fun h0 =>
    hthree j' k k' (Ne.symm hkj') (Ne.symm hk'j') hkk h0 (hz k hkj hkj') (hz k' hk'j hk'j')
  have hall : ∀ i, i = j ∨ i = j' ∨ i = k ∨ i = k' := by
    intro i
    by_contra hne
    push Not at hne
    exact hthree i k k' hne.2.2.1 hne.2.2.2 hkk (hz i hne.1 hne.2.1) (hz k hkj hkj')
      (hz k' hk'j hk'j')
  have hjj' : j ≠ j' := by
    intro hjj
    subst hjj
    obtain ⟨i₁, i₂, i₃, h12, h13, h23, h1j, h2j, h3j⟩ := exists_three_ne hr j
    exact hthree i₁ i₂ i₃ h12 h13 h23 (hz i₁ h1j h1j) (hz i₂ h2j h2j) (hz i₃ h3j h3j)
  have hfixeq : fixedSpace (F.ι s) = F.U k ⊔ F.U k' := by
    symm
    refine Submodule.eq_of_le_of_finrank_le (sup_le hUk hUk') ?_
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (F.U k) (F.U k')
    rw [F.inf_eq_bot hkk, finrank_bot, add_zero] at h1
    omega
  set b := F.ι s₀ with hb
  have hxb : OddOrderIsometry Q p b := F.oddOrderIsometry hQ hp2 hp hAΩ s₀
  have hL' := isComponentOf_isometryCentralizer hL
  obtain ⟨h, hh, hLF⟩ := exists_le_supportedBlock hxb hL'
  have heoth : ∀ v ∈ othersSpace b.toLinearMap h, F.ι s v = v :=
    (mem_supportedBlock.mp (hLF hsL)).2
  have hAC : ∀ c ∈ A, c ∈ isometryCentralizer Q b := by
    intro c hc
    obtain ⟨t, rfl⟩ := F.exists_eq hc
    refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup (hAΩ hc),
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hLq : CFSG.IsQuasisimple L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2
  by_cases hX : h = X - 1
  ·
    subst hX
    rcases fixed_case_small hxb hp hp2 hL' hLF with hin | ⟨hK4, eL⟩
    · have hδF : F.ι (ofAdd (Pi.single j 1)) ∈ supportedBlock Q b (X - 1) :=
        mem_supportedBlock.mpr ⟨hAC _ (F.mem _), fun v hv => F.fix_single hsj (heoth v hv)⟩
      refine Or.inl ⟨_, hin _ hδF (F.pow_p _), F.mem _, F.single_ne_one j, ?_⟩
      have hδz : ∀ i, i ≠ j →
          toAdd (ofAdd (Pi.single j (1 : ZMod p)) : Multiplicative (Fin r → ZMod p)) i = 0 :=
        fun i hij => by rw [toAdd_ofAdd, Pi.single_eq_of_ne hij]
      have h6 := F.finrank_add_add_le (Ne.symm hkj') (Ne.symm hk'j') hkk
        (F.le_fixedSpace (hδz j' (Ne.symm hjj'))) (F.le_fixedSpace (hδz k hkj))
        (F.le_fixedSpace (hδz k' hk'j))
      have := F.two_le_finrank j'
      exact direct_of_supp hQ hp hp2 hAΩ F (j := j) (j' := j)
        (fun i hi => Or.inl (by by_contra hij; exact hi (hδz i hij))) (by omega)
        (fun hsp' => by have := hsp'.1; omega)
    · rcases hKp with ⟨h2, -⟩ | ⟨h4', h5⟩
      · omega
      · exact Or.inr (Or.inr ⟨h5, K, inferInstance, inferInstance, h4', eL⟩)
  have hLeq := free_case hxb hp hp2 hh hX hL' hLF
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself := hxb.reciprocal_eq_of_dvd_card_succ hp hpq hh hX
  have hsplit := fun i => Frame.le_or_le F hR hxb hh hself i
  have hUV : ∀ i, toAdd s i ≠ 0 → F.U i ≤ primaryComponent b.toLinearMap h := by
    intro i hi
    refine (hsplit i).resolve_right fun hio => ?_
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot i)
    exact hu0 (F.fpf s i hi u hu (heoth u (hio hu)))
  have hUj := hUV j hsj
  have hUj' := hUV j' hsj'
  have hLq' : CFSG.IsQuasisimple ↥(specialBlock Q b h) := hLeq ▸ hLq
  have hm := two_le_primaryMultiplicity hxb hh hLq'
  by_cases hB : F.U k ≤ primaryComponent b.toLinearMap h ∨
      F.U k' ≤ primaryComponent b.toLinearMap h
  ·
    refine Or.inr (Or.inl ?_)
    obtain ⟨k₁, k₂, hk₁V, hk₂⟩ : ∃ k₁ k₂ : Fin r, F.U k₁ ≤ primaryComponent b.toLinearMap h ∧
        ∀ i, i = j ∨ i = j' ∨ i = k₁ ∨ i = k₂ := by
      rcases hB with hB | hB
      · exact ⟨k, k', hB, hall⟩
      · exact ⟨k', k, hB, fun i => by have := hall i; tauto⟩
    refine Frame.card_le_of_coords F inf_le_left j k₂ fun t ht htj htk₂ => ?_
    obtain ⟨htA, htC⟩ := Subgroup.mem_inf.mp ht
    have hMF : ∀ f ∈ specialBlock Q b h, ∀ v, F.ι t (f v) = f (F.ι t v) := by
      intro f hf v
      rw [← hLeq] at hf
      have h1 := Subgroup.mem_centralizer_iff.mp htC f hf
      exact (LinearEquiv.congr_fun h1 v).symm
    have hMc : F.ι t ∈ Subgroup.centralizer ({b} : Set (V ≃ₗ[K] V)) :=
      (Subgroup.mem_inf.mp (hAC _ htA)).2
    obtain ⟨z, hz⟩ := exists_smul_of_commute_selfDual hxb hp hp2 hh hX hself.symm hm hMc hMF
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot j)
    have hz1 : z = 1 := by
      have h1 : u = ((z • (⟨u, hUj hu⟩ : primaryComponent b.toLinearMap h) :
          primaryComponent b.toLinearMap h) : V) :=
        (F.triv t j htj u hu).symm.trans (hz ⟨u, hUj hu⟩)
      have h2 : (z - 1) • (⟨u, hUj hu⟩ : primaryComponent b.toLinearMap h) = 0 := by
        rw [sub_smul, one_smul, sub_eq_zero]
        exact Subtype.ext h1.symm
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd (congrArg Subtype.val h3) hu0
    have htriv : ∀ v ∈ primaryComponent b.toLinearMap h, F.ι t v = v := fun v hv => by
      have h1 := hz ⟨v, hv⟩
      rw [hz1, one_smul] at h1
      exact h1
    have hcoordV : ∀ i, F.U i ≤ primaryComponent b.toLinearMap h → toAdd t i = 0 := by
      intro i hi
      by_contra h0
      obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot i)
      exact hw0 (F.fpf t i h0 w hw (htriv w (hi hw)))
    apply toAdd.injective
    funext i
    rw [toAdd_one, Pi.zero_apply]
    rcases hk₂ i with rfl | rfl | rfl | rfl
    · exact htj
    · exact hcoordV _ hUj'
    · exact hcoordV _ hk₁V
    · exact htk₂
  push Not at hB
  obtain ⟨hBk, hBk'⟩ := hB
  have hko := (hsplit k).resolve_left hBk
  have hk'o := (hsplit k').resolve_left hBk'
  have hPnd : ∀ w ∈ F.U j ⊔ F.U j',
      (∀ v ∈ F.U j ⊔ F.U j', QuadraticMap.polar Q v w = 0) → w = 0 := by
    intro w hw hw0
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hw
    have ha0 : a = 0 := F.nondeg j a ha fun v hv => by
      have h1 := hw0 v (Submodule.mem_sup_left hv)
      rwa [QuadraticMap.polar_add_right, F.orth j j' hjj' v hv a' ha', add_zero] at h1
    have ha'0 : a' = 0 := F.nondeg j' a' ha' fun v hv => by
      have h1 := hw0 v (Submodule.mem_sup_right hv)
      rwa [QuadraticMap.polar_add_right, F.orth j' j (Ne.symm hjj') v hv a ha, zero_add] at h1
    rw [ha0, ha'0, add_zero]
  have hVP : ∀ v ∈ primaryComponent b.toLinearMap h, v ∈ F.U j ⊔ F.U j' := by
    intro v hv
    obtain ⟨w, hw, w', hw', hww⟩ :=
      CFSG.RankThree.PartOne.KCOrthogonal.exists_add_of_isCompl (isCompl_orthogonal hPnd) v
    have hw'fix : w' ∈ F.U k ⊔ F.U k' := by
      rw [← hfixeq]
      refine mem_fixedSpace.mpr ((F.fix s w').mpr fun i hi u hu => ?_)
      rcases hs i hi with rfl | rfl
      · exact mem_orthogonal_polar.mp hw' u (Submodule.mem_sup_left hu)
      · exact mem_orthogonal_polar.mp hw' u (Submodule.mem_sup_right hu)
    have hw'o : w' ∈ othersSpace b.toLinearMap h := sup_le hko hk'o hw'fix
    have hwV : w ∈ primaryComponent b.toLinearMap h := sup_le hUj hUj' hw
    have hw'V : w' ∈ primaryComponent b.toLinearMap h := by
      have : w' = v - w := by rw [← hww]; abel
      rw [this]
      exact Submodule.sub_mem _ hv hwV
    have hw'0 : w' = 0 :=
      Submodule.disjoint_def.mp (hxb.isCompl_orbit_others hh).disjoint w'
        (Submodule.mem_sup_left hw'V) hw'o
    rw [← hww, hw'0, add_zero]
    exact hw
  obtain ⟨u, -, hU⟩ := Frame.exists_line F hR hxb hh hX hUj
  obtain ⟨u', -, hU'⟩ := Frame.exists_line F hR hxb hh hX hUj'
  have hm2 : primaryMultiplicity b.toLinearMap h = 2 := by
    refine le_antisymm ?_ hm
    let φ : (Fin 2 → AdjoinRoot h) →ₗ[AdjoinRoot h] primaryComponent b.toLinearMap h :=
      (LinearMap.proj 0).smulRight u + (LinearMap.proj 1).smulRight u'
    have hφ : Function.Surjective φ := by
      intro v
      obtain ⟨a, ha, a', ha', hv⟩ := Submodule.mem_sup.mp (hVP v v.2)
      obtain ⟨z, hz⟩ := hU a ha
      obtain ⟨z', hz'⟩ := hU' a' ha'
      refine ⟨![z, z'], Subtype.ext ?_⟩
      show ((z • u + z' • u' : primaryComponent b.toLinearMap h) : V) = (v : V)
      rw [Submodule.coe_add, hz, hz', hv]
    have h1 := LinearMap.finrank_range_le φ
    rw [LinearMap.range_eq_top.mpr hφ, finrank_top, Module.finrank_fin_fun] at h1
    exact h1
  obtain ⟨E, _, _, hE, ⟨eE⟩⟩ := exists_specialBlock_equiv_SL2 hxb hp hp2 hpq hh hX hm2
  rcases hKp with ⟨hK2, -⟩ | ⟨hK4, hp5⟩
  · exfalso
    have := isSolvable_SL_two (hE.trans hK2)
    have hs : Group.IsSolvable ↥(specialBlock Q b h) :=
      Group.isSolvable_of_isSolvable_injective (f := eE.toMonoidHom) eE.injective
    exact ClNonsplit.not_isQuasisimple_of_le hs (le_of_eq hLeq) hLq
  · exact Or.inr (Or.inr ⟨hp5, E, inferInstance, inferInstance, hE.trans hK4,
      ⟨(MulEquiv.subgroupCongr hLeq).trans eE⟩⟩)

end Main

end SevOmSmall

end CFSG.StandardType

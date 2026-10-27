module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFrame
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsComp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmFix
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarFixed

public section

namespace CFSG.StandardType

namespace SevOm

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

section Special

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [CharP K 2] in
theorem isQuasisimple_specialBlock_paired (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
    have := hx.p_lt_card_adjoinRoot hp hh hne1
    have := hp.two_le
    omega
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm)
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hm h4)

theorem card_primeFactors_gu {n : ℕ} (hn : n = 18 ∨ n = 648) : n.primeFactors.card ≤ 2 :=
  LayerCores.card_primeFactors_small hn

theorem isQuasisimple_or_isSolvable_specialBlock_selfDual (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) ∨ Group.IsSolvable ↥(specialBlock Q x h) := by
  classical
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, -, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hpo hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  have hℓ : ℓ = 2 := by
    have := hU.charP
    have h2 : CharP (AdjoinRoot h) 2 := charP_of_injective_algebraMap
      (algebraMap K (AdjoinRoot h)).injective 2
    exact CharP.eq (AdjoinRoot h) this h2
  subst hℓ
  have hfd : 1 ≤ f * d := hU.one_le
  set m := primaryMultiplicity x.toLinearMap h with hmdef
  by_cases hbig : 4 ≤ 2 ^ (f * d) ∨ 4 ≤ m
  · left
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm ?_
    rcases Nat.lt_or_ge m 3 with h2 | h3
    · have hm2 : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 := by
        have : m = 2 := by omega
        exact this
      exact CFSG.RankThree.Classical.isQuasisimple_sesqSpecialUnitaryGroup hU hBsymm hBl hm2
        (by omega)
    · refine isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hU hBsymm hBl h3 fun e => ?_
      have h1 : m = 3 := congrArg Prod.fst e
      have h2 : 2 ^ (f * d) = 2 := congrArg Prod.snd e
      omega
  · right
    push Not at hbig
    have h2 : 2 ^ (f * d) = 2 := by
      have : f * d = 1 := by
        by_contra hne
        have : 2 ≤ f * d := by omega
        have : 2 ^ 2 ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) this
        omega
      rw [this, pow_one]
    have hcardU : Nat.card (sesqUnitaryGroup B) = 18 ∨ Nat.card (sesqUnitaryGroup B) = 648 := by
      rcases (show m = 2 ∨ m = 3 by omega) with hm' | hm'
      · left
        have h1 := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl hm'
          (by norm_num)).1
        rw [h2] at h1
        have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
        exact_mod_cast h1.trans e
      · right
        have h1 := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl hm'
          (by norm_num)).1
        rw [h2] at h1
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
        exact_mod_cast h1.trans e
    have : Finite (sesqUnitaryGroup B) := Nat.finite_of_card_ne_zero (by omega)
    have hsU : Group.IsSolvable ↥(sesqUnitaryGroup B) :=
      isSolvable_of_card_primeFactors_le_two (card_primeFactors_gu hcardU)
    have hsSU : Group.IsSolvable ↥(sesqSpecialUnitaryGroup B) :=
      Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (sesqSpecialUnitaryGroup_le B))
    exact Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective

theorem isQuasisimple_or_isSolvable_specialBlock (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) ∨ Group.IsSolvable ↥(specialBlock Q x h) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hself : h = reciprocalPolynomial h
  · exact isQuasisimple_or_isSolvable_specialBlock_selfDual hx hp hp2 hh hne1 hself hm
  · exact Or.inl (isQuasisimple_specialBlock_paired hx hp hp2 hh hne1 hself hm)

end Special

section SplitFour

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  LayerCores LayerFacts OmNonsplit
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

omit [CharP K 2] in
theorem splitFour_factors (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hsp : SplitFour R)
    (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    ∃ T₁ T₂ : Subgroup (W ≃ₗ[K] W),
      ⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆ =
        T₁ ⊔ T₂ ∧
      (∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆,
        ∀ t ∈ T₁, g * t * g⁻¹ ∈ T₁) ∧
      (∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆,
        ∀ t ∈ T₂, g * t * g⁻¹ ∈ T₂) ∧
      (∀ x ∈ T₁, ∀ y ∈ T₂, x * y = y * x) ∧
      CFSG.Assembly.IsComponentOf T₁ (TauCeti.QuadraticMap.orthogonalGroup R) ∧
      CFSG.Assembly.IsComponentOf T₂ (TauCeti.QuadraticMap.orthogonalGroup R) ∧
      (∃ ψ : SL(2, K) →* (W ≃ₗ[K] W), Function.Injective ψ ∧ ψ.range = T₁) ∧
      (∃ ψ : SL(2, K) →* (W ≃ₗ[K] W), Function.Injective ψ ∧ ψ.range = T₂) ∧
      ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup R, Odd (orderOf g) →
        g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆ := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  set O := TauCeti.QuadraticMap.orthogonalGroup R with hO
  obtain ⟨-, e, -, -, hsup, hq₁, hq₂, hn₁, hn₂, hcomm, -, hsq⟩ :=
    orthogonal_split_four_derived hK2 hK3 R hR hsp.1 hsp.2
  have hinl : Function.Injective ((specialRho (K := K)).comp (MonoidHom.inl _ _)) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    have h := congrArg (fun g : DeterminantIsometries K =>
      g.val (1 : Matrix (Fin 2) (Fin 2) K)) hA
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at h
    rw [specialRho_apply] at h
    exact Subtype.ext (by simpa using h)
  have hinr : Function.Injective ((specialRho (K := K)).comp (MonoidHom.inr _ _)) := by
    rw [injective_iff_map_eq_one]
    intro B hB
    have h := congrArg (fun g : DeterminantIsometries K =>
      g.val (1 : Matrix (Fin 2) (Fin 2) K)) hB
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at h
    rw [specialRho_apply] at h
    have h1 : B⁻¹ = 1 := Subtype.ext (by simpa using h)
    rw [← inv_inv B, h1, inv_one]
  have hcn : ((commutator ↥O).subgroupOf (⊤ : Subgroup ↥O)).Normal :=
    (Subgroup.normal_subgroupOf_iff le_top).mpr fun x k hx _ =>
      (inferInstance : (commutator ↥O).Normal).conj_mem x hx k
  have hcomp : ∀ L : Subgroup ↥O, L ≤ commutator ↥O → (L.subgroupOf (commutator ↥O)).Normal →
      CFSG.IsQuasisimple L → CFSG.Assembly.IsComponentOf (L.map O.subtype) O := by
    intro L hLle hLn hLq
    refine ⟨Subgroup.map_subtype_le L, ?_, ?_⟩
    · have h1 : CFSG.Assembly.IsSubnormal L ⊤ := CFSG.Assembly.IsSubnormal.step hLle hLn
        (CFSG.Assembly.IsSubnormal.step le_top hcn (CFSG.Assembly.IsSubnormal.refl ⊤))
      have h2 := ggSubnormal_map O.subtype h1
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (L.equivMapOfInjective _ O.subtype_injective) hLq)
  set F₁ := (determinantLeftFactor K).map e.symm.toMonoidHom with hF₁
  set F₂ := (determinantRightFactor K).map e.symm.toMonoidHom with hF₂
  have hle₁ : F₁ ≤ commutator ↥O := by rw [hsup]; exact le_sup_left
  have hle₂ : F₂ ≤ commutator ↥O := by rw [hsup]; exact le_sup_right
  have hcomm' : ⁅O, O⁆ = (commutator ↥O).map O.subtype := (Subgroup.map_subtype_commutator O).symm
  have hnorm : ∀ F : Subgroup ↥O, F ≤ commutator ↥O → (F.subgroupOf (commutator ↥O)).Normal →
      ∀ g ∈ ⁅O, O⁆, ∀ t ∈ F.map O.subtype, g * t * g⁻¹ ∈ F.map O.subtype := by
    intro F hFle hFn g hg t ht
    rw [hcomm'] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    obtain ⟨t', ht', rfl⟩ := ht
    exact ⟨g' * t' * g'⁻¹, (Subgroup.normal_subgroupOf_iff hFle).mp hFn t' g' ht' hg', by simp⟩
  refine ⟨F₁.map O.subtype, F₂.map O.subtype, ?_, hnorm F₁ hle₁ hn₁, hnorm F₂ hle₂ hn₂, ?_,
    hcomp F₁ hle₁ hn₁ hq₁, hcomp F₂ hle₂ hn₂ hq₂,
    ⟨O.subtype.comp (e.symm.toMonoidHom.comp ((specialRho (K := K)).comp (MonoidHom.inl _ _))),
      O.subtype_injective.comp (e.symm.injective.comp hinl), ?_⟩,
    ⟨O.subtype.comp (e.symm.toMonoidHom.comp ((specialRho (K := K)).comp (MonoidHom.inr _ _))),
      O.subtype_injective.comp (e.symm.injective.comp hinr), ?_⟩, ?_⟩
  · rw [hcomm', hsup, Subgroup.map_sup]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hcomm x hx y hy)
  · rw [MonoidHom.range_comp, MonoidHom.range_comp, hF₁, determinantLeftFactor]
  · rw [MonoidHom.range_comp, MonoidHom.range_comp, hF₂, determinantRightFactor]
  · intro g hg hodd
    obtain ⟨k, hk⟩ := hodd
    set g' : ↥O := ⟨g, hg⟩ with hg'
    have hord : orderOf g' = orderOf g := Subgroup.orderOf_mk g hg
    have h1 : g' = (g' ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf g' + 1 by rw [hord, hk]; ring, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [hcomm']
    exact ⟨g', h1 ▸ Subgroup.pow_mem _ (hsq g') _, rfl⟩

theorem splitFour_conj_mem (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hsp : SplitFour R)
    {T : Subgroup (W ≃ₗ[K] W)} (hTq : CFSG.IsQuasisimple T)
    (hTs : CFSG.Assembly.IsSubnormal T (TauCeti.QuadraticMap.orthogonalGroup R))
    {g : W ≃ₗ[K] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup R) (hgo : Odd (orderOf g)) :
    ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
  have := finite_linearEquiv (K := K) (V := W)
  obtain ⟨-, ⟨hns, -⟩ | ⟨-, hK4, -⟩⟩ := structure_of_isSubnormal hR hTq hTs
  · exact absurd hsp hns
  obtain ⟨T₁, T₂, hsup, hn₁, hn₂, -, hc₁, hc₂, -, -, hodd⟩ :=
    splitFour_factors hR hsp (by omega) (by omega)
  have hTA : CFSG.Assembly.IsComponentOf T (TauCeti.QuadraticMap.orthogonalGroup R) :=
    ⟨ggSubnormal_le hTs, hTs,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hTq⟩
  have hgc := hodd g hg hgo
  rcases isComponentOf_eq_or_commute hTA hc₁ with h1 | h1
  · rw [h1]
    exact hn₁ g hgc
  rcases isComponentOf_eq_or_commute hTA hc₂ with h2 | h2
  · rw [h2]
    exact hn₂ g hgc
  exfalso
  have hTc : T ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup R,
      TauCeti.QuadraticMap.orthogonalGroup R⁆ := by
    rw [← ggCommutator_eq_of_isQuasisimple hTq]
    exact Subgroup.commutator_mono (ggSubnormal_le hTs) (ggSubnormal_le hTs)
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2
  have h5 : ⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆ ≤
      Subgroup.centralizer (T : Set (W ≃ₗ[K] W)) := by
    rw [hsup]
    exact sup_le h1 h2
  exact not_le_centralizer_self_of_isQuasisimple hTA.2.2 (hTc.trans h5)

end SplitFour

section Component

open CFSG.LocalAnalysis.ComponentInitial LayerCores LayerFacts OmNonsplit CFSG.RankThree.Classical2
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {a : V ≃ₗ[K] V}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem isComponentOf_isometryCentralizer {L : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L (orthDerived Q ⊓ Subgroup.centralizer {a})) :
    CFSG.Assembly.IsComponentOf L (isometryCentralizer Q a) := by
  obtain ⟨hle, hsn, hq⟩ := hL
  have hle' : orthDerived Q ⊓ Subgroup.centralizer {a} ≤ isometryCentralizer Q a :=
    inf_le_inf_right _ orthDerived_le_orthogonalGroup
  refine ⟨hle.trans hle', ggIsSubnormal_trans hsn (ggSubnormal_of_normal hle' ?_), hq⟩
  intro u hu s hs
  have hu1 : u ∈ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hu).2
  have hs1 : s ∈ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hs).2
  exact Subgroup.mem_inf.mpr ⟨LayerPDiv.conj_mem_commutator_self _ (Subgroup.mem_inf.mp hu).1
    (Subgroup.mem_inf.mp hs).1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hu1 hs1)
      (Subgroup.inv_mem _ hu1)⟩

omit [CharP K 2] in
theorem exists_le_supportedBlock (hx : OddOrderIsometry Q p a) {L : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L (isometryCentralizer Q a)) :
    ∃ h ∈ primaryFactors a.toLinearMap, L ≤ supportedBlock Q a h := by
  have := finite_linearEquiv (K := K) (V := V)
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  by_contra hno
  push Not at hno
  have hc : ∀ r ∈ Rep, supportedBlock Q a r ≤ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    intro r hr
    rcases CoordSL.le_or_commutator_eq_bot_of_normal hL (supportedBlock_le_isometryCentralizer r)
      ((Subgroup.normal_subgroupOf_iff (supportedBlock_le_isometryCentralizer r)).mpr
        fun f m hf hm => conj_mem_supportedBlock hm hf) with h1 | h1
    · exact absurd h1 (hno r (hRep.1 hr))
    · rw [Subgroup.commutator_comm] at h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hall : isometryCentralizer Q a ≤ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) :=
    (hx.isometryCentralizer_le hRep).trans (iSup₂_le hc)
  exact not_le_centralizer_self_of_isQuasisimple hL.2.2 (hL.1.trans hall)

@[expose] noncomputable def resFix (a : V ≃ₗ[K] V) :
    ↥(Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V))) →* (fixedSpace a ≃ₗ[K] fixedSpace a) where
  toFun c := restrictEquiv (fixedSpace a) c.1 (fun _ hw => mem_fixedSpace_of_apply c.2 hw)
    (fun _ hw => mem_fixedSpace_of_apply (symm_mem_centralizer a c.2) hw)
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem coe_resFix (c : ↥(Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)))) (w : fixedSpace a) :
    (resFix a c w : V) = c.1 w := rfl

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem resFix_mem {c : ↥(Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)))}
    (hc : c.1 ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    resFix a c ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace a).subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  show Q ((resFix a c w : fixedSpace a) : V) = Q (w : V)
  rw [coe_resFix]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hc _

@[expose] noncomputable def fixRho (hx : OddOrderIsometry Q p a) :
    ↥(supportedBlock Q a (X - 1)) →* (fixedSpace a ≃ₗ[K] fixedSpace a) :=
  (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace a).subtype)).subtype.comp
    (fixedBlockEquiv hx).toMonoidHom

omit [Finite K] [CharP K 2] in
theorem coe_fixRho (hx : OddOrderIsometry Q p a) (g : ↥(supportedBlock Q a (X - 1)))
    (w : fixedSpace a) : (fixRho hx g w : V) = g.1 w := rfl

omit [Finite K] [CharP K 2] in
theorem fixRho_eq_restrictFixed (hx : OddOrderIsometry Q p a) (g : ↥(supportedBlock Q a (X - 1))) :
    fixRho hx g = restrictFixed Q a g := rfl

omit [Finite K] [CharP K 2] in
theorem fixRho_injective (hx : OddOrderIsometry Q p a) : Function.Injective (fixRho hx) :=
  Subtype.val_injective.comp (fixedBlockEquiv hx).injective

omit [Finite K] [CharP K 2] in
theorem range_fixRho (hx : OddOrderIsometry Q p a) :
    (fixRho hx).range = TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace a).subtype) := by
  ext φ
  constructor
  · rintro ⟨g, rfl⟩
    exact (fixedBlockEquiv hx g).2
  · intro hφ
    refine ⟨(fixedBlockEquiv hx).symm ⟨φ, hφ⟩, ?_⟩
    change ((fixedBlockEquiv hx ((fixedBlockEquiv hx).symm ⟨φ, hφ⟩) :
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace a).subtype))) :
        fixedSpace a ≃ₗ[K] fixedSpace a) = φ
    rw [MulEquiv.apply_symm_apply]

omit [Finite K] [CharP K 2] in
theorem fixRho_conj (hx : OddOrderIsometry Q p a) {c : V ≃ₗ[K] V}
    (hc : c ∈ isometryCentralizer Q a) (g : ↥(supportedBlock Q a (X - 1))) :
    fixRho hx ⟨c * g.1 * c⁻¹, conj_mem_supportedBlock hc g.2⟩ =
      resFix a ⟨c, (Subgroup.mem_inf.mp hc).2⟩ * fixRho hx g *
        (resFix a ⟨c, (Subgroup.mem_inf.mp hc).2⟩)⁻¹ := by
  refine LinearEquiv.ext fun w => Subtype.ext ?_
  rw [← map_inv]
  change c (g.1 (c⁻¹ w)) = ((resFix a ⟨c, (Subgroup.mem_inf.mp hc).2⟩ ((fixRho hx g)
    (resFix a ⟨c, (Subgroup.mem_inf.mp hc).2⟩⁻¹ w)) : fixedSpace a) : V)
  rw [coe_resFix, coe_fixRho, coe_resFix]
  rfl

theorem fixed_case (hx : OddOrderIsometry Q p a) (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup (V ≃ₗ[K] V)} (hL : CFSG.Assembly.IsComponentOf L (isometryCentralizer Q a))
    (hLF : L ≤ supportedBlock Q a (X - 1)) :
    (∀ c ∈ isometryCentralizer Q a, c ^ p = 1 → ∀ g ∈ L, c * g * c⁻¹ ∈ L) ∧
      (finrank K (fixedSpace a) = 4 ∨
        ∀ u ∈ supportedBlock Q a (X - 1), u ^ p = 1 → u ∈ L) := by
  classical
  set F := supportedBlock Q a (X - 1) with hF
  set R := Q.comp (fixedSpace a).subtype with hR
  set OW := TauCeti.QuadraticMap.orthogonalGroup R with hOW
  have hRnd : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  set ρ := fixRho hx with hρ
  have hρinj : Function.Injective ρ := fixRho_injective hx
  set T := (L.subgroupOf F).map ρ with hT
  have hLq : CFSG.IsQuasisimple L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2
  have hTq : CFSG.IsQuasisimple T :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hLF).symm.trans
        ((L.subgroupOf F).equivMapOfInjective ρ hρinj)) hLq
  have hTs : CFSG.Assembly.IsSubnormal T OW := by
    have h1 : CFSG.Assembly.IsSubnormal L F :=
      ggSubnormal_mono hL.2.1 hLF (supportedBlock_le_isometryCentralizer _)
    have h2 := ggSubnormal_comap F.subtype h1
    rw [show F.comap F.subtype = ⊤ from Subgroup.subgroupOf_self F] at h2
    have h3 := ggSubnormal_map ρ h2
    rwa [← MonoidHom.range_eq_map, hρ, range_fixRho] at h3
  have hmemT : ∀ u (hu : u ∈ F), ρ ⟨u, hu⟩ ∈ T → u ∈ L := by
    intro u hu h
    obtain ⟨y, hy, hyu⟩ := h
    have := hρinj hyu
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  have hTmem : ∀ g (hg : g ∈ L), ρ ⟨g, hLF hg⟩ ∈ T := fun g hg =>
    ⟨⟨g, hLF hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hres : ∀ c (hc : c ∈ isometryCentralizer Q a),
      resFix a ⟨c, (Subgroup.mem_inf.mp hc).2⟩ ∈ OW :=
    fun c hc => resFix_mem (Subgroup.mem_inf.mp hc).1
  obtain ⟨h4, ⟨hns, hTc⟩ | ⟨hsp, -, -⟩⟩ := structure_of_isSubnormal hRnd hTq hTs
  · obtain ⟨-, hodd⟩ := LayerPDiv.isQuasisimple_commutator_of_not_split hRnd (by omega) hns
    refine ⟨fun c hc _ g hg => ?_, Or.inr fun u hu hup => hmemT u hu ?_⟩
    · have hcg : c * g * c⁻¹ ∈ F := conj_mem_supportedBlock hc (hLF hg)
      refine hmemT _ hcg ?_
      rw [show (⟨c * g * c⁻¹, hcg⟩ : ↥F) = ⟨c * (⟨g, hLF hg⟩ : ↥F).1 * c⁻¹,
          conj_mem_supportedBlock hc (hLF hg)⟩ from rfl, hρ, fixRho_conj hx hc, ← hρ, hTc]
      exact LayerPDiv.conj_mem_commutator_self OW (hres c hc) (hTc ▸ hTmem g hg)
    · rw [hTc]
      have hOW : ρ ⟨u, hu⟩ ∈ OW := (fixedBlockEquiv hx ⟨u, hu⟩).2
      have h1 : ρ ⟨u, hu⟩ ^ p = 1 := by
        rw [← map_pow]
        have : (⟨u, hu⟩ : ↥F) ^ p = 1 := Subtype.ext (by simpa using hup)
        rw [this, map_one]
      exact hodd _ hOW (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one h1))
  · refine ⟨fun c hc hcp g hg => ?_, Or.inl hsp.1⟩
    have hcg : c * g * c⁻¹ ∈ F := conj_mem_supportedBlock hc (hLF hg)
    refine hmemT _ hcg ?_
    rw [show (⟨c * g * c⁻¹, hcg⟩ : ↥F) = ⟨c * (⟨g, hLF hg⟩ : ↥F).1 * c⁻¹,
        conj_mem_supportedBlock hc (hLF hg)⟩ from rfl, hρ, fixRho_conj hx hc, ← hρ]
    have hrp : resFix a ⟨c, (Subgroup.mem_inf.mp hc).2⟩ ^ p = 1 := by
      rw [← map_pow]
      have : (⟨c, (Subgroup.mem_inf.mp hc).2⟩ : ↥(Subgroup.centralizer ({a} : Set _))) ^ p = 1 :=
        Subtype.ext (by simpa using hcp)
      rw [this, map_one]
    exact splitFour_conj_mem hRnd hsp hTq hTs (hres c hc)
      (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hrp)) _ (hTmem g hg)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem commutator_le_specialBlock (h : K[X]) :
    ⁅supportedBlock Q a h, supportedBlock Q a h⁆ ≤ specialBlock Q a h := by
  refine Subgroup.commutator_le.mpr fun g hg g' hg' => ?_
  have hmem : ⁅g, g'⁆ ∈ supportedBlock Q a h :=
    Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator hg hg')
  refine mem_specialBlock.mpr ⟨hmem, ?_⟩
  have he : (⟨⁅g, g'⁆, hmem⟩ : ↥(supportedBlock Q a h)) =
      ⁅(⟨g, hg⟩ : ↥(supportedBlock Q a h)), ⟨g', hg'⟩⁆ := rfl
  rw [he]
  have h2 : (blockDet Q a h).toHomUnits ⁅(⟨g, hg⟩ : ↥(supportedBlock Q a h)), ⟨g', hg'⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  have h3 := congrArg Units.val h2
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at h3

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem exists_pow_mul_pow_mem_specialBlock (hp : p.Prime) {h : K[X]} [Fact (Irreducible h)]
    {u v : V ≃ₗ[K] V} (hu : u ∈ supportedBlock Q a h) (hv : v ∈ supportedBlock Q a h)
    (hup : u ^ p = 1) (hvp : v ^ p = 1) :
    ∃ α γ : ℕ, α < p ∧ γ < p ∧ (α ≠ 0 ∨ γ ≠ 0) ∧ u ^ α * v ^ γ ∈ specialBlock Q a h := by
  set U : ↥(supportedBlock Q a h) := ⟨u, hu⟩ with hUdef
  set W : ↥(supportedBlock Q a h) := ⟨v, hv⟩ with hWdef
  have hU : U ^ p = 1 := Subtype.ext (by simpa [U] using hup)
  have hW : W ^ p = 1 := Subtype.ext (by simpa [W] using hvp)
  obtain ⟨α, γ, hα, hγ, hαγ, h1⟩ := SevSpNs.exists_pow_mul_pow_eq_one hp
    (z₁ := (blockDet Q a h).toHomUnits U) (z₂ := (blockDet Q a h).toHomUnits W)
    (by rw [← map_pow, hU, map_one]) (by rw [← map_pow, hW, map_one])
  refine ⟨α, γ, hα, hγ, hαγ, mem_specialBlock.mpr ⟨(U ^ α * W ^ γ).2, ?_⟩⟩
  have he : (⟨u ^ α * v ^ γ, (U ^ α * W ^ γ).2⟩ : ↥(supportedBlock Q a h)) =
      U ^ α * W ^ γ := rfl
  rw [he]
  have h2 := congrArg Units.val (show (blockDet Q a h).toHomUnits (U ^ α * W ^ γ) = 1 by
    rw [map_mul, map_pow, map_pow, h1])
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at h2

theorem free_case (hx : OddOrderIsometry Q p a) (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]}
    (hh : h ∈ primaryFactors a.toLinearMap) (hne1 : h ≠ X - 1) {L : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L (isometryCentralizer Q a))
    (hLF : L ≤ supportedBlock Q a h) : L = specialBlock Q a h := by
  have := finite_linearEquiv (K := K) (V := V)
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hLq : CFSG.IsQuasisimple L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2
  have hLP : L ≤ specialBlock Q a h := by
    rw [← ggCommutator_eq_of_isQuasisimple hLq]
    exact (Subgroup.commutator_mono hLF hLF).trans (commutator_le_specialBlock h)
  have hm : 2 ≤ primaryMultiplicity a.toLinearMap h := by
    by_contra hm
    have hpos : 1 ≤ primaryMultiplicity a.toLinearMap h := by
      have hne : primaryComponent a.toLinearMap h ≠ ⊥ :=
        primaryComponent_ne_bot hx.squarefree_minpoly hh
      have : Nontrivial (primaryComponent a.toLinearMap h) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne
      exact Module.finrank_pos
    have h1 := hx.specialBlock_eq_bot_of_finrank_eq_one hh (by omega)
    rw [h1] at hLP
    obtain ⟨u, u', huu⟩ := exists_mul_ne_of_isQuasisimple hLq
    have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.mp (hLP u.2))
    have hu' : u' = 1 := Subtype.ext (Subgroup.mem_bot.mp (hLP u'.2))
    exact huu (by rw [hu, hu'])
  rcases isQuasisimple_or_isSolvable_specialBlock hx hp hp2 hh hne1 hm with hq | hs
  · have hPc : CFSG.Assembly.IsComponentOf (specialBlock Q a h) (isometryCentralizer Q a) :=
      ⟨specialBlock_le_isometryCentralizer h,
        ggSubnormal_of_normal (specialBlock_le_isometryCentralizer h)
          (fun u hu s hs => conj_mem_specialBlock hu hs),
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq⟩
    rcases isComponentOf_eq_or_commute hL hPc with h1 | h1
    · exact h1
    · exfalso
      apply not_le_centralizer_self_of_isQuasisimple hL.2.2
      rw [Subgroup.commutator_comm] at h1
      exact hLP.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
  · exact (ClNonsplit.not_isQuasisimple_of_le hs hLP hLq).elim

theorem exists_block_of_isComponentOf (hx : OddOrderIsometry Q p a) (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L (orthDerived Q ⊓ Subgroup.centralizer {a})) :
    ∃ h : K[X], L ≤ supportedBlock Q a h ∧
      (∀ c ∈ isometryCentralizer Q a, c ^ p = 1 → ∀ g ∈ L, c * g * c⁻¹ ∈ L) ∧
      ((h = X - 1 ∧ finrank K (fixedSpace a) = 4) ∨
        ∀ u ∈ supportedBlock Q a h, ∀ v ∈ supportedBlock Q a h, u ^ p = 1 → v ^ p = 1 →
          ∃ α γ : ℕ, α < p ∧ γ < p ∧ (α ≠ 0 ∨ γ ≠ 0) ∧ u ^ α * v ^ γ ∈ L) := by
  have hL' := isComponentOf_isometryCentralizer hL
  obtain ⟨h, hh, hLF⟩ := exists_le_supportedBlock hx hL'
  by_cases hX : h = X - 1
  · subst hX
    obtain ⟨hn, hcase⟩ := fixed_case hx hp hp2 hL' hLF
    refine ⟨X - 1, hLF, hn, ?_⟩
    rcases hcase with h4 | hin
    · exact Or.inl ⟨rfl, h4⟩
    · refine Or.inr fun u hu v _ hup _ => ⟨1, 0, hp.one_lt, hp.pos, Or.inl one_ne_zero, ?_⟩
      rw [pow_one, pow_zero, mul_one]
      exact hin u hu hup
  · have hLeq := free_case hx hp hp2 hh hX hL' hLF
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    refine ⟨h, hLF, fun c hc _ g hg => ?_, Or.inr fun u hu v hv hup hvp => ?_⟩
    · rw [hLeq] at hg ⊢
      exact conj_mem_specialBlock hc hg
    · rw [hLeq]
      exact exists_pow_mul_pow_mem_specialBlock hp hu hv hup hvp

end Component

end SevOm

end CFSG.StandardType

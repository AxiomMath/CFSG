module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFix
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsFrame
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmBlock

public section

namespace CFSG.StandardType

namespace SevOm

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

section Indices

theorem exists_two_ne {r : ℕ} (hr : 4 ≤ r) (j j' : Fin r) :
    ∃ k k' : Fin r, k ≠ k' ∧ k ≠ j ∧ k ≠ j' ∧ k' ≠ j ∧ k' ≠ j' := by
  classical
  have hcard : 1 < (Finset.univ \ ({j, j'} : Finset (Fin r))).card := by
    have h1 : ({j, j'} : Finset (Fin r)).card ≤ 2 := Finset.card_le_two
    have h2 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin r)) {j, j'}
    have h3 : (Finset.univ ∩ ({j, j'} : Finset (Fin r))).card ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_right).trans h1
    rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  obtain ⟨k, hk, k', hk', hkk⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hk hk'
  exact ⟨k, k', hkk, hk.1, hk.2, hk'.1, hk'.2⟩

theorem exists_three_ne {r : ℕ} (hr : 4 ≤ r) (k : Fin r) :
    ∃ i₁ i₂ i₃ : Fin r, i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧ i₁ ≠ k ∧ i₂ ≠ k ∧ i₃ ≠ k := by
  obtain ⟨i₁, i₂, h12, h1k, -, h2k, -⟩ := exists_two_ne hr k k
  obtain ⟨i₃, i₄, h34, h31, h32, h41, h42⟩ := exists_two_ne hr i₁ i₂
  by_cases h3k : i₃ = k
  · exact ⟨i₁, i₂, i₄, h12, Ne.symm h41, Ne.symm h42, h1k, h2k, fun h => h34 (h3k.trans h.symm)⟩
  · exact ⟨i₁, i₂, i₃, h12, Ne.symm h31, Ne.symm h32, h1k, h2k, h3k⟩

end Indices

section Small

open CFSG.LocalAnalysis.ComponentInitial LayerCores LayerFacts OmNonsplit

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem Frame.fix_single (F : Frame Q p A r) [NeZero p] {t : Multiplicative (Fin r → ZMod p)}
    {j : Fin r} (hj : toAdd t j ≠ 0) {v : V} (hv : F.ι t v = v) :
    F.ι (ofAdd (Pi.single j 1)) v = v := by
  classical
  have : Fact (1 < p) := ⟨by
    have := NeZero.ne p
    by_contra h
    have hp1 : p = 1 := by omega
    subst hp1
    exact hj (Subsingleton.elim _ _)⟩
  refine (F.fix _ v).mpr fun i hi => ?_
  have hij : i = j := by
    by_contra h
    exact hi (by rw [toAdd_ofAdd, Pi.single_eq_of_ne h])
  subst hij
  exact (F.fix t v).mp hv i hj

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem Frame.single_ne_one (F : Frame Q p A r) [Fact p.Prime] (j : Fin r) :
    F.ι (ofAdd (Pi.single j 1)) ≠ 1 := by
  classical
  intro h
  have h1 : (ofAdd (Pi.single j (1 : ZMod p)) : Multiplicative (Fin r → ZMod p)) = 1 :=
    F.inj (h.trans (map_one F.ι).symm)
  have h2 := congrFun (congrArg toAdd h1) j
  rw [toAdd_ofAdd, Pi.single_eq_same, toAdd_one, Pi.zero_apply] at h2
  exact one_ne_zero h2

theorem exists_small_supp (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q) (F : Frame Q p A r)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (s₀ : Multiplicative (Fin r → ZMod p)) {L : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L (orthDerived Q ⊓ Subgroup.centralizer {F.ι s₀}))
    (hpL : p ∣ Nat.card L) :
    ∃ s, F.ι s ∈ L ∧ F.ι s ≠ 1 ∧ ∃ j j' : Fin r, ∀ i, toAdd s i ≠ 0 → i = j ∨ i = j' := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := finite_linearEquiv (K := K) (V := V)
  have hx := F.oddOrderIsometry hQ hp2 hp hAΩ s₀
  obtain ⟨h, hLF, hnorm, hcase⟩ := exists_block_of_isComponentOf hx hp hp2 hL
  have hAC : ∀ c ∈ A, c ∈ isometryCentralizer Q (F.ι s₀) := by
    intro c hc
    obtain ⟨t, rfl⟩ := F.exists_eq hc
    refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup (hAΩ hc),
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hApg : IsPGroup p A := fun c => by
    obtain ⟨t, ht⟩ := F.exists_eq c.2
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, ← ht, F.pow_p, Subgroup.coe_one])⟩
  obtain ⟨w, hwL, hw1, hwp, hwc⟩ := SevSpNs.exists_mem_inf_centralizer hp hApg
    (fun c hc g hg => hnorm c (hAC c hc) (by
      obtain ⟨t, rfl⟩ := F.exists_eq hc
      exact F.pow_p t) g hg) hpL
  have hwA : w ∈ A :=
    hmax w (Subgroup.mem_inf.mp (hL.1 hwL)).1 hwp fun c hc => (hwc c hc).symm
  obtain ⟨t, rfl⟩ := F.exists_eq hwA
  by_cases hsmall : ∃ j j' : Fin r, ∀ i, toAdd t i ≠ 0 → i = j ∨ i = j'
  · exact ⟨t, hwL, hw1, hsmall⟩
  push Not at hsmall
  have ht0 : ∃ j, toAdd t j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hw1
    have : t = 1 := toAdd.injective (funext hall)
    rw [this, map_one]
  obtain ⟨j, hj⟩ := ht0
  obtain ⟨j', hj', hj'1, -⟩ := hsmall j j
  obtain ⟨j'', hj'', hj''1, hj''2⟩ := hsmall j j'
  have hwfix : ∀ v ∈ othersSpace (F.ι s₀).toLinearMap h, F.ι t v = v :=
    (mem_supportedBlock.mp (hLF hwL)).2
  rcases hcase with ⟨rfl, h4⟩ | hprod
  ·
    exfalso
    have hU : ∀ i, toAdd t i ≠ 0 → F.U i ≤ fixedSpace (F.ι s₀) := by
      intro i hi
      by_cases hs : toAdd s₀ i = 0
      · exact F.le_fixedSpace hs
      · exfalso
        obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot i)
        refine hu0 (F.fpf t i hi u hu (hwfix u ?_))
        rw [← hx.suppPerp_fixedSpace]
        exact mem_suppPerp.mpr fun w hw => by
          rw [QuadraticMap.polar_comm]
          exact (F.fix s₀ w).mp (mem_fixedSpace.mp hw) i hs u hu
    have h6 := F.finrank_add_add_le (Ne.symm hj'1) (Ne.symm hj''1) (Ne.symm hj''2)
      (hU j hj) (hU j' hj') (hU j'' hj'')
    have := F.two_le_finrank j
    have := F.two_le_finrank j'
    have := F.two_le_finrank j''
    omega
  ·
    have hmemF : ∀ i, toAdd t i ≠ 0 →
        F.ι (ofAdd (Pi.single i 1)) ∈ supportedBlock Q (F.ι s₀) h := fun i hi =>
      mem_supportedBlock.mpr ⟨hAC _ (F.mem _), fun v hv => F.fix_single hi (hwfix v hv)⟩
    obtain ⟨α, γ, hα, hγ, hαγ, hmem⟩ := hprod _ (hmemF j hj) _ (hmemF j' hj')
      (F.pow_p _) (F.pow_p _)
    set s : Multiplicative (Fin r → ZMod p) :=
      ofAdd (Pi.single j (α : ZMod p) + Pi.single j' (γ : ZMod p)) with hs
    have hse : F.ι s = F.ι (ofAdd (Pi.single j 1)) ^ α * F.ι (ofAdd (Pi.single j' 1)) ^ γ := by
      rw [← MonoidHom.map_pow F.ι, ← MonoidHom.map_pow F.ι, ← MonoidHom.map_mul F.ι]
      congr 1
      apply toAdd.injective
      rw [hs, toAdd_ofAdd, toAdd_mul, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
      funext i
      rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hj'1.symm,
          Pi.single_eq_of_ne hj'1.symm]
        ring
      · by_cases hij' : i = j'
        · subst hij'
          rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij]
          ring
        · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij',
            Pi.single_eq_of_ne hij']
          ring
    refine ⟨s, hse ▸ hmem, fun h1 => ?_, j, j', fun i hi => ?_⟩
    · have hs1 : s = 1 := F.inj (h1.trans (map_one F.ι).symm)
      have h2 := congrFun (congrArg toAdd hs1) j
      have h3 := congrFun (congrArg toAdd hs1) j'
      simp only [hs, toAdd_ofAdd, toAdd_one, Pi.zero_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne' hj'1, Pi.single_eq_of_ne hj'1, add_zero, zero_add] at h2 h3
      rw [ZMod.natCast_eq_zero_iff] at h2 h3
      rcases hαγ with h | h
      · exact h (Nat.eq_zero_of_dvd_of_lt h2 hα)
      · exact h (Nat.eq_zero_of_dvd_of_lt h3 hγ)
    · by_contra hne
      push Not at hne
      apply hi
      simp only [hs, toAdd_ofAdd, Pi.add_apply, Pi.single_eq_of_ne hne.1,
        Pi.single_eq_of_ne hne.2, add_zero]

end Small

section Sixteen

open CFSG.LocalAnalysis.ComponentInitial LayerCores LayerFacts OmNonsplit
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [FiniteDimensional K V] in
theorem card_ne_three : Nat.card K ≠ 3 := by
  intro h3
  have : Fintype K := Fintype.ofFinite K
  have h0 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rw [Fintype.card_eq_nat_card, h3] at h0
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : (1 : K) = 0 := by linear_combination h0 - h2
  exact one_ne_zero h1

theorem sixteen_of_splitFour (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q) (F : Frame Q p A r) (hr : 4 ≤ r)
    {s : Multiplicative (Fin r → ZMod p)} {j j' : Fin r}
    (hs : ∀ i, toAdd s i ≠ 0 → i = j ∨ i = j')
    (hsp : SplitFour (Q.comp (fixedSpace (F.ι s)).subtype)) (hK : Nat.card K ≠ 2) :
    ∃ L₂ L₃ : Subgroup (V ≃ₗ[K] V),
      CFSG.Assembly.IsComponentOf L₂ (orthDerived Q ⊓ Subgroup.centralizer {F.ι s}) ∧
      CFSG.Assembly.IsComponentOf L₃ (orthDerived Q ⊓ Subgroup.centralizer {F.ι s}) ∧
      Nonempty (↥L₂ ≃* SL(2, K)) ∧ Nonempty (↥L₃ ≃* SL(2, K)) ∧
      ∃ e' ∈ L₂ ⊔ L₃, e' ∈ A ∧ e' ≠ 1 ∧ ∃ L₄ : Subgroup (V ≃ₗ[K] V),
        CFSG.Assembly.IsComponentOf L₄ (orthDerived Q ⊓ Subgroup.centralizer {e'}) ∧
        Nat.card (A ⊓ Subgroup.centralizer (L₄ : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set e := F.ι s with he
  have hx : OddOrderIsometry Q p e := F.oddOrderIsometry hQ hp2 hp hAΩ s
  set W := fixedSpace e with hW
  have hR : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  obtain ⟨T₁, T₂, hsup, hn₁, hn₂, -, hc₁, hc₂, ⟨ψ₁, hψ₁, hr₁⟩, ⟨ψ₂, hψ₂, hr₂⟩, hodd⟩ :=
    splitFour_factors hR hsp hK card_ne_three
  set F₀ := supportedBlock Q e (X - 1) with hF₀
  set ρ := fixRho hx with hρ
  have hρinj : Function.Injective ρ := fixRho_injective hx
  set OW := TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) with hOW
  have hcO : ⁅OW, OW⁆ ≤ ρ.range := by
    rw [hρ, range_fixRho]
    exact Subgroup.commutator_le_self _
  have hT₁ : T₁ ≤ ρ.range := (hsup ▸ le_sup_left : T₁ ≤ ⁅OW, OW⁆).trans hcO
  have hT₂ : T₂ ≤ ρ.range := (hsup ▸ le_sup_right : T₂ ≤ ⁅OW, OW⁆).trans hcO
  set D := supportedFixedDerived Q e with hD
  have hDle : D ≤ orthDerived Q ⊓ Subgroup.centralizer {e} :=
    le_inf hx.supportedFixedDerived_le_orthDerived
      (supportedFixedDerived_le_isometryCentralizer.trans inf_le_right)
  have hDn : ∀ u ∈ orthDerived Q ⊓ Subgroup.centralizer {e}, ∀ g ∈ D, u * g * u⁻¹ ∈ D :=
    fun u hu g hg => hx.conj_mem_supportedFixedDerived (Subgroup.mem_inf.mpr
      ⟨orthDerived_le_orthogonalGroup (Subgroup.mem_inf.mp hu).1, (Subgroup.mem_inf.mp hu).2⟩) hg
  have hfac : ∀ T : Subgroup (W ≃ₗ[K] W), T ≤ ⁅OW, OW⁆ →
      (∀ g ∈ ⁅OW, OW⁆, ∀ t ∈ T, g * t * g⁻¹ ∈ T) →
      CFSG.Assembly.IsComponentOf T OW →
      CFSG.Assembly.IsComponentOf ((T.comap ρ).map F₀.subtype)
        (orthDerived Q ⊓ Subgroup.centralizer {e}) ∧
      Nonempty (↥((T.comap ρ).map F₀.subtype) ≃* ↥T) := by
    intro T hTc hTn hTcomp
    have hTr : T ≤ ρ.range := hTc.trans hcO
    have eT : ↥((T.comap ρ).map F₀.subtype) ≃* ↥T :=
      ((T.comap ρ).equivMapOfInjective F₀.subtype F₀.subtype_injective).symm.trans
        (((T.comap ρ).equivMapOfInjective ρ hρinj).trans
          (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hTr)))
    have hLD : (T.comap ρ).map F₀.subtype ≤ D := by
      rintro _ ⟨g, hg, rfl⟩
      have hg' : restrictFixed Q e g ∈ orthDerived (Q.comp W.subtype) := by
        rw [← fixRho_eq_restrictFixed hx]
        exact hTc hg
      exact mem_supportedFixedDerived.mpr ⟨g.2, hg'⟩
    have hLn : ∀ u ∈ D, ∀ g ∈ (T.comap ρ).map F₀.subtype,
        u * g * u⁻¹ ∈ (T.comap ρ).map F₀.subtype := by
      rintro u hu _ ⟨g, hg, rfl⟩
      obtain ⟨huF, hur⟩ := mem_supportedFixedDerived.mp hu
      have hur' : ρ ⟨u, huF⟩ ∈ ⁅OW, OW⁆ := by
        rw [hρ, fixRho_eq_restrictFixed hx]
        exact hur
      have hmem : (⟨u, huF⟩ : ↥F₀) * g * (⟨u, huF⟩ : ↥F₀)⁻¹ ∈ T.comap ρ := by
        rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
        exact hTn _ hur' _ hg
      refine ⟨_, hmem, ?_⟩
      rw [map_mul, map_mul, map_inv]
      rfl
    refine ⟨⟨hLD.trans hDle, ggIsSubnormal_trans (ggSubnormal_of_normal hLD hLn)
      (ggSubnormal_of_normal hDle hDn), ?_⟩, ⟨eT⟩⟩
    have hTq : CFSG.IsQuasisimple ↥T :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native T).1 hTcomp.2.2
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eT.symm hTq)
  obtain ⟨hL₁, ⟨e₁⟩⟩ := hfac T₁ (hsup ▸ le_sup_left) hn₁ hc₁
  obtain ⟨hL₂, ⟨e₂⟩⟩ := hfac T₂ (hsup ▸ le_sup_right) hn₂ hc₂
  have eψ : ∀ {T : Subgroup (W ≃ₗ[K] W)} {ψ : SL(2, K) →* (W ≃ₗ[K] W)},
      Function.Injective ψ → ψ.range = T → Nonempty (↥T ≃* SL(2, K)) := fun hψ hrg =>
    ⟨((MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrg)).symm⟩
  obtain ⟨f₁⟩ := eψ hψ₁ hr₁
  obtain ⟨f₂⟩ := eψ hψ₂ hr₂
  obtain ⟨k, k', -, hkj, hkj', -, -⟩ := exists_two_ne hr j j'
  have hsk : toAdd s k = 0 := by
    by_contra h0
    rcases hs k h0 with h | h
    · exact hkj h
    · exact hkj' h
  set e' := F.ι (ofAdd (Pi.single k 1)) with he'
  have he'A : e' ∈ A := F.mem _
  have he'C : e' ∈ isometryCentralizer Q e := by
    refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup (hAΩ he'A),
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [he', he, ← map_mul, ← map_mul, mul_comm]
  have he'F : e' ∈ F₀ := by
    refine mem_supportedBlock.mpr ⟨he'C, fun v hv => (F.fix _ v).mpr fun i hi u hu => ?_⟩
    have hik : i = k := by
      by_contra h
      exact hi (by rw [toAdd_ofAdd, Pi.single_eq_of_ne h])
    subst hik
    rw [← hx.suppPerp_fixedSpace] at hv
    exact mem_suppPerp.mp hv u (F.le_fixedSpace hsk hu)
  have hρe' : ρ ⟨e', he'F⟩ ∈ T₁ ⊔ T₂ := by
    rw [← hsup]
    refine hodd _ (fixedBlockEquiv hx ⟨e', he'F⟩).2 ?_
    have h1 : ρ ⟨e', he'F⟩ ^ p = 1 := by
      rw [← map_pow]
      have : (⟨e', he'F⟩ : ↥F₀) ^ p = 1 := Subtype.ext (by simpa using F.pow_p _)
      rw [this, map_one]
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one h1)
  have hmem : e' ∈ (T₁.comap ρ).map F₀.subtype ⊔ (T₂.comap ρ).map F₀.subtype := by
    rw [← Subgroup.map_sup]
    refine ⟨⟨e', he'F⟩, ?_, rfl⟩
    have hX : (T₁.comap ρ ⊔ T₂.comap ρ).map ρ = T₁ ⊔ T₂ := by
      rw [Subgroup.map_sup, Subgroup.map_comap_eq_self hT₁, Subgroup.map_comap_eq_self hT₂]
    rw [← hX] at hρe'
    obtain ⟨y, hy, hye⟩ := hρe'
    rw [← hρinj hye]
    exact hy
  refine ⟨_, _, hL₁, hL₂, ⟨e₁.trans f₁⟩, ⟨e₂.trans f₂⟩, e', hmem, he'A, F.single_ne_one k, ?_⟩
  obtain ⟨i₁, i₂, i₃, h12, h13, h23, h1k, h2k, h3k⟩ := exists_three_ne hr k
  have hU : ∀ i, i ≠ k → F.U i ≤ fixedSpace e' := fun i hik =>
    F.le_fixedSpace (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hik])
  have h6 := F.finrank_add_add_le h12 h13 h23 (hU i₁ h1k) (hU i₂ h2k) (hU i₃ h3k)
  have := F.two_le_finrank i₁
  have := F.two_le_finrank i₂
  have := F.two_le_finrank i₃
  exact direct_of_supp hQ hp hp2 hAΩ F (j := k) (j' := k) (fun i hi => by
      left
      by_contra h
      exact hi (by rw [toAdd_ofAdd, Pi.single_eq_of_ne h])) (by rw [← he']; omega)
    (fun h => by have := h.1; rw [← he'] at this; omega)

theorem exists_witness_orth (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q) (F : Frame Q p A r) (hr : 4 ≤ r)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (s₀ : Multiplicative (Fin r → ZMod p)) {L : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L (orthDerived Q ⊓ Subgroup.centralizer {F.ι s₀}))
    (hpL : p ∣ Nat.card L) :
    (∃ e ∈ L, e ∈ A ∧ e ≠ 1 ∧ ∃ L₂ : Subgroup (V ≃ₗ[K] V),
      CFSG.Assembly.IsComponentOf L₂ (orthDerived Q ⊓ Subgroup.centralizer {e}) ∧
      Nat.card (A ⊓ Subgroup.centralizer (L₂ : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p ^ 2) ∨
    (Nat.card K ≠ 2 ∧ ∃ e ∈ L, e ∈ A ∧ e ≠ 1 ∧ ∃ L₂ L₃ : Subgroup (V ≃ₗ[K] V),
      CFSG.Assembly.IsComponentOf L₂ (orthDerived Q ⊓ Subgroup.centralizer {e}) ∧
      CFSG.Assembly.IsComponentOf L₃ (orthDerived Q ⊓ Subgroup.centralizer {e}) ∧
      Nonempty (↥L₂ ≃* SL(2, K)) ∧ Nonempty (↥L₃ ≃* SL(2, K)) ∧
      ∃ e' ∈ L₂ ⊔ L₃, e' ∈ A ∧ e' ≠ 1 ∧ ∃ L₄ : Subgroup (V ≃ₗ[K] V),
        CFSG.Assembly.IsComponentOf L₄ (orthDerived Q ⊓ Subgroup.centralizer {e'}) ∧
        Nat.card (A ⊓ Subgroup.centralizer (L₄ : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p ^ 2) ∨
    (Nat.card K = 2 ∧ p = 3) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hsL, hs1, j, j', hs⟩ := exists_small_supp hQ hp hp2 hAΩ F hmax s₀ hL hpL
  obtain ⟨k, k', hkk, hkj, hkj', hk'j, hk'j'⟩ := exists_two_ne hr j j'
  have hz : ∀ i, i ≠ j → i ≠ j' → toAdd s i = 0 := fun i hij hij' => by
    by_contra h0
    rcases hs i h0 with h | h
    · exact hij h
    · exact hij' h
  have h4 := F.finrank_add_le hkk (F.le_fixedSpace (hz k hkj hkj'))
    (F.le_fixedSpace (hz k' hk'j hk'j'))
  have := F.two_le_finrank k
  have := F.two_le_finrank k'
  by_cases hsp : SplitFour (Q.comp (fixedSpace (F.ι s)).subtype)
  · by_cases hK : Nat.card K = 2
    · refine Or.inr (Or.inr ⟨hK, ?_⟩)
      have hk2 : finrank K (F.U k) = 2 := by
        have := hsp.1
        omega
      have h3 := F.dvd_card_sub_one k
      rw [Module.natCard_eq_pow_finrank (K := K), hK, hk2] at h3
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    · exact Or.inr (Or.inl ⟨hK, F.ι s, hsL, F.mem s, hs1,
        sixteen_of_splitFour hQ hp hp2 hAΩ F hr hs hsp hK⟩)
  · exact Or.inl ⟨F.ι s, hsL, F.mem s, hs1,
      direct_of_supp hQ hp hp2 hAΩ F hs (by omega) hsp⟩

end Sixteen

end SevOm

end CFSG.StandardType

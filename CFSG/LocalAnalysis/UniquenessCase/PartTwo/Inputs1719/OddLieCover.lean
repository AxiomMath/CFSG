module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieModelClosed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ReeMain
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LieType.HighestRoot.ModelCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)

theorem exists_cover_of_closed_fin_of_not_dvd {S X Q : Type} [Group S] [Finite S] [Group X]
    [Finite X] [Group Q] (ℓ : ℕ)
    (hclosed : ∀ (E : Type) [Group E] [Finite E] (π : E →* S), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ¬ ℓ ∣ Nat.card π.ker → ∃ σ : S →* E, ∀ g, π (σ g) = g)
    (hXp : commutator X = ⊤) (π : X →* Q) (hπ : Function.Surjective π)
    (hπc : π.ker ≤ Subgroup.center X) (hℓ : ¬ ℓ ∣ Nat.card π.ker)
    (ρ : S →* Q) (hρ : Function.Surjective ρ) (hρc : ρ.ker ≤ Subgroup.center S) :
    ∃ α : S →* X, Function.Surjective α ∧ α.ker ≤ Subgroup.center S ∧ ∀ s, π (α s) = ρ s := by
  classical
  let E : Subgroup (X × S) :=
    MonoidHom.eqLocus (π.comp (MonoidHom.fst X S)) (ρ.comp (MonoidHom.snd X S))
  let p : E →* S := (MonoidHom.snd X S).comp E.subtype
  have hp : Function.Surjective p := by
    intro s
    obtain ⟨x, hx⟩ := hπ (ρ s)
    exact ⟨⟨(x, s), hx⟩, rfl⟩
  have hpc : p.ker ≤ Subgroup.center E := by
    intro e he
    have hs : e.1.2 = 1 := he
    have hx : π e.1.1 = 1 := by
      have h : π e.1.1 = ρ e.1.2 := e.2
      rw [hs, map_one] at h
      exact h
    have hxc : e.1.1 ∈ Subgroup.center X := hπc hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.1 hxc g.1.1
    · simp [hs]
  have hmem1 : ∀ e : p.ker, ((e : E) : X × S).1 ∈ π.ker := by
    intro e
    have hs : ((e : E) : X × S).2 = 1 := e.2
    have h : π ((e : E) : X × S).1 = ρ ((e : E) : X × S).2 := (e : E).2
    rw [MonoidHom.mem_ker, h, hs, map_one]
  have hmem2 : ∀ x : π.ker, (((x : X), (1 : S)) : X × S) ∈ E := by
    intro x
    show π (x : X) = ρ 1
    rw [MonoidHom.mem_ker.mp x.2, map_one]
  let eqv : p.ker ≃ π.ker :=
    { toFun := fun e => ⟨_, hmem1 e⟩
      invFun := fun x => ⟨⟨_, hmem2 x⟩, rfl⟩
      left_inv := fun e => by
        have hs : ((e : E) : X × S).2 = 1 := e.2
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext rfl hs.symm
      right_inv := fun x => rfl }
  have hcard : Nat.card p.ker = Nat.card π.ker := Nat.card_congr eqv
  obtain ⟨σ, hσ⟩ := hclosed E p hp hpc (by rw [hcard]; exact hℓ)
  let α : S →* X := (MonoidHom.fst X S).comp (E.subtype.comp σ)
  have hαπ : ∀ s, π (α s) = ρ s := by
    intro s
    have h : π ((σ s : E) : X × S).1 = ρ ((σ s : E) : X × S).2 := (σ s).2
    have h2 : ((σ s : E) : X × S).2 = s := hσ s
    rw [h2] at h
    exact h
  refine ⟨α, ?_, ?_, hαπ⟩
  · have hcomm : ∀ x₁ x₂ : X, ⁅x₁, x₂⁆ ∈ α.range := by
      intro x₁ x₂
      obtain ⟨s₁, hs₁⟩ := hρ (π x₁)
      obtain ⟨s₂, hs₂⟩ := hρ (π x₂)
      have hz₁ : (α s₁)⁻¹ * x₁ ∈ Subgroup.center X := by
        apply hπc
        rw [MonoidHom.mem_ker, map_mul, map_inv, hαπ, hs₁]
        exact inv_mul_cancel _
      have hz₂ : (α s₂)⁻¹ * x₂ ∈ Subgroup.center X := by
        apply hπc
        rw [MonoidHom.mem_ker, map_mul, map_inv, hαπ, hs₂]
        exact inv_mul_cancel _
      have e₁ : x₁ = α s₁ * ((α s₁)⁻¹ * x₁) := by group
      have e₂ : x₂ = α s₂ * ((α s₂)⁻¹ * x₂) := by group
      set z₁ := (α s₁)⁻¹ * x₁ with hz₁def
      set z₂ := (α s₂)⁻¹ * x₂ with hz₂def
      have c₁ : ∀ g : X, g * z₁ = z₁ * g := Subgroup.mem_center_iff.1 hz₁
      have c₂ : ∀ g : X, g * z₂ = z₂ * g := Subgroup.mem_center_iff.1 hz₂
      have key : ⁅x₁, x₂⁆ = ⁅α s₁, α s₂⁆ := by
        rw [e₁, e₂]
        exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_comm_mul_central _ _ _ _ c₁ c₂
      rw [key]
      exact ⟨⁅s₁, s₂⁆, by simp [map_commutatorElement]⟩
    have hle : commutator X ≤ α.range := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_le.2 fun x₁ _ x₂ _ => hcomm x₁ x₂
    intro x
    have h := hle
    rw [hXp] at h
    exact h (Subgroup.mem_top x)
  · intro s hs
    have : ρ s = 1 := by
      rw [← hαπ]
      have : α s = 1 := hs
      rw [this, map_one]
    exact hρc this

theorem not_dvd_card_center_of_cover {U X : Type} [Group U] [Finite U] [Group X] [Finite X]
    [Group.IsPerfect U] {r : ℕ} [hr : Fact r.Prime]
    (hU : ∀ z ∈ Subgroup.center U, z ^ r = 1 → z = 1)
    (ψ : U →* X) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center U) :
    ¬ r ∣ Nat.card (Subgroup.center X) := by
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) r hdvd
  have hmap := CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel ψ hψ hker
  have hzU : (z : X) ∈ (Subgroup.center U).map ψ := by rw [hmap]; exact z.2
  obtain ⟨u, hu, hux⟩ := hzU
  have hzo : orderOf (z : X) = r := by rw [Subgroup.orderOf_coe]; exact hz
  obtain ⟨k, hk⟩ : r ∣ orderOf u := by
    rw [← hzo, ← hux]
    exact orderOf_map_dvd ψ u
  have hw : u ^ k ∈ Subgroup.center U := Subgroup.pow_mem _ hu k
  have hwr : (u ^ k) ^ r = 1 := by rw [← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  have hdk : orderOf u ∣ k := orderOf_dvd_of_pow_eq_one (hU _ hw hwr)
  have hpos : 0 < orderOf u := orderOf_pos u
  rw [hk] at hdk hpos
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hle := Nat.le_of_dvd hk0 hdk
  have h2 := hr.out.two_le
  nlinarith

open CFSG.LieType.RootSystem in
theorem exists_isLongestRoot {K : Type} [Group K] (D : CFSG.LieType.Universal.UniversalRootDatum K)
    (hD : 0 < D.rank) : ∃ γ, CFSG.ClassicalInvolution.Generic.IsLongestRoot D γ := by
  obtain ⟨γ, hγ, hmax⟩ := Set.exists_max_image D.roots
    (fun γ => form D.isFiniteType (toRat γ) (toRat γ)) (finite_roots D.isFiniteType D.divisible)
    ⟨_, (isCTRootSystem D.isFiniteType D.divisible).single_mem ⟨0, hD⟩⟩
  exact ⟨γ, hγ, hmax⟩

section Ree

open CFSG.Blueprint
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsReeOver17)


theorem isFundTag_of_not_ree {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n r f q : ℕ}
    (hr2 : r ≠ 2) (hadm : StatedLieAdmissible t n r f) (hq : q = r ^ f)
    (hqs : CFSG.Open.IsQuasisimple X) (hX : LieModel (X ⧸ Subgroup.center X) t n r f)
    (hRee : ¬ IsReeOver17 X q) : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
  cases t
  case twistedB2 => exact absurd hadm.2.2.2.1 hr2
  case twistedF4 => exact absurd hadm.2.2.2.1 hr2
  case Tits => exact absurd hadm.2.2.2.1 hr2
  case twistedG2 =>
    exfalso
    obtain ⟨-, hf1, rfl, rfl, ⟨k, rfl⟩, -⟩ := hadm
    have hZ : Subgroup.center X = ⊥ := Subgroup.card_eq_one.mp
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.ree_card_center_eq_one
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).mp hqs)
        ⟨_, hf1, hX⟩)
    exact hRee ⟨k, hq, LieModel.of_quotient_center hZ hX⟩
  all_goals trivial

end Ree

section Cover


theorem exists_cover_of_lieModel {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {n r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n r f) (hqs : CFSG.Open.IsQuasisimple X)
    (hX : LieModel (X ⧸ Subgroup.center X) t n r f)
    (hcl : (5 ≤ r ^ f ∧ ¬ (t = .PSL ∧ n = 2)) ∨
      (r = 3 ∧ f = 1 ∧ ¬ 3 ∣ Nat.card (Subgroup.center X))) :
    ∃ ψ : (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).K →* X,
      Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).K := by
  classical
  set U := CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr with hU
  have : Finite U.K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 hr
      (CFSG.ClassicalInvolution.Asc77.ih8_isFundTag_mf hfund) hadm
  obtain ⟨-, hUm⟩ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n r f hr hfund hadm
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.Upgrade.lieModel_unique hr2 hfund hUm hX
  let ρ : U.K →* X ⧸ Subgroup.center X :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center U.K))
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρc : ρ.ker ≤ Subgroup.center U.K := by
    intro k hk
    have h1 : e (QuotientGroup.mk' (Subgroup.center U.K) k) = 1 := hk
    rw [map_eq_one_iff _ e.injective] at h1
    exact (QuotientGroup.eq_one_iff k).1 h1
  have hπc : (QuotientGroup.mk' (Subgroup.center X)).ker ≤ Subgroup.center X := by
    rw [QuotientGroup.ker_mk']
  rcases hcl with ⟨hq5, hA1⟩ | ⟨rfl, rfl, h3⟩
  · obtain ⟨α, hαs, hαk, -⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_cover_of_closed_fin
        (fun E _ _ π hπ hcen => modelUniv_closed hr hr2 hfund hadm hq5 hA1 E π hπ hcen)
        hqs.1 (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _) hπc
        ρ hρ hρc
    exact ⟨α, hαs, hαk⟩
  · obtain ⟨α, hαs, hαk, -⟩ :=
      exists_cover_of_closed_fin_of_not_dvd 3
        (fun E _ _ π hπ hcen h3' => modelUniv_closed_three hfund hadm E π hπ hcen h3')
        hqs.1 (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _) hπc
        (by rw [QuotientGroup.ker_mk']; exact h3) ρ hρ hρc
    exact ⟨α, hαs, hαk⟩

theorem exists_cover_of_lieModel_three_full {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {n : ℕ} (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hqs : CFSG.Open.IsQuasisimple X)
    (hX : LieModel (X ⧸ Subgroup.center X) t n 3 1) (hex : ¬ IsSmallThreeTag t n) :
    ∃ ψ : (CFSG.ClassicalInvolution.Generic.modelUniv t n 3 1 Nat.prime_three).K →* X,
      Function.Surjective ψ ∧ ψ.ker ≤
        Subgroup.center (CFSG.ClassicalInvolution.Generic.modelUniv t n 3 1 Nat.prime_three).K := by
  classical
  set U := CFSG.ClassicalInvolution.Generic.modelUniv t n 3 1 Nat.prime_three with hU
  have : Finite U.K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three
      (CFSG.ClassicalInvolution.Asc77.ih8_isFundTag_mf hfund) hadm
  obtain ⟨-, hUm⟩ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n 3 1 Nat.prime_three
    hfund hadm
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.Upgrade.lieModel_unique (by norm_num) hfund hUm hX
  let ρ : U.K →* X ⧸ Subgroup.center X :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center U.K))
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρc : ρ.ker ≤ Subgroup.center U.K := by
    intro k hk
    have h1 : e (QuotientGroup.mk' (Subgroup.center U.K) k) = 1 := hk
    rw [map_eq_one_iff _ e.injective] at h1
    exact (QuotientGroup.eq_one_iff k).1 h1
  have hπc : (QuotientGroup.mk' (Subgroup.center X)).ker ≤ Subgroup.center X := by
    rw [QuotientGroup.ker_mk']
  obtain ⟨α, hαs, hαk, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_cover_of_closed_fin
      (fun E _ _ π hπ hcen => modelUniv_closed_three_full hfund hadm hex E π hπ hcen)
      hqs.1 (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _) hπc
      ρ hρ hρc
  exact ⟨α, hαs, hαk⟩

theorem not_dvd_card_center_of_lieModel {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {n r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n r f) (hqs : CFSG.Open.IsQuasisimple X)
    (hX : LieModel (X ⧸ Subgroup.center X) t n r f)
    (hcl : (5 ≤ r ^ f ∧ ¬ (t = .PSL ∧ n = 2)) ∨ (r = 3 ∧ f = 1 ∧ ¬ IsSmallThreeTag t n)) :
    ¬ r ∣ Nat.card (Subgroup.center X) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ψ, hψs, hψk⟩ : ∃ ψ : (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).K →* X,
      Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).K := by
    rcases hcl with h | ⟨rfl, rfl, hex⟩
    · exact exists_cover_of_lieModel hr hr2 hfund hadm hqs hX (Or.inl h)
    · exact exists_cover_of_lieModel_three_full hfund hadm hqs hX hex
  have : Finite (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 hr
      (CFSG.ClassicalInvolution.Asc77.ih8_isFundTag_mf hfund) hadm
  have hUq := (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n r f hr hfund hadm).1
  have : Group.IsPerfect (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).K := ⟨hUq.1⟩
  exact not_dvd_card_center_of_cover
    (fun z hz hzr => CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t n r f hr hr2
      hfund hadm z hz hzr) ψ hψs hψk

end Cover

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie

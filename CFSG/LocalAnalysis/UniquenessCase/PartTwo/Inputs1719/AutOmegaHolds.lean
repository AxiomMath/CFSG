module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AutOmegaThreeL2Square
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.OutL2U3Product
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3ProdAut
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
public import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
public import CFSG.LieType.ChevTwo.OppCl.SmallGlue
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.GroupTheory

theorem commute_of_pow_three_aut_l2 {S : Type} [Group S] [Finite S] {n : ℕ}
    (hS : IsL2 S n) (R : Subgroup (MulAut S)) (hR : IsPGroup 3 R) {α β : MulAut S}
    (hα : α ∈ R) (hβ : β ∈ R) (hα3 : α ^ 3 = 1) (hβ3 : β ^ 3 = 1) : α * β = β * α := by
  have hEv := (P22fin.isL2Ev_of_isL2 hS).1
  have hcyc : ∀ P : Sylow 3 S, IsCyclic (P : Subgroup S) := fun P =>
    P22y.isCyclic_of_isPGroup_of_isL2Ev hEv Nat.prime_three (by norm_num) P P.isPGroup'
  have := P22y.isCyclic_outer_of_isL2Ev hEv
  refine CFSG.RankThree.PartTwo.KFacts.commute_of_pow_three_eq_one_of_isPGroup hcyc hR ?_ hα hβ
    hα3 hβ3
  intro σ _ τ _ hσ hτ hσI
  set π := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S) with hπ
  have hσ1 : π σ ≠ 1 := fun h => hσI ((QuotientGroup.eq_one_iff σ).mp h)
  have hσ3 : π σ ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
  have hτ3 : π τ ^ 3 = 1 := by rw [← map_pow, hτ, map_one]
  have hzp : π τ ∈ Subgroup.zpowers (π σ) := by
    by_cases hτ1 : π τ = 1
    · rw [hτ1]
      exact one_mem _
    · have h : Subgroup.zpowers (π τ) = Subgroup.zpowers (π σ) := by
        rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
          orderOf_eq_prime hτ3 hτ1, orderOf_eq_prime hσ3 hσ1]
      rw [← h]
      exact Subgroup.mem_zpowers _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzp
  have hnn : (0 : ℤ) ≤ (-j) % 3 := Int.emod_nonneg _ (by norm_num)
  refine ⟨((-j) % 3).toNat, ?_⟩
  have hord : orderOf (π σ) = 3 := orderOf_eq_prime hσ3 hσ1
  have h1 : π (σ ^ ((-j) % 3).toNat * τ) = 1 := by
    rw [map_mul, map_pow, ← hj, ← zpow_natCast, ← zpow_add, Int.toNat_of_nonneg hnn]
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hord]
    push_cast
    omega
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem k_19_13_autOmega_holds : K_19_13_autOmega := by
  unfold K_19_13_autOmega
  intro X _ _ n hn _ hshape Q hQ α hα β hβ hα3 hβ3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hshape with hsq | ⟨hu3, hpow⟩
  ·
    obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := hsq
    letI : Group A := gA
    letI : Group B := gB
    have : Finite (A × B) := Finite.of_equiv X e.toEquiv
    have : Finite A := Finite.of_injective (fun a : A => (a, (1 : B)))
      (fun _ _ h => by simpa using h)
    have : Finite B := Finite.of_injective (fun b : B => ((1 : A), b))
      (fun _ _ h => by simpa using h)
    obtain ⟨eA⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2Model_of_lieModel hA
    obtain ⟨eB⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2Model_of_lieModel hB
    let eAB : B ≃* A := eB.trans eA.symm
    let e' : X ≃* A × A := e.trans (MulEquiv.prodCongr (MulEquiv.refl A) eAB)
    have : IsSimpleGroup A :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
    have hZ : Subgroup.center A = ⊥ := S17.center_eq_bot_of_lieModel_psl2 hA
    have hsimple : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤ := fun N hN => by
      have := hN
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
    have hcentral : ∀ a : A, (∀ c : A, a * c = c * a) → a = 1 := by
      intro a ha
      have : a ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr (fun c => (ha c).symm)
      rwa [hZ, Subgroup.mem_bot] at this
    have hnt : ∃ s : A, s ≠ 1 := exists_ne 1
    let κ : MulAut X ≃* MulAut (A × A) := MulAut.congr e'
    let Q' : Subgroup (MulAut (A × A)) := Q.map κ.toMonoidHom
    have hQ' : IsPGroup 3 Q' := hQ.map κ.toMonoidHom
    let R : Subgroup (MulAut A × MulAut A) := Q'.comap (mulAutProdHom A A)
    let R₁ : Subgroup (MulAut A) := R.map (MonoidHom.fst (MulAut A) (MulAut A))
    let R₂ : Subgroup (MulAut A) := R.map (MonoidHom.snd (MulAut A) (MulAut A))
    have hR : IsPGroup 3 R := hQ'.comap_of_injective _ (mulAutProdHom_injective A A)
    have hR₁ : IsPGroup 3 R₁ := hR.map _
    have hR₂ : IsPGroup 3 R₂ := hR.map _
    have hpres : ∀ γ ∈ Q', (∀ x : A, (γ (x, 1)).2 = 1) ∧
        ∀ x : A, (γ (1, x)).1 = 1 := by
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hγ
      have hodd : Odd (orderOf δ) :=
        CFSG.LieType.ChevTwo.OppCl.odd_orderOf_of_mem_isPGroup
          Nat.prime_three (by norm_num) hQ hδ
      have hSC : CFSG.ComponentClassification.AutL2Facts.SimpleCentreless A :=
        ⟨hsimple, hcentral, hnt⟩
      have h1 := hSC.presFst_of_odd (φ := κ δ) (by rwa [MulEquiv.orderOf_eq])
      exact ⟨h1, hSC.snd_of_fst h1⟩
    let α' : MulAut (A × A) := κ α
    let β' : MulAut (A × A) := κ β
    have hα'Q' : α' ∈ Q' := Subgroup.mem_map.mpr ⟨α, hα, rfl⟩
    have hβ'Q' : β' ∈ Q' := Subgroup.mem_map.mpr ⟨β, hβ, rfl⟩
    obtain ⟨f₁, f₂, hf⟩ :=
      CFSG.EvenSporadicStandard.M24Std.ProdAut.exists_prod_preserve α'
        (hpres α' hα'Q').1 (hpres α' hα'Q').2
    obtain ⟨g₁, g₂, hg⟩ :=
      CFSG.EvenSporadicStandard.M24Std.ProdAut.exists_prod_preserve β'
        (hpres β' hβ'Q').1 (hpres β' hβ'Q').2
    have hα'3 : α' ^ 3 = 1 := by
      change (κ α) ^ 3 = 1
      rw [← map_pow, hα3, map_one]
    have hβ'3 : β' ^ 3 = 1 := by
      change (κ β) ^ 3 = 1
      rw [← map_pow, hβ3, map_one]
    have hf₁3 : f₁ ^ 3 = 1 := MulEquiv.ext fun a => by
      have := congrArg (fun γ : MulAut (A × A) => (γ (a, 1)).1) hα'3
      simpa [CFSG.EvenSporadicStandard.Fin76b.pow_apply_pres hf] using this
    have hf₂3 : f₂ ^ 3 = 1 := MulEquiv.ext fun b => by
      have := congrArg (fun γ : MulAut (A × A) => (γ (1, b)).2) hα'3
      simpa [CFSG.EvenSporadicStandard.Fin76b.pow_apply_pres hf] using this
    have hg₁3 : g₁ ^ 3 = 1 := MulEquiv.ext fun a => by
      have := congrArg (fun γ : MulAut (A × A) => (γ (a, 1)).1) hβ'3
      simpa [CFSG.EvenSporadicStandard.Fin76b.pow_apply_pres hg] using this
    have hg₂3 : g₂ ^ 3 = 1 := MulEquiv.ext fun b => by
      have := congrArg (fun γ : MulAut (A × A) => (γ (1, b)).2) hβ'3
      simpa [CFSG.EvenSporadicStandard.Fin76b.pow_apply_pres hg] using this
    have hf₁mem : f₁ ∈ R₁ := by
      have hmul : mulAutProdHom A A (f₁, f₂) = α' := by
        apply MulEquiv.ext
        rintro ⟨a, b⟩
        rw [mulAutProdHom_apply, hf a b]
      refine Subgroup.mem_map.mpr ⟨(f₁, f₂), ?_, rfl⟩
      rw [Subgroup.mem_comap, hmul]
      exact hα'Q'
    have hf₂mem : f₂ ∈ R₂ := by
      have hmul : mulAutProdHom A A (f₁, f₂) = α' := by
        apply MulEquiv.ext
        rintro ⟨a, b⟩
        rw [mulAutProdHom_apply, hf a b]
      refine Subgroup.mem_map.mpr ⟨(f₁, f₂), ?_, rfl⟩
      rw [Subgroup.mem_comap, hmul]
      exact hα'Q'
    have hg₁mem : g₁ ∈ R₁ := by
      have hmul : mulAutProdHom A A (g₁, g₂) = β' := by
        apply MulEquiv.ext
        rintro ⟨a, b⟩
        rw [mulAutProdHom_apply, hg a b]
      refine Subgroup.mem_map.mpr ⟨(g₁, g₂), ?_, rfl⟩
      rw [Subgroup.mem_comap, hmul]
      exact hβ'Q'
    have hg₂mem : g₂ ∈ R₂ := by
      have hmul : mulAutProdHom A A (g₁, g₂) = β' := by
        apply MulEquiv.ext
        rintro ⟨a, b⟩
        rw [mulAutProdHom_apply, hg a b]
      refine Subgroup.mem_map.mpr ⟨(g₁, g₂), ?_, rfl⟩
      rw [Subgroup.mem_comap, hmul]
      exact hβ'Q'
    have hcomm₁ : f₁ * g₁ = g₁ * f₁ :=
      commute_of_pow_three_aut_l2 hA R₁ hR₁ hf₁mem hg₁mem hf₁3 hg₁3
    have hcomm₂ : f₂ * g₂ = g₂ * f₂ :=
      commute_of_pow_three_aut_l2 hA R₂ hR₂ hf₂mem hg₂mem hf₂3 hg₂3
    have hα'β' : α' * β' = β' * α' := by
      apply MulEquiv.ext
      rintro ⟨a, b⟩
      have hc₁ : ∀ a, f₁ (g₁ a) = g₁ (f₁ a) := fun a =>
        congrArg (fun γ : MulAut A => γ a) hcomm₁
      have hc₂ : ∀ b, f₂ (g₂ b) = g₂ (f₂ b) := fun b =>
        congrArg (fun γ : MulAut A => γ b) hcomm₂
      simp only [MulAut.mul_apply, hf, hg, hc₁, hc₂]
    have hαβ : κ (α * β) = κ (β * α) := by
      rw [map_mul, map_mul]
      exact hα'β'
    exact κ.injective hαβ
  ·
    obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := hu3
    letI : Group A := gA
    letI : Group B := gB
    have : Finite (A × B) := Finite.of_equiv X e.toEquiv
    have : Finite A := Finite.of_injective (fun a : A => (a, (1 : B)))
      (fun _ _ h => by simpa using h)
    have : Finite B := Finite.of_injective (fun b : B => ((1 : A), b))
      (fun _ _ h => by simpa using h)
    have hOut : IsPGroup 2 (Outer X) :=
      S17.k_OutL2U3Product_holds X n (by omega) hpow
        (Or.inr ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩)
    have hZ : Subgroup.center X = ⊥ :=
      center_eq_bot_of_isL2Square_or_isL2U3Product
        (Or.inr ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩)
    have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
      P22y.conj_injective_of_center_eq_bot hZ
    let InnX : Subgroup (MulAut X) :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner X
    have hQle : Q ≤ (MulAut.conj : X →* MulAut X).range := by
      have hmap : Q.map (QuotientGroup.mk' InnX) = ⊥ := by
        have hdisj := IsPGroup.disjoint_of_ne 3 2 (by norm_num)
          (Q.map (QuotientGroup.mk' InnX)) (⊤ : Subgroup (Outer X))
          (hQ.map _) (hOut.to_subgroup ⊤)
        exact disjoint_top.mp hdisj
      intro a ha
      have hmem : QuotientGroup.mk' InnX a ∈ Q.map (QuotientGroup.mk' InnX) := ⟨a, ha, rfl⟩
      rw [hmap] at hmem
      have h1 : a ∈ (QuotientGroup.mk' InnX).ker :=
        MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hmem)
      rw [QuotientGroup.ker_mk'] at h1
      exact h1
    let Q' : Subgroup X := Q.comap (MulAut.conj : X →* MulAut X)
    have hQ' : IsPGroup 3 Q' := hQ.comap_of_injective _ hinj
    obtain ⟨x, hx⟩ : ∃ x : X, MulAut.conj x = α := MonoidHom.mem_range.mp (hQle hα)
    obtain ⟨y, hy⟩ : ∃ y : X, MulAut.conj y = β := MonoidHom.mem_range.mp (hQle hβ)
    have hxQ' : x ∈ Q' := by
      rw [Subgroup.mem_comap, hx]
      exact hα
    have hyQ' : y ∈ Q' := by
      rw [Subgroup.mem_comap, hy]
      exact hβ
    let Q'' : Subgroup (A × B) := Q'.map e.toMonoidHom
    have hQ'' : IsPGroup 3 Q'' := hQ'.map e.toMonoidHom
    let P₁ : Subgroup A := Q''.map (MonoidHom.fst A B)
    let P₂ : Subgroup B := Q''.map (MonoidHom.snd A B)
    have hP₁ : IsPGroup 3 P₁ := hQ''.map _
    have hP₂ : IsPGroup 3 P₂ := hQ''.map _
    have hEv : IsL2Ev A n := (P22fin.isL2Ev_of_isL2 hA).1
    have hP₁cyc : IsCyclic P₁ :=
      P22y.isCyclic_of_isPGroup_of_isL2Ev hEv Nat.prime_three (by norm_num) P₁ hP₁
    obtain ⟨t, ht⟩ : ∃ t : ℕ, n = 2 * t := by
      obtain ⟨t, ht⟩ := hn
      exact ⟨t, by omega⟩
    have hB' : IsU3 B (2 * t) := ht ▸ hB
    have hpt : CFSG.Open.pRank 3 (⊤ : Subgroup B) = 1 :=
      k_U3FourPowThreeRankOne_holds B t (by omega) hB'
    have hP₂cyc : IsCyclic P₂ :=
      CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) hP₂ le_top
        (by rw [hpt])
    have hxQ'' : e x ∈ Q'' := Subgroup.mem_map.mpr ⟨x, hxQ', rfl⟩
    have hyQ'' : e y ∈ Q'' := Subgroup.mem_map.mpr ⟨y, hyQ', rfl⟩
    have haP₁ : (e x).1 ∈ P₁ := Subgroup.mem_map.mpr ⟨e x, hxQ'', rfl⟩
    have ha'P₁ : (e y).1 ∈ P₁ := Subgroup.mem_map.mpr ⟨e y, hyQ'', rfl⟩
    have hbP₂ : (e x).2 ∈ P₂ := Subgroup.mem_map.mpr ⟨e x, hxQ'', rfl⟩
    have hb'P₂ : (e y).2 ∈ P₂ := Subgroup.mem_map.mpr ⟨e y, hyQ'', rfl⟩
    have hcommA : (e x).1 * (e y).1 = (e y).1 * (e x).1 := by
      have : IsMulCommutative P₁ := hP₁cyc.isMulCommutative
      exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := P₁)).comm
        ⟨(e x).1, haP₁⟩ ⟨(e y).1, ha'P₁⟩)
    have hcommB : (e x).2 * (e y).2 = (e y).2 * (e x).2 := by
      have : IsMulCommutative P₂ := hP₂cyc.isMulCommutative
      exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := P₂)).comm
        ⟨(e x).2, hbP₂⟩ ⟨(e y).2, hb'P₂⟩)
    have hxy : x * y = y * x := by
      apply e.injective
      have hprod : e x * e y = e y * e x := Prod.ext hcommA hcommB
      rw [map_mul, map_mul]
      exact hprod
    calc α * β = MulAut.conj x * MulAut.conj y := by rw [← hx, ← hy]
      _ = MulAut.conj (x * y) := (map_mul (MulAut.conj : X →* MulAut X) x y).symm
      _ = MulAut.conj (y * x) := by rw [hxy]
      _ = MulAut.conj y * MulAut.conj x := map_mul (MulAut.conj : X →* MulAut X) y x
      _ = β * α := by rw [← hy, ← hx]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

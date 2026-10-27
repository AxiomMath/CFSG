module

public import CFSG.RankThree.PartOne.S9.Alpha.LocalCompletion
public import CFSG.RankThree.PartOne.S9.Alpha.Transport
public import CFSG.RankThree.PartOne.S9.Alpha.Centralizer
public import CFSG.RankThree.PartOne.S9.Sylow.ResidualBridge
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaSolvableCriterion

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank Subgroup

namespace AlphaTheory

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElementaryAbelian_of_le_alpha {p : ℕ} {A B : Subgroup G} (hA : IsElementaryAbelian p A)
    (hBA : B ≤ A) : IsElementaryAbelian p B := CFSG.IsElementaryAbelian.of_le hA hBA

omit [Finite G] in
theorem isElementaryAbelian_subgroupOf {p : ℕ} {E N : Subgroup G} (hEN : E ≤ N)
    (hE : IsElementaryAbelian p E) : IsElementaryAbelian p (E.subgroupOf N) :=
  { toIsMulCommutative := ⟨⟨fun a b => by
      apply (Subgroup.subgroupOfEquivOfLe hEN).injective
      rw [map_mul, map_mul]
      exact hE.is_comm.comm _ _⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      apply (Subgroup.subgroupOfEquivOfLe hEN).injective
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p _ }

omit [Finite G] in
theorem exists_ne_one_of_card_eq_sq {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : Nat.card E = p ^ 2) : ∃ t ∈ E, t ≠ 1 := by
  by_contra h
  push Not at h
  have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
  rw [this, Subgroup.card_bot] at hE
  have := hp.one_lt
  have h2 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) this
  omega

theorem localAlphaBound_of_section_nine {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup G}
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (H1 : ∀ c ∈ A, c ≠ 1 → ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 → c ∈ D →
      ⁅inSubgroup (pCore 2) (normalizer (zpowers c : Set G) ⊓ centralizer (D : Set G)), A⁆ ≤
        inSubgroup (pCore 2) (normalizer (zpowers c : Set G)))
    (H2 : ∀ c ∈ A, c ≠ 1 → ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → ∀ t ∈ B, t ≠ 1 →
      CFSG.Quasithin.twoPrimeResidual (residualGroup p (normalizer (zpowers c : Set G)) B t) ≤
        inSubgroup (aschbacherSolvableCore p) (normalizer (zpowers c : Set G))) :
    LocalAlphaBound p A := by
  intro E hEA hEcard c hcA hc1
  have := hA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    SteinbergBY.mul_comm_of_isMulCommutative hx hy
  have hcord : orderOf c = p := SteinbergBY.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  set N := normalizer (zpowers c : Set G) with hN
  set C := centralizer ({c} : Set G) with hC
  obtain ⟨hCN, -, -, hB⟩ :=
    SteinbergBY.alpha_normal_odd_cyclic_centralizer_transfer_normalizer hp hp2 hcord
  have hEC : E ≤ C := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hcomm x (hEA hx) c hcA)
  have hEN : E ≤ N := hEC.trans hCN
  have hEel : IsElementaryAbelian p E := isElementaryAbelian_of_le_alpha hA hEA
  obtain ⟨t, htE, ht1⟩ := exists_ne_one_of_card_eq_sq hp hEcard
  have hEN' : Nat.card (E.subgroupOf N) = p ^ 2 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have hαN : twoCoreAlpha (E.subgroupOf N) ≤ pCore 2 ↥N := by
    obtain ⟨hθs, -, hθp, -⟩ := solvable_prime_complement_core_characterization (H := ↥N) hp
    have htE' : (⟨t, hEN htE⟩ : N) ∈ E.subgroupOf N := htE
    have ht1' : (⟨t, hEN htE⟩ : N) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
    have hres : CFSG.Quasithin.twoPrimeResidual
        (⁅inSubgroup (aschbacherSolvableCore p)
            (centralizer ({(⟨t, hEN htE⟩ : N)} : Set N)), E.subgroupOf N⁆ ⊔
          thetaT p (E.subgroupOf N)) ≤ aschbacherSolvableCore p ↥N := by
      have h2 := H2 c hcA hc1 E hEA hEcard t htE ht1
      rw [Sec9A.residualGroup_eq_map hp hEN htE ht1] at h2
      have h3 := (map_twoPrimeResidual_le_of_injective N.subtype N.subtype_injective _).trans h2
      exact (Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp h3
    have hXK : twoCoreX (E.subgroupOf N) ≤ aschbacherSolvableCore p ↥N :=
      (SteinbergBY.section_nine_residual_to_intersection hp hp2 (E.subgroupOf N)).2
        ⟨⟨t, hEN htE⟩, htE', ht1', hres⟩
    have hJ : ∀ b ∈ E.subgroupOf N, b ≠ 1 →
        ⁅inSubgroup (pCore 2) (centralizer ({b} : Set N)), E.subgroupOf N⁆ ≤ pCore 2 ↥N := by
      intro b hb hb1
      refine commutator_pCore_le_of_map hEN b ?_
      have hbE : (b : G) ∈ E := hb
      have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
      exact commutator_inf_centralizer_le hp hp2 hA hAcard hcA hc1 (H1 c hcA hc1) hEA hbE hb1'
    exact (SteinbergBY.alpha_solvable_normal_subgroup_criterion hp
      (isElementaryAbelian_subgroupOf hEN hEel) (by rw [hEN']) inferInstance hθs hθp hXK hJ).2.2
  have hαC := (hB E hEC).2 hαN
  exact Subgroup.map_mono hαC

end AlphaTheory

theorem sectionNineAlphaVerificationReduction :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ A : Subgroup G,
      IsElementaryAbelian p A → Nat.card A = p ^ 3 →
      (∀ c ∈ A, c ≠ 1 → ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 → c ∈ D →
        ⁅inSubgroup (pCore 2) (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
            Subgroup.centralizer (D : Set G)), A⁆ ≤
          inSubgroup (pCore 2) (Subgroup.normalizer (Subgroup.zpowers c : Set G))) →
      (∀ c ∈ A, c ≠ 1 → ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → ∀ t ∈ B, t ≠ 1 →
        CFSG.Quasithin.twoPrimeResidual
            (residualGroup p (Subgroup.normalizer (Subgroup.zpowers c : Set G)) B t) ≤
          inSubgroup (aschbacherSolvableCore p)
            (Subgroup.normalizer (Subgroup.zpowers c : Set G))) →
      LocalAlphaBound p A ∧
        (∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → IsPGroup 2 (twoCoreAlpha B)) ∧
        ∀ B D : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → D ≤ A → Nat.card D = p ^ 2 →
          twoCoreAlpha B = twoCoreAlpha D := by
  intro G _ _ p hp hp2 A hA hAcard H1 H2
  have hLAB : LocalAlphaBound p A :=
    AlphaTheory.localAlphaBound_of_section_nine hp hp2 hA hAcard H1 H2
  obtain ⟨h2grp, hEq⟩ := alphaRankThreeLocalCompletion G p hp hp2 A hA hAcard hLAB
  exact ⟨hLAB, h2grp, hEq⟩

end CFSG.RankThree.PartOne

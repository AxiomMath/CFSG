module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwoModule
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.CharacterTheory.Semidihedral.ElementaryActionTransport
public import CFSG.RankThree.CentralExtension.InvariantComplement
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup
open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism)
open CFSG.RankThree.CentralExtension (autCommutator)
open scoped IsMulCommutative

theorem mulAut_commute_of_isCyclic {V : Type*} [Group V] [IsCyclic V] (α β : MulAut V) :
    α * β = β * α :=
  (IsCyclic.mulAutMulEquiv (G := V)).injective (by rw [map_mul, map_mul, mul_comm])

theorem eq_bot_of_isPerfect_of_commute {G : Type*} [Group G] (J : Subgroup G)
    [Group.IsPerfect J] (h : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x) : J = ⊥ := by
  have h1 : ⁅J, J⁆ = J := Subgroup.commutator_eq_self
  rw [← h1, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact h y hy x hx

theorem perfect_action_on_rank_two_exponent_prime_group_is_trivial_or_generating {r : ℕ}
    (hr : r.Prime) (_hr2 : r ≠ 2) {D : Type*} [Group D] [Finite D] (hD : IsPGroup r D)
    (hexp : ∀ x : D, x ^ r = 1) (hrank : CFSG.pRank r D ≤ 2) {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] (φ : A →* MulAut D) :
    autCommutator φ.range = ⊥ ∨
      (autCommutator φ.range = ⊤ ∧ Nat.card (D ⧸ frattini D) = r ^ 2 ∧
        (∃ (a : A) (x : D ⧸ frattini D), quotientAutomorphism (frattini D) (φ a) x ≠ x) ∧
        ∀ W : Subgroup (D ⧸ frattini D),
          (∀ a : A, ∀ w ∈ W, quotientAutomorphism (frattini D) (φ a) w ∈ W) →
            W = ⊥ ∨ W = ⊤) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, -, -, hVel, d, hVd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hD
  have hrank' : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrank
  have hV2 := (CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hD hexp hrank').2
  have hd2 : d ≤ 2 := by
    rw [hVd] at hV2
    exact (Nat.pow_le_pow_iff_right hr.one_lt).1 hV2
  set ψ : A →* MulAut (D ⧸ frattini D) := (quotientAutomorphism (frattini D)).comp φ with hψ
  have hψa : ∀ a, ψ a = quotientAutomorphism (frattini D) (φ a) := fun a => rfl
  by_cases htriv : ∀ a : A, ψ a = 1
  ·
    left
    have hker := (CFSG.GroupTheory.frattini_automorphism_kernel hD).2
    have hle : φ.range ≤ (quotientAutomorphism (frattini D)).ker := by
      rintro _ ⟨a, rfl⟩
      exact htriv a
    have hrg : IsPGroup r φ.range := hker.to_le hle
    have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have hbot : φ.range = ⊥ := by
      by_contra hne
      have : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
      have : Group.IsNilpotent φ.range := hrg.isNilpotent
      exact Group.IsPerfect.not_isSolvable φ.range inferInstance
    rw [autCommutator, eq_bot_iff, closure_le]
    rintro _ ⟨u, a, ha, rfl⟩
    rw [hbot, mem_bot] at ha
    rw [ha, MulAut.one_apply, inv_mul_cancel]
    exact (⊥ : Subgroup D).one_mem
  right
  push Not at htriv
  obtain ⟨a₀, ha₀⟩ := htriv
  obtain ⟨x₀, hx₀⟩ : ∃ x, ψ a₀ x ≠ x := by
    by_contra h
    push Not at h
    exact ha₀ (MulEquiv.ext h)
  have : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hψne : ψ.range ≠ ⊥ := by
    intro h
    exact ha₀ ((mem_bot).1 (h ▸ ⟨a₀, rfl⟩))
  have hd : d = 2 := by
    by_contra hd
    have hcyc : IsCyclic (D ⧸ frattini D) := by
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
      · rw [pow_zero] at hVd
        have : Subsingleton (D ⧸ frattini D) := (Nat.card_eq_one_iff_unique.1 hVd).1
        exact isCyclic_of_subsingleton
      · rw [pow_one] at hVd
        exact isCyclic_of_prime_card hVd
    exact hψne (eq_bot_of_isPerfect_of_commute ψ.range
      fun x _ y _ => mulAut_commute_of_isCyclic x y)
  subst hd
  have : IsElementaryAbelian r (D ⧸ frattini D) := hVel
  have : Finite (Additive (D ⧸ frattini D)) := inferInstanceAs (Finite (D ⧸ frattini D))
  have : FiniteDimensional (ZMod r) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod r) (Additive (D ⧸ frattini D)) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod r) (V := Additive (D ⧸ frattini D))
    rw [Nat.card_zmod] at h
    have h' : Nat.card (Additive (D ⧸ frattini D)) = r ^ 2 := hVd
    rw [h'] at h
    exact (Nat.pow_right_injective hr.two_le h).symm
  have hirr : ∀ W : Subgroup (D ⧸ frattini D), (∀ a : A, ∀ w ∈ W, ψ a w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_contra hcon
    push Not at hcon
    obtain ⟨hW1, hW2⟩ := hcon
    have hWd : Nat.card W ∣ r ^ 2 := hVd ▸ Subgroup.card_subgroup_dvd_card W
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hr).1 hWd
    have hk1 : k = 1 := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
      · exact absurd ((Subgroup.card_eq_one).1 (by rw [hk, pow_zero])) hW1
      · rfl
      · exact absurd ((Subgroup.card_eq_iff_eq_top W).1 (by rw [hk, hVd])) hW2
    subst hk1
    let L : Submodule (ZMod r) (Additive (D ⧸ frattini D)) :=
      AddSubgroup.toZModSubmodule r (Subgroup.toAddSubgroup W)
    have hLmem : ∀ w : Additive (D ⧸ frattini D), w ∈ L ↔ Additive.toMul w ∈ W := fun w =>
      Iff.rfl
    have hLcard : Nat.card L = r := by
      rw [pow_one] at hk
      refine Eq.trans ?_ hk
      exact Nat.card_congr
        { toFun := fun w => ⟨Additive.toMul (w : Additive (D ⧸ frattini D)), w.2⟩
          invFun := fun w => ⟨Additive.ofMul (w : D ⧸ frattini D), w.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hLfin : Module.finrank (ZMod r) L = 1 := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod r) (V := L)
      rw [Nat.card_zmod, hLcard] at h
      exact (Nat.pow_right_injective hr.two_le
        (show r ^ 1 = r ^ Module.finrank (ZMod r) L by rw [pow_one]; exact h)).symm
    set J := (Semidihedral.ElementaryActionTransport.primeFieldAction (p := r) ψ).range
    have : Group.IsPerfect J := Group.IsPerfect.range _
    have hJ : J ≠ ⊥ := by
      intro h
      have hmem : Semidihedral.ElementaryActionTransport.primeFieldAction (p := r) ψ a₀ ∈ J :=
        ⟨a₀, rfl⟩
      rw [h, mem_bot] at hmem
      apply hx₀
      have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod r)
          (Additive (D ⧸ frattini D)) =>
        (g : Module.End (ZMod r) (Additive (D ⧸ frattini D))) (Additive.ofMul x₀)) hmem
      simpa using this
    obtain ⟨-, hline, -⟩ := CFSG.SectionRank.Ccomm.perfect_linear_two_basics_module hfin J hJ
    obtain ⟨g, ⟨a, rfl⟩, hga⟩ := hline L hLfin
    apply hga
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, hLmem] at hw
    rw [hLmem]
    exact hW a _ hw
  refine ⟨?_, hVd, ⟨a₀, x₀, hx₀⟩, hirr⟩
  set S : Set D := {g | ∃ u, ∃ a ∈ φ.range, g = u⁻¹ * a u}
  have himage : QuotientGroup.mk' (frattini D) '' S =
      {v | ∃ (y : D ⧸ frattini D) (a : A), v = y⁻¹ * ψ a y} := by
    ext v
    constructor
    · rintro ⟨_, ⟨u, _, ⟨a, rfl⟩, rfl⟩, rfl⟩
      refine ⟨QuotientGroup.mk' (frattini D) u, a, ?_⟩
      rw [hψa, map_mul, map_inv]
      exact congrArg (HMul.hMul _)
        ((CFSG.GroupTheory.frattini_automorphism_kernel hD).1 (φ a) u).symm
    · rintro ⟨y, a, rfl⟩
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (frattini D) y
      refine ⟨u⁻¹ * φ a u, ⟨u, φ a, ⟨a, rfl⟩, rfl⟩, ?_⟩
      rw [hψa, map_mul, map_inv]
      exact congrArg (HMul.hMul _)
        ((CFSG.GroupTheory.frattini_automorphism_kernel hD).1 (φ a) u).symm
  have hinv : ∀ a : A, ∀ w ∈ closure {v | ∃ (y : D ⧸ frattini D) (a : A), v = y⁻¹ * ψ a y},
      ψ a w ∈ closure {v | ∃ (y : D ⧸ frattini D) (a : A), v = y⁻¹ * ψ a y} := by
    intro b w hw
    have hmap := Subgroup.mem_map_of_mem (ψ b).toMonoidHom hw
    rw [MonoidHom.map_closure] at hmap
    refine closure_mono ?_ hmap
    rintro _ ⟨_, ⟨y, a, rfl⟩, rfl⟩
    refine ⟨ψ b y, b * a * b⁻¹, ?_⟩
    change ψ b (y⁻¹ * ψ a y) = (ψ b y)⁻¹ * ψ (b * a * b⁻¹) (ψ b y)
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply,
      MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hne : closure {v | ∃ (y : D ⧸ frattini D) (a : A), v = y⁻¹ * ψ a y} ≠ ⊥ := by
    intro h
    have hmem : x₀⁻¹ * ψ a₀ x₀ ∈ closure {v | ∃ (y : D ⧸ frattini D) (a : A),
        v = y⁻¹ * ψ a y} := subset_closure ⟨x₀, a₀, rfl⟩
    rw [h, mem_bot, inv_mul_eq_one] at hmem
    exact hx₀ hmem.symm
  have htop := (hirr _ hinv).resolve_left hne
  rw [autCommutator]
  exact CFSG.LocalAnalysis.ComponentInitial.frattini_generator_lifting S (by rw [himage, htop])

end CFSG.Quasithin.H13.NQTerm

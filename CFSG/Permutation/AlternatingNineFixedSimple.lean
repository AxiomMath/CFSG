module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab

public section

namespace CFSG.Permutation

open Equiv Equiv.Perm

private lemma exists_isCycle_orderOf_five_of_card_sixty
    (X : Subgroup (alternatingGroup (Fin 9))) (hX : Nat.card X = 60) :
    ∃ c : alternatingGroup (Fin 9), c ∈ X ∧ (c : Perm (Fin 9)).IsCycle ∧
      orderOf (c : Perm (Fin 9)) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : 5 ∣ Nat.card X := by rw [hX]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 5 h5
  let c : alternatingGroup (Fin 9) := x
  have hxP : orderOf (c : Perm (Fin 9)) = 5 := by
    change orderOf (((x : X) : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 5
    rw [Subgroup.orderOf_coe (H := alternatingGroup (Fin 9)), Subgroup.orderOf_coe (H := X),
      hx]
  have hcyc : (c : Perm (Fin 9)).IsCycle := by
    refine isCycle_of_prime_order ?_ ?_
    · rw [hxP]; norm_num
    · rw [hxP]
      have hle := Finset.card_le_univ (c : Perm (Fin 9)).support
      rw [Fintype.card_fin] at hle
      omega
  exact ⟨c, x.2, hcyc, hxP⟩

private lemma exists_nat_pow_eq_on_support_of_commute_of_card_five {π c : Perm (Fin 9)}
    (hc : c.IsCycle) (hc5 : c.support.card = 5) (hcomm : Commute π c) :
    ∃ j : ℕ, ∀ x ∈ c.support, π x = (c ^ j) x := by
  obtain ⟨hc', hmem⟩ := (hc.commute_iff').mp hcomm
  rw [Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨i, hi⟩ := hmem
  have happ : ∀ x (hx : x ∈ c.support), π x = (c ^ i) x := by
    intro x hx
    have h := congrArg (fun f : Perm c.support => (f ⟨x, hx⟩ : c.support)) hi
    have h2 : (((c.subtypePermOfSupport ^ i) ⟨x, hx⟩ : c.support) : Fin 9) = (c ^ i) x := by
      simpa [subtypePermOfSupport] using
        subtypePerm_apply_zpow_of_mem (g := c) (s := c.support)
          (fun _ => apply_mem_support) (i := i) hx
    exact (h2.symm.trans (congrArg Subtype.val h)).symm
  let j : ℕ := (i % 5).toNat
  have hmod : i % 5 = (j : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num : (5 : ℤ) ≠ 0))]
  have hord : (orderOf c : ℤ) = 5 := by rw [hc.orderOf, hc5]; norm_num
  have hcij : c ^ i = c ^ (j : ℤ) := by
    have h := zpow_mod_orderOf c i
    rw [hord, hmod] at h
    exact h.symm
  refine ⟨j, fun x hx => ?_⟩
  rw [happ x hx, hcij, zpow_natCast]

private lemma cube_eq_one_of_fixes_support_of_card_five {c : Perm (Fin 9)} (hc : c.IsCycle)
    (hc5 : c.support.card = 5) {j : ℕ} (h : ∀ x ∈ c.support, ((c ^ j) ^ 3) x = x) :
    (c ^ j) ^ 3 = 1 := by
  have hpow : (c ^ j) ^ 3 = c ^ (3 * j) := by
    have h1 : (c ^ j) ^ 3 = c ^ (j * 3) := (pow_mul c j 3).symm
    exact h1.trans (by rw [Nat.mul_comm])
  rw [hpow]
  refine (hc.pow_eq_one_iff'' (n := 3 * j)).2 fun x hx => ?_
  have hx' := h x (mem_support.mpr hx)
  rwa [hpow] at hx'

private lemma fix_support_of_commute_of_cube {π c : Perm (Fin 9)} (hc : c.IsCycle)
    (hc5 : c.support.card = 5) (hcomm : Commute π c) (hπ3 : π ^ 3 = 1) :
    ∀ x ∈ c.support, π x = x := by
  obtain ⟨j, hj⟩ := exists_nat_pow_eq_on_support_of_commute_of_card_five hc hc5 hcomm
  have hiter : ∀ x ∈ c.support, ((c ^ j) ^ 3) x = x := by
    intro x hx
    have hx1 : π x ∈ c.support := (mem_support_iff_of_commute hcomm x).mpr hx
    have hx2 : π (π x) ∈ c.support := (mem_support_iff_of_commute hcomm (π x)).mpr hx1
    calc ((c ^ j) ^ 3) x = (c ^ j) ((c ^ j) ((c ^ j) x)) := by
          simp [pow_succ, Perm.mul_apply]
      _ = (c ^ j) ((c ^ j) (π x)) := by rw [hj x hx]
      _ = (c ^ j) (π (π x)) := by rw [hj (π x) hx1]
      _ = π (π (π x)) := by rw [hj (π (π x)) hx2]
      _ = x := by
        simpa [pow_succ, Perm.mul_apply] using congrArg (fun f : Perm (Fin 9) => f x) hπ3
  have h3 := cube_eq_one_of_fixes_support_of_card_five hc hc5 hiter
  have hdvd5 : orderOf (c ^ j) ∣ 5 := by
    simpa [hc.orderOf, hc5] using orderOf_pow_dvd (x := c) j
  have hone : orderOf (c ^ j) = 1 := by
    have hg := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) hdvd5
    rw [show Nat.gcd 3 5 = 1 by norm_num] at hg
    exact Nat.dvd_one.mp hg
  have hcj : c ^ j = 1 := orderOf_eq_one_iff.mp hone
  intro x hx
  rw [hj x hx, hcj, one_apply]

private lemma eq_one_or_isThreeCycle_of_cube_of_support_card_le_four {π : Perm (Fin 9)}
    (hπ3 : π ^ 3 = 1) (hcard : π.support.card ≤ 4) : π = 1 ∨ π.IsThreeCycle := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcycle : π.cycleType = Multiset.replicate π.cycleType.card 3 :=
    cycleType_of_pow_prime_eq_one hπ3
  have hsum : π.cycleType.sum = π.support.card := sum_cycleType π
  have hc3 : π.cycleType.card * 3 = π.support.card := by
    rw [← hsum, hcycle]
    simp [Multiset.sum_replicate, nsmul_eq_mul]
  have hle1 : π.cycleType.card ≤ 1 := by omega
  interval_cases hc : π.cycleType.card
  · exact Or.inl (card_cycleType_eq_zero.mp hc)
  · exact Or.inr (by rw [IsThreeCycle, hcycle]; decide)

private theorem exists_perm_cube_eq_one_fixing_fiveCycle
    (α : MulAut (alternatingGroup (Fin 9))) (hα : α ^ 3 = 1)
    (X : Subgroup (alternatingGroup (Fin 9))) (hX : Nat.card X = 60)
    (hfix : ∀ x ∈ X, α x = x) :
    ∃ π : Perm (Fin 9), α = MulAut.conjNormal π ∧ π ^ 3 = 1 ∧ π.support.card ≤ 4 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)
  obtain ⟨π, hπ⟩ := hbij.2 α
  have hπα : MulAut.conjNormal (H := alternatingGroup (Fin 9)) π = α := hπ
  have hπ3 : π ^ 3 = 1 := by
    apply hbij.1
    rw [map_pow, hπα, hα, map_one]
  obtain ⟨c, hcX, hcCyc, hcOrd⟩ := exists_isCycle_orderOf_five_of_card_sixty X hX
  let cP : Perm (Fin 9) := c
  have hcPcyc : cP.IsCycle := hcCyc
  have hc5 : cP.support.card = 5 := hcPcyc.orderOf.symm.trans hcOrd
  have hcπ : Commute π cP := by
    have h1 : MulAut.conjNormal (H := alternatingGroup (Fin 9)) π c = c := by
      rw [hπα]
      exact hfix c hcX
    have hconj : π * cP * π⁻¹ = cP := by
      have h := congrArg (fun y : alternatingGroup (Fin 9) => (y : Perm (Fin 9))) h1
      simpa [cP, MulAut.conjNormal_apply] using h
    have h2 := congrArg (fun y : Perm (Fin 9) => y * π) hconj.symm
    exact (commute_iff_eq π cP).mpr (by simpa [mul_assoc] using h2.symm)
  have hfixπ : ∀ x ∈ cP.support, π x = x :=
    fix_support_of_commute_of_cube hcPcyc hc5 hcπ hπ3
  have hdisj : π.Disjoint cP := by
    intro x
    by_cases hx : x ∈ cP.support
    · exact Or.inl (hfixπ x hx)
    · exact Or.inr (notMem_support.mp hx)
  have hsupp4 : π.support.card ≤ 4 := by
    have hunion : π.support ∪ cP.support ⊆ (Finset.univ : Finset (Fin 9)) := by simp
    have hcard := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint (disjoint_iff_disjoint_support.mp hdisj), hc5,
      Finset.card_univ, Fintype.card_fin] at hcard
    omega
  exact ⟨π, hπ.symm, hπ3, hsupp4⟩

private lemma alpha_fixes_altStabilizer_of_isThreeCycle
    (α : MulAut (alternatingGroup (Fin 9))) (π : Perm (Fin 9))
    (hπα : α = MulAut.conjNormal π) :
    ∀ w ∈ CFSG.CGT.PushingUp.altStabilizer 9 π.support, α w = w := by
  intro w hw
  have hwS : ∀ y ∈ π.support, (w : Perm (Fin 9)) y = y := by
    rwa [CFSG.CGT.PushingUpLit.CGT6.mem_altStabilizer_iff] at hw
  have hdisj : π.Disjoint (w : Perm (Fin 9)) := by
    intro y
    by_cases hy : y ∈ π.support
    · exact Or.inr (hwS y hy)
    · exact Or.inl (notMem_support.mp hy)
  have h1 : MulAut.conjNormal (H := alternatingGroup (Fin 9)) π w = w := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    rw [hdisj.commute.eq]
    simp
  rw [hπα]
  exact h1

private lemma isSimpleGroup_and_card_altStabilizer_of_isThreeCycle {π : Perm (Fin 9)}
    (hπ : π.IsThreeCycle) :
    IsSimpleGroup (CFSG.CGT.PushingUp.altStabilizer 9 π.support) ∧
      Nat.card (CFSG.CGT.PushingUp.altStabilizer 9 π.support) = 360 := by
  have hcard : π.support.card = 3 := hπ.card_support
  constructor
  · have h6 : 9 - π.support.card = 6 := by rw [hcard]
    have eW : CFSG.CGT.PushingUp.altStabilizer 9 π.support ≃*
        alternatingGroup (Fin 6) :=
      (CFSG.CGT.PushingUpLit.CGT6.altStabilizerEquiv π.support).trans
        (Equiv.altCongrHom (finCongr h6))
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    exact eW.isSimpleGroup
  · rw [CFSG.CGT.PushingUpLit.CGT6.card_altStabilizer π.support (by omega), hcard]
    norm_num

private lemma le_altStabilizer_of_isThreeCycle
    (π : Perm (Fin 9)) (hπ : π.IsThreeCycle)
    (X : Subgroup (alternatingGroup (Fin 9))) (hXs : IsSimpleGroup X) (hX : Nat.card X = 60)
    (hcomm : ∀ x : X, Commute ((x : X) : Perm (Fin 9)) π) :
    X ≤ CFSG.CGT.PushingUp.altStabilizer 9 π.support := by
  let S := π.support
  have hmaps : ∀ x : X, ∀ y : ↥S, ((x : X) : Perm (Fin 9)) y ∈ S := by
    intro x y
    show ((x : X) : Perm (Fin 9)) y ∈ π.support
    exact (mem_support_iff_of_commute (hcomm x) y).mpr y.2
  let act : MulAction X ↥S :=
    { smul := fun x y => ⟨((x : X) : Perm (Fin 9)) y, hmaps x y⟩
      one_smul := by intro y; apply Subtype.ext; rfl
      mul_smul := by intro x y z; apply Subtype.ext; rfl }
  letI : MulAction X ↥S := act
  let φ : X →* Perm ↥S := MulAction.toPermHom X ↥S
  have hker_top : φ.ker = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top φ.ker with hbot | htop
    · exfalso
      have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
      have hcard_le : Nat.card X ≤ Nat.card (Perm ↥S) :=
        Nat.card_le_card_of_injective φ hinj
      have hS : Nat.card ↥S = 3 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        exact hπ.card_support
      have hperm : Nat.card (Perm ↥S) = 6 := by
        rw [Nat.card_perm, hS]; norm_num
      rw [hX, hperm] at hcard_le
      omega
    · exact htop
  intro x hx
  rw [CFSG.CGT.PushingUpLit.CGT6.mem_altStabilizer_iff]
  intro y hy
  have hxker : (⟨x, hx⟩ : X) ∈ φ.ker := by rw [hker_top]; exact Subgroup.mem_top _
  have hφx : φ ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.mp hxker
  have h := congrArg (fun f : Perm ↥S => (f ⟨y, hy⟩ : ↥S)) hφx
  have h' := congrArg Subtype.val h
  change (((⟨x, hx⟩ : X) : Perm (Fin 9)) y : Fin 9) = y at h'
  exact h'

private theorem exists_simple_fixed_of_isThreeCycle
    (α : MulAut (alternatingGroup (Fin 9))) (π : Perm (Fin 9))
    (hπα : α = MulAut.conjNormal π) (hπ : π.IsThreeCycle)
    (X : Subgroup (alternatingGroup (Fin 9))) (hXs : IsSimpleGroup X) (hX : Nat.card X = 60)
    (hcomm : ∀ x : X, Commute ((x : X) : Perm (Fin 9)) π) :
    ∃ W : Subgroup (alternatingGroup (Fin 9)), X ≤ W ∧ (∀ w ∈ W, α w = w) ∧
      IsSimpleGroup W ∧ 180 < Nat.card W := by
  refine ⟨CFSG.CGT.PushingUp.altStabilizer 9 π.support,
    le_altStabilizer_of_isThreeCycle π hπ X hXs hX hcomm,
    alpha_fixes_altStabilizer_of_isThreeCycle α π hπα, ?_, ?_⟩
  · exact (isSimpleGroup_and_card_altStabilizer_of_isThreeCycle hπ).1
  · rw [(isSimpleGroup_and_card_altStabilizer_of_isThreeCycle hπ).2]
    norm_num

private theorem exists_simple_fixed_of_aut_eq_one (α : MulAut (alternatingGroup (Fin 9)))
    (hα1 : α = 1) (X : Subgroup (alternatingGroup (Fin 9))) :
    ∃ W : Subgroup (alternatingGroup (Fin 9)), X ≤ W ∧ (∀ w ∈ W, α w = w) ∧
      IsSimpleGroup W ∧ 180 < Nat.card W := by
  refine ⟨⊤, le_top, ?_, ?_, ?_⟩
  · intro w _
    rw [hα1, MulAut.one_apply]
  · haveI : IsSimpleGroup (alternatingGroup (Fin 9)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    exact (Subgroup.topEquiv).isSimpleGroup
  · rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin]
    norm_num

theorem exists_simple_fixed_of_alternatingNine_aut_cube
    (α : MulAut (alternatingGroup (Fin 9))) (hα : α ^ 3 = 1)
    (X : Subgroup (alternatingGroup (Fin 9))) (hXs : IsSimpleGroup X) (hX : Nat.card X = 60)
    (hfix : ∀ x ∈ X, α x = x) :
    ∃ W : Subgroup (alternatingGroup (Fin 9)), X ≤ W ∧ (∀ w ∈ W, α w = w) ∧
      IsSimpleGroup W ∧ 180 < Nat.card W := by
  obtain ⟨π, hπ, hπ3, hsupp4⟩ :=
    exists_perm_cube_eq_one_fixing_fiveCycle α hα X hX hfix
  rcases eq_one_or_isThreeCycle_of_cube_of_support_card_le_four hπ3 hsupp4 with hπ1 | hπ3c
  · have hα1 : α = 1 := by rw [hπ, hπ1, map_one]
    exact exists_simple_fixed_of_aut_eq_one α hα1 X
  · have hcomm : ∀ x : X, Commute ((x : X) : Perm (Fin 9)) π := by
      intro x
      have h1 : MulAut.conjNormal (H := alternatingGroup (Fin 9)) π x = x := by
        rw [← hπ]
        exact hfix x x.2
      have hconj : π * ((x : X) : Perm (Fin 9)) * π⁻¹ =
          ((x : X) : Perm (Fin 9)) := by
        have h := congrArg (fun y : alternatingGroup (Fin 9) => (y : Perm (Fin 9))) h1
        simpa [MulAut.conjNormal_apply] using h
      have h2 := congrArg (fun y : Perm (Fin 9) => y * π) hconj.symm
      exact (commute_iff_eq _ _).mpr (by simpa [mul_assoc] using h2)
    exact exists_simple_fixed_of_isThreeCycle α π hπ hπ3c X hXs hX hcomm

end CFSG.Permutation

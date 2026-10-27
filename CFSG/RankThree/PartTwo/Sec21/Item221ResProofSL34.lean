module

public import CFSG.RankThree.PartTwo.Sec21.Item221ProofStatements
public import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec21.Star22Theorem3
import CFSG.RankThree.PartTwo.Sec21.Item221ResProofThree
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def SL34LeviCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A L : Subgroup G),
    IsElemAbelian 3 A → A ≤ Subgroup.normalizer (L : Set G) → CFSG.IsQuasisimple L →
    Nonempty (lBar L ≃* SL3 2) → IsTypeCOnBarSL A L →
    IsPGroup 2 (aschbacherSolvableCore 3 L) →
    ∀ a' ∈ A, ¬ L ≤ Subgroup.centralizer ({a'} : Set G) →
    ∀ V : Subgroup G, V ≤ L → V ≤ Subgroup.centralizer ({a'} : Set G) → IsElemAbelian 2 V →
      Nat.card V = 4 → V ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
    ∀ a ∈ A, ¬ L ≤ Subgroup.centralizer ({a} : Set G) →
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {a}) ≠ ⊥ →
      Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {a}) ≃*
        projSL 2 (GaloisField 2 2))

namespace Item221ResProof

variable {G : Type} [Group G]

theorem le_centralizer_theta [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hθ : IsPGroup 2 (inSubgroup (aschbacherSolvableCore 3) L)) :
    A ≤ Subgroup.centralizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) := by
  set T := inSubgroup (aschbacherSolvableCore 3) L
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hcomm : ⁅T, A⁆ = ⊥ := by
    have hTA : ⁅T, A⁆ ≤ T :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_theta hAL)
    apply eq_bot_of_isPGroup_two_of_odd (hθ.to_le hTA)
    exact Odd.of_dvd_nat (hpair.mem_S.2.1 c hcA hpairs.2.1) (Subgroup.card_dvd_of_le
      (Subgroup.commutator_mono (theta_le_theta_centralizer hLc) le_rfl))
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h := Subgroup.commutator_mem_commutator ht ha
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem inf_eq_bot_of_le_centralizer [Finite G] {A V T : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hV : V ∈ fourGroupsMinus A) (hAT : A ≤ Subgroup.centralizer (T : Set G)) : V ⊓ T = ⊥ := by
  obtain ⟨hV4, hVeq⟩ := hV
  obtain ⟨hAV, hVe, hVc⟩ := mem_fourGroups_iff.mp hV4
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  by_contra hv1
  have hall : A ≤ Subgroup.centralizer (V : Set G) := by
    intro a ha
    refine mem_centralizer_of_fixes_four hVe hVc (hAV ha) (hAe.2 a ha) hv.1 hv1 ?_
    have := Subgroup.mem_centralizer_iff.mp (hAT ha) v hv.2
    rw [← this, mul_inv_cancel_right]
  have hbot : ⁅V, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hall ha) x hx).symm
  rw [← hVeq] at hbot
  rw [hbot, Subgroup.card_bot] at hVc
  omega

theorem exists_pow_mul_mem_centralizer [Finite G] {A V : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hV : V ∈ fourGroups A) {x y : G} (hxA : x ∈ A) (hyA : y ∈ A)
    (hx : x ∉ Subgroup.centralizer (V : Set G)) :
    ∃ k : ℕ, k < 3 ∧ x ^ k * y ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hAV, hVe, hVc⟩ := mem_fourGroups_iff.mp hV
  have hconj : ∀ g ∈ A, ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hAV hg) v).mp hv
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  obtain ⟨⟨u, huV⟩, hu1⟩ : ∃ u : V, u ≠ 1 := by
    refine Subgroup.ne_bot_iff_exists_ne_one.mp fun h => ?_
    rw [h, Subgroup.card_bot] at hVc
    omega
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hfix : ∀ g ∈ A, g * u * g⁻¹ = u → g ∈ Subgroup.centralizer (V : Set G) := fun g hg h =>
    mem_centralizer_of_fixes_four hVe hVc (hAV hg) (hAe.2 g hg) huV hu1' h
  set v := x * u * x⁻¹ with hv
  set w := x * v * x⁻¹ with hw
  have hvV : v ∈ V := hconj x hxA u huV
  have hwV : w ∈ V := hconj x hxA v hvV
  have hx2 : x ^ 2 * u * (x ^ 2)⁻¹ = w := by
    rw [hw, hv]
    simp only [pow_succ, pow_zero, one_mul]
    group
  have hxu : v ≠ u := fun h => hx (hfix x hxA h)
  have hv1 : v ≠ 1 := fun h => hu1' (by
    calc u = x⁻¹ * v * x := by rw [hv]; group
      _ = 1 := by rw [h]; group)
  have hwu : w ≠ u := by
    intro h
    apply hx
    have hx2A : x ^ 2 ∈ A := A.pow_mem hxA 2
    have hc := hfix (x ^ 2) hx2A (hx2.trans h)
    have : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc x = x ^ 3 * x := by rw [hx3, one_mul]
        _ = x ^ 4 := (pow_succ x 3).symm
    rw [this]
    exact Subgroup.pow_mem _ hc 2
  have hwv : w ≠ v := fun h => by
    apply hxu
    calc v = x⁻¹ * w * x := by rw [hw]; group
      _ = x⁻¹ * v * x := by rw [h]
      _ = u := by rw [hv]; group
  have hw1 : w ≠ 1 := fun h => hv1 (by
    calc v = x⁻¹ * w * x := by rw [hw]; group
      _ = 1 := by rw [h]; group)
  have hcases : ∀ t ∈ V, t = 1 ∨ t = u ∨ t = v ∨ t = w := by
    intro t ht
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2, h3, h4⟩ := hne
    have hinj : Function.Injective (fun i : Fin 5 => (![(1 : G), u, v, w, t] i)) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> first
        | exact absurd hij.symm hu1' | exact absurd hij hu1'
        | exact absurd hij.symm hv1 | exact absurd hij hv1
        | exact absurd hij.symm hw1 | exact absurd hij hw1
        | exact absurd hij.symm h1 | exact absurd hij h1
        | exact absurd hij.symm hxu | exact absurd hij hxu
        | exact absurd hij.symm hwu | exact absurd hij hwu
        | exact absurd hij.symm hwv | exact absurd hij hwv
        | exact absurd hij.symm h2 | exact absurd hij h2
        | exact absurd hij.symm h3 | exact absurd hij h3
        | exact absurd hij.symm h4 | exact absurd hij h4
    have hmem : ∀ i : Fin 5, ![(1 : G), u, v, w, t] i ∈ V := by
      intro i
      fin_cases i
      · exact V.one_mem
      · exact huV
      · exact hvV
      · exact hwV
      · exact ht
    have h5 := Nat.card_le_card_of_injective
      (fun i : Fin 5 => (⟨_, hmem i⟩ : V)) (fun i j h => hinj (congrArg Subtype.val h))
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, hVc] at h5
    omega
  have hyu : y * u * y⁻¹ ∈ V := hconj y hyA u huV
  rcases hcases _ hyu with h | h | h | h
  · exfalso
    apply hu1'
    calc u = y⁻¹ * (y * u * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  · exact ⟨0, by norm_num, by rw [pow_zero, one_mul]; exact hfix y hyA h⟩
  ·
    refine ⟨2, by norm_num, hfix _ (A.mul_mem (A.pow_mem hxA 2) hyA) ?_⟩
    calc x ^ 2 * y * u * (x ^ 2 * y)⁻¹ = x ^ 2 * (y * u * y⁻¹) * (x ^ 2)⁻¹ := by group
      _ = x ^ 2 * v * (x ^ 2)⁻¹ := by rw [h]
      _ = x ^ 3 * u * (x ^ 3)⁻¹ := by
        rw [hv]
        simp only [pow_succ, pow_zero, one_mul]
        group
      _ = u := by rw [hx3]; group
  ·
    refine ⟨1, by norm_num, hfix _ (A.mul_mem (A.pow_mem hxA 1) hyA) ?_⟩
    calc x ^ 1 * y * u * (x ^ 1 * y)⁻¹ = x * (y * u * y⁻¹) * x⁻¹ := by group
      _ = x * w * x⁻¹ := by rw [h]
      _ = x ^ 3 * u * (x ^ 3)⁻¹ := by
        rw [hw, hv]
        simp only [pow_succ, pow_zero, one_mul]
        group
      _ = u := by rw [hx3]; group

theorem nine_le_card_inf_centralizer [Finite G] {A V : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 3 ^ 3) (hV : V ∈ fourGroups A) {x : G} (hxA : x ∈ A)
    (hx : x ∉ Subgroup.centralizer (V : Set G)) :
    9 ≤ Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
  have h := fun y : A => exists_pow_mul_mem_centralizer hAe hV hxA y.2 hx
  choose k hk hky using h
  let g : A → Fin 3 × (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := fun y =>
    (⟨k y, hk y⟩, ⟨x ^ k y * y, A.mul_mem (A.pow_mem hxA _) y.2, hky y⟩)
  have hg : Function.Injective g := by
    intro y z hyz
    have h1 : k y = k z := congrArg (fun p => (p.1 : ℕ)) hyz
    have h2 : x ^ k y * (y : G) = x ^ k z * z := congrArg (fun p => ((p.2 : _) : G)) hyz
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  have hle := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, hA27] at hle
  omega

end Item221ResProof

open Item221ResProof

theorem item221SL34_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hS : SL34LeviCover) :
    Item221SL34 := by
  intro G _ _ A E U c L hpair hA27 hq hL hC hθ hU' a haA hac hne
  obtain ⟨U', hU', hU'L⟩ := hU'
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  obtain ⟨hE, hEA⟩ := hpair.mem_E
  have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hA27, hE.2.1]; norm_num)
  rw [hEeq] at hU'
  have hU'4 := hU'.1
  obtain ⟨hAU', hU'e, hU'c⟩ := mem_fourGroups_iff.mp hU'4
  have hθG : IsPGroup 2 (inSubgroup (aschbacherSolvableCore 3) L) := hθ.map L.subtype
  have hAT := le_centralizer_theta hpair hAL hθG
  have hU'T := inf_eq_bot_of_le_centralizer hAe hU' hAT
  have hLstar : L ∈ lStar A :=
    lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1)
  have hcL : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨hcA, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hcA) hc1
  have hCL : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcL) ?_).symm
    rw [card_inf_centralizer_eq_three h66 hpair.standing hpair.mem_S hLstar, Nat.card_zpowers,
      hc3]
  have hnot : ∀ b ∈ A, b ∉ Subgroup.zpowers c → ¬ L ≤ Subgroup.centralizer ({b} : Set G) := by
    intro b hbA hbc hLb
    apply hbc
    rw [← hCL]
    refine ⟨hbA, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLb hl)
  obtain ⟨x, hxA, hx⟩ : ∃ x ∈ A, x ∉ Subgroup.centralizer (U' : Set G) := by
    by_contra h
    push Not at h
    have hbot : ⁅U', A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (h b hb) u hu).symm
    rw [← hU'.2] at hbot
    rw [hbot, Subgroup.card_bot] at hU'c
    omega
  have h9 := nine_le_card_inf_centralizer hAe hA27 hU'4 hxA hx
  obtain ⟨a', ha'C, ha'c⟩ : ∃ a' ∈ A ⊓ Subgroup.centralizer (U' : Set G),
      a' ∉ Subgroup.zpowers c := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show A ⊓ Subgroup.centralizer (U' : Set G) ≤
      Subgroup.zpowers c from h)
    rw [Nat.card_zpowers, hc3] at hle
    omega
  have hU'a' : U' ≤ Subgroup.centralizer ({a'} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp ha'C.2 u hu)
  exact hS G A L hAe hAL hq hL hC hθ a' ha'C.1 (hnot a' ha'C.1 ha'c) U' hU'L hU'a' hU'e hU'c
    hU'T a haA (hnot a haA hac) hne

end CFSG.RankThree.PartTwo.Sec21

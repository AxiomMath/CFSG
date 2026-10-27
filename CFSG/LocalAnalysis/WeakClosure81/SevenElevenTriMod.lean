module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriQuot

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri

open Subgroup CFSG.RankThree.FFModules

private lemma triaMod_one_add_pow_two_pow {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
    (N : Module.End (ZMod 2) A) (k : ℕ) :
    (1 + N) ^ (2 ^ k) = 1 + N ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
      rw [hpow, pow_add, ih]
      have hNN : N ^ (2 ^ k) + N ^ (2 ^ k) = 0 := by
        ext x
        rw [LinearMap.add_apply, ← two_smul (ZMod 2) ((N ^ (2 ^ k)) x)]
        rw [show (2 : ZMod 2) = 0 by decide, zero_smul, LinearMap.zero_apply]
      have hsq : (1 + N ^ (2 ^ k)) * (1 + N ^ (2 ^ k)) =
          1 + N ^ (2 ^ k) + N ^ (2 ^ k) + N ^ (2 ^ k) * N ^ (2 ^ k) := by
        rw [add_mul, one_mul, mul_add, mul_one]
        abel
      rw [hsq, add_assoc 1 (N ^ (2 ^ k)) (N ^ (2 ^ k)), hNN, add_zero, ← pow_add]

private theorem triality_isNilpotent_rep_sub_one {Γ X A : Type} [Group Γ] [Group X] [AddCommGroup A]
    [Module (ZMod 2) A] [Finite A] {π : Γ →* X} {𝔇 : Set Γ} {s : X}
    (hL : TrialityHyp π 𝔇 s) (ρ : Representation (ZMod 2) Γ A)
    (hI : TrialityIdent π 𝔇 ρ) :
    ∀ g : Γ, IsNilpotent (ρ g - 1) := by
  classical
  haveI : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun S : Subrepresentation ρ => (S.toSubmodule : Set A))
      (fun S T h =>
        Subrepresentation.toSubmodule_injective
          (Submodule.ext (fun x => Set.ext_iff.mp h x)))
  let P : Subrepresentation ρ → Prop := fun T =>
    ∀ g : Γ, ∃ m : ℕ, ∀ x ∈ T.toSubmodule, ((ρ g - 1) ^ m) x = 0
  have key : ∀ n : ℕ, ∀ T : Subrepresentation ρ,
      Nat.card (T.toSubmodule : Set A) = n → P T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hT
      by_cases hbot : T = ⊥
      · rw [hbot]
        intro g
        refine ⟨0, fun x hx => ?_⟩
        rw [pow_zero, Module.End.one_apply]
        change x ∈ (⊥ : Submodule (ZMod 2) A) at hx
        simpa using hx
      · have hne : ({S : Subrepresentation ρ | S < T} : Set (Subrepresentation ρ)).Nonempty :=
          ⟨⊥, bot_lt_iff_ne_bot.mpr hbot⟩
        obtain ⟨S, hSmax⟩ :=
          (Set.toFinite ({S : Subrepresentation ρ | S < T})).exists_maximal hne
        have hST : S < T := hSmax.1
        have hcov : S ⋖ T := by
          refine ⟨hST, fun U hSU hUT => ?_⟩
          exact (not_le_of_gt hSU) (hSmax.2 hUT hSU.le)
        have hcard : Nat.card (S.toSubmodule : Set A) <
            Nat.card (T.toSubmodule : Set A) := by
          refine Set.Finite.card_lt_card (Set.toFinite (T.toSubmodule : Set A)) ⟨?_, ?_⟩
          · intro x hx
            exact hST.le hx
          · intro hsub
            have hEq : S.toSubmodule = T.toSubmodule := by
              exact Submodule.ext fun x => ⟨fun hx => hST.le hx, fun hx => hsub hx⟩
            exact hST.ne (Subrepresentation.toSubmodule_injective hEq)
        have hcardn : Nat.card (S.toSubmodule : Set A) < n := by
          rwa [hT] at hcard
        have hPS : P S := ih (Nat.card (S.toSubmodule : Set A)) hcardn S rfl
        intro g
        obtain ⟨m, hm⟩ := hPS g
        refine ⟨m + 1, fun x hx => ?_⟩
        have hfac := factorRep_eq_one_of_triality hL hI hcov g
        have hquot :
            Submodule.Quotient.mk (p := factorSub S T)
                ((T.toRepresentation g) (⟨x, hx⟩ : T.toSubmodule)) =
              Submodule.Quotient.mk (p := factorSub S T) ((⟨x, hx⟩ : T.toSubmodule)) := by
          have h := congrArg (fun f : Module.End (ZMod 2)
              (T.toSubmodule ⧸ factorSub S T) =>
              f (Submodule.Quotient.mk (p := factorSub S T)
                (⟨x, hx⟩ : T.toSubmodule))) hfac
          simpa only [Module.End.one_apply, factorRep_mk] using h
        have hmemT : (T.toRepresentation g - 1) (⟨x, hx⟩ : T.toSubmodule) ∈ factorSub S T :=
          (Submodule.Quotient.eq (p := factorSub S T)).mp hquot
        have hmemS : ((T.toRepresentation g - 1) (⟨x, hx⟩ : T.toSubmodule)).1 ∈
            S.toSubmodule := by
          simpa [factorSub] using hmemT
        have hcoe : ((T.toRepresentation g - 1) (⟨x, hx⟩ : T.toSubmodule)).1 =
            (ρ g - 1) x := rfl
        have hmem : (ρ g - 1) x ∈ S.toSubmodule := by
          rwa [hcoe] at hmemS
        have hzero := hm ((ρ g - 1) x) hmem
        rw [pow_succ, Module.End.mul_apply]
        exact hzero
  have htop := key (Nat.card ((⊤ : Subrepresentation ρ).toSubmodule : Set A)) ⊤ rfl
  intro g
  obtain ⟨m, hm⟩ := htop g
  refine ⟨m, LinearMap.ext fun x => ?_⟩
  simpa using hm x (Submodule.mem_top)

theorem false_of_isNilpotent_rep {Γ X A : Type} [Group Γ] [Group X] [AddCommGroup A]
    [Module (ZMod 2) A] [Finite A] {π : Γ →* X} {𝔇 : Set Γ} {s : X}
    (hL : TrialityHyp π 𝔇 s) (ρ : Representation (ZMod 2) Γ A)
    (hI : TrialityIdent π 𝔇 ρ) (hker : ∀ g : Γ, ρ g = 1 → π g = 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil := triality_isNilpotent_rep_sub_one hL ρ hI
  have hP : IsPGroup 2 X := by
    intro x
    obtain ⟨g, rfl⟩ := hL.surj x
    obtain ⟨m, hm⟩ := hnil g
    have hN : (ρ g - 1) ^ (2 ^ m) = 0 :=
      pow_eq_zero_of_le (Nat.le_of_lt (Nat.lt_two_pow_self : m < 2 ^ m)) hm
    have hpow : (ρ g) ^ (2 ^ m) = 1 := by
      have h1 : ρ g = 1 + (ρ g - 1) := by abel
      rw [h1, triaMod_one_add_pow_two_pow, hN, add_zero]
    refine ⟨m, ?_⟩
    have hmap : ρ (g ^ (2 ^ m)) = 1 := by
      rw [map_pow]
      exact hpow
    have hpi := hker (g ^ (2 ^ m)) hmap
    simpa only [map_pow] using hpi
  obtain ⟨a, b, t, ha, hb, ht, hab, hta, htb, htab⟩ := hL.line
  obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (a * b)
  have h3 : 3 = 2 ^ k := hab.symm.trans hk
  cases k with
  | zero => norm_num at h3
  | succ k =>
      have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
      rw [← h3] at h2
      norm_num at h2

end CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri

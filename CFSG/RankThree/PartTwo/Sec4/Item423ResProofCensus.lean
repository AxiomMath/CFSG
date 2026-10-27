module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofCensus
import CFSG.RankThree.ThinCatalog.FiveModels
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.GorensteinWalter (PSL2)

@[expose] def Census423 (X : Type) [Group X] [Finite X] : Prop :=
  ∀ D : Subgroup X, Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) D →
    Nat.card D = 9 →
  ∀ Y : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ Y →
    thetaAlpha 3 ((D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y) ≠ ⊥ →
      (Nonempty (X ≃* alternatingGroup (Fin 7)) ∧
          Nonempty (autIn (⊤ : Subgroup X) D ≃* Multiplicative (ZMod 4))) ∨
        (Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
          Nonempty (autIn (⊤ : Subgroup X) D ≃* QuaternionGroup 2)) ∨
        ((Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
            Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) ∧
          Nonempty (autIn (⊤ : Subgroup X) D ≃* Equiv.Perm (Fin 3)))

@[expose] def K423Inner46OneThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (∃ e : ℕ, 1 ≤ e ∧ Nonempty (X ≃* projSL 2 (GaloisField 3 e))) → IsQuasisimple X →
      Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

@[expose] def K423Inner46One : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46One X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

@[expose] def K423Inner46Two : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Two X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

@[expose] def K423Inner46Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Three X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

@[expose] def K423Inner46Four : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Four X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

@[expose] def K423Inner46Five : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Five X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

@[expose] def K423Inner46Six : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Six X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

@[expose] def K423Inner46SixRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46SixRest X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

@[expose] def K423Inner46Seven : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Seven X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

@[expose] def K423Inner46Eight : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Eight X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

theorem k423InnerCensus_of (h1 : K423Inner46One) (h2 : K423Inner46Two)
    (h3 : K423Inner46Three) (h4 : K423Inner46Four) (h5 : K423Inner46Five)
    (h6 : K423Inner46Six) (h7 : K423Inner46Seven) (h8 : K423Inner46Eight) :
    K423InnerCensus := by
  intro X _ _ hX hq hZ hSL
  rcases (isList46_iff X).mp hX with h | h | h | h | h | h | h | h
  · exact h1 X h hq hZ hSL
  · exact h2 X h hq hZ hSL
  · exact h3 X h hq hZ hSL
  · exact h4 X h hq hZ hSL
  · exact h5 X h hq hZ hSL
  · exact h6 X h hq hZ hSL
  · exact h7 X h hq hZ hSL
  · exact h8 X h hq hZ hSL

namespace Res423Census

variable {X : Type} [Group X] [Finite X]

theorem census423_of_cyclic_sylow (hX : ∀ Q : Sylow 3 X, IsCyclic Q) : Census423 X := by
  intro D hD hD9
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hDQ⟩ := (Sec5.isPGroup_of_isElemAbelian hD.prop).exists_le_sylow
  have := hX Q
  have hDc : IsCyclic D := by
    have hc : IsCyclic (D.subgroupOf Q) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hDQ).toMonoidHom
      (MulEquiv.surjective _)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D)
  have hg9 : orderOf g = 9 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hD9]
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hD.prop.2 g g.2)
  have h93 := orderOf_dvd_of_pow_eq_one hg3
  rw [hg9] at h93
  exact absurd h93 (by norm_num)

theorem census423_of_not_nine_dvd (hX : ¬ 9 ∣ Nat.card X) : Census423 X := by
  intro D _ hD9
  exfalso
  apply hX
  rw [← hD9]
  exact Subgroup.card_subgroup_dvd_card D

theorem isCyclic_sylow_of_mulEquiv {Y : Type*} [Group Y] (φ : X ≃* Y)
    (hY : ∀ Q : Sylow 3 Y, IsCyclic Q) (Q : Sylow 3 X) : IsCyclic Q := by
  have : Finite Y := Finite.of_equiv X φ.toEquiv
  have hf : Function.Surjective φ.symm.toMonoidHom := φ.symm.surjective
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf 3 Q
  have := hY S
  rw [Sylow.coe_mapSurjective]
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem isCyclic_sylow_of_projSL_two {p e : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (he : 1 ≤ e)
    (h4 : 4 ≤ p ^ e) (φ : X ≃* projSL 2 (GaloisField p e)) (Q : Sylow 3 X) : IsCyclic Q := by
  refine isCyclic_sylow_of_mulEquiv (φ.trans (projSLEquivPSL _)) (fun Q' => ?_) Q
  refine KFacts.isCyclic_sylow_three_psl2 ?_ ?_ Q'
  · rw [ringChar.eq (GaloisField p e) p]
    exact hp3
  · rw [GaloisField.card p e (by omega)]
    exact h4

omit [Finite X] in
theorem not_nine_dvd_card_of_projSL_two_two (φ : X ≃* projSL 2 (GaloisField 2 1)) :
    ¬ 9 ∣ Nat.card X := by
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := GaloisField 2 1) (CharTwo.neg_eq 1)
  have h := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := GaloisField 2 1)
  rw [hcenter, mul_one, GaloisField.card 2 1 (by norm_num)] at h
  rw [Nat.card_congr ((φ.trans (projSLEquivPSL _)).toEquiv), h]
  norm_num

end Res423Census

open Res423Census Item424Proof

theorem k423Inner46One_of (h : K423Inner46OneThree) : K423Inner46One := by
  rintro X _ _ ⟨p, e, hp, hp2, he, ⟨φ⟩⟩ hq hZ hSL
  by_cases hp3 : p = 3
  · subst hp3
    exact h X ⟨e, he, ⟨φ⟩⟩ hq hZ hSL
  · refine census423_of_cyclic_sylow (isCyclic_sylow_of_projSL_two hp3 he ?_ φ)
    have hp5 : 5 ≤ p := by
      have := hp.out.two_le
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p
        · exact absurd rfl hp2
        · exact absurd rfl hp3
        · exact absurd hp.out (by norm_num)
      · exact h
    calc 4 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he

theorem k423Inner46Two : K423Inner46Two := by
  rintro X _ _ ⟨p, e, hp, hp3, he, -, hX⟩ - - hSL
  have hp3' : p ≠ 3 := by omega
  refine census423_of_cyclic_sylow ?_
  rcases hX with hX | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact isCyclic_sylow_of_isSLThreeEpsAt hp3' hX fun h => hSL (Or.inl ⟨_, h⟩)
  · have hq : p ^ e % 3 = 2 := by
      have h0 : p ^ e % 3 ≠ 0 := by
        intro h0
        have h3 : 3 ∣ p ^ e := Nat.dvd_of_mod_eq_zero h0
        exact hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
          (Nat.prime_three.dvd_of_dvd_pow h3)).symm
      have : p ^ e % 3 ≠ 1 := fun h1 => hSL (Or.inr ⟨p, e, hp, he, Or.inl ⟨h1, ⟨φ⟩⟩⟩)
      omega
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega)
      (Or.inr ⟨hq, ⟨φ⟩⟩)
  · have hq : p ^ e % 3 = 1 := by
      have h0 : p ^ e % 3 ≠ 0 := by
        intro h0
        have h3 : 3 ∣ p ^ e := Nat.dvd_of_mod_eq_zero h0
        exact hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
          (Nat.prime_three.dvd_of_dvd_pow h3)).symm
      have : p ^ e % 3 ≠ 2 := fun h1 => hSL (Or.inr ⟨p, e, hp, he, Or.inr ⟨h1, ⟨φ⟩⟩⟩)
      omega
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega)
      (Or.inl ⟨hq, ⟨φ⟩⟩)

theorem k423Inner46Six_of (hR : K423Inner46SixRest) :
    K423Inner46Six := by
  intro X _ _ hX hq hZ hSL
  have h2 : ∀ n : ℕ, (2 ^ n) % 3 ≠ 0 := fun n h0 => by
    have h3 : 3 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h0
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  rcases hX with
      ⟨⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨f, hf | hf | hf | hf | hf⟩⟩ |
      ⟨n, hn, hX⟩
  ·
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      exact census423_of_not_nine_dvd (not_nine_dvd_card_of_projSL_two_two φ)
    · refine census423_of_cyclic_sylow (isCyclic_sylow_of_projSL_two (by norm_num) hn ?_ φ)
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  · refine census423_of_cyclic_sylow ?_
    have hq : 2 ^ n % 3 = 2 := by
      have : 2 ^ n % 3 ≠ 1 := fun h1 => hSL (Or.inr ⟨2, n, ⟨Nat.prime_two⟩, hn,
        Or.inl ⟨h1, ⟨φ⟩⟩⟩)
      have := h2 n
      omega
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega)
      (Or.inr ⟨hq, ⟨φ⟩⟩)
  · refine census423_of_cyclic_sylow ?_
    have hq : 2 ^ n % 3 = 1 := by
      have : 2 ^ n % 3 ≠ 2 := fun h1 => hSL (Or.inr ⟨2, n, ⟨Nat.prime_two⟩, hn,
        Or.inr ⟨h1, ⟨φ⟩⟩⟩)
      have := h2 n
      omega
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega)
      (Or.inl ⟨hq, ⟨φ⟩⟩)
  · exact hR X (Or.inl ⟨n, hn, Or.inl ⟨φ⟩⟩) hq hZ hSL
  · exact hR X (Or.inl ⟨n, hn, Or.inr ⟨φ⟩⟩) hq hZ hSL
  · exact hR X (Or.inr ⟨f, Or.inl hf⟩) hq hZ hSL
  · exact hR X (Or.inr ⟨f, Or.inr (Or.inl hf)⟩) hq hZ hSL
  · refine census423_of_not_nine_dvd fun h9 => ?_
    exact ThinCatalog.not_three_dvd_card_of_suzukiModel hf ((show 3 ∣ 9 by norm_num).trans h9)
  · exact hR X (Or.inr ⟨f, Or.inr (Or.inr (Or.inl hf))⟩) hq hZ hSL
  · exact hR X (Or.inr ⟨f, Or.inr (Or.inr (Or.inr hf))⟩) hq hZ hSL
  · exact census423_of_cyclic_sylow (isCyclic_sylow_of_isSLThreeEpsAt (by norm_num) hX
      fun h => hSL (Or.inl ⟨_, h⟩))

end CFSG.RankThree.PartTwo.Sec4

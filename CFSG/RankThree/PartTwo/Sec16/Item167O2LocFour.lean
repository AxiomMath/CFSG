module

public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec13.Notation
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KSListsProofArith
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec16.Item166Res4ProofOrders

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace Proof167Four

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.Assembly.RankThreeEven
open scoped commutatorElement

@[expose] def Small44 (n : ℕ) : Prop :=
  (∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ n ∧ n ∣ r * (r ^ 2 - 1)) ∨ n ∣ 5616 ∨ n ∣ 92160

private theorem card_Q8D8_dvd : Nat.card Q8D8 ∣ 64 := by
  have h := Subgroup.card_quotient_dvd_card q8D8Kernel
  have hQ : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hD : Nat.card (DihedralGroup 4) = 8 := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hcard : Nat.card (QuaternionGroup 2 × DihedralGroup 4) = 64 := by
    rw [Nat.card_prod, hQ, hD]
  rwa [hcard] at h

private theorem card_Z4Q8Q8_dvd : Nat.card Z4Q8Q8 ∣ 256 := by
  have h := Subgroup.card_quotient_dvd_card z4Q8Q8Kernel
  have hZ : Nat.card (Multiplicative (ZMod 4)) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hQ : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcard :
      Nat.card (Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2) = 256 := by
    rw [Nat.card_prod, Nat.card_prod, hZ, hQ]
  rwa [hcard] at h

private theorem small44_of_case2 {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {θ : Subgroup X} [θ.Normal] [IsSimpleGroup (X ⧸ θ)] (hθsolv : Group.IsSolvable θ)
    (h2 : Nonempty (X ⧸ oTwoFitting X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) :
    Small44 (Nat.card (X ⧸ θ)) := by
  obtain ⟨e2⟩ := h2
  let N : Subgroup X := oTwoFitting X
  have hNn : N.Normal := oTwoFitting_normal X
  haveI : N.Normal := hNn
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hJq : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
    isQuasisimple_SL2 (p := 5) (by norm_num)
  have hnt : Nontrivial (X ⧸ N) := by
    haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hJq
    exact e2.surjective.nontrivial
  have hle : N ≤ θ := le_of_nontrivial_quotient hθsolv hnt
  have hc : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) = 2 :=
    card_center_SL2 (p := 5) (by norm_num)
  have hmult := card_quotient_mul_card_center (X := X) (K := θ) (N := N) hθsolv hle hJq e2
  rw [hc, card_SL2] at hmult
  have h120 : Nat.card (X ⧸ θ) * 2 = 120 := by simpa using hmult
  have hdvd : Nat.card (X ⧸ θ) ∣ 92160 := by
    have hd : Nat.card (X ⧸ θ) ∣ 120 := ⟨2, by omega⟩
    exact hd.trans (by norm_num)
  exact Or.inr (Or.inr hdvd)

private theorem small44_of_case3 {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {θ : Subgroup X} [θ.Normal] [IsSimpleGroup (X ⧸ θ)] (hθsolv : Group.IsSolvable θ)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h3 : Nonempty (X ⧸ oTwoP p X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :
    Small44 (Nat.card (X ⧸ θ)) := by
  obtain ⟨e3⟩ := h3
  let N : Subgroup X := oTwoP p X
  have hNn : N.Normal := oTwoP_normal p X
  haveI : N.Normal := hNn
  have hp5 : 5 ≤ p := by
    have hp3' : 3 ≤ p := by omega
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hJq : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    isQuasisimple_SL2 (p := p) (by omega)
  have hnt : Nontrivial (X ⧸ N) := by
    haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hJq
    exact e3.surjective.nontrivial
  have hle : N ≤ θ := le_of_nontrivial_quotient hθsolv hnt
  have hc : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = 2 :=
    card_center_SL2 (p := p) (by omega)
  have hmult := card_quotient_mul_card_center (X := X) (K := θ) (N := N) hθsolv hle hJq e3
  rw [hc, card_SL2] at hmult
  have hmult' : Nat.card (X ⧸ θ) * 2 = p * (p ^ 2 - 1) := by simpa using hmult
  have hpn : p ∣ Nat.card (X ⧸ θ) := by
    have hp_dvd : p ∣ Nat.card (X ⧸ θ) * 2 := by
      rw [hmult']
      exact dvd_mul_right p _
    rcases (Nat.Prime.dvd_mul hp).mp hp_dvd with h | h
    · exact h
    · exfalso
      have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
      omega
  have hdvd : Nat.card (X ⧸ θ) ∣ p * (p ^ 2 - 1) := ⟨2, by omega⟩
  exact Or.inl ⟨p, hp, hp3, hpn, hdvd⟩

private theorem small44_of_case4 {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {θ : Subgroup X} [θ.Normal] [IsSimpleGroup (X ⧸ θ)] (hθsolv : Group.IsSolvable θ)
    (h4 : Nonempty (X ⧸ oTwoP 3 X ≃* projSL 3 (GaloisField 3 1)) ∨
      IsExtOf (X ⧸ oTwoP 3 X) (alternatingGroup (Fin 5)) Q8D8) :
    Small44 (Nat.card (X ⧸ θ)) := by
  let N : Subgroup X := oTwoP 3 X
  have hNn : N.Normal := oTwoP_normal 3 X
  haveI : N.Normal := hNn
  have hnt : Nontrivial (X ⧸ N) := by
    rcases h4 with hleft | hext
    · obtain ⟨e4⟩ := hleft
      have hcard : Nat.card (X ⧸ N) = 5616 := by
        rw [Nat.card_congr e4.toEquiv, ← Nat.card_congr sl3EquivProjSL.toEquiv,
          card_SL3_three]
      have hnt' : 1 < Nat.card (X ⧸ N) := by rw [hcard]; norm_num
      exact Finite.one_lt_card_iff_nontrivial.mp hnt'
    · obtain ⟨K, hK, hrest⟩ := hext
      obtain ⟨-, hA⟩ := hrest
      obtain ⟨eA⟩ := hA
      haveI : K.Normal := hK
      haveI : Nontrivial (alternatingGroup (Fin 5)) :=
        (alternatingGroup.isSimpleGroup (by simp)).toNontrivial
      exact (eA.surjective.comp (QuotientGroup.mk'_surjective K)).nontrivial
  have hle : N ≤ θ := le_of_nontrivial_quotient hθsolv hnt
  have hdiv : Nat.card (X ⧸ θ) ∣ Nat.card (X ⧸ N) := Subgroup.index_dvd_of_le hle
  rcases h4 with hleft | hext
  · obtain ⟨e4⟩ := hleft
    have hcard : Nat.card (X ⧸ N) = 5616 := by
      rw [Nat.card_congr e4.toEquiv, ← Nat.card_congr sl3EquivProjSL.toEquiv,
        card_SL3_three]
    have hd : Nat.card (X ⧸ N) ∣ 5616 := ⟨1, by omega⟩
    exact Or.inr (Or.inl (hdiv.trans hd))
  · have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
      KFacts.KS14.card_alternatingGroup_five_seven_ten.1
    have hcard : Nat.card (X ⧸ N) = 60 * Nat.card Q8D8 := by
      rw [KFacts.L34.card_of_isExtOf hext, hcardA5]
    have hdvd : Nat.card (X ⧸ N) ∣ 92160 := by
      rw [hcard]
      exact (mul_dvd_mul_left 60 card_Q8D8_dvd).trans (by norm_num)
    exact Or.inr (Or.inr (hdiv.trans hdvd))

private theorem small44_of_oddCore_ext {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {θ : Subgroup X} [θ.Normal] [IsSimpleGroup (X ⧸ θ)] (hθsolv : Group.IsSolvable θ)
    {A B : Type} [Group A] [Group B] (hA : IsSimpleGroup A)
    (hAcard : Nat.card A = 60 ∨ Nat.card A = 360) (hBcard : Nat.card B ∣ 256)
    (h : IsExtOf (X ⧸ CFSG.oddCore X) A B) : Small44 (Nat.card (X ⧸ θ)) := by
  have hcardExt := KFacts.L34.card_of_isExtOf h
  obtain ⟨K, hK, -, ⟨eA⟩⟩ := h
  haveI : K.Normal := hK
  haveI : Nontrivial A := hA.toNontrivial
  have hntO : Nontrivial (X ⧸ CFSG.oddCore X) :=
    (eA.surjective.comp (QuotientGroup.mk'_surjective K)).nontrivial
  have hOle : CFSG.oddCore X ≤ θ :=
    le_of_nontrivial_quotient (X := X) (K := θ) (N := CFSG.oddCore X) hθsolv hntO
  have hdiv : Nat.card (X ⧸ θ) ∣ Nat.card (X ⧸ CFSG.oddCore X) :=
    Subgroup.index_dvd_of_le hOle
  have hdvd : Nat.card (X ⧸ CFSG.oddCore X) ∣ 92160 := by
    rw [hcardExt]
    rcases hAcard with h' | h' <;> rw [h']
    · exact (mul_dvd_mul_left 60 hBcard).trans (by norm_num)
    · exact (mul_dvd_mul_left 360 hBcard).trans (by norm_num)
  exact Or.inr (Or.inr (hdiv.trans hdvd))

theorem commutator_theta_le_oddCore_or_small44 (h44 : Sec4.Item4_4) {X : Type} [Group X]
    [Finite X] (hS4 : SectionFourHyp X) (hXp : Group.IsPerfect X)
    (hXs : IsSimpleGroup (X ⧸ aschbacherSolvableCore 3 X)) (hO2 : CFSG.pCore 2 X = ⊥) :
    ⁅aschbacherSolvableCore 3 X, (⊤ : Subgroup X)⁆ ≤ CFSG.oddCore X ∨
      Small44 (Nat.card (X ⧸ aschbacherSolvableCore 3 X)) := by
  haveI : Group.IsPerfect X := hXp
  set θ := aschbacherSolvableCore 3 X with hθdef
  set O := CFSG.oddCore X with hOdef
  have hXs' : IsSimpleGroup (X ⧸ θ) := by simpa [hθdef] using hXs
  haveI : IsSimpleGroup (X ⧸ θ) := hXs'
  have hθn : θ.Normal := by simpa [hθdef] using aschbacherSolvableCore_normal 3 X
  haveI : θ.Normal := hθn
  have hθsolv : Group.IsSolvable θ := by
    simpa [hθdef] using
      (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).1
  have hθ3 : ¬ 3 ∣ Nat.card θ := by
    simpa [hθdef] using
      (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.1
  have hθnotop : θ ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (X ⧸ θ) := htop ▸ QuotientGroup.subsingleton_quotient_top
    haveI : Nontrivial (X ⧸ θ) := hXs'.toNontrivial
    exact not_subsingleton (X ⧸ θ) hsub
  have h44' := h44 X hS4 hXp θ hθsolv hXs'
  rcases h44' with h1 | h2 | ⟨p, hp, hp3, h3⟩ | h4 | ⟨-, h5⟩
  ·
    have h1' : IsQuasisimple (X ⧸ (⊥ : Subgroup X)) :=
      h1.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hO2.symm)
    have hXq : IsQuasisimple X := h1'.of_mulEquiv QuotientGroup.quotientBot.symm
    have hθcenter : θ ≤ Subgroup.center X := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq hθn with htop | hcenter
      · exact absurd htop hθnotop
      · exact hcenter
    refine Or.inl ?_
    calc
      ⁅θ, (⊤ : Subgroup X)⁆ ≤ ⁅Subgroup.center X, (⊤ : Subgroup X)⁆ :=
        Subgroup.commutator_mono hθcenter le_rfl
      _ = ⊥ := Subgroup.commutator_center_left (⊤ : Subgroup X)
      _ ≤ O := bot_le
  ·
    exact Or.inr (small44_of_case2 hθsolv h2)
  ·
    exact Or.inr (small44_of_case3 hθsolv hp hp3 h3)
  ·
    exact Or.inr (small44_of_case4 hθsolv h4)
  ·
    have h5' := h5 hθ3
    have hOn : O.Normal := by simpa [hOdef] using CFSG.oddCore_normal (G := X)
    haveI : O.Normal := hOn
    have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
      KFacts.KS14.card_alternatingGroup_five_seven_ten.1
    have hcardA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
      norm_num
    rcases h5' with ⟨-, hinner⟩ | ⟨-, hinner⟩
    · rcases hinner with hq | hext
      ·
        have hntO : Nontrivial (X ⧸ O) := CFSG.LocalCores.isQuasisimple_nontrivial hq
        have hOle : O ≤ θ :=
          le_of_nontrivial_quotient (X := X) (K := θ) (N := O) hθsolv hntO
        have himg : (θ.map (QuotientGroup.mk' O)).Normal :=
          Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
        rcases CFSG.LocalCores.quasisimple_normal_subgroups hq himg with htop | hcenter
        · exfalso
          have hsurj : Function.Surjective ((QuotientGroup.mk' O).comp θ.subtype) := by
            rw [← MonoidHom.range_eq_top]
            have hrange : MonoidHom.range ((QuotientGroup.mk' O).comp θ.subtype) =
                θ.map (QuotientGroup.mk' O) := by
              ext x
              constructor
              · rintro ⟨a, rfl⟩
                exact ⟨a, a.2, rfl⟩
              · rintro ⟨a, ha, rfl⟩
                exact ⟨⟨a, ha⟩, rfl⟩
            rw [hrange, htop]
          haveI : Group.IsSolvable θ := hθsolv
          haveI : Group.IsPerfect (X ⧸ O) := hq.1
          exact (Group.IsPerfect.not_isSolvable (X ⧸ O))
            (Group.isSolvable_of_surjective hsurj)
        · refine Or.inl ?_
          refine Subgroup.commutator_le.mpr ?_
          intro a ha b hb
          have hain : QuotientGroup.mk' O a ∈ Subgroup.center (X ⧸ O) :=
            hcenter (Subgroup.mem_map_of_mem (QuotientGroup.mk' O) ha)
          have hcomm : ⁅(QuotientGroup.mk' O a), (QuotientGroup.mk' O b)⁆ = 1 := by
            rw [commutatorElement_eq_one_iff_mul_comm]
            exact (Subgroup.mem_center_iff.mp hain (QuotientGroup.mk' O b)).symm
          have hmap : QuotientGroup.mk' O ⁅a, b⁆ = 1 := by
            rw [map_commutatorElement, hcomm]
          exact (QuotientGroup.eq_one_iff _).mp hmap
      · exact Or.inr (small44_of_oddCore_ext (A := alternatingGroup (Fin 5)) (B := Q8D8)
          hθsolv (alternatingGroup.isSimpleGroup (by simp)) (Or.inl hcardA5)
          (card_Q8D8_dvd.trans (by norm_num)) hext)
    · rcases hinner with hext1 | hext2 | hext3
      · exact Or.inr (small44_of_oddCore_ext (A := alternatingGroup (Fin 5)) (B := Q8D8)
          hθsolv (alternatingGroup.isSimpleGroup (by simp)) (Or.inl hcardA5)
          (card_Q8D8_dvd.trans (by norm_num)) hext1)
      · exact Or.inr (small44_of_oddCore_ext (A := alternatingGroup (Fin 5)) (B := Z4Q8Q8)
          hθsolv (alternatingGroup.isSimpleGroup (by simp)) (Or.inl hcardA5)
          card_Z4Q8Q8_dvd hext2)
      · exact Or.inr (small44_of_oddCore_ext (A := alternatingGroup (Fin 6)) (B := Z4Q8Q8)
          hθsolv (alternatingGroup.isSimpleGroup (by simp)) (Or.inr hcardA6)
          card_Z4Q8Q8_dvd hext3)

theorem isQuasisimple_or_pRank_le_three_or_small44 (h44 : Sec4.Item4_4) {X : Type} [Group X]
    [Finite X] (hS4 : SectionFourHyp X) (hXp : Group.IsPerfect X)
    (hXs : IsSimpleGroup (X ⧸ aschbacherSolvableCore 3 X)) (hO2 : CFSG.pCore 2 X = ⊥) :
    IsQuasisimple X ∨ CFSG.Open.pRank 2 (⊤ : Subgroup X) ≤ 3 ∨
      Small44 (Nat.card (X ⧸ aschbacherSolvableCore 3 X)) := by
  haveI : Group.IsPerfect X := hXp
  set θ := aschbacherSolvableCore 3 X with hθdef
  have hXs' : IsSimpleGroup (X ⧸ θ) := by simpa [hθdef] using hXs
  haveI : IsSimpleGroup (X ⧸ θ) := hXs'
  have hθn : θ.Normal := by simpa [hθdef] using aschbacherSolvableCore_normal 3 X
  haveI : θ.Normal := hθn
  have hθsolv : Group.IsSolvable θ := by
    simpa [hθdef] using
      (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).1
  have hθ3 : ¬ 3 ∣ Nat.card θ := by
    simpa [hθdef] using
      (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.1
  have h44' := h44 X hS4 hXp θ hθsolv hXs'
  rcases h44' with h1 | h2 | ⟨p, hp, hp3, h3⟩ | h4 | ⟨-, h5⟩
  ·
    have h1' : IsQuasisimple (X ⧸ (⊥ : Subgroup X)) :=
      h1.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hO2.symm)
    exact Or.inl (h1'.of_mulEquiv QuotientGroup.quotientBot.symm)
  ·
    exact Or.inr (Or.inr (small44_of_case2 hθsolv h2))
  ·
    exact Or.inr (Or.inr (small44_of_case3 hθsolv hp hp3 h3))
  ·
    exact Or.inr (Or.inr (small44_of_case4 hθsolv h4))
  ·
    have h5' := h5 hθ3
    have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
      KFacts.KS14.card_alternatingGroup_five_seven_ten.1
    have hcardA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
      norm_num
    rcases h5' with ⟨hrank, hinner⟩ | ⟨hrank, hinner⟩
    · rcases hinner with hq | hext
      ·
        refine Or.inr (Or.inl ?_)
        omega
      · exact Or.inr (Or.inr (small44_of_oddCore_ext (A := alternatingGroup (Fin 5)) (B := Q8D8)
          hθsolv (alternatingGroup.isSimpleGroup (by simp)) (Or.inl hcardA5)
          (card_Q8D8_dvd.trans (by norm_num)) hext))
    · rcases hinner with hext1 | hext2 | hext3
      · exact Or.inr (Or.inr (small44_of_oddCore_ext (A := alternatingGroup (Fin 5)) (B := Q8D8)
          hθsolv (alternatingGroup.isSimpleGroup (by simp)) (Or.inl hcardA5)
          (card_Q8D8_dvd.trans (by norm_num)) hext1))
      · exact Or.inr (Or.inr (small44_of_oddCore_ext (A := alternatingGroup (Fin 5)) (B := Z4Q8Q8)
          hθsolv (alternatingGroup.isSimpleGroup (by simp)) (Or.inl hcardA5)
          card_Z4Q8Q8_dvd hext2))
      · exact Or.inr (Or.inr (small44_of_oddCore_ext (A := alternatingGroup (Fin 6)) (B := Z4Q8Q8)
          hθsolv (alternatingGroup.isSimpleGroup (by simp)) (Or.inr hcardA6)
          card_Z4Q8Q8_dvd hext3))

theorem not_small44_of_eq {n : ℕ}
    (hn : n = 2520 ∨ n = 95040 ∨ n = 443520 ∨ n = 604800 ∨ n = 1814400) :
    ¬ Small44 n := by
  have key : ∀ r : ℕ, r.Prime → r ∣ 2 ^ 7 * (3 ^ 4 * (5 ^ 2 * (7 ^ 1 * 11 ^ 1))) →
      r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 11 := by
    intro r hr h
    rcases hr.dvd_mul.mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow hr h))
    rcases hr.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
        (Nat.Prime.dvd_of_dvd_pow hr h)))
    rcases hr.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp
        (Nat.Prime.dvd_of_dvd_pow hr h))))
    rcases hr.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_seven).mp
          (Nat.Prime.dvd_of_dvd_pow hr h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_eleven).mp
          (Nat.Prime.dvd_of_dvd_pow hr h)))))
  rintro (⟨r, hrprime, hr3, hrdvd, hndvd⟩ | h5616 | h92160)
  · have hMn : n ∣ 19958400 := by
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hrM : r ∣ 19958400 := hrdvd.trans hMn
    have hfac : 19958400 = 2 ^ 7 * (3 ^ 4 * (5 ^ 2 * (7 ^ 1 * 11 ^ 1))) := by
      norm_num
    have hmem := key r hrprime (by rwa [hfac] at hrM)
    have hrle : r * (r ^ 2 - 1) ≤ 1320 := by
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hrpos : 0 < r * (r ^ 2 - 1) := by
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hnle : n ≤ r * (r ^ 2 - 1) := Nat.le_of_dvd hrpos hndvd
    have hngt : 1320 < n := by
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> norm_num
    omega
  · rcases hn with rfl | rfl | rfl | rfl | rfl <;> norm_num at h5616
  · rcases hn with rfl | rfl | rfl | rfl | rfl <;> norm_num at h92160

theorem not_small44_card_of_isoLThreePi {X : Type} [Group X] [Finite X] {p e : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) (h : Sec4.IsoLThreePi X p e) :
    ¬ Small44 (Nat.card X) := by
  have hp : p.Prime := Fact.out
  set q := p ^ e with hqdef
  set n := Nat.card X with hndef
  have hqmod : q % 3 = 1 ∨ q % 3 = 2 := by
    rcases h with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact Or.inl h1
    · exact Or.inr h2
  have hq3 : q % 3 ≠ 0 := by omega
  have hpne3 : p ≠ 3 := by
    intro h3
    apply hq3
    rw [hqdef, h3]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 3 (by omega))
  have hp5 : 5 ≤ p := by
    have hp3 : 3 ≤ p := by
      have h2 : 2 ≤ p := hp.two_le
      omega
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    omega
  have hq5 : 5 ≤ q := le_trans hp5 (Nat.le_self_pow (by omega) p)
  have hq3bound : 5 * q ^ 2 ≤ q ^ 3 := by
    calc 5 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hq5
      _ = q ^ 3 := by ring
  obtain ⟨A, hA, h3n⟩ : ∃ A : ℕ,
      (A = (q ^ 2 - 1) * (q ^ 3 - 1) ∨ A = (q ^ 2 - 1) * (q ^ 3 + 1)) ∧
        3 * n = q ^ 3 * A := by
    rcases Proof166Res4.three_mul_card_of_isoLThreePi (X := X) he h with h | h
    · exact ⟨_, Or.inl rfl, by simpa [n, q] using h⟩
    · exact ⟨_, Or.inr rfl, by simpa [n, q] using h⟩
  have hq3ge : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
  have hq2sub : 24 ≤ q ^ 2 - 1 := by
    have h25 : 25 ≤ q ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
    omega
  have hq3sub : 124 ≤ q ^ 3 - 1 := by omega
  have hAge : 2976 ≤ A := by
    rcases hA with rfl | rfl
    · calc 2976 = 24 * 124 := by norm_num
        _ ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.mul_le_mul hq2sub hq3sub
    · have hq3add : 124 ≤ q ^ 3 + 1 := by omega
      calc 2976 = 24 * 124 := by norm_num
        _ ≤ (q ^ 2 - 1) * (q ^ 3 + 1) := Nat.mul_le_mul hq2sub hq3add
  have hbig : 92160 < n := by
    have h3n' : 3 * n = q ^ 3 * A := h3n
    have hlt : 3 * 92160 < 3 * n := by
      calc 3 * 92160 = 276480 := by norm_num
        _ < 125 * 2976 := by norm_num
        _ ≤ q ^ 3 * A := Nat.mul_le_mul hq3ge hAge
        _ = 3 * n := h3n'.symm
    omega
  have hq3dvdn : q ^ 3 ∣ n := by
    have hcop : Nat.Coprime (q ^ 3) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by
        intro hd
        exact hq3 (Nat.dvd_iff_mod_eq_zero.mp (Nat.prime_three.dvd_of_dvd_pow hd)))).symm
    have hd : q ^ 3 ∣ 3 * n := by
      rw [h3n]
      exact dvd_mul_right _ _
    exact hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using hd)
  rintro (⟨r, hrprime, hr3, hrn, hndvd⟩ | h5616 | h92160)
  · have hq3_dvd_rr : q ^ 3 ∣ r * (r ^ 2 - 1) := hq3dvdn.trans hndvd
    have hrne : r ≠ p := by
      intro hrp
      have hp3dvdq3 : p ^ 3 ∣ q ^ 3 := by
        rw [hqdef, ← pow_mul]
        exact pow_dvd_pow p (by omega : 3 ≤ e * 3)
      have hp3dvd : p ^ 3 ∣ p * (p ^ 2 - 1) :=
        hp3dvdq3.trans (by rwa [hrp] at hq3_dvd_rr)
      have hmul : p * p ^ 2 ∣ p * (p ^ 2 - 1) := by
        rwa [show p ^ 3 = p * p ^ 2 by ring] at hp3dvd
      have hp2dvd : p ^ 2 ∣ p ^ 2 - 1 := (Nat.mul_dvd_mul_iff_left hp.pos).mp hmul
      have hpos : 0 < p ^ 2 - 1 := by
        have : 1 < p ^ 2 := by nlinarith [hp.two_le]
        omega
      have hle := Nat.le_of_dvd hpos hp2dvd
      omega
    have hr_not_dvd_q : ¬ r ∣ q := by
      intro hrd
      have hrdp : r ∣ p := by
        have : r ∣ p ^ e := by simpa [hqdef] using hrd
        exact Nat.Prime.dvd_of_dvd_pow hrprime this
      exact hrne ((Nat.prime_dvd_prime_iff_eq hrprime hp).mp hrdp)
    have hcop : Nat.Coprime (q ^ 3) r := by
      refine Nat.Coprime.pow_left 3 ?_
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hrprime).mpr hr_not_dvd_q
    have hq3_dvd_r2sub : q ^ 3 ∣ r ^ 2 - 1 := by
      have hd : q ^ 3 ∣ (r ^ 2 - 1) * r := by simpa [mul_comm] using hq3_dvd_rr
      exact hcop.dvd_of_dvd_mul_right hd
    have hpq3 : q ^ 3 = p ^ (3 * e) := by
      rw [hqdef, ← pow_mul]
      congr 1
      omega
    have hr2sub : r ^ 2 - 1 = (r - 1) * (r + 1) := by
      have h : r ^ 2 = (r - 1) * (r + 1) + 1 := by
        obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        rw [hk]
        simp only [Nat.add_sub_cancel]
        ring
      omega
    have hp3e_dvd : p ^ (3 * e) ∣ (r - 1) * (r + 1) := by
      rwa [hr2sub, hpq3] at hq3_dvd_r2sub
    have hsplit : p ^ (3 * e) ∣ r - 1 ∨ p ^ (3 * e) ∣ r + 1 := by
      by_cases hpdiv : p ∣ r + 1
      · right
        have hpnot : ¬ p ∣ r - 1 := by
          intro hd
          have h2 : p ∣ (r + 1) - (r - 1) := Nat.dvd_sub hpdiv hd
          have h2eq : (r + 1) - (r - 1) = 2 := by omega
          rw [h2eq] at h2
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
        have hcop' : Nat.Coprime (p ^ (3 * e)) (r - 1) :=
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpnot).pow_left (3 * e)
        exact hcop'.dvd_of_dvd_mul_left hp3e_dvd
      · left
        have hcop' : Nat.Coprime (p ^ (3 * e)) (r + 1) :=
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpdiv).pow_left (3 * e)
        exact hcop'.dvd_of_dvd_mul_right hp3e_dvd
    have hr_ge : q ^ 3 - 1 ≤ r := by
      rcases hsplit with hd | hd
      · have hle : p ^ (3 * e) ≤ r - 1 := Nat.le_of_dvd (by omega) hd
        rw [← hpq3] at hle
        omega
      · have hle : p ^ (3 * e) ≤ r + 1 := Nat.le_of_dvd (by omega) hd
        rw [← hpq3] at hle
        omega
    have hr_gt : q + 1 < r := by
      have hq3gt : q + 2 < q ^ 3 := by nlinarith [hq3bound, hq5]
      have hq3gt' : q + 1 < q ^ 3 - 1 := by omega
      omega
    have hr_dvd_3n : r ∣ 3 * n := hrn.mul_left 3
    have hr_dvd_prod : r ∣ q ^ 3 * A := by rwa [h3n] at hr_dvd_3n
    have hr_dvd_A : r ∣ A := (hcop.symm).dvd_of_dvd_mul_left hr_dvd_prod
    have hr_not_dvd_q2sub : ¬ r ∣ q ^ 2 - 1 := by
      intro hd
      have hq2eq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        have h : q ^ 2 = (q - 1) * (q + 1) + 1 := by
          obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
          rw [hk]
          simp only [Nat.add_sub_cancel]
          ring
        omega
      rw [hq2eq] at hd
      rcases (hrprime.dvd_mul).mp hd with h | h
      · have hle := Nat.le_of_dvd (by omega : 0 < q - 1) h
        omega
      · have hle := Nat.le_of_dvd (by omega : 0 < q + 1) h
        omega
    have hr_dvd_q3sub : r ∣ q ^ 3 - 1 ∨ r ∣ q ^ 3 + 1 := by
      rcases hA with hAeq | hAeq
      · left
        have hd : r ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by rwa [hAeq] at hr_dvd_A
        exact (hrprime.dvd_mul.mp hd).resolve_left hr_not_dvd_q2sub
      · right
        have hd : r ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by rwa [hAeq] at hr_dvd_A
        exact (hrprime.dvd_mul.mp hd).resolve_left hr_not_dvd_q2sub
    have hr_le : r ≤ q ^ 2 + q + 1 := by
      rcases hr_dvd_q3sub with hd | hd
      · have hq3subeq : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
          have h : q ^ 3 = (q - 1) * (q ^ 2 + q + 1) + 1 := by
            obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
            rw [hk]
            simp only [Nat.add_sub_cancel]
            ring
          omega
        have hd' : r ∣ (q - 1) * (q ^ 2 + q + 1) := by rwa [hq3subeq] at hd
        have hr_not_dvd_qsub : ¬ r ∣ q - 1 := by
          intro hd''
          have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hd''
          omega
        have hd'' : r ∣ q ^ 2 + q + 1 :=
          (hrprime.dvd_mul.mp hd').resolve_left hr_not_dvd_qsub
        exact Nat.le_of_dvd (by positivity) hd''
      · have hq3addeq : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
          obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
          rw [hk]
          have hsub : (k + 1) ^ 2 - (k + 1) = k * (k + 1) := by
            have h : (k + 1) ^ 2 = k * (k + 1) + (k + 1) := by ring
            omega
          rw [hsub]
          ring
        have hd' : r ∣ (q + 1) * (q ^ 2 - q + 1) := by rwa [hq3addeq] at hd
        have hr_not_dvd_qadd : ¬ r ∣ q + 1 := by
          intro hd''
          have hle := Nat.le_of_dvd (by omega : 0 < q + 1) hd''
          omega
        have hd'' : r ∣ q ^ 2 - q + 1 :=
          (hrprime.dvd_mul.mp hd').resolve_left hr_not_dvd_qadd
        have hle := Nat.le_of_dvd (by nlinarith [hq5]) hd''
        omega
    have hq3gt : q ^ 2 + q + 2 < q ^ 3 := by nlinarith [hq3bound, hq5]
    omega
  · have hle : n ≤ 5616 := Nat.le_of_dvd (by norm_num) h5616
    omega
  · have hle : n ≤ 92160 := Nat.le_of_dvd (by norm_num) h92160
    omega

theorem not_small44_card_of_isoLThreePi_two {X : Type} [Group X] [Finite X] {e : ℕ} (he : 2 ≤ e)
    (h : Sec4.IsoLThreePi X 2 e) : ¬ Small44 (Nat.card X) := by
  set q := 2 ^ e with hqdef
  set n := Nat.card X with hndef
  obtain ⟨A, hA, h3n⟩ : ∃ A : ℕ,
      (A = (q ^ 2 - 1) * (q ^ 3 - 1) ∨ A = (q ^ 2 - 1) * (q ^ 3 + 1)) ∧
        3 * n = q ^ 3 * A := by
    rcases Proof166Res4.three_mul_card_of_isoLThreePi (X := X) (p := 2) (by omega) h with h | h
    · exact ⟨_, Or.inl rfl, by simpa [n, q] using h⟩
    · exact ⟨_, Or.inr rfl, by simpa [n, q] using h⟩
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hq3pow : q ^ 3 = 2 ^ (3 * e) := by rw [hqdef, ← pow_mul, mul_comm]
  have hcop3 : Nat.Coprime (q ^ 3) 3 := by
    rw [hq3pow]
    exact Nat.Coprime.pow_left (3 * e) (by norm_num : Nat.Coprime 2 3)
  have hq3dvdn : q ^ 3 ∣ n := by
    have hd : q ^ 3 ∣ 3 * n := by
      rw [h3n]
      exact dvd_mul_right _ _
    exact hcop3.dvd_of_dvd_mul_right (by simpa [mul_comm] using hd)
  rintro (⟨r, hrprime, hr3, hrn, hndvd⟩ | h5616 | h92160)
  ·
    have hrodd : Odd r := hrprime.odd_of_ne_two (by omega)
    have hr_not_dvd_q : ¬ r ∣ q := by
      intro hrd
      have hrd2 : r ∣ 2 := by
        have : r ∣ 2 ^ e := by simpa [hqdef] using hrd
        exact hrprime.dvd_of_dvd_pow this
      have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) hrd2
      omega
    have hcop : Nat.Coprime (q ^ 3) r := by
      refine Nat.Coprime.pow_left 3 ?_
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hrprime).mpr hr_not_dvd_q
    have hq3_dvd_r2sub : q ^ 3 ∣ r ^ 2 - 1 := by
      have hd : q ^ 3 ∣ r * (r ^ 2 - 1) := hq3dvdn.trans hndvd
      exact hcop.dvd_of_dvd_mul_left hd
    have hr2sub : r ^ 2 - 1 = (r - 1) * (r + 1) := by
      have h' : r ^ 2 = (r - 1) * (r + 1) + 1 := by
        obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        rw [hk]
        simp only [Nat.add_sub_cancel]
        ring
      omega
    have h2dvd : 2 ^ (3 * e) ∣ (r - 1) * (r + 1) := by
      rw [← hr2sub, ← hq3pow]
      exact hq3_dvd_r2sub
    have h2dvd' : 2 ^ (3 * e - 1 + 1) ∣ (r - 1) * (r + 1) := by
      rwa [show 3 * e - 1 + 1 = 3 * e by omega]
    have hr_ge : 2 ^ (3 * e - 1) - 1 ≤ r := by
      have hle := Sec11.KSListsProof.two_pow_le_of_dvd_mul_succ hrodd (by omega) h2dvd'
      omega
    have hpow : 2 ^ (3 * e - 1) = q ^ 2 * 2 ^ (e - 1) := by
      have hq2 : q ^ 2 = 2 ^ (2 * e) := by
        rw [hqdef, ← pow_mul]
        congr 1
        omega
      rw [hq2, ← pow_add]
      congr 1
      omega
    have h2e : 2 ≤ 2 ^ (e - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (e - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hqsq : q + 3 ≤ q ^ 2 := by
      calc q + 3 ≤ 4 * q := by omega
        _ ≤ q * q := Nat.mul_le_mul_right q hq4
        _ = q ^ 2 := by ring
    have hbig : q ^ 2 + q + 3 ≤ 2 ^ (3 * e - 1) := by
      rw [hpow]
      nlinarith [h2e, hqsq]
    have hr_gt : q + 1 < r := by omega
    have hr_not_dvd_q2sub : ¬ r ∣ q ^ 2 - 1 := by
      intro hd
      have hq2eq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        have h' : q ^ 2 = (q - 1) * (q + 1) + 1 := by
          obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
          rw [hk]
          simp only [Nat.add_sub_cancel]
          ring
        omega
      rw [hq2eq] at hd
      rcases (hrprime.dvd_mul).mp hd with h' | h'
      · have hle := Nat.le_of_dvd (by omega : 0 < q - 1) h'
        omega
      · have hle := Nat.le_of_dvd (by omega : 0 < q + 1) h'
        omega
    have hr_dvd_3n : r ∣ 3 * n := hrn.mul_left 3
    have hr_dvd_prod : r ∣ q ^ 3 * A := by rwa [h3n] at hr_dvd_3n
    have hr_dvd_A : r ∣ A := (hcop.symm).dvd_of_dvd_mul_left hr_dvd_prod
    have hr_dvd_q3sub : r ∣ q ^ 3 - 1 ∨ r ∣ q ^ 3 + 1 := by
      rcases hA with hAeq | hAeq
      · have hd : r ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by rwa [hAeq] at hr_dvd_A
        exact Or.inl ((hrprime.dvd_mul.mp hd).resolve_left hr_not_dvd_q2sub)
      · have hd : r ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by rwa [hAeq] at hr_dvd_A
        exact Or.inr ((hrprime.dvd_mul.mp hd).resolve_left hr_not_dvd_q2sub)
    have hr_le : r ≤ q ^ 2 + q + 1 := by
      rcases hr_dvd_q3sub with hd | hd
      · have hq3subeq : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
          have h' : q ^ 3 = (q - 1) * (q ^ 2 + q + 1) + 1 := by
            obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
            rw [hk]
            simp only [Nat.add_sub_cancel]
            ring
          omega
        have hd' : r ∣ (q - 1) * (q ^ 2 + q + 1) := by rwa [hq3subeq] at hd
        have hr_not_dvd_qsub : ¬ r ∣ q - 1 := by
          intro hd''
          have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hd''
          omega
        exact Nat.le_of_dvd (by positivity)
          ((hrprime.dvd_mul.mp hd').resolve_left hr_not_dvd_qsub)
      · have hq3addeq : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
          obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
          rw [hk]
          have hsub : (k + 1) ^ 2 - (k + 1) = k * (k + 1) := by
            have h' : (k + 1) ^ 2 = k * (k + 1) + (k + 1) := by ring
            omega
          rw [hsub]
          ring
        have hd' : r ∣ (q + 1) * (q ^ 2 - q + 1) := by rwa [hq3addeq] at hd
        have hr_not_dvd_qadd : ¬ r ∣ q + 1 := by
          intro hd''
          have hle := Nat.le_of_dvd (by omega : 0 < q + 1) hd''
          omega
        have hd'' : r ∣ q ^ 2 - q + 1 := (hrprime.dvd_mul.mp hd').resolve_left hr_not_dvd_qadd
        have hle := Nat.le_of_dvd (by nlinarith [hq4]) hd''
        omega
    omega
  ·
    have hdvd : 2 ^ (3 * e) ∣ 5616 := by
      rw [← hq3pow]
      exact hq3dvdn.trans h5616
    have h2dvd : 2 ^ 6 ∣ 5616 :=
      (Nat.pow_dvd_pow 2 (by omega : 6 ≤ 3 * e)).trans hdvd
    norm_num at h2dvd
  ·
    have hdvd : 2 ^ (3 * e) ∣ 92160 := by
      rw [← hq3pow]
      exact hq3dvdn.trans h92160
    have hcop : Nat.Coprime (2 ^ (3 * e)) 45 :=
      Nat.Coprime.pow_left (3 * e) (by norm_num : Nat.Coprime 2 45)
    have hdvd2 : 2 ^ (3 * e) ∣ 2 ^ 11 := by
      have h45 : 92160 = 2 ^ 11 * 45 := by norm_num
      rw [h45] at hdvd
      exact hcop.dvd_of_dvd_mul_right hdvd
    have he3 : 3 * e ≤ 11 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
        (Nat.le_of_dvd (by positivity) hdvd2)
    have hee : e = 2 ∨ e = 3 := by omega
    rcases hee with rfl | rfl
    ·
      have hn : n = 20160 ∨ n = 20800 := by
        have hq4' : q = 4 := by rw [hqdef]; norm_num
        rw [hq4'] at hA h3n
        rcases hA with h' | h'
        · rw [h'] at h3n
          norm_num at h3n
          omega
        · rw [h'] at h3n
          norm_num at h3n
          omega
      rcases hn with hn1 | hn2
      · rw [hn1] at h92160
        norm_num at h92160
      · rw [hn2] at h92160
        norm_num at h92160
    ·
      have hq8 : q = 8 := by rw [hqdef]; norm_num
      have hAge : 32193 ≤ A := by
        rw [hq8] at hA
        rcases hA with h' | h' <;> rw [h'] <;> norm_num
      have hq3 : q ^ 3 = 512 := by rw [hq8]; norm_num
      have hnle : n ≤ 92160 := Nat.le_of_dvd (by norm_num) h92160
      rw [hq3] at h3n
      omega

theorem not_small44_card (X : Type) [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨ Sec13.IsLThreePi X ∨
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
        Nonempty (X ≃* alternatingGroup (Fin 10)))
    (h2 : ∀ n : ℕ, 1 ≤ n → ¬ Sec4.IsoLThreePi X 2 n) : ¬ Small44 (Nat.card X) := by
  rintro hsmall
  rcases hX with hJ2 | hL3 | hA7 | hM22 | hM12 | hA10
  · obtain ⟨e⟩ := hJ2
    have hcard : Nat.card X = 604800 := by
      rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]
    exact not_small44_of_eq (n := Nat.card X)
      (Or.inr (Or.inr (Or.inr (Or.inl hcard)))) hsmall
  · obtain ⟨p, e, hpf, he, hiso⟩ := hL3
    by_cases hp2 : p = 2
    · exact absurd (hp2 ▸ hiso) (h2 e he)
    · exact not_small44_card_of_isoLThreePi (X := X) hp2 he hiso hsmall
  · obtain ⟨e⟩ := hA7
    have hcard : Nat.card X = 2520 := by
      rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    exact not_small44_of_eq (n := Nat.card X) (Or.inl hcard) hsmall
  · obtain ⟨e⟩ := hM22
    have hcard : Nat.card X = 443520 := by
      rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeM22]
    exact not_small44_of_eq (n := Nat.card X)
      (Or.inr (Or.inr (Or.inl hcard))) hsmall
  · obtain ⟨e⟩ := hM12
    have hcard : Nat.card X = 95040 := by
      rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeM12]
    exact not_small44_of_eq (n := Nat.card X)
      (Or.inr (Or.inl hcard)) hsmall
  · obtain ⟨e⟩ := hA10
    have hcard : Nat.card X = 1814400 := by
      rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2]
    exact not_small44_of_eq (n := Nat.card X)
      (Or.inr (Or.inr (Or.inr (Or.inr hcard)))) hsmall

end Proof167Four

end CFSG.RankThree.PartTwo.Sec16

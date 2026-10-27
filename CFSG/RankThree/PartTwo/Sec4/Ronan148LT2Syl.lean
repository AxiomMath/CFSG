module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCrit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AbelianSylowGL

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp)
open CFSG.Open (StatedSL StatedSp)
open Matrix

theorem noCQ425_of_isCyclic_sylow {S : Type} [Group S] [Finite S]
    (h : ∀ Q : Sylow 3 S, IsCyclic Q) : NoCQ425 S :=
  noCC425_of_abelian_sylow fun P a b ha hb => by
    letI := (h P).commGroup
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : (P : Subgroup S)) ⟨b, hb⟩)

theorem comm_sylow_projImage {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {r : ℕ} [Fact r.Prime]
    (hH : ∀ P : Subgroup H, IsPGroup r P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (Q : Sylow r (projImage H)) :
    ∀ a b : projImage H, a ∈ (Q : Subgroup (projImage H)) → b ∈ (Q : Subgroup (projImage H)) →
      a * b = b * a := by
  let f : ↥H →* ↥(projImage H) := ProjGenLinGroup.mk.subgroupMap H
  have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective _ _
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf r Q
  intro a b ha hb
  rw [Sylow.coe_mapSurjective] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  rw [← map_mul f, ← map_mul f, hH S S.isPGroup' a' ha' b' hb']

theorem comm_of_isPGroup_GL4 {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (P : Subgroup (GL (Fin 4) K)) (hP : IsPGroup 3 P) : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K % 3 = 2 := by rwa [Fintype.card_eq_nat_card]
  have h0 : ¬ 3 ∣ Fintype.card K := by omega
  have hd : 3 ∣ Fintype.card K ^ 2 - 1 := by
    have h1 : 1 ≤ Fintype.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : (Fintype.card K ^ 2 - 1) % 3 = 0 := by
      have hsq : Fintype.card K ^ 2 % 3 = 1 := by
        rw [Nat.pow_mod, hq]
      omega
    exact Nat.dvd_of_mod_eq_zero this
  have hmin : ∀ j, 1 ≤ j → j < 2 → ¬ 3 ∣ Fintype.card K ^ j - 1 := by
    intro j hj1 hj2
    have hj : j = 1 := by omega
    subst hj
    rw [pow_one]
    omega
  have hc := CFSG.AGLEmbeddingD2.AbelianSylowGL.isMulCommutative_of_isPGroup_GL
    (k := K) (r := 3) (by decide) (m := 4) (d := 2) h0 hd hmin (by norm_num) P hP
  intro a ha b hb
  exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

noncomputable def glSumEquiv (K : Type) [Field K] : GL (Fin 2 ⊕ Fin 2) K ≃* GL (Fin 4) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin (2 + 2))).toMulEquiv

theorem sp4_card_fac (n : ℕ) (hn : 1 ≤ n) :
    n ^ 4 * ((n ^ 2 - 1) * (n ^ 4 - 1)) = (n - 1) ^ 2 * (n ^ 4 * ((n + 1) ^ 2 * (n ^ 2 + 1))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 : (m + 1) ^ 2 - 1 = m * (m + 2) := by
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega
  have h4 : (m + 1) ^ 4 - 1 = m * (m + 2) * ((m + 1) ^ 2 + 1) := by
    have : (m + 1) ^ 4 = m * (m + 2) * ((m + 1) ^ 2 + 1) + 1 := by ring
    omega
  rw [h2, h4]
  ring

theorem comm_of_isPGroup_Sp4_mod_one {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 1)
    (P : Subgroup (StatedSp 2 K)) (hP : IsPGroup 3 P) : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set τ := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom (r := 2) (k := K)
  have hτ : Function.Injective τ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom_injective
  set T := τ.range with hT
  haveI : IsMulCommutative T := ⟨⟨by
    rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    apply Subtype.ext
    change τ x * τ y = τ y * τ x
    rw [← map_mul, ← map_mul, mul_comm]⟩⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq4 : 4 ≤ Nat.card K := by omega
  have hcardT : Nat.card T = (Nat.card K - 1) ^ 2 := by
    rw [hT, ← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv, Nat.card_fun, Nat.card_units,
      Nat.card_fin]
  have hcardSp := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two K
  have hindex : ¬ 3 ∣ T.index := by
    have hmul := Subgroup.card_mul_index T
    rw [hcardT, hcardSp, sp4_card_fac _ (by omega)] at hmul
    have hpos : 0 < (Nat.card K - 1) ^ 2 := by
      have : 0 < Nat.card K - 1 := by omega
      positivity
    have hidx : T.index = Nat.card K ^ 4 * ((Nat.card K + 1) ^ 2 * (Nat.card K ^ 2 + 1)) :=
      Nat.eq_of_mul_eq_mul_left hpos hmul
    rw [hidx]
    intro h3
    have hq3 : ¬ 3 ∣ Nat.card K := by omega
    have h1 : ¬ 3 ∣ Nat.card K + 1 := by omega
    have h2 : ¬ 3 ∣ Nat.card K ^ 2 + 1 := by
      intro h
      have : (Nat.card K ^ 2 + 1) % 3 = 2 := by
        rw [Nat.add_mod, Nat.pow_mod, hK]
      omega
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hq3 (Nat.prime_three.dvd_of_dvd_pow h)
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · exact h1 (Nat.prime_three.dvd_of_dvd_pow h)
      · exact h2 h
  have hc := CFSG.AGLEmbeddingD2.AbelianSylowGL.isMulCommutative_of_isPGroup_of_not_dvd_index
    T hindex hP
  intro a ha b hb
  exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

section Rows

theorem kT2_SL3_mod_two {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2) :
    RowOf425 (projSL 3 K) :=
  rowOf425_of_noCQ' (noCQ425_of_isCyclic_sylow (KFacts.isCyclic_sylow_three_projSL hK))

theorem kT2_SU3_mod_one {p f : ℕ} [Fact p.Prime] (hf : f ≠ 0) (hq : p ^ f % 3 = 1) :
    RowOf425 (projSU 3 p f) :=
  rowOf425_of_noCQ' (noCQ425_of_isCyclic_sylow (KFacts.isCyclic_sylow_three_projSU hf hq))

theorem kT2_SL4_mod_two {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2) :
    RowOf425 (projSL 4 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine rowOf425_of_noCQ' (noCC425_of_abelian_sylow ?_)
  rw [← CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 4 K]
  refine comm_sylow_projImage fun P hP a ha b hb => ?_
  have h := comm_of_isPGroup_GL4 hK (P.map (StatedSL 4 K).subtype) (hP.map _) _
    ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact Subtype.ext h

theorem kT2_Sp4_mod_two {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2) :
    RowOf425 (projSp 2 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine rowOf425_of_noCQ' (noCC425_of_abelian_sylow ?_)
  rw [← CFSG.RankThree.PartOne.projImage_statedSp_eq_projSp 2 K]
  refine comm_sylow_projImage fun P hP a ha b hb => ?_
  set f : ↥(StatedSp 2 K) →* GL (Fin 4) K :=
    (glSumEquiv K).toMonoidHom.comp (StatedSp 2 K).subtype with hf
  have hfi : Function.Injective f := (glSumEquiv K).injective.comp Subtype.val_injective
  have h := comm_of_isPGroup_GL4 hK (P.map f) (hP.map _) _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul] at h
  exact hfi h

theorem kT2_Sp4_mod_one {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 1) :
    RowOf425 (projSp 2 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine rowOf425_of_noCQ' (noCC425_of_abelian_sylow ?_)
  rw [← CFSG.RankThree.PartOne.projImage_statedSp_eq_projSp 2 K]
  exact comm_sylow_projImage fun P hP => comm_of_isPGroup_Sp4_mod_one hK P hP

theorem kT2_Sp4 {K : Type} [Field K] [Finite K] (hK : ¬ 3 ∣ Nat.card K) :
    RowOf425 (projSp 2 K) := by
  rcases (by omega : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2) with h | h
  · exact kT2_Sp4_mod_one h
  · exact kT2_Sp4_mod_two h

theorem kT2_four_Sp (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowOf425 (projSp 2 (GaloisField p 1)) := by
  refine kT2_Sp4 ?_
  rw [GaloisField.card p 1 one_ne_zero, pow_one]
  intro h3
  have hpr : p.Prime := Fact.out
  rcases (Nat.dvd_prime hpr).mp h3 with h | h <;> omega

theorem kT2_seven_Sp4 (n : ℕ) (hn : 1 ≤ n) : RowOf425 (projSp 2 (GaloisField 2 n)) := by
  refine kT2_Sp4 ?_
  rw [GaloisField.card 2 n (by omega)]
  intro h3
  have := Nat.prime_three.dvd_of_dvd_pow h3
  omega

theorem kT2_two_SL_mod_two (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (hq : p ^ e % 3 = 2) :
    RowOf425 (projSL 3 (GaloisField p e)) :=
  kT2_SL3_mod_two (by rw [GaloisField.card p e (by omega)]; exact hq)

theorem kT2_two_SU_mod_one (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (hq : p ^ e % 3 = 1) :
    RowOf425 (projSU 3 p e) :=
  kT2_SU3_mod_one (by omega) hq

theorem kT2_four_SL_mod_two (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    RowOf425 (projSL 4 (GaloisField p 1)) :=
  kT2_SL4_mod_two (by rw [GaloisField.card p 1 one_ne_zero, pow_one]; exact hp)

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148L

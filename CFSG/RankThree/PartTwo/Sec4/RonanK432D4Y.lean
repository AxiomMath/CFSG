module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFacts
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF2
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.Sec19

theorem natCard_sup_dvd_of_commute_pair {G : Type} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) ∣ Nat.card ↥A * Nat.card ↥B := by
  let f : (↥A × ↥B) →* G :=
    { toFun := fun p => (p.1 : G) * (p.2 : G)
      map_one' := by simp
      map_mul' := fun p q => by
        have h : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) := hc _ q.1.2 _ p.2.2
        show (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G)) =
          (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G))
        calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by simp only [mul_assoc]
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [h]
          _ = (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G)) := by simp only [mul_assoc] }
  have hrange : f.range = A ⊔ B := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨p, rfl⟩
      exact mul_mem ((le_sup_left : A ≤ A ⊔ B) p.1.2) ((le_sup_right : B ≤ A ⊔ B) p.2.2)
    · refine sup_le ?_ ?_
      · intro a ha
        exact MonoidHom.mem_range.mpr ⟨(⟨a, ha⟩, 1), by simp [f]⟩
      · intro b hb
        exact MonoidHom.mem_range.mpr ⟨(1, ⟨b, hb⟩), by simp [f]⟩
  have hdvd := Subgroup.card_range_dvd f
  rw [hrange, Nat.card_prod] at hdvd
  exact hdvd

theorem ordTrialityD4_eq_mul (q : ℕ) (hq : 1 ≤ q) :
    CFSG.Open.ordTrialityD4 q =
      q ^ 3 * ((q ^ 3) ^ 2 - 1) * (q * (q ^ 2 - 1)) * (q ^ 8 * (q ^ 8 + q ^ 4 + 1)) := by
  unfold CFSG.Open.ordTrialityD4
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have e : (q ^ 3) ^ 2 = q ^ 6 := by ring
  rw [e]
  zify [h2, h6]
  ring

theorem three_dvd_pow_eight_mul_quot (q : ℕ) : 3 ∣ q ^ 8 * (q ^ 8 + q ^ 4 + 1) := by
  have hr : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  apply Nat.dvd_of_mod_eq_zero
  rcases hr with hr | hr | hr <;> simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, hr]

section Main

set_option linter.unusedSectionVars false


theorem natCard_Asub_eq {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}
    (P : D4Par n X σ) :
    Nat.card ↥(Asub σ) = (2 ^ n) ^ 3 * (((2 ^ n) ^ 3) ^ 2 - 1) := by
  rw [← Nat.card_congr (asubEquiv P).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, P.card]

theorem natCard_Bsub_eq {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}
    (P : D4Par n X σ) :
    Nat.card ↥(Bsub σ) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [← Nat.card_congr (bsubEquiv P).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, P.card_fix]

theorem not_weaklyClosed_of_conj_mem_Bsub {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}
    (P : CFSG.RankThree.PartTwo.Sec19.D4Par n X σ) (hn : 2 ≤ n)
    (hcard : Nat.card (CFSG.RankThree.PartTwo.Sec19.C0 σ) = CFSG.Open.ordTrialityD4 (2 ^ n))
    {z g : CFSG.RankThree.PartTwo.Sec19.C0 σ} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hg : g * z * g⁻¹ ∈ CFSG.RankThree.PartTwo.Sec19.Bsub σ) :
    ¬ WeaklyClosed (Subgroup.zpowers z) := by
  haveI : Finite (C0 σ) := finite_C0
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = g * z * g⁻¹ := ⟨_, rfl⟩
  rw [← hbdef] at hg
  have hb3 : b ^ 3 = 1 := by
    rw [hbdef, conj_pow, hz3]
    group
  have hb1 : b ≠ 1 := by
    intro h
    apply hz1
    have h' : g * z * g⁻¹ = 1 := by rw [← hbdef]; exact h
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hAB := trialityABFacts_of_par CFSG.Goldschmidt.topStatement P hn
  have hC : Subgroup.centralizer ({b} : Set (C0 σ)) ≤ Asub σ ⊔ Bsub σ :=
    centralizer_le_AB σ hAB n hn P.card P.frob hg hb3 hb1
  have hCdvd : Nat.card ↥(Subgroup.centralizer ({b} : Set (C0 σ))) ∣
      Nat.card ↥(Asub σ) * Nat.card ↥(Bsub σ) :=
    (Subgroup.card_dvd_of_le hC).trans
      (natCard_sup_dvd_of_commute_pair (A := Asub σ) (B := Bsub σ) fun a ha c hc =>
        Asub_Bsub_commute ha hc)
  have h3 : 3 * (Nat.card ↥(Asub σ) * Nat.card ↥(Bsub σ)) ∣ Nat.card (C0 σ) := by
    rw [natCard_Asub_eq P, natCard_Bsub_eq P, hcard,
      ordTrialityD4_eq_mul (2 ^ n) (Nat.one_le_pow _ _ (by norm_num))]
    obtain ⟨k, hk⟩ := three_dvd_pow_eight_mul_quot (2 ^ n)
    exact ⟨k, by rw [hk]; ring⟩
  have hH := three_dvd_index_of_card_dvd (Subgroup.centralizer ({b} : Set (C0 σ))) hCdvd h3
  have hbwc := not_weaklyClosed_of_three_dvd_index hord hH
  intro hz
  apply hbwc
  have hmap := weaklyClosed_map_mulEquiv (MulAut.conj g) hz
  have e : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers, hbdef]
    rfl
  rw [e] at hmap
  exact hmap

end Main

end CFSG.RankThree.PartTwo.Sec4.RonanK432

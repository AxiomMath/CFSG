module

public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section SL2

@[expose] def slThree (R : Type) [CommRing R] : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

theorem slThree_pow_three (R : Type) [CommRing R] : slThree R ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) R) ^ 3 = 1
  rw [pow_succ, pow_succ, pow_one, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem slThree_ne_one (R : Type) [CommRing R] [Nontrivial R] : slThree R ≠ 1 := by
  intro h
  have := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 0) h
  simp [slThree] at this

theorem three_dvd_card_specialLinearGroup_two (p : ℕ) [Fact p.Prime] :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  have hord : orderOf (slThree (ZMod p)) = 3 :=
    orderOf_eq_prime (slThree_pow_three _) (slThree_ne_one _)
  rw [← hord]
  exact orderOf_dvd_natCard _

end SL2

section General

variable {X Y : Type} [Group X] [Group Y]

theorem suzukiModel_of_mulEquiv (e : X ≃* Y) {k : ℕ} (h : SuzukiModel Y 2 k) :
    SuzukiModel X 2 k := by
  obtain ⟨h2, a, ha, K, i1, i2, hk, hK, ⟨f⟩⟩ := h
  exact ⟨h2, a, ha, K, i1, i2, hk, hK, ⟨e.trans f⟩⟩

theorem isSimpleGroup_and_a23List_of_threePrime {L : Subgroup X} (hL : A36Conclusion L)
    (h3 : ¬ 3 ∣ Nat.card L) : IsSimpleGroup ↥L ∧ A23List ↥L := by
  rcases hL with ⟨-, hs, hl⟩ | ⟨-, hc, -⟩ | ⟨p, hp, -, -, -, hnat⟩ | ⟨-, -, hsl, -⟩
  · exact ⟨hs, hl⟩
  · exfalso
    apply h3
    rw [← hc]
    exact Subgroup.card_subgroup_dvd_card _
  · exfalso
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨-, ψ, hψ, -⟩ := hnat
    exact h3 ((three_dvd_card_specialLinearGroup_two p).trans (Subgroup.card_dvd_of_surjective hψ))
  · exfalso
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨e⟩ := hsl
    apply h3
    have h1 : 3 ∣ Nat.card (↥L ⧸ CFSG.fittingSubgroup ↥L) := by
      rw [Nat.card_congr e.toEquiv]
      exact three_dvd_card_specialLinearGroup_two 5
    exact h1.trans (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _))

end General

section QTKE

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_and_suzukiModel_of_cComp (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) (hSz : SimpleThreePrimeSuzukiFact)
    {X Y : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥) (hY : Y ∈ cComp X) (h3 : ¬ 3 ∣ Nat.card Y) :
    IsSimpleGroup (O2Q Y) ∧ ∃ k : ℕ, SuzukiModel (O2Q Y) 2 k := by
  have hA := (lemma_1_2_1_four_strong hQ hs hnab h36 hX hY).1
  obtain ⟨ψ, hψ, -⟩ := exists_modO2_surjection hY
  have h3' : ¬ 3 ∣ Nat.card (modO2Image X Y) := fun h =>
    h3 (h.trans (Subgroup.card_dvd_of_surjective hψ))
  obtain ⟨hsimple, hlist⟩ := isSimpleGroup_and_a23List_of_threePrime hA h3'
  obtain ⟨e⟩ := modO2_mulEquiv hY
  obtain ⟨k, hk⟩ := hSz _ hsimple hlist h3'
  exact ⟨e.isSimpleGroup, k, suzukiModel_of_mulEquiv e hk⟩

end QTKE

end CFSG.Quasithin.H13

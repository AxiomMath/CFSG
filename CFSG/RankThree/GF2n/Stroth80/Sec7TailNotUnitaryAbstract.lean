module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNotUnitaryBase
public import CFSG.RankThree.GF2n.Stroth80.Sec7OutSolvableExtra
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailSimpleFactors

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem le_of_normal_two_group_of_sup_eq {Y : Type} [Group Y] [Finite Y] {E N R B : Subgroup Y}
    (hER : E ≤ R) (hNR : N ≤ R) (hEN : E ⊔ N = R) [(N.subgroupOf R).Normal]
    {S : Type} [Group S] [IsSimpleGroup S] (hS : ¬ IsPGroup 2 S)
    (eRN : (↥R ⧸ N.subgroupOf R) ≃* S) (hBE : B ≤ E)
    (hBn : ∀ e ∈ E, ∀ b ∈ B, e * b * e⁻¹ ∈ B) (hB2 : IsPGroup 2 B) : B ≤ N := by
  obtain ⟨θ, hθs, hθk⟩ := exists_surj_ker_eq_one hER hNR hEN eRN
  have hB'n : (B.subgroupOf E).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact hBn (g : Y) g.2 (n : Y) hn
  have hB'2 : IsPGroup 2 (B.subgroupOf E) :=
    hB2.of_equiv (Subgroup.subgroupOfEquivOfLe hBE).symm
  haveI hMn : ((B.subgroupOf E).map θ).Normal := Subgroup.Normal.map hB'n θ hθs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((B.subgroupOf E).map θ) with hbot | htop
  · intro b hb
    have he : (⟨b, hBE hb⟩ : ↥E) ∈ B.subgroupOf E := hb
    have hθb : θ ⟨b, hBE hb⟩ ∈ (B.subgroupOf E).map θ := Subgroup.mem_map_of_mem θ he
    rw [hbot, Subgroup.mem_bot] at hθb
    exact (hθk _).mp hθb
  · exfalso
    apply hS
    intro s
    have hs : s ∈ (B.subgroupOf E).map θ := by
      rw [htop]
      exact Subgroup.mem_top s
    obtain ⟨k, hk⟩ := (hB'2.map θ) ⟨s, hs⟩
    exact ⟨k, congrArg Subtype.val hk⟩

theorem notUnitary_abstract (hLevi : UnitarySixLeviStatement)
    (hOutU : OutSolvableUnitarySixStatement) {Y : Type} [Group Y] [Finite Y]
    (q : ℕ) (hq4 : 4 ≤ q) (hq2 : ∃ f : ℕ, 1 ≤ f ∧ q = 2 ^ f)
    (hU : IsPSUModel 6 q ↥(generalizedFitting Y)) (N R K : Subgroup Y) (hNR : N ≤ R)
    (hRK : R ≤ K) (hN2 : IsPGroup 2 N) (hNn : ∀ k ∈ K, k ∈ normalizer (N : Set Y))
    (hCKN : ∀ k ∈ K, (∀ n ∈ N, k * n = n * k) → k ∈ N)
    (K₀ : Type) [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = q)
    (hRN : ∃ _ : (N.subgroupOf R).Normal,
      Nonempty ((↥R ⧸ N.subgroupOf R) ≃* StatedProj (StatedSL 4 K₀))) : False := by
  classical
  obtain ⟨hnormNR, ⟨eRN⟩⟩ := hRN
  haveI : (generalizedFitting Y).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := Y)).2
  obtain ⟨f, hf, rfl⟩ := hq2
  have hmodel := statedClassicalModel_psu_six hf hU
  haveI hsimpU : IsSimpleGroup ↥(generalizedFitting Y) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 6 2 f hmodel).2
  have hnonab := exists_noncomm_of_psu_six_model hmodel
  have hCU : ∀ c : Y, (∀ s ∈ generalizedFitting Y, c * s = s * c) → c = 1 := by
    intro c hc
    have hcU : c ∈ generalizedFitting Y := CFSG.centralizer_generalizedFitting_le Y
      (Subgroup.mem_centralizer_iff.mpr fun s hs => (hc s hs).symm)
    have hcen : (⟨c, hcU⟩ : ↥(generalizedFitting Y)) ∈ Subgroup.center ↥(generalizedFitting Y) :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(generalizedFitting Y)) with h | h
    · rw [h, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      have ha : a ∈ Subgroup.center ↥(generalizedFitting Y) := by rw [h]; exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
  obtain ⟨hsimp4, hnab4⟩ := statedProj_statedSL_four_simple_nonabelian K₀
  haveI : IsSimpleGroup (StatedProj (StatedSL 4 K₀)) := hsimp4
  haveI : Finite (StatedProj (StatedSL 4 K₀)) := Finite.of_equiv _ eRN.toEquiv
  have hperf4 : Group.IsPerfect (StatedProj (StatedSL 4 K₀)) :=
    isPerfect_of_simple_nonabelian hnab4
  have hperfRN : commutator (↥R ⧸ N.subgroupOf R) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := eRN.symm.toMonoidHom) eRN.symm.surjective
      (G := StatedProj (StatedSL 4 K₀))).commutator_eq_top
  obtain ⟨E, hER, hEperf, hEN, hEn⟩ := exists_perfect_sup_eq hNR hperfRN
  have hEne : E ≠ ⊥ := by
    intro h
    have hRN' : R ≤ N := by
      rw [← hEN, h, bot_sup_eq]
    haveI : Subsingleton (↥R ⧸ N.subgroupOf R) := by
      have : N.subgroupOf R = ⊤ := Subgroup.subgroupOf_eq_top.mpr hRN'
      rw [this]
      exact QuotientGroup.subsingleton_quotient_top
    obtain ⟨a, b, hab⟩ := hnab4
    exact hab (by
      have := Subsingleton.elim (eRN.symm a) (eRN.symm b)
      have h2 := eRN.symm.injective this
      rw [h2])
  have hEU : E ≤ generalizedFitting Y :=
    perfect_le_of_out_solvable hCU (hOutU (2 ^ f) ⟨f, hf, rfl⟩ _ hU) hEperf
  have hRnormE : ∀ r ∈ R, r ∈ normalizer (E : Set Y) := fun r hr =>
    hEn r (Subgroup.le_normalizer hr)
  have hA : E ⊓ N ≠ ⊥ := by
    intro hA0
    apply hEne
    have hcomm : ∀ e ∈ E, ∀ n ∈ N, e * n = n * e := by
      intro e he n hn
      have h1 : ⁅e, n⁆ ∈ E ⊓ N := by
        refine ⟨?_, ?_⟩
        · have h3 : n * e⁻¹ * n⁻¹ ∈ E :=
            (Subgroup.mem_normalizer_iff.mp (hRnormE n (hNR hn)) e⁻¹).mp (E.inv_mem he)
          have h4 := E.mul_mem he h3
          have e1 : ⁅e, n⁆ = e * (n * e⁻¹ * n⁻¹) := by simp [commutatorElement_def, mul_assoc]
          rw [e1]
          exact h4
        · have h3 : e * n * e⁻¹ ∈ N :=
            (Subgroup.mem_normalizer_iff.mp (hNn e (hRK (hER he))) n).mp hn
          have e1 : ⁅e, n⁆ = (e * n * e⁻¹) * n⁻¹ := by simp [commutatorElement_def]
          rw [e1]
          exact N.mul_mem h3 (N.inv_mem hn)
      rw [hA0, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    rw [eq_bot_iff]
    intro e he
    have hmem : e ∈ E ⊓ N := ⟨he, hCKN e (hRK (hER he)) (hcomm e he)⟩
    rw [hA0] at hmem
    exact hmem
  have hAU : E ⊓ N ≤ generalizedFitting Y := inf_le_left.trans hEU
  have hA2 : IsPGroup 2 ↥(E ⊓ N) := isPGroup_subgroup_of_le 2 hN2 inf_le_right
  obtain ⟨P, O, hPU, hOP, hAO, hO2, hOn, hNP, hS⟩ :=
    hLevi (2 ^ f) ⟨f, hf, rfl⟩ Y (generalizedFitting Y) hU (E ⊓ N) hAU hA hA2
  have hEP : E ≤ P := fun g hg => hNP g (hEU hg) fun a ha =>
    ⟨E.mul_mem (E.mul_mem hg ha.1) (E.inv_mem hg),
      (Subgroup.mem_normalizer_iff.mp (hNn g (hRK (hER hg))) a).mp ha.2⟩
  have hnot2 : ¬ IsPGroup 2 (StatedProj (StatedSL 4 K₀)) := nonab_simple_not_isPGroup_two hnab4
  have hEO : E ⊓ O = E ⊓ N := by
    apply le_antisymm
    · intro x hx
      have hB : E ⊓ O ≤ N := le_of_normal_two_group_of_sup_eq hER hNR hEN hnot2 eRN inf_le_left
        (fun e he b hb => ⟨E.mul_mem (E.mul_mem he hb.1) (E.inv_mem he),
          hOn e (hEP he) b hb.2⟩) (isPGroup_subgroup_of_le 2 hO2 inf_le_right)
      exact ⟨hx.1, hB hx⟩
    · exact le_inf inf_le_left hAO
  have hcard : Nat.card ↥E = Nat.card ↥(E ⊓ N) * Nat.card (StatedProj (StatedSL 4 K₀)) :=
    card_eq_card_inf_mul_quot hER hNR hEN eRN
  have hL4 := card_L4_eq_of_even hK₀ ⟨f, hf, rfl⟩
  have hpos : 0 < Nat.card ↥(E ⊓ N) := Nat.card_pos
  have hdvd : ∀ D : ℕ, Nat.card ↥E ∣ Nat.card ↥(E ⊓ O) * D →
      Nat.card (StatedProj (StatedSL 4 K₀)) ∣ D := by
    intro D h
    rw [hEO, hcard] at h
    exact Nat.dvd_of_mul_dvd_mul_left hpos h
  obtain ⟨h1, h2, h3⟩ := notUnitary_arith hq4
  rcases hS E hEP hEperf with h | h | h
  · exact h1 (hL4 ▸ hdvd _ h)
  · exact h2 (hL4 ▸ hdvd _ h)
  · exact h3 (hL4 ▸ hdvd _ h)

end CFSG.RankThree.GF2n.Stroth80

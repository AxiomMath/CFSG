module

public import CFSG.Quasithin.Background.B1More13A
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Sup

theorem card_sup_dvd_of_normal {Γ : Type} [Group Γ] [Finite Γ] {R A B : Subgroup Γ}
    (hA : A ≤ R) (hAn : (A.subgroupOf R).Normal) (hB : B ≤ R) :
    Nat.card ↥(A ⊔ B) ∣ Nat.card ↥A * Nat.card ↥B := by
  have hAB : A ⊔ B ≤ R := sup_le hA hB
  have hAn' : (A.subgroupOf (A ⊔ B)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hAn.conj_mem ⟨(n : Γ), hA hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨(g : Γ), hAB g.2⟩
    exact Subgroup.mem_subgroupOf.mp h
  haveI := hAn'
  let A' : Subgroup ↥(A ⊔ B) := A.subgroupOf (A ⊔ B)
  let B' : Subgroup ↥(A ⊔ B) := B.subgroupOf (A ⊔ B)
  have hsup : A' ⊔ B' = ⊤ := by
    apply Subgroup.map_injective (f := (A ⊔ B).subtype) Subtype.val_injective
    rw [Subgroup.map_sup]
    have h1 : A'.map (A ⊔ B).subtype = A := Subgroup.map_subgroupOf_eq_of_le le_sup_left
    have h2 : B'.map (A ⊔ B).subtype = B := Subgroup.map_subgroupOf_eq_of_le le_sup_right
    rw [h1, h2]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let f : ↥B' →* ↥(A ⊔ B) ⧸ A' := (QuotientGroup.mk' A').comp B'.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ A' ⊔ B' := by
      rw [hsup]
      exact Subgroup.mem_top x
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨⟨z, hz⟩, ?_⟩
    have hy1 : QuotientGroup.mk' A' y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    show QuotientGroup.mk' A' z = QuotientGroup.mk' A' x
    rw [← hyz, map_mul, hy1, one_mul]
  have hdvd : Nat.card (↥(A ⊔ B) ⧸ A') ∣ Nat.card ↥B' := Subgroup.card_dvd_of_surjective hf
  have hA' : Nat.card ↥A' = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hB' : Nat.card ↥B' = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hΛ : Nat.card ↥(A ⊔ B) = Nat.card (↥(A ⊔ B) ⧸ A') * Nat.card ↥A' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup A'
  rw [hA'] at hΛ
  rw [hB'] at hdvd
  calc Nat.card ↥(A ⊔ B) = Nat.card (↥(A ⊔ B) ⧸ A') * Nat.card ↥A := hΛ
    _ ∣ Nat.card ↥B * Nat.card ↥A := mul_dvd_mul_right hdvd _
    _ = Nat.card ↥A * Nat.card ↥B := mul_comm _ _

theorem not_three_dvd_sup_of_normal {Γ : Type} [Group Γ] [Finite Γ] (R : Subgroup Γ)
    {ι : Type} [Finite ι] (N : ι → Subgroup Γ) (hN : ∀ i, N i ≤ R)
    (hNn : ∀ i, ((N i).subgroupOf R).Normal) (hp : ∀ i, ¬ 3 ∣ Nat.card ↥(N i)) :
    ¬ 3 ∣ Nat.card ↥(⨆ i, N i) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, ¬ 3 ∣ Nat.card ↥(s.sup N) ∧ s.sup N ≤ R := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨?_, bot_le⟩
      rw [Finset.sup_empty, Subgroup.card_bot]
      norm_num
    | insert i s hi ih =>
      obtain ⟨hs3, hsR⟩ := ih
      rw [Finset.sup_insert]
      refine ⟨fun h3 => ?_, sup_le (hN i) hsR⟩
      have hdvd := card_sup_dvd_of_normal (hN i) (hNn i) hsR
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans hdvd) with h | h
      · exact hp i h
      · exact hs3 h
  rw [← Finset.sup_univ_eq_iSup]
  exact (key Finset.univ).1

end Sup

section Components

theorem not_three_dvd_of_components {Γ : Type} [Group Γ] [Finite Γ] (R : Subgroup Γ)
    {ι : Type} [Finite ι] (N : ι → Subgroup Γ) (i₀ : ι) (K : Subgroup Γ)
    (hR : R = ⨆ i, N i) (hNR : ∀ i, N i ≤ R) (hNn : ∀ i, ((N i).subgroupOf R).Normal)
    (hNc : ∀ i, IsComponentOf (N i) ⊤)
    (hNcard : ∀ i, Nat.card ↥(N i) = Nat.card ↥(N i₀))
    (hKR : K ≤ R) (hKc : IsComponentOf K ⊤) (hK3 : ¬ 3 ∣ Nat.card ↥K)
    (k : ℕ) (hq : Nat.card Γ ∣ 2 ^ k * Nat.card ↥R) (h3 : 3 ∣ Nat.card Γ) : False := by
  obtain ⟨j, hj⟩ : ∃ j, ⁅K, N j⁆ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hcommK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
      intro a ha b hb
      have hall : ∀ c ∈ R, a * c = c * a := by
        intro c hc
        rw [hR] at hc
        refine Subgroup.iSup_induction N (C := fun c => a * c = c * a) hc ?_ ?_ ?_
        · intro i c hc'
          have hm : ⁅a, c⁆ ∈ ⁅K, N i⁆ := Subgroup.commutator_mem_commutator ha hc'
          rw [hcon i, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
          exact hm
        · simp
        · intro x y hx hy
          calc a * (x * y) = (a * x) * y := by rw [mul_assoc]
            _ = (x * a) * y := by rw [hx]
            _ = x * (a * y) := by rw [mul_assoc]
            _ = x * (y * a) := by rw [hy]
            _ = (x * y) * a := by rw [mul_assoc]
      exact hall b (hKR hb)
    obtain ⟨hcomm, hsimp⟩ := hKc.2.2
    have hbot : commutator ↥K = ⊥ := by
      apply le_bot_iff.mp
      refine Subgroup.commutator_le.mpr ?_
      intro x _ y _
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (Subtype.ext (hcommK x x.2 y y.2))
    rw [hbot] at hcomm
    have hK1 : ∀ x : ↥K, x = 1 := fun x => by
      have hx : x ∈ (⊤ : Subgroup ↥K) := Subgroup.mem_top x
      rw [← hcomm, Subgroup.mem_bot] at hx
      exact hx
    haveI := hsimp
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (↥K ⧸ Subgroup.center ↥K)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact hxy (by rw [hK1 a, hK1 b])
  have hjK : K ≤ N j := by
    rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot (H := ⊤) hKc (hNc j).2.1 with h | h
    · exact h
    · exact (hj h).elim
  have hNjK : N j ≤ K := by
    rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot (H := ⊤) (hNc j) hKc.2.1 with h | h
    · exact h
    · exact (hj (by rw [Subgroup.commutator_comm]; exact h)).elim
  have hKj : K = N j := le_antisymm hjK hNjK
  have hcardK : Nat.card ↥K = Nat.card ↥(N i₀) := by rw [hKj, hNcard j]
  have hi : ∀ i, ¬ 3 ∣ Nat.card ↥(N i) := fun i => by
    rw [hNcard i, ← hcardK]
    exact hK3
  have hR3 : ¬ 3 ∣ Nat.card ↥R := by
    have h := not_three_dvd_sup_of_normal R N hNR hNn hi
    rw [← hR] at h
    exact h
  have h3' : 3 ∣ 2 ^ k * Nat.card ↥R := h3.trans hq
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
  · have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h2
  · exact hR3 h

end Components

end CFSG.Quasithin.H13

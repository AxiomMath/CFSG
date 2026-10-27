module

public import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup

variable {G : Type*} [Group G]

theorem characteristic_two_type_faithful_plane_two_group_witness [Finite G]
    (hG : CFSG.IsCharacteristicPType G 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A Q B : Subgroup G} (hA : CFSG.IsElementaryAbelian p A) (hQ2 : IsPGroup 2 Q)
    (hQ1 : Q ≠ ⊥) (hAQ : A ≤ normalizer (Q : Set G)) (hBA : B ≤ A) (hB : Nat.card B = p ^ 2) :
    let S := CFSG.inSubgroup (CFSG.pCore 2) (normalizer (Q : Set G))
    (S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ normalizer (S : Set G)) ∧ A ⊓ centralizer (S : Set G) = ⊥ ∧
      ∃ b ∈ B, b ≠ 1 ∧ ⁅S ⊓ centralizer ({b} : Set G), B⁆ ≠ ⊥ ∧
        IsPGroup 2 (⁅S ⊓ centralizer ({b} : Set G), B⁆ : Subgroup G) ∧
        B ≤ normalizer ((⁅S ⊓ centralizer ({b} : Set G), B⁆ : Subgroup G) : Set G) ∧
        ⁅S ⊓ centralizer ({b} : Set G), B⁆ ≤ S ⊓ centralizer ({b} : Set G) := by
  intro S
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Q : Set G) with hH
  have hQS : Q ≤ S := le_inSubgroup_pCore_of_normal hQ2 le_normalizer le_rfl
  have hS1 : S ≠ ⊥ := fun h => hQ1 (le_bot_iff.mp (h ▸ hQS))
  have hS2 : IsPGroup 2 S := (CFSG.pCore_isPGroup (p := 2) (G := H)).map H.subtype
  have hAS : A ≤ normalizer (S : Set G) := hAQ.trans (le_normalizer_inSubgroup_pCore 2 H)
  have hfaith : A ⊓ centralizer (S : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro a ⟨haA, haC⟩
    have haS : a ∈ S := mem_inSubgroup_pCore_of_isCharacteristicPType hG hQ2 hQ1 (hAQ haA)
      fun s hs => mem_centralizer_iff.mp haC s hs
    have hp' : IsPGroup p A := CFSG.IsElementaryAbelian.isPGroup p A
    have hdisj := IsPGroup.disjoint_of_ne p 2 hp2 A S hp' hS2
    have : a ∈ A ⊓ S := ⟨haA, haS⟩
    rwa [hdisj.eq_bot] at this
  refine ⟨⟨hS1, hS2, hAS⟩, hfaith, ?_⟩
  have hBe : CFSG.IsElementaryAbelian p B := isElementaryAbelian_of_le hA hBA
  have hpS : ¬ p ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hBN : ∀ b ∈ B, B ≤ normalizer ((S ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G) := by
    intro b hb
    refine le_normalizer_of_forall_conj_mem fun c hc x hx => ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hAS (hBA hc)) x).mp hx.1
    · have hcb : c * b = b * c := congrArg Subtype.val (hBe.is_comm.comm ⟨c, hc⟩ ⟨b, hb⟩)
      have hxb : x * b = b * x := mem_centralizer_singleton_iff.mp hx.2
      refine mem_centralizer_singleton_iff.mpr ?_
      calc c * x * c⁻¹ * b = c * x * (c⁻¹ * b * c) * c⁻¹ := by group
        _ = c * x * b * c⁻¹ := by
            rw [show c⁻¹ * b * c = b by rw [mul_assoc, ← hcb]; group]
        _ = c * b * x * c⁻¹ := by rw [mul_assoc c x b, hxb, ← mul_assoc]
        _ = b * (c * x * c⁻¹) := by rw [hcb]; group
  obtain ⟨b, hb, hb1, hne⟩ : ∃ b ∈ B, b ≠ 1 ∧ ⁅S ⊓ centralizer ({b} : Set G), B⁆ ≠ ⊥ := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hSB : S ≤ centralizer (B : Set G) :=
      le_of_forall_inf_centralizer_le hBe hB.ge hpS (hBA.trans hAS) fun b hb hb1 =>
        commutator_eq_bot_iff_le_centralizer.mp (hcon b hb hb1)
    have hBC : B ≤ A ⊓ centralizer (S : Set G) :=
      fun b hb => ⟨hBA hb, mem_centralizer_iff.mpr fun s hs =>
        (mem_centralizer_iff.mp (hSB hs) b hb).symm⟩
    rw [hfaith, le_bot_iff] at hBC
    rw [hBC, card_bot] at hB
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hle := le_normalizer_iff_commutator_le_left.mp (hBN b hb)
  exact ⟨b, hb, hb1, hne, hS2.to_le (hle.trans inf_le_left), normalizer_commutator_ge_right _ _,
    hle⟩

end CFSG.RankThree.GroupTheory.SteinbergBM

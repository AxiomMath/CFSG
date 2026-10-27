
module

public import CFSG.Quasithin.Vol2.Ch1Comm

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Lemma122Rank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], A38Types X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1

@[expose] def Lemma122A : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → quasithinIsQTKECat G → (∃ a b : G, a * b ≠ b * a) →
    ∀ H L : Subgroup G, pCoreOf 2 H ≠ ⊥ → L ∈ cComp H → ∀ p : ℕ, p.Prime → p ≠ 2 →
      Set.ncard (conjSubgroupsBy H L) = 2 → p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) →
        Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = p ^ k} = conjClosure L H

variable {G : Type} [Group G] [Finite G]

theorem pRank_modO2_eq (L : Subgroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) = CFSG.Open.pRank p L := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hndvd : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    intro h
    rw [hn] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L) hndvd]
  exact pRank_top_subtype L

theorem lemma_1_2_2_b (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hrank : Lemma122Rank) {H L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : CFSG.Open.pRank p L = 2) :
    (L.subgroupOf H).Normal := by
  rcases lemma_1_2_1_three hK hs hnab h37 h38 hH hL with hn | ⟨-, htypes⟩
  · exact hn
  · exfalso
    have h1 := hrank _ htypes p hp hp2
    rw [pRank_modO2_eq L hp hp2, hm] at h1
    omega

end CFSG.Quasithin

module

public import CFSG.Quasithin.EmptyFaithful.S152VR6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

namespace S152V

theorem rank2_of_two_le_pRank {S : Type} [Group S] [Finite S] (h : 2 ≤ CFSG.pRank 3 S) : Rank2 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let T : Set ℕ := {r | ∃ A : Subgroup S, CFSG.IsElementaryAbelian 3 ↥A ∧ Nat.card ↥A = 3 ^ r}
  have hbot : CFSG.IsElementaryAbelian 3 ↥(⊥ : Subgroup S) := by
    rw [CFSG.RankThree.Asc83Table.isElementaryAbelian_iff]
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    · rw [Subgroup.mem_bot] at ha
      rw [ha, one_pow]
  have hne : T.Nonempty := ⟨0, ⊥, hbot, by simp⟩
  have hbdd : BddAbove T := by
    refine ⟨Nat.card S, ?_⟩
    rintro r ⟨B, -, hB⟩
    calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card S := Subgroup.card_le_card_group B
  obtain ⟨A, hA, hcard⟩ := Nat.sSup_mem hne hbdd
  have hk : 2 ≤ sSup T := h
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) 3 (n := 2)
    (by rw [hcard]; exact pow_dvd_pow 3 hk)
  have hA' := (CFSG.RankThree.Asc83Table.isElementaryAbelian_iff).1 hA
  refine ⟨K.map A.subtype, ⟨⟨fun a b => ?_⟩⟩, ?_, ?_⟩
  · obtain ⟨a', -, ha⟩ := a.2
    obtain ⟨b', -, hb⟩ := b.2
    apply Subtype.ext
    show (a : S) * b = b * a
    rw [← ha, ← hb]
    exact hA'.1 _ a'.2 _ b'.2
  · rintro _ ⟨a', -, rfl⟩
    exact hA'.2 _ a'.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
    norm_num

theorem rank2_of_E9Basis {L : Type*} [Group L] (E : CFSG.RankThree.Asc83Table.E9Basis L) : Rank2 L := by
  have h := (CFSG.RankThree.Asc83Table.isElementaryAbelian_iff).1 E.isElementaryAbelian
  refine ⟨E.sub, ⟨⟨fun a b => ?_⟩⟩, fun x hx => h.2 x hx, E.card⟩
  exact Subtype.ext (h.1 _ a.2 _ b.2)

theorem rank2_of_nine
    {s : TauCeti.SporadicName} (hs : NineSporadic s) {Γ : Type} [Group Γ] [Finite Γ]
    (e : Γ ≃* NativeSporadic.Carrier s) : Rank2 Γ := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rank2_of_two_le_pRank (CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_M11 e)
  · exact rank2_of_two_le_pRank (CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_M12 e)
  · exact rank2_of_equiv e (rank2_of_E9Basis CFSG.RankThree.Asc83Table.M22.E)
  · exact rank2_of_equiv e (rank2_of_E9Basis CFSG.RankThree.Asc83Table.M23.E)
  · exact rank2_of_two_le_pRank (CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_M24 e)
  · exact rank2_of_two_le_pRank (CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_J2 e)
  · exact rank2_of_two_le_pRank (CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_HS e)
  · exact rank2_of_two_le_pRank (CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_He e)
  · exact rank2_of_two_le_pRank (CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_Ru e)

end S152V

@[expose] def SporadicInvolutionAtlas : Prop :=
  ∀ (s : TauCeti.SporadicName), NineSporadic s → ∀ (Γ : Type) [Group Γ] [Finite Γ],
    Nonempty (Γ ≃* NativeSporadic.Carrier s) →
      (∀ α : MulAut Γ, α ^ 3 = 1 → ∃ g : Γ, α = MulAut.conj g) ∧
        ∀ t : Γ, orderOf t = 2 → (∃ S : Sylow 2 Γ, ∀ x ∈ S, x * t = t * x) →
          ¬ 9 ∣ Nat.card (Subgroup.centralizer ({t} : Set Γ))

theorem sporadicInvolution3Rank_of_atlas
    (h : SporadicInvolutionAtlas) : SporadicInvolution3Rank := fun s hs Γ _ _ hΓ => by
  obtain ⟨e⟩ := hΓ
  exact ⟨S152V.rank2_of_nine hs e, h s hs Γ ⟨e⟩⟩

end CFSG.Quasithin

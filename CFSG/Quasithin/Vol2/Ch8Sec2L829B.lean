module

public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Quasithin.Background.C48AsmLine

public import CFSG.Quasithin.Vol2.Ch8Sec2L825H

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs

section L829B

variable {G : Type} [Group G] [Finite G]

theorem e214_two_82 (hE214 : AS_E_2_14) {H T M V : Subgroup G} {h : G}
    (hhI : h ∈ ch82I V h) (hIC : IsInIHTVC H T (H ⊓ M) V (ch82I V h)) (hZ1 : ch82ZI V h ≠ ⊥)
    (h28 : E2.Hyp28 H T (H ⊓ M) V) (hchar : QuasithinUnique.CharTwo H)
    (hTI : IsTISetIn V (H ⊓ M)) (hDLSz : IsDihL2Sz (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))) :
    e214P V (ch82I V h) h = kerIn (M ⊓ ch82I V h) (ch82I V h) ∨
      IsSz 3 (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) := by
  have hMI := inf_inf_eq_82 (M := M) hIC.1
  obtain ⟨-, ⟨h2, -⟩, -⟩ :=
    hE214 G H T (H ⊓ M) V (ch82I V h) h h28 hchar hTI hIC hhI rfl hZ1
      (isDihL2Sz_of_eq hMI.symm hDLSz)
  rw [← hMI]
  exact h2

theorem e214P_eq_kerIn_82 (hE214 : AS_E_2_14)
    {H T M V : Subgroup G} {h : G} {k : ℕ}
    (hhI : h ∈ ch82I V h) (hIC : IsInIHTVC H T (H ⊓ M) V (ch82I V h)) (hZ1 : ch82ZI V h ≠ ⊥)
    (h28 : E2.Hyp28 H T (H ⊓ M) V) (hchar : QuasithinUnique.CharTwo H)
    (hTI : IsTISetIn V (H ⊓ M)) (hk : k ≤ 2)
    (hcases : (k = 1 ∧ ∃ m : ℕ, Odd m ∧ 1 < m ∧
        Nonempty (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h) ≃* DihedralGroup m)) ∨
      IsPSL 2 2 k (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) ∨
      IsSz k (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))) :
    e214P V (ch82I V h) h = kerIn (M ⊓ ch82I V h) (ch82I V h) := by
  have hord : ∀ c : ℕ, Nat.card (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) = c →
      4 ∣ c → c ≠ 60 → False := by
    intro c hc h4 h60
    rcases hcases with ⟨-, m, hm, -, ⟨e⟩⟩ | hP | hS
    · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hc
      obtain ⟨j, rfl⟩ := hm
      omega
    · have hk2 : k = 2 := by
        obtain ⟨⟨-, hk1, -, h22, -⟩, -⟩ := hP
        rcases (show k = 1 ∨ k = 2 by omega) with h | h
        · subst h
          exact absurd rfl h22
        · exact h
      subst hk2
      rw [C48.card_psl_two_two hP] at hc
      omega
    · obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hS
      omega
  have hDLSz : IsDihL2Sz (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) := by
    rcases hcases with ⟨-, hD⟩ | hP | hS
    · exact Or.inl hD
    · exact Or.inr (Or.inl ⟨k, hP⟩)
    · exact Or.inr (Or.inr ⟨k, hS⟩)
  rcases e214_two_82 hE214 hhI hIC hZ1 h28 hchar hTI hDLSz with hP | hS
  · exact hP
  · exfalso
    obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := hS
    have ha : a = 1 := by omega
    subst ha
    have hc : Nat.card (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) = 29120 := by
      rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
      norm_num
    exact hord _ hc (by norm_num) (by norm_num)

omit [Finite G] in
theorem le_normalizer_sup_ch82A_82 {T V : Subgroup G} {h : G}
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hP : e214P V (ch82I V h) h = pCoreOf 2 (ch82I V h))
    (hTO : T ≤ Subgroup.normalizer (pCoreOf 2 (ch82I V h) : Set G)) :
    T ≤ Subgroup.normalizer ((V ⊔ ch82A V h : Subgroup G) : Set G) := by
  have heq : V ⊔ ch82A V h = V ⊔ pCoreOf 2 (ch82I V h) := by
    rw [← hP]
    apply le_antisymm
    · exact sup_le le_sup_left (le_sup_of_le_right le_sup_left)
    · exact sup_le le_sup_left (sup_le le_sup_right (inf_le_left.trans le_sup_left))
  rw [heq]
  exact fun t ht => Subgroup.inf_normalizer_le_normalizer_sup V (pCoreOf 2 (ch82I V h))
    ⟨hTV ht, hTO ht⟩

end L829B

end CFSG.Quasithin.H13

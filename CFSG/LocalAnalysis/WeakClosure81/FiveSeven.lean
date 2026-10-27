module

public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenPerm
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenRed
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenSix
public import CFSG.LocalAnalysis.WeakClosure81.FiveSixEmbed

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Equiv

variable {G : Type} [Group G] [Finite G]

theorem five_seven (hR : R3_1) {H M A : Subgroup G} (h : Sec5Hyp H M A) {n : ℕ} (hn : 4 < n)
    (hL : Nonempty (↥(Fstar H) ≃* alternatingGroup (Fin n)))
    (h1 : (maxOver H A).ncard = 1) :
    Nonempty (↥H ≃* alternatingGroup (Fin 5)) ∧ IsSylowIn 2 A H := by
  obtain ⟨e⟩ := hL
  obtain ⟨M₀, hM₀, h₀, -, hAne, hHA⟩ := five_seven_reduction (by omega) e h h1
  obtain ⟨ι, hιinj, hιF⟩ : ∃ ι : ↥H →* Perm (Fin n), Function.Injective ι ∧
      ((Fstar H).subgroupOf H).map ι = alternatingGroup (Fin n) := by
    by_cases h6 : n = 6
    · subst h6
      exact exists_embedding_of_six h₀ hM₀ hHA e
    · exact exists_embedding_of_ne_six (by omega) h6 e
  have hAH : A ≤ H := h.le_group
  have hAlt : alternatingGroup (Fin n) ≤ (⊤ : Subgroup ↥H).map ι :=
    hιF ▸ Subgroup.map_mono le_top
  have hA'ab : IsElemAbelian 2 ((A.subgroupOf H).map ι) :=
    (h.isElemAbelian.subgroupOf H).map ι
  have hA'ne : (A.subgroupOf H).map ι ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ hιinj] at hbot
    apply hAne
    calc A = (A.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hAH).symm
      _ = ⊥ := by rw [hbot, Subgroup.map_bot]
  have h1' : (maxOver ((⊤ : Subgroup ↥H).map ι) ((A.subgroupOf H).map ι)).ncard = 1 :=
    (ncard_maxOver_map_subgroupOf hAH ι hιinj).trans h1
  obtain ⟨h5, hK5, hcard4⟩ := five_seven_perm hR hn hAlt hA'ab hA'ne h1'
  subst h5
  have hrange : ι.range = alternatingGroup (Fin 5) := (MonoidHom.range_eq_map ι).trans hK5
  let eH : ↥H ≃* alternatingGroup (Fin 5) :=
    (MonoidHom.ofInjective hιinj).trans (MulEquiv.subgroupCongr hrange)
  have hHcard : Nat.card ↥H = 60 := by
    rw [Nat.card_congr eH.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hAcard : Nat.card ↥A = 4 := by
    have e1 : Nat.card ↥(A.subgroupOf H) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
    have e2 : Nat.card ↥((A.subgroupOf H).map ι) = Nat.card ↥(A.subgroupOf H) :=
      Subgroup.card_map_of_injective hιinj
    rw [← e1, ← e2]
    exact hcard4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨eH⟩, isSylowIn_of_card_eq hAH ?_⟩
  have hf : (60 : ℕ).factorization 2 = 2 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  rw [hAcard, hHcard, hf]
  norm_num

end CFSG.LocalAnalysis.WeakClosure81

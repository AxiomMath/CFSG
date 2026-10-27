module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenIndex

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

private theorem card_sup_mul_card_inf_aux {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hA
  have h2 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h3 := Subgroup.relIndex_mul_card B A
  have h4 : B ⊓ (A ⊔ B) = B := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [← h2, ← h3, inf_comm]
  ring

private theorem le_normalizer_of_forall_mem {Q W : Subgroup G}
    (h : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W) : Q ≤ Subgroup.normalizer (W : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h q hq x, fun hx => ?_⟩
  have := h q⁻¹ (Q.inv_mem hq) _ hx
  simpa [mul_assoc] using this

theorem not_le_centralizer_symm {W W' : Subgroup G}
    (hne : ¬ W' ≤ Subgroup.centralizer (W : Set G)) :
    ¬ W ≤ Subgroup.centralizer (W' : Set G) := by
  intro h
  apply hne
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.1 (h hw) y hy).symm

theorem TransvPair.inf_centralizer_eq {Q W S W' S' : Subgroup G} (h : TransvPair Q W S)
    (h' : TransvPair Q W' S') (hne : ¬ W' ≤ Subgroup.centralizer (W : Set G)) :
    W ⊓ Subgroup.centralizer (W' : Set G) = S := by
  obtain ⟨y, hyW', hyC⟩ := SetLike.not_le_iff_exists.1 hne
  apply le_antisymm
  · intro z hz
    obtain ⟨hzW, hzC⟩ := Subgroup.mem_inf.1 hz
    have hy := h.centralizer_eq y (h'.le hyW') hyC
    have hz' : z ∈ W ⊓ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_inf.2 ⟨hzW, Subgroup.centralizer_le (Set.singleton_subset_iff.2 hyW') hzC⟩
    rwa [hy] at hz'
  · intro s hs
    refine Subgroup.mem_inf.2 ⟨h.le_W hs, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w' hw'
    by_cases hC : w' ∈ Subgroup.centralizer (W : Set G)
    · exact (Subgroup.mem_centralizer_iff.1 hC s (h.le_W hs)).symm
    · have hw := h.centralizer_eq w' (h'.le hw') hC
      have hs' : s ∈ W ⊓ Subgroup.centralizer ({w'} : Set G) := by
        rw [hw]
        exact hs
      exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs').2).symm

theorem TransvPair.sup_inf_centralizer_eq {Q W S W' S' : Subgroup G} (h : TransvPair Q W S)
    (h' : TransvPair Q W' S') (hne : ¬ W' ≤ Subgroup.centralizer (W : Set G)) :
    W' ⊔ (Q ⊓ Subgroup.centralizer (W : Set G)) = Q := by
  have hS' := h'.inf_centralizer_eq h (not_le_centralizer_symm hne)
  have hDN : Q ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (W' : Set G) :=
    inf_le_left.trans (le_normalizer_of_forall_mem h'.normal)
  have hprod := card_sup_mul_card_inf_aux hDN
  have hinf : (Q ⊓ Subgroup.centralizer (W : Set G)) ⊓ W' = S' := by
    rw [← hS']
    ext z
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hc⟩, hw⟩
      exact ⟨hw, hc⟩
    · rintro ⟨hw, hc⟩
      exact ⟨⟨h'.le hw, hc⟩, hw⟩
  rw [hinf] at hprod
  have hpos : 0 < Nat.card S' := Nat.card_pos
  have h4 : Nat.card ↥(Q ⊓ Subgroup.centralizer (W : Set G) ⊔ W') =
      4 * Nat.card ↥(Q ⊓ Subgroup.centralizer (W : Set G)) := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hprod, h'.card_S]
    ring
  have hle : Q ⊓ Subgroup.centralizer (W : Set G) ⊔ W' ≤ Q := sup_le inf_le_left h'.le
  have heq : Q ⊓ Subgroup.centralizer (W : Set G) ⊔ W' = Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h4]; exact h.card_index.le)
  rw [sup_comm]
  exact heq

theorem TransvPair.card_inf_centralizer {Q W S W' S' : Subgroup G} (h : TransvPair Q W S)
    (h' : TransvPair Q W' S') (hne : ¬ W' ≤ Subgroup.centralizer (W : Set G)) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer (W : Set G)) =
      4 * Nat.card ↥(Q ⊓ Subgroup.centralizer (W : Set G) ⊓
        Subgroup.centralizer (W' : Set G)) := by
  have hSW : W ⊓ Subgroup.centralizer (W' : Set G) = S := h.inf_centralizer_eq h' hne
  have hWD : W ≤ Q ⊓ Subgroup.centralizer (W : Set G) :=
    le_inf h.le fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' => h.comm w' hw' w hw
  have hEW : (Q ⊓ Subgroup.centralizer (W : Set G) ⊓ Subgroup.centralizer (W' : Set G)) ⊓ W =
      S := by
    rw [← hSW]
    ext z
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hc⟩, hw⟩
      exact ⟨hw, hc⟩
    · rintro ⟨hw, hc⟩
      exact ⟨⟨hWD hw, hc⟩, hw⟩
  have hEN : Q ⊓ Subgroup.centralizer (W : Set G) ⊓ Subgroup.centralizer (W' : Set G) ≤
      Subgroup.normalizer (W : Set G) :=
    (inf_le_left.trans inf_le_left).trans (le_normalizer_of_forall_mem h.normal)
  have hprod := card_sup_mul_card_inf_aux hEN
  rw [hEW, h.card_S] at hprod
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hlow : Nat.card ↥(Q ⊓ Subgroup.centralizer (W : Set G) ⊓
      Subgroup.centralizer (W' : Set G) ⊔ W) =
      4 * Nat.card ↥(Q ⊓ Subgroup.centralizer (W : Set G) ⊓
        Subgroup.centralizer (W' : Set G)) := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hprod]
    ring
  have hle1 : Nat.card ↥(Q ⊓ Subgroup.centralizer (W : Set G) ⊓
      Subgroup.centralizer (W' : Set G) ⊔ W) ≤
      Nat.card ↥(Q ⊓ Subgroup.centralizer (W : Set G)) :=
    Subgroup.card_le_of_le (sup_le inf_le_left hWD)
  have hrelD : (Q ⊓ Subgroup.centralizer (W : Set G)).relIndex Q = 4 := by
    have := Subgroup.relIndex_mul_card (Q ⊓ Subgroup.centralizer (W : Set G)) Q
    rw [inf_of_le_left inf_le_left, h.card_index] at this
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
  have hrelD' : (Q ⊓ Subgroup.centralizer (W' : Set G)).relIndex Q = 4 := by
    have := Subgroup.relIndex_mul_card (Q ⊓ Subgroup.centralizer (W' : Set G)) Q
    rw [inf_of_le_left inf_le_left, h'.card_index] at this
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
  have hEeq : Q ⊓ Subgroup.centralizer (W : Set G) ⊓ Subgroup.centralizer (W' : Set G) =
      (Q ⊓ Subgroup.centralizer (W : Set G)) ⊓ (Q ⊓ Subgroup.centralizer (W' : Set G)) := by
    ext z
    simp only [Subgroup.mem_inf]
    tauto
  have hle2 : (Q ⊓ Subgroup.centralizer (W : Set G) ⊓
      Subgroup.centralizer (W' : Set G)).relIndex Q ≤ 16 := by
    rw [hEeq]
    calc _ ≤ _ := Subgroup.relIndex_inf_le
      _ = 16 := by rw [hrelD, hrelD']
  have hEQ : Q ⊓ Subgroup.centralizer (W : Set G) ⊓ Subgroup.centralizer (W' : Set G) ≤ Q :=
    inf_le_left.trans inf_le_left
  have hmul := Subgroup.relIndex_mul_card (Q ⊓ Subgroup.centralizer (W : Set G) ⊓
    Subgroup.centralizer (W' : Set G)) Q
  rw [inf_of_le_left hEQ] at hmul
  have hQ := h.card_index
  have hup : Nat.card Q ≤ 16 * Nat.card ↥(Q ⊓ Subgroup.centralizer (W : Set G) ⊓
      Subgroup.centralizer (W' : Set G)) := by
    rw [← hmul]
    exact Nat.mul_le_mul_right _ hle2
  omega

end CFSG.LocalAnalysis.WeakClosure81

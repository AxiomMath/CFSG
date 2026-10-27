module

public import CFSG.RankThree.GF2n.Smith81.S81ZIdealGen
public import CFSG.RankThree.GF2n.Smith81.S81ZE7
public import CFSG.RankThree.GF2n.Smith81.S81QRadNu

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z
open CFSG.RankThree.GF2n.Smith81.S81Z.IdealEnum

open _root_.Classical in
@[expose] def Rd6 : Finset Rt := Rpos.filter fun γ => γ node1 = 0

theorem mem_Rd6 {γ : Rt} : γ ∈ Rd6 ↔ γ ∈ Perp ∧ 0 < ht γ := by
  classical
  simp only [Rd6, Finset.mem_filter, mem_Rpos, perp_iff]
  tauto

theorem closed_Rd6 : Closed Rd6 where
  root α hα := (perp_iff.1 (mem_Rd6.1 hα).1).1
  pos α hα := (mem_Rd6.1 hα).2
  add α hα β hβ hr := by
    have h1 := mem_Rd6.1 hα
    have h2 := mem_Rd6.1 hβ
    refine mem_Rd6.2 ⟨perp_iff.2 ⟨hr, ?_⟩, ?_⟩
    · have := (perp_iff.1 h1.1).2
      have := (perp_iff.1 h2.1).2
      simp [Pi.add_apply, *]
    · rw [ht_add]; omega

@[expose] def fA2 : (Fin (Tag.rank .E7) → ℤ) →+ ℤ := Pi.evalAddMonoidHom (fun _ => ℤ) nodeA2

@[expose] def fNu : (Fin (Tag.rank .E7) → ℤ) →+ ℤ := Pi.evalAddMonoidHom (fun _ => ℤ) nodeNu

@[expose] def ordD6 : List ℕ :=
  [93, 85, 75, 76, 64, 65, 50, 51, 52, 54, 37, 38, 40, 42, 23, 24, 26, 28, 30, 10, 12, 14, 16,
   18, 1, 2, 3, 4, 5, 6]

@[expose] def covD6 : List (List ℕ) :=
  [[], [0], [0, 1], [0, 1], [0, 2, 3], [0, 1, 3], [1, 2, 3, 4], [0, 2, 4, 5], [0, 1, 3, 5],
   [0, 1, 3, 5], [1, 2, 5, 6, 7], [0, 2, 4, 7, 8], [0, 2, 4, 7, 9], [0, 1, 3, 8, 9],
   [3, 4, 5, 6, 7, 10], [1, 2, 6, 8, 10, 11], [1, 2, 6, 9, 10, 12], [0, 2, 4, 11, 12, 13],
   [0, 1, 5, 8, 9, 13], [3, 4, 6, 8, 11, 14, 15], [3, 4, 6, 9, 12, 14, 16],
   [1, 2, 6, 13, 15, 16, 17], [0, 2, 7, 11, 12, 17, 18], [0, 3, 5, 8, 9, 13, 18],
   [5, 7, 8, 10, 11, 14, 15, 19], [5, 7, 9, 10, 12, 14, 16, 20], [3, 4, 6, 13, 17, 19, 20, 21],
   [1, 2, 10, 15, 16, 18, 21, 22], [0, 4, 7, 11, 12, 17, 22, 23], [1, 3, 5, 8, 9, 13, 18, 23]]

@[expose] def badD6 : List (List ℕ) :=
  [[], [], [], [], [], [], [], [], [], [], [], [9], [8], [7, 10], [13], [9, 12], [8, 11],
   [5, 10, 14], [4, 6, 14], [9, 12, 16, 18], [8, 11, 15, 18], [5, 7, 14], [3, 6, 14, 19, 20],
   [2, 6, 10, 15, 16, 21], [9, 12, 13, 16, 17, 20, 21], [8, 11, 13, 15, 17, 19, 21],
   [5, 7, 10, 18, 22, 24, 25], [3, 4, 14, 19, 20, 23, 26], [1, 6, 10, 15, 16, 21, 27],
   [2, 4, 7, 11, 12, 17, 22, 28]]

variable {K : Type} [Field K]

@[expose] def rtD6 (i : ℕ) : Rt := (Tag.rootCertificate .E7).root (ordD6.getD i 0)

@[expose] def cvD6 (k : ℕ) : List ℕ := covD6.getD k []

@[expose] def bdD6 (k : ℕ) : List ℕ := badD6.getD k []

theorem rtD6_pos : ∀ i < 30, 0 < ht (rtD6 i) := by decide +kernel

theorem rtD6_node1 : ∀ i < 30, rtD6 i node1 = 0 := by decide +kernel

theorem ordD6_lt : ∀ i < 30, ordD6.getD i 0 < 126 := by decide +kernel

theorem isRoot_rtD6 {i : ℕ} (hi : i < 30) : IsRoot .E7 (rtD6 i) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) _ (by have := ordD6_lt i hi; omega)

theorem rtD6_mem_Rd6 {i : ℕ} (hi : i < 30) : rtD6 i ∈ Rd6 :=
  mem_Rd6.2 ⟨perp_iff.2 ⟨isRoot_rtD6 hi, rtD6_node1 i hi⟩, rtD6_pos i hi⟩

theorem exists_rtD6 {γ : Rt} (hγ : IsRoot .E7 γ) (h0 : γ node1 = 0) (hp : 0 < ht γ) :
    ∃ i < 30, rtD6 i = γ := by
  revert h0 hp
  refine (forall_isRoot_iff fun γ => γ node1 = 0 → 0 < ht γ → ∃ i < 30, rtD6 i = γ).2 ?_ γ hγ
  decide +kernel

theorem rtD6_inj : ∀ i < 30, ∀ j < 30, rtD6 i = rtD6 j → i = j := by decide +kernel

theorem cvD6_sound : ∀ k < 30, ∀ m ∈ cvD6 k, ∃ j < 30, rtD6 k + rtD6 j = rtD6 m := by decide +kernel

theorem bdD6_sound : ∀ k < 30, ∀ j ∈ bdD6 k, ∃ m < 30, rtD6 k + rtD6 j = rtD6 m := by decide +kernel

theorem cvD6_lt30 : ∀ k < 30, ∀ m ∈ cvD6 k, m < k := by decide +kernel

theorem cvD6_lt (k m : ℕ) (hm : m ∈ cvD6 k) : m < k := by
  by_cases hk : k < 30
  · exact cvD6_lt30 k hk m hm
  · have hlen : covD6.length = 30 := by decide +kernel
    have : cvD6 k = [] := List.getD_eq_default _ _ (by omega)
    rw [this] at hm
    simp at hm

@[expose] def S2idx : Finset ℕ := (Finset.range 30).filter fun i => rtD6 i nodeA2 = 1

@[expose] def S3idx : Finset ℕ := (Finset.range 30).filter fun i => rtD6 i nodeNu = 1

theorem ideals_card_ge_15 :
    ∀ S ∈ ideals cvD6 bdD6 30, 15 ≤ S.toFinset.card → S.toFinset = S2idx ∨ S.toFinset = S3idx := by
  decide +kernel

theorem hIdeal_D6 : ∀ A : Finset Rt, A ⊆ Rd6 → (∀ α ∈ A, ∀ β ∈ A, ¬ IsRoot .E7 (α + β)) →
    (∀ α ∈ A, ∀ β ∈ Rd6, IsRoot .E7 (α + β) → α + β ∈ A) → 15 ≤ A.card →
    A = Rn fA2 Rd6 ∨ A = Rn fNu Rd6 := by
  classical
  intro A hAsub habel hup hcard
  set T : Finset ℕ := (Finset.range 30).filter fun i => rtD6 i ∈ A with hT
  have hmemT : ∀ i, i ∈ T ↔ i < 30 ∧ rtD6 i ∈ A := fun i => by
    simp [hT]
  have hlt : ∀ i ∈ T, i < 30 := fun i hi => ((hmemT i).1 hi).1
  have hAT : A = T.image rtD6 := by
    ext γ
    rw [Finset.mem_image]
    constructor
    · intro hγ
      have hγR := mem_Rd6.1 (hAsub hγ)
      have hγ' := perp_iff.1 hγR.1
      obtain ⟨i, hi, hiγ⟩ := exists_rtD6 hγ'.1 hγ'.2 hγR.2
      exact ⟨i, (hmemT i).2 ⟨hi, hiγ ▸ hγ⟩, hiγ⟩
    · rintro ⟨i, hi, rfl⟩
      exact ((hmemT i).1 hi).2
  have hTcard : 15 ≤ T.card := by
    have hinj : Set.InjOn rtD6 (T : Set ℕ) := fun i hi j hj hij =>
      rtD6_inj i (hlt i hi) j (hlt j hj) hij
    calc 15 ≤ A.card := hcard
      _ = (T.image rtD6).card := by rw [← hAT]
      _ = T.card := Finset.card_image_of_injOn hinj
  have hcovT : ∀ i ∈ T, ∀ m ∈ cvD6 i, m ∈ T := by
    intro i hi m hm
    have hi30 := hlt i hi
    have hiA := ((hmemT i).1 hi).2
    obtain ⟨j, hj, hsum⟩ := cvD6_sound i hi30 m hm
    have hmi := cvD6_lt i m hm
    refine (hmemT m).2 ⟨by omega, ?_⟩
    have h1 : IsRoot .E7 (rtD6 i + rtD6 j) := by
      rw [hsum]
      exact isRoot_rtD6 (by omega)
    have h2 := hup _ hiA (rtD6 j) (rtD6_mem_Rd6 hj) h1
    rwa [hsum] at h2
  have hbadT : ∀ i ∈ T, ∀ j ∈ bdD6 i, j ∉ T := by
    intro i hi j hj hjT
    obtain ⟨m, hm, hsum⟩ := bdD6_sound i (hlt i hi) j hj
    have hiA := ((hmemT i).1 hi).2
    have hjA := ((hmemT j).1 hjT).2
    exact habel _ hiA _ hjA (by rw [hsum]; exact isRoot_rtD6 hm)
  obtain ⟨S, hS, hSeq⟩ := mem_ideals cvD6 bdD6 cvD6_lt 30 T hlt hcovT hbadT
  have hS23 : T = S2idx ∨ T = S3idx := by
    rw [← hSeq]
    exact ideals_card_ge_15 S hS (by rw [hSeq]; exact hTcard)
  have key : ∀ (n : Fin (Tag.rank .E7)), T = (Finset.range 30).filter (fun i => rtD6 i n = 1) →
      A = Rn (Pi.evalAddMonoidHom (fun _ => ℤ) n) Rd6 := by
    intro n hTn
    rw [hAT, hTn]
    ext γ
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hi30, hpr⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_filter.2 ⟨rtD6_mem_Rd6 (Finset.mem_range.1 hi30), hpr⟩
    · intro hγ
      obtain ⟨hγR, hγ1⟩ := Finset.mem_filter.1 hγ
      have hγR' := mem_Rd6.1 hγR
      have hγ' := perp_iff.1 hγR'.1
      obtain ⟨i, hi, hiγ⟩ := exists_rtD6 hγ'.1 hγ'.2 hγR'.2
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, by rw [hiγ]; exact hγ1⟩, hiγ⟩
  rcases hS23 with h | h
  · exact Or.inl (key nodeA2 h)
  · exact Or.inr (key nodeNu h)

end CFSG.RankThree.GF2n.Smith81.D6Spin

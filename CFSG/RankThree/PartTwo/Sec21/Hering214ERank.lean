module

public import CFSG.RankThree.PartTwo.Sec21.Hering214ESplit
public import CFSG.RankThree.PartTwo.Sec21.Hering214ERankP
public import CFSG.RankThree.PartTwo.Sec21.Hering214ERankQ
public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofBar
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (localRank)
open Item211Res2Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem forall_eq_zpow_mul_of_even {A E U L : Subgroup G} {c : G}
    (hPF : Item211LieProof.PairFacts A E U c L) (h3 : localRank 3 G ≤ 3) [Group.IsPerfect L]
    (hθc : aschbacherSolvableCore 3 L ≤ Subgroup.center L)
    (heven : Even (Nat.card (aschbacherSolvableCore 3 L)))
    (hinn : barImage L E ≤ (MulAut.conj : lBar L →* MulAut (lBar L)).range)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center L))
    (hQ : ∃ Q : Subgroup G, Q ≤ L ∧ IsElemAbelian 3 Q ∧ Nat.card Q = 9) :
    c ∉ L ∧ ∀ e ∈ E, ∃ k : ℤ, ∃ y ∈ E ⊓ L, e = c ^ k * y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcL : c ∉ L := by
    intro hc
    have hcZ : (⟨c, hc⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hPF.L_le_centralizer g.2)) c rfl).symm
    set z : Subgroup.center L := ⟨⟨c, hc⟩, hcZ⟩ with hz
    have hz3 : z ^ 3 = 1 := Subtype.ext (Subtype.ext (by simp [z, hPF.c3]))
    have hz1 : z ≠ 1 := fun h => hPF.c1 (by
      simpa [z] using congrArg (fun w : Subgroup.center L => ((w : L) : G)) h)
    exact hZ3 ((orderOf_eq_prime hz3 hz1) ▸ orderOf_dvd_natCard z)
  have hsplit : ∀ e ∈ E, ∃ l ∈ L, ∃ z ∈ Subgroup.centralizer (L : Set G), e = l * z := by
    intro e he
    have heN := hPF.EL he
    have hp : IsPGroup 3 (Subgroup.zpowers e) := fun g => ⟨1, Subtype.ext (by
      simpa using hPF.Ee.2 _ ((Subgroup.zpowers_le.mpr he) g.2))⟩
    have hinn' : barAct L ⟨e, heN⟩ ∈ (MulAut.conj : lBar L →* MulAut (lBar L)).range :=
      hinn (mem_barImage_iff.mpr ⟨e, heN, he, rfl⟩)
    obtain ⟨l, hl, z, hz, rfl, -⟩ := exists_mul_of_barAct_inner hθc heN hp hinn'
    exact ⟨l, hl, z, hz, rfl⟩
  have hdvd : Nat.card (E ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hPF.E27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk3, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have h3' : Nat.card (E ⊓ L : Subgroup G) ≤ 3 := by
        rw [hkeq]
        interval_cases k <;> norm_num
      obtain ⟨P, hPC, hP, hP9, hPL⟩ :=
        exists_elemAbelian_nine_le_centralizer hPF.Ee hPF.E27 hsplit hZ3 h3'
      obtain ⟨Q, hQL, hQe, hQ9⟩ := hQ
      exact false_of_elemAbelian_nine_le_centralizer h3 heven hQL hQe hQ9 hPC hP hP9 hPL
    have hk3' : k ≠ 3 := by
      rintro rfl
      have heq : E ⊓ L = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by
        rw [hkeq, hPF.E27]; norm_num)
      have hcEL : c ∈ E ⊓ L := by rw [heq]; exact hPF.cE
      exact hcL hcEL.2
    have hk : k = 2 := by omega
    rw [hkeq, hk]
    norm_num
  set B := E ⊓ L with hBdef
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ⟨?_, ?_⟩
    · rw [hPF.E_comm c hPF.cE x hx.1, mul_inv_cancel_right]
      exact hx.1
    · exact (Subgroup.mem_normalizer_iff.mp (hPF.EL hPF.cE) x).mp hx.2
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hPF.orderOf_c]
  have hdisj : Disjoint B (Subgroup.zpowers c) := by
    have hdvd3 : Nat.card (Subgroup.zpowers c ⊓ B : Subgroup G) ∣ 3 :=
      hc3 ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3c
    · rw [disjoint_iff, inf_comm]
      exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers c ⊓ B = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3c, hc3])
      have hmem : c ∈ Subgroup.zpowers c ⊓ B := by rw [heq]; exact Subgroup.mem_zpowers c
      exact hcL hmem.2.2
  have hcard : Nat.card (B ⊔ Subgroup.zpowers c : Subgroup G) = 27 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B _ hcN hdisj,
      hc3, hEL9]
  have hle : B ⊔ Subgroup.zpowers c ≤ E :=
    sup_le inf_le_left (Subgroup.zpowers_le.mpr hPF.cE)
  have hEq : B ⊔ Subgroup.zpowers c = E :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hPF.E27])
  refine ⟨hcL, fun e he => ?_⟩
  rw [← hEq, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at he
  obtain ⟨w, hw, y, hy, rfl⟩ := he
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨m, y, hy, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.Hering214Even

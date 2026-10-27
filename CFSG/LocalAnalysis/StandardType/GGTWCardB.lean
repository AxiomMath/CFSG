module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWDFalse
public import CFSG.LocalAnalysis.StandardType.GGTWDCells36Orb
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
public import CFSG.LocalAnalysis.StandardType.GGTWCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTWCardJ
public import CFSG.GroupTheory.SubgroupCardMul

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nCB_card_mul_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hZJ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J)) :
    Nat.card ↥(Bs ⊓ J) * p ^ 2 ≤ Nat.card ↥Bs := by
  have hC : GGConfig p B Bs x L D J := hH.1
  unfold GGConfig at hC
  have hStd : LargeEvenStdSub p B x L D J := hC.2.2
  have hPre : LargeEvenStdSubPre p B x L D J := hStd.1
  unfold LargeEvenStdSubPre at hPre
  obtain ⟨hDleB, _hElem, hDcard, _hxD, _hJ, _hIC, hDeq⟩ := hPre
  have hBleBs : B ≤ Bs := hC.2.1.1
  have hDcent : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [hDeq]
    exact inf_le_right
  have hZJ' : ¬ p ∣ Nat.card ↥((Subgroup.center ↥J).map J.subtype) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective J)]
    exact hZJ
  have hDJleZJ : D ⊓ J ≤ (Subgroup.center ↥J).map J.subtype := by
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgD, hgJ⟩ := hg
    rw [Subgroup.mem_map]
    refine ⟨⟨g, hgJ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    show (j : G) * g = g * (j : G)
    exact (Subgroup.mem_centralizer_iff.mp (hDcent hgD)) (j : G) j.2
  have hDJdvdZJ : Nat.card ↥(D ⊓ J) ∣
      Nat.card ↥((Subgroup.center ↥J).map J.subtype) :=
    Subgroup.card_dvd_of_le hDJleZJ
  have hDJnotp : ¬ p ∣ Nat.card ↥(D ⊓ J) := fun h => hZJ' (h.trans hDJdvdZJ)
  have hDp : IsPGroup p ↥D :=
    IsPGroup.of_card_dvd_pow (n := 2) (by rw [hDcard])
  have hDJp : IsPGroup p ↥(D ⊓ J) := hDp.to_le inf_le_left
  have hDJcard : Nat.card ↥(D ⊓ J) = 1 := by
    rcases hDJp.card_eq_or_dvd with h1 | hdiv
    · exact h1
    · exact absurd hdiv hDJnotp
  have hDJbot : D ⊓ J = ⊥ := Subgroup.card_eq_one.mp hDJcard
  have hHDbot : (Bs ⊓ J) ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨⟨_hgBs, hgJ⟩, hgD⟩ := hg
    have hmem : g ∈ D ⊓ J := ⟨hgD, hgJ⟩
    rwa [hDJbot] at hmem
  have hle := CFSG.card_mul_card_le_of_inf_eq_bot (A := Bs) (D := Bs ⊓ J) (D' := D)
    inf_le_left (hDleB.trans hBleBs) hHDbot
  rwa [hDcard] at hle

theorem ggTW_card_ge {G : Type} [Group G] [Finite G] {p N k : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) {B Bs : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hk : k = 1 ∨ k = 2)
    (hZJ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    (hA : GGTWAligned p N k Bs L J K ∨ GGTWAligned p N k Bs K J L) :
    p ^ (N - 1) ≤ Nat.card ↥Bs := by
  have hN5 : 5 ≤ N := by rcases hN with rfl | rfl | rfl | rfl | rfl <;> omega
  have hpow : p ^ (N - 3) * p ^ 2 = p ^ (N - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hmul : p ^ (N - 3) * p ^ 2 ≤ Nat.card ↥(Bs ⊓ J) * p ^ 2 :=
    Nat.mul_le_mul_right _ (ggTW_inf_J_ge hp hpN hN hH hk hA)
  exact (hpow ▸ hmul).trans (l05nCB_card_mul_le hH hZJ)

theorem ggTW_inf_J_card {G : Type} [Group G] [Finite G] {p N k : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 9) {B Bs : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hk : k = 1 ∨ k = 2)
    (hCard : Nat.card ↥Bs = p ^ (N - 1)) (hZJ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    (hA : GGTWAligned p N k Bs L J K ∨ GGTWAligned p N k Bs K J L) :
    Nat.card ↥(Bs ⊓ J) = p ^ (N - 3) := by
  have hN5 : 5 ≤ N := by rcases hN with rfl | rfl | rfl <;> omega
  have hN' : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10 := by
    rcases hN with h | h | h <;> tauto
  have hpow : p ^ (N - 1) = p ^ (N - 3) * p ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hle : Nat.card ↥(Bs ⊓ J) * p ^ 2 ≤ p ^ (N - 3) * p ^ 2 := by
    have h := l05nCB_card_mul_le hH hZJ
    rwa [hCard, hpow] at h
  have hle' : Nat.card ↥(Bs ⊓ J) ≤ p ^ (N - 3) :=
    Nat.le_of_mul_le_mul_right hle (pow_pos (by omega : 0 < p) 2)
  exact le_antisymm hle' (ggTW_inf_J_ge hp hpN hN' hH hk hA)

end CFSG.StandardType

end

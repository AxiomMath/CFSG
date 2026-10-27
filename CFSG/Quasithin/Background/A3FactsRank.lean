module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.Quasithin

namespace A3Facts

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

theorem pRank_prod_ge {S T : Type} [Group S] [Group T] [Finite S] [Finite T] {p : ℕ}
    (hp : 1 < p) :
    CFSG.Open.pRank p (⊤ : Subgroup S) + CFSG.Open.pRank p (⊤ : Subgroup T) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (S × T)) := by
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp (⊤ : Subgroup S)
  obtain ⟨F, -, hF, hFc⟩ := CFSG.SectionRank.exists_pRank hp (⊤ : Subgroup T)
  have hEcomm : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have hFcomm : ∀ a b : F, a * b = b * a := fun a b => hF.1.is_comm.comm a b
  refine CFSG.SectionRank.le_pRank_of_injective (A := E × F) hp ?_ ?_ ?_
    (f := (E.subtype.prodMap F.subtype)) ?_ (H := ⊤) le_top
  · rintro ⟨a, b⟩ ⟨a', b'⟩
    exact Prod.ext (hEcomm a a') (hFcomm b b')
  · rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (hE.2 a a.2)) (Subtype.ext (hF.2 b b.2))
  · rw [Nat.card_prod, hEc, hFc, pow_add]
  · exact Prod.map_injective.2 ⟨E.subtype_injective, F.subtype_injective⟩

theorem one_le_pRank_of_orderOf {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime) {x : S}
    (hx : orderOf x = r) : 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup S) := by
  have : Fact r.Prime := ⟨hr⟩
  refine CFSG.SectionRank.le_pRank hr.one_lt (le_top : Subgroup.zpowers x ≤ ⊤) ⟨?_, ?_⟩ ?_
  · exact ⟨⟨fun a b => by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
      apply Subtype.ext
      change (a : S) * b = b * a
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]⟩⟩
  · intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
      one_zpow]
  · rw [Nat.card_zpowers, hx, pow_one]

theorem exists_odd_prime_pRank_pos {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup S) := by
  by_contra hcon
  push Not at hcon
  have hfin : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card S → d = 2 := by
    intro d hd hdvd
    by_contra hd2
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) d hdvd
    exact absurd (hcon d hd hd2) (not_lt.2 (one_le_pRank_of_orderOf hd hx))
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hfin
    (fun {d} hd hdvd => hall hd hdvd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 S := IsPGroup.of_card hpow
  obtain ⟨a, b, hab⟩ := hnonab
  have : Nontrivial S := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hcn := hP.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact (Subgroup.nontrivial_iff_ne_bot _ |>.1 hcn) h
  · exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a)

theorem two_le_pRank_of_gens {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : Commute x y) (hx1 : x ≠ 1)
    (hy1 : ∀ n : ℕ, x ^ n ≠ y) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
  CFSG.SectionRank.two_le_pRank_top_of_commute hx hy hxy hx1 hy1

theorem two_le_pRank_of_not_isCyclic {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨S, -, hS, hSe⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hSe' : CFSG.Open.IsElemAbelian p S :=
    (isElementaryAbelian_iff_isElemAbelian p S).1 hSe
  refine CFSG.SectionRank.le_pRank hp.out.one_lt (le_top : S.map P.subtype ≤ ⊤)
    (isElemAbelian_map hSe' _) ?_
  rw [Subgroup.card_map_of_injective P.subtype_injective, hS]

theorem two_le_pRank_of_cubic {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {x y : G} (hxy : ⁅x, y⁆ ≠ 1)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 3) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  refine two_le_pRank_of_not_isCyclic hp2 (P := Subgroup.closure ({x, y} : Set G))
    (IsPGroup.of_card hcard) fun hcyc => hxy ?_
  have hcomm : x * y = y * x := by
    have := hcyc.isMulCommutative
    exact congrArg Subtype.val (this.is_comm.comm ⟨x, Subgroup.subset_closure (by simp)⟩
      ⟨y, Subgroup.subset_closure (by simp)⟩)
  rw [commutatorElement_def, hcomm]
  group

theorem two_le_pRank_of_square {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 2) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have hz : ∀ z : G, z ^ p = 1 → Nat.card (Subgroup.zpowers z) ≤ p := fun z hz => by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one hz)
  have hp2 : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  refine two_le_pRank_of_gens hx hy hxy ?_ fun n h => ?_
  · rintro rfl
    have hle : Subgroup.closure ({1, y} : Set G) ≤ Subgroup.zpowers y := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    have := hz y hy
    omega
  · have hle : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.zpowers x := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_zpowers _
      · rw [← h]
        exact Subgroup.npow_mem_zpowers x n
    have := Subgroup.card_le_of_le hle
    have := hz x hx
    omega

@[expose] def OddRankTwo (S : Type) [Group S] [Finite S] : Prop :=
  ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup S)

theorem OddRankTwo.of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    (e : S ≃* T) (h : OddRankTwo T) : OddRankTwo S := by
  obtain ⟨r, hr, hr2, h2⟩ := h
  exact ⟨r, hr, hr2, by rw [pRank_top_eq_of_mulEquiv hr.one_lt e]; exact h2⟩

end A3Facts

end CFSG.Quasithin

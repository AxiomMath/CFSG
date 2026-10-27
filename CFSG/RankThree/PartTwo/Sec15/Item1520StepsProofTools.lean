module

public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1520

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {E : Subgroup G} (K : Subgroup G)
    (hE : CFSG.Assembly.IsElemAbelian p E) : CFSG.Assembly.IsElemAbelian p (E.subgroupOf K) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE K

omit [Finite G] in
theorem card_subgroupOf_inf (H K : Subgroup G) :
    Nat.card ↥((H ⊓ K).subgroupOf K) = Nat.card ↥(H ⊓ K) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem isoLThreePi_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) {p n : ℕ}
    [Fact p.Prime] (h : Sec4.IsoLThreePi T p n) : Sec4.IsoLThreePi S p n := by
  rcases h with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
  · exact Or.inl ⟨h1, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨h2, ⟨e.trans f⟩⟩

theorem theta_eq_bot_of_isSimpleGroup {L : Subgroup G} {c : G}
    (hL : L ∈ thetaComponentsAt 3 c) (hs : IsSimpleGroup ↥L) :
    aschbacherSolvableCore 3 ↥L = ⊥ := by
  obtain ⟨hsolv, -⟩ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 ↥L) with h | h
  · exact h
  · exfalso
    have hperf : Group.IsPerfect ↥L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
    rw [h] at hsolv
    have : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (f := (Subgroup.topEquiv (G := ↥L)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := ↥L)).symm.injective
    exact Group.IsPerfect.not_isSolvable ↥L this

omit [Finite G] in
theorem not_mem_of_isSimpleGroup {L : Subgroup G} {c : G} (hL : L ∈ thetaComponentsAt 3 c)
    (hs : IsSimpleGroup ↥L) (hc1 : c ≠ 1) : c ∉ L := by
  intro hcL
  have hperf : Group.IsPerfect ↥L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hcen : Subgroup.center ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exfalso
      have : Group.IsSolvable ↥L := Group.isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
      exact Group.IsPerfect.not_isSolvable ↥L this
  have hmem : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt hL g.2)
    exact Subtype.ext hg
  rw [hcen, Subgroup.mem_bot] at hmem
  exact hc1 (congrArg Subtype.val hmem)

omit [Finite G] in
theorem isoLThreePi_of_theta_eq_bot {K : Subgroup G} (hθ : aschbacherSolvableCore 3 ↥K = ⊥)
    {p e : ℕ} [Fact p.Prime] (h : Sec4.IsoLThreePi (↥K ⧸ aschbacherSolvableCore 3 ↥K) p e) :
    Sec4.IsoLThreePi ↥K p e :=
  isoLThreePi_of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hθ.symm)) h

theorem iso_of (h1517 : Step1517R) {A : Subgroup G} {c : G} {L Y : Subgroup G}
    (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y) {p : ℕ} {P : Subgroup G}
    (hP : Data1519 A (lB A) L p P) :
    ∃ m : ℕ, 1 ≤ m ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m ∧
      Sec4.IsoLThreePi ↥L 2 m ∧ IsSimpleGroup ↥L := by
  obtain ⟨m, hm1, hiso, -⟩ := hP.2.2.1
  have hs : IsSimpleGroup ↥L := (h1517 G A c L h Y hctx).2.1
  have hθ := theta_eq_bot_of_isSimpleGroup h.mem_thetaComponentsAt hs
  exact ⟨m, hm1, hiso, isoLThreePi_of_theta_eq_bot hθ hiso, hs⟩

theorem config_of (h1517 : Step1517R) (h138 : Item138N) {A : Subgroup G} {c : G}
    {L Y : Subgroup G} (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y) {p : ℕ}
    {P : Subgroup G} (hP : Data1519 A (lB A) L p P) :
    ∃ m : ℕ, 1 ≤ m ∧ Sec4.IsoLThreePi ↥L 2 m ∧ ¬ (2 ^ m % 9 = 1 ∨ 2 ^ m % 9 = 8) ∧
      IsSimpleGroup ↥L ∧ c ∉ L ∧ Nat.card ↥(A ⊓ L) = 9 ∧ A ≤ Subgroup.zpowers c ⊔ L := by
  obtain ⟨m, hm1, hiso, hisoL, hs⟩ := iso_of h1517 h hctx hP
  obtain ⟨-, -, -, -, -, hprod, -, -, -⟩ := hctx.concl1515
  have h9 : ¬ (2 ^ m % 9 = 1 ∨ 2 ^ m % 9 = 8) :=
    not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC hm1 hiso hprod
  have hcL : c ∉ L := not_mem_of_isSimpleGroup h.mem_thetaComponentsAt hs h.ne_one
  have h9AL : Nat.card ↥(A ⊓ L) = 9 :=
    card_inf_eq_nine h.toSec13Data (isPerfect_lBar h.toSec13Data) hprod.some
  exact ⟨m, hm1, hisoL, h9, hs, hcL, h9AL, Sec16.le_sup_of_card_inf h hcL h9AL⟩

end CFSG.RankThree.PartTwo.Sec15.Proof1520

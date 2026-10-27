module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Linear
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.RankThree.SubgroupLists.SL2Perfect
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.RankThree.PartTwo.Sec21.Item229Pre

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.OrderReductions.FrattiniAutomorphisms
open scoped MatrixGroups

theorem false_of_mulEquiv_SL2 {S : Type*} [Group S] [IsSimpleGroup S]
    (hnc : ∃ x y : S, x * y ≠ y * x) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (e : S ≃* SL(2, ZMod p)) : False := by
  have hcard : Nat.card (Subgroup.center SL(2, ZMod p)) = 2 := Sec4.Census.card_center_SL2 hp2
  have hne : Subgroup.center SL(2, ZMod p) ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot _).mp (by omega)
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hs : e.symm g ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hg (e t)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · rw [h, Subgroup.mem_bot] at hs
    apply hg1
    apply Subtype.ext
    have := congrArg e hs
    simpa using this
  · obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)

theorem acts_trivially_of_rank_le_two {P S : Type*} [Group P]
    [Finite P] [Group S] [Finite S] [IsSimpleGroup S] (hSnc : ∃ x y : S, x * y ≠ y * x) {q : ℕ}
    [hq : Fact q.Prime] (hq2 : q ≠ 2) (hPp : IsPGroup q P) (hexp : ∀ x : P, x ^ q = 1)
    (hclass : commutator P ≤ Subgroup.center P) (hrank : CFSG.pRank q P ≤ 2)
    (ρ : S →* MulAut P) : ρ = 1 := by
  have hSperf : Group.IsPerfect S := isPerfect_of_isSimpleGroup hSnc
  set V := P ⧸ frattini P
  obtain ⟨-, hcomm, hpow, -, d, hd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hPp
  have hd2 : d ≤ 2 := by
    have h1 := (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hPp hexp hclass).1 hrank
    have hfc := CFSG.RankThree.PartTwo.frattini_eq_commutator hPp hexp
    have hd' : Nat.card (P ⧸ commutator P) = q ^ d := by
      rw [← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hfc).toEquiv]
      exact hd
    rwa [CFSG.RankThree.PartTwo.pRank_eq_of_isMulCommutative hq.out
      (CFSG.RankThree.PartTwo.quotient_pow_eq_one hexp _)
      CFSG.RankThree.PartTwo.isMulCommutative_quotient_commutator hd'] at h1
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := V)
    (fun a b => hcomm.is_comm.comm a b) hpow hd
  set ρ' : S →* GL (Fin d) (ZMod q) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp
      ((quotientAutomorphism (frattini P)).comp ρ) with hρ'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ'.ker with hker | hker
  ·
    exfalso
    have hinj : Function.Injective ρ' := (MonoidHom.ker_eq_bot_iff _).mp hker
    have : Nontrivial S := IsSimpleGroup.toNontrivial
    have hne : ρ'.range ≠ ⊥ := by
      intro hbot
      obtain ⟨x, hx⟩ := exists_ne (1 : S)
      have : ρ' x ∈ ρ'.range := ⟨x, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hx (hinj (this.trans (map_one ρ').symm))
    haveI : Group.IsPerfect ρ'.range := Group.IsPerfect.range ρ'
    have eρ : S ≃* ρ'.range := MonoidHom.ofInjective hinj
    by_cases hd2' : d = 2
    · subst hd2'
      rcases CFSG.RankThree.SubgroupLists.perfect_gl2_mulEquiv hq2 ρ'.range hne with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩
      · exact false_of_mulEquiv_SL2 hSnc hq2 (eρ.trans e')
      · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        exact false_of_mulEquiv_SL2 hSnc (by norm_num) (eρ.trans e')
    ·
      obtain ⟨x, y, hxy⟩ := hSnc
      apply hxy
      apply hinj
      rw [map_mul, map_mul]
      exact Sec4.Census.GL_comm_of_le_one (by omega) _ _
  ·
    obtain ⟨-, hkerP⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hPp
    have hρker : ∀ s : S, ρ s ∈ (quotientAutomorphism (frattini P)).ker := by
      intro s
      have hs : s ∈ ρ'.ker := by rw [hker]; exact Subgroup.mem_top s
      rw [MonoidHom.mem_ker] at hs ⊢
      have := (CFSG.SectionRank.Ccomm.elemAutEquivGL e).map_eq_one_iff.mp hs
      exact this
    set g : S →* (quotientAutomorphism (frattini P)).ker :=
      ρ.codRestrict _ hρker with hg
    haveI : Group.IsNilpotent (quotientAutomorphism (frattini P)).ker := hkerP.isNilpotent
    haveI : Group.IsPerfect g.range := Group.IsPerfect.range g
    have hrange : g.range = ⊥ := by
      by_contra hne
      haveI : Nontrivial g.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isSolvable g.range inferInstance
    refine MonoidHom.ext fun s => ?_
    have h1 : g s ∈ g.range := ⟨s, rfl⟩
    rw [hrange, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1

end CFSG.RankThree.PartTwo.Sec21.Hering233i

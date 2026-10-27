module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Local
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44End
import CFSG.RankThree.SubgroupLists.SL2Perfect
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Matrix CFSG.OrderReductions.FrattiniAutomorphisms
open scoped MatrixGroups commutatorElement

variable {X : Type*} [Group X] [Finite X]

theorem GL_comm_of_le_one {R : Type*} [CommRing R] {d : ℕ} (hd : d ≤ 1) (a b : GL (Fin d) R) :
    a * b = b * a :=
  CFSG.SectionRank.Ccomm.GL_comm_of_le_one hd a b

omit [Finite X] in
theorem CriticalAt.commutator_le_center {p : ℕ} {D : Subgroup X} (h : CriticalAt p D) :
    commutator D ≤ Subgroup.center D := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_center_iff]
  intro d
  apply Subtype.ext
  have := (h.comm a a.2 b (h.le b.2)).2 d d.2
  simp only [commutatorElement_def] at this ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact this.symm

variable [Group.IsPerfect X] {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)]

theorem linearOutcome_of_criticalAt (hK : Group.IsSolvable K) {p : ℕ} [hp : Fact p.Prime]
    (hp3 : 3 < p) (hpS : Subgroup.centralizer (pCore p X : Set X) ≤ K) {D : Subgroup X}
    (h : CriticalAt p D) (hD : CFSG.pRank p D ≤ 2) :
    ∃ (N : Subgroup X) (_ : N.Normal), LinearOutcome X p N := by
  have hDp : IsPGroup p D := pCore_isPGroup.to_le h.le
  have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, h.exp x x.2, Subgroup.coe_one])
  have hclass := h.commutator_le_center
  set V := D ⧸ frattini D
  obtain ⟨-, hcomm, hpow, -, d, hd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  have hd2 : d ≤ 2 := by
    have h1 := (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDp hexp hclass).1 hD
    have hfc := CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hexp
    have hd' : Nat.card (D ⧸ commutator D) = p ^ d := by
      rw [← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hfc).toEquiv]
      exact hd
    rwa [CFSG.RankThree.PartTwo.pRank_eq_of_isMulCommutative hp.out
      (CFSG.RankThree.PartTwo.quotient_pow_eq_one hexp _)
      CFSG.RankThree.PartTwo.isMulCommutative_quotient_commutator hd'] at h1
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := V)
    (fun a b => hcomm.is_comm.comm a b) hpow hd
  set ρ : X →* GL (Fin d) (ZMod p) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp h.frattiniAct
  have hker : ρ.ker = h.frattiniKer := by
    ext x
    rw [MonoidHom.mem_ker, h.mem_frattiniKer_iff]
    change (CFSG.SectionRank.Ccomm.elemAutEquivGL e) (h.frattiniAct x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
  have hNK : h.frattiniKer ≤ K := h.frattiniKer_le hK hpS
  have hN : h.frattiniKer.Normal := h.frattiniKer_normal
  refine ⟨h.frattiniKer, hN, ⟨fun y hy hyp x hx => ?_, ?_⟩⟩
  · have := h.centralizes_of_mem_frattiniKer hy hyp x hx
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [this]
  ·
    have hne : ρ.range ≠ ⊥ := by
      intro hbot
      have htop : ρ.ker = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have : ρ x ∈ ρ.range := ⟨x, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      rw [hker] at htop
      have hKtop : K = ⊤ := top_le_iff.mp (htop ▸ hNK)
      exact (QuotientGroup.nontrivial_iff.mp inferInstance) hKtop
    have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    have hd2' : d = 2 := by
      by_contra hd2'
      apply hne
      have hcomm' : ∀ a b : ρ.range, a * b = b * a := fun a b =>
        Subtype.ext (GL_comm_of_le_one (by omega) _ _)
      have : IsMulCommutative ρ.range := ⟨⟨hcomm'⟩⟩
      have : Subsingleton ρ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
      rw [eq_bot_iff]
      intro g hg
      have := Subsingleton.elim (⟨g, hg⟩ : ρ.range) 1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    subst hd2'
    have hp2 : p ≠ 2 := by omega
    have eρ : X ⧸ h.frattiniKer ≃* ρ.range :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ρ)
    rcases CFSG.RankThree.SubgroupLists.perfect_gl2_mulEquiv hp2 ρ.range hne with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩
    · exact Or.inl ⟨hp3, ⟨eρ.trans e'⟩⟩
    · exact Or.inr (Or.inl ⟨eρ.trans e'⟩)

end CFSG.RankThree.PartTwo.Sec4.Census

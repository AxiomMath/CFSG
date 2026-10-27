module

public import CFSG.RankThree.PartTwo.KFacts.K73Recognition
public import CFSG.RankThree.PartTwo.Sec10.Item108

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item102 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R →
      Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} = Subgroup.zpowers a ⊔ sec10D c R L ∧
      (∃ e ∈ R ⊓ L, KFacts.WreathData e a ∧
        Subgroup.closure {e, a} = Subgroup.zpowers a ⊔ (R ⊓ L)) ∧
      c ∉ Subgroup.zpowers a ⊔ (R ⊓ L) ∧
      ((R ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c ∧
          R = Subgroup.zpowers a ⊔ sec10D c R L) ∨
        ((∀ σ : MulAut R, ((Subgroup.zpowers c).subgroupOf R).map σ.toMonoidHom =
            (Subgroup.zpowers c).subgroupOf R) ∧
          CFSG.ABGLocalTools.IsSylowOf 3 R ⊤))

section Hyp

variable {G : Type} [Group G] [Finite G]

theorem le_of_hyp91 {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R : Subgroup G}
    (h : Sec9.Hyp91 G A c L a R) : A ≤ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcA := h.mem_A
  set HW := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
    Subgroup.normalizer (A : Set G) with hHW
  obtain ⟨Ws, hWs⟩ := h.isSylowOf_inf
  have hAHW : A ≤ HW := by
    refine le_inf (fun x hx => ?_) (fun x hx => Subgroup.le_normalizer hx)
    have hxc : x * c = c * x := congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcA⟩)
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [hxc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  have hAn : (A.subgroupOf HW).Normal := by
    constructor
    intro n hn w
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (w.2.2) _).mp hn
  have hA3 : IsPGroup 3 (A.subgroupOf HW) := by
    have hA3' : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
    exact hA3'.comap_subtype
  have h1 := hA3.le_sylow_of_normal Ws
  intro x hx
  have h2 : (⟨x, hAHW hx⟩ : HW) ∈ (Ws : Subgroup HW) := h1 (Subgroup.mem_subgroupOf.mpr hx)
  have h3 : x ∈ R ⊓ Subgroup.normalizer (A : Set G) := by
    rw [← hWs]
    exact ⟨⟨x, hAHW hx⟩, h2, rfl⟩
  exact h3.1

end Hyp

end CFSG.RankThree.PartTwo.Sec10

module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45Nt_nonabelian_of_kghyp {p : ℕ} (hp : p.Prime) {K : Type} [Group K] {R : Type}
    [Group R] {I F : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {lab : LargeEvenLabel} {ψ : MulAut K} {E : Subgroup (MulAut K)}
    (hyp : GGL45TorusKGHyp p lab I F θ ψ E) : ∃ a b : R, a * b ≠ b * a := by
  by_contra h
  push Not at h
  obtain ⟨-, -, -, hcard, -⟩ := hyp
  haveI : Group.IsPerfect K := ⟨hK⟩
  have hQcomm : IsMulCommutative (K ⧸ Subgroup.center K) :=
    isMulCommutative_iff.mpr fun a b => by
      apply θ.injective
      rw [map_mul, map_mul]
      exact h (θ a) (θ b)
  have hQtop : Subgroup.center (K ⧸ Subgroup.center K) = ⊤ := Subgroup.center_eq_top
  have hQbot : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot K
  have hQsub : Subsingleton (K ⧸ Subgroup.center K) := by
    refine ⟨fun a b => ?_⟩
    have ha : a = 1 := by
      have hmem : a ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
        rw [hQtop]; exact Subgroup.mem_top a
      rw [hQbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hb : b = 1 := by
      have hmem : b ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
        rw [hQtop]; exact Subgroup.mem_top b
      rw [hQbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [ha, hb]
  have hcenterK : Subgroup.center K = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim (x : K ⧸ Subgroup.center K) 1
  haveI : IsMulCommutative K := Subgroup.center_eq_top_iff.mp hcenterK
  have htopbot : (⊤ : Subgroup K) = ⊥ := by rw [← hK, commutator_eq_bot]
  have hKsub : Subsingleton K := by
    refine ⟨fun a b => ?_⟩
    have ha : a = 1 := by
      have hmem : a ∈ (⊥ : Subgroup K) := by
        rw [← htopbot]; exact Subgroup.mem_top a
      exact Subgroup.mem_bot.mp hmem
    have hb : b = 1 := by
      have hmem : b ∈ (⊥ : Subgroup K) := by
        rw [← htopbot]; exact Subgroup.mem_top b
      exact Subgroup.mem_bot.mp hmem
    rw [ha, hb]
  haveI : Subsingleton E :=
    ⟨fun a b => Subtype.ext (MulEquiv.ext fun x => Subsingleton.elim (a.1 x) (b.1 x))⟩
  haveI : Nonempty E := ⟨1⟩
  have hcardE : Nat.card E = 1 := Nat.card_unique
  have hp2 : p ^ 2 ≤ 1 := by rw [← hcardE]; exact hcard
  have h4 : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
  omega

end CFSG.StandardType

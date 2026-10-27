module

public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def PSp45AutThreeInv : Prop :=
  ∀ (P : Type) [Group P] [Finite P], StatedClassicalModel P .PSp 2 5 1 →
    ∀ B : Subgroup (MulAut P), IsElemAbelian 3 B → ∃ i : P, orderOf i = 2 ∧ ∀ β ∈ B, β i = i

namespace Item221ResProof

variable {G : Type} [Group G]

@[expose] def autOfLe {A X : Subgroup G} (h : A ≤ Subgroup.normalizer (X : Set G)) :
    Subgroup (MulAut X) :=
  (X.normalizerMonoidHom.comp (Subgroup.inclusion h)).range

theorem isElemAbelian_autOfLe {A X : Subgroup G} (hA : IsElemAbelian 3 A)
    (h : A ≤ Subgroup.normalizer (X : Set G)) : IsElemAbelian 3 (autOfLe h) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, hA.1.is_comm.comm a b]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 a a.2)
    rw [ha3, map_one]

theorem mem_centralizer_of_forall_fixed {A X : Subgroup G}
    (h : A ≤ Subgroup.normalizer (X : Set G)) {i : X}
    (hi : ∀ β ∈ autOfLe h, β i = i) : (i : G) ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 := congrArg Subtype.val (hi _ ⟨⟨a, ha⟩, rfl⟩)
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inclusion] at h1
  calc a * (i : G) = a * i * a⁻¹ * a := by group
    _ = i * a := by rw [h1]

end Item221ResProof

open Item221ResProof

theorem item228NotPSp45_of (h45 : Sec4.Item4_5) (h224 : Item224) (hK : PSp45AutThreeInv) :
    Item228NotPSp45 := by
  intro G _ _ A E U c L hpair _ φ _ X hX _ hP
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  obtain ⟨a, haA, ha1, hXa⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have hAN : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe haA ha1
      X hXa
  obtain ⟨i, hi2, hfix⟩ := hK X hP (autOfLe hAN) (isElemAbelian_autOfLe hAe hAN)
  have hiC := mem_centralizer_of_forall_fixed hAN hfix
  have hodd := h224 G A E U c L hpair
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer (A : Set G)) := by
    have := orderOf_dvd_natCard (⟨(i : G), hiC⟩ : Subgroup.centralizer (A : Set G))
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hi2] at this
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end CFSG.RankThree.PartTwo.Sec21

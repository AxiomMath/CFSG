module

public import CFSG.Quasithin.Background.E1Solv

public section

namespace CFSG.Quasithin.E1.RootLift

open CFSG.Open CFSG.Quasithin E1

theorem isSolvable_of_eOne {Q : Type*} [Group Q] [Finite Q] {B : Subgroup Q} (h : EOne Q B) :
    Group.IsSolvable Q := by
  obtain ⟨p, hp, -, htop, -⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Group.IsSolvable (Q ⧸ oTwoP Q p) := by
    have htop' : CFSG.Open.pCore 2 (Q ⧸ oTwoP Q p) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (oTwoP Q p) x
      have hq : q ∈ oTwoPTwo Q p := htop ▸ Subgroup.mem_top q
      exact hq
    have hP : IsPGroup 2 ↥(CFSG.Open.pCore 2 (Q ⧸ oTwoP Q p)) :=
      CFSG.LieType.BorelTits.pCore_isPGroup 2
    rw [htop'] at hP
    have hP' : IsPGroup 2 (Q ⧸ oTwoP Q p) := hP.of_equiv Subgroup.topEquiv
    have := hP'.isNilpotent
    infer_instance
  have hO2 : CFSG.Open.pCore 2 Q ≤ oTwoP Q p := by
    intro x hx
    show QuotientGroup.mk' (CFSG.Open.pCore 2 Q) x ∈ CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q)
    have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 Q) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact Subgroup.one_mem _
  have hN : Group.IsSolvable ↥(oTwoP Q p) := by
    have hO : IsPGroup 2 ↥(CFSG.Open.pCore 2 Q) := CFSG.LieType.BorelTits.pCore_isPGroup 2
    have hP : IsPGroup p ↥(CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q)) :=
      CFSG.LieType.BorelTits.pCore_isPGroup p
    have : Group.IsSolvable ↥(CFSG.Open.pCore 2 Q) := by
      have := hO.isNilpotent
      infer_instance
    have : Group.IsSolvable ↥(CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q)) := by
      have := hP.isNilpotent
      infer_instance
    let g : ↥(oTwoP Q p) →* ↥(CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q)) :=
      ((QuotientGroup.mk' (CFSG.Open.pCore 2 Q)).comp (oTwoP Q p).subtype).codRestrict _
        fun x => x.2
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hO2) g fun x hx => ?_
    have hx1 : QuotientGroup.mk' (CFSG.Open.pCore 2 Q) (x : Q) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact ⟨⟨x, hx1⟩, rfl⟩
  exact Group.isSolvable_of_ker_le_range (oTwoP Q p).subtype (QuotientGroup.mk' (oTwoP Q p))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem not_eTwo_of_barRad_eq_bot {Q : Type*} [Group Q] {S B : Subgroup Q}
    (h : barRad Q B = ⊥) : ¬ ETwo Q S B := by
  rintro ⟨-, -, -, L, hL, -, hcase⟩
  rw [h] at hcase
  rcases hcase with hL' | ⟨hN, -⟩
  · rw [Subgroup.commutator_bot_right] at hL'
    apply not_isSolvable_of_isComponent hL
    rw [hL']
    infer_instance
  · exact hN bot_le

variable {K X : Type*} [Group K] [Group X] [Finite K] [Finite X]

end CFSG.Quasithin.E1.RootLift

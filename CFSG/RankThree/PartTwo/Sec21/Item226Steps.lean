module

public import CFSG.RankThree.PartTwo.Sec21.Item226Pre

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

theorem three_dvd_card_of_sec21Pair [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) : 3 ∣ Nat.card A := by
  obtain ⟨E', hE', hE'A⟩ := hpair.mem_S.1.2.2
  have h27 := hE'.2.1
  have hdvd := Subgroup.card_dvd_of_le hE'A
  rw [h27] at hdvd
  exact (by norm_num : 3 ∣ 27).trans hdvd

theorem pCore_three_closure_dStar_eq_bot [Finite G] (h2130 : Item2130) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) :
    CFSG.pCore 3 (Subgroup.closure (dStar A)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.closure (dStar A) with hZ
  set Q : Subgroup (MulAut A) := (CFSG.pCore 3 Z).map Z.subtype with hQ
  have hQ3 : IsPGroup 3 Q := (CFSG.pCore_isPGroup).map Z.subtype
  have hQW : ∀ w ∈ wStar A, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q := by
    intro w hw q hq
    have hZw : ∀ z ∈ Z, w * z * w⁻¹ ∈ Z := fun z hz => conj_mem_closure_dStar hw hz
    have hZw' : ∀ z ∈ Z, w⁻¹ * z * w⁻¹⁻¹ ∈ Z := fun z hz =>
      conj_mem_closure_dStar ((wStar A).inv_mem hw) hz
    let α : Z ≃* Z :=
      { toFun := fun z => ⟨w * z * w⁻¹, hZw z z.2⟩
        invFun := fun z => ⟨w⁻¹ * z * w⁻¹⁻¹, hZw' z z.2⟩
        left_inv := fun z => Subtype.ext (by simp [mul_assoc])
        right_inv := fun z => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hP := CFSG.pCore_map_iso 3 α
    obtain ⟨z, hz, rfl⟩ := hq
    have hz' : α z ∈ CFSG.pCore 3 Z := by
      rw [← hP]
      exact ⟨z, hz, rfl⟩
    exact ⟨α z, hz', rfl⟩
  set C : Subgroup A :=
    { carrier := {a | ∀ q ∈ Q, q a = a}
      mul_mem' := fun ha hb q hq => by rw [map_mul, ha q hq, hb q hq]
      one_mem' := fun q _ => map_one q
      inv_mem' := fun ha q hq => by rw [map_inv, ha q hq] } with hC
  have hCle : ∀ ψ ∈ wStar A, C.map ψ.toMonoidHom ≤ C := by
    rintro ψ hψ _ ⟨a, ha, rfl⟩ q hq
    have h := ha _ (hQW _ ((wStar A).inv_mem hψ) q hq)
    simp only [inv_inv, MulAut.mul_apply] at h
    have h' := congrArg ψ h
    simpa using h'
  have hCW : ∀ ψ ∈ wStar A, C.map ψ.toMonoidHom = C := fun ψ hψ =>
    Subgroup.eq_of_le_of_card_ge (hCle ψ hψ)
      (le_of_eq (Subgroup.card_map_of_injective ψ.injective).symm)
  rcases h2130 G A E U c L hpair C hCW with hbot | htop
  · exfalso
    have h1 : (1 : A) ∈ MulAction.fixedPoints Q A := fun q => by
      change (q : MulAut A) 1 = 1
      exact map_one _
    obtain ⟨b, hb, hne⟩ := hQ3.exists_fixed_point_of_prime_dvd_card_of_fixed_point A
      (three_dvd_card_of_sec21Pair hpair) h1
    have hbC : b ∈ C := fun q hq => hb ⟨q, hq⟩
    rw [hbot] at hbC
    exact hne ((Subgroup.mem_bot).mp hbC).symm
  · have hQ1 : Q = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      rw [Subgroup.mem_bot]
      refine MulEquiv.ext fun a => ?_
      have ha : a ∈ C := htop ▸ Subgroup.mem_top a
      exact ha q hq
    rw [eq_bot_iff]
    intro z hz
    have hzQ : (z : MulAut A) ∈ Q := ⟨z, hz, rfl⟩
    rw [hQ1, Subgroup.mem_bot] at hzQ
    rw [Subgroup.mem_bot]
    exact Subtype.ext hzQ

theorem rank3II_22_6_oThreeCentral (h2130 : Item2130) : Item226OThreeCentral := by
  intro G _ _ A E U c L hpair _ _ _
  rw [pCore_three_closure_dStar_eq_bot h2130 hpair]
  exact bot_le

end CFSG.RankThree.PartTwo.Sec21

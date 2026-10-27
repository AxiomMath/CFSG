module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelNoTv

public section

namespace CFSG.StandardType.TableBExc.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem not_isTransvection_top
    (c : ZMod 3) (hc : c ≠ 0) (u : WeylGroup .E6)
    (hfix : Nat.card {x : Fin Tag.E6.rank → ZMod 3 // c • adAct .E6 3 u x = x} * 3 =
      Nat.card (Fin Tag.E6.rank → ZMod 3))
    (hN : ∀ x : Fin Tag.E6.rank → ZMod 3,
      c • adAct .E6 3 u (c • adAct .E6 3 u x - x) = c • adAct .E6 3 u x - x) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc_eq : c = 1 := by
    obtain ⟨x₀, hx₀⟩ := exists_not_mem_hypE6
    have hx₀' : NoOffRest.kDotP 3 x₀ ≠ 0 := fun h => hx₀ (NoOffRest.mem_hypE6.mpr h)
    have key : ∀ y : Fin Tag.E6.rank → ZMod 3,
        NoOffRest.kDotP 3 (c • adAct .E6 3 u y - y) = (c - 1) * NoOffRest.kDotP 3 y := by
      intro y
      rw [NoOffRest.kDotP_sub, NoOffRest.kDotP_smul, NoOffRest.kDot_adAct]
      ring
    have hinner := key x₀
    have houter := key (c • adAct .E6 3 u x₀ - x₀)
    have hzero : NoOffRest.kDotP 3
        (c • adAct .E6 3 u (c • adAct .E6 3 u x₀ - x₀) - (c • adAct .E6 3 u x₀ - x₀)) = 0 := by
      rw [hN x₀, sub_self, NoOffRest.kDotP_zero]
    have hsq : (c - 1) * ((c - 1) * NoOffRest.kDotP 3 x₀) = 0 := by
      have h := houter ▸ hzero
      rwa [hinner] at h
    have hsq' : (c - 1) * (c - 1) = 0 := by
      rcases mul_eq_zero.mp hsq with h | h
      · rw [h, zero_mul]
      · rw [(mul_eq_zero.mp h).resolve_right hx₀', zero_mul]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsq').elim id id)
  rw [hc_eq] at hfix hN
  simp only [one_smul] at hfix hN
  have hzero : adAct .E6 3 u (0 : Fin Tag.E6.rank → ZMod 3) = 0 := by
    simpa using adAct_smul u (0 : ZMod 3) (0 : Fin Tag.E6.rank → ZMod 3)
  have hneg : ∀ x : Fin Tag.E6.rank → ZMod 3, adAct .E6 3 u (-x) = -adAct .E6 3 u x := by
    intro x
    have h := NoOffRest.adAct_sub u (0 : Fin Tag.E6.rank → ZMod 3) x
    rw [zero_sub, hzero, zero_sub] at h
    exact h
  let F : AddSubgroup (Fin Tag.E6.rank → ZMod 3) :=
    { carrier := {x | adAct .E6 3 u x = x}
      add_mem' := by
        intro x y hx hy
        change adAct .E6 3 u (x + y) = x + y
        rw [NoOffRest.adAct_add, show adAct .E6 3 u x = x from hx,
          show adAct .E6 3 u y = y from hy]
      zero_mem' := by
        change adAct .E6 3 u (0 : Fin Tag.E6.rank → ZMod 3) = 0
        exact hzero
      neg_mem' := by
        intro x hx
        change adAct .E6 3 u (-x) = -x
        rw [hneg, show adAct .E6 3 u x = x from hx] }
  have hcardF : Nat.card F = 3 ^ 5 := by
    have h : Nat.card F * 3 = 3 ^ 6 := by
      rw [card_top] at hfix
      exact hfix
    have h36 : (3 : ℕ) ^ 6 = 3 ^ 5 * 3 := by norm_num
    rw [h36] at h
    exact Nat.mul_right_cancel (by norm_num) h
  let κ : F →+ ZMod 3 :=
    { toFun := fun x => NoOffRest.kDotP 3 (x : Fin Tag.E6.rank → ZMod 3)
      map_zero' := by
        change NoOffRest.kDotP 3 (0 : Fin Tag.E6.rank → ZMod 3) = 0
        exact NoOffRest.kDotP_zero
      map_add' := by
        intro x y
        change NoOffRest.kDotP 3
            ((x : Fin Tag.E6.rank → ZMod 3) + (y : Fin Tag.E6.rank → ZMod 3)) =
          NoOffRest.kDotP 3 (x : Fin Tag.E6.rank → ZMod 3) +
            NoOffRest.kDotP 3 (y : Fin Tag.E6.rank → ZMod 3)
        rw [NoOffRest.kDotP_add] }
  haveI : Fact (Nat.Prime (Nat.card (ZMod 3))) :=
    ⟨by rw [Nat.card_zmod]; exact Nat.prime_three⟩
  rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card κ.range with hbot | htop
  ·
    have hκ0 : ∀ z : F, κ z = 0 := by
      intro z
      have hz : κ z ∈ κ.range := AddMonoidHom.mem_range.mpr ⟨z, rfl⟩
      rw [hbot] at hz
      simpa using hz
    have hle : F ≤ NoOffRest.hypE6 := by
      intro x hx
      rw [NoOffRest.mem_hypE6]
      exact hκ0 ⟨x, hx⟩
    have heq : F = NoOffRest.hypE6 :=
      AddSubgroup.eq_of_le_of_card_ge hle (by rw [NoOffRest.card_hypE6, hcardF])
    have hfix_on : ∀ x ∈ NoOffRest.hypE6, adAct .E6 3 u x = x := by
      intro x hx
      have hxF : x ∈ F := by rw [heq]; exact hx
      exact hxF
    have hu : u = 1 := eq_one_of_adAct_eq_on_hypE6 hfix_on
    have hcardV : Nat.card F = Nat.card (Fin Tag.E6.rank → ZMod 3) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => by
        change adAct .E6 3 u x = x
        rw [hu, adAct_one]))
    exact absurd (by rw [← hcardF, hcardV, card_top] : (3 : ℕ) ^ 5 = 3 ^ 6) (by norm_num)
  ·
    have hcard_range : Nat.card κ.range = 3 := by
      rw [htop, AddSubgroup.card_top, Nat.card_zmod]
    have hcard_ker : Nat.card κ.ker = 3 ^ 4 := by
      have h := AddSubgroup.card_ker_mul_card_range κ
      rw [hcardF, hcard_range] at h
      have h35 : (3 : ℕ) ^ 5 = 3 ^ 4 * 3 := by norm_num
      rw [h35] at h
      exact Nat.mul_right_cancel (by norm_num) h
    let t' : NoOffRest.hypE6 →+ NoOffRest.hypE6 :=
      { toFun := fun x =>
          ⟨adAct .E6 3 u (x : Fin Tag.E6.rank → ZMod 3), NoOffRest.adAct_mem_hypE6 u x.2⟩
        map_zero' := Subtype.ext (by simpa using hzero)
        map_add' := fun x y => Subtype.ext (NoOffRest.adAct_add u
          (x : Fin Tag.E6.rank → ZMod 3) (y : Fin Tag.E6.rank → ZMod 3)) }
    have hker_eq : Nat.card κ.ker = Nat.card {x : NoOffRest.hypE6 // t' x = x} :=
      Nat.card_congr
        { toFun := fun z =>
            ⟨⟨(z.1 : Fin Tag.E6.rank → ZMod 3),
                NoOffRest.mem_hypE6.mpr (AddMonoidHom.mem_ker.mp z.2)⟩,
              Subtype.ext z.1.2⟩
          invFun := fun y =>
            ⟨⟨(y.1 : Fin Tag.E6.rank → ZMod 3), congrArg Subtype.val y.2⟩,
              NoOffRest.mem_hypE6.mp y.1.2⟩
          left_inv := fun z => Subtype.ext (Subtype.ext rfl)
          right_inv := fun y => Subtype.ext (Subtype.ext rfl) }
    have hN' : ∀ x : NoOffRest.hypE6, t' (t' x - x) = t' x - x :=
      fun x => Subtype.ext (hN (x : Fin Tag.E6.rank → ZMod 3))
    have hfix' : Nat.card {x : NoOffRest.hypE6 // t' x = x} * 3 = Nat.card NoOffRest.hypE6 := by
      rw [← hker_eq, hcard_ker, NoOffRest.card_hypE6]
      norm_num
    exact not_isTransvection_hypE6 1 one_ne_zero u t' (fun x => by simp [t']) hfix' hN'

end CFSG.StandardType.TableBExc.E6Three

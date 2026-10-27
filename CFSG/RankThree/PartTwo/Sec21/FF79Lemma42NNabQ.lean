module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NNabP
public import CFSG.RankThree.PartOne.MB3.FixedPoint
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NHyp

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG.Holt.General.AltRecPrim

variable {Γ : Type} [Group Γ] [Finite Γ] {Q L : Subgroup Γ} {b : Γ}

theorem exists_ne_one_mem (F : SimpleFactors Q) (j : Fin F.r) : ∃ x ∈ F.S j, x ≠ 1 := by
  obtain ⟨a, ha, c, hc, hac⟩ := F.not_commute j
  refine ⟨a, ha, ?_⟩
  rintro rfl
  exact hac (by simp)

theorem exists_fixed_of_cj_self (h : NHyp Q L b) (F : SimpleFactors Q) (j : Fin F.r)
    (hb : Cj F b j j) : ∃ x ∈ F.S j, x ≠ 1 ∧ b * x * b⁻¹ = x := by
  by_contra hcon
  push Not at hcon
  let α : MulAut (F.S j) :=
    { toFun := fun x => ⟨b * x * b⁻¹, (hb x).mp x.2⟩
      invFun := fun x => ⟨b⁻¹ * x * b, hb.symm_mem x.2⟩
      left_inv := fun x => Subtype.ext (by show b⁻¹ * (b * (x : Γ) * b⁻¹) * b = x; group)
      right_inv := fun x => Subtype.ext (by show b * (b⁻¹ * (x : Γ) * b) * b⁻¹ = x; group)
      map_mul' := fun x y => Subtype.ext (by
        show b * ((x : Γ) * y) * b⁻¹ = b * (x : Γ) * b⁻¹ * (b * (y : Γ) * b⁻¹); group) }
  have hα : ∀ x : F.S j, α x = x → x = 1 := by
    intro x hx
    have hx' : b * (x : Γ) * b⁻¹ = x := congrArg Subtype.val hx
    by_contra hx1
    exact hcon x x.2 (fun h1 => hx1 (Subtype.ext h1)) hx'
  have hb3 : b ^ 3 = 1 := h.order ▸ pow_orderOf_eq_one b
  have hα3 : α ^ 3 = 1 := by
    ext x
    show b * (b * (b * (x : Γ) * b⁻¹) * b⁻¹) * b⁻¹ = x
    have hb3' : b * b * b = 1 := by simpa [pow_succ, mul_assoc] using hb3
    have : b * (b * (b * (x : Γ) * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * x * (b * b * b)⁻¹ := by
      group
    rw [this, hb3']
    group
  have hne1 : α ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hx1⟩ := exists_ne_one_mem F j
    have : α ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [h1]; rfl
    exact hx1 (congrArg Subtype.val (hα _ this))
  have hord : orderOf α = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hα3) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne1
    · exact h1
  have hnil : Group.IsNilpotent (F.S j) :=
    CFSG.RankThree.PartOne.MB3.isNilpotent_of_fixedPointFree_prime α
      (by rw [hord]; exact Nat.prime_three) hα
  haveI := F.isSimpleGroup j
  haveI := hnil
  obtain ⟨a, ha, c, hc, hac⟩ := F.not_commute j
  exact hac (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : F.S j) ⟨c, hc⟩))

theorem fixed_factor (h : NHyp Q L b) (hQ : Q.Normal) (F : SimpleFactors Q) (j : Fin F.r)
    (hb : Cj F b j j) : ∀ l ∈ L, Cj F l j j := by
  obtain ⟨x, hxS, hx1, hxb⟩ := exists_fixed_of_cj_self h F j hb
  have hxQ : x ∈ Q := F.le j hxS
  have hxC : x ∈ Subgroup.centralizer (L : Set Γ) := by
    have hxcb : x ∈ Subgroup.centralizer ({b} : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [hxb]
    exact h.cent (Subgroup.mem_inf.mpr ⟨hxQ, hxcb⟩)
  intro l hl
  obtain ⟨k, hk⟩ := exists_Cj F hQ l j
  by_cases hkj : k = j
  · exact hkj ▸ hk
  · exfalso
    have hxl : l * x * l⁻¹ = x := by
      have := Subgroup.mem_centralizer_iff.mp hxC l hl
      calc l * x * l⁻¹ = (l * x) * l⁻¹ := rfl
        _ = (x * l) * l⁻¹ := by rw [this]
        _ = x := by group
    have hxk : x ∈ F.S k := by
      have := (hk x).mp hxS
      rwa [hxl] at this
    refine hx1 (F.eq_one_of_forall_commute hxk fun t ht => ?_)
    exact F.commute_of_ne (Ne.symm hkj) hxS ht

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

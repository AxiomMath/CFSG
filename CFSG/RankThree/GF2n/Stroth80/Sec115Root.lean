module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec11Torus
public import CFSG.Timmesfeld.Defs
import CFSG.RankThree.GF2n.Stroth80.Sec115Perfect
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec114Alg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section Def

variable {G : Type} [Group G]

@[expose] def EbarIn (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] : Set ↥(Xbar M Q Z B) :=
  {x | (x : Mbar M Q) ∈ Ebar M Q Z B}

end Def

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

omit [Finite G] in
theorem ebarIn_eq_setOf_isConj {e₀ : Mbar M Q} (he₀ : e₀ ∈ Ebar M Q Z B)
    (hcls : Ebar M Q Z B = {e | ∃ x ∈ Xbar M Q Z B, e = x * e₀ * x⁻¹}) :
    EbarIn M Q Z B =
      {g | IsConj (⟨e₀, Subgroup.subset_closure he₀⟩ : ↥(Xbar M Q Z B)) g} := by
  ext g
  refine (Set.ext_iff.mp hcls (g : Mbar M Q)).trans ?_
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, isConj_iff]
  constructor
  · rintro ⟨x, hx, hgx⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hgx.symm⟩
  · rintro ⟨c, hcg⟩
    exact ⟨c, c.2, (congrArg Subtype.val hcg).symm⟩

theorem orderOf_eq_two_of_mem_ebarIn {d : ↥(Xbar M Q Z B)} (hd : d ∈ EbarIn M Q Z B) :
    orderOf d = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact Ctx.orderOf_eq_two_of_mem_Ebar hd

theorem isRootInvolutionSet_ebarIn
    (horder : ∀ e₁ ∈ Ebar M Q Z B, ∀ e₂ ∈ Ebar M Q Z B,
      (orderOf (e₁ * e₂) = 2 ∨ orderOf (e₁ * e₂) = 4 ∨ Odd (orderOf (e₁ * e₂))) ∧
      (orderOf (e₁ * e₂) = 4 → (e₁ * e₂) ^ 2 ∈ Ebar M Q Z B)) :
    CFSG.Timmesfeld.IsRootInvolutionSet (EbarIn M Q Z B) := by
  refine ⟨fun d hd => orderOf_eq_two_of_mem_ebarIn hd, fun d hd e he => ?_,
    fun d hd e he h4 => ?_⟩
  · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact (horder _ hd _ he).1
  · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul] at h4
    show (((d * e) ^ 2 : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ Ebar M Q Z B
    rw [Subgroup.coe_pow, Subgroup.coe_mul]
    exact (horder _ hd _ he).2 h4

omit [Finite G] in
theorem closure_ebarIn_eq_top : Subgroup.closure (EbarIn M Q Z B) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

theorem Ctx.not_mem_center_Xbar_of_mem_Ebar (hc : Ctx M Q Z B) {d : ↥(Xbar M Q Z B)}
    (hd : (d : Mbar M Q) ∈ Ebar M Q Z B) : d ∉ Subgroup.center ↥(Xbar M Q Z B) := by
  intro hdZ
  have hdvd := Subgroup.orderOf_dvd_natCard _ hdZ
  rw [orderOf_eq_two_of_mem_ebarIn hd] at hdvd
  exact hc.odd_card_center_Xbar.not_two_dvd_nat hdvd

theorem Ctx.ebarIn_rootData (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) (h112 : Stroth112Statement) :
    (∃ d₀ : ↥(Xbar M Q Z B), EbarIn M Q Z B = {g | IsConj d₀ g}) ∧
    CFSG.Timmesfeld.IsRootInvolutionSet (EbarIn M Q Z B) ∧
    Subgroup.closure (EbarIn M Q Z B) = ⊤ ∧
    (∀ N : Subgroup ↥(Xbar M Q Z B), N.Normal → IsPGroup 2 N → N = ⊥) ∧
    ∀ d ∈ EbarIn M Q Z B, d ∉ Subgroup.center ↥(Xbar M Q Z B) := by
  obtain ⟨⟨e₀, he₀, hcls⟩, horder⟩ := h112 G M Q Z B hc n hw hn ha2
  exact ⟨⟨_, ebarIn_eq_setOf_isConj he₀ hcls⟩, isRootInvolutionSet_ebarIn horder,
    closure_ebarIn_eq_top, fun N hN hN2 => eq_bot_of_normal_isPGroup_of_subnormal le_rfl
      Subgroup.le_normalizer hc.Xbar_normal hc.pCore_two_Mbar N hN hN2,
    fun d hd => hc.not_mem_center_Xbar_of_mem_Ebar hd⟩

theorem mul_self_eq_one_of_mem_Ebar {e : Mbar M Q} (he : e ∈ Ebar M Q Z B) : e * e = 1 := by
  rw [← pow_two, ← Ctx.orderOf_eq_two_of_mem_Ebar he]
  exact pow_orderOf_eq_one e

theorem mul_comm_of_mem_Ebar {u v : Mbar M Q} (hu : u ∈ Ebar M Q Z B) (hv : v ∈ Ebar M Q Z B)
    (huv : u * v ∈ Ebar M Q Z B) : u * v = v * u := by
  have e1 : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_Ebar huv)
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_Ebar hu),
    inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_Ebar hv)] at e1
  exact e1.symm

theorem IsLBTorus.mk'_conj_ne {a y : G} (hc : Ctx M Q Z B) (hy : IsLBTorus M Q Z B y)
    (ha : a ∈ LB M Q B) (haQ : a ∉ Q) :
    QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hy.mem_M⟩ *
        QuotientGroup.mk' (Q.subgroupOf M) ⟨a, hc.LB_le_M ha⟩ *
        (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hy.mem_M⟩)⁻¹ ≠
      QuotientGroup.mk' (Q.subgroupOf M) ⟨a, hc.LB_le_M ha⟩ := by
  intro h
  have h1 : QuotientGroup.mk' (Q.subgroupOf M) ((⟨y, hy.mem_M⟩ : ↥M) * ⟨a, hc.LB_le_M ha⟩ *
      (⟨y, hy.mem_M⟩ : ↥M)⁻¹ * (⟨a, hc.LB_le_M ha⟩ : ↥M)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h, mul_inv_cancel]
  have h2 : y ^ 1 * a * (y ^ 1)⁻¹ * a⁻¹ ∈ Q := by
    rw [pow_one]
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hq := hc.hyp.q4
  exact haQ (hy.fpf 1 one_pos (by omega) a ha h2)

theorem Ctx.ebarIn_meetsSq (hc : Ctx M Q Z B) {a y : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) (hy : IsLBTorus M Q Z B y) :
    ∃ u ∈ EbarIn M Q Z B, ∃ v ∈ EbarIn M Q Z B, u ≠ v ∧ Commute u v ∧
      u * v ∈ EbarIn M Q Z B := by
  set u : Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) ⟨a, hc.LB_le_M ha⟩ with hu_def
  set yb : Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hy.mem_M⟩ with hy_def
  have hu : u ∈ Ebar M Q Z B := hc.mk_mem_Ebar ha hA
  have hv : yb * u * yb⁻¹ ∈ Ebar M Q Z B := hc.Ebar_conj hu yb
  have hne : yb * u * yb⁻¹ ≠ u := IsLBTorus.mk'_conj_ne hc hy ha hA.2.1
  have huv : u * (yb * u * yb⁻¹) ∈ Ebar M Q Z B := by
    rcases hy.line_closed a ha 0 1 with h | ⟨k, -, hk⟩
    · simp only [pow_zero, one_mul, inv_one, mul_one, pow_one] at h
      exfalso
      exact hA.2.1 (hy.fpf 1 one_pos (by have := hc.hyp.q4; omega) a ha
        (hc.conj_mul_inv_mem_of_mul_conj_mem ha h))
    · simp only [pow_zero, one_mul, inv_one, mul_one, pow_one] at hk
      rw [hu_def, hy_def, mk'_mul_conj_eq_of_mem (l := ⟨a, hc.LB_le_M ha⟩) (y := ⟨y, hy.mem_M⟩) hk]
      exact hc.Ebar_conj hu _
  refine ⟨⟨u, Subgroup.subset_closure hu⟩, hu, ⟨_, Subgroup.subset_closure hv⟩, hv,
    fun h => hne (congrArg Subtype.val h).symm, Subtype.ext (mul_comm_of_mem_Ebar hu hv huv),
    huv⟩

end CFSG.RankThree.GF2n.Stroth80

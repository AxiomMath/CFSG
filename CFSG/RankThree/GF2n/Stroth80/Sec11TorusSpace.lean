module

public import CFSG.RankThree.GF2n.Stroth80.Ctx
import CFSG.RankThree.GF2n.Stroth80.Sec11TorusComm
import CFSG.RankThree.GF2n.Stroth80.Sec34Trans
public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Space

variable {G : Type} [Group G]

abbrev LBSpace (M Q B : Subgroup G) [(Q.subgroupOf M).Normal] : Type :=
  Additive (Abelianization ↥(bar M Q (LB M Q B)))

open _root_.Classical in
@[expose] noncomputable def lbVec (M Q B : Subgroup G) [(Q.subgroupOf M).Normal] (l : G) :
    LBSpace M Q B :=
  if h : l ∈ LB M Q B ⊓ M then
    Additive.ofMul (Abelianization.of ⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨l, h.2⟩,
      Subgroup.mem_map.mpr ⟨⟨l, h.2⟩, Subgroup.mem_subgroupOf.mpr h.1, rfl⟩⟩)
  else 0

end Space

variable {G : Type} [Group G]

theorem mem_LB_of_mem_QB_inf {M Q B : Subgroup G} {a : G} (ha : a ∈ QB B ⊓ M) : a ∈ LB M Q B :=
  (le_sup_right : QB B ⊓ M ≤ Q ⊔ (QB B ⊓ M)) ha

variable [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.conj_mem_PB_of_mem_normalizer (hc : Ctx M Q Z B) {g : G} (hgM : g ∈ M)
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) {a : G} (ha : a ∈ QB B ⊓ M) :
    g * a * g⁻¹ ∈ QB B ⊓ M :=
  ⟨(Subgroup.mem_normalizer_iff.mp (hc.normalizer_B_le_normalizer_QB hgB) a).mp ha.1,
    M.mul_mem (M.mul_mem hgM ha.2) (M.inv_mem hgM)⟩

theorem Ctx.conj_mem_LB_of_mem_normalizer (hc : Ctx M Q Z B) {g : G} (hgM : g ∈ M)
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) {l : G} (hl : l ∈ LB M Q B) :
    g * l * g⁻¹ ∈ LB M Q B := by
  obtain ⟨s, hs, q, hq, rfl⟩ := hc.exists_mul_of_mem_LB hl
  have e : g * (s * q) * g⁻¹ = (g * s * g⁻¹) * (g * q * g⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (mem_LB_of_mem_QB_inf (hc.conj_mem_PB_of_mem_normalizer hgM hgB hs))
    ((le_sup_left : Q ≤ Q ⊔ (QB B ⊓ M))
      ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) q).mp hq))

variable [(Q.subgroupOf M).Normal]

omit [Finite G] in
theorem lbVec_of_mem {l : G} (h : l ∈ LB M Q B ⊓ M) (x : ↥(bar M Q (LB M Q B)))
    (hx : QuotientGroup.mk' (Q.subgroupOf M) ⟨l, h.2⟩ = x) :
    lbVec M Q B l = Additive.ofMul (Abelianization.of x) := by
  obtain ⟨x, hxm⟩ := x
  change QuotientGroup.mk' (Q.subgroupOf M) ⟨l, h.2⟩ = x at hx
  subst hx
  rw [lbVec, dif_pos h]

theorem lbVec_mul (hc : Ctx M Q Z B) {l l' : G} (hl : l ∈ LB M Q B) (hl' : l' ∈ LB M Q B) :
    lbVec M Q B (l * l') = lbVec M Q B l + lbVec M Q B l' := by
  have h1 : l ∈ LB M Q B ⊓ M := ⟨hl, hc.LB_le_M hl⟩
  have h2 : l' ∈ LB M Q B ⊓ M := ⟨hl', hc.LB_le_M hl'⟩
  simp only [lbVec, dif_pos h1, dif_pos h2, dif_pos (Subgroup.mul_mem _ h1 h2)]
  rfl

theorem lbVec_eq_zero_iff (hc : Ctx M Q Z B) {l : G} (hl : l ∈ LB M Q B) :
    lbVec M Q B l = 0 ↔ l ∈ Q := by
  have h1 : l ∈ LB M Q B ⊓ M := ⟨hl, hc.LB_le_M hl⟩
  have := hc.isElemAbelian_bar_LB.1
  have hinj : Function.Injective
      (Abelianization.of : ↥(bar M Q (LB M Q B)) →* Abelianization ↥(bar M Q (LB M Q B))) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [Abelianization.ker_of, commutator_eq_bot])
  simp only [lbVec, dif_pos h1]
  rw [ofMul_eq_zero, map_eq_one_iff _ hinj]
  constructor
  · intro h
    have h' : QuotientGroup.mk' (Q.subgroupOf M) (⟨l, h1.2⟩ : ↥M) = 1 := congrArg Subtype.val h
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h')
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff (⟨l, h1.2⟩ : ↥M)).mpr
      (Subgroup.mem_subgroupOf.mpr h))

theorem lbVec_eq_iff (hc : Ctx M Q Z B) {l l' : G} (hl : l ∈ LB M Q B) (hl' : l' ∈ LB M Q B) :
    lbVec M Q B l = lbVec M Q B l' ↔ l⁻¹ * l' ∈ Q := by
  have hm : l⁻¹ * l' ∈ LB M Q B := Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) hl'
  have e : lbVec M Q B l' = lbVec M Q B l + lbVec M Q B (l⁻¹ * l') := by
    rw [← lbVec_mul hc hl hm, mul_inv_cancel_left]
  rw [e, ← lbVec_eq_zero_iff hc hm]
  simp

theorem lbVec_add_self (hc : Ctx M Q Z B) {l : G} (hl : l ∈ LB M Q B) :
    lbVec M Q B l + lbVec M Q B l = 0 := by
  rw [← lbVec_mul hc hl hl, lbVec_eq_zero_iff hc (Subgroup.mul_mem _ hl hl), ← pow_two]
  exact hc.sq_mem_Q_of_mem_LB hl

theorem lbVec_eq_of_mul_mem (hc : Ctx M Q Z B) {l l' : G} (hl : l ∈ LB M Q B)
    (hl' : l' ∈ LB M Q B) (h : l * l' ∈ Q) : lbVec M Q B l = lbVec M Q B l' := by
  have h1 := (lbVec_eq_zero_iff hc (Subgroup.mul_mem _ hl hl')).mpr h
  rw [lbVec_mul hc hl hl'] at h1
  calc lbVec M Q B l = -lbVec M Q B l' := eq_neg_of_add_eq_zero_left h1
    _ = lbVec M Q B l' := (eq_neg_of_add_eq_zero_left (lbVec_add_self hc hl')).symm

theorem lbVec_surjective (hc : Ctx M Q Z B) (v : LBSpace M Q B) :
    ∃ a ∈ QB B ⊓ M, lbVec M Q B a = v := by
  obtain ⟨x, hx⟩ : ∃ x : ↥(bar M Q (LB M Q B)), Abelianization.of x = Additive.toMul v :=
    QuotientGroup.mk_surjective (Additive.toMul v)
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp x.2
  have hmLB : (m : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hm
  obtain ⟨s, hs, y, hy, hsy⟩ := hc.exists_mul_of_mem_LB hmLB
  refine ⟨s, hs, ?_⟩
  rw [(lbVec_eq_iff hc (mem_LB_of_mem_QB_inf hs) hmLB).mpr
    (by rw [hsy, inv_mul_cancel_left]; exact hy), lbVec_of_mem ⟨hmLB, m.2⟩ x hmx, hx]
  rfl

theorem lbSpace_add_self (hc : Ctx M Q Z B) (v : LBSpace M Q B) : v + v = 0 := by
  obtain ⟨a, ha, rfl⟩ := lbVec_surjective hc v
  exact lbVec_add_self hc (mem_LB_of_mem_QB_inf ha)

@[expose] noncomputable def lbLift (hc : Ctx M Q Z B) (v : LBSpace M Q B) : G :=
  (lbVec_surjective hc v).choose

theorem lbLift_mem (hc : Ctx M Q Z B) (v : LBSpace M Q B) : lbLift hc v ∈ QB B ⊓ M :=
  (lbVec_surjective hc v).choose_spec.1

theorem lbVec_lbLift (hc : Ctx M Q Z B) (v : LBSpace M Q B) : lbVec M Q B (lbLift hc v) = v :=
  (lbVec_surjective hc v).choose_spec.2

end CFSG.RankThree.GF2n.Stroth80

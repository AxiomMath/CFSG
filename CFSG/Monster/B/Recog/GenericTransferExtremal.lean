module

public import CFSG.Monster.B.Recog.GenericParity
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Transfer
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Recog

open MulAction

namespace TransferExtremal

variable {G : Type*} [Group G]

theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := rfl

open _root_.Classical in
@[expose] noncomputable def sgn (H M : Subgroup G) (hM : M.relIndex H = 2) :
    H →* Multiplicative (ZMod 2) where
  toFun h := Multiplicative.ofAdd (if (h : G) ∈ M then 0 else 1)
  map_one' := by simp
  map_mul' h k := by
    have hmul := Subgroup.mul_mem_iff_of_index_two (H := M.subgroupOf H) hM (a := h) (b := k)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hmul
    by_cases h1 : (h : G) ∈ M <;> by_cases h2 : (k : G) ∈ M <;>
      simp [h1, h2, hmul, ← ofAdd_add, zmod_two_one_add_one]

open _root_.Classical in
theorem toAdd_sgn (H M : Subgroup G) (hM : M.relIndex H = 2) (h : H) :
    Multiplicative.toAdd (sgn H M hM h) = if (h : G) ∈ M then 0 else 1 := rfl

section Transfer

variable (H : Subgroup G)

theorem out_mk_of_smul_eq {t : G} {x : G ⧸ H} (hx : t • x = x) :
    (Quotient.mk (orbitRel (Subgroup.zpowers t) (G ⧸ H)) x).out = x := by
  have h := Quotient.exact
    (Quotient.out_eq (Quotient.mk (orbitRel (Subgroup.zpowers t) (G ⧸ H)) x))
  have h' : (Quotient.mk (orbitRel (Subgroup.zpowers t) (G ⧸ H)) x).out ∈
      orbit (Subgroup.zpowers t) x := orbitRel_apply.1 h
  obtain ⟨⟨g, hg⟩, hgx⟩ := h'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [← hgx]
  exact mem_fixedBy.1 (mem_fixedBy_zpow (mem_fixedBy.2 hx) k)

variable (M : Subgroup G) (hM : M.relIndex H = 2) [H.FiniteIndex]

open _root_.Classical in
theorem toAdd_transfer_eq {t : G} (ht : t ^ 2 = 1) :
    Multiplicative.toAdd ((sgn H M hM).transfer t) =
      (Nat.card {x : G ⧸ H // t • x = x ∧ x.out⁻¹ * t * x.out ∉ M} : ZMod 2) := by
  have : Fintype (Quotient (orbitRel (Subgroup.zpowers t) (G ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  have key : ∀ q : Quotient (orbitRel (Subgroup.zpowers t) (G ⧸ H)),
      Multiplicative.toAdd (sgn H M hM
        ⟨q.out.out⁻¹ * t ^ Function.minimalPeriod (t • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem H t q.out⟩) =
      if t • q.out = q.out ∧ q.out.out⁻¹ * t * q.out.out ∉ M then 1 else 0 := by
    intro q
    rw [toAdd_sgn]
    show (if q.out.out⁻¹ * t ^ Function.minimalPeriod (t • ·) q.out * q.out.out ∈ M
      then (0 : ZMod 2) else 1) = _
    by_cases hq : t • q.out = q.out
    · rw [minimalPeriod_eq_one_iff_fixedBy.2 hq, pow_one]
      by_cases hm : q.out.out⁻¹ * t * q.out.out ∈ M <;> simp [hq, hm]
    · have hper : Function.IsPeriodicPt (t • ·) 2 q.out := by
        show (fun x => t • x)^[2] q.out = q.out
        rw [Function.iterate_succ_apply', Function.iterate_one, smul_smul, ← sq, ht, one_smul]
      have h2 : Function.minimalPeriod (t • ·) q.out = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hper.minimalPeriod_dvd with h | h
        · exact absurd (minimalPeriod_eq_one_iff_fixedBy.1 h) hq
        · exact h
      rw [h2, ht, mul_one, inv_mul_cancel]
      simp [hq, M.one_mem]
  rw [Fintype.sum_congr _ _ key, Finset.sum_boole]
  congr 1
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun q => ⟨q.1.out, q.2⟩
      invFun := fun x => ⟨Quotient.mk _ x.1, by rw [out_mk_of_smul_eq H x.2.1]; exact x.2⟩
      left_inv := fun q => Subtype.ext (Quotient.out_eq q.1)
      right_inv := fun x => Subtype.ext (out_mk_of_smul_eq H x.2.1) }

end Transfer

theorem smul_coe_eq_iff_conj_mem (H : Subgroup G) (g y : G) :
    g • (y : G ⧸ H) = y ↔ y⁻¹ * g * y ∈ H := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq,
    show (g * y)⁻¹ * y = (y⁻¹ * g * y)⁻¹ by group, inv_mem_iff]

theorem conj_out_mem_of_smul_eq (H : Subgroup G) {g : G} {x : G ⧸ H} (hx : g • x = x) :
    x.out⁻¹ * g * x.out ∈ H := by
  rw [← smul_coe_eq_iff_conj_mem, QuotientGroup.out_eq']
  exact hx

theorem centralizer_conj_eq_map (t y : G) :
    Subgroup.centralizer {y⁻¹ * t * y} =
      (Subgroup.centralizer {t}).map (MulAut.conj y⁻¹).toMonoidHom := by
  ext z
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · intro hz
    refine ⟨y * z * y⁻¹, Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · calc y * z * y⁻¹ * t = y * (z * (y⁻¹ * t * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * t * y) * z) * y⁻¹ := by rw [hz]
        _ = t * (y * z * y⁻¹) := by group
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨c, hc, rfl⟩
    have hc' := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc y⁻¹ * c * y * (y⁻¹ * t * y) = y⁻¹ * (c * t) * y := by group
      _ = y⁻¹ * (t * c) * y := by rw [hc']
      _ = y⁻¹ * t * y * (y⁻¹ * c * y) := by group

open _root_.Classical in
theorem natCard_subtype_and_add (α : Type*) [Finite α] (p q : α → Prop) :
    Nat.card {x // p x ∧ q x} + Nat.card {x // p x ∧ ¬ q x} = Nat.card {x // p x} := by
  have : Fintype α := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter p) q,
    Finset.filter_filter, Finset.filter_filter]

end TransferExtremal

open TransferExtremal

theorem exists_conj_mem_odd_relIndex_of_transfer {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {M : Subgroup G} (hMidx : M.relIndex T = 2) {t : G} (ht : t ^ 2 = 1)
    (hG : ∀ K : Subgroup G, K.index = 2 → t ∈ K) :
    ∃ g : G, g * t * g⁻¹ ∈ M ∧
      Odd ((T : Subgroup G).relIndex (Subgroup.centralizer {g * t * g⁻¹})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htV : (sgn (T : Subgroup G) M hMidx).transfer t = 1 := by
    have hidx : ((sgn (T : Subgroup G) M hMidx).transfer).ker.index ∣ 2 := by
      rw [Subgroup.index_ker]
      have h := Subgroup.card_subgroup_dvd_card ((sgn (T : Subgroup G) M hMidx).transfer).range
      rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2)), Fintype.card_multiplicative,
        ZMod.card] at h
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
    · rw [Subgroup.index_eq_one] at h
      have hmem : t ∈ ((sgn (T : Subgroup G) M hMidx).transfer).ker := by
        rw [h]; exact Subgroup.mem_top t
      exact hmem
    · exact hG _ h
  have hB : Even (Nat.card {x : G ⧸ (T : Subgroup G) //
      t • x = x ∧ x.out⁻¹ * t * x.out ∉ M}) := by
    have h := toAdd_transfer_eq (T : Subgroup G) M hMidx ht
    rw [htV, toAdd_one] at h
    exact ZMod.natCast_eq_zero_iff_even.1 h.symm
  have hF : Odd (Nat.card {x : G ⧸ (T : Subgroup G) // t • x = x}) := by
    have h := card_modEq_card_fixedBy (α := G ⧸ (T : Subgroup G)) ht
    have hidx : ¬ 2 ∣ Nat.card (G ⧸ (T : Subgroup G)) := T.not_dvd_index
    have hfix : Nat.card (fixedBy (G ⧸ (T : Subgroup G)) t) =
        Nat.card {x : G ⧸ (T : Subgroup G) // t • x = x} := rfl
    rw [hfix] at h
    rw [Nat.odd_iff, ← h]
    omega
  have hA : Odd (Nat.card {x : G ⧸ (T : Subgroup G) //
      t • x = x ∧ x.out⁻¹ * t * x.out ∈ M}) := by
    have h := natCard_subtype_and_add (G ⧸ (T : Subgroup G)) (fun x => t • x = x)
      (fun x => x.out⁻¹ * t * x.out ∈ M)
    rw [← h] at hF
    exact (Nat.odd_add.1 hF).2 hB
  have hN := Subgroup.normal_of_index_eq_two (H := M.subgroupOf (T : Subgroup G)) hMidx
  let C : Subgroup G := Subgroup.centralizer {t}
  let S : Sylow 2 C := default
  let A : SubMulAction (S : Subgroup C) (G ⧸ (T : Subgroup G)) :=
    { carrier := {x | t • x = x ∧ x.out⁻¹ * t * x.out ∈ M}
      smul_mem' := by
        intro s x hx
        have hc : ((s : C) : G) * t = t * ((s : C) : G) :=
          Subgroup.mem_centralizer_singleton_iff.1 (s : C).2
        refine ⟨?_, ?_⟩
        · show t • (((s : C) : G) • x) = ((s : C) : G) • x
          rw [smul_smul, ← hc, ← smul_smul, hx.1]
        · show (((s : C) : G) • x).out⁻¹ * t * (((s : C) : G) • x).out ∈ M
          have hz : ((((s : C) : G) * x.out : G) : G ⧸ (T : Subgroup G)) =
              ((((s : C) : G) • x).out : G ⧸ (T : Subgroup G)) := by
            rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe,
              QuotientGroup.out_eq']
          have hh := QuotientGroup.eq.1 hz
          have hnT := conj_out_mem_of_smul_eq (T : Subgroup G) hx.1
          have hconj := hN.conj_mem ⟨_, hnT⟩ (Subgroup.mem_subgroupOf.2 hx.2) ⟨_, hh⟩⁻¹
          have hct : ((s : C) : G) * t * ((s : C) : G)⁻¹ = t := by rw [hc, mul_inv_cancel_right]
          have e : (((s : C) : G) • x).out⁻¹ * t * (((s : C) : G) • x).out =
              ((((s : C) : G) * x.out)⁻¹ * (((s : C) : G) • x).out)⁻¹ * (x.out⁻¹ * t * x.out) *
                ((((s : C) : G) * x.out)⁻¹ * (((s : C) : G) • x).out) := by
            calc (((s : C) : G) • x).out⁻¹ * t * (((s : C) : G) • x).out =
                (((s : C) : G) • x).out⁻¹ * (((s : C) : G) * t * ((s : C) : G)⁻¹) *
                  (((s : C) : G) • x).out := by rw [hct]
              _ = _ := by group
          rw [e]
          have hm := Subgroup.mem_subgroupOf.1 hconj
          simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using hm }
  have hcong := S.isPGroup'.card_modEq_card_fixedPoints A
  have hAcard : Nat.card A = Nat.card {x : G ⧸ (T : Subgroup G) //
      t • x = x ∧ x.out⁻¹ * t * x.out ∈ M} := rfl
  rw [hAcard] at hcong
  have hne : Nat.card (fixedPoints (S : Subgroup C) A) ≠ 0 := by
    intro h0
    rw [h0] at hcong
    exact (Nat.not_even_iff_odd.2 hA) (Nat.even_iff.2 hcong)
  obtain ⟨⟨a, ha⟩⟩ := (Nat.card_ne_zero.1 hne).1
  have hfix : ∀ s : (S : Subgroup C), ((s : C) : G) • (a : G ⧸ (T : Subgroup G)) = a :=
    fun s => congrArg Subtype.val (ha s)
  refine ⟨(a : G ⧸ (T : Subgroup G)).out⁻¹, ?_, ?_⟩
  · rw [inv_inv]
    exact a.2.2
  · rw [inv_inv, centralizer_conj_eq_map]
    have hle : ((S : Subgroup C).map C.subtype).map
        (MulAut.conj (a : G ⧸ (T : Subgroup G)).out⁻¹).toMonoidHom ≤ (T : Subgroup G) := by
      rintro _ ⟨w, ⟨s, hs, rfl⟩, rfl⟩
      have h := conj_out_mem_of_smul_eq (T : Subgroup G) (hfix ⟨s, hs⟩)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact h
    have hdvd := Subgroup.relIndex_dvd_of_le_left (C.map
      (MulAut.conj (a : G ⧸ (T : Subgroup G)).out⁻¹).toMonoidHom) hle
    have hidx : (((S : Subgroup C).map C.subtype).map
        (MulAut.conj (a : G ⧸ (T : Subgroup G)).out⁻¹).toMonoidHom).relIndex
          (C.map (MulAut.conj (a : G ⧸ (T : Subgroup G)).out⁻¹).toMonoidHom) =
        (S : Subgroup C).index := by
      rw [Subgroup.relIndex_map_map_of_injective _ _
        (MulAut.conj (a : G ⧸ (T : Subgroup G)).out⁻¹).injective, Subgroup.relIndex,
        Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    rw [hidx] at hdvd
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => S.not_dvd_index (h.trans hdvd))


theorem exists_conj_mem_odd_relIndex_of_isSimpleGroup {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hG2 : Nat.card G ≠ 2) (T : Sylow 2 G) {M : Subgroup G}
    (hMidx : M.relIndex T = 2) {t : G} (ht : t ^ 2 = 1) :
    ∃ g : G, g * t * g⁻¹ ∈ M ∧
      Odd ((T : Subgroup G).relIndex (Subgroup.centralizer {g * t * g⁻¹})) :=
  exists_conj_mem_odd_relIndex_of_transfer T hMidx ht fun K hK => by
    have hN := Subgroup.normal_of_index_eq_two hK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · rw [h, Subgroup.index_bot] at hK
      exact absurd hK hG2
    · rw [h, Subgroup.index_top] at hK
      exact absurd hK (by norm_num)

end CFSG.Monster.B.Recog

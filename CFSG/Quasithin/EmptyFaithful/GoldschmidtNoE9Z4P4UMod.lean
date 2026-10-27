module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Odd
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Ex2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Pair

variable {V : Type} [CommGroup V] [Finite V] {X Tb P Qa Qb : Subgroup (MulAut V)}

omit [Finite V] in
theorem PlanePair.symm (hp : PlanePair Tb P Qa Qb) : PlanePair Tb P Qb Qa := by
  obtain ⟨hQa, hQb, hca, hcb, hsup, hdisj, hcsup, hfa, hfb, σ, hσ, hσQ⟩ := hp
  refine ⟨hQb, hQa, hcb, hca, by rw [sup_comm]; exact hsup, hdisj.symm,
    by rw [sup_comm]; exact hcsup, hfb, hfa, σ⁻¹, Tb.inv_mem hσ, ?_⟩
  ext x
  rw [mem_conjBy_iff, ← hσQ, mem_conjBy_iff]
  simp [mul_assoc]

omit [Finite V] in
theorem conjBy_mul_eq (a b : MulAut V) (Q : Subgroup (MulAut V)) :
    conjBy (a * b) Q = conjBy a (conjBy b Q) := by
  ext x
  rw [mem_conjBy_iff, mem_conjBy_iff, mem_conjBy_iff]
  simp [mul_assoc]

omit [Finite V] in
theorem E9Z4Str.mem_normalizer_swap (h : E9Z4Str X Tb P) (hp : PlanePair Tb P Qa Qb)
    {y : MulAut V} (hy : y ∈ Tb) (hya : y ∈ Subgroup.normalizer (Qa : Set (MulAut V))) :
    y ∈ Subgroup.normalizer (Qb : Set (MulAut V)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, σ, hσ, hσQ⟩ := hp
  rw [E9Z4Str.mem_normalizer_iff_conjBy] at hya ⊢
  rw [← hσQ, ← conjBy_mul_eq, ← h.Tb_comm hσ hy, conjBy_mul_eq, hya]

theorem E9Z4Str.conjBy_eq_of_not_mem_normalizer (h : E9Z4Str X Tb P) (hp : PlanePair Tb P Qa Qb)
    {y : MulAut V} (hy : y ∈ Tb) (hyn : y ∉ Subgroup.normalizer (Qa : Set (MulAut V))) :
    conjBy y Qa = Qb := by
  have hidx := h.relIndex_normalizer_Tb hp
  obtain ⟨-, -, hQ3, -, -, -, -, -, -, σ, hσ, hσQ⟩ := id hp
  have hσn : σ ∉ Subgroup.normalizer (Qa : Set (MulAut V)) := by
    intro hn
    have hc := E9Z4Str.mem_normalizer_iff_conjBy.mp hn
    rw [hσQ] at hc
    have hinf := h.plane_inf_eq_bot hp
    rw [← hc, inf_idem] at hinf
    have : Nat.card Qa = 1 := by rw [← hc, hinf, Subgroup.card_bot]
    omega
  set N : Subgroup (MulAut V) := Subgroup.normalizer (Qa : Set (MulAut V)) with hN
  have hidx' : (N.subgroupOf Tb).index = 2 := hidx
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.mp hidx'
  have key : ∀ x : Tb, (x : MulAut V) ∉ N → x * c ∈ N.subgroupOf Tb := by
    intro x hx
    rcases hc x with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (Subgroup.mem_subgroupOf.mp h1) hx
  have h1 := key ⟨σ, hσ⟩ hσn
  have h2 := key ⟨y, hy⟩ hyn
  have h3 := (N.subgroupOf Tb).mul_mem h1 ((N.subgroupOf Tb).inv_mem h2)
  have e : (⟨σ, hσ⟩ * c) * (⟨y, hy⟩ * c)⁻¹ = (⟨σ, hσ⟩ * ⟨y, hy⟩⁻¹ : Tb) := by group
  rw [e] at h3
  have hn : σ * y⁻¹ ∈ N := Subgroup.mem_subgroupOf.mp h3
  have hnb : σ * y⁻¹ ∈ Subgroup.normalizer (Qb : Set (MulAut V)) :=
    h.mem_normalizer_swap hp (Tb.mul_mem hσ (Tb.inv_mem hy)) hn
  have hcn := E9Z4Str.mem_normalizer_iff_conjBy.mp
    ((Subgroup.normalizer (Qb : Set (MulAut V))).inv_mem hnb)
  have hy' : y = (σ * y⁻¹)⁻¹ * σ := by group
  rw [hy', conjBy_mul_eq, hσQ, hcn]

end Pair

section Group

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem inf_normalizer_HLb_swap
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {Tb P Qa Qb : Subgroup (MulAut ↥(kOf (rhoH h)))} (hTH : T ≤ H)
    (hTb : Tb = (T.subgroupOf H).map (resBeta (rhoH h)))
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) (hp : PlanePair Tb P Qa Qb) :
    T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qb : Set G) =
      T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G) := by
  have key : ∀ {Qa Qb : Subgroup (MulAut ↥(kOf (rhoH h)))}, PlanePair Tb P Qa Qb →
      T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G) ≤
        T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qb : Set G) := by
    intro Qa Qb hp x ⟨hxT, hxN⟩
    have hxH : x ∈ H := hTH hxT
    have hyT : resBeta (rhoH h) ⟨x, hxH⟩ ∈ Tb :=
      hTb ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxT)
    refine ⟨hxT, (mem_normalizer_HLb_iff h (hp.2.1.trans hstr.P_le_X)).mpr
      (hstr.mem_normalizer_swap hp hyT ((mem_normalizer_HLb_iff h
        (hp.1.trans hstr.P_le_X)).mp hxN))⟩
  exact le_antisymm (key hp.symm) (key hp)

theorem exists_oTwoUpper_moves
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {Tb P Qa Qb : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) (hp : PlanePair Tb P Qa Qb)
    {v : G} (hv : v ∈ conjClosure (VZ T M) H) {k k' : ↥(kOf (rhoH h))} (hk : k ∈ commV Qa)
    (hk1 : k ≠ 1) (hk' : k' ∈ commV Qb)
    (hcls : clsU h hv = (k : UMod h) * (k' : UMod h)) :
    ∃ x ∈ oTwoUpper (HLb (resBeta (rhoH h)) Qa), x * v * x⁻¹ ≠ v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ3 : Nat.card Qa = 3 := hp.2.2.1
  have hr : Qa ≤ (resBeta (rhoH h)).range := hp.1.trans hstr.P_le_X
  obtain ⟨q, hqQ, hq1, -, -⟩ := exists_generator_of_prime_card hQ3
  obtain ⟨x, hxH, hxO, hxq⟩ := exists_mem_oTwoUpper_resBeta_eq h hr hQ3 hqQ
  refine ⟨x, hxO, fun hxv => ?_⟩
  have hρ : rhoH h ⟨x, hxH⟩ (clsU h hv) = clsU h hv := by
    rw [rhoH_clsU]
    exact clsU_congr h _ hv hxv
  rw [hcls, map_mul] at hρ
  have h1 : rhoH h ⟨x, hxH⟩ (k : UMod h) = ((q k : ↥(kOf (rhoH h))) : UMod h) := by
    rw [← hxq]
    exact (resBeta_apply _ _ k).symm
  have h2 : rhoH h ⟨x, hxH⟩ (k' : UMod h) = (k' : UMod h) := by
    have hfix : resBeta (rhoH h) ⟨x, hxH⟩ k' = k' := by
      rw [hxq]
      exact hp.2.2.2.2.2.2.2.2.1 hk' q hqQ
    exact (resBeta_apply _ _ k').symm.trans (congrArg Subtype.val hfix)
  rw [h1, h2] at hρ
  have h3 : q k = k := Subtype.ext (mul_right_cancel hρ)
  exact hk1 (hstr.eq_one_of_fix_plane hQ3 hqQ hq1 hk h3)

theorem exists_moves_self
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Tb P Qa Qb : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) (hp : PlanePair Tb P Qa Qb) {u : G}
    (hu : u ∈ uHi T M H (HLb (resBeta (rhoH h)) Qa)) (huZ : u ∉ quasithinOmegaOneCenter T) :
    ∃ x ∈ oTwoUpper (HLb (resBeta (rhoH h)) Qa), x * u * x⁻¹ ≠ u := by
  have hr : Qa ≤ (resBeta (rhoH h)).range := hp.1.trans hstr.P_le_X
  have hUu : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure (HLb_le _) hu
  obtain ⟨k, hk, hkc⟩ := exists_mem_commV_of_mem_uHi h hsplit hr hUu hu
  have hk1 : k ≠ 1 := fun e => huZ ((clsU_eq_one_iff h hUu).mp (by rw [← hkc, e]; rfl))
  exact exists_oTwoUpper_moves h hstr hp hUu hk hk1 (one_mem _)
    (k' := 1) (by rw [← hkc]; simp)

theorem exists_moves_mul_conj
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Tb P Qa Qb : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) (hp : PlanePair Tb P Qa Qb) {u t : G}
    (hu : u ∈ uHi T M H (HLb (resBeta (rhoH h)) Qa)) (huZ : u ∉ quasithinOmegaOneCenter T)
    (htH : t ∈ H) (htc : conjBy (resBeta (rhoH h) ⟨t, htH⟩) Qa = Qb) :
    ∃ x ∈ oTwoUpper (HLb (resBeta (rhoH h)) Qa),
      x * (u * (t * u * t⁻¹)) * x⁻¹ ≠ u * (t * u * t⁻¹) := by
  have hr : Qa ≤ (resBeta (rhoH h)).range := hp.1.trans hstr.P_le_X
  have hUu : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure (HLb_le _) hu
  have hUt : t * u * t⁻¹ ∈ conjClosure (VZ T M) H := conj_mem_UH htH hUu
  have hUv : u * (t * u * t⁻¹) ∈ conjClosure (VZ T M) H :=
    (conjClosure (VZ T M) H).mul_mem hUu hUt
  obtain ⟨k, hk, hkc⟩ := exists_mem_commV_of_mem_uHi h hsplit hr hUu hu
  have hk1 : k ≠ 1 := fun e => huZ ((clsU_eq_one_iff h hUu).mp (by rw [← hkc, e]; rfl))
  have hk' : resBeta (rhoH h) ⟨t, htH⟩ k ∈ commV Qb := by
    rw [← htc, commV_conjBy]
    exact ⟨k, hk, rfl⟩
  refine exists_oTwoUpper_moves h hstr hp hUv hk hk1 hk' ?_
  rw [← clsU_mul h hUu hUt, ← hkc, ← rhoH_clsU h ⟨t, htH⟩ hUu, ← hkc]
  exact congrArg _ (resBeta_apply _ _ k).symm

end Group

end CFSG.Quasithin

module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec18

theorem false_of_dihedral_l2odd189 {G : Type*} [Group G] {H : Subgroup G} {z : ℕ}
    (e : H ≃* DihedralGroup z) {T : Subgroup G} (hTH : T ≤ H) (hT : ¬ IsCyclic T)
    (hT2 : IsPGroup 2 T) {x : G} (hxH : x ∈ H) (hx : orderOf x = 3)
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) : False := by
  have hxo : orderOf (⟨x, hxH⟩ : H) = 3 := by rw [Subgroup.orderOf_mk, hx]
  obtain ⟨k, hk⟩ : ∃ k : ZMod z, e ⟨x, hxH⟩ = DihedralGroup.r k := by
    rcases h : e ⟨x, hxH⟩ with k | k
    · exact ⟨k, rfl⟩
    · exfalso
      have := MulEquiv.orderOf_eq e ⟨x, hxH⟩
      rw [h, DihedralGroup.orderOf_sr, hxo] at this
      norm_num at this
  have hk3 : k * 3 = 0 := by
    have h3 : (⟨x, hxH⟩ : H) ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
    have := congrArg e h3
    rw [map_pow, hk, DihedralGroup.r_pow, map_one, DihedralGroup.one_def] at this
    exact DihedralGroup.r.inj this
  obtain ⟨t, htT, i, hi⟩ :
      ∃ (t : G) (htT : t ∈ T), ∃ i : ZMod z, e ⟨t, hTH htT⟩ = DihedralGroup.sr i := by
    by_contra hno
    push Not at hno
    apply hT
    let f : T →* DihedralGroup z := e.toMonoidHom.comp (Subgroup.inclusion hTH)
    have hf : ∀ t : T, f t ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z) := by
      intro t
      rcases h : f t with j | j
      · obtain ⟨n, rfl⟩ := ZMod.intCast_surjective j
        exact ⟨n, DihedralGroup.r_one_zpow n⟩
      · exact absurd h (hno t t.2 j)
    refine isCyclic_of_injective (f.codRestrict _ hf) fun a b hab => ?_
    have h := congrArg Subtype.val hab
    simp only [MonoidHom.codRestrict_apply] at h
    exact Subgroup.inclusion_injective hTH (e.injective h)
  have hxtx : x * t * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hxT t).mp htT
  have hmem : t * (x * t * x⁻¹) ∈ H := H.mul_mem (hTH htT) (hTH hxtx)
  have heq : t * (x * t * x⁻¹) = x := by
    have h1 : (⟨t * (x * t * x⁻¹), hmem⟩ : H) =
        ⟨t, hTH htT⟩ * (⟨x, hxH⟩ * ⟨t, hTH htT⟩ * (⟨x, hxH⟩ : H)⁻¹) := rfl
    have h2 : e ⟨t * (x * t * x⁻¹), hmem⟩ = e ⟨x, hxH⟩ := by
      rw [h1, map_mul, map_mul, map_mul, map_inv, hi, hk, DihedralGroup.r_mul_sr,
        DihedralGroup.inv_r, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
      congr 1
      linear_combination (-1 : ZMod z) * hk3
    exact congrArg Subtype.val (e.injective h2)
  have hxT' : x ∈ T := heq ▸ T.mul_mem htT hxtx
  obtain ⟨n, hn⟩ := hT2 ⟨x, hxT'⟩
  have hdvd : orderOf x ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  rw [hx] at hdvd
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

theorem false_of_perm_four_l2odd189 {G : Type*} [Group G] [Finite G] {H T : Subgroup G}
    (e : H ≃* Equiv.Perm (Fin 4)) (hTH : T ≤ H) (hHT : H ≤ Subgroup.normalizer (T : Set G))
    (hcard : Nat.card H = Nat.card T * 3) : False := by
  have hN : (T.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTH).mpr hHT
  have hTc : Nat.card (T.subgroupOf H) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hQ : Nat.card (H ⧸ T.subgroupOf H) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf H)
    rw [hTc, hcard, mul_comm (Nat.card T) 3] at h
    exact (Nat.eq_of_mul_eq_mul_right hpos h).symm
  have hinv : ∀ b : H, b * b = 1 → b ∈ T.subgroupOf H := by
    intro b hb
    have h3 : ((b : H ⧸ T.subgroupOf H)) ^ 3 = 1 := by
      rw [← hQ]
      exact pow_card_eq_one'
    have h2 : ((b : H ⧸ T.subgroupOf H)) * (b : H ⧸ T.subgroupOf H) = 1 := by
      rw [← QuotientGroup.mk_mul, hb, QuotientGroup.mk_one]
    have h1 : (b : H ⧸ T.subgroupOf H) = 1 := by
      calc (b : H ⧸ T.subgroupOf H) =
            (b : H ⧸ T.subgroupOf H) ^ 3 * ((b : H ⧸ T.subgroupOf H) *
              (b : H ⧸ T.subgroupOf H))⁻¹ := by group
        _ = 1 := by rw [h3, h2, inv_one, one_mul]
    exact (QuotientGroup.eq_one_iff b).mp h1
  have htop : T.subgroupOf H = ⊤ := by
    rw [eq_top_iff]
    have h : (⊤ : Subgroup H) =
        (Subgroup.closure {σ : Equiv.Perm (Fin 4) | σ.IsSwap}).map e.symm.toMonoidHom := by
      rw [Equiv.Perm.closure_isSwap, Subgroup.map_top_of_surjective _ e.symm.surjective]
    rw [h, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨σ, ⟨a, b, -, rfl⟩, rfl⟩
    apply hinv
    rw [← map_mul]
    simp [Equiv.swap_mul_self]
  have h := Nat.card_congr (MulEquiv.subgroupCongr htop).toEquiv
  rw [Subgroup.card_top, hTc, hcard] at h
  omega

theorem alternatingGroup_four_not_inv_l2odd189 :
    ∀ a b : alternatingGroup (Fin 4), a ^ 3 = 1 → a ≠ 1 → b * a * b⁻¹ ≠ a⁻¹ := by
  decide +kernel

theorem false_of_alternating_four_l2odd189 {G : Type*} [Group G] {H : Subgroup G}
    (e : H ≃* alternatingGroup (Fin 4)) {x w : G} (hxH : x ∈ H) (hwH : w ∈ H)
    (hx : orderOf x = 3) (hwx : w * x * w⁻¹ = x⁻¹) : False := by
  have hxo : orderOf (⟨x, hxH⟩ : H) = 3 := by rw [Subgroup.orderOf_mk, hx]
  refine alternatingGroup_four_not_inv_l2odd189 (e ⟨x, hxH⟩) (e ⟨w, hwH⟩) ?_ ?_ ?_
  · rw [← map_pow, ← hxo, pow_orderOf_eq_one, map_one]
  · intro h
    have h1 : (⟨x, hxH⟩ : H) = 1 := by rw [← map_eq_one_iff e e.injective]; exact h
    rw [h1, orderOf_one] at hxo
    norm_num at hxo
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext hwx

theorem false_of_borel_l2odd189 {G : Type*} [Group G] {H T : Subgroup G} (hTH : T ≤ H)
    (hT : ¬ IsCyclic T) (hT2 : IsPGroup 2 T) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup H} [P.Normal] (hPp : IsPGroup p P) (hPc : IsCyclic (H ⧸ P)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply hT
  have hT2' : IsPGroup 2 (T.subgroupOf H) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hdisj : Disjoint (T.subgroupOf H) P :=
    IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) _ _ hT2' hPp
  have hcyc : IsCyclic (T.subgroupOf H) := by
    refine isCyclic_of_injective ((QuotientGroup.mk' P).comp (T.subgroupOf H).subtype) ?_
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ht
    have hmem : (t : H) ∈ T.subgroupOf H ⊓ P := ⟨t.2, ht⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (Subtype.ext hmem)
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTH).surjective

end CFSG.RankThree.PartTwo.Sec18

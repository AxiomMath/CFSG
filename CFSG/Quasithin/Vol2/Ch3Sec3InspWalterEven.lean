module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterC0
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.Dihedral.Glauberman.DicksonMaxList

public section

namespace CFSG.Quasithin.H13.S3320

open CFSG.QuasithinUnique CFSG.RankThree.PartOne.KCRootAxis
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

variable {Q : Type} [Group Q] [Finite Q] {Y : Subgroup Q}

omit [Finite Q] in
theorem commutator_mem_of_char_two [Y.Normal] (hC : Subgroup.centralizer (Y : Set Q) = ⊥)
    {K : Type} [Field K] [Finite K] [CharP K 2] (eY : ↥Y ≃* PSL(2, K)) (x y : Q) :
    x * y * x⁻¹ * y⁻¹ ∈ Y := by
  let eS : ↥Y ≃* SL₂ K := eY.trans (slEquivPSL K).symm
  let ψ : Q →* MulAut (SL₂ K) := (MulAut.congr eS).toMonoidHom.comp MulAut.conjNormal
  let π : Q →* Outer (SL₂ K) := (QuotientGroup.mk' (inner (SL₂ K))).comp ψ
  have hcyc : IsCyclic (Outer (SL₂ K)) := out_sl2_isCyclic
  obtain ⟨γ, hγ⟩ := hcyc.exists_generator
  have hcomm : π (x * y * x⁻¹ * y⁻¹) = 1 := by
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hγ (π x))
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hγ (π y))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← ha, ← hb,
      (Commute.zpow_zpow_self γ a b).eq]
    group
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff _).mp hcomm
  exact mem_of_congr_conjNormal_eq hC eS hg.symm

theorem not_L2even [Y.Normal] (hC : Subgroup.centralizer (Y : Set Q) = ⊥) {f : ℕ} (hf : 2 ≤ f)
    (eY : ↥Y ≃* PSL(2, GaloisField 2 f)) {S H : Subgroup Q} (hS : IsSylowTwoOf S ⊤)
    (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hSH : S ≤ H)
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hWS, hW2, hWc, -, hSW, h₀, hh₀H, hh₀, s, hsS, hw'⟩ := o2_facts hS hab hSH e
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hSY : Nat.card ↥(S ⊓ Y) = 2 ^ f := by
    rw [card_inf_normal hS, Nat.card_congr eY.toEquiv]
    let P : Sylow 2 (PSL(2, GaloisField 2 f)) := Classical.choice Sylow.nonempty
    obtain ⟨eP⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hK P
    rw [← Sylow.card_eq_multiplicity P, ← Nat.card_congr eP.toEquiv]
    exact hK
  set T : Subgroup Q := S ⊓ Y with hT
  have hWrelS : W.relIndex S = 2 := by
    have h1 := Subgroup.card_mul_index (W.subgroupOf S)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWS).toEquiv, hSW] at h1
    have h1' : Nat.card W * W.relIndex S = 2 * Nat.card W := h1
    have hpos : 0 < Nat.card W := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1']; ring)
  have hWrelT : W.relIndex T ≤ 2 :=
    hWrelS ▸ Subgroup.relIndex_le_of_le_right inf_le_left (by rw [hWrelS]; norm_num)
  have hcardWT : 2 ≤ Nat.card (W.subgroupOf T) := by
    have h1 := Subgroup.card_mul_index (W.subgroupOf T)
    have h4 : 4 ≤ Nat.card T := by
      rw [hSY]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have h2 : (W.subgroupOf T).index ≤ 2 := hWrelT
    by_contra hlt
    push Not at hlt
    have : Nat.card (W.subgroupOf T) * (W.subgroupOf T).index ≤ 1 * 2 :=
      Nat.mul_le_mul (by omega) h2
    omega
  have hWT2 : IsPGroup 2 (W.subgroupOf T) := hW2.comap_of_injective T.subtype T.subtype_injective
  obtain ⟨k, hk⟩ := hWT2.exists_card_eq
  have h2dvd : 2 ∣ Nat.card (W.subgroupOf T) := by
    rw [hk] at hcardWT ⊢
    rcases k with _ | k
    · simp at hcardWT
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  set t : Q := ((t' : ↥T) : Q) with htdef
  have htW : t ∈ W := Subgroup.mem_subgroupOf.mp t'.2
  have htY : t ∈ Y := (t' : ↥T).2.2
  have ht2 : orderOf t = 2 := by
    rw [htdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht']
  set w' := s * h₀ * s⁻¹ * h₀ with hw'def
  set z := s * h₀ * s⁻¹ * h₀⁻¹ with hzdef
  have hzY : z ∈ Y := commutator_mem_of_char_two hC eY s h₀
  have hzw : z = w' * (h₀⁻¹ * h₀⁻¹) := by rw [hzdef, hw'def]; group
  have hsH : s ∈ H := hSH hsS
  have hst : Commute s t := hab s hsS t (hWS htW)
  have hh₀t : Commute h₀ t := hWc t htW h₀ hh₀H
  have hzt : Commute z t := by
    rw [hzdef]
    exact ((hst.mul_left hh₀t).mul_left hst.inv_left).mul_left hh₀t.inv_left
  obtain ⟨m, hm⟩ := hW2.exists_card_eq
  have hw'm : w' ^ 2 ^ m = 1 := by
    have : (⟨w', hw'⟩ : ↥W) ^ 2 ^ m = 1 := by
      rw [← hm]
      exact pow_card_eq_one'
    simpa using congrArg Subtype.val this
  have hcw : Commute w' (h₀⁻¹ * h₀⁻¹) := by
    have h1 := hWc w' hw' h₀⁻¹ (H.inv_mem hh₀H)
    have h2 : Commute w' h₀⁻¹ := h1.symm
    exact h2.mul_right h2
  set c := z ^ 2 ^ m with hcdef
  have hcY : c ∈ Y := Y.pow_mem hzY _
  have hc_eq : c = (h₀⁻¹ * h₀⁻¹) ^ 2 ^ m := by
    rw [hcdef, hzw, hcw.mul_pow, hw'm, one_mul]
  have hh₀3 : h₀ ^ 3 = 1 := by rw [← hh₀]; exact pow_orderOf_eq_one h₀
  have hc3 : c ^ 3 = 1 := by
    rw [hc_eq, ← pow_mul, mul_comm, pow_mul, ← mul_inv_rev, inv_pow, (Commute.refl h₀).mul_pow,
      hh₀3, one_mul, inv_one, one_pow]
  have hc1 : c ≠ 1 := by
    intro h
    rw [hc_eq, ← mul_inv_rev, inv_pow, inv_eq_one, ← pow_two, ← pow_mul] at h
    have h3 : 3 ∣ 2 * 2 ^ m := hh₀ ▸ orderOf_dvd_of_pow_eq_one h
    have h4 : 3 ∣ 2 ^ (m + 1) := by rwa [pow_succ, mul_comm]
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
    omega
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hct : Commute c t := hzt.pow_left _
  have key := Glauberman.Dickson.psl2_eq_one_of_commute hK (c := eY ⟨c, hcY⟩) (x := eY ⟨t, htY⟩)
    (by
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hct.eq)
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hcord]; norm_num)
    (by
      have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
      have ht2'' : (⟨t, htY⟩ : ↥Y) ^ 2 = 1 := Subtype.ext (by simpa using ht2')
      rw [← map_pow, ht2'', map_one])
    (by
      rw [Ne, MulEquiv.map_eq_one_iff]
      intro h
      have : t = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at ht2
      omega)
  rw [MulEquiv.map_eq_one_iff] at key
  exact hc1 (congrArg Subtype.val key)

end CFSG.Quasithin.H13.S3320

module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.GF2Type.Smith1979.CaseIIExclL52
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S59

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {R : Type} [Group R] [Finite R]

theorem card_le_factorial_index_of_ne_top {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) : Nat.card G ≤ H.index.factorial := by
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  calc Nat.card G ≤ Nat.card (Equiv.Perm (G ⧸ H)) := Nat.card_le_card_of_injective _ hinj
    _ = H.index.factorial := by rw [Nat.card_perm, Subgroup.index_eq_card]

theorem center_eq_bot_of_simple_168 [IsSimpleGroup R] (hR : Nat.card R = 168) :
    Subgroup.center R = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : R, a * b = b * a := fun a b => by
      have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ : ∃ y : R, orderOf y = 2 :=
      exists_prime_orderOf_dvd_card' 2 (by omega)
    haveI : (Subgroup.zpowers y).Normal := ⟨fun n hn g => by
      have hc : g * n * g⁻¹ = n := by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]
      rw [hc]
      exact hn⟩
    have hy1 : Subgroup.zpowers y ≠ ⊥ := by
      intro h1
      have hc : Nat.card (Subgroup.zpowers y) = 1 := by rw [h1, Subgroup.card_bot]
      rw [Nat.card_zpowers, hy] at hc
      norm_num at hc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers y) with h2 | h2
    · exact hy1 h2
    · have hc : Nat.card (Subgroup.zpowers y) = 168 := by
        rw [h2, Subgroup.card_top, hR]
      rw [Nat.card_zpowers, hy] at hc
      norm_num at hc

theorem eq_top_of_orders_168 [IsSimpleGroup R] (hR : Nat.card R = 168) (K : Subgroup R)
    (h7 : ∃ x ∈ K, orderOf x = 7) (h3 : ∃ x ∈ K, orderOf x = 3)
    (h2 : ∃ x ∈ K, orderOf x = 2) : K = ⊤ := by
  obtain ⟨x, hx, hx7⟩ := h7
  obtain ⟨y, hy, hy3⟩ := h3
  obtain ⟨z, hz, hz2⟩ := h2
  have hdiv : ∀ g : R, g ∈ K → orderOf g ∣ Nat.card K := fun g hg => by
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_dvd_natCard _
  have h7' : 7 ∣ Nat.card K := by
    have h := hdiv x hx
    rwa [hx7] at h
  have h3' : 3 ∣ Nat.card K := by
    have h := hdiv y hy
    rwa [hy3] at h
  have h2' : 2 ∣ Nat.card K := by
    have h := hdiv z hz
    rwa [hz2] at h
  have h42 : 42 ∣ Nat.card K := by omega
  haveI : Nonempty K := ⟨1⟩
  have hge : 42 ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos h42
  by_contra hK
  have hidx : Nat.card K * K.index = 168 := by rw [Subgroup.card_mul_index, hR]
  have hle4 : K.index ≤ 4 := by
    have h1 : 42 * K.index ≤ Nat.card K * K.index := Nat.mul_le_mul hge (le_refl _)
    omega
  have hfac : 168 ≤ K.index.factorial := by
    have h := card_le_factorial_index_of_ne_top hK
    rwa [hR] at h
  have h24 : K.index.factorial ≤ Nat.factorial 4 := Nat.factorial_le hle4
  have h4 : Nat.factorial 4 = 24 := by decide
  omega

theorem exists_order_seven_normalized [IsSimpleGroup R] (hR : Nat.card R = 168) (β : R)
    (hβ : orderOf β = 3) : ∃ γ : R, orderOf γ = 7 ∧ β * γ * β⁻¹ ∈ Subgroup.zpowers γ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI hfin : Finite (Sylow 7 R) :=
    Finite.of_injective (fun P : Sylow 7 R => ((P : Subgroup R) : Set R))
      fun P Q h => Sylow.ext (SetLike.coe_injective h)
  have hN_dvd : Nat.card (Sylow 7 R) ∣ 168 := by
    obtain ⟨P0⟩ : Nonempty (Sylow 7 R) := inferInstance
    have h := (Sylow.card_dvd_index P0).trans (Subgroup.index_dvd_card (P0 : Subgroup R))
    rwa [hR] at h
  have hN_mod : Nat.card (Sylow 7 R) % 7 = 1 := card_sylow_modEq_one 7 R
  have hN3 : ¬ 3 ∣ Nat.card (Sylow 7 R) := by
    intro h3
    have hle : Nat.card (Sylow 7 R) ≤ 168 := Nat.le_of_dvd (by norm_num) hN_dvd
    have key : ∀ n : ℕ, n ≤ 168 → n ∣ 168 → n % 7 = 1 → n % 3 ≠ 0 := by
      intro n hn1 hn2 hn3 hn4
      interval_cases n <;> omega
    exact key _ hle hN_dvd hN_mod (by omega)
  have hβ3 : β ^ 3 = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  have hσ : (MulAction.toPermHom R (Sylow 7 R) β) ^ (3 ^ 1) = 1 := by
    rw [pow_one, ← map_pow, hβ3, map_one]
  haveI : Fintype (Sylow 7 R) := Fintype.ofFinite _
  have hcard3 : ¬ 3 ∣ Fintype.card (Sylow 7 R) := by
    rwa [← Nat.card_eq_fintype_card]
  obtain ⟨P, hP⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard3 hσ
  have hβP : β • P = P := hP
  have hn : β ∈ Subgroup.normalizer (P : Subgroup R) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hβP
  have h7R : 7 ∣ Nat.card R := by omega
  have hne : (P : Subgroup R) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P h7R
  have hdvdP : Nat.card (P : Subgroup R) ∣ 168 := by
    have h := Subgroup.card_subgroup_dvd_card (P : Subgroup R)
    rwa [hR] at h
  have hP7 : Nat.card (P : Subgroup R) = 7 := by
    obtain ⟨n, hn'⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · rcases Nat.lt_or_ge n 1 with h0 | h1
      · exfalso
        apply hne
        apply Subgroup.card_eq_one.mp
        rw [hn', show n = 0 by omega, pow_zero]
      · rw [hn', show n = 1 by omega, pow_one]
    · exfalso
      have h49 : 7 ^ 2 ∣ Nat.card (P : Subgroup R) := by
        rw [hn']
        exact pow_dvd_pow 7 hge
      have h49' := h49.trans hdvdP
      norm_num at h49'
  have h7P : 7 ∣ Nat.card (P : Subgroup R) := by omega
  obtain ⟨x, hx⟩ : ∃ x : (P : Subgroup R), orderOf x = 7 :=
    exists_prime_orderOf_dvd_card' 7 h7P
  have hxR : orderOf (x : R) = 7 := (Subgroup.orderOf_coe x).trans hx
  have hzp : Subgroup.zpowers (x : R) = (P : Subgroup R) := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr x.2
    · have h1 : Nat.card (Subgroup.zpowers (x : R)) = 7 := by
        rw [Nat.card_zpowers, hxR]
      omega
  refine ⟨(x : R), hxR, ?_⟩
  rw [hzp]
  exact (Subgroup.mem_normalizer_iff.mp hn (x : R)).mp x.2


section Transport

variable {G : Type} [Group G] [Finite G] {R : Subgroup G}

theorem isLnq_simple_card (h : IsLnq 3 2 1 R) : IsSimpleGroup ↥R ∧ Nat.card R = 168 := by
  obtain ⟨e⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two h
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
    CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  exact ⟨MulEquiv.isSimpleGroup e, by
    rw [Nat.card_congr e.toEquiv, CFSG.ComponentClassification.GHarris.card_GL32_gh]⟩

theorem exists_seven_in (h : IsLnq 3 2 1 R) {β : G} (hβR : β ∈ R) (hβ : orderOf β = 3) :
    ∃ γ ∈ R, orderOf γ = 7 ∧ β * γ * β⁻¹ ∈ Subgroup.zpowers γ := by
  obtain ⟨hs, hc⟩ := isLnq_simple_card h
  haveI := hs
  obtain ⟨γ, hγ7, hγ⟩ := exists_order_seven_normalized hc ⟨β, hβR⟩
    (by rw [Subgroup.orderOf_mk]; exact hβ)
  refine ⟨(γ : G), γ.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hγ7
  · have := Subgroup.mem_map_of_mem R.subtype hγ
    rw [MonoidHom.map_zpowers] at this
    simpa using this

theorem eq_of_orders_in (h : IsLnq 3 2 1 R) {K : Subgroup G} (hKR : K ≤ R)
    (h7 : ∃ x ∈ K, orderOf x = 7) (h3 : ∃ x ∈ K, orderOf x = 3)
    (h2 : ∃ x ∈ K, orderOf x = 2) : K = R := by
  obtain ⟨hs, hc⟩ := isLnq_simple_card h
  haveI := hs
  have key : ∀ n : ℕ, (∃ x ∈ K, orderOf x = n) → ∃ y ∈ K.subgroupOf R, orderOf y = n := by
    rintro n ⟨x, hx, hxn⟩
    refine ⟨⟨x, hKR hx⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
    rw [Subgroup.orderOf_mk]
    exact hxn
  have htop := eq_top_of_orders_168 hc (K.subgroupOf R) (key 7 h7) (key 3 h3) (key 2 h2)
  refine le_antisymm hKR fun x hx => ?_
  have : (⟨x, hx⟩ : R) ∈ K.subgroupOf R := by rw [htop]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem eq_one_of_central_in (h : IsLnq 3 2 1 R) {x : G} (hxR : x ∈ R)
    (hx : ∀ r ∈ R, x * r = r * x) : x = 1 := by
  obtain ⟨hs, hc⟩ := isLnq_simple_card h
  haveI := hs
  have hmem : (⟨x, hxR⟩ : R) ∈ Subgroup.center R :=
    Subgroup.mem_center_iff.mpr fun r => Subtype.ext (hx r r.2).symm
  rw [center_eq_bot_of_simple_168 hc, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

end Transport

end CFSG.RankThree.PartTwo.Sec21.FF81.S59

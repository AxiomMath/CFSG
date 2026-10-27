module

public import CFSG.LocalAnalysis.WeakClosure81.W16LBorelDefs
public import CFSG.GH74.Uniqueness.Bender.Sylow2SpecialSuzuki

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.GH74.Uniqueness.Bender
open Subgroup

section Certified


theorem borel166Conclusion_of_benderType_sz {K : Type} [Group K] [Finite K] {n : ℕ}
    (hB : BenderType K n 2 1) (Q : Sylow 2 K) {Y : Subgroup K} (hY : Nat.card Y = 2 ^ n)
    (hYe : IsElemAbelian 2 Y) (hYQ : Y ≤ (Q : Subgroup K)) :
    Borel166Conclusion Y (Q : Subgroup K) := by
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  have hRD := hB.suzuki_rootData Q
  have hn2 : 2 ≤ n := hB.two_le.2
  have hYZ : Y ≤ rootCenter (Q : Subgroup K) :=
    hc.elemAbelian_le_rootCenter hYQ (fun x hx => by
      simpa [pow_two] using hYe.2 x hx)
  have hYeq : Y = rootCenter (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hYZ (by rw [hY, hc.card_center])
  rw [hYeq]
  haveI : IsCyclic ↥(cartan (Q : Subgroup K) t) := hc.isCyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(cartan (Q : Subgroup K) t))
  set h : K := (g : K) with hh
  have hhD : h ∈ cartan (Q : Subgroup K) t := by rw [hh]; exact g.2
  have hhB : h ∈ borel (Q : Subgroup K) := cartan_le_borel _ t hhD
  have hcardD : Nat.card (cartan (Q : Subgroup K) t) = 2 ^ n - 1 := by
    rw [hc.card_cartan, mul_one]
  have hcardD_gt : 1 < Nat.card (cartan (Q : Subgroup K) t) := by
    rw [hcardD]
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hord : orderOf h = Nat.card (cartan (Q : Subgroup K) t) := by
    rw [hh, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  have hodd : Odd (orderOf h) := by rw [hord]; exact hc.odd_card_cartan
  have hne : h ≠ 1 := by
    intro h1
    rw [h1] at hord
    rw [orderOf_one] at hord
    omega
  have hgen : ∀ d ∈ cartan (Q : Subgroup K) t, ∃ k : ℤ, h ^ k = d := by
    intro d hd
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨d, hd⟩)
    exact ⟨k, by rw [hh, ← Subgroup.coe_zpow]; exact congrArg Subtype.val hk⟩
  refine ⟨h, ?_, ?_, hodd, ?_, ?_⟩
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_rootCenter hhB hx
    · intro hx
      have hmem : h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ ∈ rootCenter (Q : Subgroup K) :=
        conj_mem_rootCenter ((borel (Q : Subgroup K)).inv_mem hhB) hx
      rw [inv_inv] at hmem
      convert hmem using 1
      group
  ·
    exact hhB
  ·
    intro P₀ hZle hP₀le hinv
    have hnorm : h ∈ Subgroup.normalizer (P₀ : Set K) :=
      Subgroup.mem_normalizer_fintype (fun y hy => hinv y hy)
    have hzp : Subgroup.zpowers h ≤ Subgroup.normalizer (P₀ : Set K) :=
      Subgroup.zpowers_le.mpr hnorm
    refine hc.suzuki_irreducible hRD hZle hP₀le ?_
    intro d hd w hw
    obtain ⟨k, hk⟩ := hgen d hd
    have hdmem : d ∈ Subgroup.zpowers h := hk ▸ Subgroup.zpow_mem_zpowers h k
    exact (Subgroup.mem_normalizer_iff.mp (hzp hdmem) w).mp hw
  ·
    intro x hx hz
    by_contra hxZ
    set z : K := h * x * h⁻¹ * x⁻¹ with hzdef
    have hz' : z ∈ rootCenter (Q : Subgroup K) := by rw [hzdef]; exact hz
    have hw : x * x ∈ rootCenter (Q : Subgroup K) := hB.sq_mem_rootCenter_suzuki Q hx
    have hw1 : x * x ≠ 1 := fun h1 => hxZ (hc.mem_rootCenter_of_mul_self hx h1)
    have hxz : x * z = z * x := (mem_rootCenter_iff.mp hz').2 x hx
    have hzz : z * z = 1 := hc.center_sq z hz'
    have hconj : h * (x * x) * h⁻¹ = x * x := by
      have h1 : h * x * h⁻¹ = z * x := by rw [hzdef]; group
      calc h * (x * x) * h⁻¹ = (h * x * h⁻¹) * (h * x * h⁻¹) := by group
        _ = (z * x) * (z * x) := by rw [h1]
        _ = z * (x * z) * x := by group
        _ = z * (z * x) * x := by rw [hxz]
        _ = z * z * (x * x) := by group
        _ = x * x := by rw [hzz, one_mul]
    have hyh : h * (x * x) = (x * x) * h := by
      have := congrArg (fun w => w * h) hconj
      simpa [mul_assoc] using this
    have hcent : h ∈ Subgroup.centralizer ({x * x} : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hyh.symm
    have hin : h ∈ cartan (Q : Subgroup K) t ⊓ Subgroup.centralizer ({x * x} : Set K) :=
      ⟨hhD, hcent⟩
    rw [hc.cartan_inf_centralizer_eq hw hw1, hc.fixCartan_eq_bot, Subgroup.mem_bot] at hin
    exact hne hin

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end

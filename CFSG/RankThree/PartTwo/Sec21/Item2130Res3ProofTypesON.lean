module

import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLocal
public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofON

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.Native.ONTriple (GM)
open scoped commutatorElement
open Item211Res3Proof Item211Res2Proof

namespace Item2130Res3Proof

variable {G : Type} [Group G] [Finite G]

theorem false_of_tripleCover_ON
    {A E U L : Subgroup G} {c b : G} {U₀ Y : Subgroup G}
    (hcfg : Config2130 G A E U c L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hC : Choice2130 A E c L b U₀ Y) (hbY : b ∈ Y)
    (hON : Sec4.IsTripleCover (lBar Y) Blueprint.NativeSporadic.ON) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  have hbA : b ∈ A := hC.b_mem.1
  have hb1 := hC.b_ne_one
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  obtain ⟨hZ, -, -⟩ := Sec13.ON134.center_eq_zpowers hbY hb3 hb1 hYC hON
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hq.1 hON
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha b hbA)
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := hC.three_norm A hA3 hAC
  have hCA : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers b := by
    have h := hC.sec_cent
    rw [Sec13.sectionCentralizer_eq_inf hAN] at h
    exact SetLike.coe_injective h
  obtain ⟨b', hb'B, hb'b⟩ : ∃ b' ∈ A ⊓ L, b' ∉ Subgroup.zpowers b := by
    by_contra hall
    push Not at hall
    have h := Subgroup.card_le_of_le (show A ⊓ L ≤ Subgroup.zpowers b from hall)
    rw [h9, Sec13.card_zpowers_of_pow_three hb3 hb1] at h
    norm_num at h
  have hb'A : b' ∈ A := hb'B.1
  obtain ⟨w₀, hw₀W, hw₀B, hw₀c⟩ := hcfg.full b' hb'B
  have hBe : ∀ x ∈ A ⊓ L, x ^ 3 = 1 := fun x hx => hAe.2 x hx.1
  obtain ⟨k, hk3, hkc⟩ := exists_pow_conj_of_isPGroup hBe hb'B hw₀B hw₀c
  set w := w₀ ^ k with hw
  have hwB := pow_conj_eq_of_conj_eq hw₀B k
  have hwb : w * b = b * w := by
    have h1 := hwB b hC.b_mem
    calc w * b = w * b * w⁻¹ * w := by group
      _ = b * w := by rw [h1]
  have hwC : Subgroup.zpowers w ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hwb
  have hwY : w ∈ Subgroup.normalizer (Y : Set G) :=
    hC.three_norm _ hk3 hwC (Subgroup.mem_zpowers w)
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hw₀W k
  have hS : IsPGroup 3 (Subgroup.zpowers w ⊔ A : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hk3 hA3 (Subgroup.zpowers_le.mpr hwA)
  set S' := (Subgroup.zpowers w ⊔ A).subgroupOf (Subgroup.normalizer (Y : Set G)) with hS'
  have hS'3 : IsPGroup 3 S' := hS.comap_subtype
  set H : Subgroup (lBar Y) := (S'.map (barAct Y)).comap MulAut.conj with hH
  have hker : IsPGroup 3 (MulAut.conj : lBar Y →* MulAut (lBar Y)).ker := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    have hgZ : (g : lBar Y) ∈ Subgroup.center (lBar Y) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun τ : MulAut (lBar Y) => τ x) g.2
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * (g : lBar Y) = ((g : lBar Y) * x * (g : lBar Y)⁻¹) * g := by rw [h1]
        _ = (g : lBar Y) * x := by group
    have h := pow_card_eq_one' (G := Subgroup.center (lBar Y)) (x := ⟨g, hgZ⟩)
    rw [hON.1] at h
    simpa using congrArg Subtype.val h
  have hH3 : IsPGroup 3 H := (hS'3.map (barAct Y)).comap_of_ker_isPGroup _ hker
  have hmemH : ∀ (g : G) (hgS : g ∈ Subgroup.zpowers w ⊔ A)
      (hgN : g ∈ Subgroup.normalizer (Y : Set G)) (x : lBar Y),
      MulAut.conj x = barAct Y ⟨g, hgN⟩ → x ∈ H := by
    intro g hgS hgN x hx
    exact ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.mpr hgS, hx.symm⟩
  have hconj : ∀ (g : G) (hgN : g ∈ Subgroup.normalizer (Y : Set G)) (x : lBar Y),
      (∀ z, barAct Y ⟨g, hgN⟩ z = x * z * x⁻¹) → MulAut.conj x = barAct Y ⟨g, hgN⟩ := by
    intro g hgN x hx
    ext z
    rw [MulAut.conj_apply, hx z]
  obtain ⟨κ, hκ⟩ := exists_inner_of_commute ψ hbY hZ hwY hwb
  obtain ⟨γ, hγ⟩ := exists_inner_of_commute ψ hbY hZ (hAN hcA) (hcomm c hcA b hbA)
  obtain ⟨β, hβ⟩ := exists_inner_of_commute ψ hbY hZ (hAN hb'A) (hcomm b' hb'A b hbA)
  have hκ' := hconj w hwY κ hκ
  have hγ' := hconj c (hAN hcA) γ hγ
  have hβ' := hconj b' (hAN hb'A) β hβ
  have hκH : κ ∈ H := hmemH w (Subgroup.mem_sup_left (Subgroup.mem_zpowers w)) hwY κ hκ'
  have hγH : γ ∈ H := hmemH c (Subgroup.mem_sup_right hcA) (hAN hcA) γ hγ'
  have hcen := comm_mem_center_of_isPGroup ψ hH3 hκH hγH
  have hrel : MulAut.conj (κ * γ * κ⁻¹) = MulAut.conj (γ * β) := by
    rw [map_mul, map_mul, map_inv, map_mul, hκ', hγ', hβ', ← map_inv, ← map_mul, ← map_mul,
      ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hkc
  have hβZ : β ∈ Subgroup.center (lBar Y) := by
    have h1 : (γ * β)⁻¹ * (κ * γ * κ⁻¹) ∈ Subgroup.center (lBar Y) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h2 := congrArg (fun τ : MulAut (lBar Y) => τ x) hrel
      simp only [MulAut.conj_apply] at h2
      calc x * ((γ * β)⁻¹ * (κ * γ * κ⁻¹))
          = (γ * β)⁻¹ * ((γ * β) * x * (γ * β)⁻¹) * (κ * γ * κ⁻¹) := by group
        _ = (γ * β)⁻¹ * ((κ * γ * κ⁻¹) * x * (κ * γ * κ⁻¹)⁻¹) * (κ * γ * κ⁻¹) := by rw [h2]
        _ = (γ * β)⁻¹ * (κ * γ * κ⁻¹) * x := by group
    have h3 : (γ * β)⁻¹ * (κ * γ * κ⁻¹) = β⁻¹ * (γ⁻¹ * ⁅κ, γ⁆ * γ) := by
      rw [commutatorElement_def]
      group
    have h4 : γ⁻¹ * ⁅κ, γ⁆ * γ = ⁅κ, γ⁆ := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp hcen γ, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h3, h4] at h1
    have h5 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hcen)
    rw [mul_inv_cancel_right] at h5
    simpa using Subgroup.inv_mem _ h5
  have htriv : barAct Y ⟨b', hAN hb'A⟩ = 1 := by
    rw [← hβ']
    ext z
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hβZ z,
      mul_inv_cancel_right]
  have hb'θ : b' ∈ Sec4.thetaQuotCentralizer Y := ⟨⟨b', hAN hb'A⟩, htriv, rfl⟩
  exact hb'b (hCA ▸ ⟨hb'A, hb'θ⟩)

end Item2130Res3Proof

end CFSG.RankThree.PartTwo.Sec21

module

public import CFSG.Sporadic.Recognition.LyonsAS44McL
public import CFSG.Sporadic.Recognition.LyonsLocalCentralizerA3

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.GH74.GLS.Stage12

theorem inverts_of_inverts_mod {K : Type*} [Group K] {x s a : K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x⁻¹) (hax : a * x = x * a) {k : ℤ}
    (hk : s * a * s⁻¹ = a⁻¹ * x ^ k) : s * a * s⁻¹ = a⁻¹ := by
  have hxk : s * x ^ k * s⁻¹ = (x ^ k)⁻¹ := by
    rw [← conj_zpow, hsx, inv_zpow]
  have h1 : s * (s * a * s⁻¹) * s⁻¹ = a := by
    have : s * (s * a * s⁻¹) * s⁻¹ = (s * s) * a * (s⁻¹ * s⁻¹) := by group
    rw [this, hs2, ← mul_inv_rev, hs2]
    simp
  have hc : a * x ^ k = x ^ k * a := (Commute.zpow_right (show Commute a x from hax) k).eq
  have h2 : a = (x ^ k)⁻¹ * a * (x ^ k)⁻¹ := by
    calc a = s * (s * a * s⁻¹) * s⁻¹ := h1.symm
      _ = s * (a⁻¹ * x ^ k) * s⁻¹ := by rw [hk]
      _ = (s * a * s⁻¹)⁻¹ * (s * x ^ k * s⁻¹) := by group
      _ = (a⁻¹ * x ^ k)⁻¹ * (x ^ k)⁻¹ := by rw [hk, hxk]
      _ = (x ^ k)⁻¹ * a * (x ^ k)⁻¹ := by group
  have h3 : x ^ (2 * k) = 1 := by
    have hc' : (x ^ k)⁻¹ * a = a * (x ^ k)⁻¹ := by
      calc (x ^ k)⁻¹ * a = (x ^ k)⁻¹ * (a * x ^ k) * (x ^ k)⁻¹ := by group
        _ = (x ^ k)⁻¹ * (x ^ k * a) * (x ^ k)⁻¹ := by rw [hc]
        _ = a * (x ^ k)⁻¹ := by group
    have h4 : a = a * (x ^ k)⁻¹ * (x ^ k)⁻¹ := by
      calc a = (x ^ k)⁻¹ * a * (x ^ k)⁻¹ := h2
        _ = a * (x ^ k)⁻¹ * (x ^ k)⁻¹ := by rw [hc']
    have h5 : (x ^ k)⁻¹ * (x ^ k)⁻¹ = 1 :=
      mul_left_cancel (a := a) (show a * ((x ^ k)⁻¹ * (x ^ k)⁻¹) = a * 1 by
        rw [mul_one, ← mul_assoc]; exact h4.symm)
    rw [two_mul, zpow_add]
    have h6 : x ^ k * x ^ k = ((x ^ k)⁻¹ * (x ^ k)⁻¹)⁻¹ := by group
    rw [h6, h5, inv_one]
  have h7 := zpow_eq_one_of_zpow_two_mul hx3 hx1 h3
  rw [hk, h7, mul_one]

section Cert

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem exists_mclFacts_of_lyData (hnrm : nrmCheck = true) (D : LyData G t ρ)
    (S : LyStd ρ x₁ x₂ x₃) :
    ∃ R T A Y, McLFacts (CentQuot (x₁ : G)) (D.x₂Q S) (D.x₃Q S) R T A Y := by
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  have hy3 := D.orderOf_x₂Q S
  have hz3 := D.orderOf_x₃Q S
  have hc2 := card_centralizer_eq_of_five_dvd e hy3 (D.five_dvd_card_centralizer_x₂Q S)
  obtain ⟨u, hu₂, -, hu₁, -⟩ := D.exists_swap23 S
  have hu₁G : (u : G) * (x₁ : G) = (x₁ : G) * (u : G) := by
    have := congrArg Subtype.val hu₁
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  let uM : ↥(centralizer ({(x₁ : G)} : Set G)) :=
    ⟨(u : G), mem_centralizer_singleton_iff.2 hu₁G⟩
  have hconj : IsConj (D.x₂Q S) (D.x₃Q S) := by
    refine isConj_iff.2 ⟨QuotientGroup.mk uM, ?_⟩
    rw [LyData.x₂Q, LyData.x₃Q, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have := congrArg Subtype.val hu₂
    simpa [uM, LyData.x₂M, LyData.x₃M] using this
  have hc3 : Nat.card ↥(centralizer ({D.x₃Q S} : Set (CentQuot (x₁ : G)))) = 29160 := by
    rw [← card_centralizer_eq_of_isConj hconj]; exact hc2
  exact exists_mclFacts hnrm e hy3 hc2 hz3 hc3 (D.x₂Q_mul_x₃Q S)

theorem normQuotAut_surjective (D : LyData G t ρ) (hx3 : x₁ ^ 3 = 1) (hx : ρ x₁ = x1p) :
    Function.Surjective (normQuotAut : ↥(NormX (x₁ : G)) →* MulAut (CentQuot (x₁ : G))) := by
  obtain ⟨e⟩ := D.centQuot_mcl hx3 hx
  have hout : Nat.card (Outer (CentQuot (x₁ : G))) = 2 := outer_card_of_equiv_mcl e
  obtain ⟨hsimple, hnab, -⟩ := D.centQuot_facts hx3 hx
  have hcen := center_eq_bot_of_simple hsimple hnab
  have hinj := D.normQuotAutQuot_injective hx3 hx
  have hcard : Nat.card (MulAut (CentQuot (x₁ : G))) ≤ Nat.card (NormQuot (x₁ : G)) := by
    rw [card_mulAut_of_outer hcen hout, D.card_normQuot hx3 hx]
  have hbij := hinj.bijective_of_nat_card_le hcard
  intro σ
  obtain ⟨q, hq⟩ := hbij.2 σ
  induction q using QuotientGroup.induction_on with
  | H n => exact ⟨n, hq⟩

theorem exists_inverting_involution (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}
    (hF : McLFacts (CentQuot (x₁ : G)) (D.x₂Q S) (D.x₃Q S) R T A Y) :
    ∃ s : G, s * s = 1 ∧ s ∈ NormX (x₁ : G) ∧ s * (x₁ : G) * s⁻¹ = (x₁ : G)⁻¹ ∧
      ∀ a ∈ preimQ (x₁ : G) A, s * a * s⁻¹ = a⁻¹ := by
  obtain ⟨σ, hσ2, hσout, hσinv⟩ := hF.inverting
  obtain ⟨n, hn⟩ := D.normQuotAut_surjective S.pow₁ S.rho₁ σ
  have hx3G : (x₁ : G) ^ 3 = 1 := by
    have := congrArg Subtype.val S.pow₁
    simpa using this
  have hx1G : (x₁ : G) ≠ 1 := by
    intro h
    have : x₁ = 1 := Subtype.ext h
    have hρ := S.rho₁
    rw [this, map_one] at hρ
    exact (by decide : (1 : Perm (Fin 11)) ≠ x1p) hρ
  have hnC : (n : G) ∉ centralizer ({(x₁ : G)} : Set G) := by
    intro hc
    apply hσout
    have : σ = MulAut.conj (QuotientGroup.mk (⟨(n : G), hc⟩ :
        ↥(centralizer ({(x₁ : G)} : Set G))) : CentQuot (x₁ : G)) := by
      rw [← hn]
      ext q
      induction q using QuotientGroup.induction_on with
      | H m =>
        rw [normQuotAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
          ← QuotientGroup.mk_mul]
        rfl
    rw [this]
    exact ⟨_, rfl⟩
  have hninv : (n : G) * (x₁ : G) * (n : G)⁻¹ = (x₁ : G)⁻¹ := by
    rcases conj_eq_or_inv hx3G hx1G n.2 with h | h
    · exact absurd (mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h)) hnC
    · exact h
  have hnn : (n : G) * (n : G) = 1 := by
    have h1 : normQuotAut (n * n) = 1 := by
      rw [map_mul, hn, ← sq]
      rw [← hσ2]
      exact pow_orderOf_eq_one σ
    have h2 := D.mem_zpowers_of_normQuotAut_eq_one S.pow₁ S.rho₁ h1
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h2
    have hj' : (x₁ : G) ^ j = (n : G) * (n : G) := hj
    have hcomm : (n : G) * (x₁ : G) ^ j * (n : G)⁻¹ = (x₁ : G) ^ j := by
      rw [hj']
      group
    rw [← conj_zpow, hninv, inv_zpow] at hcomm
    have h3 : (x₁ : G) ^ (2 * j) = 1 := by
      have : (x₁ : G) ^ j * (x₁ : G) ^ j = 1 := by
        calc (x₁ : G) ^ j * (x₁ : G) ^ j = ((x₁ : G) ^ j)⁻¹ * (x₁ : G) ^ j := by rw [hcomm]
          _ = 1 := inv_mul_cancel _
      rw [two_mul, zpow_add]
      exact this
    have h4 := zpow_eq_one_of_zpow_two_mul hx3G hx1G h3
    rw [← hj', h4]
  refine ⟨(n : G), hnn, n.2, hninv, fun a ha => ?_⟩
  obtain ⟨hac, haA⟩ := mem_preimQ.1 ha
  have hmk : normQuotAut n (QuotientGroup.mk (⟨a, hac⟩ : ↥(centralizer ({(x₁ : G)} : Set G)))) =
      (QuotientGroup.mk (⟨a, hac⟩ : ↥(centralizer ({(x₁ : G)} : Set G))))⁻¹ := by
    rw [hn]
    exact hσinv _ haA
  rw [normQuotAut_mk, ← QuotientGroup.mk_inv, QuotientGroup.eq] at hmk
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmk
  have hk' : (x₁ : G) ^ k = ((n : G) * a * (n : G)⁻¹)⁻¹ * a⁻¹ := by
    have := congrArg Subtype.val hk
    simpa only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv, conjCent_apply] using this
  have h6 : ((n : G) * a * (n : G)⁻¹)⁻¹ = (x₁ : G) ^ k * a := by
    rw [hk']
    group
  have hk'' : (n : G) * a * (n : G)⁻¹ = a⁻¹ * (x₁ : G) ^ (-k) := by
    have := congrArg (fun z => z⁻¹) h6
    simp only [inv_inv, mul_inv_rev] at this
    rw [this, zpow_neg]
  exact inverts_of_inverts_mod hx3G hx1G hnn hninv (mem_centralizer_singleton_iff.1 hac) hk''

end LyData

end Cert

end CFSG.Sporadic.Recognition.LyonsSims

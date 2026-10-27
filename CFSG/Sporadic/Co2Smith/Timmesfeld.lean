module

public import CFSG.Sporadic.Co2Smith.Transport
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LargeExtraspecial.OfFStar

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem natCard_sp62 : Nat.card Sp62 = 1451520 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod]
  decide

variable {G : Type*} [Group G] [Finite G] {t : G}

theorem pCore_eq_fStar (h : TimmesfeldCo2Hyp G t) :
    CFSG.pCore 2 (centralizer ({t} : Set G)) = timmesfeldFStar (centralizer ({t} : Set G)) := by
  set H := centralizer ({t} : Set G)
  have hNn : (timmesfeldFStar H).Normal := CFSG.LargeExtraspecial.timmesfeldFStar_normal H
  refine le_antisymm ?_ (le_sSup ⟨hNn, h.extraspecial.1⟩)
  have hnil : Group.IsNilpotent (CFSG.pCore 2 H) := CFSG.pCore_isNilpotent
  exact (le_sSup ⟨CFSG.pCore_normal, hnil⟩ : CFSG.pCore 2 H ≤ timmesfeldFitting H).trans
    le_sup_left

omit [Finite G] in
theorem selfInCentralizer_comm (x : centralizer ({t} : Set G)) :
    x * selfInCentralizer t = selfInCentralizer t * x := by
  apply Subtype.ext
  exact (mem_centralizer_singleton_iff.mp x.2)

theorem natCard_centralizer (h : TimmesfeldCo2Hyp G t) :
    Nat.card (centralizer ({t} : Set G)) = 2 ^ 9 * 1451520 := by
  obtain ⟨φ, hφ, hker⟩ := h.quotient
  rw [← natCard_sp62, ← h.card, ← hker,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, mul_comm]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker

theorem smithLocal_of_timmesfeld (h : TimmesfeldCo2Hyp G t) :
    SmithLocal (centralizer ({t} : Set G)) where
  card_pCore := by rw [pCore_eq_fStar h]; exact h.card
  pCore_noncomm := by
    by_contra hall
    push Not at hall
    set N := timmesfeldFStar (centralizer ({t} : Set G))
    have htop : center N = ⊤ := by
      refine (Subgroup.eq_top_iff' _).mpr fun a => mem_center_iff.mpr fun b => ?_
      apply Subtype.ext
      have ha : (a : centralizer ({t} : Set G)) ∈ CFSG.pCore 2 _ := by
        rw [pCore_eq_fStar h]; exact a.2
      have hb : (b : centralizer ({t} : Set G)) ∈ CFSG.pCore 2 _ := by
        rw [pCore_eq_fStar h]; exact b.2
      exact hall _ hb _ ha
    have h2 := h.extraspecial.2.2.2
    rw [htop, Subgroup.card_top, h.card] at h2
    norm_num at h2
  quotient_equiv := by
    obtain ⟨φ, hφ, hker⟩ := h.quotient
    exact ⟨(QuotientGroup.quotientMulEquivOfEq ((pCore_eq_fStar h).trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩
  sylow_five := by
    intro P x hx hxP y _
    obtain ⟨g, hg5, hgfix⟩ := h.spin
    have hcard : Nat.card (zpowers g) = 5 := by rw [Nat.card_zpowers, hg5]
    have hpg : IsPGroup 5 (zpowers g) := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
    have hidx : ¬ 5 ∣ (zpowers g).index := by
      have hm := (zpowers g).index_mul_card
      rw [hcard, natCard_centralizer h] at hm
      omega
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set G))
      (hpg.toSylow hidx) P
    have hkg : k * g * k⁻¹ ∈ P := by
      rw [← hk]
      change k * g * k⁻¹ ∈ ((k • hpg.toSylow hidx : Sylow 5 _) : Subgroup _)
      rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe]
      have hmem : MulAut.conj k • g ∈ MulAut.conj k • (zpowers g) :=
        Subgroup.smul_mem_pointwise_smul g (MulAut.conj k) (zpowers g) (mem_zpowers g)
      simpa [MulAut.smul_def] using hmem
    have hc := hxP _ hkg
    have hy0 : k⁻¹ * x * k ∈ timmesfeldFStar (centralizer ({t} : Set G)) := by
      rw [← pCore_eq_fStar h]
      simpa using (CFSG.pCore_normal (p := 2) (G := centralizer ({t} : Set G))).conj_mem x hx k⁻¹
    have hfix : g * (k⁻¹ * x * k) * g⁻¹ = k⁻¹ * x * k := by
      have hc' : g * (k⁻¹ * x * k) = (k⁻¹ * x * k) * g := by
        calc g * (k⁻¹ * x * k) = k⁻¹ * ((k * g * k⁻¹) * x) * k := by group
          _ = k⁻¹ * (x * (k * g * k⁻¹)) * k := by rw [hc]
          _ = (k⁻¹ * x * k) * g := by group
      rw [hc', mul_inv_cancel_right]
    rcases hgfix _ hy0 (Or.inl hfix) with h1 | h1
    · have : x = 1 := by
        calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
          _ = 1 := by rw [h1]; group
      rw [this, one_mul, mul_one]
    · have : x = selfInCentralizer t := by
        calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
          _ = k * selfInCentralizer t * k⁻¹ := by rw [h1]
          _ = selfInCentralizer t := by rw [selfInCentralizer_comm k]; group
      rw [this]
      exact (selfInCentralizer_comm y).symm

theorem smithHyp_of_timmesfeld (h : TimmesfeldCo2Hyp G t) : SmithHyp G t :=
  haveI := h.simple
  smithHyp_of_simple h.orderOf_eq h.noncomm (smithLocal_of_timmesfeld h)

end CFSG.Sporadic.Co2Smith

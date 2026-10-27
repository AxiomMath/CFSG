module

public import CFSG.RankThree.GF2n.Tim79a34QEBranches
public import CFSG.RankThree.GF2n.Tim79a34GammaSteps
public import CFSG.RankThree.GF2n.Tim79a34C8Base
public import CFSG.RankThree.GF2n.Tim79a34PResidual
public import CFSG.RankThree.GF2n.Tim79a34QESmith
public import CFSG.RankThree.GF2n.Tim79a34QEOrder
public import CFSG.RankThree.GF2n.Tim79a34SpOrder

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

theorem ntQEInStatement_holds : NTQEInStatement := by
  intro G _ _ M V Q P H hH hZ hn hrel hQN
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  have hIW : Sec34IWStatement :=
    sec34IW_holds hN spRadFactsStatement_holds commPairingStatement_holds
  have h11a : Lemma11aStatement := lemma11a_holds spRadFactsStatement_holds
  have h11b : Lemma11bStatement := lemma11b_holds hN h11a spRadFactsStatement_holds
  have h12 : Lemma12Statement := lemma12Statement_holds
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hZ
  obtain ⟨n, Φ, ψ, -, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hZ
  have hNat : NatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨n', hn'3, ⟨e⟩⟩ := hn
  have hnn : n = n' := by
    let e2 : Xbar V H ≃* XbarZ V H := MulEquiv.ofBijective (projZ V H) (iw_projZ_bijective hZ)
    exact statedSp_gf2_rank_eq (Φ.trans (e2.trans e.symm))
  have hn3 : 3 ≤ n := by omega
  obtain ⟨-, -, -, hPcard⟩ := h11a G M V Q P H hH hZ hcP Φ ψ hNat a T ha hT hTV
  obtain ⟨hAP, -, hPcent⟩ := h11b G M V Q P H hH hZ hcP
  have hcentM : Subgroup.centralizer ({c8W ψ a} : Set G) = M :=
    (h12 G M V Q P H hH hZ Φ ψ hNat a T ha hT hTV).1
  set aG : G := c8W ψ a with haGdef
  have hMQ : Q = inSubgroup (pCore 2) M := hc.hQ
  have hMN : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hMQ]
    exact (inSubgroup_pCore_two M).2.2
  have hQM : Q ≤ M := by
    rw [hMQ]
    exact (inSubgroup_pCore_two M).2.1
  have hQ2 : IsPGroup 2 Q := by
    rw [hMQ]
    exact (inSubgroup_pCore_two M).1
  have haV : aG ∈ V := hpoint a T ha hT hTV
  have haG1 : aG ≠ 1 := fun h => ha (c8W_inj ψ (h.trans (c8W_zero ψ).symm))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haG2 : orderOf aG = 2 :=
    orderOf_eq_prime (hc.elemAb.2 _ haV) haG1
  have hA2 : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  have hAmem : aG ∈ V ⊓ wOf V H := Subgroup.mem_inf.mpr ⟨haV, c8W_mem ψ a⟩
  have hAc : ∀ m ∈ M, ∀ x ∈ V ⊓ wOf V H, m * x * m⁻¹ = x := by
    intro m hm x hx
    rcases l12_two_elt hA2 hAmem haG1 x hx with rfl | rfl
    · group
    · have hmc : m ∈ Subgroup.centralizer ({aG} : Set G) := by
        rw [hcentM]
        exact hm
      have := Subgroup.mem_centralizer_iff.mp hmc aG (Set.mem_singleton _)
      rw [← this]
      group
  have hV4 : Nat.card ↥V = 4 := by
    have h := twb_card_barOf_mul (V := V) (H := H) (K := V) hc.V_le_H
    have e1 : Nat.card ↥(barOf V H V) = 2 := hH.q_two
    have e2 : Nat.card ↥(V ⊓ wOf V H) = 2 := by rw [hH.module]; exact hH.q_two
    rw [e1, e2] at h
    omega
  obtain ⟨C, hCQ, hPCQ, hPC, -, -, -⟩ := Gamma.sec34GammaStatement_holds G M V Q P H hH hZ
  have hPQ : P ≤ Q := hc.P_le_Q
  have hAn : ∀ q ∈ Q, ∀ x ∈ V ⊓ wOf V H, q * x * q⁻¹ ∈ V ⊓ wOf V H := fun q hq x hx => by
    rw [hAc q (hQM hq) x hx]
    exact hx
  have hPA : P ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) :=
    l12_le_normalizer (fun k hk v hv => hAc k (hQM (hPQ hk)) v hv)
  have hCA : C ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) :=
    l12_le_normalizer (fun k hk v hv => hAc k (hQM (hCQ hk)) v hv)
  have hPP : ∀ p ∈ P, ∀ x ∈ P, ⁅p, x⁆ ∈ V ⊓ wOf V H := fun p hp x hx => by
    rw [← hAP]
    exact Subgroup.commutator_mem_commutator hp hx
  have hPQA : ∀ x ∈ Q, ∀ p ∈ P, ⁅p, x⁆ ∈ V ⊓ wOf V H := by
    rw [← hPCQ]
    exact l12_sup_normalizes hPA hCA hPP hPC
  have hVn : ∀ q ∈ M, ∀ v ∈ V, q * v * q⁻¹ ∈ V := by
    intro q hq v hv
    have hgN : q ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hq
    exact (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
  have hCV : ∀ q ∈ Q, (∀ v ∈ V, q * v = v * q) → q ∈ P := by
    intro q hq hqv
    rw [hc.hP]
    exact Subgroup.mem_inf.mpr ⟨hq, Subgroup.mem_centralizer_iff.mpr fun v hv => (hqv v hv).symm⟩
  have hCP : ∀ q ∈ Q, (∀ p ∈ P, q * p = p * q) → q ∈ V := by
    intro q hq hqp
    rw [← hPcent]
    exact Subgroup.mem_centralizer_iff.mpr fun p hp => (hqp p hp).symm
  obtain ⟨hQQ, hQcen⟩ := qe_derived_center hPQ hrel hA2 hAP
    (fun q hq x hx => hAn q hq x hx) hPQA inf_le_left hc.V_le_P hV4 hCV hCP
  have hext : IsExtraspecial2 Q := ⟨hQ2, by rw [hQQ, hQcen], by rw [hQQ]; exact hA2⟩
  have hQG : Q ≤ pResidual 2 G := by
    intro q hq
    simp only [pResidual, Subgroup.mem_iInf]
    intro N hN hpow
    haveI := hN
    refine hQN N ?_ hq
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := hpow g
    exact ⟨k, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hk⟩
  have hfit := Tim78.inf_centralizer_le_of_generalizedFitting_eq hc.fitting
  rw [← hMQ] at hfit
  have hw : Nat.card ↥Q = 2 ^ (1 + 2 * (2 * n - 1)) := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := Q)
    rw [hrel, inf_eq_left.mpr hPQ, hPcard] at h
    rw [← h, ← pow_succ']
    congr 1
    omega
  haveI : (pResidual 2 G).Normal := Quasithin.G6.pResidual_normal_aux 2
  refine no_normal_four_in_residual (pResidual 2 G)
    (fun N _ hq => pResidual_two_idem G N hq) haG2 hQG haV hc.V_le_Q hV4
    (by rw [hcentM]; exact hQM)
    (fun m hm q hq => by
      rw [hcentM] at hm
      exact (Subgroup.mem_normalizer_iff.mp (hMN hm) q).mp hq)
    (fun m hm v hv => by
      rw [hcentM] at hm
      exact hVn m hm v hv)
    hext
    (fun m hm hcomm => by
      rw [hcentM] at hm
      exact hfit (Subgroup.mem_inf.mpr ⟨hm, Subgroup.mem_centralizer_iff.mpr
        fun q hq => (hcomm q hq).symm⟩))
    (fun R hR hRn hR2 => by
      rw [hcentM] at hR hRn
      rw [hMQ]
      exact le_pCore_of_normal_inf hR hRn hR2)
    hw (by omega)

end CFSG.RankThree.GF2n.Tim79a

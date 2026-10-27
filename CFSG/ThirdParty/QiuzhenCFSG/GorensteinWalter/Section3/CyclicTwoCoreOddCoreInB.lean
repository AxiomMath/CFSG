module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenStructure
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The odd core of the maximal overgroup lies in `B = C_U(S)`

In the cyclic first-case A₇ layer model the whole maximal overgroup `M`
has `A₇` as its odd-core quotient.  The image of the component layer is a
nontrivial normal subgroup of that quotient, hence all of `A₇`.  The
`2`-Sylow subgroup `S` therefore has order `8`, and a `2`-Sylow subgroup of
the component layer has the same order; by Sylow conjugacy in `M` this puts
`S` inside the component layer.  The odd core `O(M)` then centralizes
`S` (through the layer) and lies in `B = C_U(S)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A₇ layer model, the Sylow `2`-subgroup `S` of the maximal
overgroup is contained in the component layer and has order `8`. -/
public theorem firstCase_cyclic_a7_S_layer_data
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7))) :
    (c.S : Subgroup G) ≤ componentLayerOf M ∧
      Nat.card (c.S : Subgroup G) = 8 := by
  classical
  let O0 : Subgroup M := pPrimeCore 2 M
  let E : Subgroup G := componentLayerOf M
  let E0 : Subgroup M := E.subgroupOf M
  let q : M →* M ⧸ O0 := QuotientGroup.mk' O0
  let Q := M ⧸ O0
  let Ebar : Subgroup Q := E0.map q
  let : O0.Normal := pPrimeCore_normal
  have hE_le_M : E ≤ M := (componentLayerOf_isNormalIn M).1
  have hE0_normal : E0.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := M) (N := E)
      (le_normalizer_of_isNormalIn (componentLayerOf_isNormalIn M))
  have : E0.Normal := hE0_normal
  have hEbar_normal : Ebar.Normal := QuotientGroup.map_normal (G := M) O0 E0
  have hEbar_ne : Ebar ≠ ⊥ := by
    intro hbot
    have hE0_le_ker : E0 ≤ q.ker := (Subgroup.map_eq_bot_iff E0).mp hbot
    have htM : c.t ∈ M := hSM (fd.V2_le_S fd.t_mem_V2)
    let tM : M := ⟨c.t, htM⟩
    have htE0 : tM ∈ E0 := Subgroup.mem_subgroupOf.mpr (hV2 fd.t_mem_V2)
    have htO0 : tM ∈ O0 := by
      have htker : tM ∈ q.ker := hE0_le_ker htE0
      simpa [q, QuotientGroup.ker_mk'] using htker
    have hdvd2 : 2 ∣ Nat.card O0 := by
      have hdvd : orderOf tM ∣ Nat.card O0 :=
        Subgroup.orderOf_dvd_natCard O0 htO0
      have hord2 : orderOf tM = 2 := by
        apply orderOf_eq_prime
        · apply Subtype.ext
          exact c.t_involution.2
        · intro h1
          exact c.t_involution.1 (congrArg Subtype.val h1)
      rwa [hord2] at hdvd
    have hodd : Odd (Nat.card O0) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M))
    exact hodd.not_two_dvd_nat hdvd2
  obtain ⟨eM⟩ := firstCase_cyclic_m_quotient_a7_of_layer_a7
    hmin M hMmax hA7
  let EA : Subgroup (alternatingGroup (Fin 7)) := Ebar.map eM.toMonoidHom
  have hEA_normal : EA.Normal :=
    hEbar_normal.map eM.toMonoidHom eM.surjective
  have hEA_ne : EA ≠ ⊥ := by
    intro hbot
    exact hEbar_ne ((Subgroup.map_eq_bot_iff_of_injective
      (H := Ebar) (f := eM.toMonoidHom) eM.injective).mp hbot)
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
  have hEA_top : EA = ⊤ :=
    (@IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ EA hEA_normal).resolve_left hEA_ne
  have hEbar_top : Ebar = ⊤ := by
    apply (Subgroup.map_injective (f := eM.toMonoidHom) eM.injective)
    simpa [EA] using hEA_top
  let SM : Sylow 2 M := c.S.subtype hSM
  let SQ : Sylow 2 Q :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective O0) SM
  have hqker : q.ker = O0 := QuotientGroup.ker_mk' O0
  have hSMker : (SM : Subgroup M) ⊓ O0 = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    rw [Subgroup.mem_bot]
    have hxS : x ∈ (SM : Subgroup M) := (Subgroup.mem_inf.mp hx).1
    have hxO : x ∈ O0 := (Subgroup.mem_inf.mp hx).2
    rcases SM.isPGroup'.exists_card_eq with ⟨n, hn⟩
    have hdvd : orderOf x ∣ 2 ^ n := by
      have hd : orderOf x ∣ Nat.card (SM : Subgroup M) :=
        Subgroup.orderOf_dvd_natCard (SM : Subgroup M) hxS
      rwa [hn] at hd
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat
        (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M)))
        (Subgroup.orderOf_dvd_natCard O0 hxO)
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨k, hk, hxeq⟩
    have hk0 : k = 0 := by
      by_contra hkne
      have h2dvd : 2 ∣ orderOf x := by
        rw [hxeq]
        exact ⟨2 ^ (k - 1), by
          rw [show k = (k - 1) + 1 by omega, pow_succ']
          rfl⟩
      exact hodd.not_two_dvd_nat h2dvd
    exact orderOf_eq_one_iff.mp (by simpa [hk0] using hxeq)
  have hcardSQ : Nat.card (SQ : Subgroup Q) = 8 := by
    let SA : Sylow 2 (alternatingGroup (Fin 7)) := a7SylowD8
    have hcardA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup]
      norm_num
    have hcardSA : Nat.card (SA : Subgroup (alternatingGroup (Fin 7))) = 8 := by
      rcases hasDihedralSylowTwo_alternatingGroupSeven SA with ⟨m, hm, ⟨eD⟩⟩
      have hcardSApow :
          Nat.card (SA : Subgroup (alternatingGroup (Fin 7))) = 2 ^ 3 := by
        rw [Sylow.card_eq_multiplicity SA, hcardA]
        rw [show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num]
        rw [Nat.factorization_mul (by norm_num) (by norm_num)]
        rw [Nat.factorization_pow]
        simp [Nat.prime_two.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (315 : ℕ))]
      have hcardSD : Nat.card (SA : Subgroup (alternatingGroup (Fin 7))) =
          2 * 2 ^ m := by
        rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
      have hpow : 2 ^ 3 = 2 ^ (m + 1) := by
        rw [← hcardSApow, hcardSD]
        rw [pow_succ, mul_comm]
      have hm2 : m = 2 := by
        have h3 : 3 = m + 1 :=
          Nat.pow_right_injective (by norm_num : (1 : ℕ) < 2) hpow
        omega
      rw [hcardSApow]
      norm_num
    let SAQ : Sylow 2 Q :=
      Sylow.mapSurjective (f := eM.symm.toMonoidHom) eM.symm.surjective SA
    have hcardSAQ : Nat.card (SAQ : Subgroup Q) = 8 := by
      have hmap : (SAQ : Subgroup Q) = SA.map eM.symm.toMonoidHom := by
        exact (Sylow.coe_mapSurjective (f := eM.symm.toMonoidHom)
          eM.symm.surjective SA).symm
      have hcardmap : Nat.card (SA.map eM.symm.toMonoidHom) = 8 := by
        have h := Subgroup.card_map_of_injective (K := SA)
          (f := eM.symm.toMonoidHom) eM.symm.injective
        rwa [hcardSA] at h
      rw [hmap]
      exact hcardmap
    have h := Nat.card_congr (Sylow.equiv SQ SAQ).toEquiv
    rwa [hcardSAQ] at h
  have hcardSM : Nat.card (SM : Subgroup M) = 8 := by
    have hformula := card_map_eq_card_mul_card_ker q (SM : Subgroup M)
    have hmap : (SM : Subgroup M).map q = (SQ : Subgroup Q) := by
      exact (Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective O0) SM).symm
    rw [hformula, hmap, hqker, hSMker, hcardSQ]
    simp
  let qE : E0 →* Q := q.comp E0.subtype
  have hqE_surj : Function.Surjective qE := by
    intro y
    have hyEbar : y ∈ Ebar := by
      rw [hEbar_top]
      trivial
    rcases Subgroup.mem_map.mp hyEbar with ⟨e0, he0, hqeq⟩
    refine ⟨⟨e0, he0⟩, ?_⟩
    simpa [qE] using hqeq
  have hqE_ker : qE.ker = (E0 ⊓ O0).subgroupOf E0 := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxq : q (E0.subtype x) = 1 := by simpa [qE] using hx
      have hxO : E0.subtype x ∈ O0 :=
        (QuotientGroup.eq_one_iff (N := O0) (E0.subtype x)).mp hxq
      exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hxO⟩
    · intro hx
      rw [MonoidHom.mem_ker]
      have hxO : E0.subtype x ∈ O0 := (Subgroup.mem_inf.mp
        (Subgroup.mem_subgroupOf.mp hx)).2
      have hxq : q (E0.subtype x) = 1 :=
        (QuotientGroup.eq_one_iff (N := O0) (E0.subtype x)).mpr hxO
      simpa [qE] using hxq
  let PE : Sylow 2 E0 := Classical.choice Sylow.nonempty
  let PEQ : Sylow 2 Q := Sylow.mapSurjective hqE_surj PE
  have hcardPEQ : Nat.card (PEQ : Subgroup Q) = 8 := by
    have h := Nat.card_congr (Sylow.equiv PEQ SQ).toEquiv
    rwa [hcardSQ] at h
  have hPEker : (PE : Subgroup E0) ⊓ qE.ker = ⊥ := by
    rw [hqE_ker]
    apply le_bot_iff.mp
    intro x hx
    rw [Subgroup.mem_bot]
    have hxP : x ∈ (PE : Subgroup E0) := (Subgroup.mem_inf.mp hx).1
    have hxK : x ∈ (E0 ⊓ O0).subgroupOf E0 := (Subgroup.mem_inf.mp hx).2
    have hxO : (x : M) ∈ O0 :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hxK)).2
    rcases PE.isPGroup'.exists_card_eq with ⟨n, hn⟩
    have hdvd : orderOf x ∣ 2 ^ n := by
      have hd : orderOf x ∣ Nat.card (PE : Subgroup E0) :=
        Subgroup.orderOf_dvd_natCard (PE : Subgroup E0) hxP
      rwa [hn] at hd
    have hordM : orderOf (x : M) = orderOf x :=
      orderOf_injective E0.subtype E0.subtype_injective x
    have hodd : Odd (orderOf (x : M)) :=
      Odd.of_dvd_nat
        (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M)))
        (Subgroup.orderOf_dvd_natCard O0 hxO)
    have hdvdM : orderOf (x : M) ∣ 2 ^ n := by
      rwa [← hordM] at hdvd
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvdM with ⟨k, hk, hxeq⟩
    have hk0 : k = 0 := by
      by_contra hkne
      have h2dvd : 2 ∣ orderOf (x : M) := by
        rw [hxeq]
        exact ⟨2 ^ (k - 1), by
          rw [show k = (k - 1) + 1 by omega, pow_succ']
          rfl⟩
      exact hodd.not_two_dvd_nat h2dvd
    have hxeqM : orderOf (x : M) = 1 := by simpa [hk0] using hxeq
    exact orderOf_eq_one_iff.mp (by rwa [hordM] at hxeqM)
  have hcardPE : Nat.card (PE : Subgroup E0) = 8 := by
    have hformula := card_map_eq_card_mul_card_ker qE (PE : Subgroup E0)
    have hmap : (PE : Subgroup E0).map qE = (PEQ : Subgroup Q) := by
      exact (Sylow.coe_mapSurjective hqE_surj PE).symm
    rw [hformula, hmap, hPEker, hcardPEQ]
    simp
  let PEM : Subgroup M := (PE : Subgroup E0).map E0.subtype
  have hcardPEM : Nat.card PEM = 8 := by
    have h := Subgroup.card_map_of_injective (K := (PE : Subgroup E0))
      (f := E0.subtype) E0.subtype_injective
    rwa [hcardPE] at h
  have hPEM_p : IsPGroup 2 PEM :=
    (PE.isPGroup' : IsPGroup 2 (PE : Subgroup E0)).map E0.subtype
  obtain ⟨QM, hQMle⟩ := IsPGroup.exists_le_sylow (p := 2) hPEM_p
  have hPEM_eq_QM : PEM = (QM : Subgroup M) := by
    apply le_antisymm hQMle
    intro x hx
    have hxP : x ∈ (QM : Subgroup M) := hx
    have hdvd : Nat.card (QM : Subgroup M) = 8 := by
      have h := Nat.card_congr (Sylow.equiv QM SM).toEquiv
      rwa [hcardSM] at h
    have hcardPEMle : Nat.card PEM = Nat.card (QM : Subgroup M) := by
      rw [hcardPEM, hdvd]
    exact (Subgroup.eq_of_le_of_card_ge hQMle
      (Nat.le_of_eq hcardPEMle.symm)).symm ▸ hxP
  obtain ⟨m, hm⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq M (Sylow 2 M)
      inferInstance inferInstance QM SM
  have hSM_le_E0 : (SM : Subgroup M) ≤ E0 := by
    intro x hx
    rw [← hm] at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyQM, hxy⟩
    have hyPEM : y ∈ PEM := by rwa [hPEM_eq_QM]
    rcases Subgroup.mem_map.mp hyPEM with ⟨e, he, hye⟩
    have hconj : (m : M) * (e : M) * (m : M)⁻¹ ∈ E0 :=
      hE0_normal.conj_mem (e : M) e.2 m
    have hxeq : x = (m : M) * (e : M) * (m : M)⁻¹ := by
      have hxy' : x = (m : M) * y * (m : M)⁻¹ := by
        simpa [MulAut.conj_apply] using hxy.symm
      have hye' : (e : M) = y := by simpa using hye
      rw [hxy', hye']
    exact hxeq ▸ hconj
  constructor
  · intro s hs
    have hsM : (⟨s, hSM hs⟩ : M) ∈ (SM : Subgroup M) := by
      change s ∈ (c.S : Subgroup G)
      exact hs
    have hsE0 : (⟨s, hSM hs⟩ : M) ∈ E0 := hSM_le_E0 hsM
    exact Subgroup.mem_subgroupOf.mp hsE0
  · have hSMco : (SM : Subgroup M) = (c.S : Subgroup G).subgroupOf M :=
      Sylow.coe_subtype c.S hSM
    have hcardS' : Nat.card ((c.S : Subgroup G).subgroupOf M) =
        Nat.card (c.S : Subgroup G) := by
      have e := Subgroup.subgroupOfEquivOfLe (H := (c.S : Subgroup G)) (K := M) hSM
      exact Nat.card_congr e.toEquiv
    rwa [hSMco, hcardS'] at hcardSM

/-- In the cyclic first-case A₇ layer model, the odd core of the maximal
overgroup `M` lies in `B = C_U(S)`. -/
public theorem firstCase_cyclic_oddCore_le_B_of_a7_layer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7))) :
    ((pPrimeCore 2 M).map M.subtype) ≤ od.d.bg.B := by
  classical
  let O0 : Subgroup M := pPrimeCore 2 M
  let O : Subgroup G := O0.map M.subtype
  let E : Subgroup G := componentLayerOf M
  have hSleE : (c.S : Subgroup G) ≤ E :=
    (firstCase_cyclic_a7_S_layer_data
      hmin c od M hMmax hSM fd hV2 hA7
    ).1
  have hOleM : O ≤ M := Subgroup.map_subtype_le (H := M) (pPrimeCore 2 M)
  have hOodd : Odd (Nat.card O) := by
    have hcard : Nat.card O = Nat.card O0 :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [hcard]
    exact Nat.coprime_two_left.mp
      (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have hOsolv : IsSolvable O := odd_order_theorem O hOodd
  have hOnorm : IsNormalIn O M := by
    refine ⟨hOleM, ?_⟩
    intro m hm o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨m, hm⟩ : M) * o0 * (⟨m, hm⟩ : M)⁻¹, ?_, rfl⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥M)).conj_mem
      o0 ho0 ⟨m, hm⟩
  have hE_norm_O : E ≤ Subgroup.normalizer (O : Set G) :=
    (componentLayerOf_isNormalIn M).1.trans (le_normalizer_of_isNormalIn hOnorm)
  have hcomm : ⁅E, O⁆ = ⊥ :=
    componentLayerOf_centralizes_solvable_of_le_normalizer
      M O hOleM hOsolv hE_norm_O
  have hOcentE : O ≤ Subgroup.centralizer (E : Set G) := by
    have hcomm' : ⁅O, E⁆ = ⊥ := by
      simpa [Subgroup.commutator_comm] using hcomm
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := O) (H₂ := E)).mp hcomm'
  have hOcentS : O ≤ Subgroup.centralizer ((c.S : Subgroup G) : Set G) :=
    hOcentE.trans (Subgroup.centralizer_le
      (show (c.S : Set G) ⊆ (E : Set G) from hSleE))
  have hOleH : O ≤ od.d.bg.H := by
    intro o ho
    have ho_cent_S : o ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G) :=
      hOcentS ho
    have ho_cent_t : o ∈ Subgroup.centralizer ({c.t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp ho_cent_S)
          c.t (c.S0_le_S c.t_mem_S0)).symm
    rw [od.d.H_eq, c.H_eq_centralizer]
    exact ho_cent_t
  have hOcentSbg : O ≤
      Subgroup.centralizer ((od.d.bg.S : Subgroup G) : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have ho_cent_S : o ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G) :=
      hOcentS ho
    exact (Subgroup.mem_centralizer_iff.mp ho_cent_S) s
      (by simpa [od.d.S_eq] using hs)
  exact oddCore_le_centralizer_U_of_H_eq_US
    od.d.bg.U od.d.bg.S od.d.bg.H od.d.bg.B O
    od.d.bg.H_eq_US (bg_U_normal_in_H od.d.bg) od.d.bg.S.isPGroup'
    (BenderGlauberman.S_le_H od.d.bg)
    (B_eq_centralizer_U od.d.bg) hOleH hOodd hOcentSbg

end CFSG.GorensteinWalter

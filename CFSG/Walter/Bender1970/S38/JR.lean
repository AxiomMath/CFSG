module

public import CFSG.Walter.Bender1970.S38.OddCore
public import CFSG.Walter.Bender1970.S3.PGroupFStar
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Adapters.GeneralizedFitting
public import CFSG.Walter.Bender1970.S38.Center

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_generalizedFitting_le (H : Subgroup G) :
    H ⊓ Subgroup.centralizer (generalizedFittingSubgroupOf H : Set G) ≤
      generalizedFittingSubgroupOf H := by
  rintro x ⟨hxH, hxC⟩
  rw [← generalizedFittingSubgroupOf_subgroup_top_eq H]
  refine ⟨⟨x, hxH⟩, CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  have hy' : (y : G) ∈ generalizedFittingSubgroupOf H := by
    rw [← generalizedFittingSubgroupOf_subgroup_top_eq H]
    exact ⟨y, hy, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp hxC) y hy'

omit [Finite G] in
theorem jr_data_conj {w : G} {L : Subgroup G} {P : Type*} [Group P]
    (hco : IsCoatom (Subgroup.centralizer ({w} : Set G)))
    (hLC : L ≤ Subgroup.centralizer ({w} : Set G))
    (hLn : (L.subgroupOf (Subgroup.centralizer ({w} : Set G))).Normal) (e : L ≃* P)
    (hCL : Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers w) (g : G) :
    IsCoatom (Subgroup.centralizer ({g * w * g⁻¹} : Set G)) ∧
      L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({g * w * g⁻¹} : Set G) ∧
      ((L.map (MulAut.conj g).toMonoidHom).subgroupOf
        (Subgroup.centralizer ({g * w * g⁻¹} : Set G))).Normal ∧
      Nonempty (L.map (MulAut.conj g).toMonoidHom ≃* P) ∧
      Subgroup.centralizer ({g * w * g⁻¹} : Set G) ⊓
        Subgroup.centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
        Subgroup.zpowers (g * w * g⁻¹) := by
  set c := MulAut.conj g with hc
  have hC : Subgroup.centralizer ({g * w * g⁻¹} : Set G) =
      (Subgroup.centralizer ({w} : Set G)).map c.toMonoidHom :=
    (map_conj_centralizer_singleton g w).symm
  rw [hC]
  refine ⟨isCoatom_map_conj g hco, Subgroup.map_mono hLC, ?_,
    ⟨(L.equivMapOfInjective c.toMonoidHom c.injective).symm.trans e⟩, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hLC)]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxN := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mp hLn hx
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨x * z * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN z).mp hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    · rintro ⟨z, hz, hzeq⟩
      refine ⟨x⁻¹ * z * x, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) z).mp hz
        simpa using this
      · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] at hzeq ⊢
        rw [hzeq]
        group
  · have h1 : ((L.map c.toMonoidHom : Subgroup G) : Set G) = c '' (L : Set G) := by
      rw [Subgroup.coe_map, MulEquiv.coe_toMonoidHom]
    rw [h1, ← map_centralizer_mulEquiv, ← Subgroup.map_inf_eq _ _ c.toMonoidHom c.injective, hCL,
      MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hc, MulAut.conj_apply]

namespace BenderCounterexample

variable (hG : BenderCounterexample G)
include hG

theorem false_of_card_eq_two
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K H)
    (hFstar : ∀ s : G, orderOf s = 2 → ∀ M ∈ benderM s, s ∈ generalizedFittingSubgroupOf M)
    (hM : ∀ s ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), orderOf s = 2 →
      benderM s = {H})
    (hN : ¬ Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H)
    (hW2 : Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) = 2)
    (hQ4 : Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) = 4) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply hG.not_isTypeJR
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hHA := hG.isAStar_of_isCoatom hH.1
  have hTab := hG.hasAbelianSylowTwo T
  have hKQ := hG.bender38Component' hH T htT hK
  have hWne := hG.centralizer_inf_ne_bot ht hH T htT hK
  set W := (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) with hWdef
  set Q := (T : Subgroup G) ⊓ K with hQdef
  have hWcyc : IsCyclic W := isCyclic_of_prime_card hW2
  have : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
  obtain ⟨⟨w, hwW⟩, hw1⟩ := exists_ne (1 : W)
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hw2 : orderOf w = 2 := by
    have h1 : orderOf (⟨w, hwW⟩ : W) ∣ 2 := hW2 ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1'
    · exact h
  have hWz : W = Subgroup.zpowers w := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hwW) ?_
    rw [hW2, Nat.card_zpowers, hw2]
  have hMw := hM w hwW hw2
  have hwF := hFstar w hw2 H (by rw [hMw]; rfl)
  have hwZ := mem_center_of_isCyclic hHA hK T hTH hTab hWcyc hwW hw2 hwF
  obtain ⟨hHw, -⟩ := hG.centralizer_eq_of_central hH.1 hw1' hwZ
  have hOodd : Odd (Nat.card (oddCoreOf H)) := odd_card_oddCoreOf H
  have hKO : ⁅K, oddCoreOf H⁆ = ⊥ :=
    isComponentOf_commutator_eq_bot_of_isSolvable hK (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd)
      (Subgroup.map_subtype_le _) (le_normalizer_of_isNormalIn (oddCoreOf_isNormalIn' H))
  have hTO : ∀ x ∈ (T : Subgroup G), ∀ o ∈ oddCoreOf H, x * o = o * x := by
    intro x hx o ho
    have hoH : o ∈ H := Subgroup.map_subtype_le _ ho
    obtain ⟨w', hw', v, hv, rfl⟩ := exists_mul_of_mem_sylow hHA hK T hTH hx
    have hw'o : w' * o = o * w' := by
      have hw'' : w' ∈ W := hw'
      rw [hWz] at hw''
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw''
      have h1 : o * w * o⁻¹ = w := hwZ o hoH
      have h2 : Commute o w := by
        show o * w = w * o
        calc o * w = o * w * o⁻¹ * o := by group
          _ = w * o := by rw [h1]
      exact (h2.zpow_right k).eq.symm
    have hvo : v * o = o * v := by
      have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKO) hv.2
      exact ((Subgroup.mem_centralizer_iff.mp h1) o ho).symm
    calc w' * v * o = w' * (o * v) := by rw [mul_assoc, hvo]
      _ = o * (w' * v) := by rw [← mul_assoc, hw'o, mul_assoc]
  have hO := hG.oddCoreOf_eq_bot hH.1 hw2 hHw T hwW.1 hTO hN
  have hWQ : Nat.card W ≤ Nat.card Q := by rw [hW2, hQ4]; norm_num
  have hKN := le_normalizer_of_card_le hHA hK T hTH hTab hWne hWQ
  have hKnH : IsNormalIn K H := ⟨hK.1, fun h hh k hk => (Subgroup.mem_normalizer_iff.mp
    (hKN hh) k).mp hk⟩
  have hZK : Subgroup.center K = ⊥ := by
    set Z : Subgroup G := (Subgroup.center K).map K.subtype with hZ
    have hZn : IsNormalIn Z H := map_characteristic_isNormalIn_of_isNormalIn _ inferInstance hKnH
    have hZodd : Odd (Nat.card Z) := by
      rw [hZ, Subgroup.card_map_of_injective K.subtype_injective]
      exact hKQ.odd_center
    have hZO : Z ≤ oddCoreOf H := by
      have h1 : Z.subgroupOf H ≤ pPrimeCore 2 H := by
        apply le_sSup
        refine ⟨⟨fun n hn h => ?_⟩, ?_⟩
        · rw [Subgroup.mem_subgroupOf] at hn ⊢
          exact hZn.2 h h.2 n hn
        · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZn.1).toEquiv]
          exact Nat.coprime_two_left.mpr hZodd
      intro z hz
      exact ⟨⟨z, hZn.1 hz⟩, h1 hz, rfl⟩
    rw [hO, le_bot_iff, hZ, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hZO
    exact hZO
  obtain ⟨p, f, hp, hpodd, hf, h5, ⟨e⟩⟩ := hKQ.psl hQ4
  have eK : K ≃* PSL(2, GaloisField p f) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZK).symm).trans e
  have hFH : CFSG.fittingSubgroupOf H ≤ Subgroup.zpowers w := by
    rw [(show CFSG.fittingSubgroupOf H = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf H)]
    refine iSup_le fun q => ?_
    have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases hq2 : (q : ℕ) = 2
    · rw [hq2, ← hWz]
      exact qCoreOf_two_le hK T hTH
    · have : Fact (q : ℕ).Prime := ⟨hq⟩
      have h1 : CFSG.pCore (q : ℕ) H ≤ pPrimeCore 2 H := by
        apply le_sSup
        refine ⟨CFSG.pCore_normal, ?_⟩
        obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := (q : ℕ)) (G := H)).exists_card_eq
        rw [hj]
        exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hyO : (y : G) ∈ oddCoreOf H := ⟨y, h1 hy, rfl⟩
      rw [hO, Subgroup.mem_bot] at hyO
      show (y : G) ∈ _
      rw [hyO]
      exact Subgroup.one_mem _
  have hEK := componentLayerOf_le_of_isCyclic hHA hK T hTH hTab hWcyc
  have hCK : Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer (K : Set G) =
      Subgroup.zpowers w := by
    rw [hHw]
    apply le_antisymm
    · rintro x ⟨hxH, hxK⟩
      have hxw : x * w = w * x := by
        calc x * w = x * w * x⁻¹ * x := by group
          _ = w * x := by rw [hwZ x hxH]
      have hFle : generalizedFittingSubgroupOf H ≤ Subgroup.centralizer ({x} : Set G) := by
        show CFSG.fittingSubgroupOf H ⊔ componentLayerOf H ≤ _
        refine sup_le (hFH.trans ?_) (hEK.trans ?_)
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact hxw.symm
        · intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp hxK) y hy
      have hxF : x ∈ Subgroup.centralizer (generalizedFittingSubgroupOf H : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp (hFle hy)
      have hxFs := inf_centralizer_generalizedFitting_le H ⟨hxH, hxF⟩
      have hxE : x ∈ Subgroup.centralizer (componentLayerOf H : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (Subgroup.mem_centralizer_iff.mp hxK) y (hEK hy)
      exact hFH (generalizedFittingSubgroupOf_inf_centralizer_le H ⟨hxFs, hxE⟩)
    · rw [Subgroup.zpowers_le]
      exact ⟨hHw ▸ Subgroup.mem_centralizer_singleton_iff.mpr rfl, hwW.2⟩
  have hKw : K ≤ Subgroup.centralizer ({w} : Set G) := hHw ▸ hK.1
  have hKn : (K.subgroupOf (Subgroup.centralizer ({w} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKw, hHw]
    exact hKN
  have hco : IsCoatom (Subgroup.centralizer ({w} : Set G)) := hHw ▸ hH.1
  refine ⟨hG.isSimpleGroup, hG.hasAbelianSylowTwo, fun s hs => ?_⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow T hs
  have hgs2 : orderOf (g * s * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]
  obtain ⟨n, -, hnw⟩ := hG.exists_conj_of_isCyclic ht hH T htT hK hWcyc hwW.1 hw2 hg hgs2
  have hseq : (g⁻¹ * n) * w * (g⁻¹ * n)⁻¹ = s := by
    calc (g⁻¹ * n) * w * (g⁻¹ * n)⁻¹ = g⁻¹ * (n * w * n⁻¹) * g := by group
      _ = g⁻¹ * (g * s * g⁻¹) * g := by rw [hnw]
      _ = s := by group
  obtain ⟨j1, j2, j3, ⟨e'⟩, j5⟩ := jr_data_conj hco hKw hKn eK hCK (g⁻¹ * n)
  rw [hseq] at j1 j2 j3 j5
  exact ⟨j1, p, f, hp, _, hpodd, hf, h5, j2, j3, ⟨e'⟩, j5⟩

end BenderCounterexample

end CFSG.Walter

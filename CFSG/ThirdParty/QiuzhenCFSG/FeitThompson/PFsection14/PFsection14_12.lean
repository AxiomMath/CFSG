module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_11_4

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.12)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.12) -/


public theorem section14_characteristicSubgroupIn_of_le_cyclic
    {G : Type u} [Group G] [Finite G]
    {U H : Subgroup G}
    (hUH : U ≤ H) (hcyc : IsCyclic H) :
    characteristicSubgroupIn U H := by
  haveI : IsCyclic H := hcyc
  exact ⟨hUH, section12_subgroup_characteristic_of_cyclic (U.subgroupOf H)⟩

public theorem section14_isHallSubgroup_map_of_surjective
    {G : Type u} {G' : Type u} [Group G] [Finite G] [Group G'] [Finite G']
    {π : Set Nat.Primes} {H : Subgroup G} (hHall : IsHallSubgroup π H)
    (f : G →* G') (hf : Function.Surjective f) :
    IsHallSubgroup π (H.map f) := by
  refine isHallSubgroup_of (G := G') (π := π) (H := H.map f)
    (hcard := ?_) (hindex := ?_)
  · intro q hq_dvd
    exact hHall.p_in_pi_of_p_dvd_card q
      (hq_dvd.trans (Subgroup.card_map_dvd (H := H) f))
  · intro q hq_mem hq_dvd_idx
    have hidx_dvd : (H.map f).index ∣ H.index :=
      Subgroup.index_map_dvd (H := H) hf
    exact (hHall.p_in_pi_of_p_dvd_index q (hq_dvd_idx.trans hidx_dvd)) hq_mem

public theorem section14_subgroupPrimeSet_conjBy
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (g : G) :
    subgroupPrimeSet (H.conjBy g) = subgroupPrimeSet H := by
  have hcard : Nat.card (H.conjBy g) = Nat.card H :=
    section11_card_conjBy (G := G) H g
  ext p
  rw [subgroupPrimeSet, subgroupPrimeSet, hcard]

public theorem section14_subgroupOf_conjBy_eq_map
    {G : Type u} [Group G] [Finite G]
    {H M : Subgroup G} (hHM : H ≤ M) (g : G) :
    let eM : M ≃* M.conjBy g := (MulAut.conj g).subgroupMap M
    (H.conjBy g).subgroupOf (M.conjBy g) = (H.subgroupOf M).map eM.toMonoidHom := by
  classical
  intro eM
  ext x
  constructor
  · intro hx
    change (x : G) ∈ H.conjBy g at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyH, hyx⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨⟨y, hHM hyH⟩, hyH, ?_⟩
    exact Subtype.ext hyx
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyH, hyx⟩
    change (x : G) ∈ H.conjBy g
    rw [← hyx]
    exact Subgroup.mem_map.mpr ⟨(y : G), hyH, rfl⟩

public theorem section14_section16NilpotentNormalHallIn_conjBy
    {G : Type u} [Group G] [Finite G]
    {H M : Subgroup G} (h : section16NilpotentNormalHallIn H M) (g : G) :
    section16NilpotentNormalHallIn (H.conjBy g) (M.conjBy g) := by
  classical
  rcases h with ⟨hHM, hNorm, hNil, hHall⟩
  let eM : M ≃* M.conjBy g := (MulAut.conj g).subgroupMap M
  have hHMg : H.conjBy g ≤ M.conjBy g := by
    simpa [Subgroup.conjBy] using
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hHM
  refine ⟨hHMg, ?_, ?_, ?_⟩
  · have hsub_eq :
        (H.conjBy g).subgroupOf (M.conjBy g) =
          (H.subgroupOf M).map eM.toMonoidHom :=
      section14_subgroupOf_conjBy_eq_map hHM g
    rw [hsub_eq]
    exact Subgroup.Normal.map hNorm eM.toMonoidHom eM.surjective
  · let eH : H ≃* H.conjBy g := (MulAut.conj g).subgroupMap H
    exact Group.nilpotent_of_mulEquiv (G := H) (G' := H.conjBy g) eH
  · have hsub_eq :
        (H.conjBy g).subgroupOf (M.conjBy g) =
          (H.subgroupOf M).map eM.toMonoidHom :=
      section14_subgroupOf_conjBy_eq_map hHM g
    rw [hsub_eq]
    rw [section14_subgroupPrimeSet_conjBy (G := G) H g]
    exact section14_isHallSubgroup_map_of_surjective hHall eM.toMonoidHom eM.surjective

public theorem section14_section16MFSubgroup_conjBy
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G} (hMF : section16MFSubgroup M MF) (g : G) :
    section16MFSubgroup (M.conjBy g) (MF.conjBy g) := by
  classical
  refine ⟨section14_section16NilpotentNormalHallIn_conjBy hMF.1 g, ?_⟩
  intro H hH
  have hback : section16NilpotentNormalHallIn (H.conjBy g⁻¹) M := by
    have htmp := section14_section16NilpotentNormalHallIn_conjBy hH g⁻¹
    simpa [section11_conjBy_inv] using htmp
  have hle_back : H.conjBy g⁻¹ ≤ MF := hMF.2 (H.conjBy g⁻¹) hback
  simpa using
    (section11_le_conjBy_inv_of_conjBy_le
      (G := G) (H := H) (K := MF) (g := g⁻¹) hle_back)

public theorem section16MFSubgroup_unique_local
    {G : Type u} [Group G] [Finite G]
    {M MF MF' : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hMF' : section16MFSubgroup M MF') :
    MF = MF' := by
  exact le_antisymm (hMF'.2 MF hMF.1) (hMF.2 MF' hMF'.1)

public theorem section14_isCyclic_of_conjBy_eq
    {G : Type u} [Group G] [Finite G]
    {H K V : Subgroup G} {g : G}
    (hHK : H.conjBy g = K) (hKV : K = V) (hVcyc : IsCyclic V) :
    IsCyclic H := by
  have hHconjV : H.conjBy g = V := hHK.trans hKV
  let eHV : H.conjBy g ≃* V := MulEquiv.subgroupCongr hHconjV
  have hHconj_cyc : IsCyclic (H.conjBy g) := eHV.isCyclic.mpr hVcyc
  let e0 : H ≃* (Subgroup.map ((MulAut.conj g).toMonoidHom) H) :=
    MulEquiv.subgroupMap (MulAut.conj g) H
  have hmap :
      Subgroup.map ((MulAut.conj g).toMonoidHom) H = H.conjBy g := by
    rfl
  let e : H ≃* H.conjBy g := e0.trans (MulEquiv.subgroupCongr hmap)
  exact e.isCyclic.mpr hHconj_cyc

public theorem section14_theorem_14_12_conjBy_eq_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
        hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          (∃ g : G, L.conjBy g = M) →
            K = V ∧ K.relIndex M = p * q →
              ∃ g : G, H.conjBy g = K := by
  intro hctx h143 h1410 hLMconj h1411
  rcases h143 with
    ⟨_hLmax, _hUnorm, hHMF, _hTypeI, _hDadeL, _hPunctL, _h52L, _hCoherL,
      _hφmem, _hφirr, _hφdeg, _hβS, _hβT, _hβL⟩
  rcases h1410 with
    ⟨_hMmax, _hModd, _hVnorm, hKMF, _hTypeI, _hDadeM, _hPunctM, _h52M, _hCoherM,
      _hψmem, _hψirr, _hψdeg, _hβM⟩
  rcases hLMconj with ⟨g, hLM⟩
  have hHconjMF : section16MFSubgroup M (H.conjBy g) := by
    have htmp := section14_section16MFSubgroup_conjBy hHMF g
    simpa [hLM] using htmp
  exact ⟨g, section16MFSubgroup_unique_local hHconjMF hKMF⟩

public theorem section14_theorem_14_12_cyclicity_from_14_11_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
        hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          (∃ g : G, L.conjBy g = M) →
              K = V ∧ K.relIndex M = p * q →
                Section13.case_9_7_b_sourceDataForSection13 Tmax Q V W2 W1 D q p v →
                  v = (q ^ p - 1) / (q - 1) →
                    d = 1 →
            IsCyclic H := by
  intro hctx h143 h1410 hLMconj h1411 hcaseT hv hd
  have hdcard : Nat.card D = 1 := by
    rcases hctx.1 with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, hdD,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    rw [← hdD, hd]
  have hVcyc : IsCyclic V :=
    section14_isCyclic_of_case_9_7_b_sourceData_card_eq_one hcaseT hdcard
  rcases section14_theorem_14_12_conjBy_eq_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d hctx h143 h1410 hLMconj h1411 with
    ⟨g, hHK⟩
  exact section14_isCyclic_of_conjBy_eq hHK h1411.1 hVcyc

public theorem section14_theorem_14_12_characteristic_from_14_11_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
        hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          (∃ g : G, L.conjBy g = M) →
            K = V ∧ K.relIndex M = p * q →
              Section13.case_9_7_b_sourceDataForSection13 Tmax Q V W2 W1 D q p v →
                v = (q ^ p - 1) / (q - 1) →
                  d = 1 →
            characteristicSubgroupIn U H := by
  intro hctx h143 h1410 hLMconj h1411 hcaseT hv hd
  have hcyc : IsCyclic H :=
    section14_theorem_14_12_cyclicity_from_14_11_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d hctx h143 h1410 hLMconj h1411 hcaseT hv hd
  rcases section14_theorem_14_5_pf13_17_inputs
      (hctx := hctx) (h143 := h143) with
    ⟨_htypeII, _hfrobLH, hUH, _hcomp⟩
  exact section14_characteristicSubgroupIn_of_le_cyclic hUH hcyc

public theorem section14_theorem_14_12_characteristic_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          (∃ g : G, L.conjBy g = M) →
            characteristicSubgroupIn U H := by
  intro hctx h143 h1410 hLMconj
  have h1411 : K = V ∧ K.relIndex M = p * q :=
    section14_theorem_14_11_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410
  rcases section14_theorem_14_4_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 with
    ⟨hcaseT, hv⟩
  have hd : d = 1 :=
    Section13.theorem_13_12 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1)
  exact section14_theorem_14_12_characteristic_from_14_11_source_bridge
    Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
    p q u v c d hctx h143 h1410 hLMconj h1411 hcaseT hv hd

public theorem section14_theorem_14_12_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          (∃ g : G, L.conjBy g = M) →
            theorem_14_2_a_data P U W2 p q ∧
              theorem_14_2_b_data Q W1 W2 U q := by
  intro hctx h143 h1410 hLMconj
  have hchar : characteristicSubgroupIn U H :=
    section14_theorem_14_12_characteristic_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d hctx h143 h1410 hLMconj
  exact section14_theorem_14_7_source_bridge
    Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 hchar


end CFSG.Section14

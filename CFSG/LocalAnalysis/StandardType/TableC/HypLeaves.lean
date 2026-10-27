module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.TableC.Extract
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.LocalAnalysis.StandardType.GGExcCompLiftInput

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType

theorem ggTC_rank_le {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} (hp : p.Prime)
    (hB : LargeEvenIsBmax p B) :
    ∀ E T : Subgroup G, T ≠ ⊥ → IsPGroup 2 T → IsElemAbelian p E →
      E ≤ Subgroup.normalizer (T : Set G) → Nat.card E ≤ Nat.card B := by
  intro E T hT h2T hE hEN
  obtain ⟨-, hBcard, -⟩ := hB
  have hEp : IsPGroup p E := CFSG.StandardType.isPGroup_of_isElemAbelian hE
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hEp
  have hk_le : k ≤ CFSG.Open.GLATwoLocalRank p G :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
      hp.one_lt hT h2T hE hEN hk
  calc Nat.card E = p ^ k := hk
    _ ≤ p ^ CFSG.Open.GLATwoLocalRank p G := Nat.pow_le_pow_right hp.pos hk_le
    _ = p ^ LargeEvenTwoLocalRank p G := rfl
    _ = Nat.card B := hBcard.symm

private theorem ggTC_nbr_of_dvd
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (h65 : ∀ d ∈ D, d ≠ 1 →
      IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}))
    {d : G} (hd : d ∈ D) (hdx : d ∉ Subgroup.zpowers x) (hpJ : p ∣ Nat.card J)
    (hDK : ¬ D ≤ Subgroup.centralizer (ggKd p B x L D J d : Set G)) :
    GGNbr p B x D J d (ggKd p B x L D J d) := by
  have hp : p.Prime := hctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hd1 : d ≠ 1 := fun h => hdx (h ▸ Subgroup.one_mem _)
  set K := ggKd p B x L D J d with hKdef
  have hK : IsComponentOf K (Subgroup.centralizer {d}) := h65 d hd hd1
  have hJK : J ≤ K := le_ggKd p B x L D J d
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hctx.j_comp.2.2
  have hpK : p ∣ Nat.card K := hpJ.trans (Subgroup.card_dvd_of_le hJK)
  have hxD : x ∈ D := hctx.x_mem_d
  have hxB : x ∈ B := hctx.sstar.2.1
  have hD : D = Subgroup.closure {x, d} :=
    (ggClosure_pair_eq hp hctx.card_d hxD hd hctx.sstar.2.2.1
      (hctx.sstar.1.1.2 x hxB) hdx).symm
  have hKO : ¬ K ≤ CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({d} : Set G)) := by
    intro hle
    have hcop : Nat.Coprime p
        (Nat.card (CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({d} : Set G)))) := by
      rw [CFSG.ComponentClassification.LBalance.primeCore_eq_map,
        Subgroup.card_map_of_injective (Subgroup.centralizer ({d} : Set G)).subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop (hpK.trans (Subgroup.card_dvd_of_le hle))
  have hA : LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G)) K :=
    (largeEvenPComponent_iff_lBalance p _ K).mpr
      ⟨hK.1, lBalanceIsPComponent_of_isComponentOf hK hKO⟩
  have hKL : K ≤ LargeEvenPLayer p (Subgroup.centralizer ({d} : Set G)) := le_sSup hA
  have hAJ : K ≤ ⨆ (a : G) (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({d} : Set G))),
      J.map (MulAut.conj a⁻¹).toMonoidHom := by
    calc K = ⨆ (a : G) (_ : a ∈ K), J.map (MulAut.conj a).toMonoidHom :=
          (eq_iSup_map_conj_of_isQuasisimple hK.2.2 hJq hJK).symm
      _ ≤ _ := by
        refine iSup₂_le fun a ha => ?_
        have h := le_iSup₂ (f := fun (a : G)
          (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({d} : Set G))) =>
            J.map (MulAut.conj a⁻¹).toMonoidHom) a⁻¹ (hKL (K.inv_mem ha))
        rwa [inv_inv] at h
  have hxA : ¬ (⁅K, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K := by
    intro h
    have hOcop : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p K)) := by
      rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hxCd : x ∈ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hctx.d_comm x hxD d hd)
    have hxN : x ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_of_le_component hK hJq hJK hxCd (hctx.le_centralizer_J hxD)
    have hxK : x ∈ Subgroup.centralizer (K : Set G) :=
      mem_centralizer_of_commutator_le_coprime hp hK.2.2 hpK hOcop
        (fun k hk => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer hk)) hxN h
    have hdK : d ∈ Subgroup.centralizer (K : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hK.1 hk)
    apply hDK
    rw [hD, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hxK
    · exact hdK
  exact ggNbr_of_pComponent hctx.thmI hctx.stdSub hpJ hD hA hJK hAJ hxA

private theorem ggPComponent_le_normalizer_of_ne
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Y K L : Subgroup G}
    (hK : LargeEvenPComponent p Y K) (hL : LargeEvenPComponent p Y L) (hne : L ≠ K) :
    L ≤ Subgroup.normalizer (K : Set G) := by
  have hKY : K ≤ Y := ((largeEvenPComponent_iff_lBalance p Y K).1 hK).1
  have hLY : L ≤ Y := ((largeEvenPComponent_iff_lBalance p Y L).1 hL).1
  have hK' : CFSG.IsPComponent p (K.subgroupOf Y) :=
    (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance
      p Y K hKY).mpr ((largeEvenPComponent_iff_lBalance p Y K).1 hK).2
  have hL' : CFSG.IsPComponent p (L.subgroupOf Y) :=
    (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance
      p Y L hLY).mpr ((largeEvenPComponent_iff_lBalance p Y L).1 hL).2
  have hne' : K.subgroupOf Y ≠ L.subgroupOf Y := fun h => hne (by
    calc L = (L.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ = (K.subgroupOf Y).map Y.subtype := by rw [h]
      _ = K := Subgroup.map_subgroupOf_eq_of_le hKY)
  have h := (CFSG.ComponentClassification.CatalogueBPrimeJoin.mutual_normalization_core_commutation
    p (K.subgroupOf Y) (L.subgroupOf Y) hK' hL' hne').1
  calc L = (L.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hLY).symm
    _ ≤ (Subgroup.normalizer (K.subgroupOf Y : Set ↥Y)).map Y.subtype := Subgroup.map_mono h
    _ ≤ Subgroup.normalizer ((K.subgroupOf Y).map Y.subtype : Set G) :=
        Subgroup.le_normalizer_map Y.subtype
    _ = Subgroup.normalizer (K : Set G) := by rw [Subgroup.map_subgroupOf_eq_of_le hKY]

theorem GGTCCtx.h7
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGTCCtx t p B Bs x L D J n f ψ) :
    ∀ d ∈ D, d ∉ Subgroup.zpowers x → ∀ K : Subgroup G,
      IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) → J ≤ K → K ≠ J →
        p ∣ Nat.card J → GGInnerDiagOn (Subgroup.zpowers x) K →
          LargeEvenMarking ↥K (fun lab _ _ _ _ _ =>
            LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥)) := by
  intro d hd hdx K hK hJK hKJ hpJ hInner
  have hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ := h.1
  have hcomp : ∀ d ∈ D, d ≠ 1 →
      IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}) := h.2.2.2.1
  have hd1 : d ≠ 1 := fun hh => hdx (hh ▸ Subgroup.one_mem _)
  have hKeq : ggKd p B x L D J d = K :=
    ggKd_eq_of_le_component hK hctx.j_comp.2.2 hJK
  have hDK : ¬ D ≤ Subgroup.centralizer (ggKd p B x L D J d : Set G) := fun hh =>
    hKJ (hKeq ▸ ggSixTC_eq_of_centralizes hctx hcomp hd hd1 hh)
  have hnbr : GGNbr p B x D J d (ggKd p B x L D J d) :=
    ggTC_nbr_of_dvd hctx hcomp hd hdx hpJ hDK
  have h5 := hctx.stdType.2.2.1 d (ggKd p B x L D J d)
    (isNeighborOf_of_ggNbr hctx.stdSub hnbr)
  rw [hKeq] at h5
  rcases largeEvenMarking_or h5.2 with hHS | hPF
  · exact hHS
  · exact absurd hPF (ggNbr_not_primeField_known hctx.prime hctx.ne_two
      (Subgroup.mem_zpowers x) hInner)

theorem GGTCCtx.h6
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGTCCtx t p B Bs x L D J n f ψ) :
    ∀ H : Subgroup G, L ≤ H → (∀ d ∈ D, d ≠ 1 → ∀ K : Subgroup G,
      IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) → J ≤ K → K ≤ H) →
        ggG0 p B x L D J ≤ H := by
  intro H hLH hKd
  have hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ := h.1
  have hcomp : ∀ d ∈ D, d ≠ 1 →
      IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}) := h.2.2.2.1
  haveI : Fact p.Prime := ⟨hctx.prime⟩
  have hxB : x ∈ B := hctx.sstar.2.1
  have hxp : x ^ p = 1 := hctx.sstar.1.1.2 x hxB
  refine ggG0_le_of hLH ?_
  intro y K hNbr
  obtain ⟨hSHat, hNbr'⟩ := hNbr
  have hyD : y ∈ D := by
    rw [hNbr'.1]
    exact Subgroup.subset_closure (by simp)
  have hy1 : y ≠ 1 := by
    intro hy
    have hDx : D = Subgroup.zpowers x := by
      rw [hNbr'.1, hy, Subgroup.zpowers_eq_closure]
      refine le_antisymm ?_ (Subgroup.closure_mono (by intro z hz; exact Or.inl hz))
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzx | hz1
      · rw [hzx]; exact Subgroup.subset_closure (Set.mem_singleton x)
      · rw [hz1]; exact Subgroup.one_mem _
    have hox : orderOf x = p := orderOf_eq_prime hxp hctx.sstar.2.2.1
    have hcard : Nat.card D = p := by rw [hDx, Nat.card_zpowers, hox]
    rw [hctx.card_d] at hcard
    have hp2 : 2 ≤ p := hctx.prime.two_le
    nlinarith
  set Ky := ggKd p B x L D J y
  have hKyC : IsComponentOf Ky (Subgroup.centralizer {y}) := hcomp y hyD hy1
  have hKyG0 : Ky ≤ ggG0 p B x L D J := hctx.ggKd_le_ggG0 hyD
  have hKyCy : Ky ≤ Subgroup.centralizer {y} := hctx.ggKd_le_centralizer hyD
  have hKy_comp : IsComponentOf Ky (ggG0 p B x L D J ⊓ Subgroup.centralizer {y}) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hKyC
      (le_inf hKyG0 hKyCy) inf_le_right
  have hKyH : Ky ≤ H := hKd y hyD hy1 Ky hKy_comp (le_ggKd p B x L D J y)
  have hcoreN : Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.normalizer (CFSG.Open.lBalancePrimeCore p
        (Subgroup.centralizer ({y} : Set G)) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.ComponentClassification.LBalance.primeCore_le p _)).mp
      (CFSG.ComponentClassification.LBalance.primeCore_normal p _)
  have hLayerY : LargeEvenPLayer p (Subgroup.centralizer {y}) ≤ Subgroup.centralizer {y} :=
    sSup_le fun L' hL' => ((largeEvenPComponent_iff_lBalance p _ L').1 hL').1
  have hnotle : ¬ Ky ≤ CFSG.Open.lBalancePrimeCore p
      (Subgroup.centralizer ({y} : Set G)) := by
    intro hle
    have hKle_core : K ≤ CFSG.Open.lBalancePrimeCore p
        (Subgroup.centralizer ({y} : Set G)) := by
      calc K ≤ ⨆ (a : G) (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G))),
            J.map (MulAut.conj a⁻¹).toMonoidHom := hNbr'.2.1
        _ ≤ CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({y} : Set G)) := by
            refine iSup₂_le fun a ha => ?_
            have haY : a ∈ Subgroup.centralizer ({y} : Set G) := hLayerY ha
            have haN : a ∈ Subgroup.normalizer
                (CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({y} : Set G)) : Set G) :=
              hcoreN haY
            have hJle : J ≤ CFSG.Open.lBalancePrimeCore p
                (Subgroup.centralizer ({y} : Set G)) :=
              (le_ggKd p B x L D J y).trans hle
            calc J.map (MulAut.conj a⁻¹).toMonoidHom
                ≤ (CFSG.Open.lBalancePrimeCore p
                    (Subgroup.centralizer ({y} : Set G))).map
                    (MulAut.conj a⁻¹).toMonoidHom := Subgroup.map_mono hJle
              _ = CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({y} : Set G)) :=
                  map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ haN)
    have hKY : K ≤ Subgroup.centralizer ({y} : Set G) :=
      ((largeEvenPComponent_iff_lBalance p _ K).1 hSHat.2.2.2.2.1).1
    have hK' : CFSG.IsPComponent p (K.subgroupOf (Subgroup.centralizer ({y} : Set G))) :=
      (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance
        p _ K hKY).mpr ((largeEvenPComponent_iff_lBalance p _ K).1 hSHat.2.2.2.2.1).2
    have hsub : K.subgroupOf (Subgroup.centralizer ({y} : Set G)) ≤
        CFSG.pPrimeCore p ↥(Subgroup.centralizer ({y} : Set G)) := by
      have hmap : (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).map
            (Subgroup.centralizer ({y} : Set G)).subtype ≤
          (CFSG.pPrimeCore p ↥(Subgroup.centralizer ({y} : Set G))).map
            (Subgroup.centralizer ({y} : Set G)).subtype := by
        rw [Subgroup.map_subgroupOf_eq_of_le hKY,
          ← CFSG.ComponentClassification.LBalance.primeCore_eq_map p
            (Subgroup.centralizer ({y} : Set G))]
        exact hKle_core
      exact (Subgroup.map_le_map_iff_of_injective
        (Subgroup.centralizer ({y} : Set G)).subtype_injective).mp hmap
    exact (CFSG.StandardType.GGPumpup.not_le_pPrimeCore hK') hsub
  have hKy_pc_lb : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer {y}) Ky :=
    lBalanceIsPComponent_of_isComponentOf hKyC hnotle
  have hKy_pc : LargeEvenPComponent p (Subgroup.centralizer {y}) Ky :=
    (largeEvenPComponent_iff_lBalance p _ Ky).mpr ⟨hKyCy, hKy_pc_lb⟩
  have hPLayerN : LargeEvenPLayer p (Subgroup.centralizer {y}) ≤
      Subgroup.normalizer (Ky : Set G) := by
    refine sSup_le fun L' hL' => ?_
    by_cases h : L' = Ky
    · rw [h]; exact Subgroup.le_normalizer
    · exact ggPComponent_le_normalizer_of_ne hKy_pc hL' h
  have hKle : K ≤ Ky := by
    calc K ≤ ⨆ (a : G) (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G))),
          J.map (MulAut.conj a⁻¹).toMonoidHom := hNbr'.2.1
      _ ≤ Ky := by
          refine iSup₂_le fun a ha => ?_
          have haN : a ∈ Subgroup.normalizer (Ky : Set G) := hPLayerN ha
          have hmap : Ky.map (MulAut.conj a⁻¹).toMonoidHom = Ky :=
            map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ haN)
          calc J.map (MulAut.conj a⁻¹).toMonoidHom
              ≤ Ky.map (MulAut.conj a⁻¹).toMonoidHom :=
                Subgroup.map_mono (le_ggKd p B x L D J y)
            _ = Ky := hmap
  exact hKle.trans hKyH

end CFSG.StandardType.TableCRes

end

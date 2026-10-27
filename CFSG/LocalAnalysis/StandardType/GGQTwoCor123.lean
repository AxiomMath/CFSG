module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsPrime
public import CFSG.LocalAnalysis.StandardType.GGQTwoCor81

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2n_stdPair_le_G0 {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hp : p = 3)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) {w : G} {X : Subgroup G}
    (hX : GGStdPair' p Bs w X) (hwD : w ∈ D)
    (hxZ : Subgroup.zpowers w = Subgroup.zpowers x ∨
      ¬ ⁅X, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p X) :
    X ≤ ggG0 p B x L D J := by
  have hHyp' : GGCorFiveTwentyHyp p B Bs x L D J := hHyp
  obtain ⟨hcfg, -, -, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hp' : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp'⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hBstar.1 hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hStdSub
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hStdSub.1.2.2.2.2.2.1.2.2
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJq
  have hCD_le : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer (D : Set G) :=
    inf_eq_right.mpr
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hStdSub.1.2.2.2.1))
  have hLinfD_sn : IsSubnormal (L ⊓ Subgroup.centralizer (D : Set G))
      (Subgroup.centralizer (D : Set G)) := by
    have h := LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hS.2.2.2.1.2.1
      (Subgroup.centralizer (D : Set G))
    rwa [hCD_le] at h
  have hJcompD : IsComponentOf J (Subgroup.centralizer (D : Set G)) :=
    isComponentOf_of_isSubnormal_of_isComponentOf hStdSub.1.2.2.2.2.2.1 hLinfD_sn
  have hQ : LargeEvenPComponent p (Subgroup.centralizer (D : Set G)) J :=
    (largeEvenPComponent_iff_lBalance p (Subgroup.centralizer (D : Set G)) J).2
      ⟨hJcompD.1, lBalanceIsPComponent_of_isComponentOf hJcompD
        (not_le_lBalancePrimeCore_of_dvd (Y := Subgroup.centralizer (D : Set G)) hpJ)⟩
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  have hJX : J ≤ X := ggQ2n_absorb hLB hHyp' hp hDBs hwD hX hQ hCav
  by_cases hzw : Subgroup.zpowers w = Subgroup.zpowers x
  · obtain ⟨-, hLpc, huniq⟩ := eq_of_le_of_stdSub hI hStdSub hpJ
    have hXpc : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) X :=
      (centralizer_singleton_eq_of_zpowers_eq hzw) ▸ hX.2.2.1
    have hXL : X = L := huniq X hXpc hJX
    rw [hXL]
    exact le_ggG0_left p B x L D J
  · have hwx : w ∉ Subgroup.zpowers x := by
      intro hw
      apply hzw
      refine le_antisymm (Subgroup.zpowers_le.mpr hw) ?_
      exact Subgroup.zpowers_le.mpr
        (mem_zpowers_of_mem_zpowers_of_ne_one hp' (hBstar.2.1.2 x hxBs) hw hX.2.1)
    have hxw : x ∉ Subgroup.zpowers w := by
      intro hxw
      apply hzw
      refine le_antisymm ?_ (Subgroup.zpowers_le.mpr hxw)
      exact Subgroup.zpowers_le.mpr
        (mem_zpowers_of_mem_zpowers_of_ne_one hp' (hBstar.2.1.2 w hX.1) hxw hx1)
    have hD : D = Subgroup.closure {x, w} := eq_closure_pair_of_mem hI hStdSub hwD hwx
    obtain ⟨hKpc, hJK, -, hcase⟩ :=
      pumpup_of_stdSub (ggPumpupInput_of_lBalance hLB) hI hStdSub hpJ hD
    have hKlb : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer ({w} : Set G))
        (ggLayerClosure p (Subgroup.centralizer ({w} : Set G)) J) :=
      ((largeEvenPComponent_iff_lBalance p _ _).1 hKpc).2
    have hXlb : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer ({w} : Set G)) X :=
      ((largeEvenPComponent_iff_lBalance p _ X).1 hX.2.2.1).2
    have hKX : X = ggLayerClosure p (Subgroup.centralizer ({w} : Set G)) J :=
      GGDichotomy.eq_of_le_of_pComponent hKlb hXlb hJK hJX hJJ hpJ
    rcases hcase with hnb | htriv
    · have hKG0 : ggLayerClosure p (Subgroup.centralizer ({w} : Set G)) J ≤
          ggG0 p B x L D J := le_ggG0_of_ggNbr hnb
      rw [hKX]
      exact hKG0
    · exfalso
      have htriv' : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X := by
        rw [hKX]
        exact htriv
      exact (hxZ.resolve_left hzw) htriv'

private theorem ggQ2nC_hxZ {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x u g : G} {X : Subgroup G} (hp : p.Prime) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hgup : (g * u * g⁻¹) ^ p = 1)
    (hZ : ∀ b ∈ B, ⁅X, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p X →
      b ∈ Subgroup.zpowers u) (hxb : g⁻¹ * x * g ∈ B) :
    Subgroup.zpowers (g * u * g⁻¹) = Subgroup.zpowers x ∨
      ¬ ⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers x⁆ ≤
        LargeEvenPPrimeCoreOf p (X.map (MulAut.conj g).toMonoidHom) := by
  by_cases hz : Subgroup.zpowers (g * u * g⁻¹) = Subgroup.zpowers x
  · exact Or.inl hz
  · refine Or.inr fun hc => ?_
    have hc' : ⁅X, Subgroup.zpowers (g⁻¹ * x * g)⁆ ≤ LargeEvenPPrimeCoreOf p X :=
      (ggStdPair'_commutator_conj_iff p X g x).mp hc
    have hmem : g⁻¹ * x * g ∈ Subgroup.zpowers u := hZ _ hxb hc'
    have hxmem : x ∈ Subgroup.zpowers (g * u * g⁻¹) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [conj_zpow, hk]
      group
    have hrev : g * u * g⁻¹ ∈ Subgroup.zpowers x :=
      mem_zpowers_of_mem_zpowers_of_ne_one hp hgup hxmem hx1
    exact hz (le_antisymm (Subgroup.zpowers_le.mpr hrev) (Subgroup.zpowers_le.mpr hxmem))

theorem ggQ2n_normalizer_inf_le {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hp : p = 3)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) :
    Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hHyp' : GGCorFiveTwentyHyp p B Bs x L D J := hHyp
  have hDJ : LargeEvenStdSub p B x L D J := hHyp.1.2.2
  obtain ⟨hcfg, -, -, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hp' : p.Prime := hI.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hBstar.1 hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxp : x ^ p = 1 := hBstar.2.1.2 x hxBs
  have hx_D : x ∈ D := hDJ.1.2.2.2.1
  have hBleBs : B ≤ Bs := hBstar.1
  have hDleB : D ≤ B := hDJ.1.1
  refine le_normalizer_of_map_conj_le (S := Subgroup.normalizer (Bs : Set G) ⊓
    Subgroup.normalizer (D : Set G)) (H := ggG0 p B x L D J) ?_
  intro g hg
  have hgBs : g ∈ Subgroup.normalizer (Bs : Set G) := hg.1
  have hgD : g ∈ Subgroup.normalizer (D : Set G) := hg.2
  have hxb : g⁻¹ * x * g ∈ B := by
    refine hDleB ?_
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgD) x).mp hx_D
    simpa using h
  have hLZ : ∀ b ∈ B, ⁅L, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p L →
      b ∈ Subgroup.zpowers x :=
    fun b hb h => ggStdPair'_L_Z hP hHyp' hCav b (hBleBs hb) h
  have hLpair : GGStdPair' p Bs x L := ggStdPair'_L hP hHyp' hCav
  have hLpair' : GGStdPair' p Bs (g * x * g⁻¹) (L.map (MulAut.conj g).toMonoidHom) :=
    ggStdPair'_conj hgBs hLpair
  have hgxD : g * x * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hgD x).mp hx_D
  have hgxp : (g * x * g⁻¹) ^ p = 1 :=
    hBstar.2.1.2 (g * x * g⁻¹) ((Subgroup.mem_normalizer_iff.mp hgBs x).mp hxBs)
  have hxZ_L := ggQ2nC_hxZ hp' hx1 hxp hgxp hLZ hxb
  have hLle : L.map (MulAut.conj g).toMonoidHom ≤ ggG0 p B x L D J :=
    ggQ2n_stdPair_le_G0 hLB hP hHyp' hp hCav hLpair' hgxD hxZ_L
  have hSup : (⨆ (y : G) (K : Subgroup G)
      (_ : LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J), K).map
        (MulAut.conj g).toMonoidHom ≤ ggG0 p B x L D J := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun K => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK => ?_
    have hnbr : GGNbr p B x D J y K := hK
    have hKpair : GGStdPair' p Bs y K := ggStdPair'_nbr hLB hP hHyp' hCav hnbr
    have hKpair' : GGStdPair' p Bs (g * y * g⁻¹) (K.map (MulAut.conj g).toMonoidHom) :=
      ggStdPair'_conj hgBs hKpair
    have hyD : y ∈ D := by
      rw [hnbr.2.1]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
    have hgyD : g * y * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hgD y).mp hyD
    have hgyp : (g * y * g⁻¹) ^ p = 1 :=
      hBstar.2.1.2 (g * y * g⁻¹)
        ((Subgroup.mem_normalizer_iff.mp hgBs y).mp (hBleBs hnbr.1.2.1))
    have hxZ_K := ggQ2nC_hxZ hp' hx1 hxp hgyp
      (ggStdPair'_nbr_Z hLB hP hHyp' hnbr) hxb
    exact ggQ2n_stdPair_le_G0 hLB hP hHyp' hp hCav hKpair' hgyD hxZ_K
  unfold ggG0
  rw [Subgroup.map_sup]
  exact sup_le hLle hSup

end CFSG.StandardType

end

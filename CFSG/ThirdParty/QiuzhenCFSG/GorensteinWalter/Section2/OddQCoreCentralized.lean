module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.KleinFourNormalizerConjugator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.DGroupInvariantClosurePCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.MinimalInvariantInvolutionCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.MinimalInvariantNormalizerCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.KleinFourCentralizerWitness
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma24
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma21
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd cores centralized by the distinguished involution

The minimal-counterexample and Klein-four pushing-up argument shows that the
distinguished involution centralizes every odd ambient `p`-core of the chosen
maximal involution-centralizer overgroup.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- In a minimal counterexample, the distinguished involution centralizes the
ambient image of every odd `p`-core of `c.Hhat`. -/
public theorem mem_centralizer_qCoreOf_of_minimalCounterexample
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    c.t ∈ Subgroup.centralizer (qCoreOf c.Hhat p : Set G) := by
  classical
  by_contra hcontra
  let : Fact p.Prime := ⟨hp⟩
  let Q : Subgroup G := qCoreOf c.Hhat p
  let Z : Subgroup G := Subgroup.zpowers c.t
  have htH : c.t ∈ c.H := by
    rw [c.H_eq_centralizer]
    simp [Subgroup.mem_centralizer_iff]
  have hHt : c.H ≤ Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
  have hQp : IsPGroup p Q := by
    simpa [Q] using qCoreOf_isPGroup c.Hhat p
  have hQle : Q ≤ qCoreOf c.Hhat p := by rfl
  have hHQ : c.H ≤ Subgroup.normalizer (Q : Set G) := by
    exact c.H_le_Hhat.trans (by
      simpa [Q] using le_normalizer_of_isNormalIn (qCoreOf_normal_in c.Hhat p))
  have hQcomm : ⁅Q, Z⁆ ≠ ⊥ := by
    intro hbot
    have hQcentZ : Q ≤ Subgroup.centralizer (Z : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hZcentQ : Z ≤ Subgroup.centralizer (Q : Set G) :=
      Subgroup.le_centralizer_iff.mp hQcentZ
    exact hcontra (hZcentQ (Subgroup.mem_zpowers c.t))
  let Good : Subgroup G → Prop := fun P =>
    IsPGroup p P ∧ P ≤ Q ∧ c.H ≤ Subgroup.normalizer (P : Set G) ∧
      ⁅P, Z⁆ ≠ ⊥
  have hGood : ∃ P : Subgroup G, Good P :=
    ⟨Q, hQp, le_rfl, hHQ, hQcomm⟩
  obtain ⟨P, hPmin⟩ :=
    exists_minimalFor_of_wellFoundedLT Good (fun R : Subgroup G => Nat.card R) hGood
  have hPp : IsPGroup p P := hPmin.prop.1
  have hPleQ : P ≤ Q := hPmin.prop.2.1
  have hHP : c.H ≤ Subgroup.normalizer (P : Set G) := hPmin.prop.2.2.1
  have hPcomm : ⁅P, Z⁆ ≠ ⊥ := hPmin.prop.2.2.2
  have hminimal : ∀ R : Subgroup G, R ≤ P →
      c.H ≤ Subgroup.normalizer (R : Set G) →
      ⁅R, Z⁆ ≠ ⊥ → P ≤ R := by
    intro R hRP hHR hRcomm
    by_contra hnot
    have hlt : R < P := lt_of_le_of_ne hRP (fun h => hnot h.ge)
    have hcardlt : Nat.card R < Nat.card P := by
      exact Set.Finite.card_lt_card (Set.toFinite (P : Set G)) hlt
    exact hPmin.not_lt ⟨hPp.to_le hRP, hRP.trans hPleQ, hHR, hRcomm⟩ hcardlt
  have hPodd : Nat.Coprime 2 (Nat.card P) := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn]
    exact (hpodd.pow).coprime_two_left
  have hcommP : ⁅P, Z⁆ = P := by
    simpa [Z] using commutator_zpowers_eq_self_of_minimal_invariant
      c.H P c.t_involution htH hHt hHP hPodd hPcomm hminimal
  have hNC :=
    normalizer_inf_qCoreOf_eq_self_and_centralizer_inf_qCoreOf_eq_self_of_minimal_invariant
      c.H P p hp hpodd c.t_involution htH hHt hHP hPp hPcomm hminimal
  have hPcentOH : P ≤ Subgroup.centralizer (qCoreOf c.H p : Set G) := by
    exact inf_eq_left.mp hNC.2
  have hPleHhat : P ≤ c.Hhat :=
    hPleQ.trans (qCoreOf_le c.Hhat p)
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply hPcomm
    simp [hbot]
  have hNne : Subgroup.normalizer (P : Set G) ≠ ⊤ := by
    intro hNtop
    have hPnormal : P.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ (minimalCounterexample_isSimple hmin) P hPnormal with
      hbot | htop
    · exact hPne hbot
    · have hHtop : c.Hhat = ⊤ := top_unique (htop ▸ hPleHhat)
      exact c.Hhat_maximal.ne_top hHtop
  obtain ⟨A, hAmax, hNA⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (P : Set G))).resolve_left hNne
  have hHA : c.H ≤ A := hHP.trans hNA
  let cA : CentralizerSetup G :=
    { c with
      Hhat := A
      H_le_Hhat := hHA
      Hhat_maximal := hAmax }
  have hclasses : HasAtLeastTwoInvolutionClasses A := by
    simpa [cA] using lemma_2_1 hmin cA
  obtain ⟨V, hVS, hV, hVescape⟩ :=
    exists_kleinFour_le_sylow_normalizer_not_le_of_two_involution_classes
      hmin cA A (by simpa [cA]) hclasses
  have hVP : V ≤ Subgroup.normalizer (P : Set G) := by
    exact hVS.trans ((centralizerSetup_S_le_H c).trans hHP)
  have htV : c.t ∈ V := by
    obtain ⟨e⟩ := c.dihedralEquiv
    let VS : Subgroup c.S := V.subgroupOf (c.S : Subgroup G)
    let eVS : VS ≃* V := Subgroup.subgroupOfEquivOfLe hVS
    have hVsub : IsKleinFour VS := {
      card_four := (Nat.card_congr eVS.toEquiv).trans hV.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eVS).trans hV.exponent_two
    }
    let tS : c.S := ⟨c.t, c.S0_le_S c.t_mem_S0⟩
    have htcenter : tS ∈ Subgroup.center c.S := by
      apply Subgroup.mem_center_iff.mpr
      intro x
      apply Subtype.ext
      have hxH : (x : G) ∈ c.H := centralizerSetup_S_le_H c x.property
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hxH
      exact hxH
    have htVS : tS ∈ VS :=
      center_mem_kleinFour_of_dihedral_mulEquiv c.one_le_m e VS hVsub htcenter
    exact htVS
  obtain ⟨s, hsV, hs1, hst, hscent⟩ :=
    exists_kleinFour_centralizer_not_le_of_commutator_eq_self
      hV hVP hPodd htV c.t_involution.1 hPne hcommP
  obtain ⟨g, hgNV, hgA, hgts⟩ :=
    exists_outside_normalizer_conjugating_t_to
      hmin c A V hHA hVS hV hVescape hsV hs1 hst htV
  let C : Subgroup G := centralizerIn P s
  let P0 : Subgroup G := ⁅C, Z⁆
  have hts : c.t * s = s * c.t := by
    have := (IsKleinFour.isMulCommutative (G := V)).is_comm.comm
      ⟨c.t, htV⟩ ⟨s, hsV⟩
    exact congrArg Subtype.val this
  have htPnorm : c.t ∈ Subgroup.normalizer (P : Set G) := hVP htV
  have htCnorm : c.t ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simp only [C, centralizerIn]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htPnorm
    have htCentS : c.t ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hts
    have htCentNorm : c.t ∈
        Subgroup.normalizer (Subgroup.centralizer ({s} : Set G) : Set G) :=
      Subgroup.le_normalizer htCentS
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htCentNorm
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c.t).injective,
      htPnorm, htCentNorm]
  have hZC : Z ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.zpowers_le.mpr htCnorm
  have hP0C : P0 ≤ C := by
    change ⁅C, Z⁆ ≤ C
    exact (Subgroup.le_normalizer_iff_commutator_le_left (H := Z) (K := C)).mp hZC
  have hP0P : P0 ≤ P := hP0C.trans (by
    intro x hx
    exact hx.1)
  have hP0ne : P0 ≠ ⊥ := by
    intro hbot
    apply hscent
    intro x hx
    have hcommbot : ⁅C, Z⁆ = ⊥ := by simpa [P0] using hbot
    have hxZ : x ∈ Subgroup.centralizer (Z : Set G) := by
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbot) hx
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer ({c.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hxZ c.t
      (Subgroup.mem_zpowers c.t)).symm
  have hCp : IsPGroup p C := by
    have hCP : C ≤ P := by
      intro x hx
      exact hx.1
    exact hPp.to_le hCP
  have hZcard : Nat.card Z = 2 := by
    have htord : orderOf c.t = 2 :=
      orderOf_eq_prime c.t_involution.2 c.t_involution.1
    simp [Z, Nat.card_zpowers, htord]
  have hZtwo : IsPGroup 2 Z := by
    refine IsPGroup.of_card (n := 1) ?_
    simp [hZcard]
  have hpne2 : p ≠ 2 := by
    intro heq
    subst p
    exact hpodd.not_two_dvd_nat (by norm_num)
  have hZCcop : Nat.Coprime (Nat.card Z) (Nat.card C) := by
    exact IsPGroup.coprime_card_of_ne 2 p hpne2.symm Z C hZtwo hCp
  have hP0self : ⁅P0, Z⁆ = P0 := by
    simpa [P0] using
      BenderSuzuki.ig1114_commutator_idempotent_of_coprime C Z hZCcop hZC
  have hPcoreA : P ≤ qCoreOf A p := by
    rw [← hcommP]
    apply commutator_le_qCoreOf_of_isDGroup A P p
      (properSubgroups_areDGroups hmin A hAmax.1) hp hpodd
      (P.le_normalizer.trans hNA) hPp (hHA htH) c.t_involution
    intro x hx
    apply hHP
    rw [c.H_eq_centralizer]
    exact hx.2
  have hAgt : IsCoatom (conjugateSubgroup A g) := by
    dsimp [conjugateSubgroup]
    exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup A).2 hAmax
  have hAgD : IsDGroup (conjugateSubgroup A g) :=
    properSubgroups_areDGroups hmin (conjugateSubgroup A g) hAgt.1
  have hHgproper : conjugateSubgroup c.H g ≠ ⊤ := by
    intro htop
    apply hAgt.1
    apply top_unique
    rw [← htop]
    exact Subgroup.map_mono hHA
  have hHgD : IsDGroup (conjugateSubgroup c.H g) :=
    properSubgroups_areDGroups hmin (conjugateSubgroup c.H g) hHgproper
  have hCentSleHg : Subgroup.centralizer ({s} : Set G) ≤
      conjugateSubgroup c.H g := by
    intro x hx
    have hgst : g⁻¹ * s * g = c.t := by
      rw [← hgts]
      group
    have hyH : g⁻¹ * x * g ∈ c.H := by
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      have hxs := Subgroup.mem_centralizer_singleton_iff.mp hx
      calc
        (g⁻¹ * x * g) * c.t = g⁻¹ * (x * s) * g := by rw [← hgst]; group
        _ = g⁻¹ * (s * x) * g := by rw [hxs]
        _ = c.t * (g⁻¹ * x * g) := by rw [← hgst]; group
    change x ∈ c.H.map (MulAut.conj g).toMonoidHom
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hyH, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group
  have hCleHg : C ≤ conjugateSubgroup c.H g := by
    intro x hx
    exact hCentSleHg hx.2
  have hCleAg : C ≤ conjugateSubgroup A g :=
    hCleHg.trans (Subgroup.map_mono hHA)
  have htAg : c.t ∈ conjugateSubgroup A g := by
    have hgInvN : g⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer (V : Set G)).inv_mem hgNV
    have hgtV : g⁻¹ * c.t * g ∈ V :=
      by simpa using (Subgroup.mem_normalizer_iff.mp hgInvN c.t).1 htV
    change c.t ∈ A.map (MulAut.conj g).toMonoidHom
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * c.t * g, ?_, ?_⟩
    · exact hHA (centralizerSetup_S_le_H c (hVS hgtV))
    · change g * (g⁻¹ * c.t * g) * g⁻¹ = c.t
      group
  have htHg : c.t ∈ conjugateSubgroup c.H g := by
    have hgInvN : g⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer (V : Set G)).inv_mem hgNV
    have hgtV : g⁻¹ * c.t * g ∈ V :=
      by simpa using (Subgroup.mem_normalizer_iff.mp hgInvN c.t).1 htV
    change c.t ∈ c.H.map (MulAut.conj g).toMonoidHom
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * c.t * g, ?_, ?_⟩
    · exact centralizerSetup_S_le_H c (hVS hgtV)
    · change g * (g⁻¹ * c.t * g) * g⁻¹ = c.t
      group
  have hP0Hg : P0 ≤ conjugateSubgroup c.H g := by
    exact hP0C.trans hCleHg
  have hP0Ag : P0 ≤ conjugateSubgroup A g :=
    hP0Hg.trans (Subgroup.map_mono hHA)
  have hP0core : P0 ≤ qCoreOf (conjugateSubgroup A g) p := by
    apply commutator_le_qCoreOf_via_invariant_closure
      (B := conjugateSubgroup A g) (P := P) P0 p hAgD hp hpodd
      hP0Ag hPp htAg c.t_involution (by
        intro x hx
        apply hHP
        rw [c.H_eq_centralizer]
        exact hx.2) hP0P hP0self
  have hqCoreConj : qCoreOf (conjugateSubgroup c.H g) p =
      (qCoreOf c.H p).map (MulAut.conj g).toMonoidHom :=
    qCoreOf_conjugateSubgroup c.H g p
  have hP0coreHg : P0 ≤ qCoreOf (conjugateSubgroup c.H g) p := by
    apply commutator_le_qCoreOf_via_invariant_closure
      (B := conjugateSubgroup c.H g) (P := P) P0 p
      hHgD hp hpodd hP0Hg hPp
      htHg c.t_involution (by
        intro x hx
        apply hHP
        rw [c.H_eq_centralizer]
        exact hx.2) hP0P hP0self
  let Pg : Subgroup G := P.map (MulAut.conj g).toMonoidHom
  have hPgP : IsPGroup p Pg := hPp.map (MulAut.conj g).toMonoidHom
  have hPgAg : Pg ≤ conjugateSubgroup A g :=
    Subgroup.map_mono (P.le_normalizer.trans hNA)
  have hPgNe : Pg ≠ ⊥ := by
    intro hbot
    apply hPne
    apply (MulAut.conj g).mapSubgroup.injective
    simpa [Pg, hbot]
  have hP0centPg : P0 ≤ Subgroup.centralizer (Pg : Set G) := by
    intro x hxP0 y hyPg
    have hxCore : x ∈ (qCoreOf c.H p).map (MulAut.conj g).toMonoidHom := by
      rw [← hqCoreConj]
      exact hP0coreHg hxP0
    rcases Subgroup.mem_map.mp hxCore with ⟨x0, hx0, rfl⟩
    rcases Subgroup.mem_map.mp hyPg with ⟨y0, hy0, rfl⟩
    change g * y0 * g⁻¹ * (g * x0 * g⁻¹) =
      g * x0 * g⁻¹ * (g * y0 * g⁻¹)
    have hcomm := Subgroup.mem_centralizer_iff.mp (hPcentOH hy0) x0 hx0
    calc
      g * y0 * g⁻¹ * (g * x0 * g⁻¹) = g * (y0 * x0) * g⁻¹ := by group
      _ = g * (x0 * y0) * g⁻¹ := by rw [← hcomm]
      _ = g * x0 * g⁻¹ * (g * y0 * g⁻¹) := by group
  have hPgNormP0 : Pg ≤ Subgroup.normalizer (P0 : Set G) :=
    (Subgroup.le_centralizer_iff.mp hP0centPg).trans
      (Subgroup.centralizer_le_normalizer (P0 : Set G))
  have hNP0neTop : Subgroup.normalizer (P0 : Set G) ≠ ⊤ := by
    intro htop
    have hP0normal : P0.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ (minimalCounterexample_isSimple hmin) P0 hP0normal with
      hbot | htopP0
    · exact hP0ne hbot
    · apply hAgt.1
      exact top_unique (htopP0 ▸ hP0Ag)
  obtain ⟨M, hMmax, hNP0M⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (P0 : Set G))).resolve_left
      hNP0neTop
  have hPgM : Pg ≤ M := hPgNormP0.trans hNP0M
  have hsNormP0 : s ∈ Subgroup.normalizer (P0 : Set G) := by
    apply Subgroup.centralizer_le_normalizer (P0 : Set G)
    intro x hx
    have hxs := Subgroup.mem_centralizer_singleton_iff.mp (hP0C hx).2
    exact hxs
  have hsM : s ∈ M := hNP0M hsNormP0
  have hHgNormPg : conjugateSubgroup c.H g ≤
      Subgroup.normalizer (Pg : Set G) := by
    exact (Subgroup.map_mono hHP).trans
      (Subgroup.le_normalizer_map (f := (MulAut.conj g).toMonoidHom))
  have hMinvPg : M ⊓ Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer (Pg : Set G) := by
    intro x hx
    exact hHgNormPg (hCentSleHg hx.2)
  let Zs : Subgroup G := Subgroup.zpowers s
  have hmapZ : Z.map (MulAut.conj g).toMonoidHom = Zs := by
    simp [Z, Zs, MonoidHom.map_zpowers, hgts]
  have hPgself : ⁅Pg, Zs⁆ = Pg := by
    have hmap := congrArg
      (fun K : Subgroup G => K.map (MulAut.conj g).toMonoidHom) hcommP
    rw [Subgroup.map_commutator, hmapZ] at hmap
    simpa [Pg] using hmap
  have hsInv : IsInvolution s := by
    constructor
    · intro hsone
      apply c.t_involution.1
      calc
        c.t = g⁻¹ * s * g := by rw [← hgts]; group
        _ = 1 := by rw [hsone]; simp
    · rw [← hgts]
      calc
        (g * c.t * g⁻¹) ^ 2 = g * (c.t * c.t) * g⁻¹ := by rw [pow_two]; group
        _ = g * (c.t ^ 2) * g⁻¹ := by rw [pow_two]
        _ = 1 := by rw [c.t_involution.2]; simp
  have hPgCoreM : Pg ≤ qCoreOf M p := by
    rw [← hPgself]
    exact commutator_le_qCoreOf_of_isDGroup M Pg p
      (properSubgroups_areDGroups hmin M hMmax.1) hp hpodd
      hPgM hPgP hsM hsInv hMinvPg
  have hNPgAg : Subgroup.normalizer (Pg : Set G) ≤ conjugateSubgroup A g := by
    calc
      Subgroup.normalizer (Pg : Set G) =
          (Subgroup.normalizer (P : Set G)).map
            (MulAut.conj g).toMonoidHom := by
              symm
              exact Subgroup.map_normalizer_eq_of_bijective P
                (MulAut.conj g).bijective
      _ ≤ A.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hNA
      _ = conjugateSubgroup A g := rfl
  have hMtoAg : NormalizerControlledBy M (conjugateSubgroup A g) :=
    ⟨Pg, hPgNe,
      hPgCoreM.trans (qCoreOf_le_fittingSubgroupOf M p hp), hNPgAg⟩
  have hAgtoM : NormalizerControlledBy (conjugateSubgroup A g) M :=
    ⟨P0, hP0ne,
      hP0core.trans (qCoreOf_le_fittingSubgroupOf (conjugateSubgroup A g) p hp),
      hNP0M⟩
  have hAtoM : NormalizerControlledBy A M :=
    ⟨P0, hP0ne,
      hP0P.trans (hPcoreA.trans (qCoreOf_le_fittingSubgroupOf A p hp)),
      hNP0M⟩
  have hMeqAg : M = conjugateSubgroup A g := by
    rcases lemma_2_3_of_controlCore (minimalCounterexample_isSimple hmin)
      hMmax hAgt (controlCore_of_normalizerControlledBy hMtoAg)
      (controlCore_of_normalizerControlledBy hAgtoM) with hEq | hPgroups
    · exact hEq
    · rcases hPgroups with ⟨r, hr, hMr, hAgr⟩
      have hrne2 : r ≠ 2 := by
        intro hre
        subst r
        have hPgF : Pg ≤ generalizedFittingSubgroupOf M :=
          hPgCoreM.trans (qCoreOf_le_fittingSubgroupOf M p hp) |>.trans le_sup_left
        have hcop : Nat.Coprime (Nat.card Pg)
            (Nat.card (generalizedFittingSubgroupOf M)) :=
          IsPGroup.coprime_card_of_ne p 2 hpne2 Pg
            (generalizedFittingSubgroupOf M) hPgP hMr
        have hdisj : Disjoint Pg (generalizedFittingSubgroupOf M) :=
          Subgroup.disjoint_of_coprime_natCard hcop
        apply hPgNe
        exact bot_unique ((le_inf le_rfl hPgF).trans hdisj.le_bot)
      exact lemma_2_4 hmin hMmax hAgt hMtoAg hr (hr.odd_of_ne_two hrne2)
        hMr hAgr
  have hAtoAg : NormalizerControlledBy A (conjugateSubgroup A g) := by
    rw [← hMeqAg]
    exact hAtoM
  have hqCoreOdd : qCoreOf A p ≤ oddCoreOf A := by
    change (pCore p A).map A.subtype ≤ (pPrimeCore 2 A).map A.subtype
    apply Subgroup.map_mono
    have hcop : Nat.Coprime 2 (Nat.card (pCore p A)) := by
      obtain ⟨n, hn⟩ := (pCore_isPGroup (G := A) (p := p)).exists_card_eq
      rw [hn]
      exact hpodd.coprime_two_left.pow_right n
    exact le_sSup
      (show pCore p A ∈
          {K : Subgroup A | K.Normal ∧ Nat.Coprime 2 (Nat.card K)} from
        ⟨inferInstance, hcop⟩)
  have hoddA : oddCoreOf A ≠ ⊥ := by
    intro hbot
    apply hPne
    apply le_bot_iff.mp
    exact hPcoreA.trans (hqCoreOdd.trans (by rw [hbot]))
  have hAeqAg : A = conjugateSubgroup A g := by
    simpa [cA] using lemma_2_5 hmin cA g hAtoAg hoddA
  have hAne : A ≠ ⊥ := by
    intro hbot
    have : c.t ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hHA htH
    exact c.t_involution.1 (by simpa using this)
  have hNormA : Subgroup.normalizer (A : Set G) = A :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) hAmax le_rfl hAne
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_rfl).mpr A.le_normalizer)
  apply hgA
  rw [← hNormA, Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hAeqAg.symm

end CFSG.GorensteinWalter

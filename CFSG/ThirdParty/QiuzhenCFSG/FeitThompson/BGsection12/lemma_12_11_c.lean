module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_11_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_11_c
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section12_normalizer_ne_top_of_ne_bot_ne_top
    {Q : Subgroup G} (hQ_ne_bot : Q ≠ ⊥) (hQ_ne_top : Q ≠ ⊤) :
    Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
  intro hNtop
  have hQnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  let : IsSimpleGroup G := IsMinCE.simple
  rcases hQnormal.eq_bot_or_eq_top with hQbot | hQtop
  · exact hQ_ne_bot hQbot
  · exact hQ_ne_top hQtop

public theorem CFSG.section12_primeOrder_ne_top
    {A X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A) :
    X ≠ ⊤ := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨_hXA, hXcard⟩
  intro htop
  have hGcard : Nat.card G = p.val := by
    simpa [htop] using hXcard
  have : Fact p.val.Prime := ⟨p.2⟩
  have : IsCyclic G := by
    exact isCyclic_of_prime_card (α := G) (p := p.val) hGcard
  have hsolv : Group.IsSolvable G := by infer_instance
  exact IsMinCE.not_solvable (G := G) hsolv


omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_normalizer_le_normalizer_centralizer
    (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have ha' : n⁻¹ * a * n ∈ A :=
      (Subgroup.mem_normalizer_iff''.mp hn a).1 ha
    have hcomm : (n⁻¹ * a * n) * c = c * (n⁻¹ * a * n) := hc (n⁻¹ * a * n) ha'
    calc
      a * (n * c * n⁻¹) = n * ((n⁻¹ * a * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * c * n⁻¹) * a := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have ha' : n * a * n⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hn a).1 ha
    have hcomm :
        (n * a * n⁻¹) * (n * c * n⁻¹) =
          (n * c * n⁻¹) * (n * a * n⁻¹) :=
      hc (n * a * n⁻¹) ha'
    calc
      a * c = n⁻¹ * ((n * a * n⁻¹) * (n * c * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * c * n⁻¹) * (n * a * n⁻¹)) * n := by rw [hcomm]
      _ = c * a := by group

/-- Lemma 12.11(c). -/
public theorem CFSG.lemma_12_11_c
    {M E E₁₂ E₁ E₂ E₃ A Mstar : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A : Set G)))
    (hqQuot : q ∈ section12QuotientPrimeSet (subgroupCentralizerIn E A) E)
    (hqCent : q ∈ subgroupPrimeSet (subgroupCentralizerIn E A)) :
    q ∈ section12Tau2Primes Mstar ∧
      (∃ P : Sylow p.val G, section10NormalIn (P : Subgroup G) Mstar) ∧
        ∃ Q : Sylow q.val G, (Q : Subgroup G) ≤ Mstar ∧
          IsMulCommutative (Q : Subgroup G) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn E A
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hp_data :=
    (lemma_12_11_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (Mstar := Mstar)
      (p := p) hM hE hp hA hMstar) hp
  have hpσstar : p ∈ section10SigmaPrimes Mstar := hp_data.1
  have hp_not_beta_star : p ∉ section10BetaPrimes Mstar := hp_data.2
  have hC_quot_tau :
      q ∈ section12Tau1Primes Mstar ∪ section12Tau2Primes Mstar :=
    (lemma_12_11_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (Mstar := Mstar)
      (p := p) hM hE hp hA hMstar) hqQuot
  have hqτ1M : q ∈ section12Tau1Primes M :=
    (corollary_12_10_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).2.2 hqQuot
  have hCGA_le_E : Subgroup.centralizer (A : Set G) ≤ E := by
    have h6 :=
      corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
    intro x hx
    simpa [h6.2.1] using h6.1 hx
  have hC_eq_CGA : C = Subgroup.centralizer (A : Set G) := by
    apply le_antisymm
    · simp [C, subgroupCentralizerIn]
    · intro x hx
      exact ⟨hCGA_le_E hx, hx⟩
  have hC_le_E : C ≤ E := by
    simp [C, subgroupCentralizerIn]
  have hC_le_M : C ≤ M := hC_le_E.trans hE.1.2.1
  have hqC : q ∈ subgroupPrimeSet C := by simpa [C] using hqCent
  have hqrankC_le_one : primeRank q.val C ≤ 1 := by
    let eC : C.subgroupOf M ≃* C := Subgroup.subgroupOfEquivOfLe hC_le_M
    have hqrankC_le_Csub : primeRank q.val C ≤ primeRank q.val (C.subgroupOf M) :=
      section12_primeRank_le_of_equiv (R := C.subgroupOf M) (S := C) q.val eC
    have hqrankCsub_le_M : primeRank q.val (C.subgroupOf M) ≤ primeRank q.val M := by
      exact section8_primeRank_le_of_subgroup (G := M) (C.subgroupOf M) q.val
    have hqrankC_le_M : primeRank q.val C ≤ primeRank q.val M :=
      hqrankC_le_Csub.trans hqrankCsub_le_M
    simpa [hqτ1M.2.2] using hqrankC_le_M.trans (le_of_eq hqτ1M.2.2)
  have : Fact q.val.Prime := ⟨q.2⟩
  have hqG_dvd : q.val ∣ Nat.card G :=
    hqC.trans ((Subgroup.card_dvd_of_le hC_le_M).trans (Subgroup.card_subgroup_dvd_card M))
  have hq_odd : q.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hqG_dvd
  obtain ⟨z, hz_order⟩ := exists_prime_orderOf_dvd_card' (G := C) q.val hqC
  let Q0 : Subgroup G := Subgroup.zpowers (z : G)
  have hQ0_le_C : Q0 ≤ C := Subgroup.zpowers_le.2 z.property
  have hQ0_primeOrder : Q0 ∈ section10PrimeOrderSubgroupsIn q C := by
    refine ⟨hQ0_le_C, ?_⟩
    dsimp [Q0]
    rw [Nat.card_zpowers]
    simpa [Subgroup.orderOf_coe] using hz_order
  have hQ0_ne_bot : Q0 ≠ ⊥ :=
    section12_primeOrder_ne_bot (G := G) (A := C) (X := Q0) (p := q) hQ0_primeOrder
  have hQ0_ne_top : Q0 ≠ ⊤ :=
    section12_primeOrder_ne_top (G := G) (A := C) (X := Q0) (p := q) hQ0_primeOrder
  have hNQ0_ne_top : Subgroup.normalizer (Q0 : Set G) ≠ ⊤ :=
    section12_normalizer_ne_top_of_ne_bot_ne_top hQ0_ne_bot hQ0_ne_top
  have hQ0_p : IsPGroup q.val Q0 := by
    refine IsPGroup.of_card (p := q.val) (G := Q0) (n := 1) ?_
    simpa [pow_one] using hQ0_primeOrder.2
  let Q0C : Subgroup C := Q0.subgroupOf C
  have hQ0C_p : IsPGroup q.val Q0C :=
    hQ0_p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Q0) (K := C) hQ0_le_C).symm
  obtain ⟨R, hQ0C_le_R⟩ := IsPGroup.exists_le_sylow (G := C) (p := q.val) hQ0C_p
  have hR_cyc : IsCyclic (R : Subgroup C) :=
    section12_sylow_cyclic_of_primeRank_le_one hq_odd hqrankC_le_one R
  let RG : Subgroup G := (R : Subgroup C).map C.subtype
  have hQ0_le_RG : Q0 ≤ RG := by
    intro x hxQ0
    let xC : C := ⟨x, hQ0_le_C hxQ0⟩
    have hxQ0C : xC ∈ Q0C := by
      simpa [Q0C, Subgroup.mem_subgroupOf] using hxQ0
    exact Subgroup.mem_map.mpr ⟨xC, hQ0C_le_R hxQ0C, rfl⟩
  have hRG_cyc : IsCyclic RG := by
    let eR : (R : Subgroup C) ≃* RG :=
      Subgroup.equivMapOfInjective (f := C.subtype) (R : Subgroup C) C.subtype_injective
    exact eR.isCyclic.mp hR_cyc
  have : IsCyclic RG := hRG_cyc
  have hQ0_char : (Q0.subgroupOf RG).Characteristic :=
    section12_subgroup_characteristic_of_cyclic (Q0.subgroupOf RG)
  have hNormRG_le_NormQ0 :
      Subgroup.normalizer (RG : Set G) ≤ Subgroup.normalizer (Q0 : Set G) := by
    have hle :
        Subgroup.normalizer (RG : Set G) ≤
          Subgroup.normalizer ((Q0.subgroupOf RG).map RG.subtype : Set G) := by
      exact section8_normalizer_map_subtype_le_of_characteristic
        (H := RG) (K := Q0.subgroupOf RG)
    have hmap_eq : (Q0.subgroupOf RG).map RG.subtype = Q0 :=
      Subgroup.map_subgroupOf_eq_of_le hQ0_le_RG
    simpa [hmap_eq] using hle
  have hA_le_CQ0 : A ≤ Subgroup.centralizer (Q0 : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxCent : x ∈ Subgroup.centralizer (A : Set G) := by
      rw [← hC_eq_CGA]
      exact hQ0_le_C hx
    exact (Subgroup.mem_centralizer_iff.mp hxCent a ha).symm
  have hA_le_NQ0 : A ≤ Subgroup.normalizer (Q0 : Set G) :=
    hA_le_CQ0.trans (centralizer_le_normalizer Q0)
  obtain ⟨Mtwo, hMtwoQ0⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top (G := G) hNQ0_ne_top
  have hA_Mtwo : A ∈ section12RankTwoElementaryAbelianIn p Mtwo := by
    exact ⟨hA_le_NQ0.trans hMtwoQ0.2, section12_rankTwo_elementary hA⟩
  have hCGA_le_Mtwo : Subgroup.centralizer (A : Set G) ≤ Mtwo :=
    proposition_12_4_a (G := G) (M := Mtwo) (A := A) (p := p) hMtwoQ0.1 hA_Mtwo
  have hH_le_Mtwo : Subgroup.normalizer (A : Set G) ≤ Mtwo := by
    let H : Subgroup G := Subgroup.normalizer (A : Set G)
    have hC_le_H : C ≤ H := by
      rw [hC_eq_CGA]
      exact centralizer_le_normalizer A
    let CH : Subgroup H := C.subgroupOf H
    let eCH : CH ≃* C := Subgroup.subgroupOfEquivOfLe hC_le_H
    let RH : Sylow q.val CH :=
      Sylow.mapSurjective (f := eCH.symm.toMonoidHom) eCH.symm.surjective R
    have : CH.Normal := by
      have hH_norm_C :
          H ≤ Subgroup.normalizer (C : Set G) := by
            rw [hC_eq_CGA]
            exact section12_normalizer_le_normalizer_centralizer (G := G) A
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_H).2 hH_norm_C
    have hFr : Subgroup.normalizer (((RH : Subgroup CH).map CH.subtype) : Set H) ⊔ CH = ⊤ := by
      have h := Sylow.normalizer_sup_eq_top (G := H) (N := CH) RH
      simpa using h
    let RHG : Subgroup H := (RH : Subgroup CH).map CH.subtype
    have hCH_map_eq : CH.map H.subtype = C := by
      simpa [CH, H] using
        (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := C) (K := H) hC_le_H)
    have hCH_map_le_Mtwo : CH.map H.subtype ≤ Mtwo := by
      simpa [hCH_map_eq] using (show C ≤ Mtwo by rw [hC_eq_CGA]; exact hCGA_le_Mtwo)
    have hRHG_map_eq : RHG.map H.subtype = RG := by
      have hcomp_eq :
          H.subtype.comp (CH.subtype.comp eCH.symm.toMonoidHom) = C.subtype := by
        ext x
        rfl
      calc
        RHG.map H.subtype =
            (((R : Subgroup C).map eCH.symm.toMonoidHom).map
              CH.subtype).map H.subtype := by
              simp [RHG, RH]
        _ = (R : Subgroup C).map
              ((H.subtype.comp CH.subtype).comp eCH.symm.toMonoidHom) := by
              rw [Subgroup.map_map, Subgroup.map_map]
        _ = (R : Subgroup C).map
              (H.subtype.comp (CH.subtype.comp eCH.symm.toMonoidHom)) := by
              rfl
        _ = (R : Subgroup C).map C.subtype := by
              rw [hcomp_eq]
        _ = RG := by
              rfl
    have hnormRHG_map_le_Mtwo :
        (Subgroup.normalizer (RHG : Set H)).map H.subtype ≤ Mtwo := by
      intro x hx
      have hxNormAmbient :
          x ∈ Subgroup.normalizer (RG : Set G) := by
        have hxMap :
            x ∈ (Subgroup.normalizer (RHG : Set H)).map H.subtype := hx
        have hxAmbient :
            x ∈ Subgroup.normalizer (section8SubgroupInAmbient RHG : Set G) :=
          section8_normalizer_subgroupInAmbient_le (G := G) (H := H) (K := RHG) hxMap
        simpa [section8SubgroupInAmbient, hRHG_map_eq] using hxAmbient
      exact hMtwoQ0.2 (hNormRG_le_NormQ0 hxNormAmbient)
    intro x hxH
    let xH : H := ⟨x, hxH⟩
    have hxTop : xH ∈ Subgroup.normalizer (RHG : Set H) ⊔ CH := by
      rw [hFr]
      exact trivial
    rcases (Subgroup.mem_sup_of_normal_right
        (s := Subgroup.normalizer (RHG : Set H)) (t := CH) (x := xH)).1 hxTop with
      ⟨n, hnNorm, c, hcC, hnc⟩
    have hnMap :
        ((n : H) : G) ∈ (Subgroup.normalizer (RHG : Set H)).map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype hnNorm
    have hnMtwo : ((n : H) : G) ∈ Mtwo := hnormRHG_map_le_Mtwo hnMap
    have hcMap : ((c : H) : G) ∈ CH.map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype hcC
    have hcMtwo : ((c : H) : G) ∈ Mtwo := hCH_map_le_Mtwo hcMap
    have hx_eq : ((n : H) : G) * ((c : H) : G) = x := by
      simpa [xH] using congrArg H.subtype hnc
    rw [← hx_eq]
    exact Mtwo.mul_mem hnMtwo hcMtwo
  have hMtwoA :
      Mtwo ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) :=
    ⟨hMtwoQ0.1, hH_le_Mtwo⟩
  have hqτ2two : q ∈ section12Tau2Primes Mtwo := by
    have hqσ_or_τ2 :
        q ∈ section10SigmaPrimes Mtwo ∪ section12Tau2Primes Mtwo :=
      lemma_12_2_a (G := G) (M := M) (Mstar := Mtwo) (X := Q0) (p := q)
        hM hQ0_p hQ0_ne_bot (hQ0_le_C.trans hC_le_M) hMtwoQ0
    have hqτ12 :
        q ∈ section12Tau1Primes Mtwo ∪ section12Tau2Primes Mtwo :=
      (lemma_12_11_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (Mstar := Mtwo)
        (p := p) hM hE hp hA hMtwoA) hqQuot
    rcases hqσ_or_τ2 with hqσtwo | hqτ2two
    · rcases hqτ12 with hqτ1two | hqτ2two
      · exact False.elim
          ((section12_tau13_not_sigma (M := Mtwo) (p := q) (Or.inl hqτ1two)) hqσtwo)
      · exact hqτ2two
    · exact hqτ2two
  have hAp : IsPGroup p.val A := by
    have hElem := (section12_rankTwo_elementary hA_M).2
    have : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  have hp_data_two :=
    (lemma_12_11_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (Mstar := Mtwo)
      (p := p) hM hE hp hA hMtwoA) hp
  have hpσtwo : p ∈ section10SigmaPrimes Mtwo := hp_data_two.1
  have hqrank_two : 2 ≤ primeRank q.val Mtwo := by
    simp [hqτ2two.2]
  obtain ⟨Bqsub, hBqsub_p, hBqsub_comm, hBqsub_gen⟩ :=
    section12_exists_pSubgroup_two_le_generatorRank_of_two_le_primeRank
      (p := q.val) (R := Mtwo) hqrank_two
  have hBqsub_noncyc : ¬ IsCyclic Bqsub := by
    intro hBqsub_cyc
    have hle : generatorRank Bqsub ≤ 1 :=
      generatorRank_le_one_of_isCyclic (G := Bqsub) hBqsub_cyc
    omega
  let Sq : Sylow q.val Mtwo := Classical.choice (Sylow.nonempty (p := q.val) (G := Mtwo))
  have hSq_noncyc : ¬ IsCyclic (Sq : Subgroup Mtwo) := by
    intro hSq_cyc
    have hqrank_le_one :
        primeRank q.val Mtwo ≤ 1 :=
      section12_primeRank_le_one_of_cyclic_sylow (p := q.val) (R := Mtwo) Sq hSq_cyc
    omega
  let SqG : Subgroup G := section10AmbientSylowSubgroup Mtwo Sq
  have hSqG_p : IsPGroup q.val SqG := by
    change IsPGroup q.val ((Sq : Subgroup Mtwo).map Mtwo.subtype)
    exact IsPGroup.map Sq.isPGroup' Mtwo.subtype
  have hSqG_le_Mtwo : SqG ≤ Mtwo := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hSqG_noncyc : ¬ IsCyclic SqG := by
    intro hSqG_cyc
    let eSq : (Sq : Subgroup Mtwo) ≃* SqG :=
      Subgroup.equivMapOfInjective (f := Mtwo.subtype) (Sq : Subgroup Mtwo)
        Mtwo.subtype_injective
    exact hSq_noncyc (eSq.isCyclic.mpr hSqG_cyc)
  obtain ⟨Bq, hBq_SqG⟩ :=
    section12_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := SqG) (p := q) hSqG_p hSqG_noncyc
  have hBq_Mtwo : Bq ∈ section12RankTwoElementaryAbelianIn q Mtwo :=
    section12_rankTwo_mono hBq_SqG hSqG_le_Mtwo
  have hnilMtwo : Group.IsNilpotent (section10Msigma Mtwo) :=
    theorem_12_5_a (G := G) (M := Mtwo) (A := Bq) (p := q)
      hMtwoQ0.1 hqτ2two hBq_Mtwo
  have hMtwo_eq_Mstar : Mtwo = Mstar := by
    by_contra hMtwo_ne
    have hnotconj : section12NotConjugate Mstar Mtwo :=
      lemma_12_2_b (G := G) (M := Mtwo) (Mstar := Mstar) (X := A) (p := p)
        hMtwoQ0.1 hAp (section12_rankTwo_ne_bot hA_Mtwo)
        (section12_rankTwo_le hA_Mtwo) hMstar (Or.inl ⟨hpσtwo, hMtwo_ne⟩)
    have hσdis :
        Disjoint (section10SigmaPrimes Mtwo) (section10SigmaPrimes Mstar) :=
      (lemma_10_12_b (G := G) (M := Mtwo) (H := Mstar)
        hMtwoQ0.1 hMstar.1 hnotconj hnilMtwo).2
    exact (Set.disjoint_left.mp hσdis) hpσtwo hpσstar
  have hqτ2star : q ∈ section12Tau2Primes Mstar := by
    simpa [hMtwo_eq_Mstar] using hqτ2two
  have hBq_Mstar : Bq ∈ section12RankTwoElementaryAbelianIn q Mstar := by
    simpa [hMtwo_eq_Mstar] using hBq_Mtwo
  have hnilMstar : Group.IsNilpotent (section10Msigma Mstar) := by
    exact theorem_12_5_a (G := G) (M := Mstar) (A := Bq) (p := q)
      hMstar.1 hqτ2star hBq_Mstar
  refine ⟨hqτ2star, ?_, ?_⟩
  · have : Fact p.val.Prime := ⟨p.2⟩
    have hσ_le_Mstar : section10Msigma Mstar ≤ Mstar := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    let Sσ : Subgroup Mstar := (section10Msigma Mstar).subgroupOf Mstar
    let eσ : Sσ ≃* section10Msigma Mstar :=
      Subgroup.subgroupOfEquivOfLe
        (H := section10Msigma Mstar) (K := Mstar) hσ_le_Mstar
    have hnilSσ : Group.IsNilpotent Sσ :=
      Group.nilpotent_of_mulEquiv (G := section10Msigma Mstar) (G' := Sσ) eσ.symm
    let Pσ : Sylow p.val Sσ := Classical.choice (Sylow.nonempty (p := p.val) (G := Sσ))
    have hPσ_norm : (Pσ : Subgroup Sσ).Normal := by
      let : Group.IsNilpotent Sσ := hnilSσ
      exact Group.IsNilpotent.sylow_normal hnilSσ p.val Pσ
    have hHallσ : IsHallSubgroup (section10SigmaPrimes Mstar) Sσ := by
      simpa [Sσ, section12Msigma_subgroupOf_eq] using
        (theorem_10_2_b (G := G) hMstar.1).2
    let PsubMstar : Subgroup Mstar := (Pσ : Subgroup Sσ).map Sσ.subtype
    have hPsubMstar_p : IsPGroup p.val PsubMstar := by
      exact IsPGroup.map (p := p.val) (H := (Pσ : Subgroup Sσ)) Pσ.isPGroup' Sσ.subtype
    have hp_not_Sσ_index : ¬ p.val ∣ Sσ.index := by
      intro hp_dvd
      exact (hHallσ.p_in_pi_of_p_dvd_index p hp_dvd) hpσstar
    have hp_not_PsubMstar_index : ¬ p.val ∣ PsubMstar.index := by
      intro hp_dvd
      have hidx : PsubMstar.index = (Pσ : Subgroup Sσ).index * Sσ.index := by
        simpa [PsubMstar] using
          (Subgroup.index_map_subtype (H := Sσ) (K := (Pσ : Subgroup Sσ)))
      have hp_prod : p.val ∣ (Pσ : Subgroup Sσ).index * Sσ.index := by
        simpa [hidx] using hp_dvd
      rcases p.2.dvd_or_dvd hp_prod with hp_Pσ | hp_Sσ
      · exact Pσ.not_dvd_index hp_Pσ
      · exact hp_not_Sσ_index hp_Sσ
    let Pstar : Sylow p.val Mstar := hPsubMstar_p.toSylow hp_not_PsubMstar_index
    have hPstar_eq : (Pstar : Subgroup Mstar) = PsubMstar := by
      simp [Pstar, IsPGroup.toSylow_coe]
    have hPσ_char : (Pσ : Subgroup Sσ).Characteristic :=
      Sylow.characteristic_of_normal Pσ hPσ_norm
    have hnormSσ_eq_top : Subgroup.normalizer (Sσ : Set Mstar) = ⊤ := by
      simpa [Sσ, section12Msigma_subgroupOf_eq] using
        (Subgroup.normalizer_eq_top_iff.mpr (section10MsigmaSubgroup_normal (M := Mstar)))
    have hnormPsub_le :
        Subgroup.normalizer (Sσ : Set Mstar) ≤
          Subgroup.normalizer (PsubMstar : Set Mstar) := by
      simpa [PsubMstar] using
        (section8_normalizer_map_subtype_le_of_characteristic
          (G := Mstar) (H := Sσ) (K := (Pσ : Subgroup Sσ)))
    have hPsubMstar_norm : PsubMstar.Normal := by
      have hnormPsub_eq_top :
          Subgroup.normalizer (PsubMstar : Set Mstar) = ⊤ := by
        apply top_unique
        simpa [hnormSσ_eq_top] using hnormPsub_le
      exact Subgroup.normalizer_eq_top_iff.mp hnormPsub_eq_top
    have hPstar_norm : (Pstar : Subgroup Mstar).Normal := by
      simpa [hPstar_eq] using hPsubMstar_norm
    have hPG_le_Mstar : section10AmbientSylowSubgroup Mstar Pstar ≤ Mstar := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hPGsub_eq :
        (section10AmbientSylowSubgroup Mstar Pstar).subgroupOf Mstar =
          (Pstar : Subgroup Mstar) := by
      ext x
      constructor
      · intro hx
        change ((x : Mstar) : G) ∈ section10AmbientSylowSubgroup Mstar Pstar at hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
        have hxy : y = x := by
          exact Subtype.ext hyx
        simpa [hxy] using hy
      · intro hx
        change ((x : Mstar) : G) ∈ section10AmbientSylowSubgroup Mstar Pstar
        exact Subgroup.mem_map_of_mem Mstar.subtype hx
    have hnormPG_le_Mstar :
        Subgroup.normalizer
            ((section10AmbientSylowSubgroup Mstar Pstar : Subgroup G) : Set G) ≤
          Mstar := by
      intro g hg
      refine theorem_10_1_d (G := G) (M := Mstar) (p := p) hMstar.1 hpσstar Pstar ?_
      intro x hx
      rw [Subgroup.conjBy, Subgroup.mem_map] at hx
      rcases hx with ⟨y, hy, rfl⟩
      exact hPG_le_Mstar ((Subgroup.mem_normalizer_iff.mp hg y).1 hy)
    rcases section8SubgroupInAmbient_sylow_of_normalizer_le
        (G := G) (p := p.val) (M := Mstar) Pstar hnormPG_le_Mstar with
      ⟨P, hP_eq⟩
    refine ⟨P, ?_⟩
    have hP_eq' : (P : Subgroup G) = section10AmbientSylowSubgroup Mstar Pstar := by
      simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hP_eq
    have hP_le_Mstar : (P : Subgroup G) ≤ Mstar := by
      rw [hP_eq']
      exact hPG_le_Mstar
    refine ⟨hP_le_Mstar, ?_⟩
    rw [hP_eq']
    simpa [hPGsub_eq] using hPstar_norm
  · have hQ0_le_Mstar : Q0 ≤ Mstar := by
      have hQ0_le_Mtwo : Q0 ≤ Mtwo := by
        have hC_le_Mtwo : C ≤ Mtwo := by
          rw [hC_eq_CGA]
          exact hCGA_le_Mtwo
        exact hQ0_le_C.trans hC_le_Mtwo
      simpa [hMtwo_eq_Mstar] using hQ0_le_Mtwo
    have hNormQ0_le_Mstar : Subgroup.normalizer (Q0 : Set G) ≤ Mstar := by
      simpa [hMtwo_eq_Mstar] using hMtwoQ0.2
    have hCentQ0_le_Mstar : Subgroup.centralizer (Q0 : Set G) ≤ Mstar :=
      (centralizer_le_normalizer Q0).trans hNormQ0_le_Mstar
    have hAnormE : section10NormalIn A E :=
      (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA).1
    have hE_le_Mstar : E ≤ Mstar := by
      have hE_le_normA : E ≤ Subgroup.normalizer (A : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hAnormE.1).1 hAnormE.2
      exact hE_le_normA.trans hMstar.2
    have hQ0_le_E : Q0 ≤ E := hQ0_le_C.trans hC_le_E
    let Q0E : Subgroup E := Q0.subgroupOf E
    have hQ0E_p : IsPGroup q.val Q0E :=
      hQ0_p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Q0) (K := E) hQ0_le_E).symm
    obtain ⟨Qe, hQ0E_le_Qe⟩ := IsPGroup.exists_le_sylow (G := E) (p := q.val) hQ0E_p
    let QE : Subgroup G := section10AmbientSylowSubgroup E Qe
    have hQE_p : IsPGroup q.val QE := by
      change IsPGroup q.val ((Qe : Subgroup E).map E.subtype)
      exact IsPGroup.map Qe.isPGroup' E.subtype
    have hQE_le_E : QE ≤ E := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hQE_le_Mstar : QE ≤ Mstar := hQE_le_E.trans hE_le_Mstar
    have hQ0_le_QE : Q0 ≤ QE := by
      intro x hxQ0
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hQ0_le_E hxQ0⟩,
          hQ0E_le_Qe (by simpa [Q0E, Subgroup.mem_subgroupOf] using hxQ0), rfl⟩
    have hqrankE_le_one : primeRank q.val E ≤ 1 := by
      let eE : E.subgroupOf M ≃* E := Subgroup.subgroupOfEquivOfLe hE.1.2.1
      have hqrankE_le_Esub : primeRank q.val E ≤ primeRank q.val (E.subgroupOf M) :=
        section12_primeRank_le_of_equiv (R := E.subgroupOf M) (S := E) q.val eE
      have hqrankEsub_le_M : primeRank q.val (E.subgroupOf M) ≤ primeRank q.val M := by
        exact section8_primeRank_le_of_subgroup (G := M) (E.subgroupOf M) q.val
      exact hqrankE_le_Esub.trans (hqrankEsub_le_M.trans (le_of_eq hqτ1M.2.2))
    have hQe_cyc : IsCyclic (Qe : Subgroup E) :=
      section12_sylow_cyclic_of_primeRank_le_one hq_odd hqrankE_le_one Qe
    have hQE_cyc : IsCyclic QE := by
      let eQ : (Qe : Subgroup E) ≃* QE :=
        Subgroup.equivMapOfInjective (f := E.subtype) (Qe : Subgroup E) E.subtype_injective
      exact eQ.isCyclic.mp hQe_cyc
    have hQE_not_le_C : ¬ QE ≤ C := by
      intro hQE_le_C
      have hQe_le_Csub : (Qe : Subgroup E) ≤ C.subgroupOf E := by
        intro x hx
        have hxQE : ((x : E) : G) ∈ QE := Subgroup.mem_map_of_mem E.subtype hx
        simpa [Subgroup.mem_subgroupOf] using hQE_le_C hxQE
      rcases hqQuot with ⟨hCsubE, hq_dvd_Cidx⟩
      exact Qe.not_dvd_index (hq_dvd_Cidx.trans (Subgroup.index_dvd_of_le hQe_le_Csub))
    have hQE_ne_Q0 : QE ≠ Q0 := by
      intro hQE_eq_Q0
      exact hQE_not_le_C (by simpa [hQE_eq_Q0] using hQ0_le_C)
    have hQ0_in_QE : Q0 ∈ section10PrimeOrderSubgroupsIn q QE := by
      exact ⟨hQ0_le_QE, hQ0_primeOrder.2⟩
    have hQE_ne_bot : QE ≠ ⊥ := by
      intro hQEbot
      exact hQ0_ne_bot ((le_bot_iff.mp (by simpa [hQEbot] using hQ0_le_QE)))
    have hOmegaQE_card : Nat.card (section12OmegaOneSubgroup q QE) = q.val :=
      section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
        (p := q) hQE_p hQE_cyc hQE_ne_bot
    have hQ0_le_OmegaQE : Q0 ≤ section12OmegaOneSubgroup q QE :=
      section12_primeOrder_le_omegaOneSubgroup_of_le (H := QE) (X := Q0) hQ0_in_QE
    have hOmegaQE_eq_Q0 : section12OmegaOneSubgroup q QE = Q0 := by
      exact (Subgroup.eq_of_le_of_card_ge hQ0_le_OmegaQE (by
        rw [hOmegaQE_card, hQ0_primeOrder.2])).symm
    have hqsigma_compl : IsPiSubgroup (G := G) (section10SigmaPrimes Mstar)ᶜ Q0 := by
      intro r hrQ0
      have hr_eq_q : r = q := by
        simpa using
          (section8_isPiSubgroup_singleton_of_isPGroup (G := G) hQ0_p r hrQ0)
      subst r
      simpa using hqτ2star.1
    have hqSylow_abelian :
        ∀ Q : Sylow q.val G, IsMulCommutative (Q : Subgroup G) := by
      intro Q
      by_contra hQnonab
      have hQnonab' : section12HasNonabelianSylowSubgroup q G := ⟨Q, hQnonab⟩
      rcases section12_exists_EData_containing_sigma_compl_piSubgroup
          (G := G) (M := Mstar) (A := Q0) hMstar.1 hQ0_le_Mstar hqsigma_compl with
        ⟨Estar, Estar₁₂, Estar₁, Estar₂, Estar₃, hEstar, hQ0_le_Estar⟩
      obtain ⟨Bstar, hBstar⟩ :=
        section12_exists_rankTwo_in_E_of_tau2
          (G := G) (M := Mstar) (E := Estar) (E₁₂ := Estar₁₂)
          (E₁ := Estar₁) (E₂ := Estar₂) (E₃ := Estar₃) hMstar.1 hEstar hqτ2star
      have hQ0_Estar : Q0 ∈ section10PrimeOrderSubgroupsIn q Estar := by
        exact ⟨hQ0_le_Estar, hQ0_primeOrder.2⟩
      have hQ0_eq_fixed :
          Q0 = subgroupCentralizerIn Bstar (section10Msigma Mstar) := by
        by_contra hQ0_ne_fixed
        exact
          (theorem_12_7_c (G := G) (M := Mstar) (E := Estar) (E₁₂ := Estar₁₂)
            (E₁ := Estar₁) (E₂ := Estar₂) (E₃ := Estar₃) (A := Bstar) (p := q)
            hMstar.1 hEstar hqτ2star hBstar hQnonab' Q0 hQ0_Estar hQ0_ne_fixed).2
            hCentQ0_le_Mstar
      obtain ⟨Estar₀, hEstar₀comp⟩ :=
        theorem_12_7_d (G := G) (M := Mstar) (E := Estar) (E₁₂ := Estar₁₂)
          (E₁ := Estar₁) (E₂ := Estar₂) (E₃ := Estar₃) (A := Bstar) (p := q)
          hMstar.1 hEstar hqτ2star hBstar hQnonab'
      have hBstar_normEstar : section10NormalIn Bstar Estar :=
        (corollary_12_6_a (G := G) (M := Mstar) (E := Estar) (E₁₂ := Estar₁₂)
          (E₁ := Estar₁) (E₂ := Estar₂) (E₃ := Estar₃) (A := Bstar) (p := q)
          hMstar.1 hEstar hqτ2star hBstar).1
      have hQ0_normEstar : section10NormalIn Q0 Estar := by
        simpa [hQ0_eq_fixed] using
          section12_CA_msigma_normalIn_E
            (G := G) (M := Mstar) (E := Estar) (E₁₂ := Estar₁₂)
            (E₁ := Estar₁) (E₂ := Estar₂) (E₃ := Estar₃) (A := Bstar)
            hEstar hBstar_normEstar
      have hQ0_comp_Estar : section12ComplementIn Estar Q0 Estar₀ := by
        simpa [hQ0_eq_fixed] using hEstar₀comp
      let Vstar : Subgroup G := section10Msigma Mstar ⊔ Estar₀
      have hQ0_comp_Mstar : section12ComplementIn Mstar Q0 Vstar :=
        section12_extend_complementIn_from_complementToMsigma
          (M := Mstar) (E := Estar) (K := Q0) (L := Estar₀) hEstar.1 hQ0_comp_Estar
      have hMsigma_cent_Q0 :
          section10Msigma Mstar ≤ Subgroup.centralizer (Q0 : Set G) := by
        simpa [hQ0_eq_fixed] using
          section12_subgroupCentralizerIn_commute Bstar (section10Msigma Mstar)
      have hMsigma_norm_Q0 :
          section10Msigma Mstar ≤ Subgroup.normalizer (Q0 : Set G) :=
        hMsigma_cent_Q0.trans (centralizer_le_normalizer Q0)
      have hEstar_norm_Q0 : Estar ≤ Subgroup.normalizer (Q0 : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0_normEstar.1).1 hQ0_normEstar.2
      have hQ0_normMstar : section10NormalIn Q0 Mstar := by
        refine ⟨hQ0_le_Mstar, ?_⟩
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0_le_Mstar).2 (by
          rw [hEstar.1.2.2.1]
          exact sup_le hMsigma_norm_Q0 hEstar_norm_Q0)
      have hQ0_comp_Mstar' :
          (Vstar.subgroupOf Mstar).IsComplement' (Q0.subgroupOf Mstar) :=
        section12_complementIn_of_normal_isComplement'
          (G := G) (H := Mstar) (K := Q0) (L := Vstar) hQ0_comp_Mstar hQ0_normMstar
      let W : Subgroup G := QE ⊓ Vstar
      have hW_ne_bot : W ≠ ⊥ := by
        let QEloc : Subgroup Mstar := QE.subgroupOf Mstar
        let Vloc : Subgroup Mstar := Vstar.subgroupOf Mstar
        let Q0loc : Subgroup Mstar := Q0.subgroupOf Mstar
        have hQ0loc_le_QEloc : Q0loc ≤ QEloc := by
          intro x hx
          change ((x : Mstar) : G) ∈ QE
          exact hQ0_le_QE (by simpa [Q0loc, Subgroup.mem_subgroupOf] using hx)
        have : Q0loc.Normal := by
          simpa [Q0loc] using hQ0_normMstar.2
        intro hWbot
        have hQE_le_Q0 : QE ≤ Q0 := by
          intro x hxQE
          let xM : Mstar := ⟨x, hQE_le_Mstar hxQE⟩
          have hxQEloc : xM ∈ QEloc := by
            simpa [QEloc, Subgroup.mem_subgroupOf] using hxQE
          have hxTop : xM ∈ Vloc ⊔ Q0loc := by
            have hxTop' : xM ∈ (⊤ : Subgroup Mstar) := by simp
            rw [hQ0_comp_Mstar'.sup_eq_top]
            exact hxTop'
          rcases (Subgroup.mem_sup_of_normal_right
              (s := Vloc) (t := Q0loc) (x := xM)).1 hxTop with
            ⟨v, hvV, q0, hq0, hmul⟩
          have hq0QEloc : q0 ∈ QEloc := hQ0loc_le_QEloc hq0
          have hvQEloc : v ∈ QEloc := by
            have hv_eq : v = xM * q0⁻¹ := by
              calc
                v = v * (q0 * q0⁻¹) := by simp
                _ = v * q0 * q0⁻¹ := by simp [mul_assoc]
                _ = xM * q0⁻¹ := by rw [hmul]
            rw [hv_eq]
            exact QEloc.mul_mem hxQEloc (QEloc.inv_mem hq0QEloc)
          have hvW : ((v : Mstar) : G) ∈ W := by
            refine ⟨?_, ?_⟩
            · simpa [W, QEloc, Subgroup.mem_subgroupOf] using hvQEloc
            · simpa [W, Vloc, Subgroup.mem_subgroupOf] using hvV
          have hvbot : ((v : Mstar) : G) ∈ (⊥ : Subgroup G) := by
            simpa [W, hWbot] using hvW
          have hvone : v = 1 := by
            apply Subtype.ext
            simpa using hvbot
          have hxQ0loc : xM ∈ Q0loc := by
            have hx_eq_q0 : xM = q0 := by simpa [hvone] using hmul.symm
            simpa [hx_eq_q0] using hq0
          simpa [Q0loc, Subgroup.mem_subgroupOf] using hxQ0loc
        have hQE_eq_Q0 : QE = Q0 := le_antisymm hQE_le_Q0 hQ0_le_QE
        exact hQE_ne_Q0 hQE_eq_Q0
      have hWp : IsPGroup q.val W := by
        intro x
        have hxQE : ((x : W) : G) ∈ QE := by
          exact (show ((x : W) : G) ∈ QE ⊓ Vstar by simp [W]).1
        rcases hQE_p ⟨x, hxQE⟩ with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext
        simpa using congrArg Subtype.val hk
      have : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hW_ne_bot
      have hqW_dvd : q.val ∣ Nat.card W :=
        section12_prime_dvd_card_of_nontrivial_pSubgroup
          (G := G) (p := q) (B := W) hWp inferInstance
      obtain ⟨w, hw_order⟩ := exists_prime_orderOf_dvd_card' (G := W) q.val hqW_dvd
      let X : Subgroup G := Subgroup.zpowers (w : G)
      have hX_W : X ∈ section10PrimeOrderSubgroupsIn q W := by
        refine ⟨Subgroup.zpowers_le.2 w.property, ?_⟩
        dsimp [X]
        rw [Nat.card_zpowers]
        simpa [Subgroup.orderOf_coe] using hw_order
      have hX_ne_bot : X ≠ ⊥ :=
        section12_primeOrder_ne_bot (G := G) (A := W) (X := X) (p := q) hX_W
      have hX_in_QE : X ∈ section10PrimeOrderSubgroupsIn q QE := by
        exact ⟨hX_W.1.trans (show W ≤ QE by
          change QE ⊓ Vstar ≤ QE
          exact inf_le_left), hX_W.2⟩
      have hX_le_Q0 : X ≤ Q0 := by
        simpa [hOmegaQE_eq_Q0] using
          section12_primeOrder_le_omegaOneSubgroup_of_le (H := QE) (X := X) hX_in_QE
      have hX_le_Vstar : X ≤ Vstar := hX_W.1.trans inf_le_right
      have hX_bot : X = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        exact Subgroup.disjoint_def.mp hQ0_comp_Mstar.2.2.2 (hX_le_Q0 hx) (hX_le_Vstar hx)
      exact hX_ne_bot hX_bot
    obtain ⟨Q, hQ0_le_Q⟩ := IsPGroup.exists_le_sylow (G := G) (p := q.val) hQ0_p
    have hQcomm : IsMulCommutative (Q : Subgroup G) := hqSylow_abelian Q
    refine ⟨Q, ?_⟩
    have hQ_le_Mstar : (Q : Subgroup G) ≤ Mstar := by
      intro x hxQ
      have hxCent : x ∈ Subgroup.centralizer (Q0 : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hyQ0
        exact (setLike_mul_comm
          (s := (Q : Subgroup G)) hxQ (hQ0_le_Q hyQ0)).symm
      exact hCentQ0_le_Mstar hxCent
    exact ⟨hQ_le_Mstar, hQcomm⟩

end Section12

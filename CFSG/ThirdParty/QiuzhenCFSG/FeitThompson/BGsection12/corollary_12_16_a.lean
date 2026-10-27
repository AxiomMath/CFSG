module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.proposition_12_15_e

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# corollary_12_16_a
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_card_conjBy_local (H : Subgroup G) (g : G) :
    Nat.card (H.conjBy g) = Nat.card H := by
  simpa [Subgroup.conjBy] using
    (Subgroup.card_map_of_injective
      (K := H) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_conjBy_le_of_subgroupOf_conjBy_le_local
    {H K M : Subgroup G} {g : G}
    (hgM : g ∈ M) (hHM : H ≤ M)
    (hsub :
      (H.subgroupOf M).map (MulAut.conj (⟨g, hgM⟩ : M)).toMonoidHom ≤
        K.subgroupOf M) :
    H.conjBy g ≤ K := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hyH, hyx⟩
  have hxM : x ∈ M := by
    have hyM : y ∈ M := hHM hyH
    have hconjM : g * y * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM hyM) (M.inv_mem hgM)
    have hx_eq : x = g * y * g⁻¹ := by
      simpa [MulAut.conj_apply] using hyx.symm
    simpa [hx_eq] using hconjM
  let xM : M := ⟨x, hxM⟩
  let yM : M := ⟨y, hHM hyH⟩
  have hyM_sub : yM ∈ H.subgroupOf M := hyH
  have hxM_conj :
      xM ∈ (H.subgroupOf M).map (MulAut.conj (⟨g, hgM⟩ : M)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨yM, hyM_sub, ?_⟩
    apply Subtype.ext
    simpa [xM, yM, MulAut.conj_apply] using hyx
  exact (hsub hxM_conj : x ∈ K)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_mem_normalizer_of_conjBy_eq_local
    {H : Subgroup G} {g : G} (hg : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g :=
      Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
    simpa [hg] using hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by simpa [hg] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by simp [mul_assoc]
        _ = g⁻¹ * (g * y * g⁻¹) * g := by
          rw [show g * x * g⁻¹ = g * y * g⁻¹ by simpa [MulAut.conj_apply] using hyx.symm]
        _ = y := by simp [mul_assoc]
    simpa [hxy] using hy

omit [IsMinCE G] in
public theorem CFSG.section12Mbeta_subgroupOf_eq {M : Subgroup G} :
    (section10Mbeta M).subgroupOf M = section10MbetaSubgroup M := by
  change (piCoreIn (section10BetaPrimes M) M).subgroupOf M =
    piCore (section10BetaPrimes M) M
  exact piCore_map_subtype_subgroupOf (G := G) (section10BetaPrimes M) M

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_local_sup_eq_top_of_sup_eq
    {H A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H)
    (hsup : A ⊔ B = H) :
    A.subgroupOf H ⊔ B.subgroupOf H = ⊤ := by
  calc
    A.subgroupOf H ⊔ B.subgroupOf H = (A ⊔ B).subgroupOf H := by
      symm
      exact Subgroup.subgroupOf_sup (A := A) (A' := B) (B := H) hAH hBH
    _ = ⊤ := by
      rw [hsup]
      simp

omit [IsMinCE G] in
private theorem CFSG.section12_primeRank_conjBy_eq_local
    (H : Subgroup G) (q : ℕ) (g : G) :
    primeRank q (H.conjBy g) = primeRank q H := by
  let e : H ≃* H.conjBy g :=
    Subgroup.equivMapOfInjective
      (f := (MulAut.conj g).toMonoidHom) H
      (EquivLike.injective (MulAut.conj g))
  exact le_antisymm
    (section12_primeRank_le_of_equiv (R := H) (S := H.conjBy g) q e)
    (section12_primeRank_le_of_equiv (R := H.conjBy g) (S := H) q e.symm)

public theorem CFSG.section12_exists_rankTwo_in_subgroup_of_two_le_primeRank
    {N : Subgroup G} {p : Nat.Primes}
    (hrank : 2 ≤ primeRank p.val N) :
    ∃ A : Subgroup G, A ∈ section12RankTwoElementaryAbelianIn p N := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  obtain ⟨B, hBp, _hBcomm, hBgen⟩ :=
    section12_exists_pSubgroup_two_le_generatorRank_of_two_le_primeRank
      (R := N) (p := p.val) hrank
  let BG : Subgroup G := B.map N.subtype
  have hBGp : IsPGroup p.val BG := by
    simpa [BG] using IsPGroup.map (p := p.val) (H := B) hBp N.subtype
  have hBGnoncyc : ¬ IsCyclic BG := by
    intro hBGcyc
    let e : B ≃* BG :=
      Subgroup.equivMapOfInjective (f := N.subtype) B N.subtype_injective
    have hBcyc : IsCyclic B := e.isCyclic.2 hBGcyc
    have hgen_le : generatorRank B ≤ 1 :=
      generatorRank_le_one_of_isCyclic (G := B) hBcyc
    omega
  obtain ⟨A, hA_BG⟩ :=
    section12_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := BG) (p := p) hBGp hBGnoncyc
  have hBG_le_N : BG ≤ N := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  exact ⟨A, section12_rankTwo_mono hA_BG hBG_le_N⟩

omit [IsMinCE G] in
public theorem CFSG.section12_rankTwo_noncyclic
    {H A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p H) :
    ¬ IsCyclic A := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  intro hcyc
  rcases section12_rankTwo_elementary hA with ⟨hcard, hElem⟩
  have : IsElementaryAbelian p.val A := hElem
  have hgen : 2 ≤ generatorRank A :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := p.val) hcard
  have hle : generatorRank A ≤ 1 :=
    generatorRank_le_one_of_isCyclic (G := A) hcyc
  omega

private theorem CFSG.section12_exists_rankTwo_in_product_factor_of_rankTwo
    {H K U A : Subgroup G} {π : Set Nat.Primes} {p : Nat.Primes}
    (_hKH : K ≤ H) (_hUH : U ≤ H)
    [hKnorm : (K.subgroupOf H).Normal]
    (hKHall : IsHallSubgroup π (K.subgroupOf H))
    (hpπ : p ∉ π)
    (hKU : K.subgroupOf H ⊔ U.subgroupOf H = ⊤)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p H) :
    ∃ B : Subgroup G, B ∈ section12RankTwoElementaryAbelianIn p U := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let AH : Subgroup H := A.subgroupOf H
  have hAHp : IsPGroup p.val AH := by
    rcases section12_rankTwo_elementary hA with ⟨_hcard, hElem⟩
    have : IsElementaryAbelian p.val A := hElem
    exact (IsElementaryAbelian.isPGroup p.val A).of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := H) (section12_rankTwo_le hA)).symm
  obtain ⟨T, hAH_le_T⟩ := IsPGroup.exists_le_sylow (G := H) (p := p.val) hAHp
  have hTnoncyc : ¬ IsCyclic (T : Subgroup H) := by
    intro hTcyc
    have hAHcyc : IsCyclic AH := Subgroup.isCyclic_of_le hAH_le_T
    let eAH : AH ≃* A :=
      Subgroup.subgroupOfEquivOfLe (H := A) (K := H) (section12_rankTwo_le hA)
    exact section12_rankTwo_noncyclic (G := G) (H := H) hA (eAH.isCyclic.mp hAHcyc)
  let Usub : Subgroup H := U.subgroupOf H
  let S : Sylow p.val Usub := Classical.choice (Sylow.nonempty (p := p.val) (G := Usub))
  rcases section12_sylow_map_subtype_of_sup_hall
      (H := H) (π := π) (K := K.subgroupOf H) (U := Usub)
      hKHall hpπ hKU S with
    ⟨T0, hT0_eq⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H T T0
  have hT0noncyc : ¬ IsCyclic (T0 : Subgroup H) := by
    intro hT0cyc
    have hconj_cyc : IsCyclic (((g • T : Sylow p.val H) : Subgroup H)) := by
      have hconj_eq :
          (((g • T : Sylow p.val H) : Subgroup H)) = (T0 : Subgroup H) := by
        simpa using congrArg (fun S : Sylow p.val H => (S : Subgroup H)) hg
      exact (MulEquiv.subgroupCongr hconj_eq).isCyclic.mpr hT0cyc
    let eT :
        (T : Subgroup H) ≃* (((g • T : Sylow p.val H) : Subgroup H)) :=
      Subgroup.equivMapOfInjective
        (f := (MulAut.conj g).toMonoidHom) (T : Subgroup H)
        (EquivLike.injective (MulAut.conj g))
    exact hTnoncyc (eT.isCyclic.mpr hconj_cyc)
  let SH : Subgroup H := (S : Subgroup Usub).map Usub.subtype
  have hSH_noncyc : ¬ IsCyclic SH := by
    intro hSHcyc
    have hT0_SH : (T0 : Subgroup H) = SH := by
      simpa [SH] using hT0_eq
    exact hT0noncyc ((MulEquiv.subgroupCongr hT0_SH).isCyclic.mpr hSHcyc)
  let Pamb : Subgroup G := SH.map H.subtype
  have hPamb_p : IsPGroup p.val Pamb := by
    have hSHp : IsPGroup p.val SH := by
      simpa [SH] using IsPGroup.map (p := p.val) (H := (S : Subgroup Usub))
        S.isPGroup' Usub.subtype
    simpa [Pamb] using IsPGroup.map (p := p.val) (H := SH) hSHp H.subtype
  have hPamb_noncyc : ¬ IsCyclic Pamb := by
    intro hPambcyc
    let eSH : SH ≃* Pamb :=
      Subgroup.equivMapOfInjective (f := H.subtype) SH H.subtype_injective
    exact hSH_noncyc (eSH.isCyclic.mpr hPambcyc)
  obtain ⟨B, hB_Pamb⟩ :=
    section12_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := Pamb) (p := p) hPamb_p hPamb_noncyc
  have hPamb_le_U : Pamb ≤ U := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨yH, hyH, rfl⟩
    rcases Subgroup.mem_map.mp hyH with ⟨yU, _hyS, hyUH⟩
    have hy_eq : yH = Usub.subtype yU := hyUH.symm
    have hyU : ((Usub.subtype yU : H) : G) ∈ U := by
      change Usub.subtype yU ∈ U.subgroupOf H
      exact yU.property
    simpa [hy_eq] using hyU
  exact ⟨B, section12_rankTwo_mono hB_Pamb hPamb_le_U⟩

private theorem CFSG.section12_conjugate_pi_subgroup_into_product_factor
    {H K U Z : Subgroup G} {π ρ : Set Nat.Primes}
    (hH : H ∈ section9MaximalSubgroups G)
    (hZH : Z ≤ H) (_hUH : U ≤ H)
    (hZπ : IsPiSubgroup (G := G) π Z)
    [hKnorm : (K.subgroupOf H).Normal]
    (hKHall : IsHallSubgroup ρ (K.subgroupOf H))
    (hdis : Disjoint π ρ)
    (hKU : K.subgroupOf H ⊔ U.subgroupOf H = ⊤) :
    ∃ g : H, Z.conjBy (g : G) ≤ U := by
  classical
  let Zsub : Subgroup H := Z.subgroupOf H
  have hZsubπ : IsPiSubgroup (G := H) π Zsub := by
    intro p hpZsub
    have hpZ : p ∈ subgroupPrimeSet Z := by
      simpa [Zsub, subgroupPrimeSet, section12_card_subgroupOf_eq hZH] using hpZsub
    exact hZπ p hpZ
  let : MulDistribMulAction Unit H := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hZsub_inv : IsInvariant Unit H Zsub := by
    refine ⟨?_⟩
    intro _ x
    simp [Zsub]
  have hHsolv : Group.IsSolvable H :=
    IsMinCE.proper_subgroups_solvable H (lt_top_iff_ne_top.mpr hH.1)
  let : Group.IsSolvable H := hHsolv
  have hcopH : Nat.Coprime (Nat.card Unit) (Nat.card H) := by simp
  obtain ⟨L, hLHall, _hLInv, hZsubL⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := H) (A := Unit) hHsolv hcopH π Zsub hZsubπ hZsub_inv
  let Usub : Subgroup H := U.subgroupOf H
  let : MulDistribMulAction Unit Usub := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hUsub_solv : Group.IsSolvable Usub := by infer_instance
  have hcopU : Nat.Coprime (Nat.card Unit) (Nat.card Usub) := by simp
  obtain ⟨LU, hLUHall, _hLUInv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := Usub) (A := Unit) hUsub_solv hcopU π
  let LUH : Subgroup H := LU.map Usub.subtype
  have hLUH_le_Usub : LUH ≤ Usub := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hLUHHall : IsHallSubgroup π LUH := by
    have hcard_eq : Nat.card LUH = Nat.card LU := by
      simpa [LUH] using
        (Subgroup.card_map_of_injective
          (K := LU) (f := Usub.subtype) Usub.subtype_injective)
    refine isHallSubgroup_of (G := H) π LUH ?_ ?_
    · intro q hqcard
      exact hLUHall.p_in_pi_of_p_dvd_card q (by simpa [hcard_eq] using hqcard)
    · intro q hqπ hqidx
      have hqρ : q ∉ ρ := by
        rw [Set.disjoint_left] at hdis
        exact hdis hqπ
      have hUnot : ¬ q.val ∣ Usub.index :=
        section12_prime_not_dvd_index_of_sup_hall
          (H := H) (π := ρ) (K := K.subgroupOf H) (U := Usub)
          hKHall hqρ hKU
      have hidx : LUH.index = LU.index * Usub.index := by
        simpa [LUH] using Subgroup.index_map_subtype (H := Usub) LU
      have hqprod : q.val ∣ LU.index * Usub.index := by
        simpa [hidx] using hqidx
      rcases q.property.dvd_or_dvd hqprod with hqLU | hqU
      · exact hLUHall.p_in_pi_of_p_dvd_index q hqLU hqπ
      · exact hUnot hqU
  obtain ⟨a, ha⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := H) hHsolv hLHall hLUHHall
  have hZsub_conj_le_Usub :
      Zsub.map (MulAut.conj a).toMonoidHom ≤ Usub := by
    have htmp :
        Zsub.map (MulAut.conj a).toMonoidHom ≤
          L.map (MulAut.conj a).toMonoidHom :=
      Subgroup.map_mono hZsubL
    have htmp' : Zsub.map (MulAut.conj a).toMonoidHom ≤ LUH := by
      simpa [ha] using htmp
    exact htmp'.trans hLUH_le_Usub
  refine ⟨a, ?_⟩
  exact section12_conjBy_le_of_subgroupOf_conjBy_le_local
    (G := G) (H := Z) (K := U) (M := H) (g := (a : G))
    a.property hZH hZsub_conj_le_Usub

private theorem CFSG.section12_tau2_of_mem_E_of_rankTwo_in_M
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpE : p ∈ subgroupPrimeSet E)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    p ∈ section12Tau2Primes M := by
  classical
  have hrank_ge : 2 ≤ primeRank p.val M :=
    section12_primeRank_at_least_two_of_rankTwo hA
  rcases section12_prime_mem_tau_union_of_mem_E
      (G := G) (M := M) (E := E) hM hE.1 hpE with hp12 | hpτ3
  · rcases hp12 with hpτ1 | hpτ2
    · have hrank_eq : primeRank p.val M = 1 :=
        section12_tau13_primeRank_eq_one (G := G) (M := M) (p := p) (Or.inl hpτ1)
      omega
    · exact hpτ2
  · have hrank_eq : primeRank p.val M = 1 :=
      section12_tau13_primeRank_eq_one (G := G) (M := M) (p := p) (Or.inr hpτ3)
    omega

private theorem CFSG.section12_rankTwo_in_M_contradicts_msigma_inf
    {M E E₁₂ E₁ E₂ E₃ H X A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpE : p ∈ subgroupPrimeSet E)
    (hH : H ∈ section9MaximalSubgroups G)
    (hHnot : section12NotConjugate H M)
    (hA_M : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hA_H : A ≤ H)
    (hXne : X ≠ ⊥)
    (hXσ : X ≤ section10Msigma M)
    (hXH : X ≤ H) :
    False := by
  classical
  have hpτ2 : p ∈ section12Tau2Primes M :=
    section12_tau2_of_mem_E_of_rankTwo_in_M
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) hM hE hpE hA_M
  have hH_ne_M : H ≠ M := by
    intro hHM
    exact hHnot 1 (by simpa [hHM] using section8_conjBy_one (G := G) H)
  have hbot :
      section10Msigma M ⊓ H = ⊥ :=
    theorem_12_5_e
      (G := G) (M := M) (A := A) (p := p)
      hM hpτ2 hA_M H ⟨hH, hA_H⟩ hH_ne_M
  have hXbot : X ≤ ⊥ := by
    rw [← hbot]
    exact le_inf hXσ hXH
  exact hXne (le_bot_iff.mp hXbot)

public theorem CFSG.section12_exists_characteristic_pSubgroup_of_nontrivial
    {Y : Subgroup G}
    (hYne : Y ≠ ⊥) (hYne_top : Y ≠ ⊤) :
    ∃ q : Nat.Primes, ∃ X : Subgroup G,
      X ≤ Y ∧ X ≠ ⊥ ∧ IsPGroup q.val X ∧
        Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  classical
  let : Group.IsSolvable Y :=
    IsMinCE.proper_subgroups_solvable Y (lt_top_iff_ne_top.mpr hYne_top)
  let F : Subgroup Y := fittingSubgroup Y
  have hFne : F ≠ ⊥ := by
    intro hFbot
    have hYcard : Nat.card Y = 1 :=
      (fitting_eq_bot_iff_card_eq_one_of_solvable Y).mp (by simpa [F] using hFbot)
    exact hYne ((Subgroup.card_eq_one (H := Y)).1 hYcard)
  have hFcard_ne_one : Nat.card F ≠ 1 := by
    intro hcard
    have hFbot : F = ⊥ := (Subgroup.card_eq_one (H := F)).1 hcard
    exact hFne hFbot
  obtain ⟨q0, hq0prime, hq0dvdF⟩ := Nat.exists_prime_and_dvd hFcard_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  let P : Sylow q.val F := Classical.choice (Sylow.nonempty (p := q.val) (G := F))
  have hPneF : (P : Subgroup F) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := F) P (by simpa [q] using hq0dvdF)
  have hPcharF : ((P : Subgroup F)).Characteristic :=
    Sylow.characteristic_of_normal P
      (Group.IsNilpotent.sylow_normal (inferInstance : Group.IsNilpotent F) q.val P)
  let PF : Subgroup Y := (P : Subgroup F).map F.subtype
  have hPFchar : PF.Characteristic := by
    let : ((P : Subgroup F)).Characteristic := hPcharF
    simpa [PF, F] using
      characteristic_map_subtype_of_characteristic (G := Y) F (P : Subgroup F)
  let X : Subgroup G := PF.map Y.subtype
  have hXne : X ≠ ⊥ := by
    intro hXbot
    have hPFbot : PF = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := PF) (f := Y.subtype) Y.subtype_injective).mp
        (by simpa [X, PF] using hXbot)
    have hPbot : (P : Subgroup F) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := (P : Subgroup F)) (f := F.subtype) F.subtype_injective).mp
        (by simpa [PF] using hPFbot)
    exact hPneF hPbot
  have hXleY : X ≤ Y := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hXq : IsPGroup q.val X := by
    simpa [X, PF] using
      IsPGroup.map (p := q.val) (H := PF)
        (IsPGroup.map (p := q.val) (H := (P : Subgroup F)) P.isPGroup' F.subtype)
        Y.subtype
  have hNormY_le_NormX :
      Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    let : PF.Characteristic := hPFchar
    simpa [X, PF] using
      section8_normalizer_map_subtype_le_of_characteristic
        (G := G) (H := Y) (K := PF)
  exact ⟨q, X, hXleY, hXne, hXq, hNormY_le_NormX⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_subgroupNormalizerIn_conjBy_eq_local
    (H Y : Subgroup G) (g : G) :
    subgroupNormalizerIn (H.conjBy g) (Y.conjBy g : Set G) =
      (subgroupNormalizerIn H (Y : Set G)).conjBy g := by
  classical
  apply le_antisymm
  · intro x hx
    rcases mem_subgroupNormalizerIn.mp hx with ⟨hxNormYg, hxHg⟩
    rcases Subgroup.mem_map.mp hxHg with ⟨y, hyH, hyx⟩
    have hx_eq : x = g * y * g⁻¹ := by
      simpa [MulAut.conj_apply] using hyx.symm
    have hYg_fix : (Y.conjBy g).conjBy x = Y.conjBy g :=
      section11_conjBy_eq_of_mem_normalizer hxNormYg
    have hYy_fix : Y.conjBy y = Y := by
      have htmp : (Y.conjBy y).conjBy g = Y.conjBy g := by
        calc
          (Y.conjBy y).conjBy g = Y.conjBy (g * y) := by
            simpa [mul_assoc] using section11_conjBy_conjBy (G := G) Y y g
          _ = (Y.conjBy g).conjBy x := by
            rw [hx_eq]
            simpa [mul_assoc] using
              (section11_conjBy_conjBy (G := G) Y g (g * y * g⁻¹)).symm
          _ = Y.conjBy g := hYg_fix
      have htmp' := congrArg (fun K : Subgroup G => K.conjBy g⁻¹) htmp
      simpa [section11_conjBy_inv, section11_conjBy_inv'] using htmp'
    refine Subgroup.mem_map.mpr ⟨y, ?_, ?_⟩
    · exact mem_subgroupNormalizerIn.mpr
        ⟨section12_mem_normalizer_of_conjBy_eq_local (G := G) hYy_fix, hyH⟩
    · simpa [MulAut.conj_apply] using hyx
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyN, hyx⟩
    rcases mem_subgroupNormalizerIn.mp hyN with ⟨hyNormY, hyH⟩
    have hx_eq : x = g * y * g⁻¹ := by
      simpa [MulAut.conj_apply] using hyx.symm
    have hY_fix : Y.conjBy y = Y :=
      section11_conjBy_eq_of_mem_normalizer hyNormY
    have hxNormYg : x ∈ Subgroup.normalizer (Y.conjBy g : Set G) := by
      apply section12_mem_normalizer_of_conjBy_eq_local (G := G)
      calc
        (Y.conjBy g).conjBy x = Y.conjBy (x * g) := by
          simpa [mul_assoc] using section11_conjBy_conjBy (G := G) Y g x
        _ = Y.conjBy (g * y) := by
          rw [hx_eq]
          simp [mul_assoc]
        _ = (Y.conjBy y).conjBy g := by
          simpa [mul_assoc] using (section11_conjBy_conjBy (G := G) Y y g).symm
        _ = Y.conjBy g := by rw [hY_fix]
    have hxHg : x ∈ H.conjBy g := by
      exact Subgroup.mem_map.mpr ⟨y, hyH, by simpa [MulAut.conj_apply] using hyx⟩
    exact mem_subgroupNormalizerIn.mpr ⟨hxNormYg, hxHg⟩

private theorem CFSG.section12_corollary_12_16_rank_bound_of_le_msigma
    {M E E₁₂ E₁ E₂ E₃ Y H : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hYne : Y ≠ ⊥) (hYσ : IsPiSubgroup (section10SigmaPrimes M) Y)
    (hYleσ : Y ≤ section10Msigma M)
    (hpE : p ∈ subgroupPrimeSet E) (hpβ : p ∉ section12BetaPrimesOfGroup G)
    (hH : H ∈ section9MaximalSubgroupsContaining Y)
    (hHnot : section12NotConjugate H M) :
    primeRank p.val (subgroupNormalizerIn H (Y : Set G)) ≤ 1 := by
  classical
  by_contra hnot_rank
  have hrank_ge : 2 ≤ primeRank p.val (subgroupNormalizerIn H (Y : Set G)) := by
    omega
  have hYne_top : Y ≠ ⊤ := by
    intro hYtop
    exact hH.1.1 (top_le_iff.mp (hYtop ▸ hH.2))
  rcases section12_exists_characteristic_pSubgroup_of_nontrivial
      (G := G) (Y := Y) hYne hYne_top with
    ⟨q, X, hXleY, hXne, hXq, hNormY_le_NormX⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  have hXσ : X ≤ section10Msigma M := hXleY.trans hYleσ
  have hX_le_M : X ≤ M := hXσ.trans (section12_Msigma_le M)
  have hXH : X ≤ H := hXleY.trans hH.2
  have hqY : q ∈ subgroupPrimeSet Y := by
    have hXnontrivial : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hXne
    exact
      section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
        (A := Y) (B := X.subgroupOf Y)
        (hBp := hXq.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := X) (K := Y) hXleY).symm)
        (hB_ne_bot := by
          intro hbot
          exact hXne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hXleY))
  have hqσ : q ∈ section10SigmaPrimes M := hYσ q hqY
  obtain ⟨A, hA_N⟩ :=
    section12_exists_rankTwo_in_subgroup_of_two_le_primeRank
      (G := G) (N := subgroupNormalizerIn H (Y : Set G)) (p := p) hrank_ge
  have hA_H : A ≤ H :=
    (section12_rankTwo_le hA_N).trans (subgroupNormalizerIn_le H (Y : Set G))
  by_cases hNXM : Subgroup.normalizer (X : Set G) ≤ M
  · have hN_le_M : subgroupNormalizerIn H (Y : Set G) ≤ M := by
      intro x hx
      exact hNXM (hNormY_le_NormX (mem_subgroupNormalizerIn.mp hx).1)
    have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
      section12_rankTwo_mono hA_N hN_le_M
    exact
      section12_rankTwo_in_M_contradicts_msigma_inf
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (H := H) (X := X) (A := A) (p := p)
        hM hE hpE hH.1 hHnot hA_M hA_H hXne hXσ hXH
  · have hNXne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
      intro hNtop
      have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
      let : IsSimpleGroup G := IsMinCE.simple
      rcases hXnormal.eq_bot_or_eq_top with hXbot | hXtop
      · exact hXne hXbot
      · have hYtop : Y = ⊤ := by
          have htop_le_Y : (⊤ : Subgroup G) ≤ Y := by
            simpa [hXtop] using hXleY
          exact top_le_iff.mp htop_le_Y
        exact hYne_top hYtop
    obtain ⟨Mstar, hMstar⟩ :=
      section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) (H := Subgroup.normalizer (X : Set G)) hNXne_top
    have hMstar_ne_M : Mstar ≠ M := by
      intro hEq
      exact hNXM (hEq ▸ hMstar.2)
    have hX_le_Mstar : X ≤ Mstar := Subgroup.le_normalizer.trans hMstar.2
    have hXinf : X ≤ M ⊓ Mstar := le_inf hX_le_M hX_le_Mstar
    obtain ⟨S, hXS⟩ :=
      IsPGroup.exists_le_sylow (G := (M ⊓ Mstar : Subgroup G)) (p := q.val)
        (hXq.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := X) (K := M ⊓ Mstar) hXinf).symm)
    have hX_leS :
        X ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S := by
      intro x hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hXinf hx⟩, hXS (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
    have hnotconj_star : section12NotConjugate Mstar M :=
      proposition_12_15_a
        (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q) (S := S)
        hM hqσ hX_le_M hXne hXq hMstar hMstar_ne_M hX_leS
    have hN_le_Mstar : subgroupNormalizerIn H (Y : Set G) ≤ Mstar := by
      intro x hx
      exact hMstar.2 (hNormY_le_NormX (mem_subgroupNormalizerIn.mp hx).1)
    have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar :=
      section12_rankTwo_mono hA_N hN_le_Mstar
    let U : Subgroup G := M ⊓ Mstar
    have hU_le_M : U ≤ M := inf_le_left
    have hU_le_Mstar : U ≤ Mstar := inf_le_right
    have hpM : p ∈ subgroupPrimeSet M :=
      section8_subgroupPrimeSet_mono hE.1.2.1 hpE
    by_cases hqσstar : q ∈ section10SigmaPrimes Mstar
    · rcases proposition_12_15_d
          (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q) (S := S)
          hM hqσ hX_le_M hXne hXq hMstar hMstar_ne_M hX_leS hqσstar with
        ⟨hjoin, _hτ1, _hβα, _hβne⟩
      have : ((section10Mbeta Mstar).subgroupOf Mstar).Normal := by
        rw [section12Mbeta_subgroupOf_eq]
        infer_instance
      have hβHall :
          IsHallSubgroup (section10BetaPrimes Mstar)
            ((section10Mbeta Mstar).subgroupOf Mstar) := by
        simpa [section12Mbeta_subgroupOf_eq] using
          (lemma_10_8_a (G := G) hMstar.1).2
      have hpβstar : p ∉ section10BetaPrimes Mstar :=
        section12_not_beta_of_not_betaG (G := G) (M := Mstar) hpβ
      have hKU :
          (section10Mbeta Mstar).subgroupOf Mstar ⊔ U.subgroupOf Mstar = ⊤ := by
        have hsup : section10Mbeta Mstar ⊔ U = Mstar := by
          simpa [U, sup_comm] using hjoin.symm
        exact
          section12_local_sup_eq_top_of_sup_eq
            (G := G) (H := Mstar) (A := section10Mbeta Mstar) (B := U)
            (section12_Mbeta_le Mstar) hU_le_Mstar hsup
      obtain ⟨B, hB_U⟩ :=
        section12_exists_rankTwo_in_product_factor_of_rankTwo
          (G := G) (H := Mstar) (K := section10Mbeta Mstar) (U := U)
          (A := A) (π := section10BetaPrimes Mstar) (p := p)
          (section12_Mbeta_le Mstar) hU_le_Mstar hβHall hpβstar hKU hA_Mstar
      have hB_M : B ∈ section12RankTwoElementaryAbelianIn p M :=
        section12_rankTwo_mono hB_U hU_le_M
      have hB_Mstar : B ≤ Mstar :=
        (section12_rankTwo_le hB_U).trans hU_le_Mstar
      exact
        section12_rankTwo_in_M_contradicts_msigma_inf
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) (H := Mstar) (X := X) (A := B) (p := p)
          hM hE hpE hMstar.1 hnotconj_star hB_M hB_Mstar hXne hXσ hX_le_Mstar
    · rcases proposition_12_15_e
          (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q) (S := S)
          hM hqσ hX_le_M hXne hXq hMstar hMstar_ne_M hX_leS hqσstar with
        ⟨_hqτ2star, hbeta_subset, hcomp⟩
      have : ((section10Msigma Mstar).subgroupOf Mstar).Normal := by
        rw [section12Msigma_subgroupOf_eq]
        infer_instance
      have hσHall :
          IsHallSubgroup (section10SigmaPrimes Mstar)
            ((section10Msigma Mstar).subgroupOf Mstar) := by
        simpa [section12Msigma_subgroupOf_eq] using
          (theorem_10_2_b (G := G) hMstar.1).2
      have hpσstar : p ∉ section10SigmaPrimes Mstar := by
        intro hpσ
        exact (section12_not_beta_of_not_betaG (G := G) (M := Mstar) hpβ)
          (hbeta_subset ⟨hpM, hpσ⟩)
      have hKU :
          (section10Msigma Mstar).subgroupOf Mstar ⊔ U.subgroupOf Mstar = ⊤ := by
        have hsup : section10Msigma Mstar ⊔ U = Mstar := by
          simpa [U] using hcomp.2.2.1.symm
        exact
          section12_local_sup_eq_top_of_sup_eq
            (G := G) (H := Mstar) (A := section10Msigma Mstar) (B := U)
            (section12_Msigma_le Mstar) hU_le_Mstar hsup
      obtain ⟨B, hB_U⟩ :=
        section12_exists_rankTwo_in_product_factor_of_rankTwo
          (G := G) (H := Mstar) (K := section10Msigma Mstar) (U := U)
          (A := A) (π := section10SigmaPrimes Mstar) (p := p)
          (section12_Msigma_le Mstar) hU_le_Mstar hσHall hpσstar hKU hA_Mstar
      have hB_M : B ∈ section12RankTwoElementaryAbelianIn p M :=
        section12_rankTwo_mono hB_U hU_le_M
      have hB_Mstar : B ≤ Mstar :=
        (section12_rankTwo_le hB_U).trans hU_le_Mstar
      exact
        section12_rankTwo_in_M_contradicts_msigma_inf
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) (H := Mstar) (X := X) (A := B) (p := p)
          hM hE hpE hMstar.1 hnotconj_star hB_M hB_Mstar hXne hXσ hX_le_Mstar

private theorem CFSG.section12_conjugate_sigma_subgroup_into_msigma_of_le
    {M Z : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hZM : Z ≤ M)
    (hZσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Z) :
    ∃ g : M, Z.conjBy (g : G) ≤ section10Msigma M := by
  classical
  let : MulDistribMulAction Unit M := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  let Zsub : Subgroup M := Z.subgroupOf M
  have hZsubσ : IsPiSubgroup (G := M) (section10SigmaPrimes M) Zsub := by
    intro p hpZsub
    have hpZ : p ∈ subgroupPrimeSet Z := by
      simpa [Zsub, subgroupPrimeSet, section12_card_subgroupOf_eq hZM] using hpZsub
    exact hZσ p hpZ
  have hZsub_inv : IsInvariant Unit M Zsub := by
    refine ⟨?_⟩
    intro _ x
    simp [Zsub]
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  obtain ⟨L, hLHall, _hLInv, hZsubL⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hMsolv hcop (section10SigmaPrimes M)
      Zsub hZsubσ hZsub_inv
  obtain ⟨a, ha⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := M) hMsolv hLHall ((theorem_10_2_b (G := G) hM).2)
  refine ⟨a, ?_⟩
  exact section12_conjBy_le_of_subgroupOf_conjBy_le_local
    (G := G) (H := Z) (K := section10Msigma M) (M := M) (g := (a : G))
    a.property hZM (by
      simpa [section12Msigma_subgroupOf_eq (G := G) (M := M), ha] using
        Subgroup.map_mono hZsubL)


public theorem CFSG.section12_corollary_12_16_exists_conjugating_element
    {M Y : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hYne : Y ≠ ⊥) (hYσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Y)
    (hYne_top : Y ≠ ⊤) :
    ∃ g : G, Y.conjBy g ≤ section10Msigma M := by
  classical
  by_cases hYM : Y ≤ M
  · rcases section12_conjugate_sigma_subgroup_into_msigma_of_le
      (G := G) (M := M) (Z := Y) hM hYM hYσ with
      ⟨a, ha⟩
    exact ⟨a, ha⟩
  obtain ⟨H, hHmax, hYleH⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top (G := G) (H := Y) hYne_top
  by_cases hconj : ∃ g : G, H = M.conjBy g
  · rcases hconj with ⟨g, hHg⟩
    let Yg : Subgroup G := Y.conjBy g⁻¹
    have hYg_le_M : Yg ≤ M := by
      have hYleHg : Y ≤ M.conjBy g := by simpa [hHg] using hYleH
      have hmap : Y.conjBy g⁻¹ ≤ (M.conjBy g).conjBy g⁻¹ := Subgroup.map_mono hYleHg
      simpa [Yg, section11_conjBy_inv] using hmap
    have hYgσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Yg := by
      intro p hpYg
      have hpY : p ∈ subgroupPrimeSet Y := by
        simpa [Yg, subgroupPrimeSet, section12_card_conjBy_local (G := G) Y g⁻¹] using hpYg
      exact hYσ p hpY
    rcases section12_conjugate_sigma_subgroup_into_msigma_of_le
        (G := G) (M := M) (Z := Yg) hM hYg_le_M hYgσ with
      ⟨a, hYga_le_sigma⟩
    refine ⟨(a : G) * g⁻¹, ?_⟩
    simpa [Yg, section11_conjBy_conjBy, mul_assoc] using hYga_le_sigma
  · have hHnot : section12NotConjugate H M := by
      intro g hHg
      exact hconj ⟨g⁻¹, by
        simpa [section11_conjBy_inv] using congrArg (fun K => K.conjBy g⁻¹) hHg⟩
    rcases section12_exists_characteristic_pSubgroup_of_nontrivial
        (G := G) (Y := Y) hYne hYne_top with
      ⟨q, X, hXleY, hXne, hXq, hNormY_le_NormX⟩
    have : Fact q.val.Prime := ⟨q.property⟩
    have hqY : q ∈ subgroupPrimeSet Y := by
      have hXnontrivial : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hXne
      exact
        section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
          (A := Y) (B := X.subgroupOf Y)
          (hBp := hXq.of_equiv
            (Subgroup.subgroupOfEquivOfLe (H := X) (K := Y) hXleY).symm)
          (hB_ne_bot := by
            intro hbot
            exact hXne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hXleY))
    have hqσ : q ∈ section10SigmaPrimes M := hYσ q hqY
    obtain ⟨a, hX_le_Ma⟩ :=
      section10_exists_conjBy_le_of_isPGroup_of_sigma
        (G := G) (M := M) (Y := X) (p := q) hqσ hXq
    let Yg : Subgroup G := Y.conjBy a⁻¹
    let Xg : Subgroup G := X.conjBy a⁻¹
    have hXg_le_M : Xg ≤ M := by
      have hmap : X.conjBy a⁻¹ ≤ (M.conjBy a).conjBy a⁻¹ := Subgroup.map_mono hX_le_Ma
      simpa [Xg, section11_conjBy_inv] using hmap
    have hXg_le_Yg : Xg ≤ Yg := by
      change X.map ((MulAut.conj a⁻¹).toMonoidHom) ≤
        Y.map ((MulAut.conj a⁻¹).toMonoidHom)
      exact Subgroup.map_mono hXleY
    have hYgσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Yg := by
      intro p hpYg
      have hpY : p ∈ subgroupPrimeSet Y := by
        simpa [Yg, subgroupPrimeSet, section12_card_conjBy_local (G := G) Y a⁻¹] using hpYg
      exact hYσ p hpY
    have hXgne : Xg ≠ ⊥ := by
      intro hXgbot
      have hXeq : X = Xg.conjBy a := by
        simpa [Xg] using (section11_conjBy_inv' (G := G) X a).symm
      have hXbot : X = ⊥ := by
        calc
          X = Xg.conjBy a := hXeq
          _ = (⊥ : Subgroup G).conjBy a := by rw [hXgbot]
          _ = ⊥ := by simp [Subgroup.conjBy]
      exact hXne hXbot
    have hXgq : IsPGroup q.val Xg := by
      change IsPGroup q.val (X.map ((MulAut.conj a⁻¹).toMonoidHom))
      exact IsPGroup.map (p := q.val) (H := X) hXq
        ((MulAut.conj a⁻¹).toMonoidHom)
    have hNormYg_le_NormXg :
        Subgroup.normalizer (Yg : Set G) ≤ Subgroup.normalizer (Xg : Set G) := by
      intro n hnYg
      have hYfix : Yg.conjBy n = Yg :=
        section11_conjBy_eq_of_mem_normalizer (H := Yg) hnYg
      have hconj_n_normY : a * n * a⁻¹ ∈ Subgroup.normalizer (Y : Set G) := by
        apply section12_mem_normalizer_of_conjBy_eq_local (G := G) (H := Y)
        calc
          Y.conjBy (a * n * a⁻¹) = (Yg.conjBy n).conjBy a := by
            calc
              Y.conjBy (a * n * a⁻¹) = (Y.conjBy a⁻¹).conjBy (a * n) := by
                simpa [mul_assoc] using
                  (section11_conjBy_conjBy (G := G) Y a⁻¹ (a * n)).symm
              _ = (Yg.conjBy n).conjBy a := by
                change (Y.conjBy a⁻¹).conjBy (a * n) = ((Y.conjBy a⁻¹).conjBy n).conjBy a
                simpa [mul_assoc] using
                  (section11_conjBy_conjBy (G := G) (Y.conjBy a⁻¹) n a).symm
          _ = Yg.conjBy a := by rw [hYfix]
          _ = Y := by
            simpa [Yg] using (section11_conjBy_inv' (G := G) Y a)
      have hconj_n_normX : a * n * a⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
        hNormY_le_NormX hconj_n_normY
      have hXfix : X.conjBy (a * n * a⁻¹) = X :=
        section11_conjBy_eq_of_mem_normalizer (H := X) hconj_n_normX
      apply section12_mem_normalizer_of_conjBy_eq_local (G := G) (H := Xg)
      calc
        Xg.conjBy n = (X.conjBy (a * n * a⁻¹)).conjBy a⁻¹ := by
          calc
            Xg.conjBy n = X.conjBy (n * a⁻¹) := by
              simpa [Xg, mul_assoc] using
                (section11_conjBy_conjBy (G := G) X a⁻¹ n)
            _ = X.conjBy (a⁻¹ * (a * n * a⁻¹)) := by
              simp [mul_assoc]
            _ = (X.conjBy (a * n * a⁻¹)).conjBy a⁻¹ := by
              simpa [mul_assoc] using
                (section11_conjBy_conjBy (G := G) X (a * n * a⁻¹) a⁻¹).symm
        _ = X.conjBy a⁻¹ := by rw [hXfix]
        _ = Xg := by rfl
    by_cases hNXgM : Subgroup.normalizer (Xg : Set G) ≤ M
    · have hNormYg_M : Subgroup.normalizer (Yg : Set G) ≤ M := hNormYg_le_NormXg.trans hNXgM
      have hYg_le_M : Yg ≤ M := Subgroup.le_normalizer.trans hNormYg_M
      rcases section12_conjugate_sigma_subgroup_into_msigma_of_le
          (G := G) (M := M) (Z := Yg) hM hYg_le_M hYgσ with
        ⟨g, hg⟩
      refine ⟨(g : G) * a⁻¹, ?_⟩
      simpa [Yg, section11_conjBy_conjBy, mul_assoc] using hg
    · have hNXgne_top : Subgroup.normalizer (Xg : Set G) ≠ ⊤ := by
        intro hNtop
        have hXgnormal : Xg.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
        let : IsSimpleGroup G := IsMinCE.simple
        rcases hXgnormal.eq_bot_or_eq_top with hXgbot | hXgtop
        · exact hXgne hXgbot
        · have hYgne_top : Yg ≠ ⊤ := by
            intro hYgtop
            apply hYne_top
            calc
              Y = Yg.conjBy a := by
                simpa [Yg] using (section11_conjBy_inv' (G := G) Y a).symm
              _ = (⊤ : Subgroup G).conjBy a := by rw [hYgtop]
              _ = ⊤ := by
                ext x
                simp [Subgroup.conjBy]
          have htop_le_Yg : (⊤ : Subgroup G) ≤ Yg := by
            simpa [hXgtop] using hXg_le_Yg
          exact hYgne_top (top_le_iff.mp htop_le_Yg)
      obtain ⟨Mstar, hMstar⟩ :=
        section9_exists_maximalSubgroupsContaining_of_ne_top
          (G := G) (H := Subgroup.normalizer (Xg : Set G)) hNXgne_top
      have hMstar_ne_M : Mstar ≠ M := by
        intro hEq
        exact hNXgM (hEq ▸ hMstar.2)
      have hXg_le_Mstar : Xg ≤ Mstar := Subgroup.le_normalizer.trans hMstar.2
      have hXginf : Xg ≤ M ⊓ Mstar := le_inf hXg_le_M hXg_le_Mstar
      obtain ⟨S, hXgS⟩ :=
        IsPGroup.exists_le_sylow (G := (M ⊓ Mstar : Subgroup G)) (p := q.val)
          (hXgq.of_equiv
            (Subgroup.subgroupOfEquivOfLe (H := Xg) (K := M ⊓ Mstar) hXginf).symm)
      have hXg_leS :
          Xg ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S := by
        intro x hx
        exact Subgroup.mem_map.mpr
          ⟨⟨x, hXginf hx⟩, hXgS (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
      have hnotconj_star : section12NotConjugate Mstar M :=
        proposition_12_15_a
          (G := G) (M := M) (Mstar := Mstar) (X := Xg) (q := q) (S := S)
          hM hqσ hXg_le_M hXgne hXgq hMstar hMstar_ne_M hXg_leS
      have hNormYg_Mstar : Subgroup.normalizer (Yg : Set G) ≤ Mstar :=
        hNormYg_le_NormXg.trans hMstar.2
      have hYg_le_Mstar : Yg ≤ Mstar := Subgroup.le_normalizer.trans hNormYg_Mstar
      let U : Subgroup G := M ⊓ Mstar
      have hU_le_M : U ≤ M := inf_le_left
      have hU_le_Mstar : U ≤ Mstar := inf_le_right
      have hmove_to_U : ∃ m : Mstar, Yg.conjBy (m : G) ≤ U := by
        by_cases hqσstar : q ∈ section10SigmaPrimes Mstar
        · rcases proposition_12_15_d
            (G := G) (M := M) (Mstar := Mstar) (X := Xg) (q := q) (S := S)
            hM hqσ hXg_le_M hXgne hXgq hMstar hMstar_ne_M hXg_leS hqσstar with
            ⟨hjoin, _hτ, _hβα, _hβne⟩
          have : ((section10Mbeta Mstar).subgroupOf Mstar).Normal := by
            rw [section12Mbeta_subgroupOf_eq]
            infer_instance
          have hβHall :
              IsHallSubgroup (section10BetaPrimes Mstar)
                ((section10Mbeta Mstar).subgroupOf Mstar) := by
            simpa [section12Mbeta_subgroupOf_eq] using
              (lemma_10_8_a (G := G) hMstar.1).2
          have hdis :
              Disjoint (section10SigmaPrimes M) (section10BetaPrimes Mstar) := by
            rw [Set.disjoint_left]
            intro r hrσM hrβstar
            exact section12_not_beta_of_sigma_notconj
              (G := G) hM hMstar.1 hnotconj_star hrσM hrβstar
          have hKU :
              (section10Mbeta Mstar).subgroupOf Mstar ⊔ U.subgroupOf Mstar = ⊤ := by
            have hsup : section10Mbeta Mstar ⊔ U = Mstar := by
              simpa [U, sup_comm] using hjoin.symm
            exact
              section12_local_sup_eq_top_of_sup_eq
                (G := G) (H := Mstar) (A := section10Mbeta Mstar) (B := U)
                (section12_Mbeta_le Mstar) hU_le_Mstar hsup
          exact
            section12_conjugate_pi_subgroup_into_product_factor
              (G := G) (H := Mstar) (K := section10Mbeta Mstar) (U := U)
              (Z := Yg) (π := section10SigmaPrimes M) (ρ := section10BetaPrimes Mstar)
              hMstar.1 hYg_le_Mstar hU_le_Mstar hYgσ hβHall hdis hKU
        · rcases proposition_12_15_e
            (G := G) (M := M) (Mstar := Mstar) (X := Xg) (q := q) (S := S)
            hM hqσ hXg_le_M hXgne hXgq hMstar hMstar_ne_M hXg_leS hqσstar with
            ⟨_hqτ2, hbeta_subset, hcomp⟩
          have : ((section10Msigma Mstar).subgroupOf Mstar).Normal := by
            rw [section12Msigma_subgroupOf_eq]
            infer_instance
          have hσHall :
              IsHallSubgroup (section10SigmaPrimes Mstar)
                ((section10Msigma Mstar).subgroupOf Mstar) := by
            simpa [section12Msigma_subgroupOf_eq] using
              (theorem_10_2_b (G := G) hMstar.1).2
          have hdis :
              Disjoint (section10SigmaPrimes M) (section10SigmaPrimes Mstar) := by
            rw [Set.disjoint_left]
            intro r hrσM hrσstar
            have hrβstar : r ∈ section10BetaPrimes Mstar :=
              hbeta_subset ⟨hrσM.1, hrσstar⟩
            exact section12_not_beta_of_sigma_notconj
              (G := G) hM hMstar.1 hnotconj_star hrσM hrβstar
          have hKU :
              (section10Msigma Mstar).subgroupOf Mstar ⊔ U.subgroupOf Mstar = ⊤ := by
            have hsup : section10Msigma Mstar ⊔ U = Mstar := by
              simpa [U] using hcomp.2.2.1.symm
            exact
              section12_local_sup_eq_top_of_sup_eq
                (G := G) (H := Mstar) (A := section10Msigma Mstar) (B := U)
                (section12_Msigma_le Mstar) hU_le_Mstar hsup
          exact
            section12_conjugate_pi_subgroup_into_product_factor
              (G := G) (H := Mstar) (K := section10Msigma Mstar) (U := U)
              (Z := Yg) (π := section10SigmaPrimes M) (ρ := section10SigmaPrimes Mstar)
              hMstar.1 hYg_le_Mstar hU_le_Mstar hYgσ hσHall hdis hKU
      rcases hmove_to_U with ⟨m, hYgm_le_U⟩
      have hYgmσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) (Yg.conjBy (m : G)) := by
        intro p hpYgm
        have hpYg : p ∈ subgroupPrimeSet Yg := by
          simpa [subgroupPrimeSet, section12_card_conjBy_local (G := G) Yg (m : G)] using hpYgm
        exact hYgσ p hpYg
      rcases section12_conjugate_sigma_subgroup_into_msigma_of_le
          (G := G) (M := M) (Z := Yg.conjBy (m : G))
          hM (hYgm_le_U.trans hU_le_M) hYgmσ with
        ⟨b, hb⟩
      refine ⟨(b : G) * (m : G) * a⁻¹, ?_⟩
      simpa [Yg, section11_conjBy_conjBy, mul_assoc] using hb

private theorem CFSG.section12_corollary_12_16_rank_bound
    {M E E₁₂ E₁ E₂ E₃ Y H : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hYne : Y ≠ ⊥) (hYσ : IsPiSubgroup (section10SigmaPrimes M) Y)
    (hpE : p ∈ subgroupPrimeSet E) (hpβ : p ∉ section12BetaPrimesOfGroup G)
    (hH : H ∈ section9MaximalSubgroupsContaining Y)
    (hHnot : section12NotConjugate H M) :
    primeRank p.val (subgroupNormalizerIn H (Y : Set G)) ≤ 1 := by
  classical
  have hYne_top : Y ≠ ⊤ := by
    intro hYtop
    exact hH.1.1 (top_le_iff.mp (hYtop ▸ hH.2))
  obtain ⟨g, hYg_leσ⟩ :=
    section12_corollary_12_16_exists_conjugating_element
      (G := G) (M := M) (Y := Y) hM hYne hYσ hYne_top
  let Yg : Subgroup G := Y.conjBy g
  let Hg : Subgroup G := H.conjBy g
  have hYg_ne : Yg ≠ ⊥ := by
    simpa [Yg] using section12_conjBy_ne_bot (G := G) hYne g
  have hYgσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Yg := by
    intro r hrYg
    have hrY : r ∈ subgroupPrimeSet Y := by
      simpa [Yg, subgroupPrimeSet, section12_card_conjBy_local (G := G) Y g] using hrYg
    exact hYσ r hrY
  have hHg_cont : Hg ∈ section9MaximalSubgroupsContaining Yg := by
    refine ⟨section12_maximal_conjBy_local (G := G) hH.1 g, ?_⟩
    change Y.map ((MulAut.conj g).toMonoidHom) ≤
      H.map ((MulAut.conj g).toMonoidHom)
    exact Subgroup.map_mono hH.2
  have hHg_not : section12NotConjugate Hg M := by
    intro k hk
    exact hHnot (k * g) (by
      simpa [Hg, section11_conjBy_conjBy, mul_assoc] using hk)
  have hcore :
      primeRank p.val (subgroupNormalizerIn Hg (Yg : Set G)) ≤ 1 :=
    section12_corollary_12_16_rank_bound_of_le_msigma
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (Y := Yg) (H := Hg) (p := p)
      hM hE hYg_ne hYgσ hYg_leσ hpE hpβ hHg_cont hHg_not
  have hnorm_eq :
      subgroupNormalizerIn Hg (Yg : Set G) =
        (subgroupNormalizerIn H (Y : Set G)).conjBy g := by
    simpa [Yg, Hg] using section12_subgroupNormalizerIn_conjBy_eq_local
      (G := G) H Y g
  have hcore' :
      primeRank p.val ((subgroupNormalizerIn H (Y : Set G)).conjBy g) ≤ 1 := by
    rw [← hnorm_eq]
    exact hcore
  have hrank_eq :
      primeRank p.val ((subgroupNormalizerIn H (Y : Set G)).conjBy g) =
        primeRank p.val (subgroupNormalizerIn H (Y : Set G)) :=
    section12_primeRank_conjBy_eq_local
      (G := G) (subgroupNormalizerIn H (Y : Set G)) p.val g
  simpa [hrank_eq] using hcore'

/-- Corollary 12.16(a). -/
public theorem CFSG.corollary_12_16_a
    {M E E₁₂ E₁ E₂ E₃ Y H : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hYne : Y ≠ ⊥) (hYσ : IsPiSubgroup (section10SigmaPrimes M) Y)
    (hpE : p ∈ subgroupPrimeSet E) (hpβ : p ∉ section12BetaPrimesOfGroup G)
    (hH : H ∈ section9MaximalSubgroupsContaining Y)
    (hHnot : section12NotConjugate H M) :
    (∃ g : G, Y.conjBy g ≤ section10Msigma M) ∧
      primeRank p.val (subgroupNormalizerIn H (Y : Set G)) ≤ 1 := by
  classical
  have hYne_top : Y ≠ ⊤ := by
    intro hYtop
    exact hH.1.1 (top_le_iff.mp (hYtop ▸ hH.2))
  exact ⟨
    section12_corollary_12_16_exists_conjugating_element
      (G := G) (M := M) (Y := Y) hM hYne hYσ hYne_top,
    section12_corollary_12_16_rank_bound
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (Y := Y) (H := H) (p := p)
      hM hE hYne hYσ hpE hpβ hH hHnot⟩

end Section12

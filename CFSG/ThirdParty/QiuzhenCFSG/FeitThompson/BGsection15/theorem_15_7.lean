module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection15.corollary_15_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-! # Theorem 15 7 from BG Section 15 -/

section Section15

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [IsMinCE G] in
private theorem CFSG.section15_mem_F_or_P1_of_not_P2
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMnotP2 : M ∉ section14MFamilyP2 G) :
    M ∈ section14MFamilyF G ∪ section14MFamilyP1 G := by
  classical
  by_cases hκ : section14KappaPrimes M = ∅
  · exact Or.inl ⟨hM, hκ⟩
  · have hκ_nonempty : (section14KappaPrimes M).Nonempty := by
      by_contra hnone
      apply hκ
      ext p
      constructor
      · intro hp
        exact False.elim (hnone ⟨p, hp⟩)
      · intro hp
        cases hp
    have hMP : M ∈ section14MFamilyP G := ⟨hM, hκ_nonempty⟩
    have hκ_eq :
        section14KappaPrimes M = subgroupPrimeSet M \ section10SigmaPrimes M := by
      by_contra hne
      exact hMnotP2 ⟨hMP, hne⟩
    exact Or.inr ⟨hMP, hκ_eq⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_zpowers_conjBy_inv
    (x g : G) :
    Subgroup.zpowers (g⁻¹ * x * g) = (Subgroup.zpowers x).conjBy g⁻¹ := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    exact Subgroup.mem_map.mpr ⟨x ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩, by
      simpa [MulAut.conj_apply, mul_assoc] using
        (conj_zpow (i := n) (a := g⁻¹) (b := x)).symm⟩
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
      simpa [MulAut.conj_apply, mul_assoc] using
        (conj_zpow (i := n) (a := g⁻¹) (b := x))⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_normalizer_conjBy
    (H : Subgroup G) (g : G) :
    Subgroup.normalizer (H.conjBy g : Set G) =
      (Subgroup.normalizer (H : Set G)).conjBy g := by
  ext x
  constructor
  · intro hx
    have hxfix : (H.conjBy g).conjBy x = H.conjBy g :=
      section11_conjBy_eq_of_mem_normalizer (G := G) hx
    have hEq : H.conjBy (x * g) = H.conjBy g := by
      rw [← section11_conjBy_conjBy (G := G) H g x]
      exact hxfix
    have hxnorm : g⁻¹ * x * g ∈ Subgroup.normalizer (H : Set G) := by
      apply section15_mem_normalizer_of_conjBy_eq (G := G) (H := H)
      calc
        H.conjBy (g⁻¹ * x * g)
            = (H.conjBy (x * g)).conjBy g⁻¹ := by
              simpa [mul_assoc] using
                (section11_conjBy_conjBy (G := G) H (x * g) g⁻¹).symm
        _ = (H.conjBy g).conjBy g⁻¹ := by rw [hEq]
        _ = H := section11_conjBy_inv (G := G) H g
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hxnorm, by
      simp [MulAut.conj_apply, mul_assoc]⟩
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨n, hn, hnx⟩
    apply section15_mem_normalizer_of_conjBy_eq (G := G) (H := H.conjBy g)
    have hnfix : H.conjBy n = H :=
      section11_conjBy_eq_of_mem_normalizer (G := G) hn
    have hx_eq : x = g * n * g⁻¹ := by
      simpa [MulAut.conj_apply] using hnx.symm
    calc
      (H.conjBy g).conjBy x = H.conjBy (x * g) :=
        section11_conjBy_conjBy (G := G) H g x
      _ = H.conjBy (g * n) := by
        rw [hx_eq]
        simp [mul_assoc]
      _ = (H.conjBy n).conjBy g :=
        (section11_conjBy_conjBy (G := G) H n g).symm
      _ = H.conjBy g := by rw [hnfix]

private theorem CFSG.section15_maximal_normalizer_eq_self_of_mem_ne_one
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hxM : x ∈ M) (hxne : x ≠ 1) :
    Subgroup.normalizer (M : Set G) = M := by
  classical
  apply le_antisymm
  · have hnorm_proper : Subgroup.normalizer (M : Set G) ≠ ⊤ := by
      intro hnorm_top
      have hMnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
      letI : IsSimpleGroup G := IsMinCE.simple
      rcases (haveI := hMnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal M) with hMbot | hMtop
      · have hxbot : x ∈ (⊥ : Subgroup G) := by
          simpa [hMbot] using hxM
        exact hxne (by simpa using hxbot)
      · exact hM.1 hMtop
    exact le_of_eq ((hM.le_iff_eq hnorm_proper).mp Subgroup.le_normalizer)
  · exact Subgroup.le_normalizer

private theorem CFSG.section15_initial_pCoreIn_not_cyclic_of_X_prime
    {M X : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    {p : Nat.Primes} (hpX : p ∈ subgroupPrimeSet X) :
    ¬ IsCyclic (section15PCoreIn p M) := by
  classical
  intro hPcyc
  let F : Subgroup G := section8FittingSubgroup M
  let P : Subgroup G := section15PCoreIn p M
  have hp_dvd_X : p.val ∣ Nat.card X := by
    simpa [subgroupPrimeSet] using hpX
  obtain ⟨z, hzX, hzne, hZprime⟩ :=
    section15_exists_primeOrder_zpowers_of_prime_dvd_card
      (G := G) (B := X) (q := p) hp_dvd_X
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hZprime) with
    ⟨hZleX, hZcard⟩
  have hZcard_nat : Nat.card (Subgroup.zpowers z) = p.val := by
    simpa [Nat.card_zpowers] using hZcard
  have hzInf :
      z ∈ section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g := by
    simpa [hX] using hzX
  have hzF : z ∈ F := by
    simpa [F] using hzInf.1
  have hzFg : z ∈ F.conjBy g := by
    simpa [F] using hzInf.2
  have hM8 : M ∈ section8MaximalSubgroups G := by
    simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hM
  have hNormalizer_zpowers_eq_M :
      ∀ {a : G}, a ∈ F → a ≠ 1 → Nat.card (Subgroup.zpowers a) = p.val →
        Subgroup.normalizer (Subgroup.zpowers a : Set G) = M := by
    intro a haF hane hcard
    let Z : Subgroup G := Subgroup.zpowers a
    have hZ_le_F : Z ≤ F := Subgroup.zpowers_le.2 haF
    have hZp : IsPGroup p.val Z :=
      section15_isPGroup_of_prime_card (G := G) (A := Z) (q := p) hcard.symm
    haveI : Group.IsNilpotent F := by
      simpa [F] using section8FittingSubgroup_isNilpotent M
    have hZ_le_coreF :
        Z ≤ piCoreIn ({p} : Set Nat.Primes) F :=
      section8_isPGroup_le_piCoreIn_singleton_of_le_nilpotent
        (G := G) (H := Z) (K := F) hZ_le_F p hZp
    have hcoreF_le_coreM :
        piCoreIn ({p} : Set Nat.Primes) F ≤
          piCoreIn ({p} : Set Nat.Primes) M :=
      section8_piCoreIn_singleton_le_of_le_normalizer
        (G := G) (Y := F) (H := M)
        (by simpa [F] using section8FittingSubgroup_le M)
        (by simpa [F] using section10_le_normalizer_fitting (G := G) M) p
    have hZ_le_P : Z ≤ P := by
      calc
        Z ≤ piCoreIn ({p} : Set Nat.Primes) F := hZ_le_coreF
        _ ≤ piCoreIn ({p} : Set Nat.Primes) M := hcoreF_le_coreM
        _ = P := by
          simp [P, section15PCoreIn, section8_piCoreIn_singleton_eq_pCore_map]
    have hP_le_M : P ≤ M := by
      simpa [P] using section15_pCoreIn_le p M
    have hM_le_normP : M ≤ Subgroup.normalizer (P : Set G) := by
      have hPnormM : (P.subgroupOf M).Normal := by
        simpa [P] using (section15_pCoreIn_normalIn p M).2
      letI : (P.subgroupOf M).Normal := hPnormM
      exact Subgroup.le_normalizer_of_normal_subgroupOf hP_le_M
    have hM_le_normZ : M ≤ Subgroup.normalizer (Z : Set G) := by
      let Zsub : Subgroup P := Z.subgroupOf P
      haveI : IsCyclic P := by simpa [P] using hPcyc
      haveI : Zsub.Characteristic :=
        section12_subgroup_characteristic_of_cyclic (H := P) Zsub
      have hnormP_le_normZsub :
          Subgroup.normalizer (P : Set G) ≤
            Subgroup.normalizer ((Zsub.map P.subtype : Subgroup G) : Set G) :=
        section8_normalizer_map_subtype_le_of_characteristic
          (G := G) (H := P) (K := Zsub)
      have hmap_eq : (Zsub.map P.subtype : Subgroup G) = Z := by
        simpa [Zsub] using Subgroup.map_subgroupOf_eq_of_le hZ_le_P
      exact hM_le_normP.trans (by simpa [hmap_eq] using hnormP_le_normZsub)
    have hZ_le_M : Z ≤ M := hZ_le_F.trans (by simpa [F] using section8FittingSubgroup_le M)
    have hZ_ne : Z ≠ ⊥ := by
      simpa [Z] using (Subgroup.zpowers_ne_bot.mpr hane)
    have hZnormM : (Z.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZ_le_M).2 hM_le_normZ
    exact
      section8_normalizer_eq_of_nontrivial_normal_in_maximal
        hM8 hZ_le_M hZ_ne hZnormM
  let zg : G := g⁻¹ * z * g
  have hzgF : zg ∈ F := by
    rcases Subgroup.mem_map.mp hzFg with ⟨y, hyF, hyz⟩
    have hzg_eq_y : zg = y := by
      dsimp [zg]
      rw [← hyz]
      simp [MulAut.conj_apply, mul_assoc]
    simpa [hzg_eq_y] using hyF
  have hzgne : zg ≠ 1 := by
    intro hzg
    apply hzne
    calc
      z = g * zg * g⁻¹ := by
        dsimp [zg]
        group
      _ = 1 := by rw [hzg]; simp
  have hZgcard : Nat.card (Subgroup.zpowers zg) = p.val := by
    have horder : orderOf zg = orderOf z := by
      dsimp [zg]
      simpa [MulAut.conj_apply] using (MulAut.conj g⁻¹).orderOf_eq z
    rw [Nat.card_zpowers, horder]
    simpa [Nat.card_zpowers] using hZcard
  have hNz : Subgroup.normalizer (Subgroup.zpowers z : Set G) = M :=
    hNormalizer_zpowers_eq_M hzF hzne hZcard_nat
  have hNzg : Subgroup.normalizer (Subgroup.zpowers zg : Set G) = M :=
    hNormalizer_zpowers_eq_M hzgF hzgne hZgcard
  have hZg_eq :
      Subgroup.zpowers zg = (Subgroup.zpowers z).conjBy g⁻¹ := by
    simpa [zg] using section15_zpowers_conjBy_inv (G := G) z g
  have hM_conj_inv : M.conjBy g⁻¹ = M := by
    calc
      M.conjBy g⁻¹ =
          (Subgroup.normalizer (Subgroup.zpowers z : Set G)).conjBy g⁻¹ := by
            rw [hNz]
      _ = Subgroup.normalizer (((Subgroup.zpowers z).conjBy g⁻¹) : Set G) := by
            rw [section15_normalizer_conjBy (G := G) (Subgroup.zpowers z) g⁻¹]
      _ = Subgroup.normalizer (Subgroup.zpowers zg : Set G) := by
            rw [← hZg_eq]
      _ = M := hNzg
  have hginv_norm_M : g⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
    section15_mem_normalizer_of_conjBy_eq (G := G) (H := M) hM_conj_inv
  have hg_norm_M : g ∈ Subgroup.normalizer (M : Set G) := by
    simpa using Subgroup.inv_mem (Subgroup.normalizer (M : Set G)) hginv_norm_M
  have hMnorm : Subgroup.normalizer (M : Set G) = M :=
    section15_maximal_normalizer_eq_self_of_mem_ne_one
      (G := G) hM (by simpa [F] using section8FittingSubgroup_le M hzF) hzne
  exact hg (by simpa [hMnorm] using hg_norm_M)

omit [IsMinCE G] in
private theorem CFSG.section15_initial_pCoreIn_le_sigma_compl_fitting_core_of_not_sigma
    {M : Subgroup G} {p : Nat.Primes}
    (hpσ : p ∉ section10SigmaPrimes M) :
    section15PCoreIn p M ≤ section15SigmaComplementFittingCore M := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let P : Subgroup G := section15PCoreIn p M
  let F : Subgroup G := section8FittingSubgroup M
  have hPF : P ≤ F := by
    intro x hx
    have hxmap : x ∈ (pCore p.val M).map M.subtype := by
      simpa [P, section15PCoreIn] using hx
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, rfl⟩
    have hyF : y ∈ fittingSubgroup M := by
      exact pCore_le_fitting M p.val hy
    have hyFsub : y ∈ (section8FittingSubgroup M).subgroupOf M := by
      simpa [section8FittingSubgroup_subgroupOf_eq M] using hyF
    exact hyFsub
  have hPπ :
      IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ P := by
    exact section15_isPiSubgroup_of_isPGroup_of_mem
      (R := G) (π := (section10SigmaPrimes M)ᶜ) (p := p)
      (P := P) (by simpa [P] using section15_pCoreIn_isPGroup p M)
      (by simpa using hpσ)
  have hM_norm_P : M ≤ Subgroup.normalizer (P : Set G) := by
    have hPM : P ≤ M := by
      simpa [P] using section15_pCoreIn_le p M
    have hPnormM : (P.subgroupOf M).Normal := by
      simpa [P] using (section15_pCoreIn_normalIn p M).2
    letI : (P.subgroupOf M).Normal := hPnormM
    exact Subgroup.le_normalizer_of_normal_subgroupOf hPM
  have hF_norm_P : F ≤ Subgroup.normalizer (P : Set G) := by
    exact (section8FittingSubgroup_le M).trans hM_norm_P
  have hPnormF : (P.subgroupOf F).Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPF).2 hF_norm_P
  have hPle :
      P ≤ piCoreIn (section10SigmaPrimes M)ᶜ F :=
    section8_le_piCoreIn_of_normal_isPiSubgroup
      (G := G) (π := (section10SigmaPrimes M)ᶜ)
      (K := P) (H := F) hPF hPnormF hPπ
  simpa [P, F, section15SigmaComplementFittingCore] using hPle

private theorem CFSG.section15_initial_prime_mem_sigma_of_fitting_intersection
    {M MF X : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (_hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (_hXne : X ≠ ⊥)
    {p : Nat.Primes} (hpX : p ∈ subgroupPrimeSet X) :
    p ∈ section10SigmaPrimes M := by
  classical
  by_contra hpσ
  have hpCore_le_Y :
      section15PCoreIn p M ≤ section15SigmaComplementFittingCore M :=
    section15_initial_pCoreIn_le_sigma_compl_fitting_core_of_not_sigma
      (M := M) (p := p) hpσ
  have hYcyc : IsCyclic (section15SigmaComplementFittingCore M) :=
    (corollary_15_5_a (G := G) (M := M) (MF := MF) hM hMF).2.1
  have hPcyc : IsCyclic (section15PCoreIn p M) := by
    letI : IsCyclic (section15SigmaComplementFittingCore M) := hYcyc
    exact Subgroup.isCyclic_of_le hpCore_le_Y
  exact
    section15_initial_pCoreIn_not_cyclic_of_X_prime
      (M := M) (X := X) (g := g) hM hg hX hpX hPcyc


private theorem CFSG.section15_initial_X_isPi_sigma
    {M MF X : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥) :
    IsPiSubgroup (section10SigmaPrimes M) X := by
  intro p hpX
  exact section15_initial_prime_mem_sigma_of_fitting_intersection hM hMF hnotTI hg hX hXne hpX

private theorem CFSG.section15_initial_X_le_msigma_of_sigma
    {M X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hXleM : X ≤ M)
    (hXσ : IsPiSubgroup (section10SigmaPrimes M) X) :
    X ≤ section10Msigma M := by
  classical
  let Xloc : Subgroup M := X.subgroupOf M
  have hXlocσ :
      IsPiSubgroup (G := M) (section10SigmaPrimes M) Xloc := by
    intro p hpXloc
    have hcard : Nat.card Xloc = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hXleM).toEquiv
    exact hXσ p (by simpa [Xloc, hcard] using hpXloc)
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  haveI : ((section10Msigma M).subgroupOf M).Normal := by
    simpa [section15_msigma_subgroupOf_eq] using (section15_msigma_normalIn (M := M)).2
  have hHall :
      IsHallSubgroup (section10SigmaPrimes M)
        ((section10Msigma M).subgroupOf M) := by
    simpa [section15_msigma_subgroupOf_eq] using
      (theorem_10_2_b (G := G) hM).2
  have hXloc_le : Xloc ≤ (section10Msigma M).subgroupOf M :=
    section15_isPiSubgroup_le_normal_hall_of_solvable
      (R := M) (π := section10SigmaPrimes M)
      (N := (section10Msigma M).subgroupOf M) (X := Xloc)
      hMsolv hHall hXlocσ
  intro x hxX
  have hxM : x ∈ M := hXleM hxX
  have hxXloc : (⟨x, hxM⟩ : M) ∈ Xloc := by
    simpa [Xloc, Subgroup.mem_subgroupOf] using hxX
  have hxMsigmaLoc : (⟨x, hxM⟩ : M) ∈ (section10Msigma M).subgroupOf M :=
    hXloc_le hxXloc
  simpa [Subgroup.mem_subgroupOf] using hxMsigmaLoc

private theorem CFSG.section15_initial_X_msigma_cyclic_beta_compl
    {M X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hXleMsigma : X ≤ section10Msigma M) :
    X ≤ section10Msigma M ∧ IsCyclic X ∧
      IsPiSubgroup (section10BetaPrimes M)ᶜ X := by
  classical
  have hXleFg : X ≤ (section8FittingSubgroup M).conjBy g := by
    rw [hX]
    exact inf_le_right
  have hFg_le_Mg : (section8FittingSubgroup M).conjBy g ≤ M.conjBy g :=
    Subgroup.map_mono (section8FittingSubgroup_le M)
  have hXleMg : X ≤ M.conjBy g := hXleFg.trans hFg_le_Mg
  have hXle_inter : X ≤ section10Msigma M ⊓ M.conjBy g :=
    le_inf hXleMsigma hXleMg
  have h12g := (lemma_12_17 (G := G) (M := M)
    (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
    hM hE).2.2 g hg
  have hXcyc : IsCyclic ↥X := by
    letI : IsCyclic ↥(section10Msigma M ⊓ M.conjBy g) := h12g.1
    exact Subgroup.isCyclic_of_le hXle_inter
  have hXβc : IsPiSubgroup (section10BetaPrimes M)ᶜ X :=
    IsPiSubgroup.of_le hXle_inter h12g.2.1
  exact ⟨hXleMsigma, hXcyc, hXβc⟩

private theorem CFSG.section15_initial_prime_not_beta_of_MF
    {M MF X : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (_hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hXleMsigma : X ≤ section10Msigma M)
    (hXβc : IsPiSubgroup (section10BetaPrimes M)ᶜ X)
    {p : Nat.Primes} (hpMF : p ∈ subgroupPrimeSet MF) :
    p ∉ section10BetaPrimes M := by
  classical
  rcases hMF.1 with ⟨hMFM, hMFnormM, hMFnil, hMFHall⟩
  let F : Subgroup G := section8FittingSubgroup M
  have hXleF : X ≤ F := by
    rw [hX]
    exact inf_le_left
  have hXleFg : X ≤ F.conjBy g := by
    rw [hX]
    exact inf_le_right
  have hcard_ne_one : Nat.card X ≠ 1 := by
    intro hcard
    exact hXne ((Subgroup.card_eq_one (H := X)).1 hcard)
  obtain ⟨q0, hq0prime, hq0dvd⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have hqX : q ∈ subgroupPrimeSet X := by
    change q0 ∣ Nat.card X
    exact hq0dvd
  obtain ⟨z, hzX, hzne, hZprime⟩ :=
    section15_exists_primeOrder_zpowers_of_prime_dvd_card
      (G := G) (B := X) (q := q) hq0dvd
  let X₁ : Subgroup G := Subgroup.zpowers z
  rcases hZprime with ⟨hX₁leX_raw, hX₁card_raw⟩
  have hX₁leX : X₁ ≤ X := by
    simpa [X₁] using hX₁leX_raw
  have hX₁card : Nat.card X₁ = q.val := by
    simpa [X₁] using hX₁card_raw
  have hX₁ne : X₁ ≠ ⊥ := by
    simpa [X₁] using (Subgroup.zpowers_ne_bot.mpr hzne)
  have hX₁q : IsPGroup q.val X₁ :=
    section15_isPGroup_of_prime_card (G := G) (A := X₁) (q := q) hX₁card.symm
  have hqβ : q ∉ section10BetaPrimes M := by
    have hqβc : q ∈ (section10BetaPrimes M)ᶜ := hXβc q hqX
    simpa using hqβc
  let C : Subgroup G := subgroupCentralizerIn MF X₁
  have hC_le_MF : C ≤ MF := by
    intro x hx
    exact hx.1
  have hC_le_M : C ≤ M := hC_le_MF.trans hMFM
  have hC_le_cent : C ≤ Subgroup.centralizer (X₁ : Set G) := by
    intro x hx
    exact hx.2
  have hCproper : C ≠ ⊤ := by
    intro hCtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [C, hCtop] using hC_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hX₁leF : X₁ ≤ F := hX₁leX.trans hXleF
  have hX₁leM : X₁ ≤ M := hX₁leF.trans (by simpa [F] using section8FittingSubgroup_le M)
  have hX₁leMsigma : X₁ ≤ section10Msigma M := hX₁leX.trans hXleMsigma
  have hqσ : q ∈ section10SigmaPrimes M := by
    have hq_dvd_X₁ : q.val ∣ Nat.card X₁ := by
      rw [hX₁card]
    have hq_dvd_Msigma : q.val ∣ Nat.card (section10Msigma M) :=
      hq_dvd_X₁.trans (Subgroup.card_dvd_of_le hX₁leMsigma)
    exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card q hq_dvd_Msigma
  have hX₁leFg : X₁ ≤ F.conjBy g := hX₁leX.trans hXleFg
  have hX₁_conj_ginv_le_M : X₁.conjBy g⁻¹ ≤ M := by
    have hto :
        X₁.conjBy g⁻¹ ≤ (F.conjBy g).conjBy g⁻¹ := by
      simpa [Subgroup.conjBy] using
        (Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hX₁leFg)
    have hback : (F.conjBy g).conjBy g⁻¹ = F := by
      simpa [F] using section11_conjBy_inv (G := G) F g
    exact hto.trans (by rw [hback]; simpa [F] using section8FittingSubgroup_le M)
  have hcentralizer_not_le_M : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M := by
    intro hcent_le_M
    have hginvM : g⁻¹ ∈ M :=
      theorem_10_1_e (G := G) (M := M) (X := X₁) (p := q)
        hM hqσ hX₁ne hX₁q hX₁leM hcent_le_M
        (g := g⁻¹) hX₁_conj_ginv_le_M
    exact hg (by simpa using M.inv_mem hginvM)
  have hcentProper : Subgroup.centralizer (X₁ : Set G) ≠ ⊤ := by
    intro hcentTop
    have htop_le_singleton :
        (⊤ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
      intro a _ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyz : y = z := by simpa using hy
      subst y
      have ha_cent_X₁ : a ∈ Subgroup.centralizer (X₁ : Set G) := by
        simp [hcentTop]
      exact Subgroup.mem_centralizer_iff.mp ha_cent_X₁ z (by
        simp [X₁])
    exact
      (section8_centralizer_singleton_ne_top_of_ne_one (G := G) hzne)
        (top_le_iff.mp htop_le_singleton)
  have hCnotUnique : C ∉ section9UniqueSubgroups G := by
    intro hCunique
    rcases hCunique with ⟨_hCproper, M₀, huniq⟩
    have hMcont : M ∈ section9MaximalSubgroupsContaining C := ⟨hM, hC_le_M⟩
    have hM_eq_M₀ : M = M₀ := by
      have hM_single : M ∈ ({M₀} : Set (Subgroup G)) := by
        simpa [huniq] using hMcont
      simpa using hM_single
    rcases section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) hcentProper with ⟨N, hNcont_cent⟩
    have hNcontC : N ∈ section9MaximalSubgroupsContaining C :=
      ⟨hNcont_cent.1, hC_le_cent.trans hNcont_cent.2⟩
    have hN_eq_M₀ : N = M₀ := by
      have hN_single : N ∈ ({M₀} : Set (Subgroup G)) := by
        simpa [huniq] using hNcontC
      simpa using hN_single
    have hN_eq_M : N = M := hN_eq_M₀.trans hM_eq_M₀.symm
    have hcent_le_M : Subgroup.centralizer (X₁ : Set G) ≤ M := by
      simpa [hN_eq_M] using hNcont_cent.2
    exact hcentralizer_not_le_M hcent_le_M
  have hC_rank_le_two : groupRank C ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ groupRank C := by omega
    have htwo : 2 ≤ groupRank C := by omega
    exact hCnotUnique (theorem_9_6 (G := G) (K := C) hCproper htwo (Or.inl hthree))
  intro hpβ
  by_cases hpq : p = q
  · subst p
    exact hqβ hpβ
  · let P : Sylow p.val M := Classical.choice (Sylow.nonempty (p := p.val) (G := M))
    let PG : Subgroup G := section10AmbientSylowSubgroup M P
    have hPGp : IsPGroup p.val PG := by
      change IsPGroup p.val ((P : Subgroup M).map M.subtype)
      exact IsPGroup.map (p := p.val) (H := (P : Subgroup M))
        P.isPGroup' M.subtype
    have hP_le_MFsub : (P : Subgroup M) ≤ MF.subgroupOf M := by
      haveI : (MF.subgroupOf M).Normal := hMFnormM
      exact section15_sylow_le_normal_hall_of_mem hMFHall hpMF P
    have hPG_le_MF : PG ≤ MF := by
      intro x hx
      have hxmap : x ∈ (P : Subgroup M).map M.subtype := by
        simpa [PG, section10AmbientSylowSubgroup] using hx
      rcases Subgroup.mem_map.mp hxmap
        with ⟨y, hyP, rfl⟩
      have hyMF : y ∈ MF.subgroupOf M := hP_le_MFsub hyP
      simpa [Subgroup.mem_subgroupOf] using hyMF
    have hPG_le_F : PG ≤ F :=
      hPG_le_MF.trans (by simpa [F] using section15_MF_le_fitting (M := M) (MF := MF) hMF)
    have hPGπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) PG :=
      section15_isPiSubgroup_of_isPGroup_of_mem
        (R := G) (π := ({p} : Set Nat.Primes)) (p := p) (P := PG)
        hPGp (by simp)
    have hX₁π : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) X₁ :=
      section15_isPiSubgroup_of_isPGroup_of_mem
        (R := G) (π := ({q} : Set Nat.Primes)) (p := q) (P := X₁)
        hX₁q (by simp)
    have hdisj : Disjoint ({p} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
      rw [Set.disjoint_left]
      intro r hrp hrq
      have hr_eq_p : r = p := by simpa using hrp
      have hr_eq_q : r = q := by simpa using hrq
      exact hpq (hr_eq_p.symm.trans hr_eq_q)
    have hPG_cent_X₁ : PG ≤ Subgroup.centralizer (X₁ : Set G) :=
      section10_isPiSubgroup_le_centralizer_of_nilpotent_disjoint
        (G := G) (π := ({p} : Set Nat.Primes)) (ρ := ({q} : Set Nat.Primes))
        (L := F) (A := PG) (B := X₁)
        hdisj (by simpa [F] using section8FittingSubgroup_isNilpotent M)
        hPG_le_F hX₁leF hPGπ hX₁π
    have hPG_le_C : PG ≤ C := by
      intro x hx
      exact ⟨hPG_le_MF hx, hPG_cent_X₁ hx⟩
    have hPG_rank_le_C : groupRank PG ≤ groupRank C := by
      let PGsub : Subgroup C := PG.subgroupOf C
      have ePGsub : PGsub ≃* PG := Subgroup.subgroupOfEquivOfLe (H := PG) (K := C) hPG_le_C
      exact (groupRank_le_of_equiv ePGsub).trans
        (section8_groupRank_le_of_subgroup (G := C) PGsub)
    have hPlocal_rank_le_PG : groupRank (P : Subgroup M) ≤ groupRank PG := by
      let ePG : (P : Subgroup M) ≃* PG :=
        Subgroup.equivMapOfInjective (f := M.subtype) (P : Subgroup M)
          M.subtype_injective
      exact groupRank_le_of_equiv ePG.symm
    have hp_rank_le_two : primeRank p.val M ≤ 2 := by
      exact ((section10_primeRank_le_groupRank_sylow (G := M) P).trans
        (hPlocal_rank_le_PG.trans hPG_rank_le_C)).trans hC_rank_le_two
    have hp_rank_gt_two : 2 < primeRank p.val M := hpβ.1.2
    omega

private theorem CFSG.section15_initial_MF_beta_compl
    {M MF X : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hXleMsigma : X ≤ section10Msigma M)
    (hXβc : IsPiSubgroup (section10BetaPrimes M)ᶜ X) :
    IsPiSubgroup (section10BetaPrimes M)ᶜ MF := by
  intro p hpMF
  exact section15_initial_prime_not_beta_of_MF
    hM hMF hnotTI hg hX hXne hXleMsigma hXβc hpMF

private theorem CFSG.section15_initial_MF_eq_msigma_of_beta_compl
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hMFβc : IsPiSubgroup (section10BetaPrimes M)ᶜ MF) :
    MF = section10Msigma M := by
  classical
  by_contra hne
  rcases section15_exists_kappa_hallSubgroupIn (G := G) (M := M) hM with ⟨K, hK⟩
  rcases theorem_15_2_b (M := M) (MF := MF) (K := K) hM hMF hK hne with
    ⟨_p, q, _hp, _hq, hqint⟩
  exact hMFβc q hqint.1 hqint.2

private theorem CFSG.section15_initial_not_P2
    {M X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hXne : X ≠ ⊥)
    (hXσ : IsPiSubgroup (section10SigmaPrimes M) X)
    (hXβc : IsPiSubgroup (section10BetaPrimes M)ᶜ X) :
    M ∉ section14MFamilyP2 G := by
  classical
  have hcard_ne_one : Nat.card X ≠ 1 := by
    intro hcard
    exact hXne ((Subgroup.card_eq_one (H := X)).1 hcard)
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let p' : Nat.Primes := ⟨p, hpprime⟩
  have hpX : p' ∈ subgroupPrimeSet X := by
    change p ∣ Nat.card X
    exact hpdvd
  have hpσ : p' ∈ section10SigmaPrimes M := hXσ p' hpX
  have hpβ : p' ∉ section10BetaPrimes M := by
    have hpβc : p' ∈ (section10BetaPrimes M)ᶜ := hXβc p' hpX
    simpa using hpβc
  intro hMP2
  rcases section15_exists_kappa_hallSubgroupIn (G := G) (M := M) hM with ⟨K, hK⟩
  have hσeqβ : section10SigmaPrimes M = section10BetaPrimes M :=
    (proposition_14_2_g (G := G) (M := M) (K := K) hMP2 hK).1
  exact hpβ (by simpa [hσeqβ] using hpσ)

/-- Theorem 15.7(a): if `F(M)` is not TI and
`X = F(M) ∩ F(M)^g ≠ 1`, then `M ∈ 𝓜_F ∪ 𝓜_{P₁}` and
`M_F = M_σ`. -/
private theorem CFSG.section15_theorem15_7_initial_reduction
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    M ∈ section14MFamilyF G ∪ section14MFamilyP1 G ∧
      MF = section10Msigma M ∧ X ≤ MF ∧ IsCyclic X := by
  classical
  have hXσ : IsPiSubgroup (section10SigmaPrimes M) X :=
    section15_initial_X_isPi_sigma hM hMF hnotTI hg hX hXne
  have hXleM : X ≤ M := by
    have hXleF : X ≤ section8FittingSubgroup M := by
      rw [hX]
      exact inf_le_left
    exact hXleF.trans (section8FittingSubgroup_le M)
  have hXleMsigma : X ≤ section10Msigma M :=
    section15_initial_X_le_msigma_of_sigma hM hXleM hXσ
  have hXdata :
      X ≤ section10Msigma M ∧ IsCyclic X ∧
        IsPiSubgroup (section10BetaPrimes M)ᶜ X :=
    section15_initial_X_msigma_cyclic_beta_compl hM hg hX hE hXleMsigma
  have hMFβc : IsPiSubgroup (section10BetaPrimes M)ᶜ MF :=
    section15_initial_MF_beta_compl
      hM hMF hnotTI hg hX hXne hXdata.1 hXdata.2.2
  have hMFeq : MF = section10Msigma M :=
    section15_initial_MF_eq_msigma_of_beta_compl hM hMF hMFβc
  have hMnotP2 : M ∉ section14MFamilyP2 G :=
    section15_initial_not_P2 hM hXne hXσ hXdata.2.2
  refine ⟨section15_mem_F_or_P1_of_not_P2 hM hMnotP2, hMFeq, ?_, hXdata.2.1⟩
  rw [hMFeq]
  exact hXdata.1

/-- Theorem 15.7 structural helper: after the initial reduction has forced
`M_F = M_σ`, Lemma 12.19's Hall `β(M)'` subgroup centralizing `E'` is all of
`M_σ`. -/
private theorem CFSG.section15_theorem15_7_msigma_centralizes_derivedE
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    section10Msigma M ≤ Subgroup.centralizer (ambientDerivedSubgroup E : Set G) := by
  classical
  have hXσ : IsPiSubgroup (section10SigmaPrimes M) X :=
    section15_initial_X_isPi_sigma hM hMF hnotTI hg hX hXne
  have hXleM : X ≤ M := by
    have hXleF : X ≤ section8FittingSubgroup M := by
      rw [hX]
      exact inf_le_left
    exact hXleF.trans (section8FittingSubgroup_le M)
  have hXleMsigma : X ≤ section10Msigma M :=
    section15_initial_X_le_msigma_of_sigma hM hXleM hXσ
  have hXdata :
      X ≤ section10Msigma M ∧ IsCyclic X ∧
        IsPiSubgroup (section10BetaPrimes M)ᶜ X :=
    section15_initial_X_msigma_cyclic_beta_compl hM hg hX hE hXleMsigma
  have hMFβc : IsPiSubgroup (section10BetaPrimes M)ᶜ MF :=
    section15_initial_MF_beta_compl
      hM hMF hnotTI hg hX hXne hXdata.1 hXdata.2.2
  have hMFeq : MF = section10Msigma M :=
    section15_initial_MF_eq_msigma_of_beta_compl hM hMF hMFβc
  have hσβc : IsPiSubgroup (section10BetaPrimes M)ᶜ (section10Msigma M) := by
    simpa [← hMFeq] using hMFβc
  rcases lemma_12_19
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE with
    ⟨H, hHHallIn, hHcentD⟩
  rcases hHHallIn with ⟨hHσ, hHHall⟩
  let Hσ : Subgroup (section10Msigma M) := H.subgroupOf (section10Msigma M)
  have hHσ_top : Hσ = ⊤ := by
    apply Subgroup.index_eq_one.mp
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hqprime hqidx
    let p : Nat.Primes := ⟨q, hqprime⟩
    have hpidx : p.val ∣ Hσ.index := by
      simpa [p] using hqidx
    have hp_notβc : p ∉ (section10BetaPrimes M)ᶜ :=
      hHHall.p_in_pi_of_p_dvd_index p hpidx
    have hpMsigma : p ∈ subgroupPrimeSet (section10Msigma M) := by
      have hmul : Hσ.index * Nat.card Hσ = Nat.card (section10Msigma M) :=
        Subgroup.index_mul_card (H := Hσ)
      have hp_mul : p.val ∣ Hσ.index * Nat.card Hσ :=
        dvd_mul_of_dvd_left hpidx _
      simpa [subgroupPrimeSet, hmul] using hp_mul
    exact hp_notβc (hσβc p hpMsigma)
  intro x hxσ
  have hxH : x ∈ H := by
    let xσ : section10Msigma M := ⟨x, hxσ⟩
    have hxHσ : xσ ∈ Hσ := by
      rw [hHσ_top]
      exact trivial
    simpa [Hσ, Subgroup.mem_subgroupOf, xσ] using hxHσ
  exact hHcentD hxH

/-- In the `M_F = M_σ` branch, the Fitting subgroup has prime support only
from `σ(M)` and the `τ₂(M)` complement. -/
private theorem CFSG.section15_fitting_prime_mem_sigma_or_tau2_of_MF_eq_msigma
    {M MF : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M)
    (hpF : p ∈ subgroupPrimeSet (section8FittingSubgroup M)) :
    p ∈ section10SigmaPrimes M ∪ section12Tau2Primes M := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  let S : Subgroup G := section10Msigma M
  let Y : Subgroup G := section15SigmaComplementFittingCore M
  let π : Set Nat.Primes := section10SigmaPrimes M ∪ section12Tau2Primes M
  have hFeq : F = S ⊔ Y := by
    simpa [F, S, Y] using
      section15_fitting_eq_msigma_sup_sigma_compl_core_of_MF_eq_msigma hMF hEq
  have hSleF : S ≤ F := by
    simpa [F, S] using section15_msigma_le_fitting_of_MF_eq_msigma hMF hEq
  have hYleF : Y ≤ F := by
    simpa [F, Y, section15SigmaComplementFittingCore] using
      (piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ
        (section8FittingSubgroup M))
  let Ssub : Subgroup F := S.subgroupOf F
  let Ysub : Subgroup F := Y.subgroupOf F
  have hSσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) S := by
    intro p hp
    exact (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card p hp
  have hYτ2 : IsPiSubgroup (G := G) (section12Tau2Primes M) Y := by
    simpa [Y] using section15_sigma_complement_fitting_core_tau2 hM hMF
  have hSsubσ : IsPiSubgroup (G := F) (section10SigmaPrimes M) Ssub :=
    section15_isPiSubgroup_subgroupOf hSσ hSleF
  have hYsubτ2 : IsPiSubgroup (G := F) (section12Tau2Primes M) Ysub :=
    section15_isPiSubgroup_subgroupOf hYτ2 hYleF
  have hSsubπ : IsPiSubgroup (G := F) π Ssub := by
    intro q hq
    exact Or.inl (hSsubσ q hq)
  have hYsubπ : IsPiSubgroup (G := F) π Ysub := by
    intro q hq
    exact Or.inr (hYsubτ2 q hq)
  have hYsub_eq : Ysub = piCore (section10SigmaPrimes M)ᶜ F := by
    simpa [Ysub, Y, F, section15SigmaComplementFittingCore] using
      (piCore_map_subtype_subgroupOf (G := G)
        (π := (section10SigmaPrimes M)ᶜ) (H := section8FittingSubgroup M))
  haveI : Ysub.Normal := by
    rw [hYsub_eq]
    infer_instance
  have hSubSup_eq : (S ⊔ Y).subgroupOf F = Ssub ⊔ Ysub := by
    exact Subgroup.subgroupOf_sup (A := S) (A' := Y) (B := F) hSleF hYleF
  have hSubSup_top : Ssub ⊔ Ysub = ⊤ := by
    rw [← hSubSup_eq]
    exact Subgroup.subgroupOf_eq_top.mpr (by rw [hFeq])
  have hSupπ : IsPiSubgroup (G := F) π (Ssub ⊔ Ysub) :=
    section15_isPiSubgroup_sup_of_normal_right hSsubπ hYsubπ
  have hTopπ : IsPiSubgroup (G := F) π (⊤ : Subgroup F) := by
    simpa [hSubSup_top] using hSupπ
  have hpTop : p.val ∣ Nat.card (⊤ : Subgroup F) := by
    simpa [F, subgroupPrimeSet, Subgroup.card_top] using hpF
  exact hTopπ p hpTop

/-- Theorem 15.7 structural step: Lemma 12.19 and the Fitting-support
decomposition force `E₃ = 1`. -/
private theorem CFSG.section15_theorem15_7_E3_eq_bot
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    E₃ = ⊥ := by
  classical
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  have hσcentD :
      section10Msigma M ≤ Subgroup.centralizer (ambientDerivedSubgroup E : Set G) :=
    section15_theorem15_7_msigma_centralizes_derivedE
      hM hMF hnotTI hg hX hXne hE
  have hE3leD : E₃ ≤ ambientDerivedSubgroup E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
  have hE3E : E₃ ≤ E := hE.2.2.2.2.1
  have hEM : E ≤ M := hE.1.2.1
  have hE3leCσ : E₃ ≤ subgroupCentralizerIn M (section10Msigma M) := by
    intro x hxE3
    refine ⟨hEM (hE3E hxE3), ?_⟩
    change x ∈ Subgroup.centralizer ((section10Msigma M : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro s hsσ
    exact (Subgroup.mem_centralizer_iff.mp (hσcentD hsσ) x (hE3leD hxE3)).symm
  have hE3leCMF : E₃ ≤ subgroupCentralizerIn M MF := by
    simpa [hred.2.1] using hE3leCσ
  have hE3leF : E₃ ≤ section8FittingSubgroup M :=
    hE3leCMF.trans
      (section15_centralizer_MF_le_fitting_of_MF_eq_msigma hM hMF hred.2.1)
  rcases hE.2.2.2.2 with ⟨hE3E', hHallE3⟩
  apply Subgroup.card_eq_one.mp
  apply section12_card_eq_one_of_no_prime_dvd
  intro p hpE3
  have hpF : p ∈ subgroupPrimeSet (section8FittingSubgroup M) :=
    section8_subgroupPrimeSet_mono hE3leF (by simpa [subgroupPrimeSet] using hpE3)
  have hpστ2 : p ∈ section10SigmaPrimes M ∪ section12Tau2Primes M :=
    section15_fitting_prime_mem_sigma_or_tau2_of_MF_eq_msigma hM hMF hred.2.1 hpF
  have hpτ3 : p ∈ section12Tau3Primes M :=
    hHallE3.p_in_pi_of_p_dvd_card p
      (by simpa [section12_card_subgroupOf_eq hE3E'] using hpE3)
  rcases hpστ2 with hpσ | hpτ2
  · exact hpτ3.1 hpσ
  · exact (section15_tau2_disjoint_tau1_tau3 (M := M) (q := p) hpτ2)
      (Or.inr hpτ3)

/-- Theorem 15.7 local support step: the initial reduction makes `M_σ`
a `β(M)'`-group. -/
private theorem CFSG.section15_theorem15_7_msigma_beta_compl
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    IsPiSubgroup (section10BetaPrimes M)ᶜ (section10Msigma M) := by
  classical
  have hXσ : IsPiSubgroup (section10SigmaPrimes M) X :=
    section15_initial_X_isPi_sigma hM hMF hnotTI hg hX hXne
  have hXleM : X ≤ M := by
    have hXleF : X ≤ section8FittingSubgroup M := by
      rw [hX]
      exact inf_le_left
    exact hXleF.trans (section8FittingSubgroup_le M)
  have hXleMsigma : X ≤ section10Msigma M :=
    section15_initial_X_le_msigma_of_sigma hM hXleM hXσ
  have hXdata :
      X ≤ section10Msigma M ∧ IsCyclic X ∧
        IsPiSubgroup (section10BetaPrimes M)ᶜ X :=
    section15_initial_X_msigma_cyclic_beta_compl hM hg hX hE hXleMsigma
  have hMFβc : IsPiSubgroup (section10BetaPrimes M)ᶜ MF :=
    section15_initial_MF_beta_compl
      hM hMF hnotTI hg hX hXne hXdata.1 hXdata.2.2
  have hMFeq : MF = section10Msigma M :=
    section15_initial_MF_eq_msigma_of_beta_compl hM hMF hMFβc
  simpa [← hMFeq] using hMFβc


/-- Theorem 15.7(d), after `E₃ = 1`: Lemma 12.1 supplies the quotient and
normality conclusions for the Section 12 data. -/
private theorem CFSG.section15_theorem15_7_d_conclusions
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    E₃ = ⊥ ∧ section10NormalIn E₂ E ∧
      section15QuotientMulEquiv E E₂ E₁ ∧ IsCyclic E₁ := by
  classical
  have hE3bot : E₃ = ⊥ :=
    section15_theorem15_7_E3_eq_bot hM hMF hnotTI hg hX hXne hE
  have h12e := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE
  have hE2norm : section10NormalIn E₂ E := by
    simpa [hE3bot, sup_bot_eq] using h12e.2.2.1
  have hE1cyc : IsCyclic E₁ :=
    (lemma_12_1_d (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
  have hE1E : E₁ ≤ E := hE.2.2.1.1.trans hE.2.1.1
  have hE2E : E₂ ≤ E := hE.2.2.2.1.1.trans hE.2.1.1
  have hEsup : E = E₁ ⊔ E₂ := by
    simpa [hE3bot, sup_bot_eq, sup_assoc] using h12e.1
  have hE1E2_disj : Disjoint E₁ E₂ := by
    rw [Subgroup.disjoint_def]
    intro x hxE1 hxE2
    have hcop : Nat.Coprime (Nat.card E₁) (Nat.card E₂) := by
      rcases hE with ⟨_hcomp, _hE12, hE1Hall, hE2Hall, _hE3Hall⟩
      rcases hE1Hall with ⟨hE1E12, hHallE1⟩
      rcases hE2Hall with ⟨hE2E12, hHallE2⟩
      refine Nat.coprime_of_dvd ?_
      intro q hqprime hqE1 hqE2
      let r : Nat.Primes := ⟨q, hqprime⟩
      have hcardE1sub : Nat.card (E₁.subgroupOf E₁₂) = Nat.card E₁ :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := E₁) (K := E₁₂) hE1E12).toEquiv
      have hcardE2sub : Nat.card (E₂.subgroupOf E₁₂) = Nat.card E₂ :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := E₂) (K := E₁₂) hE2E12).toEquiv
      have hr1 : r ∈ section12Tau1Primes M :=
        hHallE1.p_in_pi_of_p_dvd_card r
          (by simpa [hcardE1sub, r] using hqE1)
      have hr2 : r ∈ section12Tau2Primes M :=
        hHallE2.p_in_pi_of_p_dvd_card r
          (by simpa [hcardE2sub, r] using hqE2)
      have h1 : primeRank r.val M = 1 := hr1.2.2
      have h2 : primeRank r.val M = 2 := hr2.2
      omega
    have hxinf : x ∈ E₁ ⊓ E₂ := ⟨hxE1, hxE2⟩
    have hcard_inf_dvd_E1 : Nat.card (E₁ ⊓ E₂ : Subgroup G) ∣ Nat.card E₁ :=
      Subgroup.card_dvd_of_le inf_le_left
    have hcard_inf_dvd_E2 : Nat.card (E₁ ⊓ E₂ : Subgroup G) ∣ Nat.card E₂ :=
      Subgroup.card_dvd_of_le inf_le_right
    have hcop_inf_E2 : Nat.Coprime (Nat.card (E₁ ⊓ E₂ : Subgroup G)) (Nat.card E₂) :=
      Nat.Coprime.of_dvd_left hcard_inf_dvd_E1 hcop
    have hcop_inf_inf :
        Nat.Coprime (Nat.card (E₁ ⊓ E₂ : Subgroup G))
          (Nat.card (E₁ ⊓ E₂ : Subgroup G)) :=
      Nat.Coprime.of_dvd_right hcard_inf_dvd_E2 hcop_inf_E2
    have hcard_inf_one : Nat.card (E₁ ⊓ E₂ : Subgroup G) = 1 := by
      exact Nat.eq_one_of_dvd_coprimes hcop_inf_inf dvd_rfl dvd_rfl
    have hinf_bot : E₁ ⊓ E₂ = (⊥ : Subgroup G) :=
      (Subgroup.card_eq_one (H := E₁ ⊓ E₂)).1 hcard_inf_one
    simpa [hinf_bot] using hxinf
  have hcomp : section12ComplementIn E E₁ E₂ :=
    ⟨hE1E, hE2E, hEsup, hE1E2_disj⟩
  haveI : (E₂.subgroupOf E).Normal := hE2norm.2
  have hcomp' : (E₁.subgroupOf E).IsComplement' (E₂.subgroupOf E) :=
    section15_normal_complementIn_isComplement' hcomp hE2norm
  have hquot : section15QuotientMulEquiv E E₂ E₁ := by
    refine ⟨hE2E, hE2norm.2, ?_⟩
    let eE1 : E₁.subgroupOf E ≃* E₁ :=
      Subgroup.subgroupOfEquivOfLe (H := E₁) (K := E) hE1E
    exact ⟨hcomp'.QuotientMulEquiv.trans eE1⟩
  exact ⟨hE3bot, hE2norm, hquot, hE1cyc⟩


public theorem CFSG.section15_msigma_eq_ambientDerived_of_familyP1
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section10Msigma M = ambientDerivedSubgroup M := by
  classical
  let S : Subgroup G := section10Msigma M
  let Kloc : Subgroup M := K.subgroupOf M
  let Sloc : Subgroup M := S.subgroupOf M
  have hprod : M = K ⊔ S := by
    simpa [S] using section15_familyP1_hall_kappa_sup_msigma_eq hM hP1 hK
  have hSleM : S ≤ M := by
    simpa [S] using (section15_msigma_le (M := M))
  have hSnormM : section10NormalIn S M := by
    simpa [S] using (section15_msigma_normalIn (M := M))
  have hHallK : IsHallSubgroup (section14KappaPrimes M) Kloc := by
    simpa [Kloc] using hK.2
  have hHallS : IsHallSubgroup (section10SigmaPrimes M) Sloc := by
    simpa [S, Sloc, section15_msigma_subgroupOf_eq] using
      (theorem_10_2_b (G := G) hM).2
  have hκσdisj : Disjoint (section14KappaPrimes M) (section10SigmaPrimes M) := by
    rw [hP1.2]
    rw [Set.disjoint_left]
    intro p hpκ hpσ
    exact hpκ.2 hpσ
  have hloc_disj : Disjoint Kloc Sloc :=
    section15_disjoint_of_hall_disjoint_primes hHallK hHallS hκσdisj
  have hdisjKS : Disjoint K S := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxS
    have hxM : x ∈ M := hK.1 hxK
    let xM : M := ⟨x, hxM⟩
    have hxKloc : xM ∈ Kloc := by
      simpa [xM, Kloc, Subgroup.mem_subgroupOf] using hxK
    have hxSloc : xM ∈ Sloc := by
      simpa [xM, S, Sloc, Subgroup.mem_subgroupOf] using hxS
    have hxbot : xM ∈ (⊥ : Subgroup M) :=
      Subgroup.disjoint_def.mp hloc_disj hxKloc hxSloc
    change (xM : G) = (1 : G)
    exact congrArg Subtype.val (by simpa using hxbot)
  have hcomp : section12ComplementIn M K S := by
    refine ⟨hK.1, hSleM, ?_, hdisjKS⟩
    simpa [S] using hprod
  have hcomp' : Kloc.IsComplement' Sloc := by
    simpa [Kloc, Sloc] using
      section15_normal_complementIn_isComplement'
        (M := M) (K := K) (N := S) hcomp hSnormM
  have hKcyc : IsCyclic K := by
    have hMP : M ∈ section14MFamilyP G := hP1.1
    have hZcyc : IsCyclic (section14Z M K) :=
      (theorem_14_7_d (G := G) (M := M) (K := K) hMP hK).2.1
    letI : IsCyclic (section14Z M K) := hZcyc
    exact Subgroup.isCyclic_of_le (show K ≤ section14Z M K by
      change K ≤ K ⊔ section14KStar M K
      exact le_sup_left)
  have hKloc_comm : IsMulCommutative Kloc := by
    letI : IsCyclic K := hKcyc
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    apply Subtype.ext
    exact setLike_mul_comm
      (s := K) x.property y.property
  haveI : Sloc.Normal := by
    simpa [S, Sloc] using hSnormM.2
  let eQ : M ⧸ Sloc ≃* Kloc := hcomp'.QuotientMulEquiv
  have hquot_comm : IsMulCommutative (M ⧸ Sloc) := by
    letI : IsMulCommutative Kloc := hKloc_comm
    letI : CommGroup Kloc := IsMulCommutative.instCommGroup
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eQ.injective
    simpa [map_mul] using (mul_comm (eQ x) (eQ y))
  have hder_le_Sloc : derivedSubgroup M ≤ Sloc :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Sloc)).1 hquot_comm
  have hDleS : ambientDerivedSubgroup M ≤ S := by
    intro x hxD
    have hxM : x ∈ M := section15_ambientDerived_le hxD
    let xM : M := ⟨x, hxM⟩
    have hxDer : xM ∈ derivedSubgroup M := by
      have hxSub : xM ∈ (ambientDerivedSubgroup M).subgroupOf M := by
        simpa [xM, Subgroup.mem_subgroupOf] using hxD
      simpa [section15_ambientDerived_subgroupOf_eq] using hxSub
    have hxS : xM ∈ Sloc := hder_le_Sloc hxDer
    simpa [xM, S, Sloc, Subgroup.mem_subgroupOf] using hxS
  exact le_antisymm
    (by simpa [S] using section15_msigma_le_ambientDerived hM)
    (by simpa [S] using hDleS)

/-- The abelian branch of Theorem 15.7(e) cannot occur in type `𝓟₁`. -/
private theorem CFSG.section15_theorem15_7_not_P1_of_abelian_MF
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFcomm : IsMulCommutative MF) :
    M ∉ section14MFamilyP1 G := by
  classical
  intro hP1
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  rcases section15_exists_kappa_hallSubgroupIn (G := G) (M := M) hM with ⟨K, hK⟩
  have hσD : section10Msigma M = ambientDerivedSubgroup M :=
    section15_msigma_eq_ambientDerived_of_familyP1 hM hP1 hK
  have hD_eq_MF : ambientDerivedSubgroup M = MF := by
    rw [← hσD, ← hred.2.1]
  have hDcomm : IsMulCommutative (ambientDerivedSubgroup M) := by
    rw [hD_eq_MF]
    exact hMFcomm
  have hSecond_bot : section15SecondDerivedSubgroup M = ⊥ := by
    simpa [section15SecondDerivedSubgroup] using
      section15_ambientDerived_eq_bot_of_isMulCommutative
        (M := ambientDerivedSubgroup M) hDcomm
  have h15_6 := corollary_15_6 (G := G) (M := M) (MF := MF) (K := K)
    hP1.1 hMF hK
  have hKstar_bot : section14KStar M K = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    simpa [hSecond_bot] using h15_6.2.2.2.1 hx
  exact h15_6.1 hKstar_bot

/-- The remaining rank computation in the abelian branch of Theorem 15.7(e):
the same prime-order subgroup `X₁≤X` used in the initial reduction bounds
`groupRank M_F` above by two, while the noncyclic `p`-core bounds it below. -/
private theorem CFSG.section15_theorem15_7_rank_MF_eq_two_of_abelian
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFcomm : IsMulCommutative MF) :
    groupRank MF = 2 := by
  classical
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  rcases hMF.1 with ⟨hMFM, _hMFnormM, _hMFnil, _hMFHall⟩
  let F : Subgroup G := section8FittingSubgroup M
  have hXleF : X ≤ F := by
    rw [hX]
    exact inf_le_left
  have hXleFg : X ≤ F.conjBy g := by
    rw [hX]
    exact inf_le_right
  have hXleMF : X ≤ MF := hred.2.2.1
  have hXleMsigma : X ≤ section10Msigma M := by
    simpa [← hred.2.1] using hXleMF
  have hcard_ne_one : Nat.card X ≠ 1 := by
    intro hcard
    exact hXne ((Subgroup.card_eq_one (H := X)).1 hcard)
  obtain ⟨q0, hq0prime, hq0dvd⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have hqX : q ∈ subgroupPrimeSet X := by
    change q0 ∣ Nat.card X
    exact hq0dvd
  obtain ⟨z, hzX, hzne, hZprime⟩ :=
    section15_exists_primeOrder_zpowers_of_prime_dvd_card
      (G := G) (B := X) (q := q) hq0dvd
  let X₁ : Subgroup G := Subgroup.zpowers z
  rcases hZprime with ⟨hX₁leX_raw, hX₁card_raw⟩
  have hX₁leX : X₁ ≤ X := by
    simpa [X₁] using hX₁leX_raw
  have hX₁card : Nat.card X₁ = q.val := by
    simpa [X₁] using hX₁card_raw
  have hX₁ne : X₁ ≠ ⊥ := by
    simpa [X₁] using (Subgroup.zpowers_ne_bot.mpr hzne)
  have hX₁q : IsPGroup q.val X₁ :=
    section15_isPGroup_of_prime_card (G := G) (A := X₁) (q := q) hX₁card.symm
  have hX₁leMF : X₁ ≤ MF := hX₁leX.trans hXleMF
  letI : IsMulCommutative MF := hMFcomm
  let C : Subgroup G := subgroupCentralizerIn MF X₁
  have hC_le_MF : C ≤ MF := by
    intro x hx
    exact hx.1
  have hC_le_M : C ≤ M := hC_le_MF.trans hMFM
  have hC_le_cent : C ≤ Subgroup.centralizer (X₁ : Set G) := by
    intro x hx
    exact hx.2
  have hCproper : C ≠ ⊤ := by
    intro hCtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [C, hCtop] using hC_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hX₁leF : X₁ ≤ F := hX₁leX.trans hXleF
  have hX₁leM : X₁ ≤ M := hX₁leF.trans (by simpa [F] using section8FittingSubgroup_le M)
  have hX₁leMsigma : X₁ ≤ section10Msigma M := hX₁leX.trans hXleMsigma
  have hqσ : q ∈ section10SigmaPrimes M := by
    have hq_dvd_X₁ : q.val ∣ Nat.card X₁ := by
      rw [hX₁card]
    have hq_dvd_Msigma : q.val ∣ Nat.card (section10Msigma M) :=
      hq_dvd_X₁.trans (Subgroup.card_dvd_of_le hX₁leMsigma)
    exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card q hq_dvd_Msigma
  have hX₁leFg : X₁ ≤ F.conjBy g := hX₁leX.trans hXleFg
  have hX₁_conj_ginv_le_M : X₁.conjBy g⁻¹ ≤ M := by
    have hto :
        X₁.conjBy g⁻¹ ≤ (F.conjBy g).conjBy g⁻¹ := by
      simpa [Subgroup.conjBy] using
        (Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hX₁leFg)
    have hback : (F.conjBy g).conjBy g⁻¹ = F := by
      simpa [F] using section11_conjBy_inv (G := G) F g
    exact hto.trans (by rw [hback]; simpa [F] using section8FittingSubgroup_le M)
  have hcentralizer_not_le_M : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M := by
    intro hcent_le_M
    have hginvM : g⁻¹ ∈ M :=
      theorem_10_1_e (G := G) (M := M) (X := X₁) (p := q)
        hM hqσ hX₁ne hX₁q hX₁leM hcent_le_M
        (g := g⁻¹) hX₁_conj_ginv_le_M
    exact hg (by simpa using M.inv_mem hginvM)
  have hcentProper : Subgroup.centralizer (X₁ : Set G) ≠ ⊤ := by
    intro hcentTop
    have htop_le_singleton :
        (⊤ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
      intro a _ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyz : y = z := by simpa using hy
      subst y
      have ha_cent_X₁ : a ∈ Subgroup.centralizer (X₁ : Set G) := by
        simp [hcentTop]
      exact Subgroup.mem_centralizer_iff.mp ha_cent_X₁ z (by
        simp [X₁])
    exact
      (section8_centralizer_singleton_ne_top_of_ne_one (G := G) hzne)
        (top_le_iff.mp htop_le_singleton)
  have hCnotUnique : C ∉ section9UniqueSubgroups G := by
    intro hCunique
    rcases hCunique with ⟨_hCproper, M₀, huniq⟩
    have hMcont : M ∈ section9MaximalSubgroupsContaining C := ⟨hM, hC_le_M⟩
    have hM_eq_M₀ : M = M₀ := by
      have hM_single : M ∈ ({M₀} : Set (Subgroup G)) := by
        simpa [huniq] using hMcont
      simpa using hM_single
    rcases section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) hcentProper with ⟨N, hNcont_cent⟩
    have hNcontC : N ∈ section9MaximalSubgroupsContaining C :=
      ⟨hNcont_cent.1, hC_le_cent.trans hNcont_cent.2⟩
    have hN_eq_M₀ : N = M₀ := by
      have hN_single : N ∈ ({M₀} : Set (Subgroup G)) := by
        simpa [huniq] using hNcontC
      simpa using hN_single
    have hN_eq_M : N = M := hN_eq_M₀.trans hM_eq_M₀.symm
    have hcent_le_M : Subgroup.centralizer (X₁ : Set G) ≤ M := by
      simpa [hN_eq_M] using hNcont_cent.2
    exact hcentralizer_not_le_M hcent_le_M
  have hC_rank_le_two : groupRank C ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ groupRank C := by omega
    have htwo : 2 ≤ groupRank C := by omega
    exact hCnotUnique (theorem_9_6 (G := G) (K := C) hCproper htwo (Or.inl hthree))
  have hX₁leMF : X₁ ≤ MF := hX₁leX.trans hred.2.2.1
  have hCeqMF : C = MF := by
    apply le_antisymm
    · exact hC_le_MF
    · intro x hxMF
      refine ⟨hxMF, ?_⟩
      change x ∈ Subgroup.centralizer (X₁ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyX₁
      exact setLike_mul_comm
        (s := MF) (hX₁leMF hyX₁) hxMF
  have hupper : groupRank MF ≤ 2 := by
    rw [← hCeqMF]
    exact hC_rank_le_two
  have hPnoncyc : ¬ IsCyclic (section15PCoreIn q M) :=
    section15_initial_pCoreIn_not_cyclic_of_X_prime
      (M := M) (X := X) (g := g) hM hg hX hqX
  have hPleMF : section15PCoreIn q M ≤ MF := by
    rw [hred.2.1]
    exact section15_pCoreIn_le_msigma_of_mem_sigma (M := M) hqσ
  obtain ⟨A, hA⟩ :=
    section15_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := section15PCoreIn q M) (p := q)
      (section15_pCoreIn_isPGroup q M) hPnoncyc
  have hA_le_MF : A ≤ MF :=
    (section15_rankTwo_le hA).trans hPleMF
  have hlower : 2 ≤ groupRank MF :=
    section15_groupRank_at_least_two_of_rankTwo_elementary_le
      (K := MF) (A := A) (p := q) hA_le_MF (section15_rankTwo_elementary hA)
  omega

/-- Theorem 15.7(e), abelian branch: an abelian `M_F` forces the first
alternative. -/
private theorem CFSG.section15_theorem15_7_abelian_alternative
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFcomm : IsMulCommutative MF) :
    M ∈ section14MFamilyF G ∧ IsMulCommutative MF ∧ groupRank MF = 2 := by
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  have hnotP1 :
      M ∉ section14MFamilyP1 G :=
    section15_theorem15_7_not_P1_of_abelian_MF
      hM hMF hnotTI hg hX hXne hE hMFcomm
  have hF : M ∈ section14MFamilyF G := by
    rcases hred.1 with hF | hP1
    · exact hF
    · exact False.elim (hnotP1 hP1)
  exact ⟨hF, hMFcomm,
    section15_theorem15_7_rank_MF_eq_two_of_abelian
      hM hMF hnotTI hg hX hXne hE hMFcomm⟩

omit [IsMinCE G] in
public theorem CFSG.section15_isMulCommutative_of_mulEquiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : IsMulCommutative B) :
    IsMulCommutative A := by
  classical
  refine ⟨⟨fun x y => ?_⟩⟩
  letI : IsMulCommutative B := hB
  letI : CommGroup B := IsMulCommutative.instCommGroup
  apply e.injective
  calc
    e (x * y) = e x * e y := e.map_mul x y
    _ = e y * e x := mul_comm (e x) (e y)
    _ = e (y * x) := (e.map_mul y x).symm

omit [IsMinCE G] in
private theorem CFSG.section15_isMulCommutative_of_nilpotent_of_sylow
    {K : Type*} [Group K] [Finite K]
    (hnil : Group.IsNilpotent K)
    (hSyl : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p K),
      IsMulCommutative (P : Subgroup K)) :
    IsMulCommutative K := by
  classical
  let e : (∀ p : (Nat.card K).primeFactors, ∀ P : Sylow p.val K, P) ≃* K :=
    Sylow.directProductOfNormal (G := K) (fun {p} [hp : Fact p.Prime] (P : Sylow p K) =>
      Group.IsNilpotent.sylow_normal hnil p P)
  refine ⟨⟨fun x y => ?_⟩⟩
  let x' := e.symm x
  let y' := e.symm y
  have hxy' : x' * y' = y' * x' := by
    funext p P
    haveI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    have hcomm : IsMulCommutative (P : Subgroup K) := hSyl p.val P
    exact Subtype.ext <|
      setLike_mul_comm (s := (P : Subgroup K))
        (x' p P).property (y' p P).property
  have hxy := congrArg e hxy'
  simpa [x', y'] using hxy

/-- The source's local `E1X_facts`: for every prime-order subgroup
`X₁≤X`, the centralizer in the nonabelian branch is non-unique, has rank at
most two, and is abelian. -/
private theorem CFSG.section15_theorem15_7_prime_order_centralizer_facts
    {M MF X E E₁₂ E₁ E₂ E₃ X₁ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hX₁ : X₁ ∈ section10PrimeOrderSubgroupsIn p X) :
    let C : Subgroup G := subgroupCentralizerIn MF X₁
    C ∉ section9UniqueSubgroups G ∧ groupRank C ≤ 2 ∧ IsMulCommutative C := by
  classical
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  rcases hMF.1 with ⟨hMFM, _hMFnormM, hMFnil, _hMFHall⟩
  let F : Subgroup G := section8FittingSubgroup M
  have hXleF : X ≤ F := by
    rw [hX]
    exact inf_le_left
  have hXleFg : X ≤ F.conjBy g := by
    rw [hX]
    exact inf_le_right
  have hXleMF : X ≤ MF := hred.2.2.1
  have hXleMsigma : X ≤ section10Msigma M := by
    simpa [← hred.2.1] using hXleMF
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX₁) with
    ⟨hX₁leX, hX₁card⟩
  have hX₁leMF : X₁ ≤ MF := hX₁leX.trans hXleMF
  have hX₁ne : X₁ ≠ ⊥ := by
    exact section12_primeOrder_ne_bot hX₁
  have hX₁p : IsPGroup p.val X₁ :=
    section15_isPGroup_of_prime_card (G := G) (A := X₁) (q := p) hX₁card.symm
  let C : Subgroup G := subgroupCentralizerIn MF X₁
  have hC_le_MF : C ≤ MF := by
    intro x hx
    exact hx.1
  have hC_le_M : C ≤ M := hC_le_MF.trans hMFM
  have hC_le_cent : C ≤ Subgroup.centralizer (X₁ : Set G) := by
    intro x hx
    exact hx.2
  have hCproper : C ≠ ⊤ := by
    intro hCtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [C, hCtop] using hC_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hX₁leF : X₁ ≤ F := hX₁leX.trans hXleF
  have hX₁leM : X₁ ≤ M := hX₁leF.trans (by simpa [F] using section8FittingSubgroup_le M)
  have hX₁leMsigma : X₁ ≤ section10Msigma M := hX₁leX.trans hXleMsigma
  have hpσ : p ∈ section10SigmaPrimes M := by
    have hp_dvd_X₁ : p.val ∣ Nat.card X₁ := by
      rw [hX₁card]
    have hp_dvd_Msigma : p.val ∣ Nat.card (section10Msigma M) :=
      hp_dvd_X₁.trans (Subgroup.card_dvd_of_le hX₁leMsigma)
    exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card p hp_dvd_Msigma
  have hX₁leFg : X₁ ≤ F.conjBy g := hX₁leX.trans hXleFg
  have hX₁_conj_ginv_le_M : X₁.conjBy g⁻¹ ≤ M := by
    have hto :
        X₁.conjBy g⁻¹ ≤ (F.conjBy g).conjBy g⁻¹ := by
      simpa [Subgroup.conjBy] using
        (Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hX₁leFg)
    have hback : (F.conjBy g).conjBy g⁻¹ = F := by
      simpa [F] using section11_conjBy_inv (G := G) F g
    exact hto.trans (by rw [hback]; simpa [F] using section8FittingSubgroup_le M)
  have hcentralizer_not_le_M : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M := by
    intro hcent_le_M
    have hginvM : g⁻¹ ∈ M :=
      theorem_10_1_e (G := G) (M := M) (X := X₁) (p := p)
        hM hpσ hX₁ne hX₁p hX₁leM hcent_le_M
        (g := g⁻¹) hX₁_conj_ginv_le_M
    exact hg (by simpa using M.inv_mem hginvM)
  have hcentProper : Subgroup.centralizer (X₁ : Set G) ≠ ⊤ := by
    intro hcentTop
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hX₁ne with ⟨z, hzne⟩
    have hzGne : (z : G) ≠ 1 := by
      intro hz
      exact hzne (Subtype.ext hz)
    have htop_le_singleton :
        (⊤ : Subgroup G) ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
      intro a _ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyz : y = (z : G) := by simpa using hy
      subst y
      have ha_cent_X₁ : a ∈ Subgroup.centralizer (X₁ : Set G) := by
        simp [hcentTop]
      exact Subgroup.mem_centralizer_iff.mp ha_cent_X₁ (z : G) z.property
    exact
      (section8_centralizer_singleton_ne_top_of_ne_one (G := G) hzGne)
        (top_le_iff.mp htop_le_singleton)
  have hCnotUnique : C ∉ section9UniqueSubgroups G := by
    intro hCunique
    rcases hCunique with ⟨_hCproper, M₀, huniq⟩
    have hMcont : M ∈ section9MaximalSubgroupsContaining C := ⟨hM, hC_le_M⟩
    have hM_eq_M₀ : M = M₀ := by
      have hM_single : M ∈ ({M₀} : Set (Subgroup G)) := by
        simpa [huniq] using hMcont
      simpa using hM_single
    rcases section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) hcentProper with ⟨N, hNcont_cent⟩
    have hNcontC : N ∈ section9MaximalSubgroupsContaining C :=
      ⟨hNcont_cent.1, hC_le_cent.trans hNcont_cent.2⟩
    have hN_eq_M₀ : N = M₀ := by
      have hN_single : N ∈ ({M₀} : Set (Subgroup G)) := by
        simpa [huniq] using hNcontC
      simpa using hN_single
    have hN_eq_M : N = M := hN_eq_M₀.trans hM_eq_M₀.symm
    have hcent_le_M : Subgroup.centralizer (X₁ : Set G) ≤ M := by
      simpa [hN_eq_M] using hNcont_cent.2
    exact hcentralizer_not_le_M hcent_le_M
  have hC_rank_le_two : groupRank C ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ groupRank C := by omega
    have htwo : 2 ≤ groupRank C := by omega
    exact hCnotUnique (theorem_9_6 (G := G) (K := C) hCproper htwo (Or.inl hthree))
  have hCcomm : IsMulCommutative C := by
    let Csub : Subgroup MF := C.subgroupOf MF
    have hCsub_nil : Group.IsNilpotent Csub := by
      letI : Group.IsNilpotent MF := hMFnil
      infer_instance
    have hCsub_comm : IsMulCommutative Csub := by
      apply section15_isMulCommutative_of_nilpotent_of_sylow hCsub_nil
      intro r _hr P
      by_contra hPnoncomm
      let φ : Csub →* G := MF.subtype.comp Csub.subtype
      let Pamb : Subgroup G := (P : Subgroup Csub).map φ
      have hPambp : IsPGroup r Pamb := by
        simpa [Pamb, φ] using (P.isPGroup'.map φ)
      have hPambNoncomm : ¬ IsMulCommutative Pamb := by
        intro hPambcomm
        have hPcomm : IsMulCommutative (P : Subgroup Csub) := by
          letI : IsMulCommutative Pamb := hPambcomm
          refine ⟨⟨fun x y => ?_⟩⟩
          have hxPamb : φ x ∈ Pamb := ⟨x, x.property, rfl⟩
          have hyPamb : φ y ∈ Pamb := ⟨y, y.property, rfl⟩
          have hxyG : φ (x * y) = φ (y * x) := by
            calc
              φ (x * y) = φ x * φ y := φ.map_mul x y
              _ = φ y * φ x :=
                setLike_mul_comm (s := Pamb) hxPamb hyPamb
              _ = φ (y * x) := (φ.map_mul y x).symm
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          simpa [φ] using hxyG
        exact hPnoncomm hPcomm
      let rp : Nat.Primes := ⟨r, Fact.out⟩
      have hPunique : Pamb ∈ section9UniqueSubgroups G :=
        theorem_12_13 (G := G) (P := Pamb) (p := rp) (by simpa [rp] using hPambp)
          (by simpa [rp] using hPambNoncomm)
      have hPamb_le_C : Pamb ≤ C := by
        intro z hz
        rcases hz with ⟨u, _huP, rfl⟩
        change (((u : Csub) : MF) : G) ∈ C
        exact Subgroup.mem_subgroupOf.mp u.property
      exact hCnotUnique (section9_unique_of_le hPamb_le_C hCproper hPunique)
    exact section15_isMulCommutative_of_mulEquiv
      (e := (Subgroup.subgroupOfEquivOfLe (H := C) (K := MF) hC_le_MF).symm)
      hCsub_comm
  exact ⟨hCnotUnique, hC_rank_le_two, hCcomm⟩

omit [IsMinCE G] in
private theorem CFSG.section15_pCore_commute_of_ne
    {R : Type*} [Group R] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) :
    ∀ x ∈ pCore p R, ∀ y ∈ pCore q R, x * y = y * x := by
  intro x hx y hy
  have hdisj : Disjoint (pCore p R) (pCore q R) :=
    IsPGroup.disjoint_of_ne p q hpq (pCore p R) (pCore q R)
      pCore_isPGroup pCore_isPGroup
  have hmem_comm : ⁅x, y⁆ ∈ ⁅pCore p R, pCore q R⁆ :=
    Subgroup.commutator_mem_commutator hx hy
  have hle : ⁅pCore p R, pCore q R⁆ ≤ pCore p R ⊓ pCore q R :=
    Subgroup.commutator_le_inf (H₁ := pCore p R) (H₂ := pCore q R)
  have hmem_inf : ⁅x, y⁆ ∈ pCore p R ⊓ pCore q R := hle hmem_comm
  have hinf_eq : (pCore p R ⊓ pCore q R : Subgroup R) = ⊥ := hdisj.eq_bot
  rw [hinf_eq] at hmem_inf
  have h1 : ⁅x, y⁆ = (1 : R) := by simpa using hmem_inf
  rwa [commutatorElement_eq_one_iff_mul_comm] at h1

omit [IsMinCE G] in
private theorem CFSG.section15_nilpotent_sylow_le_centralizer_of_pSubgroup_ne
    {R : Type*} [Group R] [Finite R] [Group.IsNilpotent R]
    {p q : Nat.Primes} (hpq : p ≠ q) (P : Sylow p.val R)
    {Q : Subgroup R} (hQq : IsPGroup q.val Q) :
    (P : Subgroup R) ≤ Subgroup.centralizer (Q : Set R) := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hpq_val : p.val ≠ q.val := by
    intro hpq_val
    exact hpq (Subtype.ext hpq_val)
  have hP_le_core : (P : Subgroup R) ≤ pCore p.val R := by
    have hPnormal : (P : Subgroup R).Normal :=
      Group.IsNilpotent.sylow_normal (p := p.val) inferInstance P
    exact le_sSup ⟨hPnormal, P.isPGroup'⟩
  have hQ_le_core : Q ≤ pCore q.val R := by
    obtain ⟨Q₀, hQ_le_Q₀⟩ := IsPGroup.exists_le_sylow (G := R) (p := q.val) hQq
    have hQ₀normal : (Q₀ : Subgroup R).Normal :=
      Group.IsNilpotent.sylow_normal (p := q.val) inferInstance Q₀
    exact hQ_le_Q₀.trans (le_sSup ⟨hQ₀normal, Q₀.isPGroup'⟩)
  intro x hxP
  rw [Subgroup.mem_centralizer_iff]
  intro y hyQ
  exact (section15_pCore_commute_of_ne hpq_val x (hP_le_core hxP) y (hQ_le_core hyQ)).symm

omit [IsMinCE G] in
private theorem CFSG.section15_pSubgroup_le_centralizer_of_nilpotent_overgroup
    {L X P : Subgroup G} {p q : Nat.Primes} (hpq : p ≠ q)
    (hLnil : Group.IsNilpotent L) (hPL : P ≤ L) (hXL : X ≤ L)
    (hPp : IsPGroup p.val P) (hXq : IsPGroup q.val X) :
    P ≤ Subgroup.centralizer (X : Set G) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Psub : Subgroup L := P.subgroupOf L
  let Xsub : Subgroup L := X.subgroupOf L
  have hPsubp : IsPGroup p.val Psub :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := P) (K := L) hPL).symm
  have hXsubq : IsPGroup q.val Xsub :=
    hXq.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := L) hXL).symm
  obtain ⟨PL, hPsub_le_PL⟩ :=
    IsPGroup.exists_le_sylow (G := L) (p := p.val) hPsubp
  letI : Group.IsNilpotent L := hLnil
  have hPL_cent_Xsub : (PL : Subgroup L) ≤ Subgroup.centralizer (Xsub : Set L) :=
    section15_nilpotent_sylow_le_centralizer_of_pSubgroup_ne
      (R := L) hpq PL hXsubq
  intro y hyP
  rw [Subgroup.mem_centralizer_iff]
  intro x hxX
  let yL : L := ⟨y, hPL hyP⟩
  let xL : L := ⟨x, hXL hxX⟩
  have hyPsub : yL ∈ Psub := hyP
  have hxXsub : xL ∈ Xsub := hxX
  have hcommL :=
    Subgroup.mem_centralizer_iff.mp (hPL_cent_Xsub (hPsub_le_PL hyPsub)) xL hxXsub
  exact congrArg Subtype.val hcommL

omit [IsMinCE G] in
private theorem CFSG.section15_pSubgroup_le_pCoreIn_of_nilpotent
    {H X : Subgroup G} {p : Nat.Primes}
    (hHnil : Group.IsNilpotent H) (hXH : X ≤ H) (hXp : IsPGroup p.val X) :
    X ≤ section15PCoreIn p H := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Xsub : Subgroup H := X.subgroupOf H
  have hXsubp : IsPGroup p.val Xsub :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := H) hXH).symm
  obtain ⟨S, hXsub_le_S⟩ :=
    IsPGroup.exists_le_sylow (G := H) (p := p.val) hXsubp
  letI : Group.IsNilpotent H := hHnil
  have hSnormal : (S : Subgroup H).Normal :=
    Group.IsNilpotent.sylow_normal (p := p.val) hHnil S
  have hS_le_core : (S : Subgroup H) ≤ pCore p.val H :=
    le_sSup ⟨hSnormal, S.isPGroup'⟩
  intro x hx
  let xH : H := ⟨x, hXH hx⟩
  have hxXsub : xH ∈ Xsub := hx
  have hxcore : xH ∈ pCore p.val H := hS_le_core (hXsub_le_S hxXsub)
  change x ∈ (pCore p.val H).map H.subtype
  exact Subgroup.mem_map.mpr ⟨xH, hxcore, rfl⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omegaOneCenter_le
    {p : Nat.Primes} (P : Subgroup G) :
    section10OmegaOneCenter p P ≤ P := by
  intro x hx
  change x ∈ (Ω₁Z p.val P).map P.subtype at hx
  rcases Subgroup.mem_map.mp hx with ⟨xP, _hxΩ, rfl⟩
  exact xP.property

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omegaOneCenter_le_centralizer
    {p : Nat.Primes} (P : Subgroup G) :
    section10OmegaOneCenter p P ≤ Subgroup.centralizer (P : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  change x ∈ (Ω₁Z p.val P).map P.subtype at hx
  rcases Subgroup.mem_map.mp hx with ⟨xP, hxΩ, rfl⟩
  let yP : P := ⟨y, hy⟩
  have hx_center : xP ∈ Subgroup.center P :=
    section15_omega1Z_le_center p.val P hxΩ
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx_center yP)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_isMulCommutative_sup_of_le_centralizer
    {A Y : Subgroup G}
    (hAcomm : IsMulCommutative A) (hYcomm : IsMulCommutative Y)
    (hYleCentA : Y ≤ Subgroup.centralizer (A : Set G)) :
    IsMulCommutative (A ⊔ Y : Subgroup G) := by
  classical
  let D : Subgroup G := A ⊔ Y
  let AD : Subgroup D := A.subgroupOf D
  let YD : Subgroup D := Y.subgroupOf D
  have hA_norm_Y : A ≤ Subgroup.normalizer (Y : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : a * y = y * a :=
        Subgroup.mem_centralizer_iff.mp (hYleCentA hy) a ha
      have hconj : a * y * a⁻¹ = y := by
        calc
          a * y * a⁻¹ = y * a * a⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hconj] using hy
    · intro hy
      let y' : G := a * y * a⁻¹
      have hy'Y : y' ∈ Y := by simpa [y'] using hy
      have hcomm' : a * y' = y' * a :=
        Subgroup.mem_centralizer_iff.mp (hYleCentA hy'Y) a ha
      have hconj : a⁻¹ * y' * a = y' := by
        have h := congrArg (fun t : G => a⁻¹ * t) hcomm'
        simpa [mul_assoc] using h.symm
      have hy_eq : y = y' := by
        calc
          y = a⁻¹ * y' * a := by simp [y', mul_assoc]
          _ = y' := hconj
      simpa [hy_eq] using hy'Y
  haveI : YD.Normal := by
    simpa [D, YD] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := A) (N := Y) hA_norm_Y)
  have hAD_YD_top : AD ⊔ YD = ⊤ := by
    calc
      AD ⊔ YD = D.subgroupOf D := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := A) (A' := Y) (B := D)
          (by simp [D])
          (by simp [D])
      _ = ⊤ := by simp
  refine ⟨⟨fun x y => ?_⟩⟩
  have hxTop : x ∈ AD ⊔ YD := by simp [hAD_YD_top]
  have hyTop : y ∈ AD ⊔ YD := by simp [hAD_YD_top]
  rcases (Subgroup.mem_sup_of_normal_right (s := AD) (t := YD) (x := x)).1 hxTop with
    ⟨aD, haD, bD, hbD, hxab⟩
  rcases (Subgroup.mem_sup_of_normal_right (s := AD) (t := YD) (x := y)).1 hyTop with
    ⟨cD, hcD, dD, hdD, hycd⟩
  let a : G := aD
  let b : G := bD
  let c : G := cD
  let d : G := dD
  have haA : a ∈ A := by simpa [a, AD, Subgroup.mem_subgroupOf] using haD
  have hbY : b ∈ Y := by simpa [b, YD, Subgroup.mem_subgroupOf] using hbD
  have hcA : c ∈ A := by simpa [c, AD, Subgroup.mem_subgroupOf] using hcD
  have hdY : d ∈ Y := by simpa [d, YD, Subgroup.mem_subgroupOf] using hdD
  have hx_eq : (x : G) = a * b := by
    have hval := congrArg (fun z : D => (z : G)) hxab
    simpa [a, b] using hval.symm
  have hy_eq : (y : G) = c * d := by
    have hval := congrArg (fun z : D => (z : G)) hycd
    simpa [c, d] using hval.symm
  have hac : a * c = c * a :=
    setLike_mul_comm (s := A) haA hcA
  have hbd : b * d = d * b :=
    setLike_mul_comm (s := Y) hbY hdY
  have hbc : b * c = c * b :=
    (Subgroup.mem_centralizer_iff.mp (hYleCentA hbY) c hcA).symm
  have had : a * d = d * a :=
    Subgroup.mem_centralizer_iff.mp (hYleCentA hdY) a haA
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  rw [hx_eq, hy_eq]
  calc
    (a * b) * (c * d) = a * (b * c) * d := by simp [mul_assoc]
    _ = a * (c * b) * d := by rw [hbc]
    _ = (a * c) * (b * d) := by simp [mul_assoc]
    _ = (c * a) * (d * b) := by rw [hac, hbd]
    _ = c * (a * d) * b := by simp [mul_assoc]
    _ = c * (d * a) * b := by rw [had]
    _ = (c * d) * (a * b) := by simp [mul_assoc]

private theorem CFSG.section15_theorem15_7_pCore_noncomm_of_primeOrder_centralizer
    {M MF X E E₁₂ E₁ E₂ E₃ X₁ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hX₁ : X₁ ∈ section10PrimeOrderSubgroupsIn p X) :
    ¬ IsMulCommutative (section15PCoreIn p MF) := by
  classical
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  rcases hMF.1 with ⟨hMFleM, _hMFnormM, hMFnil, _hMFHall⟩
  have hfacts :=
    section15_theorem15_7_prime_order_centralizer_facts
      (G := G) hM hMF hnotTI hg hX hXne hE hX₁
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX₁) with
    ⟨hX₁leX, hX₁card⟩
  have hXleMF : X ≤ MF := hred.2.2.1
  have hX₁leMF : X₁ ≤ MF := hX₁leX.trans hXleMF
  have hX₁p : IsPGroup p.val X₁ :=
    section15_isPGroup_of_prime_card (G := G) (A := X₁) (q := p) hX₁card.symm
  intro hPcomm
  apply hMFnoncomm
  apply section15_isMulCommutative_of_nilpotent_of_sylow hMFnil
  intro r _hr S
  by_cases hrp : r = p.val
  · subst r
    haveI : Fact p.val.Prime := ⟨p.property⟩
    refine ⟨⟨fun x y => ?_⟩⟩
    have hSnormal : (S : Subgroup MF).Normal :=
      Group.IsNilpotent.sylow_normal (p := p.val) hMFnil S
    have hS_le_core : (S : Subgroup MF) ≤ pCore p.val MF :=
      le_sSup ⟨hSnormal, S.isPGroup'⟩
    have hxP : (((x : S) : MF) : G) ∈ section15PCoreIn p MF := by
      change (((x : S) : MF) : G) ∈ (pCore p.val MF).map MF.subtype
      exact Subgroup.mem_map.mpr ⟨(x : MF), hS_le_core x.property, rfl⟩
    have hyP : (((y : S) : MF) : G) ∈ section15PCoreIn p MF := by
      change (((y : S) : MF) : G) ∈ (pCore p.val MF).map MF.subtype
      exact Subgroup.mem_map.mpr ⟨(y : MF), hS_le_core y.property, rfl⟩
    have hxyG :
        (((x * y : S) : MF) : G) = (((y * x : S) : MF) : G) :=
      setLike_mul_comm
        (s := section15PCoreIn p MF) hxP hyP
    apply Subtype.ext
    apply Subtype.ext
    exact hxyG
  · let rp : Nat.Primes := ⟨r, Fact.out⟩
    have hrp' : rp ≠ p := by
      intro h
      exact hrp (congrArg (fun q : Nat.Primes => q.val) h)
    let X₁sub : Subgroup MF := X₁.subgroupOf MF
    have hX₁subp : IsPGroup p.val X₁sub :=
      hX₁p.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := X₁) (K := MF) hX₁leMF).symm
    letI : Group.IsNilpotent MF := hMFnil
    have hScentX₁ : (S : Subgroup MF) ≤ Subgroup.centralizer (X₁sub : Set MF) := by
      simpa [rp] using
        section15_nilpotent_sylow_le_centralizer_of_pSubgroup_ne
          (R := MF) (p := rp) (q := p) hrp' S hX₁subp
    refine ⟨⟨fun x y => ?_⟩⟩
    let C : Subgroup G := subgroupCentralizerIn MF X₁
    have hxC : (((x : S) : MF) : G) ∈ C := by
      refine ⟨(x : MF).property, ?_⟩
      change (((x : S) : MF) : G) ∈ Subgroup.centralizer (X₁ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hzX₁
      let zMF : MF := ⟨z, hX₁leMF hzX₁⟩
      have hcommMF :
          zMF * (x : MF) = (x : MF) * zMF :=
        Subgroup.mem_centralizer_iff.mp (hScentX₁ x.property) zMF hzX₁
      exact congrArg Subtype.val hcommMF
    have hyC : (((y : S) : MF) : G) ∈ C := by
      refine ⟨(y : MF).property, ?_⟩
      change (((y : S) : MF) : G) ∈ Subgroup.centralizer (X₁ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hzX₁
      let zMF : MF := ⟨z, hX₁leMF hzX₁⟩
      have hcommMF :
          zMF * (y : MF) = (y : MF) * zMF :=
        Subgroup.mem_centralizer_iff.mp (hScentX₁ y.property) zMF hzX₁
      exact congrArg Subtype.val hcommMF
    haveI : IsMulCommutative C := by
      simpa [C] using hfacts.2.2
    have hxyG :
        (((x * y : S) : MF) : G) = (((y * x : S) : MF) : G) :=
      setLike_mul_comm (s := C) hxC hyC
    apply Subtype.ext
    apply Subtype.ext
    exact hxyG

private theorem CFSG.section15_theorem15_7_X_eq_primeOrder_and_centralizer_split_of_nonabelian_MF
    {M MF X E E₁₂ E₁ E₂ E₃ X₁ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hX₁ : X₁ ∈ section10PrimeOrderSubgroupsIn p X) :
    X = X₁ ∧
      ∃ Z : Subgroup G,
        IsCyclic Z ∧ Disjoint X₁ Z ∧
          subgroupCentralizerIn (section15PCoreIn p MF)
            (X₁ ⊔ section10OmegaOneCenter p (section15PCoreIn p MF)) = X₁ ⊔ Z := by
  classical
  have hfacts :=
    section15_theorem15_7_prime_order_centralizer_facts
      (G := G) hM hMF hnotTI hg hX hXne hE hX₁
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  rcases hMF.1 with ⟨hMFleM, _hMFnormM, hMFnil, _hMFHall⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX₁) with
    ⟨hX₁leX, hX₁card⟩
  have hXleMF : X ≤ MF := hred.2.2.1
  have hX₁leMF : X₁ ≤ MF := hX₁leX.trans hXleMF
  have hX₁p : IsPGroup p.val X₁ :=
    section15_isPGroup_of_prime_card (G := G) (A := X₁) (q := p) hX₁card.symm
  have hPnoncomm : ¬ IsMulCommutative (section15PCoreIn p MF) :=
    section15_theorem15_7_pCore_noncomm_of_primeOrder_centralizer
      (G := G) hM hMF hnotTI hg hX hXne hE hMFnoncomm hX₁
  have hXp : IsPGroup p.val X := by
    apply section8_isPGroup_of_isPiSubgroup_singleton
    intro q hqX
    have hqeqp : q = p := by
      by_contra hqne
      obtain ⟨z, _hzX, _hzne, hX₂prime⟩ :=
        section15_exists_primeOrder_zpowers_of_prime_dvd_card
          (G := G) (B := X) (q := q) hqX
      let X₂ : Subgroup G := Subgroup.zpowers z
      have hX₂leX : X₂ ≤ X := hX₂prime.1
      have hX₂leMF : X₂ ≤ MF := hX₂leX.trans hXleMF
      have hX₂q : IsPGroup q.val X₂ :=
        section15_isPGroup_of_prime_card (G := G) (A := X₂) (q := q)
          hX₂prime.2.symm
      have hP_le_cent_X₂ :
          section15PCoreIn p MF ≤ Subgroup.centralizer (X₂ : Set G) :=
        section15_pSubgroup_le_centralizer_of_nilpotent_overgroup
          (G := G) (L := MF) (X := X₂) (P := section15PCoreIn p MF)
          (p := p) (q := q) (by intro hpq; exact hqne hpq.symm)
          hMFnil (section15_pCoreIn_le p MF) hX₂leMF
          (section15_pCoreIn_isPGroup p MF) hX₂q
      have hfacts₂ :=
        section15_theorem15_7_prime_order_centralizer_facts
          (G := G) (M := M) (MF := MF) (X := X) (E := E)
          (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
          (X₁ := X₂) (g := g) (p := q)
          hM hMF hnotTI hg hX hXne hE (by simpa [X₂] using hX₂prime)
      let C₂ : Subgroup G := subgroupCentralizerIn MF X₂
      have hP_le_C₂ : section15PCoreIn p MF ≤ C₂ := by
        intro y hyP
        exact ⟨section15_pCoreIn_le p MF hyP, hP_le_cent_X₂ hyP⟩
      have hPcomm : IsMulCommutative (section15PCoreIn p MF) := by
        haveI : IsMulCommutative C₂ := by
          simpa [C₂] using hfacts₂.2.2
        refine ⟨⟨fun a b => ?_⟩⟩
        have hcommG :
            (a : G) * (b : G) = (b : G) * (a : G) :=
          setLike_mul_comm
            (s := C₂) (hP_le_C₂ a.property) (hP_le_C₂ b.property)
        exact Subtype.ext hcommG
      exact hPnoncomm hPcomm
    simp [hqeqp]
  have hXleP : X ≤ section15PCoreIn p MF :=
    section15_pSubgroup_le_pCoreIn_of_nilpotent
      (G := G) (H := MF) (X := X) (p := p) hMFnil hXleMF hXp
  let P : Subgroup G := section15PCoreIn p MF
  let Z₀ : Subgroup G := section10OmegaOneCenter p P
  have hX₁notleZ₀ : ¬ X₁ ≤ Z₀ := by
    intro hX₁leZ₀
    have hP_le_C : P ≤ subgroupCentralizerIn MF X₁ := by
      intro x hxP
      refine ⟨section15_pCoreIn_le p MF (by simpa [P] using hxP), ?_⟩
      change x ∈ Subgroup.centralizer (X₁ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyX₁
      have hyZ₀ : y ∈ Z₀ := hX₁leZ₀ hyX₁
      have hy_cent_P : y ∈ Subgroup.centralizer (P : Set G) := by
        simpa [Z₀] using section15_omegaOneCenter_le_centralizer (G := G) (p := p) P hyZ₀
      exact (Subgroup.mem_centralizer_iff.mp hy_cent_P x hxP).symm
    have hPcomm : IsMulCommutative P := by
      haveI : IsMulCommutative (subgroupCentralizerIn MF X₁) := by
        simpa using hfacts.2.2
      refine ⟨⟨fun a b => ?_⟩⟩
      have hcommG :
          (a : G) * (b : G) = (b : G) * (a : G) :=
        setLike_mul_comm
          (s := subgroupCentralizerIn MF X₁) (hP_le_C a.property) (hP_le_C b.property)
      exact Subtype.ext hcommG
    exact hPnoncomm (by simpa [P] using hPcomm)
  have hX₁neZ₀ : X₁ ≠ Z₀ := by
    intro hX₁eqZ₀
    exact hX₁notleZ₀ (by rw [hX₁eqZ₀])
  have hZ₀leP : Z₀ ≤ P := by
    simpa [Z₀] using section15_omegaOneCenter_le (G := G) (p := p) P
  have hX₁leP : X₁ ≤ P := hX₁leX.trans hXleP
  let B : Subgroup G := X₁ ⊔ Z₀
  have hPp : IsPGroup p.val P := by
    simpa [P] using section15_pCoreIn_isPGroup p MF
  have hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G) := by
    have hp_dvd_X₁ : p.val ∣ Nat.card X₁ := by rw [hX₁card]
    have hp_dvd_G : p.val ∣ Nat.card G :=
      hp_dvd_X₁.trans (Subgroup.card_subgroup_dvd_card X₁)
    simpa [subgroupPrimeSet] using hp_dvd_G
  have hBleP : B ≤ P := by
    simpa [B] using sup_le hX₁leP hZ₀leP
  have hX₁B : X₁ ∈ section10PrimeOrderSubgroupsIn p B := by
    exact ⟨by simp [B], hX₁card⟩
  have hBmax : B ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G := by
    haveI : Fact p.val.Prime := ⟨p.property⟩
    let C : Subgroup G := subgroupCentralizerIn MF X₁
    have hCnotUnique : C ∉ section9UniqueSubgroups G := by
      simpa [C] using hfacts.1
    have hCrank : groupRank C ≤ 2 := by
      simpa [C] using hfacts.2.1
    have hX₁elem : IsElementaryAbelian p.val X₁ := by
      haveI : IsCyclic X₁ := isCyclic_of_prime_card (p := p.val) hX₁card
      exact section15_isElementaryAbelian_of_prime_card_isCyclic
        (p := p.val) (H := X₁) hX₁card
    have hZ₀elem : IsElementaryAbelian p.val Z₀ := by
      simpa [Z₀] using
        section15_omegaOneCenter_isElementaryAbelian (G := G) (p := p) P
    have hZ₀leCentX₁ : Z₀ ≤ Subgroup.centralizer (X₁ : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro x hxX₁
      have hz_cent_P : z ∈ Subgroup.centralizer (P : Set G) := by
        simpa [Z₀] using
          section15_omegaOneCenter_le_centralizer (G := G) (p := p) P hz
      exact Subgroup.mem_centralizer_iff.mp hz_cent_P x (hX₁leP hxX₁)
    have hBelem : IsElementaryAbelian p.val B := by
      letI : IsElementaryAbelian p.val X₁ := hX₁elem
      letI : IsElementaryAbelian p.val Z₀ := hZ₀elem
      simpa [B] using
        section15_isElementaryAbelian_sup_of_le_centralizer
          (G := G) (p := p.val) (E := X₁) (D := Z₀) hZ₀leCentX₁
    have hB_le_C : B ≤ C := by
      have hB_le_cent_X₁ : B ≤ Subgroup.centralizer (X₁ : Set G) := by
        simpa [B] using
          (show X₁ ⊔ Z₀ ≤ Subgroup.centralizer (X₁ : Set G) from
            sup_le
              (by
                intro x hxX₁
                rw [Subgroup.mem_centralizer_iff]
                intro y hyX₁
                haveI : IsElementaryAbelian p.val X₁ := hX₁elem
                exact
                  setLike_mul_comm
                    (s := X₁) hyX₁ hxX₁)
              hZ₀leCentX₁)
      intro x hxB
      exact ⟨section15_pCoreIn_le p MF (by simpa [P] using hBleP hxB),
        hB_le_cent_X₁ hxB⟩
    have hX₁nebot : X₁ ≠ ⊥ := by
      intro hbot
      exact p.property.ne_one (by
        rw [← hX₁card, (Subgroup.card_eq_one (H := X₁)).2 hbot])
    have hPnebot : P ≠ ⊥ := by
      intro hPbot
      exact hX₁nebot <| le_bot_iff.mp <| by
        intro x hx
        simpa [hPbot] using hX₁leP hx
    haveI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPnebot
    have hZ₀nebot : Z₀ ≠ ⊥ := by
      simpa [Z₀] using
        section15_omegaOneCenter_ne_bot_of_nontrivial_pSubgroup
          (G := G) (p := p) (P := P) hPp
    have hX₁infZ₀_bot : X₁ ⊓ Z₀ = ⊥ := by
      by_contra hne
      have hX₁leZ₀' : X₁ ≤ Z₀ :=
        section15_le_of_prime_card_inf_ne_bot
          (G := G) (A := X₁) (B := Z₀) (q := p) hX₁card.symm hne
      exact hX₁notleZ₀ hX₁leZ₀'
    have hZ₀notleX₁ : ¬ Z₀ ≤ X₁ := by
      intro hZ₀leX₁
      have hZ₀leInf : Z₀ ≤ X₁ ⊓ Z₀ := by
        intro z hz
        exact ⟨hZ₀leX₁ hz, hz⟩
      exact hZ₀nebot (le_bot_iff.mp (by simpa [hX₁infZ₀_bot] using hZ₀leInf))
    have hX₁ltB : X₁ < B := by
      refine lt_of_le_of_ne (by simp [B] : X₁ ≤ B) ?_
      intro hX₁eqB
      have hB_le_X₁ : B ≤ X₁ := by rw [← hX₁eqB]
      exact hZ₀notleX₁ ((by simp [B] : Z₀ ≤ B).trans hB_le_X₁)
    have hp_lt_cardB : p.val < Nat.card B := by
      simpa [hX₁card] using natCard_lt_of_subgroup_lt hX₁ltB
    have hBp : IsPGroup p.val B := by
      letI : IsElementaryAbelian p.val B := hBelem
      exact IsElementaryAbelian.isPGroup p.val B
    have hBcard_lower : p.val ^ 2 ≤ Nat.card B := by
      rcases hBp.exists_card_eq with ⟨n, hn⟩
      have hn_ge_two : 2 ≤ n := by
        by_cases hn0 : n = 0
        · have hp_lt_one : p.val < 1 := by simpa [hn, hn0] using hp_lt_cardB
          exact False.elim ((not_lt_of_ge p.property.one_lt.le) hp_lt_one)
        by_cases hn1 : n = 1
        · simp [hn, hn1] at hp_lt_cardB
        omega
      rw [hn]
      exact Nat.pow_le_pow_right p.property.pos hn_ge_two
    have hBgen_le_rankC : generatorRank B ≤ groupRank C := by
      let Bsub : Subgroup C := B.subgroupOf C
      have hBsubp : IsPGroup p.val Bsub :=
        hBp.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := B) (K := C) hB_le_C).symm
      have hBsubcomm : IsMulCommutative Bsub := by
        letI : IsMulCommutative B := hBelem.toIsMulCommutative
        exact Subgroup.subgroupOf_isMulCommutative (H := B) (K := C)
      have hgen_eq : generatorRank Bsub = generatorRank B := by
        rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
        exact Group.rank_congr
          (Subgroup.subgroupOfEquivOfLe (H := B) (K := C) hB_le_C)
      have hgen_le_prime : generatorRank Bsub ≤ primeRank p.val C :=
        section12_generatorRank_le_primeRank_of_subgroup
          (R := C) (q := p.val) hBsubp hBsubcomm
      have hprime_le_rankC : primeRank p.val C ≤ groupRank C := by
        let S : Sylow p.val C :=
          Classical.choice (Sylow.nonempty (p := p.val) (G := C))
        exact
          (section10_primeRank_le_groupRank_sylow (G := C) (p := p) S).trans
            (section8_groupRank_le_of_subgroup (G := C) (S : Subgroup C))
      have hgen_le_prime' : generatorRank B ≤ primeRank p.val C := by
        simpa [hgen_eq] using hgen_le_prime
      exact hgen_le_prime'.trans hprime_le_rankC
    have hBgen_le_two : generatorRank B ≤ 2 := hBgen_le_rankC.trans hCrank
    have hBcard_upper : Nat.card B ≤ p.val ^ 2 := by
      letI : IsElementaryAbelian p.val B := hBelem
      letI : CommGroup B := IsMulCommutative.instCommGroup
      have hcard_dvd : Nat.card B ∣ p.val ^ Group.rank B := by
        simpa using card_dvd_exponent_pow_rank' (G := B) (n := p.val) (fun b =>
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (show Monoid.exponent B ∣ p.val by
              simpa using IsElementaryAbelian.exponent_dvd_p p.val B) b)
      have hrank_le_two : Group.rank B ≤ 2 := by
        simpa [generatorRank_eq_group_rank] using hBgen_le_two
      calc
        Nat.card B ≤ p.val ^ Group.rank B :=
          Nat.le_of_dvd (pow_pos p.property.pos _) hcard_dvd
        _ ≤ p.val ^ 2 := Nat.pow_le_pow_right p.property.pos hrank_le_two
    have hBcard : Nat.card B = p.val ^ 2 :=
      le_antisymm hBcard_upper hBcard_lower
    have hBrankTwo : B ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := ⟨hBcard, hBelem⟩
    have hBmaxElem : B ∈ maximalElementaryAbelianSubgroups p.val G := by
      by_contra hBnotmax
      have hBunique : B ∈ section9UniqueSubgroups G :=
        theorem_9_6_in_particular (G := G)
          ⟨p.val, p.property, hBrankTwo, hBnotmax⟩
      have hCproper : C ≠ ⊤ := by
        have hC_le_M : C ≤ M := by
          intro x hxC
          exact hMFleM hxC.1
        intro hCtop
        have htop_le_M : (⊤ : Subgroup G) ≤ M := by
          simpa [hCtop] using hC_le_M
        exact hM.1 (top_le_iff.mp htop_le_M)
      exact hCnotUnique (section9_unique_of_le hB_le_C hCproper hBunique)
    exact ⟨hBrankTwo, hBmaxElem⟩
  obtain ⟨Z, hZ₀leZ, hZcyc, hdisjX₁Z, hCPeq⟩ :=
    lemma_10_13_b (G := G) (p := p) (A := B) (P := P) (A₀ := X₁)
      hpG hBmax hPp (by simpa [P] using hPnoncomm) hBleP hX₁B
      (by simpa [Z₀, P] using hX₁neZ₀)
  have hXcomm : IsMulCommutative X := by
    letI : IsCyclic X := hred.2.2.2
    letI : CommGroup X := IsCyclic.commGroup
    infer_instance
  have hXleCP : X ≤ subgroupCentralizerIn P B := by
    intro x hxX
    refine ⟨by simpa [P] using hXleP hxX, ?_⟩
    change x ∈ Subgroup.centralizer (B : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hyB
    have hB_le_cent_x : B ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · intro y hyX₁
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hz_eq : z = x := by simpa using hz
        subst z
        exact
          setLike_mul_comm
            (s := X) hxX (hX₁leX hyX₁)
      · intro y hyZ₀
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hz_eq : z = x := by simpa using hz
        subst z
        have hy_cent_P : y ∈ Subgroup.centralizer (P : Set G) := by
          simpa [Z₀] using
            section15_omegaOneCenter_le_centralizer (G := G) (p := p) P hyZ₀
        exact Subgroup.mem_centralizer_iff.mp hy_cent_P x (by simpa [P] using hXleP hxX)
    have hy_cent_x : y ∈ Subgroup.centralizer ({x} : Set G) := hB_le_cent_x hyB
    exact (Subgroup.mem_centralizer_iff.mp hy_cent_x x (by simp)).symm
  have hOmegaX_card :
      Nat.card (section12OmegaOneSubgroup p X) = p.val :=
    section15_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
      (G := G) (H := X) (p := p) hXp hred.2.2.2 hXne
  have hOmegaX_primeX :
      section12OmegaOneSubgroup p X ∈ section10PrimeOrderSubgroupsIn p X :=
    ⟨section15_omegaOneSubgroup_le, hOmegaX_card⟩
  have hX₁_le_OmegaX : X₁ ≤ section12OmegaOneSubgroup p X :=
    section15_primeOrder_le_omegaOneSubgroup_of_le (G := G) (H := X) (X := X₁) hX₁
  have hOmegaX_eq_X₁ : section12OmegaOneSubgroup p X = X₁ := by
    symm
    exact
      section15_eq_of_le_primeOrderSubgroupsIn
        (G := G) (A := X) (X := X₁) (Y := section12OmegaOneSubgroup p X) (p := p)
        hX₁ hOmegaX_primeX hX₁_le_OmegaX
  have hXinfZ_bot : X ⊓ Z = ⊥ := by
    by_contra hXinfZ_ne
    have hOmegaX_le_inf : section12OmegaOneSubgroup p X ≤ X ⊓ Z :=
      section15_omegaOneSubgroup_le_of_nontrivial_subgroup_of_cyclic_pSubgroup
        (G := G) (H := X) (K := X ⊓ Z) (p := p)
        hXp hred.2.2.2 hXne inf_le_left hXinfZ_ne
    have hX₁leZ : X₁ ≤ Z := by
      intro x hxX₁
      have hxOmega : x ∈ section12OmegaOneSubgroup p X := by
        simpa [hOmegaX_eq_X₁] using hxX₁
      exact (hOmegaX_le_inf hxOmega).2
    have hX₁leInf : X₁ ≤ X₁ ⊓ Z := by
      intro x hxX₁
      exact ⟨hxX₁, hX₁leZ hxX₁⟩
    have hX₁infZ_bot : X₁ ⊓ Z = ⊥ := hdisjX₁Z.eq_bot
    have hX₁bot : X₁ = ⊥ := by
      apply le_bot_iff.mp
      intro x hxX₁
      have hxInf : x ∈ X₁ ⊓ Z := hX₁leInf hxX₁
      simpa [hX₁infZ_bot] using hxInf
    have hX₁nebot : X₁ ≠ ⊥ := by
      intro hbot
      exact p.property.ne_one (by
        rw [← hX₁card, (Subgroup.card_eq_one (H := X₁)).2 hbot])
    exact hX₁nebot hX₁bot
  have hZleCP : Z ≤ subgroupCentralizerIn P B := by
    intro z hz
    rw [hCPeq]
    exact (show Z ≤ X₁ ⊔ Z from le_sup_right) hz
  have hZleCentX₁ : Z ≤ Subgroup.centralizer (X₁ : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX₁
    exact Subgroup.mem_centralizer_iff.mp (hZleCP hz).2 x
      ((show X₁ ≤ B from by simp [B]) hxX₁)
  have hX₁comm : IsMulCommutative X₁ := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    exact
      setLike_mul_comm
        (s := X) (hX₁leX a.property) (hX₁leX b.property)
  have hZcomm : IsMulCommutative Z := by
    letI : IsCyclic Z := hZcyc
    letI : CommGroup Z := IsCyclic.commGroup
    infer_instance
  have hDcomm : IsMulCommutative (X₁ ⊔ Z : Subgroup G) :=
    section15_isMulCommutative_sup_of_le_centralizer
      (G := G) hX₁comm hZcomm hZleCentX₁
  have hXleX₁ : X ≤ X₁ := by
    intro x hxX
    have hxCP : x ∈ subgroupCentralizerIn P B := hXleCP hxX
    have hxD : x ∈ X₁ ⊔ Z := by
      simpa [hCPeq] using hxCP
    let D : Subgroup G := X₁ ⊔ Z
    let X₁D : Subgroup D := X₁.subgroupOf D
    let ZD : Subgroup D := Z.subgroupOf D
    haveI : IsMulCommutative D := by simpa [D] using hDcomm
    letI : CommGroup D := IsMulCommutative.instCommGroup
    haveI : X₁D.Normal := by
      infer_instance
    have hX₁D_ZD_top : X₁D ⊔ ZD = ⊤ := by
      calc
        X₁D ⊔ ZD = D.subgroupOf D := by
          exact
            (Subgroup.subgroupOf_sup
              (A := X₁) (A' := Z) (B := D)
              (by simp [D]) (by simp [D])).symm
        _ = ⊤ := by simp
    have hxTop : (⟨x, hxD⟩ : D) ∈ X₁D ⊔ ZD := by
      simp [hX₁D_ZD_top]
    rcases (Subgroup.mem_sup_of_normal_left
        (s := X₁D) (t := ZD) (x := (⟨x, hxD⟩ : D))).1 hxTop with
      ⟨aD, haD, zD, hzD, hxaz⟩
    let a : G := aD
    let z : G := zD
    have haX₁ : a ∈ X₁ := by simpa [a, X₁D, Subgroup.mem_subgroupOf] using haD
    have hzZ : z ∈ Z := by simpa [z, ZD, Subgroup.mem_subgroupOf] using hzD
    have hx_eq : x = a * z := by
      have hval := congrArg (fun t : D => (t : G)) hxaz
      simpa [a, z] using hval.symm
    have hzX : z ∈ X := by
      have haX : a ∈ X := hX₁leX haX₁
      have hz_eq : z = a⁻¹ * x := by
        calc
          z = a⁻¹ * (a * z) := by simp
          _ = a⁻¹ * x := by rw [hx_eq]
      rw [hz_eq]
      exact X.mul_mem (X.inv_mem haX) hxX
    have hzInf : z ∈ X ⊓ Z := ⟨hzX, hzZ⟩
    have hz_one : z = 1 := by
      have hzBot : z ∈ (⊥ : Subgroup G) := by simpa [hXinfZ_bot] using hzInf
      exact Subgroup.mem_bot.mp hzBot
    rw [hx_eq, hz_one, mul_one]
    exact haX₁
  have hXeq : X = X₁ := le_antisymm hXleX₁ hX₁leX
  refine ⟨hXeq, Z, hZcyc, hdisjX₁Z, ?_⟩
  simpa [P, B, Z₀] using hCPeq

private theorem CFSG.section15_theorem15_7_X_eq_primeOrder_of_nonabelian_MF
    {M MF X E E₁₂ E₁ E₂ E₃ X₁ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hX₁ : X₁ ∈ section10PrimeOrderSubgroupsIn p X) :
    X = X₁ :=
  (section15_theorem15_7_X_eq_primeOrder_and_centralizer_split_of_nonabelian_MF
    (G := G) (M := M) (MF := MF) (X := X) (E := E)
    (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
    (X₁ := X₁) (g := g) (p := p)
    hM hMF hnotTI hg hX hXne hE hMFnoncomm hX₁).1

/-- The common nonabelian setup in Theorem 15.7(e): for the source prime
`p=|X|`, the `p`-core of `M_F` is nonabelian and the `p'`-core is cyclic. -/
private theorem CFSG.section15_theorem15_7_X_card_prime_of_nonabelian_MF
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF) :
    Nat.Prime (Nat.card X) := by
  classical
  have hcard_ne_one : Nat.card X ≠ 1 := by
    intro hcard
    exact hXne ((Subgroup.card_eq_one (H := X)).1 hcard)
  obtain ⟨q0, hq0prime, hq0dvd⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  obtain ⟨z, _hzX, _hzne, hZprime⟩ :=
    section15_exists_primeOrder_zpowers_of_prime_dvd_card
      (G := G) (B := X) (q := q) hq0dvd
  let X₁ : Subgroup G := Subgroup.zpowers z
  have hXeq : X = X₁ :=
    section15_theorem15_7_X_eq_primeOrder_of_nonabelian_MF
      (G := G) (M := M) (MF := MF) (X := X) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (X₁ := X₁) (g := g) (p := q)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm
      (by simpa [X₁] using hZprime)
  have hXcard : Nat.card X = q.val := by
    simpa [X₁, hXeq] using hZprime.2
  simpa [hXcard] using q.property

private theorem CFSG.section15_theorem15_7_pCore_MF_noncomm_of_source_prime
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hpX : p.val = Nat.card X) :
    ¬ IsMulCommutative (section15PCoreIn p MF) := by
  have hXprime : X ∈ section10PrimeOrderSubgroupsIn p X := ⟨le_rfl, hpX.symm⟩
  exact
    section15_theorem15_7_pCore_noncomm_of_primeOrder_centralizer
      (G := G) (M := M) (MF := MF) (X := X) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (X₁ := X) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hXprime

private theorem CFSG.section15_theorem15_7_pPrimeCore_cyclic_of_primeOrder_centralizer
    {M MF X E E₁₂ E₁ E₂ E₃ X₁ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hX₁ : X₁ ∈ section10PrimeOrderSubgroupsIn p X) :
    IsCyclic (section10PPrimeCore p MF) := by
  classical
  have hfacts :=
    section15_theorem15_7_prime_order_centralizer_facts
      (G := G) hM hMF hnotTI hg hX hXne hE hX₁
  have hPnoncomm :
      ¬ IsMulCommutative (section15PCoreIn p MF) :=
    section15_theorem15_7_pCore_noncomm_of_primeOrder_centralizer
      (G := G) (M := M) (MF := MF) (X := X) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (X₁ := X₁) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hX₁
  by_contra hPPrimeNoncyc
  rcases hMF.1 with ⟨hMFleM, _hMFnormM, hMFnil, _hMFHall⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX₁) with
    ⟨hX₁leX, hX₁card⟩
  let P : Subgroup G := section15PCoreIn p MF
  let L : Subgroup G := section10PPrimeCore p MF
  let C : Subgroup G := subgroupCentralizerIn MF X₁
  have hPp : IsPGroup p.val P := by
    simpa [P] using section15_pCoreIn_isPGroup p MF
  have hPunique : P ∈ section9UniqueSubgroups G :=
    theorem_12_13 (G := G) (P := P) (p := p) hPp (by simpa [P] using hPnoncomm)
  have hLleMF : L ≤ MF := by
    simpa [L] using section15_pPrimeCore_le (G := G) (p := p) MF
  have hLnil : Group.IsNilpotent L := by
    haveI : Group.IsNilpotent MF := hMFnil
    let LMF : Subgroup MF := L.subgroupOf MF
    have hLMFnil : Group.IsNilpotent LMF := inferInstance
    exact
      (Group.isNilpotent_congr
        (Subgroup.subgroupOfEquivOfLe (H := L) (K := MF) hLleMF)).1 hLMFnil
  have hLrank : 2 ≤ groupRank L := by
    haveI : Group.IsNilpotent L := hLnil
    exact
      section15_groupRank_at_least_two_of_not_isCyclic L
        (by simpa [L] using hPPrimeNoncyc)
  have hL_cent_P : L ≤ Subgroup.centralizer (P : Set G) := by
    simpa [L, P] using
      section15_pPrimeCore_le_centralizer_pCoreIn (G := G) (p := p) MF
  have hLunique : L ∈ section9UniqueSubgroups G :=
    corollary_9_2 (G := G) (L := P) (K := L) hPunique hL_cent_P hLrank
  have hX₁p : IsPGroup p.val X₁ :=
    section15_isPGroup_of_prime_card (G := G) (A := X₁) (q := p) hX₁card.symm
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  have hX₁leMF : X₁ ≤ MF := hX₁leX.trans hred.2.2.1
  have hX₁leP : X₁ ≤ P := by
    simpa [P] using
      section15_pSubgroup_le_pCoreIn_of_nilpotent
        (G := G) (H := MF) (X := X₁) (p := p) hMFnil hX₁leMF hX₁p
  have hLleC : L ≤ C := by
    intro x hxL
    refine ⟨hLleMF hxL, ?_⟩
    change x ∈ Subgroup.centralizer (X₁ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hyX₁
    exact Subgroup.mem_centralizer_iff.mp (hL_cent_P hxL) y (hX₁leP hyX₁)
  have hCproper : C ≠ ⊤ := by
    have hC_le_M : C ≤ M := by
      intro x hxC
      exact hMFleM hxC.1
    intro hCtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hCtop] using hC_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  exact hfacts.1 (by
    simpa [C] using section9_unique_of_le hLleC hCproper hLunique)

private theorem CFSG.section15_theorem15_7_pPrimeCore_MF_cyclic_of_source_prime
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hpX : p.val = Nat.card X) :
    IsCyclic (section10PPrimeCore p MF) := by
  have hXprime : X ∈ section10PrimeOrderSubgroupsIn p X := ⟨le_rfl, hpX.symm⟩
  exact
    section15_theorem15_7_pPrimeCore_cyclic_of_primeOrder_centralizer
      (G := G) (M := M) (MF := MF) (X := X) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (X₁ := X) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hXprime

private theorem CFSG.section15_theorem15_7_nonabelian_setup
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF) :
    ∃ p : Nat.Primes,
      p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
        ¬ IsMulCommutative (section15PCoreIn p MF) ∧
          IsCyclic (section10PPrimeCore p MF) := by
  classical
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  let p : Nat.Primes :=
    ⟨Nat.card X, section15_theorem15_7_X_card_prime_of_nonabelian_MF
      hM hMF hnotTI hg hX hXne hE hMFnoncomm⟩
  have hpX : p.val = Nat.card X := rfl
  have hpXmem : p ∈ subgroupPrimeSet X := by
    have hp_dvd : p.val ∣ Nat.card X := by rw [hpX]
    simpa [subgroupPrimeSet] using hp_dvd
  have hpσ : p ∈ section10SigmaPrimes M :=
    section15_initial_prime_mem_sigma_of_fitting_intersection
      hM hMF hnotTI hg hX hXne hpXmem
  have hXleMsigma : X ≤ section10Msigma M := by
    simpa [← hred.2.1] using hred.2.2.1
  rcases section15_initial_X_msigma_cyclic_beta_compl
      hM hg hX hE hXleMsigma with ⟨_hXle, _hXcyc, hXβc⟩
  have hpβ : p ∉ section10BetaPrimes M := hXβc p hpXmem
  exact ⟨p, hpX, ⟨hpσ, hpβ⟩,
    section15_theorem15_7_pCore_MF_noncomm_of_source_prime
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hpX,
    section15_theorem15_7_pPrimeCore_MF_cyclic_of_source_prime
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hpX⟩

omit [Finite G] [IsMinCE G] in
/-- If `U` is a normal-complement quotient representative for `M/H`, then an
exponent bound on `U` is exactly the needed quotient exponent bound. -/
private theorem CFSG.section15QuotientExponentDvd_of_complement_exponent_dvd
    {H M U : Subgroup G} {n : ℕ}
    (hcomp : section12ComplementIn M H U)
    (hHnorm : section10NormalIn H M)
    (hdvd : Monoid.exponent U ∣ n) :
    section15QuotientExponentDvd H M n := by
  classical
  rcases hcomp with ⟨hHM, hUM, hMprod, hdisj⟩
  rcases hHnorm with ⟨hHMnorm, hHnormal⟩
  have hcomp_symm : section12ComplementIn M U H :=
    ⟨hUM, hHM, by simpa [sup_comm] using hMprod, hdisj.symm⟩
  have hHnorm' : section10NormalIn H M := ⟨hHMnorm, hHnormal⟩
  have hcomp' : (U.subgroupOf M).IsComplement' (H.subgroupOf M) :=
    section15_normal_complementIn_isComplement' hcomp_symm hHnorm'
  haveI : (H.subgroupOf M).Normal := hHnormal
  let eQ : M ⧸ H.subgroupOf M ≃* U.subgroupOf M := hcomp'.QuotientMulEquiv
  have hUsub_exp : Monoid.exponent (U.subgroupOf M) = Monoid.exponent U := by
    simpa using Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUM)
  have hquot_exp : Monoid.exponent (M ⧸ H.subgroupOf M) = Monoid.exponent U := by
    calc
      Monoid.exponent (M ⧸ H.subgroupOf M) =
          Monoid.exponent (U.subgroupOf M) := by
        simpa using Monoid.exponent_eq_of_mulEquiv eQ
      _ = Monoid.exponent U := hUsub_exp
  exact ⟨hHMnorm, hHnormal, by simpa [hquot_exp] using hdvd⟩

omit [Finite G] [IsMinCE G] in
/-- If `U` is a normal-complement quotient representative for `M/H`, then a
cardinality bound on `U` is exactly the needed quotient cardinality bound. -/
private theorem CFSG.section15QuotientCardDvd_of_complement_card_dvd
    {H M U : Subgroup G} {n : ℕ}
    (hcomp : section12ComplementIn M H U)
    (hHnorm : section10NormalIn H M)
    (hdvd : Nat.card U ∣ n) :
    section15QuotientCardDvd H M n := by
  classical
  rcases hcomp with ⟨hHM, hUM, hMprod, hdisj⟩
  rcases hHnorm with ⟨hHMnorm, hHnormal⟩
  have hcomp_symm : section12ComplementIn M U H :=
    ⟨hUM, hHM, by simpa [sup_comm] using hMprod, hdisj.symm⟩
  have hHnorm' : section10NormalIn H M := ⟨hHMnorm, hHnormal⟩
  have hcomp' : (U.subgroupOf M).IsComplement' (H.subgroupOf M) :=
    section15_normal_complementIn_isComplement' hcomp_symm hHnorm'
  haveI : (H.subgroupOf M).Normal := hHnormal
  let eQ : M ⧸ H.subgroupOf M ≃* U.subgroupOf M := hcomp'.QuotientMulEquiv
  have hUsub_card : Nat.card (U.subgroupOf M) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
  have hquot_card : Nat.card (M ⧸ H.subgroupOf M) = Nat.card U := by
    calc
      Nat.card (M ⧸ H.subgroupOf M) = Nat.card (U.subgroupOf M) :=
        Nat.card_congr eQ.toEquiv
      _ = Nat.card U := hUsub_card
  exact ⟨hHMnorm, hHnormal, by simpa [hquot_card] using hdvd⟩

omit [IsMinCE G] in
/-- A faithful regular conjugation action on a cyclic subgroup of order `q`
has exponent dividing `q - 1`, matching the source's `regular_norm_dvd_pred`
use. -/
private theorem CFSG.section15_exponent_dvd_prime_sub_one_of_regular_conj_action
    {A Z : Subgroup G} {q : Nat.Primes}
    (hAnormZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hZcyc : IsCyclic Z)
    (hZcard : Nat.card Z = q.val)
    (hregular :
      ∀ a : G, a ∈ A → a ≠ 1 → elementCentralizerIn Z a = ⊥) :
    Monoid.exponent A ∣ q.val - 1 := by
  classical
  letI : MulDistribMulAction A Z :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) A Z hAnormZ
  let φ : A →* MulAut Z := MulDistribMulAction.toMulAut A Z
  have hZne : Z ≠ ⊥ := by
    intro hZbot
    have hcard_one : Nat.card Z = 1 := (Subgroup.card_eq_one (H := Z)).2 hZbot
    exact q.property.ne_one (hZcard.symm.trans hcard_one)
  have hφker_bot : φ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a haKer
    have hφa : φ a = 1 := by simpa [φ, MonoidHom.mem_ker] using haKer
    by_cases ha_one : (a : G) = 1
    · exact Subtype.ext ha_one
    · exfalso
      have hcent_bot : elementCentralizerIn Z (a : G) = ⊥ :=
        hregular (a : G) a.property ha_one
      have hZleCent : Z ≤ elementCentralizerIn Z (a : G) := by
        intro z hzZ
        refine ⟨hzZ, ?_⟩
        have hfix : a • (⟨z, hzZ⟩ : Z) = ⟨z, hzZ⟩ := by
          simpa [φ, MulDistribMulAction.toMulAut_apply] using
            congrArg (fun f : MulAut Z => f ⟨z, hzZ⟩) hφa
        have hconj : (a : G) * z * (a : G)⁻¹ = z := by
          calc
            (a : G) * z * (a : G)⁻¹ =
                (((Subgroup.conjMulDistribMulActionOfLeNormalizer
                    (G := G) A Z hAnormZ).smul a ⟨z, hzZ⟩ : Z) : G) :=
              (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
                (G := G) A Z hAnormZ a ⟨z, hzZ⟩).symm
            _ = z := congrArg Subtype.val hfix
        have hcomm : z * (a : G) = (a : G) * z := by
          have h := congrArg (fun t : G => t * (a : G)) hconj
          simpa [mul_assoc] using h.symm
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      have hZbot' : Z = ⊥ := le_bot_iff.mp (by simpa [hcent_bot] using hZleCent)
      exact hZne hZbot'
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hφker_bot
  have hA_exp_dvd_Aut : Monoid.exponent A ∣ Monoid.exponent (MulAut Z) :=
    Monoid.exponent_dvd_of_monoidHom φ hφinj
  have hAut_exp_dvd_card : Monoid.exponent (MulAut Z) ∣ Nat.card (MulAut Z) :=
    Group.exponent_dvd_nat_card
  have hAut_card : Nat.card (MulAut Z) = q.val - 1 := by
    letI : IsCyclic Z := hZcyc
    rw [IsCyclic.card_mulAut, hZcard, Nat.totient_prime q.property]
  exact hA_exp_dvd_Aut.trans (by simpa [hAut_card] using hAut_exp_dvd_card)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_pCore_characteristic
    {R : Type*} [Group R] {p : ℕ} [Fact p.Prime] :
    (pCore p R).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have hmap_le : (pCore p R).map φ.toMonoidHom ≤ pCore p R := by
    exact le_sSup ⟨Subgroup.Normal.map (H := pCore p R) inferInstance
      φ.toMonoidHom φ.surjective,
      IsPGroup.map (p := p) (H := pCore p R)
        (pCore_isPGroup (G := R) (p := p)) φ.toMonoidHom⟩
  have hsymm_le : (pCore p R).map φ.symm.toMonoidHom ≤ pCore p R := by
    exact le_sSup ⟨Subgroup.Normal.map (H := pCore p R) inferInstance
      φ.symm.toMonoidHom φ.symm.surjective,
      IsPGroup.map (p := p) (H := pCore p R)
        (pCore_isPGroup (G := R) (p := p)) φ.symm.toMonoidHom⟩
  have hmap_symm :
      ((pCore p R).map φ.symm.toMonoidHom).map φ.toMonoidHom = pCore p R := by
    rw [Subgroup.map_map]
    have hcomp : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id R := by
      ext x
      simp
    rw [hcomp]
    simp
  exact le_antisymm hmap_le <| by
    calc
      pCore p R = ((pCore p R).map φ.symm.toMonoidHom).map φ.toMonoidHom :=
        hmap_symm.symm
      _ ≤ (pCore p R).map φ.toMonoidHom := Subgroup.map_mono hsymm_le

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omega1Z_characteristic
    (p : ℕ) (R : Type*) [Group R] :
    (Ω₁Z p R).Characteristic := by
  let ZR : Subgroup R := Subgroup.center R
  let Ωc : Subgroup ZR := omega₁ (G := ZR) (p := p)
  have hZchar : ZR.Characteristic := Subgroup.centerCharacteristic
  letI : ZR.Characteristic := hZchar
  have hΩchar : Ωc.Characteristic := by
    simpa [Ωc] using omega₁_characteristic (G := ZR) (p := p)
  letI : Ωc.Characteristic := hΩchar
  simpa [Ω₁Z, ZR, Ωc] using
    characteristic_map_subtype_of_characteristic (G := R) ZR Ωc

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_normalizer_le_normalizer_map_subtype_of_characteristic
    (H : Subgroup G) (K : Subgroup H) [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (((K : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem ((K : Subgroup H).map H.subtype)
    (Subgroup.normalizer (H : Set G)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, by simp⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

omit [IsMinCE G] in
private theorem CFSG.section15_pSubgroup_le_pCore_of_nilpotent
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    [Group.IsNilpotent R] {B : Subgroup R} (hBp : IsPGroup p B) :
    B ≤ pCore p R := by
  obtain ⟨S, hB_le_S⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hBp
  have hS_normal : (S : Subgroup R).Normal :=
    Group.IsNilpotent.sylow_normal (p := p) inferInstance S
  exact hB_le_S.trans (le_sSup ⟨hS_normal, S.isPGroup'⟩)

omit [IsMinCE G] in
private theorem CFSG.section15_pCore_ne_bot_of_dvd_card_nilpotent
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {q : ℕ} [Fact q.Prime] (hq : q ∣ Nat.card H) :
    pCore q H ≠ ⊥ := by
  classical
  let S : Sylow q H := Classical.choice inferInstance
  have hS_le : (S : Subgroup H) ≤ pCore q H :=
    section15_pSubgroup_le_pCore_of_nilpotent (p := q) (R := H) S.isPGroup'
  have hqS : q ∣ Nat.card (S : Subgroup H) :=
    Sylow.dvd_card_of_dvd_card S hq
  intro hbot
  have hSbot : (S : Subgroup H) = ⊥ :=
    le_bot_iff.mp (hS_le.trans (le_of_eq hbot))
  have hcardS : Nat.card (S : Subgroup H) = 1 := by
    simp [hSbot]
  rw [hcardS] at hqS
  exact (Fact.out : Nat.Prime q).not_dvd_one hqS

omit [IsMinCE G] in
private theorem CFSG.section15_pCoreIn_ne_bot_of_mem_primeSet_nilpotent
    {H : Subgroup G} {q : Nat.Primes}
    (hHnil : Group.IsNilpotent H) (hqH : q ∈ subgroupPrimeSet H) :
    section15PCoreIn q H ≠ ⊥ := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  letI : Group.IsNilpotent H := hHnil
  have hcore_ne : pCore q.val H ≠ ⊥ :=
    section15_pCore_ne_bot_of_dvd_card_nilpotent
      (H := H) (q := q.val) (by simpa [subgroupPrimeSet] using hqH)
  simpa [section15PCoreIn] using
    section15_map_subtype_ne_bot_of_ne_bot (G := G) (M := H) hcore_ne

omit [IsMinCE G] in
private theorem CFSG.section15_pCoreIn_le_pPrimeCore_of_ne
    {H : Subgroup G} {p q : Nat.Primes} (hqp : q ≠ p) :
    section15PCoreIn q H ≤ section10PPrimeCore p H := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hqval_ne_pval : q.val ≠ p.val := by
    intro hval
    exact hqp (Subtype.ext hval)
  have hcore_le : pCore q.val H ≤ pPrimeCore p.val H := by
    have hqcore_coprime : Nat.Coprime p.val (Nat.card (pCore q.val H)) := by
      obtain ⟨n, hcard⟩ :=
        (pCore_isPGroup (G := H) (p := q.val)).exists_card_eq
      rw [hcard]
      exact ((Nat.coprime_primes p.property q.property).2 hqval_ne_pval.symm).pow_right n
    exact le_sSup
      (show pCore q.val H ∈
          {K : Subgroup H | K.Normal ∧ Nat.Coprime p.val (Nat.card K)} from
        ⟨inferInstance, hqcore_coprime⟩)
  have hcore_eq :
      section10PPrimeCore p H = (pPrimeCore p.val H).map H.subtype := by
    have hp_eq : (⟨p.val, Fact.out⟩ : Nat.Primes) = p := Subtype.ext rfl
    simpa [section10PPrimeCore, section10PPrimeSet, hp_eq] using
      section8_piCoreIn_singleton_compl_eq_pPrimeCore_map
        (G := G) (p := p.val) H
  have hmap_le :
      (pCore q.val H).map H.subtype ≤ (pPrimeCore p.val H).map H.subtype :=
    Subgroup.map_mono hcore_le
  simpa [section15PCoreIn, hcore_eq] using hmap_le

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omega1_map_subtype_le
    {R : Type*} [Group R] {p : ℕ} (H : Subgroup R) :
    (omega₁ (G := H) (p := p)).map H.subtype ≤ omega₁ (G := R) (p := p) := by
  rw [omega₁, omega, MonoidHom.map_closure]
  refine (Subgroup.closure_le (K := omega₁ (G := R) (p := p))).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.subset_closure ?_
  simpa [pow_one] using congrArg H.subtype hx

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omega1_le_map_subtype_of_forall_pow_eq_one_mem
    {R : Type*} [Group R] {p : ℕ} (H : Subgroup R)
    (hmem : ∀ x : R, x ^ p = 1 → x ∈ H) :
    omega₁ (G := R) (p := p) ≤ (omega₁ (G := H) (p := p)).map H.subtype := by
  rw [omega₁, omega]
  refine (Subgroup.closure_le (K := (omega₁ (G := H) (p := p)).map H.subtype)).2 ?_
  intro x hx
  have hxH : x ∈ H := hmem x (by simpa [pow_one] using hx)
  have hxOmegaH : ⟨x, hxH⟩ ∈ omega₁ (G := H) (p := p) := by
    change ⟨x, hxH⟩ ∈ Subgroup.closure {y : H | y ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    simpa [pow_one] using hx
  exact Subgroup.mem_map_of_mem H.subtype hxOmegaH

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omega1Z_eq_omega1_of_isCyclic
    {R : Type*} [Group R] [IsCyclic R] {p : ℕ} :
    Ω₁Z p R = omega₁ (G := R) (p := p) := by
  classical
  letI : CommGroup R := IsCyclic.commGroup
  have hcenter : Subgroup.center R = ⊤ := CommGroup.center_eq_top
  apply le_antisymm
  · simpa [Ω₁Z] using
      section15_omega1_map_subtype_le (R := R) (p := p) (Subgroup.center R)
  · have hle :=
      section15_omega1_le_map_subtype_of_forall_pow_eq_one_mem
        (R := R) (p := p) (Subgroup.center R) (fun x _hx => by simp [hcenter])
    simpa [Ω₁Z] using hle

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omega1_eq_centralProduct_left_of_exponent
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R]
    {R₁ R₂ : Subgroup R}
    (hprod : IsCentralProduct R₁ R₂)
    (hR₁exp : Monoid.exponent R₁ = p)
    (hΩeq :
      (omega₁ (G := R₂) (p := p)).map R₂.subtype =
        (derivedSubgroup R₁).map R₁.subtype) :
    omega₁ (G := R) (p := p) = R₁ := by
  rcases hprod with ⟨_hR₁norm, _hR₂norm, hcomm12, hsup12⟩
  have hR₁_le_omega : R₁ ≤ omega₁ (G := R) (p := p) := by
    intro y hy
    change y ∈ Subgroup.closure {u : R | u ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    have hy_pow_sub : (⟨y, hy⟩ : R₁) ^ p = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent (↥R₁) ∣ p by simp [hR₁exp]) ⟨y, hy⟩
    have hy_pow : y ^ p = 1 := by
      simpa using congrArg R₁.subtype hy_pow_sub
    simpa [pow_one] using hy_pow
  have homega_le_R₁ : omega₁ (G := R) (p := p) ≤ R₁ := by
    rw [omega₁, omega]
    refine (Subgroup.closure_le (K := R₁)).2 ?_
    intro x hx
    have hx_pow : x ^ p = 1 := by simpa [pow_one] using hx
    have hx_sup : x ∈ R₁ ⊔ R₂ := by
      rw [hsup12]
      exact Subgroup.mem_top x
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := R₁) (t := R₂)).1 hx_sup with
      ⟨y, hy, z, hz, hyz⟩
    let yR₁ : R₁ := ⟨y, hy⟩
    let zR₂ : R₂ := ⟨z, hz⟩
    have hy_cent : (z : R) * (y : R) = (y : R) * (z : R) := by
      exact
        Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := R₁) (H₂ := R₂)).1
            hcomm12 hy)
          z hz
    have hy_commute : Commute (y : R) (z : R) := hy_cent.symm
    have hy_pow_sub : yR₁ ^ p = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent (↥R₁) ∣ p by simp [hR₁exp]) yR₁
    have hy_pow : (y : R) ^ p = 1 := by
      simpa [yR₁] using congrArg R₁.subtype hy_pow_sub
    have hz_pow : (z : R) ^ p = 1 := by
      have hsplit : ((y : R) * (z : R)) ^ p = (y : R) ^ p * (z : R) ^ p := by
        simpa using hy_commute.mul_pow p
      calc
        (z : R) ^ p = (y : R) ^ p * (z : R) ^ p := by simp [hy_pow]
        _ = ((y : R) * (z : R)) ^ p := by simpa using hsplit.symm
        _ = x ^ p := by simp [hyz]
        _ = 1 := hx_pow
    have hz_pow_sub : zR₂ ^ p = 1 := by
      apply Subtype.ext
      simpa [zR₂] using hz_pow
    have hz_omega : zR₂ ∈ omega₁ (G := R₂) (p := p) := by
      change zR₂ ∈ Subgroup.closure {u : R₂ | u ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [pow_one] using hz_pow_sub
    have hz_map : (z : R) ∈ (omega₁ (G := R₂) (p := p)).map R₂.subtype :=
      Subgroup.mem_map_of_mem R₂.subtype hz_omega
    rw [hΩeq] at hz_map
    rcases Subgroup.mem_map.mp hz_map with ⟨d, hd, hd_eq⟩
    have hz_R₁ : (z : R) ∈ R₁ := by
      rw [← hd_eq]
      exact d.2
    rw [← hyz]
    exact R₁.mul_mem hy hz_R₁
  exact le_antisymm homega_le_R₁ hR₁_le_omega

omit [IsMinCE G] in
private theorem CFSG.section15_omegaOneCenter_card_eq_prime_of_cyclic_pSubgroup
    {H : Subgroup G} {q : Nat.Primes}
    (hHp : IsPGroup q.val H) (hHcyc : IsCyclic H) (hHne : H ≠ ⊥) :
    Nat.card (section10OmegaOneCenter q H) = q.val := by
  classical
  haveI : Fact (IsPGroup q.val H) := ⟨hHp⟩
  haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hHne
  letI : IsCyclic H := hHcyc
  have hcard :
      Nat.card (section10OmegaOneCenter q H) =
        Nat.card (omega₁ (G := H) (p := q.val)) := by
    calc
      Nat.card (section10OmegaOneCenter q H) = Nat.card (Ω₁Z q.val H) := by
        simpa [section10OmegaOneCenter] using
          (Subgroup.card_map_of_injective
            (K := Ω₁Z q.val H) (f := H.subtype) H.subtype_injective)
      _ = Nat.card (omega₁ (G := H) (p := q.val)) := by
        rw [section15_omega1Z_eq_omega1_of_isCyclic (R := H) (p := q.val)]
  exact hcard.trans
    (section15_natCard_omegaOne_cyclic_pGroup_eq_prime (H := H) (p := q) hHcyc)

omit [IsMinCE G] in
private theorem CFSG.section15_frobeniusJoin_regular_on_subgroup
    {K R Z : Subgroup G}
    (hfrob : section12FrobeniusJoinWithKernel K R)
    (hZK : Z ≤ K) :
    ∀ r : G, r ∈ R → r ≠ 1 → elementCentralizerIn Z r = ⊥ := by
  classical
  let S : Subgroup G := K ⊔ R
  let Ksub : Subgroup S := K.subgroupOf S
  let Rsub : Subgroup S := R.subgroupOf S
  have hcentK :
      ∀ x : Rsub, x ≠ 1 → elementCentralizerIn Ksub (x : S) = ⊥ :=
    (lemma_3_1 (G := S) (K := Ksub) (R := Rsub)
      hfrob.kernel_ne_bot hfrob.complement_ne_bot hfrob.normal hfrob.isComplement').1 hfrob
  intro r hrR hrne
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hy with ⟨hyZ, hycent⟩
  let rS : S := ⟨r, Subgroup.mem_sup_right hrR⟩
  let rR : Rsub := ⟨rS, by simpa [Rsub, rS, Subgroup.mem_subgroupOf] using hrR⟩
  let yS : S := ⟨y, Subgroup.mem_sup_left (hZK hyZ)⟩
  have hrR_ne : rR ≠ 1 := by
    intro h
    apply hrne
    simpa [rR, rS] using congrArg (fun t : Rsub => ((t : S) : G)) h
  have hyKsub : yS ∈ Ksub := by
    simpa [Ksub, yS, Subgroup.mem_subgroupOf] using hZK hyZ
  have hycentS : yS ∈ Subgroup.centralizer ({(rR : S)} : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz_eq : z = (rR : S) := by simpa using hz
    subst z
    apply Subtype.ext
    have hcommG : y * r = r * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hycent
    simpa [yS, rR, rS] using hcommG.symm
  have hyCentK : yS ∈ elementCentralizerIn Ksub (rR : S) := ⟨hyKsub, hycentS⟩
  have hybot : yS ∈ (⊥ : Subgroup S) := by
    simpa [hcentK rR hrR_ne] using hyCentK
  have hyone : y = 1 := by
    have hySone : yS = 1 := by simpa using hybot
    simpa [yS] using congrArg (fun t : S => (t : G)) hySone
  simp [hyone]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omegaOneCenter_normalized_by_complement_of_frobeniusJoin
    {K R : Subgroup G} {q : Nat.Primes}
    (hfrob : section12FrobeniusJoinWithKernel K R) :
    R ≤ Subgroup.normalizer
      (section10OmegaOneCenter q (section15PCoreIn q K) : Set G) := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let S : Subgroup G := K ⊔ R
  have hR_norm_K : R ≤ Subgroup.normalizer (K : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem K R ?_
    intro r x hxK
    let rS : S := ⟨r, Subgroup.mem_sup_right r.property⟩
    let xS : S := ⟨x, Subgroup.mem_sup_left hxK⟩
    have hxKsub : xS ∈ K.subgroupOf S := by
      simpa [xS, Subgroup.mem_subgroupOf] using hxK
    have hconj : rS * xS * rS⁻¹ ∈ K.subgroupOf S :=
      hfrob.normal.conj_mem xS hxKsub rS
    simpa [rS, xS, S, mul_assoc, Subgroup.mem_subgroupOf] using hconj
  have hPchar : (pCore q.val K).Characteristic :=
    section15_pCore_characteristic (R := K) (p := q.val)
  letI : (pCore q.val K).Characteristic := hPchar
  have hnorm_pcore :
      Subgroup.normalizer (K : Set G) ≤
        Subgroup.normalizer (section15PCoreIn q K : Set G) := by
    have hnorm :=
      section15_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) K (pCore q.val K)
    simpa [section15PCoreIn] using hnorm
  have hΩchar : (Ω₁Z q.val (section15PCoreIn q K)).Characteristic :=
    section15_omega1Z_characteristic q.val (section15PCoreIn q K)
  letI : (Ω₁Z q.val (section15PCoreIn q K)).Characteristic := hΩchar
  have hnorm_Ω :
      Subgroup.normalizer (section15PCoreIn q K : Set G) ≤
        Subgroup.normalizer
          (section10OmegaOneCenter q (section15PCoreIn q K) : Set G) := by
    have hnorm :=
      section15_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) (section15PCoreIn q K)
        (Ω₁Z q.val (section15PCoreIn q K))
    simpa [section10OmegaOneCenter] using hnorm
  exact hR_norm_K.trans (hnorm_pcore.trans hnorm_Ω)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omegaOneCenter_normalized_by_normalizer
    {H A : Subgroup G} {q : Nat.Primes}
    (hAnormH : A ≤ Subgroup.normalizer (H : Set G)) :
    A ≤ Subgroup.normalizer
      (section10OmegaOneCenter q (section15PCoreIn q H) : Set G) := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hPchar : (pCore q.val H).Characteristic :=
    section15_pCore_characteristic (R := H) (p := q.val)
  letI : (pCore q.val H).Characteristic := hPchar
  have hnorm_pcore :
      Subgroup.normalizer (H : Set G) ≤
        Subgroup.normalizer (section15PCoreIn q H : Set G) := by
    have hnorm :=
      section15_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) H (pCore q.val H)
    simpa [section15PCoreIn] using hnorm
  have hΩchar : (Ω₁Z q.val (section15PCoreIn q H)).Characteristic :=
    section15_omega1Z_characteristic q.val (section15PCoreIn q H)
  letI : (Ω₁Z q.val (section15PCoreIn q H)).Characteristic := hΩchar
  have hnorm_Ω :
      Subgroup.normalizer (section15PCoreIn q H : Set G) ≤
        Subgroup.normalizer
          (section10OmegaOneCenter q (section15PCoreIn q H) : Set G) := by
    have hnorm :=
      section15_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) (section15PCoreIn q H)
        (Ω₁Z q.val (section15PCoreIn q H))
    simpa [section10OmegaOneCenter] using hnorm
  exact hAnormH.trans (hnorm_pcore.trans hnorm_Ω)

omit [IsMinCE G] in
private theorem CFSG.section15_ambientDerived_le_pCoreIn_of_nilpotent_pPrimeCore_cyclic
    {H : Subgroup G} {p : Nat.Primes}
    (hHnil : Group.IsNilpotent H)
    (hPPrimeCyclic : IsCyclic (section10PPrimeCore p H)) :
    ambientDerivedSubgroup H ≤ section15PCoreIn p H := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let P : Subgroup H := pCore p.val H
  let L : Subgroup H := pPrimeCore p.val H
  let qH : H →* H ⧸ P := QuotientGroup.mk' P
  have hL_map_eq :
      L.map H.subtype = section10PPrimeCore p H := by
    have hp_eq : (⟨p.val, Fact.out⟩ : Nat.Primes) = p := Subtype.ext rfl
    simpa [L, section10PPrimeCore, section10PPrimeSet, hp_eq] using
      (section8_piCoreIn_singleton_compl_eq_pPrimeCore_map
        (G := G) (p := p.val) H).symm
  have hLcyc : IsCyclic L := by
    let e : L ≃* L.map H.subtype :=
      Subgroup.equivMapOfInjective (f := H.subtype) L H.subtype_injective
    have hmap_cyc : IsCyclic (L.map H.subtype) := by
      rw [hL_map_eq]
      exact hPPrimeCyclic
    exact e.isCyclic.2 hmap_cyc
  letI : Group.IsNilpotent H := hHnil
  have hfit_top : fittingSubgroup H = ⊤ :=
    fitting_eq_top_of_nilpotent (G := H)
  have htop_le_PL : (⊤ : Subgroup H) ≤ P ⊔ L := by
    rw [← hfit_top]
    simpa [P, L] using
      section15_local_fitting_le_pCore_sup_pPrimeCore (H := H) (p := p.val)
  let φ : L →* H ⧸ P := qH.comp L.subtype
  have hφ_surj : Function.Surjective φ := by
    intro z
    rcases QuotientGroup.mk'_surjective (N := P) z with ⟨x, rfl⟩
    have hxPL : x ∈ P ⊔ L := htop_le_PL (Subgroup.mem_top x)
    rcases (Subgroup.mem_sup_of_normal_left (s := P) (t := L) (x := x)).1 hxPL with
      ⟨a, haP, b, hbL, habx⟩
    refine ⟨⟨b, hbL⟩, ?_⟩
    change qH b = qH x
    rw [← habx]
    simp [qH, P, haP]
  have hquot_cyc : IsCyclic (H ⧸ P) := by
    letI : IsCyclic L := hLcyc
    exact isCyclic_of_surjective φ hφ_surj
  have hquot_comm : IsMulCommutative (H ⧸ P) := by
    letI : CommGroup (H ⧸ P) := hquot_cyc.commGroup
    exact ⟨inferInstance⟩
  have hder_le_P : derivedSubgroup H ≤ P := by
    have hcomm_le : _root_.commutator H ≤ P :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := P)).1 hquot_comm
    simpa [derivedSubgroup, derivedSeries_one, _root_.commutator_def, P] using hcomm_le
  have hmap_le :
      (derivedSubgroup H).map H.subtype ≤ (pCore p.val H).map H.subtype :=
    Subgroup.map_mono hder_le_P
  simpa [ambientDerivedSubgroup, section15PCoreIn, P] using hmap_le

public theorem CFSG.lemma_15_1_e_join
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hUne : U ≠ ⊥) :
    ∃ U₀ : Subgroup G,
      U₀ ≤ U ∧ Monoid.exponent U₀ = Monoid.exponent U ∧
        section12FrobeniusJoinWithKernel (section10Msigma M) U₀ := by
  classical
  by_cases hK : K = ⊥
  · have hUcomp : section12ComplementToMsigma M U :=
      section15_trivial_K_U_complementToMsigma hKU hK
    rcases section15_exists_EData_for_fixed_sigma_complement
        (G := G) (M := M) (E := U) hM hUcomp with
      ⟨E₁₂, E₁, E₂, E₃, hE⟩
    rcases theorem_12_12_b
        (G := G) (M := M) (E := U) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hE
        (section15_theorem12_12_hcent_of_U hM hKU) with
      ⟨U₀, hU₀U, hexp, hFrob⟩
    exact ⟨U₀, hU₀U, hexp, hFrob⟩
  · have hUcomm : IsMulCommutative U :=
      (lemma_15_1_b hM hKU hK).2
    let E : Subgroup G := K ⊔ U
    have hEcomp : section12ComplementToMsigma M E := by
      change section12ComplementIn M (section10Msigma M) (K ⊔ U)
      exact hKU.2.2.1
    rcases section15_exists_EData_for_fixed_sigma_complement
        (G := G) (M := M) (E := E) hM hEcomp with
      ⟨E₁₂, E₁, E₂, E₃, hE⟩
    have hUnormE : section10NormalIn U E := by
      simpa [E] using
        section15_kappa_compl_context_U_normal_in_KU
          (G := G) (M := M) (K := K) (U := U) hM hKU
    have hUHallE : ∃ π : Set Nat.Primes, section12HallSubgroupIn π U E := by
      let hHallU := section15_kappa_compl_context_U_hall hKU
      refine ⟨(section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ, ?_⟩
      simpa [E] using
        section15_hallSubgroupIn_of_le_overgroup
          (M := M) (E := K ⊔ U) (U := U)
          (π := (section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ)
          hHallU le_sup_right (sup_le hKU.1.1 hHallU.1)
    rcases section15_theorem_12_12_b_abelian_normal_subgroup
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (V := U) hM hE hUnormE hUHallE hUcomm hUne
        (section15_theorem12_12_hcent_of_U hM hKU) with
      ⟨U₀, hU₀U, hexp, hFrob⟩
    exact ⟨U₀, hU₀U, hexp, hFrob⟩

private theorem CFSG.section15_complementToMsigma_ne_bot
    {M E : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) :
    E ≠ ⊥ := by
  classical
  intro hEbot
  let N : Subgroup M := section10MsigmaSubgroup M
  let Ec : Subgroup M := E.subgroupOf M
  have hcomp' : Ec.IsComplement' N :=
    section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp
  have hEc_bot : Ec = ⊥ := by
    ext x
    constructor
    · intro hx
      change x = 1
      apply Subtype.ext
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [Ec, hEbot] using hx
      simpa using hxbot
    · intro hx
      change (x : G) ∈ E
      rw [hEbot]
      change (x : G) = 1
      exact congrArg Subtype.val (by simpa using hx)
  have hNtop : N = ⊤ := by
    have hcomp_bot : (⊥ : Subgroup M).IsComplement' N := by
      simpa [hEc_bot] using hcomp'
    exact Subgroup.isComplement'_bot_left.mp hcomp_bot
  have hder_top : derivedSubgroup M = ⊤ := by
    apply top_le_iff.mp
    rw [← hNtop]
    exact (theorem_10_2_c (M := M) hM).2
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    have hMsigma_le_M : section10Msigma M ≤ M := section15_msigma_le
    have hMsigma_bot : section10Msigma M = ⊥ :=
      le_bot_iff.mp (by simpa [hMbot] using hMsigma_le_M)
    exact (theorem_10_2_e (M := M) hM) hMsigma_bot
  haveI : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot (H := M)).2 hM_ne_bot
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hcomm_lt : commutator M < (⊤ : Subgroup M) :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := M)
  have hcomm_top : commutator M = (⊤ : Subgroup M) := by
    simpa [derivedSubgroup, derivedSeries_one, _root_.commutator_def] using hder_top
  exact hcomm_lt.ne hcomm_top

private theorem CFSG.section15_theorem15_7_source_p_omegaOneCenter_card
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (_hMFnoncomm : ¬ IsMulCommutative MF)
    (hpX : p.val = Nat.card X)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF)) :
    Nat.card (section10OmegaOneCenter p (section15PCoreIn p MF)) = p.val := by
  classical
  have hXprime : X ∈ section10PrimeOrderSubgroupsIn p X := ⟨le_rfl, hpX.symm⟩
  have hfacts :=
    section15_theorem15_7_prime_order_centralizer_facts
      (G := G) hM hMF hnotTI hg hX hXne hE hXprime
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  rcases hMF.1 with ⟨hMFleM, _hMFnormM, hMFnil, _hMFHall⟩
  have hXleMF : X ≤ MF := hred.2.2.1
  have hXp : IsPGroup p.val X :=
    section15_isPGroup_of_prime_card (G := G) (A := X) (q := p) hpX
  have hXleP : X ≤ section15PCoreIn p MF :=
    section15_pSubgroup_le_pCoreIn_of_nilpotent
      (G := G) (H := MF) (X := X) (p := p) hMFnil hXleMF hXp
  let P : Subgroup G := section15PCoreIn p MF
  let Z₀ : Subgroup G := section10OmegaOneCenter p P
  have hXnotleZ₀ : ¬ X ≤ Z₀ := by
    intro hXleZ₀
    have hP_le_C : P ≤ subgroupCentralizerIn MF X := by
      intro x hxP
      refine ⟨section15_pCoreIn_le p MF (by simpa [P] using hxP), ?_⟩
      change x ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyX
      have hyZ₀ : y ∈ Z₀ := hXleZ₀ hyX
      have hy_cent_P : y ∈ Subgroup.centralizer (P : Set G) := by
        simpa [Z₀] using section15_omegaOneCenter_le_centralizer (G := G) (p := p) P hyZ₀
      exact (Subgroup.mem_centralizer_iff.mp hy_cent_P x hxP).symm
    have hPcomm : IsMulCommutative P := by
      haveI : IsMulCommutative (subgroupCentralizerIn MF X) := by
        simpa using hfacts.2.2
      refine ⟨⟨fun a b => ?_⟩⟩
      have hcommG :
          (a : G) * (b : G) = (b : G) * (a : G) :=
        setLike_mul_comm
          (s := subgroupCentralizerIn MF X) (hP_le_C a.property) (hP_le_C b.property)
      exact Subtype.ext hcommG
    exact hpNoncomm (by simpa [P] using hPcomm)
  have hXneZ₀ : X ≠ Z₀ := by
    intro hXeqZ₀
    exact hXnotleZ₀ (by rw [hXeqZ₀])
  have hZ₀leP : Z₀ ≤ P := by
    simpa [Z₀] using section15_omegaOneCenter_le (G := G) (p := p) P
  have hXleP' : X ≤ P := by
    simpa [P] using hXleP
  let B : Subgroup G := X ⊔ Z₀
  have hPp : IsPGroup p.val P := by
    simpa [P] using section15_pCoreIn_isPGroup p MF
  have hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G) := by
    have hp_dvd_X : p.val ∣ Nat.card X := by rw [← hpX]
    have hp_dvd_G : p.val ∣ Nat.card G :=
      hp_dvd_X.trans (Subgroup.card_subgroup_dvd_card X)
    simpa [subgroupPrimeSet] using hp_dvd_G
  have hBleP : B ≤ P := by
    simpa [B] using sup_le hXleP' hZ₀leP
  have hXB : X ∈ section10PrimeOrderSubgroupsIn p B := by
    exact ⟨by simp [B], hpX.symm⟩
  have hBmax : B ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G := by
    haveI : Fact p.val.Prime := ⟨p.property⟩
    let C : Subgroup G := subgroupCentralizerIn MF X
    have hCnotUnique : C ∉ section9UniqueSubgroups G := by
      simpa [C] using hfacts.1
    have hCrank : groupRank C ≤ 2 := by
      simpa [C] using hfacts.2.1
    have hXelem : IsElementaryAbelian p.val X := by
      haveI : IsCyclic X := isCyclic_of_prime_card (p := p.val) hpX.symm
      exact section15_isElementaryAbelian_of_prime_card_isCyclic
        (p := p.val) (H := X) hpX.symm
    have hZ₀elem : IsElementaryAbelian p.val Z₀ := by
      simpa [Z₀] using
        section15_omegaOneCenter_isElementaryAbelian (G := G) (p := p) P
    have hZ₀leCentX : Z₀ ≤ Subgroup.centralizer (X : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro x hxX
      have hz_cent_P : z ∈ Subgroup.centralizer (P : Set G) := by
        simpa [Z₀] using
          section15_omegaOneCenter_le_centralizer (G := G) (p := p) P hz
      exact Subgroup.mem_centralizer_iff.mp hz_cent_P x (hXleP' hxX)
    have hBelem : IsElementaryAbelian p.val B := by
      letI : IsElementaryAbelian p.val X := hXelem
      letI : IsElementaryAbelian p.val Z₀ := hZ₀elem
      simpa [B] using
        section15_isElementaryAbelian_sup_of_le_centralizer
          (G := G) (p := p.val) (E := X) (D := Z₀) hZ₀leCentX
    have hB_le_C : B ≤ C := by
      have hB_le_cent_X : B ≤ Subgroup.centralizer (X : Set G) := by
        simpa [B] using
          (show X ⊔ Z₀ ≤ Subgroup.centralizer (X : Set G) from
            sup_le
              (by
                intro x hxX
                rw [Subgroup.mem_centralizer_iff]
                intro y hyX
                haveI : IsElementaryAbelian p.val X := hXelem
                exact
                  setLike_mul_comm
                    (s := X) hyX hxX)
              hZ₀leCentX)
      intro x hxB
      exact ⟨section15_pCoreIn_le p MF (by simpa [P] using hBleP hxB),
        hB_le_cent_X hxB⟩
    have hPnebot : P ≠ ⊥ := by
      intro hPbot
      exact hXne <| le_bot_iff.mp <| by
        intro x hx
        simpa [hPbot] using hXleP' hx
    haveI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPnebot
    have hZ₀nebot : Z₀ ≠ ⊥ := by
      simpa [Z₀] using
        section15_omegaOneCenter_ne_bot_of_nontrivial_pSubgroup
          (G := G) (p := p) (P := P) hPp
    have hXinfZ₀_bot : X ⊓ Z₀ = ⊥ := by
      by_contra hne
      have hXleZ₀' : X ≤ Z₀ :=
        section15_le_of_prime_card_inf_ne_bot
          (G := G) (A := X) (B := Z₀) (q := p) hpX hne
      exact hXnotleZ₀ hXleZ₀'
    have hZ₀notleX : ¬ Z₀ ≤ X := by
      intro hZ₀leX
      have hZ₀leInf : Z₀ ≤ X ⊓ Z₀ := by
        intro z hz
        exact ⟨hZ₀leX hz, hz⟩
      exact hZ₀nebot (le_bot_iff.mp (by simpa [hXinfZ₀_bot] using hZ₀leInf))
    have hXltB : X < B := by
      refine lt_of_le_of_ne (by simp [B] : X ≤ B) ?_
      intro hXeqB
      have hB_le_X : B ≤ X := by rw [← hXeqB]
      exact hZ₀notleX ((by simp [B] : Z₀ ≤ B).trans hB_le_X)
    have hp_lt_cardB : p.val < Nat.card B := by
      simpa [hpX] using natCard_lt_of_subgroup_lt hXltB
    have hBp : IsPGroup p.val B := by
      letI : IsElementaryAbelian p.val B := hBelem
      exact IsElementaryAbelian.isPGroup p.val B
    have hBcard_lower : p.val ^ 2 ≤ Nat.card B := by
      rcases hBp.exists_card_eq with ⟨n, hn⟩
      have hn_ge_two : 2 ≤ n := by
        by_cases hn0 : n = 0
        · have hp_lt_one : p.val < 1 := by simpa [hn, hn0] using hp_lt_cardB
          exact False.elim ((not_lt_of_ge p.property.one_lt.le) hp_lt_one)
        by_cases hn1 : n = 1
        · simp [hn, hn1] at hp_lt_cardB
        omega
      rw [hn]
      exact Nat.pow_le_pow_right p.property.pos hn_ge_two
    have hBgen_le_rankC : generatorRank B ≤ groupRank C := by
      let Bsub : Subgroup C := B.subgroupOf C
      have hBsubp : IsPGroup p.val Bsub :=
        hBp.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := B) (K := C) hB_le_C).symm
      have hBsubcomm : IsMulCommutative Bsub := by
        letI : IsMulCommutative B := hBelem.toIsMulCommutative
        exact Subgroup.subgroupOf_isMulCommutative (H := B) (K := C)
      have hgen_eq : generatorRank Bsub = generatorRank B := by
        rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
        exact Group.rank_congr
          (Subgroup.subgroupOfEquivOfLe (H := B) (K := C) hB_le_C)
      have hgen_le_prime : generatorRank Bsub ≤ primeRank p.val C :=
        section12_generatorRank_le_primeRank_of_subgroup
          (R := C) (q := p.val) hBsubp hBsubcomm
      have hprime_le_rankC : primeRank p.val C ≤ groupRank C := by
        let S : Sylow p.val C :=
          Classical.choice (Sylow.nonempty (p := p.val) (G := C))
        exact
          (section10_primeRank_le_groupRank_sylow (G := C) (p := p) S).trans
            (section8_groupRank_le_of_subgroup (G := C) (S : Subgroup C))
      have hgen_le_prime' : generatorRank B ≤ primeRank p.val C := by
        simpa [hgen_eq] using hgen_le_prime
      exact hgen_le_prime'.trans hprime_le_rankC
    have hBgen_le_two : generatorRank B ≤ 2 := hBgen_le_rankC.trans hCrank
    have hBcard_upper : Nat.card B ≤ p.val ^ 2 := by
      letI : IsElementaryAbelian p.val B := hBelem
      letI : CommGroup B := IsMulCommutative.instCommGroup
      have hcard_dvd : Nat.card B ∣ p.val ^ Group.rank B := by
        simpa using card_dvd_exponent_pow_rank' (G := B) (n := p.val) (fun b =>
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (show Monoid.exponent B ∣ p.val by
              simpa using IsElementaryAbelian.exponent_dvd_p p.val B) b)
      have hrank_le_two : Group.rank B ≤ 2 := by
        simpa [generatorRank_eq_group_rank] using hBgen_le_two
      calc
        Nat.card B ≤ p.val ^ Group.rank B :=
          Nat.le_of_dvd (pow_pos p.property.pos _) hcard_dvd
        _ ≤ p.val ^ 2 := Nat.pow_le_pow_right p.property.pos hrank_le_two
    have hBcard : Nat.card B = p.val ^ 2 :=
      le_antisymm hBcard_upper hBcard_lower
    have hBrankTwo : B ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := ⟨hBcard, hBelem⟩
    have hBmaxElem : B ∈ maximalElementaryAbelianSubgroups p.val G := by
      by_contra hBnotmax
      have hBunique : B ∈ section9UniqueSubgroups G :=
        theorem_9_6_in_particular (G := G)
          ⟨p.val, p.property, hBrankTwo, hBnotmax⟩
      have hCproper : C ≠ ⊤ := by
        have hC_le_M : C ≤ M := by
          intro x hxC
          exact hMFleM hxC.1
        intro hCtop
        have htop_le_M : (⊤ : Subgroup G) ≤ M := by
          simpa [hCtop] using hC_le_M
        exact hM.1 (top_le_iff.mp htop_le_M)
      exact hCnotUnique (section9_unique_of_le hB_le_C hCproper hBunique)
    exact ⟨hBrankTwo, hBmaxElem⟩
  have hZ₀primeB :
      Z₀ ∈ section10PrimeOrderSubgroupsIn p B := by
    simpa [Z₀, P] using
      lemma_10_13_a (G := G) (p := p) (A := B) (P := P) (A₀ := X)
        hpG hBmax hPp (by simpa [P] using hpNoncomm) hBleP hXB
        (by simpa [Z₀, P] using hXneZ₀)
  exact hZ₀primeB.2

/-- The `B = X ⊔ Ω₁(Z(P))` construction from the source-prime branch,
packaged inside the `p`-core.  This is the exact rank-two maximal elementary
abelian subgroup needed by Theorem 5.3 in the `𝓟₁` exceptional route. -/
private theorem CFSG.section15_theorem15_7_source_p_rankTwoMaximal_pCore
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hpX : p.val = Nat.card X)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF)) :
    ∃ B : Subgroup (section15PCoreIn p MF),
      B ∈ section10RankTwoMaximalElementaryAbelianSubgroups p
        (section15PCoreIn p MF) := by
  classical
  have hXprime : X ∈ section10PrimeOrderSubgroupsIn p X := ⟨le_rfl, hpX.symm⟩
  have hfacts :=
    section15_theorem15_7_prime_order_centralizer_facts
      (G := G) hM hMF hnotTI hg hX hXne hE hXprime
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  rcases hMF.1 with ⟨hMFleM, _hMFnormM, hMFnil, _hMFHall⟩
  have hXleMF : X ≤ MF := hred.2.2.1
  have hXp : IsPGroup p.val X :=
    section15_isPGroup_of_prime_card (G := G) (A := X) (q := p) hpX
  have hXleP : X ≤ section15PCoreIn p MF :=
    section15_pSubgroup_le_pCoreIn_of_nilpotent
      (G := G) (H := MF) (X := X) (p := p) hMFnil hXleMF hXp
  let P : Subgroup G := section15PCoreIn p MF
  let Z₀ : Subgroup G := section10OmegaOneCenter p P
  have hXnotleZ₀ : ¬ X ≤ Z₀ := by
    intro hXleZ₀
    have hP_le_C : P ≤ subgroupCentralizerIn MF X := by
      intro x hxP
      refine ⟨section15_pCoreIn_le p MF (by simpa [P] using hxP), ?_⟩
      change x ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyX
      have hyZ₀ : y ∈ Z₀ := hXleZ₀ hyX
      have hy_cent_P : y ∈ Subgroup.centralizer (P : Set G) := by
        simpa [Z₀] using section15_omegaOneCenter_le_centralizer (G := G) (p := p) P hyZ₀
      exact (Subgroup.mem_centralizer_iff.mp hy_cent_P x hxP).symm
    have hPcomm : IsMulCommutative P := by
      haveI : IsMulCommutative (subgroupCentralizerIn MF X) := by
        simpa using hfacts.2.2
      refine ⟨⟨fun a b => ?_⟩⟩
      have hcommG :
          (a : G) * (b : G) = (b : G) * (a : G) :=
        setLike_mul_comm
          (s := subgroupCentralizerIn MF X) (hP_le_C a.property) (hP_le_C b.property)
      exact Subtype.ext hcommG
    exact hpNoncomm (by simpa [P] using hPcomm)
  have hZ₀card : Nat.card Z₀ = p.val := by
    simpa [Z₀, P] using
      section15_theorem15_7_source_p_omegaOneCenter_card
        (G := G) (M := M) (MF := MF) (X := X) (E := E)
        (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        (g := g) (p := p)
        hM hMF hnotTI hg hX hXne hE hMFnoncomm hpX hpNoncomm
  have hZ₀leP : Z₀ ≤ P := by
    simpa [Z₀] using section15_omegaOneCenter_le (G := G) (p := p) P
  have hXleP' : X ≤ P := by
    simpa [P] using hXleP
  let B : Subgroup G := X ⊔ Z₀
  have hBleP : B ≤ P := by
    simpa [B] using sup_le hXleP' hZ₀leP
  have hBmax : B ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G := by
    haveI : Fact p.val.Prime := ⟨p.property⟩
    let C : Subgroup G := subgroupCentralizerIn MF X
    have hCnotUnique : C ∉ section9UniqueSubgroups G := by
      simpa [C] using hfacts.1
    have hXelem : IsElementaryAbelian p.val X := by
      haveI : IsCyclic X := isCyclic_of_prime_card (p := p.val) hpX.symm
      exact section15_isElementaryAbelian_of_prime_card_isCyclic
        (p := p.val) (H := X) hpX.symm
    have hZ₀elem : IsElementaryAbelian p.val Z₀ := by
      simpa [Z₀] using
        section15_omegaOneCenter_isElementaryAbelian (G := G) (p := p) P
    have hZ₀leCentX : Z₀ ≤ Subgroup.centralizer (X : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro x hxX
      have hz_cent_P : z ∈ Subgroup.centralizer (P : Set G) := by
        simpa [Z₀] using
          section15_omegaOneCenter_le_centralizer (G := G) (p := p) P hz
      exact Subgroup.mem_centralizer_iff.mp hz_cent_P x (hXleP' hxX)
    have hBelem : IsElementaryAbelian p.val B := by
      letI : IsElementaryAbelian p.val X := hXelem
      letI : IsElementaryAbelian p.val Z₀ := hZ₀elem
      simpa [B] using
        section15_isElementaryAbelian_sup_of_le_centralizer
          (G := G) (p := p.val) (E := X) (D := Z₀) hZ₀leCentX
    have hB_le_C : B ≤ C := by
      have hB_le_cent_X : B ≤ Subgroup.centralizer (X : Set G) := by
        simpa [B] using
          (show X ⊔ Z₀ ≤ Subgroup.centralizer (X : Set G) from
            sup_le
              (by
                intro x hxX
                rw [Subgroup.mem_centralizer_iff]
                intro y hyX
                haveI : IsElementaryAbelian p.val X := hXelem
                exact
                  setLike_mul_comm
                    (s := X) hyX hxX)
              hZ₀leCentX)
      intro x hxB
      exact ⟨section15_pCoreIn_le p MF (by simpa [P] using hBleP hxB),
        hB_le_cent_X hxB⟩
    have hXinfZ₀_bot : X ⊓ Z₀ = ⊥ := by
      by_contra hne
      have hXleZ₀' : X ≤ Z₀ :=
        section15_le_of_prime_card_inf_ne_bot
          (G := G) (A := X) (B := Z₀) (q := p) hpX hne
      exact hXnotleZ₀ hXleZ₀'
    have hBcard : Nat.card B = p.val ^ 2 := by
      have hX_norm : (X.subgroupOf B).Normal := by
        have hBcomm : IsMulCommutative B := hBelem.toIsMulCommutative
        letI : IsMulCommutative B := hBcomm
        letI : CommGroup B := IsMulCommutative.instCommGroup
        infer_instance
      have hcomp :
          (X.subgroupOf B).IsComplement' (Z₀.subgroupOf B) := by
        refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
        · rw [Subgroup.disjoint_def]
          intro z hzX hzZ
          apply Subtype.ext
          have hzinf : ((z : B) : G) ∈ X ⊓ Z₀ := ⟨hzX, hzZ⟩
          have hzbot : ((z : B) : G) ∈ (⊥ : Subgroup G) := by
            simpa [hXinfZ₀_bot] using hzinf
          exact Subgroup.mem_bot.mp hzbot
        · rw [Set.eq_univ_iff_forall]
          intro z
          let XB : Subgroup B := X.subgroupOf B
          let ZB : Subgroup B := Z₀.subgroupOf B
          haveI : XB.Normal := by simpa [XB] using hX_norm
          have hsup_top : XB ⊔ ZB = ⊤ := by
            simpa [XB, ZB, B] using
              (Subgroup.subgroupOf_sup (A := X) (A' := Z₀) (B := B)
                le_sup_left le_sup_right).symm
          have hz : z ∈ XB ⊔ ZB := by simp [hsup_top]
          rcases (Subgroup.mem_sup_of_normal_left
              (x := z) (s := XB) (t := ZB)).1 hz with
            ⟨x, hxX, y, hyZ, hxy⟩
          exact ⟨x, hxX, y, hyZ, hxy⟩
      have hmul := hcomp.card_mul
      rw [natCard_subgroupOf_eq X B (by simp [B]),
        natCard_subgroupOf_eq Z₀ B (by simp [B]),
        hpX.symm, hZ₀card] at hmul
      simpa [pow_two] using hmul.symm
    have hBrankTwo : B ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := ⟨hBcard, hBelem⟩
    have hBmaxElem : B ∈ maximalElementaryAbelianSubgroups p.val G := by
      by_contra hBnotmax
      have hBunique : B ∈ section9UniqueSubgroups G :=
        theorem_9_6_in_particular (G := G)
          ⟨p.val, p.property, hBrankTwo, hBnotmax⟩
      have hCproper : C ≠ ⊤ := by
        have hC_le_M : C ≤ M := by
          intro x hxC
          exact hMFleM hxC.1
        intro hCtop
        have htop_le_M : (⊤ : Subgroup G) ≤ M := by
          simpa [hCtop] using hC_le_M
        exact hM.1 (top_le_iff.mp htop_le_M)
      exact hCnotUnique (section9_unique_of_le hB_le_C hCproper hBunique)
    exact ⟨hBrankTwo, hBmaxElem⟩
  refine ⟨B.subgroupOf P, ?_⟩
  simpa [P] using
    section15_rankTwoMaximal_subgroupOf_of_le
      (G := G) (p := p) (A := B) (S := P) hBleP hBmax.1 hBmax.2

/-- The type `𝓕` endpoint of Theorem 15.7(e): Lemma 15.1(e), applied to
the nonabelian setup, gives the exponent divisibility in alternative (2). -/
private theorem CFSG.section15_theorem15_7_F_exponent_divisibility
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hF : M ∈ section14MFamilyF G)
    (hpX : p.val = Nat.card X)
    (_hpσβ : p ∈ section10SigmaPrimes M \ section10BetaPrimes M)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF))
    (hpPrimeCyclic : IsCyclic (section10PPrimeCore p MF)) :
    ∀ q : Nat.Primes, q ∈ subgroupPrimeSet MF →
      section15QuotientExponentDvd MF M (q.val - 1) := by
  classical
  rcases hMF.1 with ⟨hMFleM, hMFnormM, hMFnil, _hMFHall⟩
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  have hMF_eq_msigma : MF = section10Msigma M := hred.2.1
  rcases section15_exists_sigma_complement (G := G) hM with ⟨U, hUcomp⟩
  have hKU : section15KUData M (⊥ : Subgroup G) U :=
    section15_KUData_of_empty_kappa_sigma_complement
      (G := G) (M := M) (U := U) hM hF.2 hUcomp
  have hUne : U ≠ ⊥ :=
    section15_complementToMsigma_ne_bot (G := G) (M := M) (E := U) hM hUcomp
  rcases lemma_15_1_e_join (G := G) (M := M) (K := (⊥ : Subgroup G)) (U := U)
      hM hKU hUne with
    ⟨U₀, _hU₀U, hExpU₀U, hFrobJoin⟩
  have hcompMFU : section12ComplementIn M MF U := by
    simpa [section12ComplementToMsigma, ← hMF_eq_msigma] using hUcomp
  have hMFnorm : section10NormalIn MF M := ⟨hMFleM, hMFnormM⟩
  intro q hqMF
  refine
    section15QuotientExponentDvd_of_complement_exponent_dvd
      (G := G) (H := MF) (M := M) (U := U) hcompMFU hMFnorm ?_
  have hU₀dvd : Monoid.exponent U₀ ∣ q.val - 1 := by
    let Pq : Subgroup G := section15PCoreIn q MF
    let Zq : Subgroup G := section10OmegaOneCenter q Pq
    have hZq_card : Nat.card Zq = q.val := by
      by_cases hqp : q = p
      · subst q
        simpa [Pq, Zq] using
          section15_theorem15_7_source_p_omegaOneCenter_card
            (G := G) (M := M) (MF := MF) (X := X) (E := E)
            (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
            (g := g) (p := p)
            hM hMF hnotTI hg hX hXne hE hMFnoncomm hpX hpNoncomm
      · have hPq_ne : Pq ≠ ⊥ := by
          simpa [Pq] using
            section15_pCoreIn_ne_bot_of_mem_primeSet_nilpotent
              (G := G) (H := MF) (q := q) hMFnil hqMF
        have hPq_cyclic : IsCyclic Pq := by
          exact
            Subgroup.isCyclic_of_le
              (H := Pq) (H' := section10PPrimeCore p MF)
              (by
                simpa [Pq] using
                  section15_pCoreIn_le_pPrimeCore_of_ne
                    (G := G) (H := MF) (p := p) (q := q) hqp)
        have hPq_p : IsPGroup q.val Pq := by
          simpa [Pq] using section15_pCoreIn_isPGroup q MF
        simpa [Zq] using
          section15_omegaOneCenter_card_eq_prime_of_cyclic_pSubgroup
            (G := G) (H := Pq) (q := q) hPq_p hPq_cyclic hPq_ne
    haveI : Fact q.val.Prime := ⟨q.property⟩
    have hZq_cyclic : IsCyclic Zq :=
      isCyclic_of_prime_card (p := q.val) hZq_card
    have hZq_le_MF : Zq ≤ MF := by
      have hZq_le_Pq : Zq ≤ Pq := by
        simpa [Zq] using section15_omegaOneCenter_le (G := G) (p := q) Pq
      exact hZq_le_Pq.trans (by simpa [Pq] using section15_pCoreIn_le q MF)
    have hZq_le_msigma : Zq ≤ section10Msigma M := by
      simpa [← hMF_eq_msigma] using hZq_le_MF
    have hU₀normZq : U₀ ≤ Subgroup.normalizer (Zq : Set G) := by
      have hnorm :=
        section15_omegaOneCenter_normalized_by_complement_of_frobeniusJoin
          (G := G) (K := section10Msigma M) (R := U₀) (q := q) hFrobJoin
      simpa [Pq, Zq, ← hMF_eq_msigma] using hnorm
    have hregular :
        ∀ a : G, a ∈ U₀ → a ≠ 1 → elementCentralizerIn Zq a = ⊥ :=
      section15_frobeniusJoin_regular_on_subgroup
        (G := G) (K := section10Msigma M) (R := U₀) (Z := Zq)
        hFrobJoin hZq_le_msigma
    exact
      section15_exponent_dvd_prime_sub_one_of_regular_conj_action
        (G := G) (A := U₀) (Z := Zq) (q := q)
        hU₀normZq hZq_cyclic hZq_card hregular
  simpa [← hExpU₀U] using hU₀dvd

/-- The type `𝓟₁` endpoint of Theorem 15.7(e): from the common nonabelian
setup, if the exponent-divisibility alternative fails, the `K*` route gives
the exceptional cardinality alternative. -/
private theorem CFSG.section15_theorem15_7_P1_kstar_route_of_not_exponent_divisibility
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hpX : p.val = Nat.card X)
    (hpσβ : p ∈ section10SigmaPrimes M \ section10BetaPrimes M)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF))
    (hpPrimeCyclic : IsCyclic (section10PPrimeCore p MF))
    (hnotExp :
      ¬ ∃ p : Nat.Primes,
        p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
          ¬ IsMulCommutative (section15PCoreIn p MF) ∧
            IsCyclic (section10PPrimeCore p MF) ∧
              ∀ q : Nat.Primes, q ∈ subgroupPrimeSet MF →
                section15QuotientExponentDvd MF M (q.val - 1)) :
    ∃ K : Subgroup G,
      section12HallSubgroupIn (section14KappaPrimes M) K M ∧
        section14KStar M K ≤ section15PCoreIn p MF ∧
          section10OmegaOneCenter p (section15PCoreIn p MF) = section14KStar M K ∧
            ¬ Nat.card K ∣ p.val - 1 := by
  classical
  rcases hMF.1 with ⟨hMFleM, hMFnormM, hMFnil, _hMFHall⟩
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  rcases section15_exists_kappa_hallSubgroupIn (G := G) (M := M) hM with ⟨K, hK⟩
  have hσD : section10Msigma M = ambientDerivedSubgroup M :=
    section15_msigma_eq_ambientDerived_of_familyP1 hM hP1 hK
  have h15_6 := corollary_15_6 (G := G) (M := M) (MF := MF) (K := K)
    hP1.1 hMF hK
  let P : Subgroup G := section15PCoreIn p MF
  let Kstar : Subgroup G := section14KStar M K
  have hsecond_le_P : section15SecondDerivedSubgroup M ≤ P := by
    have hsecond_eq :
        section15SecondDerivedSubgroup M =
          ambientDerivedSubgroup (section10Msigma M) :=
      section15_secondDerived_eq_ambientDerived_msigma_of_msigma_eq_derived hσD
    rw [hsecond_eq]
    simpa [P, ← hred.2.1] using
      section15_ambientDerived_le_pCoreIn_of_nilpotent_pPrimeCore_cyclic
        (G := G) (H := MF) (p := p) hMFnil hpPrimeCyclic
  have hKstar_le_P : Kstar ≤ P := by
    simpa [Kstar] using h15_6.2.2.2.1.trans hsecond_le_P
  have hPp : IsPGroup p.val P := by
    simpa [P] using section15_pCoreIn_isPGroup p MF
  have hKstar_p : IsPGroup p.val Kstar :=
    IsPGroup.to_le (H := Kstar) (K := P) hPp hKstar_le_P
  have hKstar_card_p : Nat.card Kstar = p.val := by
    haveI : Fact p.val.Prime := ⟨p.property⟩
    rcases section15_familyP1_kstar_card_prime
        (G := G) (M := M) (K := K) hM hP1 hK with
      ⟨r, hr⟩
    rcases hKstar_p.exists_card_eq with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hnle
      have hn0 : n = 0 := by omega
      have hcard_one : Nat.card Kstar = 1 := by simp [hn, hn0]
      have hKstar_bot : Kstar = ⊥ := (Subgroup.card_eq_one (H := Kstar)).1 hcard_one
      exact h15_6.1 (by simpa [Kstar] using hKstar_bot)
    have hp_dvd_card : p.val ∣ Nat.card Kstar := by
      rw [hn]
      exact dvd_pow_self p.val (Nat.ne_of_gt hnpos)
    have hp_dvd_r : p.val ∣ r.val := by
      simpa [Kstar, hr] using hp_dvd_card
    have hp_eq_r : p.val = r.val :=
      (Nat.prime_dvd_prime_iff_eq p.property r.property).1 hp_dvd_r
    simp [Kstar, hr, hp_eq_r]
  have hprime : section14ActsInPrimeManner K (section10Msigma M) := by
    rcases proposition_14_2_a (G := G) (M := M) (K := K) hP1.1 hK with
      ⟨U, hU⟩
    exact hU.1
  have hD_eq_MF : ambientDerivedSubgroup M = MF := by
    rw [← hσD, ← hred.2.1]
  have hcompMFK : section12ComplementIn M MF K := by
    rcases theorem_14_7_h (G := G) (M := M) (K := K) hP1.1 hK with
      ⟨hKM, hDM, hsup, hdisj⟩
    have hsup' : M = K ⊔ MF := by simpa [hD_eq_MF] using hsup
    refine ⟨hMFleM, hKM, ?_, ?_⟩
    · simpa [sup_comm] using hsup'
    · simpa [hD_eq_MF] using hdisj.symm
  have hMFnorm : section10NormalIn MF M := ⟨hMFleM, hMFnormM⟩
  have hKnormMF : K ≤ Subgroup.normalizer (MF : Set G) :=
    hK.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormM)
  have hnot_imp :
      ¬ (section10OmegaOneCenter p P = Kstar → Nat.card K ∣ p.val - 1) := by
    intro himp
    apply hnotExp
    refine ⟨p, hpX, hpσβ, hpNoncomm, hpPrimeCyclic, ?_⟩
    intro q hqMF
    refine
      section15QuotientExponentDvd_of_complement_exponent_dvd
        (G := G) (H := MF) (M := M) (U := K) hcompMFK hMFnorm ?_
    let Pq : Subgroup G := section15PCoreIn q MF
    let Zq : Subgroup G := section10OmegaOneCenter q Pq
    have hZq_card : Nat.card Zq = q.val := by
      by_cases hqp : q = p
      · subst q
        simpa [Pq, Zq, P] using
          section15_theorem15_7_source_p_omegaOneCenter_card
            (G := G) (M := M) (MF := MF) (X := X) (E := E)
            (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
            (g := g) (p := p)
            hM hMF hnotTI hg hX hXne hE hMFnoncomm hpX hpNoncomm
      · have hPq_ne : Pq ≠ ⊥ := by
          simpa [Pq] using
            section15_pCoreIn_ne_bot_of_mem_primeSet_nilpotent
              (G := G) (H := MF) (q := q) hMFnil hqMF
        have hPq_cyclic : IsCyclic Pq := by
          exact
            Subgroup.isCyclic_of_le
              (H := Pq) (H' := section10PPrimeCore p MF)
              (by
                simpa [Pq] using
                  section15_pCoreIn_le_pPrimeCore_of_ne
                    (G := G) (H := MF) (p := p) (q := q) hqp)
        have hPq_p : IsPGroup q.val Pq := by
          simpa [Pq] using section15_pCoreIn_isPGroup q MF
        simpa [Zq] using
          section15_omegaOneCenter_card_eq_prime_of_cyclic_pSubgroup
            (G := G) (H := Pq) (q := q) hPq_p hPq_cyclic hPq_ne
    haveI : Fact q.val.Prime := ⟨q.property⟩
    have hZq_cyclic : IsCyclic Zq :=
      isCyclic_of_prime_card (p := q.val) hZq_card
    by_cases hZq_eq_Kstar : Zq = Kstar
    · have hqeqp : q = p := by
        apply Subtype.ext
        calc
          q.val = Nat.card Zq := hZq_card.symm
          _ = Nat.card Kstar := by rw [hZq_eq_Kstar]
          _ = p.val := hKstar_card_p
      have hKexp_card : Monoid.exponent K ∣ Nat.card K :=
        Group.exponent_dvd_nat_card
      have hKcard : Nat.card K ∣ q.val - 1 := by
        subst q
        exact himp (by simpa [P, Kstar] using hZq_eq_Kstar)
      exact hKexp_card.trans hKcard
    · have hZq_le_MF : Zq ≤ MF := by
        have hZq_le_Pq : Zq ≤ Pq := by
          simpa [Zq] using section15_omegaOneCenter_le (G := G) (p := q) Pq
        exact hZq_le_Pq.trans (by simpa [Pq] using section15_pCoreIn_le q MF)
      have hZq_le_msigma : Zq ≤ section10Msigma M := by
        simpa [← hred.2.1] using hZq_le_MF
      have hKnormZq : K ≤ Subgroup.normalizer (Zq : Set G) := by
        have hnorm :=
          section15_omegaOneCenter_normalized_by_normalizer
            (G := G) (H := MF) (A := K) (q := q) hKnormMF
        simpa [Pq, Zq] using hnorm
      have hregular :
          ∀ a : G, a ∈ K → a ≠ 1 → elementCentralizerIn Zq a = ⊥ := by
        intro a haK hane
        rw [Subgroup.eq_bot_iff_forall]
        intro y hy
        by_contra hyne
        have hy_msigma : y ∈ section10Msigma M := hZq_le_msigma hy.1
        have hcent_eq :
            elementCentralizerIn (section10Msigma M) a = Kstar := by
          simpa [Kstar] using
            section15_elementCentralizerIn_eq_kstar_of_prime_manner
              (G := G) (M := M) (K := K) hprime haK hane
        have hyKstar : y ∈ Kstar := by
          have hycent :
              y ∈ elementCentralizerIn (section10Msigma M) a := ⟨hy_msigma, hy.2⟩
          simpa [hcent_eq] using hycent
        have hinf_ne : Zq ⊓ Kstar ≠ ⊥ := by
          intro hbot
          have hybot : y ∈ (⊥ : Subgroup G) := by
            simpa [hbot] using (show y ∈ Zq ⊓ Kstar from ⟨hy.1, hyKstar⟩)
          exact hyne (Subgroup.mem_bot.mp hybot)
        have hZq_le_Kstar : Zq ≤ Kstar :=
          section15_le_of_prime_card_inf_ne_bot
            (G := G) (A := Zq) (B := Kstar) (q := q) hZq_card.symm hinf_ne
        have hKstar_inf_Zq_ne : Kstar ⊓ Zq ≠ ⊥ := by
          simpa [inf_comm] using hinf_ne
        have hKstar_le_Zq : Kstar ≤ Zq :=
          section15_le_of_prime_card_inf_ne_bot
            (G := G) (A := Kstar) (B := Zq) (q := p)
            hKstar_card_p.symm hKstar_inf_Zq_ne
        exact hZq_eq_Kstar (le_antisymm hZq_le_Kstar hKstar_le_Zq)
      exact
        section15_exponent_dvd_prime_sub_one_of_regular_conj_action
          (G := G) (A := K) (Z := Zq) (q := q)
          hKnormZq hZq_cyclic hZq_card hregular
  have hOmega_eq : section10OmegaOneCenter p P = Kstar := by
    by_contra hne
    exact hnot_imp (fun h => False.elim (hne h))
  have hKcard_not_dvd : ¬ Nat.card K ∣ p.val - 1 := by
    intro hdvd
    exact hnot_imp (fun _ => hdvd)
  exact ⟨K, hK, by simpa [Kstar, P] using hKstar_le_P,
    by simpa [Kstar, P] using hOmega_eq, hKcard_not_dvd⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omegaOneCenter_le_centerIn
    (p : Nat.Primes) (P : Subgroup G) :
    section10OmegaOneCenter p P ≤ centerIn P := by
  intro x hx
  exact ⟨section15_omegaOneCenter_le (G := G) (p := p) P hx,
    section15_omegaOneCenter_le_centralizer (G := G) (p := p) P hx⟩


private theorem CFSG.section15_theorem15_7_P1_center_pCore_eq_kstar_of_omega_eq
    {M MF X E E₁₂ E₁ E₂ E₃ K : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (_hMFnoncomm : ¬ IsMulCommutative MF)
    (hP1 : M ∈ section14MFamilyP1 G)
    (_hpX : p.val = Nat.card X)
    (hpσβ : p ∈ section10SigmaPrimes M \ section10BetaPrimes M)
    (_hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF))
    (_hpPrimeCyclic : IsCyclic (section10PPrimeCore p MF))
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (_hKstar_le : section14KStar M K ≤ section15PCoreIn p MF)
    (hOmega_eq : section10OmegaOneCenter p (section15PCoreIn p MF) = section14KStar M K) :
    centerIn (section15PCoreIn p MF) = section14KStar M K := by
  classical
  let P : Subgroup G := section15PCoreIn p MF
  let Z : Subgroup G := centerIn P
  let Kstar : Subgroup G := section14KStar M K
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hMF.1 with ⟨hMFleM, hMFnormM, _hMFnil, _hMFHall⟩
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  have hP_le_MF : P ≤ MF := by
    simpa [P] using section15_pCoreIn_le p MF
  have hP_le_msigma : P ≤ section10Msigma M := by
    simpa [← hred.2.1] using hP_le_MF
  have hKstar_le_Z : Kstar ≤ Z := by
    have hΩ_le_Z :
        section10OmegaOneCenter p P ≤ Z :=
      section15_omegaOneCenter_le_centerIn (G := G) p P
    simpa [P, Z, Kstar, hOmega_eq] using hΩ_le_Z
  have hK_norm_MF : K ≤ Subgroup.normalizer (MF : Set G) := by
    have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormM
    exact hK.1.trans hM_norm_MF
  have hK_norm_P : K ≤ Subgroup.normalizer (P : Set G) := by
    have hPchar : (pCore p.val MF).Characteristic :=
      section15_pCore_characteristic (R := MF) (p := p.val)
    letI : (pCore p.val MF).Characteristic := hPchar
    have hnorm :
        Subgroup.normalizer (MF : Set G) ≤ Subgroup.normalizer (P : Set G) := by
      simpa [P, section15PCoreIn] using
        section15_normalizer_le_normalizer_map_subtype_of_characteristic
          (G := G) MF (pCore p.val MF)
    exact hK_norm_MF.trans hnorm
  have hK_norm_Z : K ≤ Subgroup.normalizer (Z : Set G) := by
    have hZchar : (Subgroup.center P).Characteristic := Subgroup.centerCharacteristic
    letI : (Subgroup.center P).Characteristic := hZchar
    have hnorm_center :
        Subgroup.normalizer (P : Set G) ≤
          Subgroup.normalizer ((centerIn P : Subgroup G) : Set G) := by
      simpa [centerIn_eq_map_center_local] using
        section15_normalizer_le_normalizer_map_subtype_of_characteristic
          (G := G) P (Subgroup.center P)
    have hnorm :
        Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
      change Subgroup.normalizer (P : Set G) ≤
        Subgroup.normalizer ((centerIn P : Subgroup G) : Set G)
      exact hnorm_center
    exact hK_norm_P.trans hnorm
  have hZp : IsPGroup p.val Z := by
    have hPp : IsPGroup p.val P := by
      simpa [P] using section15_pCoreIn_isPGroup p MF
    exact IsPGroup.to_le (H := Z) (K := P) hPp (by
      intro z hz
      exact hz.1)
  have hK_coprime_p : Nat.Coprime (Nat.card K) p.val := by
    have hp_not_dvd_K : ¬ p.val ∣ Nat.card K := by
      intro hp_dvd_K
      have hpκ : p ∈ section14KappaPrimes M := by
        have hKsub_card : Nat.card (K.subgroupOf M) = Nat.card K :=
          section12_card_subgroupOf_eq hK.1
        exact hK.2.p_in_pi_of_p_dvd_card p (by
          simpa [hKsub_card] using hp_dvd_K)
      have hp_not_κ : p ∉ section14KappaPrimes M := by
        rw [hP1.2]
        intro hpκ'
        exact hpκ'.2 hpσβ.1
      exact hp_not_κ hpκ
    exact ((p.property.coprime_iff_not_dvd).2 hp_not_dvd_K).symm
  have hK_coprime_Z : Nat.Coprime (Nat.card K) (Nat.card Z) := by
    rcases hZp.exists_card_eq with ⟨n, hn⟩
    simpa [hn] using hK_coprime_p.pow_right n
  have hpodd : p.val ≠ 2 := by
    have hp_dvd_M : p.val ∣ Nat.card M := by
      simpa [subgroupPrimeSet] using hpσβ.1.1
    have hp_dvd_G : p.val ∣ Nat.card G :=
      hp_dvd_M.trans (Subgroup.card_subgroup_dvd_card M)
    exact Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  haveI : Subgroup.Normalizes K Z := ⟨hK_norm_Z⟩
  have hΩ_triv :
      ActsTriviallyOnSubgroup (A := K) (G := Z)
        (omega₁ (G := Z) (p := p.val)) := by
    have hΩ_le_fixed :
        omega₁ (G := Z) (p := p.val) ≤ fixedPointSubgroup K Z := by
      rw [omega₁, omega]
      refine (Subgroup.closure_le (K := fixedPointSubgroup K Z)).2 ?_
      intro z hz
      change z ∈ fixedPointSubgroup K Z
      rw [FixedPoints.mem_subgroup]
      intro a
      apply Subtype.ext
      have hzpowZ : z ^ p.val = 1 := by
        change z ^ (p.val ^ 1) = 1 at hz
        simpa [pow_one] using hz
      have hzpowG : ((z : Z) : G) ^ p.val = 1 := by
        exact congrArg Subtype.val hzpowZ
      have hzZ : ((z : Z) : G) ∈ Z := z.property
      have hzP : ((z : Z) : G) ∈ P := hzZ.1
      let zP : P := ⟨((z : Z) : G), hzP⟩
      have hzP_center : zP ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hzZ.2 (y : G) y.property
      let zC : Subgroup.center P := ⟨zP, hzP_center⟩
      have hzCpow : zC ^ p.val = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [zC, zP] using hzpowG
      have hzCΩ : zC ∈ omega₁ (G := Subgroup.center P) (p := p.val) := by
        change zC ∈ Subgroup.closure {x : Subgroup.center P | x ^ (p.val ^ 1) = 1}
        exact Subgroup.subset_closure (by simpa [pow_one] using hzCpow)
      have hzΩ₁Z : zP ∈ Ω₁Z p.val P := by
        change zP ∈ (omega₁ (G := Subgroup.center P) (p := p.val)).map
          (Subgroup.center P).subtype
        exact Subgroup.mem_map_of_mem (Subgroup.center P).subtype hzCΩ
      have hzΩ : ((z : Z) : G) ∈ section10OmegaOneCenter p P := by
        change ((z : Z) : G) ∈ (Ω₁Z p.val P).map P.subtype
        exact Subgroup.mem_map_of_mem P.subtype hzΩ₁Z
      have hzKstar : ((z : Z) : G) ∈ Kstar := by
        simpa [P, Kstar, hOmega_eq] using hzΩ
      have hzCentK : ((z : Z) : G) ∈ Subgroup.centralizer (K : Set G) :=
        section15_mem_centralizer_of_mem_kstar (G := G) (M := M) (K := K) hzKstar
      have hcomm : (a : G) * ((z : Z) : G) = ((z : Z) : G) * (a : G) := by
        exact Subgroup.mem_centralizer_iff.mp hzCentK (a : G) a.property
      have hconj : (a : G) * ((z : Z) : G) * (a : G)⁻¹ = ((z : Z) : G) := by
        simpa [mul_assoc] using congrArg (fun t : G => t * (a : G)⁻¹) hcomm
      simpa using hconj
    intro a z hz
    exact hΩ_le_fixed hz a
  have hZ_triv : ActsTrivially (A := K) (G := Z) := by
    haveI : Fact (IsPGroup p.val Z) := ⟨hZp⟩
    exact theorem_1_11 (G := Z) (A := K) (p := p.val) hpodd hK_coprime_Z hΩ_triv
  have hZ_le_Kstar : Z ≤ Kstar := by
    intro y hyZ
    change y ∈ subgroupCentralizerIn (section10Msigma M) K
    refine ⟨hP_le_msigma hyZ.1, ?_⟩
    change y ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    let kK : K := ⟨k, hk⟩
    let yZ : Z := ⟨y, hyZ⟩
    have hfix : kK • yZ = yZ := hZ_triv kK yZ
    have hconj : k * y * k⁻¹ = y := by
      simpa [kK, yZ] using congrArg Subtype.val hfix
    simpa [mul_assoc] using congrArg (fun t : G => t * k) hconj
  exact le_antisymm (by simpa [Z, Kstar] using hZ_le_Kstar)
    (by simpa [Z, Kstar] using hKstar_le_Z)


private theorem CFSG.section15_theorem15_7_P1_pCore_rank_le_two_of_center_eq_kstar
    {M MF X E E₁₂ E₁ E₂ E₃ K : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hpX : p.val = Nat.card X)
    (hpσβ : p ∈ section10SigmaPrimes M \ section10BetaPrimes M)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF))
    (_hpPrimeCyclic : IsCyclic (section10PPrimeCore p MF))
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (_hKstar_le : section14KStar M K ≤ section15PCoreIn p MF)
    (hCenter_eq : centerIn (section15PCoreIn p MF) = section14KStar M K)
    (hKcard_not_dvd : ¬ Nat.card K ∣ p.val - 1) :
    groupRank (section15PCoreIn p MF) ≤ 2 := by
  classical
  let P : Subgroup G := section15PCoreIn p MF
  by_contra hRank_not
  have hRank_notP : ¬ groupRank P ≤ 2 := by
    simpa [P] using hRank_not
  have hRank3 : 3 ≤ groupRank P := by omega
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hpodd : p.val ≠ 2 := by
    have hp_dvd_M : p.val ∣ Nat.card M := by
      simpa [subgroupPrimeSet] using hpσβ.1.1
    have hp_dvd_G : p.val ∣ Nat.card G :=
      hp_dvd_M.trans (Subgroup.card_subgroup_dvd_card M)
    exact Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hPp : IsPGroup p.val P := by
    simpa [P] using section15_pCoreIn_isPGroup p MF
  rcases
    section15_theorem15_7_source_p_rankTwoMaximal_pCore
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hpX hpNoncomm with
    ⟨B, hB⟩
  have hNarrow : IsNarrowPGroup p.val P := by
    exact
      (theorem_5_3 (p := p.val) hpodd (R := P) hPp hRank3).2
        ⟨B, hB.1, hB.2⟩
  rcases hMF.1 with ⟨hMFleM, hMFnormM, _hMFnil, _hMFHall⟩
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  have hP_le_MF : P ≤ MF := by
    simpa [P] using section15_pCoreIn_le p MF
  have hP_le_msigma : P ≤ section10Msigma M := by
    simpa [← hred.2.1] using hP_le_MF
  have hK_norm_MF : K ≤ Subgroup.normalizer (MF : Set G) := by
    have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormM
    exact hK.1.trans hM_norm_MF
  have hK_norm_P : K ≤ Subgroup.normalizer (P : Set G) := by
    have hPchar : (pCore p.val MF).Characteristic :=
      section15_pCore_characteristic (R := MF) (p := p.val)
    letI : (pCore p.val MF).Characteristic := hPchar
    have hnorm :
        Subgroup.normalizer (MF : Set G) ≤ Subgroup.normalizer (P : Set G) := by
      simpa [P, section15PCoreIn] using
        section15_normalizer_le_normalizer_map_subtype_of_characteristic
          (G := G) MF (pCore p.val MF)
    exact hK_norm_MF.trans hnorm
  haveI : Subgroup.Normalizes K P := ⟨hK_norm_P⟩
  let ρ : K →* MulAut P := MulDistribMulAction.toMulAut K P
  let Kstar : Subgroup G := section14KStar M K
  have hprime : section14ActsInPrimeManner K (section10Msigma M) := by
    rcases proposition_14_2_a (G := G) (M := M) (K := K) hP1.1 hK with
      ⟨U, hU⟩
    exact hU.1
  have hρinj : Function.Injective ρ := by
    have hρker_bot : ρ.ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro k hkρ
      have hρk : ρ k = 1 := by
        simpa [ρ, MonoidHom.mem_ker] using hkρ
      by_cases hkG_one : (k : G) = 1
      · exact Subtype.ext hkG_one
      · exfalso
        have hcent_eq :
            elementCentralizerIn (section10Msigma M) (k : G) = Kstar := by
          simpa [Kstar] using
            section15_elementCentralizerIn_eq_kstar_of_prime_manner
              (G := G) (M := M) (K := K) hprime k.property hkG_one
        have hP_le_Kstar : P ≤ Kstar := by
          intro x hxP
          have hx_msigma : x ∈ section10Msigma M := hP_le_msigma hxP
          have hfix :
              k • (⟨x, hxP⟩ : P) = ⟨x, hxP⟩ := by
            simpa [ρ, MulDistribMulAction.toMulAut_apply] using
              congrArg (fun f : MulAut P => f ⟨x, hxP⟩) hρk
          have hconj : (k : G) * x * (k : G)⁻¹ = x := by
            simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hK_norm_P]
              using congrArg Subtype.val hfix
          have hx_cent_k : x ∈ Subgroup.centralizer ({(k : G)} : Set G) := by
            rw [Subgroup.mem_centralizer_singleton_iff]
            have h := congrArg (fun t : G => t * (k : G)) hconj
            simpa [mul_assoc] using h.symm
          have hxcent : x ∈ elementCentralizerIn (section10Msigma M) (k : G) :=
            ⟨hx_msigma, hx_cent_k⟩
          simpa [hcent_eq] using hxcent
        have hP_le_center : P ≤ centerIn P := by
          simpa [P, Kstar, hCenter_eq] using hP_le_Kstar
        have hPcomm : IsMulCommutative P := by
          refine ⟨⟨fun x y => ?_⟩⟩
          have hxcenter : ((x : P) : G) ∈ centerIn P := hP_le_center x.property
          have hcommG : ((x : P) : G) * ((y : P) : G) =
              ((y : P) : G) * ((x : P) : G) :=
            (Subgroup.mem_centralizer_iff.mp hxcenter.2 ((y : P) : G) y.property).symm
          exact Subtype.ext hcommG
        exact hpNoncomm (by simpa [P] using hPcomm)
    exact (MonoidHom.ker_eq_bot_iff ρ).1 hρker_bot
  have hKcyc : IsCyclic K := by
    have hZcyc : IsCyclic (section14Z M K) :=
      (theorem_14_7_d (G := G) (M := M) (K := K) hP1.1 hK).2.1
    letI : IsCyclic (section14Z M K) := hZcyc
    exact Subgroup.isCyclic_of_le (show K ≤ section14Z M K by
      change K ≤ K ⊔ section14KStar M K
      exact le_sup_left)
  have hK_coprime_p : Nat.Coprime (Nat.card K) p.val := by
    have hp_not_dvd_K : ¬ p.val ∣ Nat.card K := by
      intro hp_dvd_K
      have hpκ : p ∈ section14KappaPrimes M := by
        have hKsub_card : Nat.card (K.subgroupOf M) = Nat.card K :=
          section12_card_subgroupOf_eq hK.1
        exact hK.2.p_in_pi_of_p_dvd_card p (by
          simpa [hKsub_card] using hp_dvd_K)
      have hp_not_κ : p ∉ section14KappaPrimes M := by
        rw [hP1.2]
        intro hpκ'
        exact hpκ'.2 hpσβ.1
      exact hp_not_κ hpκ
    exact ((p.property.coprime_iff_not_dvd).2 hp_not_dvd_K).symm
  let A : Subgroup (MulAut P) := ρ.range
  have hKodd : Odd (Nat.card K) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card K)
  have hAodd : Odd (Nat.card A) := by
    exact odd_of_card_dvd hKodd (by simpa [A, ρ] using Subgroup.card_range_dvd ρ)
  haveI : Group.IsSolvable K := by
    let KM : Subgroup M := K.subgroupOf M
    have hsolvM : Group.IsSolvable M :=
      IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
    haveI : Group.IsSolvable M := hsolvM
    have hKM_solv : Group.IsSolvable KM := by infer_instance
    let eK : KM ≃* K := Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hK.1
    exact Group.isSolvable_of_surjective (f := eK.toMonoidHom) eK.surjective
  haveI : Group.IsSolvable A := by
    change Group.IsSolvable ρ.range
    exact Group.isSolvable_of_surjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
  have hAcyc : IsCyclic A := by
    haveI : IsCyclic K := hKcyc
    exact isCyclic_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hρrange_inj : Function.Injective ρ.rangeRestrict := by
    intro x y hxy
    exact hρinj (congrArg Subtype.val hxy)
  let eρ : K ≃* A :=
    MulEquiv.ofBijective ρ.rangeRestrict ⟨hρrange_inj, ρ.rangeRestrict_surjective⟩
  have hAcard_eq_K : Nat.card A = Nat.card K := by
    simpa [eρ] using (Nat.card_congr eρ.toEquiv).symm
  haveI : IsCyclic A := hAcyc
  obtain ⟨a, ha_gen⟩ := IsCyclic.exists_monoid_generator (α := A)
  have horderA : orderOf a = Nat.card A := by
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    have hx := ha_gen x
    rcases (Submonoid.mem_powers_iff _ _).mp hx with ⟨n, hn⟩
    rw [← hn]
    exact ⟨(n : ℤ), by simp⟩
  have horder_coe_cardK : orderOf ((a : A) : MulAut P) = Nat.card K := by
    simpa [Subgroup.orderOf_coe, hAcard_eq_K] using horderA
  have hcop_order : Nat.Coprime p.val (orderOf ((a : A) : MulAut P)) := by
    rw [horder_coe_cardK]
    exact hK_coprime_p.symm
  have horder_dvd : orderOf ((a : A) : MulAut P) ∣ p.val - 1 := by
    simpa [A] using
      theorem_5_5_b (p := p.val) hpodd (R := P) hNarrow hRank3
        (A := A) hAodd ((a : A) : MulAut P) a.2 hcop_order
  have hKcard_dvd : Nat.card K ∣ p.val - 1 := by
    simpa [horder_coe_cardK] using horder_dvd
  exact hKcard_not_dvd hKcard_dvd

private theorem CFSG.section15_theorem15_7_P1_pCore_global_sylow_of_msigma
    {M MF : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hMF_eq_msigma : MF = section10Msigma M)
    (hpσ : p ∈ section10SigmaPrimes M) :
    ∃ S : Sylow p.val G, (S : Subgroup G) = section15PCoreIn p MF := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let P : Subgroup G := section15PCoreIn p MF
  have hP_le_MF : P ≤ MF := by
    simpa [P] using section15_pCoreIn_le p MF
  let Psub : Subgroup MF := P.subgroupOf MF
  have hPsub_eq_core : Psub = pCore p.val MF := by
    simpa [Psub, P] using section15_pCoreIn_subgroupOf_eq p MF
  have hPsub_not_index : ¬ p.val ∣ Psub.index := by
    rcases hMF.1 with ⟨_hMFleM, _hMFnormM, hMFnil, _hMFHall⟩
    let S : Sylow p.val MF := Classical.choice (Sylow.nonempty (p := p.val) (G := MF))
    have hSnormal : (S : Subgroup MF).Normal :=
      Group.IsNilpotent.sylow_normal hMFnil p.val S
    have hS_le_core : (S : Subgroup MF) ≤ pCore p.val MF :=
      le_sSup
        (show (S : Subgroup MF) ∈
          {K : Subgroup MF | K.Normal ∧ IsPGroup p.val K} from
            ⟨hSnormal, S.isPGroup'⟩)
    have hcore_le_S : pCore p.val MF ≤ (S : Subgroup MF) :=
      section15_pCore_le_sylow S
    have hcore_eq_S : pCore p.val MF = (S : Subgroup MF) :=
      le_antisymm hcore_le_S hS_le_core
    have hPsub_eq_S : Psub = (S : Subgroup MF) := by
      rw [hPsub_eq_core, hcore_eq_S]
    simpa [hPsub_eq_S] using S.not_dvd_index
  have hMF_not_index : ¬ p.val ∣ MF.index := by
    intro hidx
    have hidx_sigma : p.val ∣ (section10Msigma M).index := by
      simpa [hMF_eq_msigma] using hidx
    exact ((theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_index p hidx_sigma) hpσ
  have hPsub_map : Psub.map MF.subtype = P := by
    exact Subgroup.map_subgroupOf_eq_of_le (G := G) (H := P) (K := MF) hP_le_MF
  have hP_index_eq : P.index = Psub.index * MF.index := by
    simpa [Psub, hPsub_map] using
      (Subgroup.index_map_subtype (H := MF) (K := Psub))
  have hP_not_index : ¬ p.val ∣ P.index := by
    intro hidx
    have hidx_prod : p.val ∣ Psub.index * MF.index := by
      simpa [hP_index_eq] using hidx
    rcases p.property.dvd_or_dvd hidx_prod with hleft | hright
    · exact hPsub_not_index hleft
    · exact hMF_not_index hright
  let S : Sylow p.val G := (section15_pCoreIn_isPGroup p MF).toSylow hP_not_index
  refine ⟨S, ?_⟩
  simp [S, P, IsPGroup.toSylow_coe]


private theorem CFSG.section15_theorem15_7_P1_pCore_card_exponent_of_rank_le_two_center_eq_kstar
    {M MF X E E₁₂ E₁ E₂ E₃ K : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (_hMFnoncomm : ¬ IsMulCommutative MF)
    (_hP1 : M ∈ section14MFamilyP1 G)
    (_hpX : p.val = Nat.card X)
    (hpσβ : p ∈ section10SigmaPrimes M \ section10BetaPrimes M)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF))
    (_hpPrimeCyclic : IsCyclic (section10PPrimeCore p MF))
    (_hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (_hKstar_le : section14KStar M K ≤ section15PCoreIn p MF)
    (hOmega_eq : section10OmegaOneCenter p (section15PCoreIn p MF) = section14KStar M K)
    (hCenter_eq : centerIn (section15PCoreIn p MF) = section14KStar M K)
    (hRank_le : groupRank (section15PCoreIn p MF) ≤ 2) :
    Nat.card (section15PCoreIn p MF) = p.val ^ 3 ∧
      Monoid.exponent (section15PCoreIn p MF) = p.val := by
  classical
  let P : Subgroup G := section15PCoreIn p MF
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  have hMF_eq_msigma : MF = section10Msigma M := hred.2.1
  rcases
    section15_theorem15_7_P1_pCore_global_sylow_of_msigma
      (G := G) (M := M) (MF := MF) (p := p)
      hM hMF hMF_eq_msigma hpσβ.1 with
    ⟨S, hS_eq_P⟩
  have hSrank_le : groupRank (S : Subgroup G) ≤ 2 := by
    rw [hS_eq_P]
    simpa [P] using hRank_le
  rcases corollary_10_7_b (G := G) S hSrank_le with hScomm | hshape
  · have hPcomm : IsMulCommutative P := by
      change IsMulCommutative (section15PCoreIn p MF)
      rw [← hS_eq_P]
      exact hScomm
    exact False.elim (hpNoncomm (by simpa [P] using hPcomm))
  · rcases hshape with
      ⟨P₁, P₂, hP₁card, hP₁noncomm, hP₁exp, hP₂cyc, hcentral, hΩcenter⟩
    have hP₁p : IsPGroup p.val P₁ := S.isPGroup'.to_subgroup P₁
    letI : Fact (IsPGroup p.val P₁) := ⟨hP₁p⟩
    have hP₁extra : IsExtraspecial p.val P₁ :=
      isExtraspecial_of_noncommutative_card_p3_exponent_p
        (K := P₁) (p := p.val) hP₁card hP₁exp hP₁noncomm
    letI : IsExtraspecial p.val P₁ := hP₁extra
    have hder_center :
        (derivedSubgroup P₁).map P₁.subtype =
          (Subgroup.center P₁).map P₁.subtype :=
      derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
        (R := (S : Subgroup G)) (p := p.val) P₁
    have hΩder :
        (omega₁ (G := P₂) (p := p.val)).map P₂.subtype =
          (derivedSubgroup P₁).map P₁.subtype := by
      letI : IsCyclic P₂ := hP₂cyc
      calc
        (omega₁ (G := P₂) (p := p.val)).map P₂.subtype =
            (Ω₁Z p.val P₂).map P₂.subtype := by
          rw [section15_omega1Z_eq_omega1_of_isCyclic (R := P₂) (p := p.val)]
        _ = (Subgroup.center P₁).map P₁.subtype := hΩcenter
        _ = (derivedSubgroup P₁).map P₁.subtype := hder_center.symm
    have homegaS : omega₁ (G := (S : Subgroup G)) (p := p.val) = P₁ :=
      section15_omega1_eq_centralProduct_left_of_exponent
        (p := p.val) (R := (S : Subgroup G)) (R₁ := P₁) (R₂ := P₂)
        hcentral hP₁exp hΩder
    have hCenterOmega_P : centerIn P = section10OmegaOneCenter p P := by
      rw [hCenter_eq, hOmega_eq]
    have hCenterOmega_S_ambient :
        centerIn (S : Subgroup G) = section10OmegaOneCenter p (S : Subgroup G) := by
      simpa [P, hS_eq_P] using hCenterOmega_P
    have hCenterOmega_S :
        Subgroup.center (S : Subgroup G) = Ω₁Z p.val (S : Subgroup G) := by
      apply Subgroup.map_injective (f := (S : Subgroup G).subtype)
        (S : Subgroup G).subtype_injective
      simpa [centerIn_eq_map_center_local, section10OmegaOneCenter] using
        hCenterOmega_S_ambient
    have hP₂_le_center : P₂ ≤ Subgroup.center (S : Subgroup G) := by
      rcases hcentral with ⟨_hP₁norm, _hP₂norm, hcomm12, hsup12⟩
      have hP₂_le_cent_P₁ : P₂ ≤ Subgroup.centralizer (P₁ : Set (S : Subgroup G)) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := P₂) (H₂ := P₁)).1
          (by simpa [Subgroup.commutator_comm] using hcomm12)
      letI : IsCyclic P₂ := hP₂cyc
      letI : CommGroup P₂ := IsCyclic.commGroup
      intro y hy
      rw [Subgroup.mem_center_iff]
      intro x
      have hx_sup : x ∈ P₁ ⊔ P₂ := by
        rw [hsup12]
        exact Subgroup.mem_top x
      rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := P₁) (t := P₂)).1 hx_sup with
        ⟨x₁, hx₁, x₂, hx₂, hx₁x₂⟩
      have hy_x₁ : y * x₁ = x₁ * y := by
        exact (Subgroup.mem_centralizer_iff.mp (hP₂_le_cent_P₁ hy) x₁ hx₁).symm
      have hy_x₂ : y * x₂ = x₂ * y := by
        have hcomm :
            (⟨y, hy⟩ : P₂) * (⟨x₂, hx₂⟩ : P₂) =
              (⟨x₂, hx₂⟩ : P₂) * (⟨y, hy⟩ : P₂) := by
          exact mul_comm _ _
        exact congrArg P₂.subtype hcomm
      rw [← hx₁x₂]
      calc
        (x₁ * x₂) * y = x₁ * (x₂ * y) := by simp [mul_assoc]
        _ = x₁ * (y * x₂) := by rw [← hy_x₂]
        _ = (x₁ * y) * x₂ := by simp [mul_assoc]
        _ = (y * x₁) * x₂ := by rw [← hy_x₁]
        _ = y * (x₁ * x₂) := by simp [mul_assoc]
    have hΩZ_le_omega :
        Ω₁Z p.val (S : Subgroup G) ≤ omega₁ (G := (S : Subgroup G)) (p := p.val) := by
      simpa [Ω₁Z] using
        section15_omega1_map_subtype_le
          (R := (S : Subgroup G)) (p := p.val)
          (Subgroup.center (S : Subgroup G))
    have hP₂_le_P₁ : P₂ ≤ P₁ := by
      intro y hy
      have hy_center : y ∈ Subgroup.center (S : Subgroup G) := hP₂_le_center hy
      have hyΩ : y ∈ Ω₁Z p.val (S : Subgroup G) := by
        simpa [hCenterOmega_S] using hy_center
      have hyomega : y ∈ omega₁ (G := (S : Subgroup G)) (p := p.val) :=
        hΩZ_le_omega hyΩ
      simpa [homegaS] using hyomega
    have hP₁top : P₁ = ⊤ := by
      rcases hcentral with ⟨_hP₁norm, _hP₂norm, _hcomm12, hsup12⟩
      calc
        P₁ = P₁ ⊔ P₂ := (sup_eq_left.mpr hP₂_le_P₁).symm
        _ = ⊤ := hsup12
    have hScard : Nat.card (S : Subgroup G) = Nat.card P₁ := by
      simp [hP₁top]
    constructor
    · calc
        Nat.card (section15PCoreIn p MF) = Nat.card (S : Subgroup G) := by
          simp [hS_eq_P]
        _ = Nat.card P₁ := hScard
        _ = p.val ^ 3 := hP₁card
    · have hTopExp : Monoid.exponent (⊤ : Subgroup (S : Subgroup G)) = p.val := by
        rw [← hP₁top]
        exact hP₁exp
      have hSexp : Monoid.exponent (S : Subgroup G) = p.val := by
        rw [Subgroup.exponent_top] at hTopExp
        exact hTopExp
      have hP_eq_S : P = (S : Subgroup G) := by
        simpa [P] using hS_eq_P.symm
      calc
        Monoid.exponent (section15PCoreIn p MF) = Monoid.exponent P := by rfl
        _ = Monoid.exponent (S : Subgroup G) := by rw [hP_eq_S]
        _ = p.val := hSexp

private theorem CFSG.section15_theorem15_7_P1_pCore_card_of_rank_le_two_center_eq_kstar
    {M MF X E E₁₂ E₁ E₂ E₃ K : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hpX : p.val = Nat.card X)
    (hpσβ : p ∈ section10SigmaPrimes M \ section10BetaPrimes M)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF))
    (hpPrimeCyclic : IsCyclic (section10PPrimeCore p MF))
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKstar_le : section14KStar M K ≤ section15PCoreIn p MF)
    (hOmega_eq : section10OmegaOneCenter p (section15PCoreIn p MF) = section14KStar M K)
    (hCenter_eq : centerIn (section15PCoreIn p MF) = section14KStar M K)
    (hRank_le : groupRank (section15PCoreIn p MF) ≤ 2) :
    Nat.card (section15PCoreIn p MF) = p.val ^ 3 := by
  exact
    (section15_theorem15_7_P1_pCore_card_exponent_of_rank_le_two_center_eq_kstar
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (K := K) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hK hKstar_le hOmega_eq hCenter_eq hRank_le).1

private theorem CFSG.section15_theorem15_7_P1_pCore_card_of_kstar_route
    {M MF X E E₁₂ E₁ E₂ E₃ K : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hpX : p.val = Nat.card X)
    (hpσβ : p ∈ section10SigmaPrimes M \ section10BetaPrimes M)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF))
    (hpPrimeCyclic : IsCyclic (section10PPrimeCore p MF))
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKstar_le : section14KStar M K ≤ section15PCoreIn p MF)
    (hOmega_eq : section10OmegaOneCenter p (section15PCoreIn p MF) = section14KStar M K)
    (hKcard_not_dvd : ¬ Nat.card K ∣ p.val - 1) :
    Nat.card (section15PCoreIn p MF) = p.val ^ 3 := by
  have hCenter_eq :
      centerIn (section15PCoreIn p MF) = section14KStar M K :=
    section15_theorem15_7_P1_center_pCore_eq_kstar_of_omega_eq
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (K := K) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hK hKstar_le hOmega_eq
  have hRank_le :
      groupRank (section15PCoreIn p MF) ≤ 2 :=
    section15_theorem15_7_P1_pCore_rank_le_two_of_center_eq_kstar
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (K := K) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hK hKstar_le hCenter_eq hKcard_not_dvd
  exact
    section15_theorem15_7_P1_pCore_card_of_rank_le_two_center_eq_kstar
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (K := K) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hK hKstar_le hOmega_eq hCenter_eq hRank_le

/-- The Theorem 2.5 cardinality core in the `𝓟₁` exceptional route: the
complement `K` acts on the extraspecial `p`-core with center fixed exactly
as `K*`, forcing `|K| ∣ p+1`. -/
private theorem CFSG.section15_theorem15_7_P1_kappa_card_dvd_p_add_one_of_kstar_route
    {M MF X E E₁₂ E₁ E₂ E₃ K : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hpX : p.val = Nat.card X)
    (hpσβ : p ∈ section10SigmaPrimes M \ section10BetaPrimes M)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF))
    (hpPrimeCyclic : IsCyclic (section10PPrimeCore p MF))
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKstar_le : section14KStar M K ≤ section15PCoreIn p MF)
    (hOmega_eq : section10OmegaOneCenter p (section15PCoreIn p MF) = section14KStar M K)
    (hKcard_not_dvd : ¬ Nat.card K ∣ p.val - 1)
    (hpCore_card : Nat.card (section15PCoreIn p MF) = p.val ^ 3) :
    Nat.card K ∣ p.val + 1 := by
  classical
  let P : Subgroup G := section15PCoreIn p MF
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  have hP_le_MF : P ≤ MF := by
    simpa [P] using section15_pCoreIn_le p MF
  have hP_le_msigma : P ≤ section10Msigma M := by
    simpa [← hred.2.1] using hP_le_MF
  have hCenter_eq :
      centerIn (section15PCoreIn p MF) = section14KStar M K :=
    section15_theorem15_7_P1_center_pCore_eq_kstar_of_omega_eq
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (K := K) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hK hKstar_le hOmega_eq
  have hRank_le :
      groupRank (section15PCoreIn p MF) ≤ 2 :=
    section15_theorem15_7_P1_pCore_rank_le_two_of_center_eq_kstar
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (K := K) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hK hKstar_le hCenter_eq hKcard_not_dvd
  have hPcardExp :
      Nat.card (section15PCoreIn p MF) = p.val ^ 3 ∧
        Monoid.exponent (section15PCoreIn p MF) = p.val :=
    section15_theorem15_7_P1_pCore_card_exponent_of_rank_le_two_center_eq_kstar
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (K := K) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hK hKstar_le hOmega_eq hCenter_eq hRank_le
  have hPexp : Monoid.exponent P = p.val := by
    simpa [P] using hPcardExp.2
  have hPp : IsPGroup p.val P := by
    simpa [P] using section15_pCoreIn_isPGroup p MF
  letI : Fact (IsPGroup p.val P) := ⟨hPp⟩
  have hPextra : IsExtraspecial p.val P := by
    exact
      isExtraspecial_of_noncommutative_card_p3_exponent_p
        (K := P) (p := p.val) (by simpa [P] using hpCore_card)
        hPexp (by simpa [P] using hpNoncomm)
  letI : IsExtraspecial p.val P := hPextra
  have hK_norm_MF : K ≤ Subgroup.normalizer (MF : Set G) := by
    rcases hMF.1 with ⟨hMFleM, hMFnormM, _hMFnil, _hMFHall⟩
    have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormM
    exact hK.1.trans hM_norm_MF
  have hK_norm_P : K ≤ Subgroup.normalizer (P : Set G) := by
    have hPchar : (pCore p.val MF).Characteristic :=
      section15_pCore_characteristic (R := MF) (p := p.val)
    letI : (pCore p.val MF).Characteristic := hPchar
    have hnorm :
        Subgroup.normalizer (MF : Set G) ≤ Subgroup.normalizer (P : Set G) := by
      simpa [P, section15PCoreIn] using
        section15_normalizer_le_normalizer_map_subtype_of_characteristic
          (G := G) MF (pCore p.val MF)
    exact hK_norm_MF.trans hnorm
  haveI : Subgroup.Normalizes K P := ⟨hK_norm_P⟩
  let φ : K →* MulAut P := MulDistribMulAction.toMulAut K P
  have hprime : section14ActsInPrimeManner K (section10Msigma M) := by
    rcases proposition_14_2_a (G := G) (M := M) (K := K) hP1.1 hK with
      ⟨U, hU⟩
    exact hU.1
  have hKcyc : IsCyclic K := by
    have hZcyc : IsCyclic (section14Z M K) :=
      (theorem_14_7_d (G := G) (M := M) (K := K) hP1.1 hK).2.1
    letI : IsCyclic (section14Z M K) := hZcyc
    exact Subgroup.isCyclic_of_le (show K ≤ section14Z M K by
      change K ≤ K ⊔ section14KStar M K
      exact le_sup_left)
  have hK_coprime_p : Nat.Coprime (Nat.card K) p.val := by
    have hp_not_dvd_K : ¬ p.val ∣ Nat.card K := by
      intro hp_dvd_K
      have hpκ : p ∈ section14KappaPrimes M := by
        have hKsub_card : Nat.card (K.subgroupOf M) = Nat.card K :=
          section12_card_subgroupOf_eq hK.1
        exact hK.2.p_in_pi_of_p_dvd_card p (by
          simpa [hKsub_card] using hp_dvd_K)
      have hp_not_κ : p ∉ section14KappaPrimes M := by
        rw [hP1.2]
        intro hpκ'
        exact hpκ'.2 hpσβ.1
      exact hp_not_κ hpκ
    exact ((p.property.coprime_iff_not_dvd).2 hp_not_dvd_K).symm
  have hcentralizer :
      ∀ x : K, x ≠ 1 → {y : P | φ x y = y} = Subgroup.center P := by
    intro x hx
    have hxGne : (x : G) ≠ 1 := by
      intro hxG
      exact hx (Subtype.ext hxG)
    have hcent_x :
        elementCentralizerIn (section10Msigma M) (x : G) = section14KStar M K := by
      simpa using
        section15_elementCentralizerIn_eq_kstar_of_prime_manner
          (G := G) (M := M) (K := K) hprime x.property hxGne
    ext y
    constructor
    · intro hy
      have hycent : (y : G) ∈ elementCentralizerIn (section10Msigma M) (x : G) := by
        refine ⟨hP_le_msigma y.property, ?_⟩
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have hyconj : (x : G) * (y : G) * (x : G)⁻¹ = y := by
          simpa [φ, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hK_norm_P]
            using congrArg Subtype.val hy
        have hmul := congrArg (fun t : G => t * (x : G)) hyconj
        simpa [mul_assoc] using hmul.symm
      have hycenterIn : (y : G) ∈ centerIn P := by
        simpa [P, hCenter_eq, hcent_x] using hycent
      have hycenterMap : (y : G) ∈ (Subgroup.center P).map P.subtype := by
        simpa [centerIn_eq_map_center_local] using hycenterIn
      rcases hycenterMap with ⟨z, hz, hz_eq⟩
      have hzy : z = y := P.subtype_injective hz_eq
      simpa [hzy] using hz
    · intro hy
      apply Subtype.ext
      have hycenterIn : (y : G) ∈ centerIn P := by
        rw [centerIn_eq_map_center_local]
        exact ⟨y, hy, rfl⟩
      have hycent : (y : G) ∈ elementCentralizerIn (section10Msigma M) (x : G) := by
        simpa [P, hCenter_eq, hcent_x] using hycenterIn
      have hmul : (y : G) * (x : G) = (x : G) * (y : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hycent.2
      have hyconj : (x : G) * (y : G) * (x : G)⁻¹ = y := by
        calc
          (x : G) * (y : G) * (x : G)⁻¹ = ((y : G) * (x : G)) * (x : G)⁻¹ := by
            rw [hmul.symm]
          _ = y := by simp [mul_assoc]
      simpa [φ, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hK_norm_P] using hyconj
  haveI : IsCyclic K := hKcyc
  have hcard_shape : Nat.card P = p.val ^ (2 * 1 + 1) := by
    simpa [P] using hpCore_card
  have h25 :
      (Nat.card K ∣ p.val ^ 1 + 1) ∨
        (Nat.card K ∣ p.val ^ 1 - 1) :=
    theorem_2_5_a (p := p.val) (n := 1) (P := P)
      hcard_shape (h := Nat.card K) (H := K) rfl hK_coprime_p
      (φ := φ) hcentralizer
  rcases h25 with hplus | hminus
  · simpa [pow_one] using hplus
  · exact False.elim (hKcard_not_dvd (by simpa [pow_one] using hminus))

private theorem CFSG.section15_theorem15_7_P1_quotient_card_dvd_of_kstar_route
    {M MF X E E₁₂ E₁ E₂ E₃ K : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hpX : p.val = Nat.card X)
    (hpσβ : p ∈ section10SigmaPrimes M \ section10BetaPrimes M)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF))
    (hpPrimeCyclic : IsCyclic (section10PPrimeCore p MF))
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKstar_le : section14KStar M K ≤ section15PCoreIn p MF)
    (hOmega_eq : section10OmegaOneCenter p (section15PCoreIn p MF) = section14KStar M K)
    (hKcard_not_dvd : ¬ Nat.card K ∣ p.val - 1)
    (hpCore_card : Nat.card (section15PCoreIn p MF) = p.val ^ 3) :
    section15QuotientCardDvd MF M (p.val + 1) := by
  classical
  rcases hMF.1 with ⟨hMFleM, hMFnormM, _hMFnil, _hMFHall⟩
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  have hσD : section10Msigma M = ambientDerivedSubgroup M :=
    section15_msigma_eq_ambientDerived_of_familyP1 hM hP1 hK
  have hD_eq_MF : ambientDerivedSubgroup M = MF := by
    rw [← hσD, ← hred.2.1]
  have hcompMFK : section12ComplementIn M MF K := by
    rcases theorem_14_7_h (G := G) (M := M) (K := K) hP1.1 hK with
      ⟨hKM, hDM, hsup, hdisj⟩
    have hsup' : M = K ⊔ MF := by simpa [hD_eq_MF] using hsup
    refine ⟨hMFleM, hKM, ?_, ?_⟩
    · simpa [sup_comm] using hsup'
    · simpa [hD_eq_MF] using hdisj.symm
  have hMFnorm : section10NormalIn MF M := ⟨hMFleM, hMFnormM⟩
  have hKcard_dvd : Nat.card K ∣ p.val + 1 :=
    section15_theorem15_7_P1_kappa_card_dvd_p_add_one_of_kstar_route
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (K := K) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hK hKstar_le hOmega_eq hKcard_not_dvd hpCore_card
  exact
    section15QuotientCardDvd_of_complement_card_dvd
      (G := G) (H := MF) (M := M) (U := K)
      hcompMFK hMFnorm hKcard_dvd

private theorem CFSG.section15_theorem15_7_P1_exceptional_of_not_exponent_divisibility
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hsetup :
      ∃ p : Nat.Primes,
        p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
          ¬ IsMulCommutative (section15PCoreIn p MF) ∧
            IsCyclic (section10PPrimeCore p MF))
    (hnotExp :
      ¬ ∃ p : Nat.Primes,
        p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
          ¬ IsMulCommutative (section15PCoreIn p MF) ∧
            IsCyclic (section10PPrimeCore p MF) ∧
              ∀ q : Nat.Primes, q ∈ subgroupPrimeSet MF →
                section15QuotientExponentDvd MF M (q.val - 1)) :
    ∃ p : Nat.Primes,
      p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
        IsCyclic (section10PPrimeCore p MF) ∧
          Nat.card (section15PCoreIn p MF) = p.val ^ 3 ∧
            ¬ IsMulCommutative (section15PCoreIn p MF) ∧
              M ∈ section14MFamilyP1 G ∧
                section15QuotientCardDvd MF M (p.val + 1) := by
  rcases hsetup with ⟨p, hpX, hpσβ, hpNoncomm, hpPrimeCyclic⟩
  rcases
    section15_theorem15_7_P1_kstar_route_of_not_exponent_divisibility
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hnotExp with
    ⟨K, hK, hKstar_le, hOmega_eq, hKcard_not_dvd⟩
  have hpCore_card :
      Nat.card (section15PCoreIn p MF) = p.val ^ 3 :=
    section15_theorem15_7_P1_pCore_card_of_kstar_route
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (K := K) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hK hKstar_le hOmega_eq hKcard_not_dvd
  have hquot :
      section15QuotientCardDvd MF M (p.val + 1) :=
    section15_theorem15_7_P1_quotient_card_dvd_of_kstar_route
      (G := G) (M := M) (MF := MF) (X := X) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (K := K) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hpX hpσβ
      hpNoncomm hpPrimeCyclic hK hKstar_le hOmega_eq hKcard_not_dvd hpCore_card
  exact ⟨p, hpX, hpσβ, hpPrimeCyclic, hpCore_card, hpNoncomm, hP1, hquot⟩

/-- The type `𝓟₁` endpoint of Theorem 15.7(e): from the common nonabelian
setup, either the exponent-divisibility alternative already holds or the
`K*` route gives the exceptional cardinality alternative. -/
private theorem CFSG.section15_theorem15_7_P1_alternative_of_nonabelian_setup
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hsetup :
      ∃ p : Nat.Primes,
        p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
          ¬ IsMulCommutative (section15PCoreIn p MF) ∧
            IsCyclic (section10PPrimeCore p MF)) :
    (∃ p : Nat.Primes,
      p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
        ¬ IsMulCommutative (section15PCoreIn p MF) ∧
          IsCyclic (section10PPrimeCore p MF) ∧
            ∀ q : Nat.Primes, q ∈ subgroupPrimeSet MF →
              section15QuotientExponentDvd MF M (q.val - 1)) ∨
      ∃ p : Nat.Primes,
        p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
          IsCyclic (section10PPrimeCore p MF) ∧
            Nat.card (section15PCoreIn p MF) = p.val ^ 3 ∧
              ¬ IsMulCommutative (section15PCoreIn p MF) ∧
                M ∈ section14MFamilyP1 G ∧
                  section15QuotientCardDvd MF M (p.val + 1) := by
  classical
  by_cases hAlt2 :
      ∃ p : Nat.Primes,
        p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
          ¬ IsMulCommutative (section15PCoreIn p MF) ∧
            IsCyclic (section10PPrimeCore p MF) ∧
              ∀ q : Nat.Primes, q ∈ subgroupPrimeSet MF →
                section15QuotientExponentDvd MF M (q.val - 1)
  · exact Or.inl hAlt2
  · exact Or.inr
      (section15_theorem15_7_P1_exceptional_of_not_exponent_divisibility
        hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1 hsetup hAlt2)

/-- Theorem 15.7(e), type `𝓕` branch: once `M_F` is nonabelian, the
source setup and Lemma 15.1(e) give the second alternative. -/
private theorem CFSG.section15_theorem15_7_F_alternative
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hF : M ∈ section14MFamilyF G) :
    ∃ p : Nat.Primes,
      p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
        ¬ IsMulCommutative (section15PCoreIn p MF) ∧
          IsCyclic (section10PPrimeCore p MF) ∧
            ∀ q : Nat.Primes, q ∈ subgroupPrimeSet MF →
              section15QuotientExponentDvd MF M (q.val - 1) := by
  rcases section15_theorem15_7_nonabelian_setup
      hM hMF hnotTI hg hX hXne hE hMFnoncomm with
    ⟨p, hpX, hpσβ, hpNoncomm, hpPrimeCyclic⟩
  exact ⟨p, hpX, hpσβ, hpNoncomm, hpPrimeCyclic,
    section15_theorem15_7_F_exponent_divisibility
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hF
      hpX hpσβ hpNoncomm hpPrimeCyclic⟩

/-- Theorem 15.7(e), type `𝓟₁` branch: the same nonabelian setup gives
either the second alternative or the exceptional third alternative. -/
private theorem CFSG.section15_theorem15_7_P1_alternative
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hP1 : M ∈ section14MFamilyP1 G) :
    (∃ p : Nat.Primes,
      p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
        ¬ IsMulCommutative (section15PCoreIn p MF) ∧
          IsCyclic (section10PPrimeCore p MF) ∧
            ∀ q : Nat.Primes, q ∈ subgroupPrimeSet MF →
              section15QuotientExponentDvd MF M (q.val - 1)) ∨
      ∃ p : Nat.Primes,
        p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
          IsCyclic (section10PPrimeCore p MF) ∧
            Nat.card (section15PCoreIn p MF) = p.val ^ 3 ∧
              ¬ IsMulCommutative (section15PCoreIn p MF) ∧
                M ∈ section14MFamilyP1 G ∧
                  section15QuotientCardDvd MF M (p.val + 1) := by
  exact
    section15_theorem15_7_P1_alternative_of_nonabelian_setup
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hP1
      (section15_theorem15_7_nonabelian_setup
        hM hMF hnotTI hg hX hXne hE hMFnoncomm)

/-- Theorem 15.7(e): the final abelian/nonabelian and `𝓜_F`/`𝓜_{P₁}`
case analysis gives one of the three alternatives. -/
private theorem CFSG.section15_theorem15_7_alternatives
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    section15Theorem15_7Alternatives M MF X := by
  by_cases hMFcomm : IsMulCommutative MF
  · exact Or.inl
      (section15_theorem15_7_abelian_alternative
        hM hMF hnotTI hg hX hXne hE hMFcomm)
  · have hred := section15_theorem15_7_initial_reduction
      hM hMF hnotTI hg hX hXne hE
    rcases hred.1 with hF | hP1
    · exact Or.inr (Or.inl
        (section15_theorem15_7_F_alternative
          hM hMF hnotTI hg hX hXne hE hMFcomm hF))
    · rcases section15_theorem15_7_P1_alternative
        hM hMF hnotTI hg hX hXne hE hMFcomm hP1 with hAlt2 | hAlt3
      · exact Or.inr (Or.inl hAlt2)
      · exact Or.inr (Or.inr hAlt3)

/-- Theorem 15.7(a): if `F(M)` is not TI and
`X = F(M) ∩ F(M)^g ≠ 1`, then `M ∈ 𝓜_F ∪ 𝓜_{P₁}` and
`M_F = M_σ`. -/
public theorem CFSG.theorem_15_7_a
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    M ∈ section14MFamilyF G ∪ section14MFamilyP1 G ∧
      MF = section10Msigma M := by
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  exact ⟨hred.1, hred.2.1⟩

/-- Theorem 15.7 support: in the same situation, `M_σ` is a
`β(M)'`-subgroup. -/
public theorem CFSG.theorem_15_7_msigma_beta_compl
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    IsPiSubgroup (section10BetaPrimes M)ᶜ (section10Msigma M) := by
  exact section15_theorem15_7_msigma_beta_compl
    hM hMF hnotTI hg hX hXne hE

/-- Theorem 15.7(b): in the same situation, `X ≤ M_F` and `X` is
cyclic. -/
public theorem CFSG.theorem_15_7_b
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    X ≤ MF ∧ IsCyclic X := by
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  exact hred.2.2

/-- Source-prime support from Theorem 15.7: in the nonabelian branch with
`p = |X|`, the source subgroup `X` has prime order and the `p`-core of
`M_F` has the prime-order centralizer split used in the definition of
`π*` in Section 16. -/
public theorem CFSG.theorem_15_7_source_prime_centralizer_split
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMFnoncomm : ¬ IsMulCommutative MF)
    (hpX : p.val = Nat.card X) :
    ∃ Z : Subgroup G,
      X ≤ section15PCoreIn p MF ∧ Nat.card X = p.val ∧
        Z ≤ section15PCoreIn p MF ∧ IsCyclic Z ∧
          subgroupCentralizerIn (section15PCoreIn p MF) X = X ⊔ Z ∧
            section12InternalDirectProduct X Z
              (subgroupCentralizerIn (section15PCoreIn p MF) X) := by
  classical
  have hXprime : X ∈ section10PrimeOrderSubgroupsIn p X := ⟨le_rfl, hpX.symm⟩
  obtain ⟨hXeq, Z, hZcyc, hdisjXZ, hCPsplit⟩ :=
    section15_theorem15_7_X_eq_primeOrder_and_centralizer_split_of_nonabelian_MF
      (G := G) (M := M) (MF := MF) (X := X) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (X₁ := X) (g := g) (p := p)
      hM hMF hnotTI hg hX hXne hE hMFnoncomm hXprime
  have hred := section15_theorem15_7_initial_reduction
    hM hMF hnotTI hg hX hXne hE
  rcases hMF.1 with ⟨_hMFleM, _hMFnormM, hMFnil, _hMFHall⟩
  have hXleMF : X ≤ MF := hred.2.2.1
  have hXp : IsPGroup p.val X :=
    section15_isPGroup_of_prime_card (G := G) (A := X) (q := p) hpX
  have hXleP : X ≤ section15PCoreIn p MF :=
    section15_pSubgroup_le_pCoreIn_of_nilpotent
      (G := G) (H := MF) (X := X) (p := p) hMFnil hXleMF hXp
  let P : Subgroup G := section15PCoreIn p MF
  let Z₀ : Subgroup G := section10OmegaOneCenter p P
  let B : Subgroup G := X ⊔ Z₀
  have hZleCP : Z ≤ subgroupCentralizerIn P B := by
    intro z hz
    rw [hCPsplit]
    exact (show Z ≤ X ⊔ Z from le_sup_right) hz
  have hZleP : Z ≤ P := by
    intro z hz
    exact (hZleCP hz).1
  have hZleCentX : Z ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    exact Subgroup.mem_centralizer_iff.mp (hZleCP hz).2 x
      ((show X ≤ B from by simp [B]) hxX)
  have hZleCentralizerX : Z ≤ subgroupCentralizerIn P X := by
    intro z hz
    exact ⟨hZleP hz, hZleCentX hz⟩
  have hXleCentralizerX : X ≤ subgroupCentralizerIn P X := by
    intro x hx
    refine ⟨by simpa [P] using hXleP hx, ?_⟩
    change x ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    haveI : Fact p.val.Prime := ⟨p.property⟩
    letI : IsCyclic X := isCyclic_of_prime_card (p := p.val) hpX.symm
    letI : CommGroup X := IsCyclic.commGroup
    exact setLike_mul_comm (s := X) hy hx
  have hcentralizer_le_sup : subgroupCentralizerIn P X ≤ X ⊔ Z := by
    intro y hy
    have hyB : y ∈ subgroupCentralizerIn P B := by
      refine ⟨hy.1, ?_⟩
      change y ∈ Subgroup.centralizer (B : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hB_le_cent_y : B ≤ Subgroup.centralizer ({y} : Set G) := by
        refine sup_le ?_ ?_
        · intro x hxX
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          have hz_eq : z = y := by simpa using hz
          subst z
          exact (Subgroup.mem_centralizer_iff.mp hy.2 x hxX).symm
        · intro z hzZ₀
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          have hw_eq : w = y := by simpa using hw
          subst w
          have hz_cent_P : z ∈ Subgroup.centralizer (P : Set G) := by
            simpa [Z₀, P] using
              section15_omegaOneCenter_le_centralizer (G := G) (p := p) P hzZ₀
          exact Subgroup.mem_centralizer_iff.mp hz_cent_P y hy.1
      exact (Subgroup.mem_centralizer_iff.mp (hB_le_cent_y (by simpa [B] using hb)) y
        (by simp)).symm
    rw [hCPsplit] at hyB
    exact hyB
  have hcentralizer_eq : subgroupCentralizerIn P X = X ⊔ Z :=
    le_antisymm hcentralizer_le_sup (sup_le hXleCentralizerX hZleCentralizerX)
  have hXleCentZ : X ≤ Subgroup.centralizer (Z : Set G) := by
    intro x hxX
    rw [Subgroup.mem_centralizer_iff]
    intro z hzZ
    exact (Subgroup.mem_centralizer_iff.mp (hZleCentX hzZ) x hxX).symm
  refine ⟨Z, hXleP, hpX.symm, hZleP, hZcyc, hcentralizer_eq, ?_⟩
  exact ⟨hXleCentralizerX, hZleCentralizerX, hcentralizer_eq, hdisjXZ, hXleCentZ⟩

omit [IsMinCE G] in
/-- A prime different from `p` has its `p`-core inside the `p'`-core. -/
public theorem CFSG.theorem_15_7_pCoreIn_le_pPrimeCore_of_ne
    {H : Subgroup G} {p q : Nat.Primes} (hqp : q ≠ p) :
    section15PCoreIn q H ≤ section10PPrimeCore p H :=
  section15_pCoreIn_le_pPrimeCore_of_ne (G := G) hqp

/-- When `M_F = M_σ`, the source `p`-core is an ambient Sylow subgroup. -/
public theorem CFSG.theorem_15_7_pCoreIn_global_sylow_of_msigma
    {M MF : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hMF_eq_msigma : MF = section10Msigma M)
    (hpσ : p ∈ section10SigmaPrimes M) :
    ∃ S : Sylow p.val G, (S : Subgroup G) = section15PCoreIn p MF :=
  section15_theorem15_7_P1_pCore_global_sylow_of_msigma
    (G := G) hM hMF hMF_eq_msigma hpσ


/-- Theorem 15.7(d): in the same situation, `E₃ = 1`, `E₂ ⊲ E`,
and `E/E₂ ≅ E₁`, with `E₁` cyclic. -/
public theorem CFSG.theorem_15_7_d
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    E₃ = ⊥ ∧ section10NormalIn E₂ E ∧
      section15QuotientMulEquiv E E₂ E₁ ∧ IsCyclic E₁ := by
  exact section15_theorem15_7_d_conclusions
    hM hMF hnotTI hg hX hXne hE

/-- Theorem 15.7(e): in the same situation, one of the three listed
alternatives holds. -/
public theorem CFSG.theorem_15_7_e
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    section15Theorem15_7Alternatives M MF X := by
  exact section15_theorem15_7_alternatives
    hM hMF hnotTI hg hX hXne hE

end Section15

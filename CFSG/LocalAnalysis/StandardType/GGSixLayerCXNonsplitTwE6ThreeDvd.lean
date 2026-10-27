module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Gen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.Layers
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Arith
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularOdd
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.PartOne.KE.E6TwFourFinal
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three

namespace TwE6Nonsplit


theorem dvd_card_of_isComponentOf_twE6_of_phiThree
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 3).eval ((2 ^ f : ℕ) : ℤ))
    {a : twistedE6RootGroup K σ} (ha : orderOf a = p)
    {X : Subgroup (twistedE6RootGroup K σ)}
    (hX : IsComponentOf X (Subgroup.centralizer ({a} : Set (twistedE6RootGroup K σ)))) :
    p ∣ Nat.card X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpq : p ∣ (2 ^ f) ^ 2 + 2 ^ f + 1 := E6Nonsplit.dvd_phiThree_nat hpf
  let Ω := AlgebraicClosure K
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := inferInstance
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 f
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  obtain ⟨g, hg, hgn⟩ := exists_inv_mul_twistE6_eq (ℓ := 2) (f := f) hf hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω phi3V)
  obtain ⟨c₀, hc₀⟩ := CFSG.RankThree.PartOne.KETw3.exists_conj_into_TStar (ℓ := 2) (f := f)
    Nat.prime_two hf hK hσ hFr hp hp3 hpq hg hgn (Subgroup.zpowers a)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one]))
  have hT : frameEmb K σ Ω g c₀ a ∈ phi3TStar K σ.toRingHom Ω Fr g := by
    rw [frameEmb_apply]
    exact hc₀ a (Subgroup.mem_zpowers a)
  have hy : orderOf (frameEmb K σ Ω g c₀ a) = p := by
    rw [orderOf_frameEmb]
    exact ha
  let ψ : twistedE6RootGroup K σ →* ModGL Tag.E6 Ω := frameEmb K σ Ω g c₀
  let y : ModGL Tag.E6 Ω := frameEmb K σ Ω g c₀ a
  let A : Subgroup (twistedE6RootGroup K σ) :=
    Subgroup.centralizer ({a} : Set (twistedE6RootGroup K σ))
  let D : Subgroup (ModGL Tag.E6 Ω) :=
    phi3CStar K σ.toRingHom Ω g ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.E6 Ω))
  have hψ : Function.Injective ψ := frameEmb_injective c₀
  have hDmap : A.map ψ = D := map_centralizer_frameEmb c₀ a
  let ψA : A →* ModGL Tag.E6 Ω := ψ.comp A.subtype
  have hψA : Function.Injective ψA := hψ.comp A.subtype_injective
  have hrange : ψA.range = D := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hDmap
  obtain ⟨-, hcent, -⟩ :=
    twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
      (σ := σ.toRingHom) (K := K) (Ω := Ω) (Fr := Fr) (g := g) (ℓ := 2) (f := f)
      Nat.prime_two hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨htri, hreg, hA2, hA2A2, -⟩ := hcent y hT hy
  have finish : ∀ {ι : Type} (P : ι → Subgroup (ModGL Tag.E6 Ω)),
      (∀ i, P i ≤ D) → (∀ i, CFSG.IsQuasisimple (P i)) →
      (∀ i, ((P i).subgroupOf D).Normal) →
      (∀ d : A, (∀ i, ∀ u ∈ P i, ψA d * u = u * ψA d) →
        (ψA d : ModGL Tag.E6 Ω) ∈ phi3Torus Ω Fr) →
      (∀ i, p ∣ Nat.card (P i)) → p ∣ Nat.card X := by
    intro ι P hPD hPq hPn hcentP hPdvd
    refine E6Nonsplit.dvd_card_of_isComponentOf_of_layers ψA hψA P ?_ hPq ?_
      (Z := (phi3Torus Ω Fr : Set (ModGL Tag.E6 Ω))) ?_ hcentP hPdvd hX
    · intro i
      rw [hrange]
      exact hPD i
    · intro i d u hu
      have hdD : (ψA d : ModGL Tag.E6 Ω) ∈ D := by
        rw [← hrange]
        exact ⟨d, rfl⟩
      have h := (hPn i).conj_mem ⟨u, hPD i hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
        ⟨ψA d, hdD⟩
      simpa using (Subgroup.mem_subgroupOf.mp h)
    · intro x hx x' hx'
      exact torusGroup_E6_comm (x := x) (y := x') hx.1 hx'.1
  rcases htri with h0 | h1 | h2
  ·
    have hDle : D ≤ phi3Torus Ω Fr := (hreg h0).2
    refine finish (fun e : Empty => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun d _ => ?_) (fun e => e.elim)
    exact hDle (by rw [← hrange]; exact ⟨d, rfl⟩)
  ·
    obtain ⟨-, hPQ, hDD, -, hPq, -, hPC, -, hPcent⟩ := hA2 h1
    have hPleD : phi3Layer Fr y ≤ D := by
      rw [show phi3Layer Fr y = ⁅D, D⁆ from hPQ.trans hDD.symm]
      exact CFSG.RankThree.Classical2.commutator_le_self' D
    have hPn : ((phi3Layer Fr y).subgroupOf D).Normal := by
      rw [show phi3Layer Fr y = ⁅D, D⁆ from hPQ.trans hDD.symm]
      exact CFSG.RankThree.Classical2.commutator_subgroupOf_normal D
    obtain ⟨R, hRmem, -, -, -, hRp⟩ := layerA2 (ℓ := 2) (f := f) (K := K) (σ := σ)
      (Ω := Ω) (Fr := Fr) (g := g) Nat.prime_two hf hK (fun c => hσ c) hFr hp hp3 hpq hg
      hgn c₀ a hT hy h1
    have hPdvd : p ∣ Nat.card (phi3Layer Fr y) := by
      have hPleC : phi3Layer Fr y ≤ ψ.range := by
        rw [show ψ.range = phi3CStar K σ.toRingHom Ω g from range_frameEmb c₀]
        exact hPC
      have hRcomap : R = (phi3Layer Fr y).comap ψ := by
        ext u
        exact hRmem u
      have hRmap : R.map ψ = phi3Layer Fr y := by
        rw [hRcomap, Subgroup.map_comap_eq_self hPleC]
      rw [← hRmap, Subgroup.card_map_of_injective hψ]
      exact (Nat.Prime.dvd_iff_not_coprime hp).mpr hRp
    refine finish (fun _ : Unit => phi3Layer Fr y) (fun _ => hPleD) (fun _ => hPq)
      (fun _ => hPn) (fun d hd => hPcent ?_) (fun _ => hPdvd)
    have hdD : (ψA d : ModGL Tag.E6 Ω) ∈ D := by
      rw [← hrange]
      exact ⟨d, rfl⟩
    exact ⟨hdD, Subgroup.mem_centralizer_iff.2 fun u hu => (hd () u hu).symm⟩
  ·
    obtain ⟨-, -, -, -, -, hPq, hPC, hres, -, hPcent⟩ := hA2A2 h2
    have hPleD : phi3Layer Fr y ≤ D := by
      rw [show phi3Layer Fr y = (CFSG.perfectResidual ↥D).map D.subtype from hres.symm]
      exact CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.map_perfectResidual_le_self D
    have hPn : ((phi3Layer Fr y).subgroupOf D).Normal := by
      rw [show phi3Layer Fr y = (CFSG.perfectResidual ↥D).map D.subtype from hres.symm]
      exact CFSG.RankThree.Classical2.map_perfectResidual_subgroupOf_normal D
    obtain ⟨R, hRmem, -, -, -, hRp⟩ := layerA2A2 (ℓ := 2) (f := f) (K := K) (σ := σ)
      (Ω := Ω) (Fr := Fr) (g := g) Nat.prime_two hf hK (fun c => hσ c) hFr hp hp3 hpq hg
      hgn c₀ a hT hy h2
    have hPdvd : p ∣ Nat.card (phi3Layer Fr y) := by
      have hPleC : phi3Layer Fr y ≤ ψ.range := by
        rw [show ψ.range = phi3CStar K σ.toRingHom Ω g from range_frameEmb c₀]
        exact hPC
      have hRcomap : R = (phi3Layer Fr y).comap ψ := by
        ext u
        exact hRmem u
      have hRmap : R.map ψ = phi3Layer Fr y := by
        rw [hRcomap, Subgroup.map_comap_eq_self hPleC]
      rw [← hRmap, Subgroup.card_map_of_injective hψ]
      exact (Nat.Prime.dvd_iff_not_coprime hp).mpr hRp
    refine finish (fun _ : Unit => phi3Layer Fr y) (fun _ => hPleD) (fun _ => hPq)
      (fun _ => hPn) (fun d hd => hPcent ?_) (fun _ => hPdvd)
    have hdD : (ψA d : ModGL Tag.E6 Ω) ∈ D := by
      rw [← hrange]
      exact ⟨d, rfl⟩
    exact ⟨hdD, Subgroup.mem_centralizer_iff.2 fun u hu => (hd () u hu).symm⟩

end TwE6Nonsplit

end CFSG.StandardType

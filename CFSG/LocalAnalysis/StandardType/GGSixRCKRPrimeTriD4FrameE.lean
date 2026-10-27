module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4FrameDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcTwD4Layer
public import CFSG.RankThree.PartOne.KD4L.TriNu
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityConjugacy
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.LieType.Ree.Endo
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Steinberg.TwistedD4 (nd)



theorem rckTriD4_exists_conj_twistedFixed_eq {τ : Tag} [E6Sub τ] {L : Type} [Field L]
    [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ)
    (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Set τ))
    (hact : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ)) :
    ∃ n₁ k : ModGL τ L, k ∈ subsystemGroup τ L (d4Set τ) ∧
      (∀ j ∈ d4Set τ, ∀ c : L,
        n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
        n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) ∧
      ∀ g : ModGL τ L,
        k * (n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹) * k⁻¹ =
          n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (k * g * k⁻¹) * n₁⁻¹ := by
  obtain ⟨q, n₁, hq, -, hnq, hgen⟩ := exists_normalized hn hπ hπ' hu hact
  have hA : n₁ ∈ Subgroup.normalizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L)) :=
    mem_normalizer_subsystemGroup_of_conj hπ hπ' hgen
  obtain ⟨k, hk, hlang⟩ :=
    ((supported_native_affine_realization_and_Lang τ L (d4Set τ)).2 ℓ f hf n₁ hA).2.2.2 q hq
  refine ⟨n₁, k, hk, hgen, fun g => ?_⟩
  have e1 : n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ =
      q * frobTwistGL τ L ℓ f n₁ g * q⁻¹ := by
    rw [hnq, frobTwistGL_apply]
    group
  rw [e1, hlang g, frobTwistGL_apply]
  group

theorem rckTriD4_exists_conj_twistedFixed_twist_eq {L : Type} [Field L] [IsAlgClosed L]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {π : Equiv.Perm (Fin TwistTag.E6.tag.rank)}
    (hπ : ∀ i ∈ d4Set TwistTag.E6.tag, π i ∈ d4Set TwistTag.E6.tag)
    (hπ' : ∀ i ∈ d4Set TwistTag.E6.tag, π.symm i ∈ d4Set TwistTag.E6.tag)
    {u : WeylGroup TwistTag.E6.tag}
    (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Set TwistTag.E6.tag))
    (hact : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (π j) 1 : Fin TwistTag.E6.tag.rank → ℤ)) :
    ∃ n₁ k : ModGL TwistTag.E6.tag L, k ∈ subsystemGroup TwistTag.E6.tag L
      (d4Set TwistTag.E6.tag) ∧
      (∀ j ∈ d4Set TwistTag.E6.tag, ∀ c : L,
        n₁ * xUnit TwistTag.E6.tag L j c * n₁⁻¹ = xUnit TwistTag.E6.tag L (π j) c ∧
        n₁ * yUnit TwistTag.E6.tag L j c * n₁⁻¹ = yUnit TwistTag.E6.tag L (π j) c) ∧
      ∀ g : ModGL TwistTag.E6.tag L,
        k * ((n * diagramMap TwistTag.E6 L) *
            Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g *
            (n * diagramMap TwistTag.E6 L)⁻¹) * k⁻¹ =
          n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (k * g * k⁻¹) * n₁⁻¹ := by
  obtain ⟨q, n₁, hq, hnq, hgen⟩ := exists_normalized_twist hn hπ hπ' hu hact
  have hA : n₁ ∈ Subgroup.normalizer (subsystemGroup TwistTag.E6.tag L
      (d4Set TwistTag.E6.tag) : Set (ModGL TwistTag.E6.tag L)) :=
    mem_normalizer_subsystemGroup_of_conj hπ hπ' hgen
  obtain ⟨k, hk, hlang⟩ :=
    ((supported_native_affine_realization_and_Lang TwistTag.E6.tag L
      (d4Set TwistTag.E6.tag)).2 ℓ f hf n₁ hA).2.2.2 q hq
  refine ⟨n₁, k, hk, hgen, fun g => ?_⟩
  have e1 : (n * diagramMap TwistTag.E6 L) *
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g *
      (n * diagramMap TwistTag.E6 L)⁻¹ =
        q * frobTwistGL TwistTag.E6.tag L ℓ f n₁ g * q⁻¹ := by
    rw [hnq, frobTwistGL_apply]
    group
  rw [e1, hlang g, frobTwistGL_apply]
  group

theorem rckTriD4_d4NativeEquiv {τ : Tag} [E6Sub τ] {L : Type} [Field L] [CharP L 2] :
    ∃ ε : ↥(adjointGroup Tag.D4 L) ≃* ↥(subsystemGroup τ L (d4Set τ)),
      (∀ (k : Fin Tag.D4.rank) (c : L),
        (ε ⟨xUnit Tag.D4 L k c, xUnit_mem_adjointGroup k c⟩ : ModGL τ L) =
          xUnit τ L (d4Id k) c) ∧
      (∀ (k : Fin Tag.D4.rank) (c : L),
        (ε ⟨yUnit Tag.D4 L k c, yUnit_mem_adjointGroup k c⟩ : ModGL τ L) =
          yUnit τ L (d4Id k) c) := by
  have h2 : ringChar L = 2 := ringChar.eq L 2
  let d4ResCod : ↥(subsystemGroup Tag.E6 L d4Support) →* ↥(adjointGroup Tag.D4 L) :=
    (d4Res L).codRestrict _ (fun g => d4Res_mem_adjointGroup g)
  have hinj : Function.Injective d4ResCod := by
    intro x y hxy
    exact d4Res_injective_of_ringChar_eq_two h2 (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective d4ResCod := by
    intro x
    have hx : (x : ModGL Tag.D4 L) ∈ (d4Res L).range := by
      rw [range_d4Res]
      exact x.2
    obtain ⟨g, hg⟩ := hx
    exact ⟨g, Subtype.ext hg⟩
  let d4ResEquiv : ↥(subsystemGroup Tag.E6 L d4Support) ≃* ↥(adjointGroup Tag.D4 L) :=
    MulEquiv.ofBijective d4ResCod ⟨hinj, hsurj⟩
  let ε : ↥(adjointGroup Tag.D4 L) ≃* ↥(subsystemGroup τ L (d4Set τ)) :=
    ((nuEquiv τ L).trans d4ResEquiv).symm
  have hd4x : ∀ (k : Fin Tag.D4.rank) (c : L),
      d4ResEquiv.symm ⟨xUnit Tag.D4 L k c, xUnit_mem_adjointGroup k c⟩ = d4QX k c := by
    intro k c
    refine d4ResEquiv.injective ?_
    rw [d4ResEquiv.apply_symm_apply]
    change ⟨xUnit Tag.D4 L k c, xUnit_mem_adjointGroup k c⟩ = d4ResCod (d4QX k c)
    apply Subtype.ext
    change xUnit Tag.D4 L k c = d4Res L (d4QX k c)
    rw [d4Res_xUnit]
  have hd4y : ∀ (k : Fin Tag.D4.rank) (c : L),
      d4ResEquiv.symm ⟨yUnit Tag.D4 L k c, yUnit_mem_adjointGroup k c⟩ = d4QY k c := by
    intro k c
    refine d4ResEquiv.injective ?_
    rw [d4ResEquiv.apply_symm_apply]
    change ⟨yUnit Tag.D4 L k c, yUnit_mem_adjointGroup k c⟩ = d4ResCod (d4QY k c)
    apply Subtype.ext
    change yUnit Tag.D4 L k c = d4Res L (d4QY k c)
    rw [d4Res_yUnit]
  have hnux : ∀ (k : Fin Tag.D4.rank) (c : L),
      (nuEquiv τ L).symm (d4QX k c) =
        ⟨xUnit τ L (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ := by
    intro k c
    refine (nuEquiv τ L).injective ?_
    rw [(nuEquiv τ L).apply_symm_apply]
    change d4QX k c = nuE τ L ⟨xUnit τ L (d4Id k) c,
      xUnit_mem_subsystemGroup (d4Id_mem k) c⟩
    rw [nuE_xUnit]
  have hnuy : ∀ (k : Fin Tag.D4.rank) (c : L),
      (nuEquiv τ L).symm (d4QY k c) =
        ⟨yUnit τ L (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ := by
    intro k c
    refine (nuEquiv τ L).injective ?_
    rw [(nuEquiv τ L).apply_symm_apply]
    change d4QY k c = nuE τ L ⟨yUnit τ L (d4Id k) c,
      yUnit_mem_subsystemGroup (d4Id_mem k) c⟩
    rw [nuE_yUnit]
  refine ⟨ε, ?_, ?_⟩
  · intro k c
    change ((nuEquiv τ L).symm (d4ResEquiv.symm
      ⟨xUnit Tag.D4 L k c, xUnit_mem_adjointGroup k c⟩) : ModGL τ L) = xUnit τ L (d4Id k) c
    rw [hd4x k c, hnux k c]
  · intro k c
    change ((nuEquiv τ L).symm (d4ResEquiv.symm
      ⟨yUnit Tag.D4 L k c, yUnit_mem_adjointGroup k c⟩) : ModGL τ L) = yUnit τ L (d4Id k) c
    rw [hd4y k c, hnuy k c]

section DiagramFrob

open CFSG.LieType.Ree

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

@[expose] noncomputable def rckTriD4_trialityMatrix : ModGL Tag.D4 L :=
  diagramMap TwistTag.D4 L

@[expose] noncomputable def rckTriD4_frobAdj (h : ℕ) :
    ↥(adjointGroup Tag.D4 L) →* ↥(adjointGroup Tag.D4 L) :=
  ((Units.map (entrywiseHom (iterateFrobenius L 2 h))).comp
    (Subgroup.subtype (adjointGroup Tag.D4 L))).codRestrict _
    (fun g => by
      haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
      simpa [entrywiseFrobGL] using
        entrywiseFrobGL_mem (p := 2) (τ := Tag.D4) (L := L) h g.2)

@[expose] noncomputable def rckTriD4_conjAdj (e : ℕ) :
    ↥(adjointGroup Tag.D4 L) ≃* ↥(adjointGroup Tag.D4 L) :=
  ((adjointGroup Tag.D4 L).equivMapOfInjective
    (MulAut.conj (rckTriD4_trialityMatrix (L := L) ^ e)).toMonoidHom
    (MulAut.conj (rckTriD4_trialityMatrix (L := L) ^ e)).injective).trans
    (MulEquiv.subgroupCongr (by
      have hpow : diagramMap TwistTag.D4 L ^ (e : ℤ) = diagramMap TwistTag.D4 L ^ e := by
        rw [zpow_natCast]
      have h := map_conj_diagramMap_zpow (t := TwistTag.D4) (L := L) (j := (e : ℤ))
      rw [hpow] at h
      change Subgroup.map (MulAut.conj (rckTriD4_trialityMatrix (L := L) ^ e)).toMonoidHom
        (adjointGroup Tag.D4 L) = adjointGroup Tag.D4 L at h
      exact h))

@[expose] noncomputable def rckTriD4_diagramFrobHom (e h : ℕ) :
    ↥(adjointGroup Tag.D4 L) →* ↥(adjointGroup Tag.D4 L) :=
  (rckTriD4_conjAdj e).toMonoidHom.comp (rckTriD4_frobAdj h)

theorem rckTriD4_frobAdj_apply (h : ℕ) (x : ↥(adjointGroup Tag.D4 L)) :
    (rckTriD4_frobAdj h x : ModGL Tag.D4 L) =
      Units.map (entrywiseHom (iterateFrobenius L 2 h)) (x : ModGL Tag.D4 L) :=
  rfl

theorem rckTriD4_conjAdj_apply (e : ℕ) (x : ↥(adjointGroup Tag.D4 L)) :
    (rckTriD4_conjAdj e x : ModGL Tag.D4 L) =
      (rckTriD4_trialityMatrix (L := L) ^ e) * (x : ModGL Tag.D4 L) *
        (rckTriD4_trialityMatrix (L := L) ^ e)⁻¹ :=
  rfl

theorem rckTriD4_diagramFrobHom_apply (e h : ℕ) (x : ↥(adjointGroup Tag.D4 L)) :
    (rckTriD4_diagramFrobHom e h x : ModGL Tag.D4 L) =
      (rckTriD4_trialityMatrix (L := L) ^ e) *
        Units.map (entrywiseHom (iterateFrobenius L 2 h)) (x : ModGL Tag.D4 L) *
        (rckTriD4_trialityMatrix (L := L) ^ e)⁻¹ := by
  simp [rckTriD4_diagramFrobHom, rckTriD4_conjAdj_apply, rckTriD4_frobAdj_apply]

theorem rckTriD4_trialityMatrix_pow_mul_xUnit (e : ℕ) (k : Fin Tag.D4.rank) (c : L) :
    rckTriD4_trialityMatrix (L := L) ^ e * xUnit Tag.D4 L k c *
        (rckTriD4_trialityMatrix (L := L) ^ e)⁻¹ =
      xUnit Tag.D4 L ((d4RhoPerm ^ e) k) c := by
  let k' : Fin TwistTag.D4.tag.rank := k
  have h := diagramMap_pow_mul_xUnit_mul_inv (t := TwistTag.D4) (K := L) e k' c
  rw [show d4RhoPerm = TwistTag.D4.perm from Equiv.ext d4RhoPerm_apply]
  change diagramMap TwistTag.D4 L ^ e * xUnit (TwistTag.D4.tag) L k' c *
      (diagramMap TwistTag.D4 L ^ e)⁻¹ =
        xUnit (TwistTag.D4.tag) L ((TwistTag.D4.perm ^ e) k') c
  exact h

theorem rckTriD4_trialityMatrix_pow_mul_yUnit (e : ℕ) (k : Fin Tag.D4.rank) (c : L) :
    rckTriD4_trialityMatrix (L := L) ^ e * yUnit Tag.D4 L k c *
        (rckTriD4_trialityMatrix (L := L) ^ e)⁻¹ =
      yUnit Tag.D4 L ((d4RhoPerm ^ e) k) c := by
  let k' : Fin TwistTag.D4.tag.rank := k
  have h := diagramMap_pow_mul_yUnit_mul_inv (t := TwistTag.D4) (K := L) e k' c
  rw [show d4RhoPerm = TwistTag.D4.perm from Equiv.ext d4RhoPerm_apply]
  change diagramMap TwistTag.D4 L ^ e * yUnit (TwistTag.D4.tag) L k' c *
      (diagramMap TwistTag.D4 L ^ e)⁻¹ =
        yUnit (TwistTag.D4.tag) L ((TwistTag.D4.perm ^ e) k') c
  exact h

theorem rckTriD4_diagramFrobHom_xElement (e h : ℕ) (k : Fin Tag.D4.rank) (c : L) :
    (rckTriD4_diagramFrobHom e h (xElement k c) : ModGL Tag.D4 L) =
      xUnit Tag.D4 L ((d4RhoPerm ^ e) k) (c ^ 2 ^ h) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [rckTriD4_diagramFrobHom_apply]
  change rckTriD4_trialityMatrix (L := L) ^ e *
      Units.map (entrywiseHom (iterateFrobenius L 2 h)) (xUnit Tag.D4 L k c) *
      (rckTriD4_trialityMatrix (L := L) ^ e)⁻¹ =
        xUnit Tag.D4 L ((d4RhoPerm ^ e) k) (c ^ 2 ^ h)
  rw [entrywise_xUnit, rckTriD4_trialityMatrix_pow_mul_xUnit]

theorem rckTriD4_diagramFrobHom_yElement (e h : ℕ) (k : Fin Tag.D4.rank) (c : L) :
    (rckTriD4_diagramFrobHom e h (yElement k c) : ModGL Tag.D4 L) =
      yUnit Tag.D4 L ((d4RhoPerm ^ e) k) (c ^ 2 ^ h) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [rckTriD4_diagramFrobHom_apply]
  change rckTriD4_trialityMatrix (L := L) ^ e *
      Units.map (entrywiseHom (iterateFrobenius L 2 h)) (yUnit Tag.D4 L k c) *
      (rckTriD4_trialityMatrix (L := L) ^ e)⁻¹ =
        yUnit Tag.D4 L ((d4RhoPerm ^ e) k) (c ^ 2 ^ h)
  rw [entrywise_yUnit, rckTriD4_trialityMatrix_pow_mul_yUnit]

theorem rckTriD4_d4NativeEquiv_equiv {τ : Tag} [E6Sub τ] {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {h e : ℕ} (he : e = 1 ∨ e = 2)
    (ε : ↥(adjointGroup Tag.D4 L) ≃* ↥(subsystemGroup τ L (d4Set τ)))
    (hεx : ∀ (k : Fin Tag.D4.rank) (c : L),
      (ε ⟨xUnit Tag.D4 L k c, xUnit_mem_adjointGroup k c⟩ : ModGL τ L) =
        xUnit τ L (d4Id k) c)
    (hεy : ∀ (k : Fin Tag.D4.rank) (c : L),
      (ε ⟨yUnit Tag.D4 L k c, yUnit_mem_adjointGroup k c⟩ : ModGL τ L) =
        yUnit τ L (d4Id k) c)
    {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L,
      n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c)
    (hπ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k)) :
    ∀ x : ↥(adjointGroup Tag.D4 L),
      n₁ * Units.map (entrywiseHom (iterateFrobenius L 2 h)) (ε x) * n₁⁻¹ =
        (ε (rckTriD4_diagramFrobHom e h x) : ModGL τ L) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hrhoE : ∀ k : Fin Tag.D4.rank, (d4RhoPerm ^ e) k = rhoE e k := by
    rcases he with rfl | rfl
    · intro k
      fin_cases k <;> rfl
    · intro k
      fin_cases k <;> rfl
  let F : ↥(adjointGroup Tag.D4 L) →* ModGL τ L :=
    (MulAut.conj n₁).toMonoidHom.comp
      ((Units.map (entrywiseHom (iterateFrobenius L 2 h))).comp
        ((Subgroup.subtype (subsystemGroup τ L (d4Set τ))).comp ε.toMonoidHom))
  let G : ↥(adjointGroup Tag.D4 L) →* ModGL τ L :=
    ((Subgroup.subtype (subsystemGroup τ L (d4Set τ))).comp ε.toMonoidHom).comp
      (rckTriD4_diagramFrobHom e h)
  have hFG : F = G := by
    refine adjointGroup_hom_ext (τ := Tag.D4) (K := L) (f := F) (g := G) ?_ ?_
    · intro k c
      simp only [F, G, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      rw [show (Subgroup.subtype (subsystemGroup τ L (d4Set τ)))
          (ε (xElement k c)) = xUnit τ L (d4Id k) c from hεx k c]
      rw [entrywise_xUnit, (hgen (d4Id k) (d4Id_mem k) (c ^ 2 ^ h)).1, hπ k]
      have harg : rckTriD4_diagramFrobHom e h (xElement k c) =
          ⟨xUnit Tag.D4 L (rhoE e k) (c ^ 2 ^ h),
            xUnit_mem_adjointGroup _ _⟩ := by
        apply Subtype.ext
        rw [rckTriD4_diagramFrobHom_xElement, hrhoE k]
      rw [harg]
      exact (hεx (rhoE e k) (c ^ 2 ^ h)).symm
    · intro k c
      simp only [F, G, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      rw [show (Subgroup.subtype (subsystemGroup τ L (d4Set τ)))
          (ε (yElement k c)) = yUnit τ L (d4Id k) c from hεy k c]
      rw [entrywise_yUnit, (hgen (d4Id k) (d4Id_mem k) (c ^ 2 ^ h)).2, hπ k]
      have harg : rckTriD4_diagramFrobHom e h (yElement k c) =
          ⟨yUnit Tag.D4 L (rhoE e k) (c ^ 2 ^ h),
            yUnit_mem_adjointGroup _ _⟩ := by
        apply Subtype.ext
        rw [rckTriD4_diagramFrobHom_yElement, hrhoE k]
      rw [harg]
      exact (hεy (rhoE e k) (c ^ 2 ^ h)).symm
  intro x
  simpa [F, G] using
    congrArg (fun φ : ↥(adjointGroup Tag.D4 L) →* ModGL τ L => φ x) hFG

end DiagramFrob

theorem rckTriD4_d4NativeEquiv_mem_rootSubgroup_single {τ : Tag} [E6Sub τ] {L : Type}
    [Field L] [CharP L 2]
    {ε : ↥(adjointGroup Tag.D4 L) ≃* ↥(subsystemGroup τ L (d4Set τ))}
    (hεx : ∀ (k : Fin Tag.D4.rank) (c : L),
      (ε ⟨xUnit Tag.D4 L k c, xUnit_mem_adjointGroup k c⟩ : ModGL τ L) =
        xUnit τ L (d4Id k) c)
    (hεy : ∀ (k : Fin Tag.D4.rank) (c : L),
      (ε ⟨yUnit Tag.D4 L k c, yUnit_mem_adjointGroup k c⟩ : ModGL τ L) =
        yUnit τ L (d4Id k) c)
    (k : Fin Tag.D4.rank) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ∀ u : ↥(adjointGroup Tag.D4 L),
      (u : ModGL Tag.D4 L) ∈ rootSubgroup Tag.D4 L (s • Pi.single k 1) ↔
        (ε u : ModGL τ L) ∈ rootSubgroup τ L (s • Pi.single (d4Id k) 1) := by
  rcases hs with rfl | rfl
  · intro u
    rw [one_smul, one_smul, mem_rootSubgroup, mem_rootSubgroup]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hu : u = ⟨xUnit Tag.D4 L k c, xUnit_mem_adjointGroup k c⟩ := by
        apply Subtype.ext
        rw [← hc, pinnedX_single]
      rw [hu, hεx k c, pinnedX_single]
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hcu : (⟨xUnit Tag.D4 L k c, xUnit_mem_adjointGroup k c⟩ :
          ↥(adjointGroup Tag.D4 L)) = u := by
        apply ε.injective
        apply Subtype.ext
        rw [hεx k c, ← pinnedX_single]
        exact hc
      rw [← hcu, pinnedX_single]
  · intro u
    rw [neg_smul, one_smul, neg_smul, one_smul, mem_rootSubgroup, mem_rootSubgroup]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hu : u = ⟨yUnit Tag.D4 L k c, yUnit_mem_adjointGroup k c⟩ := by
        apply Subtype.ext
        rw [← hc, pinnedX_neg_single]
      rw [hu, hεy k c, pinnedX_neg_single]
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hcu : (⟨yUnit Tag.D4 L k c, yUnit_mem_adjointGroup k c⟩ :
          ↥(adjointGroup Tag.D4 L)) = u := by
        apply ε.injective
        apply Subtype.ext
        rw [hεy k c, ← pinnedX_neg_single]
        exact hc
      rw [← hcu, pinnedX_neg_single]

theorem rckTriD4_diagramFrobHom_coe_triPsi (e h : ℕ)
    (x : ↥(adjointGroup Tag.D4 GGL)) :
    (rckTriD4_diagramFrobHom e h x : ModGL Tag.D4 GGL) =
      triPsi h e (x : ModGL Tag.D4 GGL) := by
  rw [rckTriD4_diagramFrobHom_apply]
  change (rckTriD4_trialityMatrix (L := GGL) ^ e) *
      Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) (x : ModGL Tag.D4 GGL) *
      (rckTriD4_trialityMatrix (L := GGL) ^ e)⁻¹ =
    (MulAut.conj (rckTriD4_trialityMatrix (L := GGL) ^ e))
      (Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) (x : ModGL Tag.D4 GGL))
  rw [MulAut.conj_apply]


end CFSG.StandardType.RCKRP

end

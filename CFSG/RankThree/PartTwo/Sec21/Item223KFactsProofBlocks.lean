module

public import CFSG.RankThree.PartTwo.Sec21.Item223KFactsProofCore
public import CFSG.RankThree.PartTwo.Sec21.Item223Gaps
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223KFactsProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (torusVec torusSU mem_torusSU_iff diagU diagU_val diagU_mul
  diagU_one diagU_injective symAct symAut symAut_apply symAut_injective movedSub blk
  torusSU_le_unitarySU card_movedSub_swap exists_isPrimitiveRoot)
open CFSG.Assembly.RankThreeEven (projSL projSU)

local notation "𝔽" m => GaloisField 2 (2 * m)

structure TorusModel {G : Type} [Group G] (X T : Subgroup G) (m : ℕ) where
  two_le : 2 ≤ m
  odd : Odd m
  ψ : unitarySU 2 m (𝔽 m) 4 ≃* X
  hψ : ∀ g, ((ψ g : X) : G) ∈ T ↔ (g : GL (Fin 4) (𝔽 m)) ∈ torusSU 3 4 (𝔽 m)

namespace TorusModel

variable {G : Type} [Group G] {X T : Subgroup G} {m : ℕ} (C : TorusModel X T m)

include C in
theorem hU : UnitaryFieldData 2 m (𝔽 m) := unitaryFieldData_galoisField (by have := C.two_le; omega)

include C in
theorem hpq : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one C.odd

include C in
theorem exists_root : ∃ ζ : (𝔽 m)ˣ, IsPrimitiveRoot ζ 3 := by
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot C.hU Nat.prime_three C.hpq
  have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
  exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩

@[expose] noncomputable def phi : unitarySU 2 m (𝔽 m) 4 →* G := X.subtype.comp C.ψ.toMonoidHom

theorem phi_apply (g : unitarySU 2 m (𝔽 m) 4) : C.phi g = ((C.ψ g : X) : G) := rfl

theorem phi_injective : Function.Injective C.phi := fun _ _ h => C.ψ.injective (Subtype.ext h)

theorem range_phi : C.phi.range = X := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact (C.ψ g).2
  · intro hx
    exact ⟨C.ψ.symm ⟨x, hx⟩, by rw [phi_apply, MulEquiv.apply_symm_apply]⟩

@[expose] noncomputable def torU : torusVec 3 4 (𝔽 m) →* unitarySU 2 m (𝔽 m) 4 :=
  ((CFSG.RankThree.PartOne.KFU.diagUHom).comp (torusVec 3 4 (𝔽 m)).subtype).codRestrict _
    fun d => torusSU_le_unitarySU C.hU C.hpq (mem_torusSU_iff.mpr ⟨d.1, d.2.1, d.2.2, rfl⟩)

theorem coe_torU (d : torusVec 3 4 (𝔽 m)) :
    ((C.torU d : unitarySU 2 m (𝔽 m) 4) : GL (Fin 4) (𝔽 m)) = diagU (d : Fin 4 → (𝔽 m)ˣ) :=
  rfl

@[expose] noncomputable def theta : torusVec 3 4 (𝔽 m) →* G := C.phi.comp C.torU

theorem theta_apply (d : torusVec 3 4 (𝔽 m)) : C.theta d = C.phi (C.torU d) := rfl

theorem theta_injective : Function.Injective C.theta := by
  intro d e h
  have h1 := congrArg (fun x : unitarySU 2 m (𝔽 m) 4 => (x : GL (Fin 4) (𝔽 m)))
    (C.phi_injective h)
  exact Subtype.ext (diagU_injective h1)

theorem theta_mem (d : torusVec 3 4 (𝔽 m)) : C.theta d ∈ T :=
  (C.hψ _).mpr (mem_torusSU_iff.mpr ⟨d.1, d.2.1, d.2.2, rfl⟩)

theorem range_theta (hTX : T ≤ X) : C.theta.range = T := by
  ext t
  constructor
  · rintro ⟨d, rfl⟩
    exact C.theta_mem d
  · intro ht
    set g := C.ψ.symm ⟨t, hTX ht⟩ with hg
    have hgt : C.phi g = t := by rw [phi_apply, hg, MulEquiv.apply_symm_apply]
    have hgT := (C.hψ g).mp (by rw [← phi_apply, hgt]; exact ht)
    obtain ⟨d, hd1, hd2, hdg⟩ := mem_torusSU_iff.mp hgT
    refine ⟨⟨d, hd1, hd2⟩, ?_⟩
    rw [theta_apply, ← hgt]
    congr 1
    exact Subtype.ext hdg

@[expose] noncomputable def thetaT (hTX : T ≤ X) : torusVec 3 4 (𝔽 m) ≃* T :=
  (MonoidHom.ofInjective C.theta_injective).trans (MulEquiv.subgroupCongr (C.range_theta hTX))

theorem coe_thetaT (hTX : T ≤ X) (d : torusVec 3 4 (𝔽 m)) :
    ((C.thetaT hTX d : T) : G) = C.theta d := rfl

theorem map_theta_eq (hTX : T ≤ X) (H : Subgroup (torusVec 3 4 (𝔽 m))) :
    H.map C.theta = (H.map (C.thetaT hTX).toMonoidHom).map T.subtype := by
  rw [Subgroup.map_map]
  rfl

@[expose] noncomputable def actT (hTX : T ≤ X) : Equiv.Perm (Fin 4) →* MulAut T :=
  (MulAut.congr (C.thetaT hTX)).toMonoidHom.comp (symAut 3 (𝔽 m))

theorem actT_injective (hTX : T ≤ X) : Function.Injective (C.actT hTX) :=
  (MulAut.congr (C.thetaT hTX)).injective.comp
    (symAut_injective Nat.prime_three (by norm_num) C.exists_root)

theorem orderOf_actT_swap (hTX : T ≤ X) {a b : Fin 4} (hab : a ≠ b) :
    orderOf (C.actT hTX (Equiv.swap a b)) = 2 := by
  rw [orderOf_injective _ (C.actT_injective hTX)]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [pow_two, Equiv.swap_mul_self]) ?_
  intro h
  have := congrArg (fun σ : Equiv.Perm (Fin 4) => σ a) h
  simp [Equiv.swap_apply_left] at this
  exact hab this.symm

theorem fixedSubgroupOf_actT (hTX : T ≤ X) (a b : Fin 4) :
    fixedSubgroupOf (C.actT hTX (Equiv.swap a b)) =
      (hplane (𝔽 m) a b).map (C.thetaT hTX).toMonoidHom := by
  rw [actT, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, fixedSubgroupOf_congr]
  rfl

theorem commOf_actT (hTX : T ≤ X) (σ : Equiv.Perm (Fin 4)) :
    commOf (C.actT hTX σ) = (movedSub 3 (𝔽 m) σ).map (C.thetaT hTX).toMonoidHom := by
  rw [actT, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, commOf_congr, commOf_symAut]

theorem commute_diagU_of_mem {K' H : Subgroup _} (hK'C : K' ≤ Subgroup.centralizer
      ((H.map C.theta : Subgroup G) : Set G)) {g : unitarySU 2 m (𝔽 m) 4} (hg : C.phi g ∈ K')
    {d : torusVec 3 4 (𝔽 m)} (hd : d ∈ H) :
    (g : GL (Fin 4) (𝔽 m)) * diagU (d : Fin 4 → (𝔽 m)ˣ) = diagU (d : Fin 4 → (𝔽 m)ˣ) * g := by
  have h1 : C.theta d * C.phi g = C.phi g * C.theta d :=
    Subgroup.mem_centralizer_iff.mp (hK'C hg) _ ⟨d, hd, rfl⟩
  rw [theta_apply, ← map_mul, ← map_mul] at h1
  have h2 := congrArg (fun u : unitarySU 2 m (𝔽 m) 4 => (u : GL (Fin 4) (𝔽 m)))
    (C.phi_injective h1)
  simp only [Subgroup.coe_mul, coe_torU] at h2
  exact h2.symm

theorem eq_map_hplane (hTX : T ≤ X) {B K' : Subgroup G} (hBT : B ≤ T) (hB9 : Nat.card B = 3 ^ 2)
    (hK'X : K' ≤ X) (hK'C : K' ≤ Subgroup.centralizer (B : Set G)) {x y : G} (hx : x ∈ K')
    (hy : y ∈ K') (hxy : x * y ≠ y * x) :
    ∃ a b : Fin 4, a ≠ b ∧ B = (hplane (𝔽 m) a b).map C.theta := by
  set H := B.comap C.theta with hH
  have hBr : B ≤ C.theta.range := (C.range_theta hTX).symm ▸ hBT
  have hHB : H.map C.theta = B := Subgroup.map_comap_eq_self hBr
  have hHcard : Nat.card H = 9 := by
    rw [← Subgroup.card_map_of_injective C.theta_injective, hHB, hB9]
    norm_num
  have hK'C' : K' ≤ Subgroup.centralizer ((H.map C.theta : Subgroup G) : Set G) := by
    rw [hHB]
    exact hK'C
  have hXr : X ≤ C.phi.range := C.range_phi.symm.le
  obtain ⟨g, hg⟩ := hXr (hK'X hx)
  obtain ⟨g', hg'⟩ := hXr (hK'X hy)
  rcases separating_or_le_hplane H with hsep | ⟨a, b, hab, hle⟩
  · exfalso
    have h := commute_of_separating hsep (fun d hd => C.commute_diagU_of_mem hK'C' (hg ▸ hx) hd)
      (fun d hd => C.commute_diagU_of_mem hK'C' (hg' ▸ hy) hd)
    apply hxy
    rw [← hg, ← hg', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  · obtain ⟨ζ, hζ⟩ := C.exists_root
    have := C.hU.finite
    refine ⟨a, b, hab, ?_⟩
    rw [← hHB, eq_hplane_of_le ⟨ζ, hζ⟩ hab hle hHcard.ge]

theorem pre_eq_blk {a b : Fin 4} (hab : a ≠ b) {K' : Subgroup G} (hK'X : K' ≤ X)
    (hK'C : K' ≤ Subgroup.centralizer
      (((hplane (𝔽 m) a b).map C.theta : Subgroup G) : Set G))
    (eK : K' ≃* projSL 2 (GaloisField 2 m)) :
    (K'.comap C.phi).map (unitarySU 2 m (𝔽 m) 4).subtype = blk C.hU hab := by
  obtain ⟨ζ, hζ⟩ := C.exists_root
  have := C.hU.finite
  have hK'r : K' ≤ C.phi.range := C.range_phi.symm ▸ hK'X
  let e₁ : K'.comap C.phi ≃* K' :=
    (Subgroup.equivMapOfInjective (K'.comap C.phi) C.phi C.phi_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hK'r))
  let e₂ : K'.comap C.phi ≃* (K'.comap C.phi).map (unitarySU 2 m (𝔽 m) 4).subtype :=
    Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)
  let e : (K'.comap C.phi).map (unitarySU 2 m (𝔽 m) 4).subtype ≃* projSL 2 (GaloisField 2 m) :=
    e₂.symm.trans (e₁.trans eK)
  have hSp := isPerfect_of_mulEquiv_projSL C.two_le e
  have hc : ∀ g ∈ (K'.comap C.phi).map (unitarySU 2 m (𝔽 m) 4).subtype,
      ∀ d ∈ hplane (𝔽 m) a b,
        g * diagU (d : Fin 4 → (𝔽 m)ˣ) = diagU (d : Fin 4 → (𝔽 m)ˣ) * g := by
    rintro _ ⟨u, hu, rfl⟩ d hd
    exact C.commute_diagU_of_mem hK'C hu hd
  have hle := le_blk_of_perfect C.hU hζ hab (Subgroup.map_subtype_le _) hSp hc
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_blk C.hU hab, Nat.card_congr e.toEquiv, card_projSL_two m (by have := C.two_le; omega)]

theorem mem_iff_of_pre_eq {a b : Fin 4} (hab : a ≠ b) {K' : Subgroup G}
    (hpre : (K'.comap C.phi).map (unitarySU 2 m (𝔽 m) 4).subtype = blk C.hU hab)
    (g : unitarySU 2 m (𝔽 m) 4) : C.phi g ∈ K' ↔ (g : GL (Fin 4) (𝔽 m)) ∈ blk C.hU hab := by
  rw [← hpre]
  constructor
  · intro hg
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g', hg', hgg'⟩
    have h : g' = g := Subtype.ext hgg'
    rw [← h]
    exact hg'

theorem eq_actT_swap (hTX : T ≤ X) (hTe : CFSG.Assembly.IsElemAbelian 3 T) {a b : Fin 4}
    (hab : a ≠ b) {K' : Subgroup G}
    (hpre : (K'.comap C.phi).map (unitarySU 2 m (𝔽 m) 4).subtype = blk C.hU hab)
    {ρ : MulAut T} (hρ : IsReflectionOn ρ)
    (hfix : fixedInG T ρ = (hplane (𝔽 m) a b).map C.theta)
    (hcK : (commOf ρ).map T.subtype ≤ K') : ρ = C.actT hTX (Equiv.swap a b) := by
  obtain ⟨ζ, hζ⟩ := C.exists_root
  have := C.hU.finite
  have hTc : ∀ x y : T, x * y = y * x := hTe.1.is_comm.comm
  have hT3 : ∀ x : T, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hTe.2 x x.2)
  have : Finite T := Finite.of_equiv _ (C.thetaT hTX).toEquiv
  refine eq_of_fixed_eq_of_commOf_eq hTc hT3 hρ.1 (C.orderOf_actT_swap hTX hab) ?_ ?_
  · rw [C.fixedSubgroupOf_actT hTX]
    apply Subgroup.map_injective T.subtype_injective
    rw [← fixedInG, hfix, C.map_theta_eq hTX]
  · rw [C.commOf_actT hTX]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro t ht
      have htK : (t : G) ∈ K' := hcK ⟨t, ht, rfl⟩
      obtain ⟨d, rfl⟩ := (C.thetaT hTX).surjective t
      refine ⟨d, ?_, rfl⟩
      rw [coe_thetaT, theta_apply, C.mem_iff_of_pre_eq hab hpre, coe_torU] at htK
      exact mem_movedSub_of_diagU_mem_blk C.hU hab htK
    · rw [hρ.2, Subgroup.card_map_of_injective (C.thetaT hTX).injective,
        card_movedSub_swap Nat.prime_three (by norm_num) ⟨ζ, hζ⟩ hab]

end TorusModel

theorem nonempty_torusModel {G : Type} [Group G] [Finite G] {X T : Subgroup G} {m : ℕ}
    (eX : X ≃* projSU 4 2 m) (hm1 : 1 < m) (hmo : Odd m) (hTX : T ≤ X)
    (hTe : CFSG.Assembly.IsElemAbelian 3 T) (hT27 : Nat.card T = 3 ^ 3) {x y : G} (hx : x ∈ X)
    (hy : y ∈ X) (hxy : x * y ≠ y * x) : Nonempty (TorusModel X T m) := by
  have hZ : Subgroup.center X = ⊥ :=
    center_eq_bot_of_mulEquiv_projSU (by omega) eX (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
      (fun h => hxy (congrArg Subtype.val h))
  have hexp : ∀ z ∈ T.subgroupOf X, z ^ 3 = 1 := fun z hz =>
    Subtype.ext (by simpa using hTe.2 _ (Subgroup.mem_subgroupOf.mp hz))
  have hcomm : ∀ z ∈ T.subgroupOf X, ∀ w ∈ T.subgroupOf X, z * w = w * z := by
    intro z hz w hw
    have h := congrArg Subtype.val (hTe.1.is_comm.comm ⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩
      ⟨(w : G), Subgroup.mem_subgroupOf.mp hw⟩)
    exact Subtype.ext h
  have hcard : Nat.card (T.subgroupOf X) = 3 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv, hT27]
  obtain ⟨ψ, hψ⟩ := exists_diag_model (by omega) hmo eX hZ (T.subgroupOf X) hexp hcomm hcard
  exact ⟨{ two_le := by omega
           odd := hmo
           ψ := ψ
           hψ := fun g => by rw [← hψ g, Subgroup.mem_subgroupOf] }⟩

end CFSG.RankThree.PartTwo.Sec21.Item223KFactsProof

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Item223KFactsProof
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KFU (blk)

local notation "𝔽" m => GaloisField 2 (2 * m)

theorem u4TorusBlocks_holds : U4TorusBlocks := by
  intro G _ _ X T B₁ B₂ K₁ K₂ m ⟨eX⟩ hm1 hmo hTX hTe hT27 hB₁T hB₂T hB₁9 hB₂9 hB12 hK₁X hK₂X
    hK₁C hK₂C _ _ ⟨eK₁⟩ ⟨eK₂⟩ ρ₁ ρ₂ hρ₁ hρ₂ hfix₁ hfix₂ hc₁ hc₂
  obtain ⟨x₁, y₁, hxy₁⟩ := exists_not_commute_of_mulEquiv_projSL eK₁
  obtain ⟨x₂, y₂, hxy₂⟩ := exists_not_commute_of_mulEquiv_projSL eK₂
  have hxy₁' : (x₁ : G) * y₁ ≠ y₁ * x₁ := fun h => hxy₁ (Subtype.ext h)
  have hxy₂' : (x₂ : G) * y₂ ≠ y₂ * x₂ := fun h => hxy₂ (Subtype.ext h)
  obtain ⟨C⟩ := nonempty_torusModel eX hm1 hmo hTX hTe hT27 (hK₁X x₁.2) (hK₁X y₁.2) hxy₁'
  obtain ⟨a₁, b₁, hab₁, rfl⟩ := C.eq_map_hplane hTX hB₁T hB₁9 hK₁X hK₁C x₁.2 y₁.2 hxy₁'
  obtain ⟨a₂, b₂, hab₂, rfl⟩ := C.eq_map_hplane hTX hB₂T hB₂9 hK₂X hK₂C x₂.2 y₂.2 hxy₂'
  have hpre₁ := C.pre_eq_blk hab₁ hK₁X hK₁C eK₁
  have hpre₂ := C.pre_eq_blk hab₂ hK₂X hK₂C eK₂
  obtain rfl := C.eq_actT_swap hTX hTe hab₁ hpre₁ hρ₁ hfix₁ hc₁
  obtain rfl := C.eq_actT_swap hTX hTe hab₂ hpre₂ hρ₂ hfix₂ hc₂
  have hsw : Equiv.swap a₁ b₁ ≠ Equiv.swap a₂ b₂ := by
    intro h
    apply hB12
    simp only [hplane, h]
  have hXr : X ≤ C.phi.range := C.range_phi.symm.le
  rcases swap_dichotomy a₁ b₁ a₂ b₂ hab₁ hab₂ hsw with
    ⟨hcomm, h13, h14, h23, h24⟩ | ⟨hnc, hcub, hshare⟩
  · refine ⟨fun _ => ?_, fun h => absurd (by rw [← map_mul, ← map_mul, hcomm]) h⟩
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨u, rfl⟩ := hXr (hK₁X hz)
    obtain ⟨v, rfl⟩ := hXr (hK₂X hw)
    have hu := (C.mem_iff_of_pre_eq hab₁ hpre₁ u).mp hz
    have hv := (C.mem_iff_of_pre_eq hab₂ hpre₂ v).mp hw
    have h := CFSG.RankThree.PartOne.KFU.blk_comm_of_disjoint hab₁ hab₂ h13 h14 h23 h24 hu hv
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h.symm
  · refine ⟨fun h => absurd ((C.actT_injective hTX) (by rw [map_mul, map_mul]; exact h)) hnc,
      fun _ => ⟨?_, ?_⟩⟩
    · have hK₁r : K₁ ≤ C.phi.range := hK₁X.trans hXr
      have hK₂r : K₂ ≤ C.phi.range := hK₂X.trans hXr
      have hsup : K₁ ⊔ K₂ = (K₁.comap C.phi ⊔ K₂.comap C.phi).map C.phi := by
        rw [Subgroup.map_sup, Subgroup.map_comap_eq_self hK₁r, Subgroup.map_comap_eq_self hK₂r]
      have hsup' : (K₁.comap C.phi ⊔ K₂.comap C.phi).map (unitarySU 2 m (𝔽 m) 4).subtype =
          blk C.hU hab₁ ⊔ blk C.hU hab₂ := by
        rw [Subgroup.map_sup, hpre₁, hpre₂]
      obtain ⟨eSU⟩ := blk_sup_blk_mulEquiv_su3_of_share C.hU C.two_le hab₁ hab₂ hshare
      exact ⟨(MulEquiv.subgroupCongr hsup).trans
        ((Subgroup.equivMapOfInjective _ _ C.phi_injective).symm.trans
          ((Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).trans
            ((MulEquiv.subgroupCongr hsup').trans
              (eSU.trans (MulEquiv.subgroupCongr (unitarySU_three_eq_SU3 m))))))⟩
    · refine closure_pair_mulEquiv_perm_three ?_ ?_ ?_ ?_
      · rw [← map_mul, Equiv.swap_mul_self, map_one]
      · rw [← map_mul, Equiv.swap_mul_self, map_one]
      · rw [← map_mul, ← map_pow, hcub, map_one]
      · intro h
        exact hnc ((C.actT_injective hTX) (by rw [map_mul, map_mul]; exact h))

end CFSG.RankThree.PartTwo.Sec21

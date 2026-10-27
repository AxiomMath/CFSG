module

public import CFSG.Quasithin.Vol2.Ch11SecOE7E
public import CFSG.Quasithin.Background.E3ClosedTwo

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)
open scoped commutatorElement

section AlmostSimple

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_normal_of_isPGroup {L N : Subgroup G} (h : AlmostSimple L) (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_bot_iff.mp ?_
  calc N ≤ CFSG.Open.pCore 2 G := CFSG.LieType.BorelTits.le_pCore 2 hN h2
    _ ≤ CFSG.solvableRadical G := E3.pCore_two_le_solvableRadical
    _ = ⊥ := h.solvableRadical_eq_bot

theorem tauOf_le_centralizer {L T A : Subgroup G} (h : AlmostSimple L) {a : G} (ha : a ∈ A) :
    tauOf ⊤ T A ≤ Subgroup.centralizer {a} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (pCoreOf 2 (⊤ : Subgroup G)).Normal := Subgroup.normalizer_eq_top_iff.mp
    (eq_top_iff.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤))
  have hO := eq_bot_of_normal_of_isPGroup h hn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤)
  intro t ht
  have h1 := ht.2.2 a ha
  rw [hO, Subgroup.mem_bot, commutatorElement_def] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc t * a = (t * a * t⁻¹ * a⁻¹) * (a * t) := by group
    _ = a * t := by rw [h1, one_mul]

theorem isSolvable_of_inf {L X : Subgroup G} [hL : L.Normal]
    (htwo : ∀ x : G, ∃ k : ℕ, x ^ 2 ^ k ∈ L) (hXL : Group.IsSolvable ↥(X ⊓ L)) :
    Group.IsSolvable ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (X ⊓ L).subgroupOf X with hNdef
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨X.mul_mem (X.mul_mem g.2 hn.1) (X.inv_mem g.2), hL.conj_mem _ hn.2 g⟩
  have hQ : IsPGroup 2 (↥X ⧸ N) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨k, hk⟩ := htwo x
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hNdef,
      Subgroup.mem_subgroupOf]
    exact ⟨X.pow_mem x.2 _, hk⟩
  have := hQ.isNilpotent
  have : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : X ⊓ L ≤ X)).toMonoidHom) (Subgroup.subgroupOfEquivOfLe _).injective
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end AlmostSimple

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {f : ℕ} (hf : 2 ≤ f)
  (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)

omit [Finite K] in
theorem normalizer_conjSub_rootU (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hB : Subgroup.normalizer ((rootU J hJ : Subgroup _) :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoordinateStabilizer J 0) :
    Subgroup.normalizer ((A1b.conjSub g (rootU J hJ) : Subgroup _) :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      A1b.conjSub g (unitaryCoordinateStabilizer J 0) := by
  rw [← hB]
  exact (Subgroup.map_equiv_normalizer_eq _ (MulAut.conj g)).symm

include hJ hf hcard hfixed in
theorem conjSub_stabilizer_sup_eq_top (g : ProjectiveSpecialUnitaryMatrixGroup J)
    {X : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (hX : ¬ Group.IsSolvable ↥X) :
    A1b.conjSub g (unitaryCoordinateStabilizer J 0) ⊔ X = ⊤ := by
  set B := unitaryCoordinateStabilizer J 0 with hBdef
  have hBc := Ch3E213M.P4C.isCoatom_stabilizer J hf hcard hfixed hJ
  have hBs := isSolvable_stabilizer J hJ hf hcard hfixed
  have hBgs : Group.IsSolvable ↥(A1b.conjSub g B) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (B.equivMapOfInjective _ (MulAut.conj g).injective).symm.toMonoidHom)
      (B.equivMapOfInjective _ (MulAut.conj g).injective).symm.injective
  have hXB : ¬ X ≤ A1b.conjSub g B := fun hle => hX
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))
  have hlt : A1b.conjSub g B < A1b.conjSub g B ⊔ X :=
    lt_of_le_of_ne le_sup_left fun h => hXB (h ▸ le_sup_right)
  have hlt' : B < A1b.conjSub g⁻¹ (A1b.conjSub g B ⊔ X) := by
    have h1 := A1b.conjSub_mono g⁻¹ hlt.le
    rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one] at h1
    refine lt_of_le_of_ne h1 fun h => ?_
    apply hlt.ne
    have h4 := congrArg (A1b.conjSub g) h
    rwa [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one] at h4
  have h2 := hBc.2 _ hlt'
  have h3 : A1b.conjSub g (A1b.conjSub g⁻¹ (A1b.conjSub g B ⊔ X)) = A1b.conjSub g B ⊔ X := by
    rw [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one]
  rw [← h3, h2]
  exact conjSub_top' g

end Model

section Transport

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
  (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {f : ℕ} (hf : 2 ≤ f)
  (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)

omit [Finite G] [Finite K] in
theorem psuEmb_mem_normalizer_iff {L : Subgroup G}
    (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    psuEmb J e x ∈ Subgroup.normalizer ((P.map (psuEmb J e) : Subgroup G) : Set G) ↔
      x ∈ Subgroup.normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  rw [← A1b.conjSub_eq_iff_mem_normalizer, ← A1b.conjSub_eq_iff_mem_normalizer,
    ← SecE3.map_conjSub]
  exact (Subgroup.map_injective (psuEmb_injective J e)).eq_iff

include hJ hf hcard hfixed in
theorem isSolvable_normalizer_inf_psu3 {L T : Subgroup G} (h : AlmostSimple L)
    (hT : quasithinIsSylowTwo T) (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Group.IsSolvable ↥(Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) := by
  have hLn := h.normal
  obtain ⟨g, hg⟩ := exists_conj_rootU_eq J hJ hf hcard hfixed hT e
  have hB := Ch3E213M.P4C.normalizer_root_eq J hf hcard hfixed hJ
  have hNP := normalizer_conjSub_rootU J hJ g hB
  have hBs := isSolvable_stabilizer J hJ hf hcard hfixed
  have hle : Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓ L ≤
      (A1b.conjSub g (unitaryCoordinateStabilizer J 0)).map (psuEmb J e) := by
    intro y hy
    obtain ⟨hyN, hyL⟩ := Subgroup.mem_inf.mp hy
    rw [← psuEmb_range J e] at hyL
    obtain ⟨x, rfl⟩ := hyL
    rw [← hg, psuEmb_mem_normalizer_iff, hNP] at hyN
    exact ⟨x, hyN, rfl⟩
  have hBgs : Group.IsSolvable
      ↥((A1b.conjSub g (unitaryCoordinateStabilizer J 0)).map (psuEmb J e)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := ((Subgroup.equivMapOfInjective _ _ (psuEmb_injective J e)).symm.trans
        ((unitaryCoordinateStabilizer J 0).equivMapOfInjective _
          (MulAut.conj g).injective).symm).toMonoidHom)
      (MulEquiv.injective _)
  exact isSolvable_of_inf h.two
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))

include hJ hf hcard hfixed in
theorem le_sup_normalizer_of_not_isSolvable {L T L₀ : Subgroup G} [L.Normal]
    (hT : quasithinIsSylowTwo T) (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hL₀L : L₀ ≤ L) (hL₀ : ¬ Group.IsSolvable ↥L₀) :
    L ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ⊔ L₀ := by
  obtain ⟨g, hg⟩ := exists_conj_rootU_eq J hJ hf hcard hfixed hT e
  set ψ := psuEmb J e with hψdef
  have hB := Ch3E213M.P4C.normalizer_root_eq J hf hcard hfixed hJ
  have hNP := normalizer_conjSub_rootU J hJ g hB
  set X := L₀.comap ψ with hX
  have hXL₀ : X.map ψ = L₀ := Subgroup.map_comap_eq_self (by rw [psuEmb_range J e]; exact hL₀L)
  have hXs : ¬ Group.IsSolvable ↥X := fun hs => hL₀ (by
    rw [← hXL₀]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective X ψ (psuEmb_injective J e)).symm.toMonoidHom)
      (MulEquiv.injective _))
  have htop := conjSub_stabilizer_sup_eq_top J hJ hf hcard hfixed g hXs
  have hBD : (A1b.conjSub g (unitaryCoordinateStabilizer J 0)).map ψ ≤
      Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hg, psuEmb_mem_normalizer_iff, hNP]
    exact hx
  calc L = (⊤ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map ψ := by
        rw [← MonoidHom.range_eq_map, psuEmb_range]
    _ = (A1b.conjSub g (unitaryCoordinateStabilizer J 0)).map ψ ⊔ L₀ := by
        rw [← htop, Subgroup.map_sup, hXL₀]
    _ ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ⊔ L₀ := sup_le_sup_right hBD _

end Transport

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

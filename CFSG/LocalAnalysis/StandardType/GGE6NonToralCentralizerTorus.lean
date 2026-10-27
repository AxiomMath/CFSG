module

public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial
public import CFSG.LieType.AlgebraicGroups.TorusGroupClosed
public import CFSG.LieType.AlgebraicGroups.CoordinateConjugation
public import CFSG.LieType.AlgebraicGroups.DiagonalSubgroupTorus
public import CFSG.LieType.AlgebraicGroups.TorusPointSubgroups
public import CFSG.LieType.Chevalley.DiagonalCharTwo
public import CFSG.LieType.AlgebraicGroups.ExactAffineRealization
public import CFSG.LieType.AlgebraicGroups.ZariskiClosureFrobenius
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralCent
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralEmbed
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralClauses
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralCyclic
public import CFSG.Permutation.FiveTransitive.KernelImageGeneration
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourToral
public import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
public import CFSG.LocalAnalysis.StandardType.GGE6MaximalCentralizerTorsion

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv
open scoped CFSG.ConvolutionPoints

variable {k : Type} [Field k] [IsAlgClosed k]

section E6
open CFSG.StandardType.E6NonToralThree CFSG.StandardType.TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem connected_centralizer_le_torus_of_regular
    (hchar : ringChar k ≠ 3)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEM : E ≤ monomialSubgroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 k)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 k ⟨e, hEM he⟩ ∈
      CFSG.StandardType.TableBExc.E6Three.modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 k ⟨e, hEM he⟩ ≠
      CFSG.StandardType.TableBExc.E6Three.gE6 i) :
    closedIdentityComponent (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))) ≤
      torusGroup .E6 k := by
  let Z := adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))
  let T := torusGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))
  have hEZ : E ≤ Z := by
    intro e he
    refine ⟨monomialSubgroup_le_adjointGroup' (hEM he), ?_⟩
    change e ∈ centralizer (E : Set (ModGL .E6 k))
    rw [mem_centralizer_iff]
    intro x hx
    exact hE.comm hx he
  have hZT : ∀ z ∈ Z, ∃ e ∈ E, ∃ t ∈ T, z = e * t := by
    intro z hz
    obtain ⟨e, he, t, ht, hc, hzt⟩ :=
      exists_mul_torus_of_commute hchar hEM hE hcard hET hAS hAg hz.1
        (fun x hx => (mem_centralizer_iff.mp hz.2 x hx).symm)
    refine ⟨e, he, t, ⟨ht, ?_⟩, hzt⟩
    change t ∈ centralizer (E : Set (ModGL .E6 k))
    rw [mem_centralizer_iff]
    intro x hx
    exact (hc x hx).symm
  have : (T.subgroupOf Z).FiniteIndex := finiteIndex_subgroupOf_of_finite_left_factor hEZ hZT
  have hT := isPointClosed_inf (isPointClosed_torusGroup (τ := Tag.E6) (k := k))
    (isPointClosed_centralizer (E : Set (ModGL .E6 k)))
  exact (closedIdentityComponent_le_of_isPointClosed_finiteIndex hT).trans inf_le_left

theorem cube_mem_original_centralizer_identityComponent
    [CharP k 2]
    (halg : letI := ZMod.algebra k 2; Algebra.IsAlgebraic (ZMod 2) k)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E)
    {x : ModGL .E6 k}
    (hx : x ∈ adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))) :
    x ^ 3 ∈ closedIdentityComponent
      (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g,hg,hEM,hreg⟩ := exists_conj_regular (by decide : (2 : ℕ) ≠ 3) halg hEG
    (Set.toFinite (E : Set (ModGL .E6 k))) hE
  let E' := E.map (MulAut.conj g).toMonoidHom
  have hE' : CFSG.Open.IsElemAbelian 3 E' := hE.map _
  have hcard' : Nat.card E' = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have hET : ¬ E' ≤ torusGroup .E6 k := by
    intro h
    exact hnt ((CFSG.StandardType.SCFourCover.e6AdToral_map_conj hg E).mp
      ⟨1,one_mem _,fun e he => by simpa using h he⟩)
  let f := (MulAut.conj g).toMonoidHom
  have hx' : f x ∈ adjointGroup .E6 k ⊓ centralizer (E' : Set (ModGL .E6 k)) := by
    rw [← map_adjoint_centralizer_conj E hg]
    exact mem_map_of_mem f hx
  have hc := cube_mem_closedIdentityComponent_of_mem_centralizer
    (by rw [ringChar.eq k 2]; decide) hEM hE' hcard' hET
      (fun e he => (hreg e he).1) (fun e he i => (hreg e he).2 i) hx'
  rw [← map_pow, ← map_adjoint_centralizer_conj E hg, closedIdentityComponent_map_conj] at hc
  obtain ⟨y,hy,hye⟩ := Subgroup.mem_map.mp hc
  have heq : y = x ^ 3 := (MulAut.conj g).injective hye
  exact heq ▸ hy

theorem isPGroup_original_centralizer_componentGroup
    [CharP k 2]
    (halg : letI := ZMod.algebra k 2; Algebra.IsAlgebraic (ZMod 2) k)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E) :
    IsPGroup 3 (↥(adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))) ⧸
      (closedIdentityComponent
        (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k)))).subgroupOf
          (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k)))) := by
  intro q
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨1, ?_⟩
  change QuotientGroup.mk x ^ 3 = 1
  rw [← QuotientGroup.mk_pow]
  apply (QuotientGroup.eq_one_iff (x ^ 3)).mpr
  exact cube_mem_original_centralizer_identityComponent halg hEG hE hcard hnt x.property

theorem mul_comm_original_centralizer
    [CharP k 2]
    (halg : letI := ZMod.algebra k 2; Algebra.IsAlgebraic (ZMod 2) k)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E)
    {x y : ModGL .E6 k}
    (hx : x ∈ adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k)))
    (hy : y ∈ adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))) : x*y=y*x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g,hg,hEM,hreg⟩ := exists_conj_regular (by decide : (2:ℕ) ≠ 3) halg hEG
    (Set.toFinite (E : Set (ModGL .E6 k))) hE
  let E' := E.map (MulAut.conj g).toMonoidHom
  have hE' : CFSG.Open.IsElemAbelian 3 E' := hE.map _
  have hcard' : Nat.card E' = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective];exact hcard
  have hET : ¬ E' ≤ torusGroup .E6 k := by
    intro h
    apply hnt
    apply (CFSG.StandardType.SCFourCover.e6AdToral_map_conj hg E).mp
    exact ⟨1,one_mem _,fun e he => by simpa using h he⟩
  let f := (MulAut.conj g).toMonoidHom
  have hx' : f x ∈ adjointGroup .E6 k ⊓ centralizer (E' : Set (ModGL .E6 k)) := by
    rw [← map_adjoint_centralizer_conj E hg]
    exact mem_map_of_mem f hx
  have hy' : f y ∈ adjointGroup .E6 k ⊓ centralizer (E' : Set (ModGL .E6 k)) := by
    rw [← map_adjoint_centralizer_conj E hg]
    exact mem_map_of_mem f hy
  apply (MulAut.conj g).injective
  rw [map_mul,map_mul]
  exact (centralizer_clauses (by rw [ringChar.eq k 2]; decide)
    hEM hE' hcard' hET (fun a ha => (hreg a ha).1)
      (fun a ha i => (hreg a ha).2 i)).1 _ hx'.1 _ hy'.1
        (fun e he => (mem_centralizer_iff.mp hx'.2 e he).symm)
        (fun e he => (mem_centralizer_iff.mp hy'.2 e he).symm)

theorem connected_centralizer_conj_le_torus
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E) :
    ∃ g ∈ adjointGroup .E6 L,
      closedIdentityComponent (adjointGroup .E6 L ⊓ centralizer
        (E.map (MulAut.conj g).toMonoidHom : Set (ModGL .E6 L))) ≤ torusGroup .E6 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgG, hEM, hreg⟩ := exists_conj_regular (by decide : (2 : ℕ) ≠ 3) halg hEG
    (Set.toFinite (E : Set (ModGL .E6 L))) hE
  let E' := E.map (MulAut.conj g).toMonoidHom
  have hE' : CFSG.Open.IsElemAbelian 3 E' := hE.map _
  have hcard' : Nat.card E' = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have hnt' : ¬ CFSG.StandardType.SCFourCover.E6AdToral E' := fun h =>
    hnt ((CFSG.StandardType.SCFourCover.e6AdToral_map_conj hgG E).mp h)
  have hET : ¬ E' ≤ torusGroup .E6 L := by
    intro h
    apply hnt'
    refine ⟨1, one_mem _, fun e he => ?_⟩
    simpa using h he
  have : Finite E' := Finite.of_surjective _ ((MulAut.conj g).toMonoidHom.subgroupMap_surjective E)
  refine ⟨g, hgG, connected_centralizer_le_torus_of_regular
    (by rw [ringChar.eq L 2]; decide : ringChar L ≠ 3) hEM hE' hcard' hET (fun e he => (hreg e he).1)
      (fun e he i => (hreg e he).2 i)⟩

theorem eq_one_of_mem_original_centralizer_of_pow_two_pow_eq_one
    [CharP k 2]
    (halg : letI := ZMod.algebra k 2; Algebra.IsAlgebraic (ZMod 2) k)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E)
    {x : ModGL .E6 k}
    (hx : x ∈ adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k)))
    {m : ℕ} (hxm : x ^ (2 ^ m) = 1) : x = 1 := by
  have hx3 := cube_mem_original_centralizer_identityComponent halg hEG hE hcard hnt hx
  obtain ⟨g,hg,hST⟩ := connected_centralizer_conj_le_torus halg hEG hE hcard hnt
  let f := (MulAut.conj g).toMonoidHom
  have hx3T : f (x ^ 3) ∈ torusGroup .E6 k := by
    apply hST
    rw [← map_adjoint_centralizer_conj E hg, closedIdentityComponent_map_conj]
    exact mem_map_of_mem f hx3
  have hx32 : f (x ^ 3) ^ (2 ^ m) = 1 := by
    rw [← map_pow, ← pow_mul, Nat.mul_comm, pow_mul, hxm, one_pow, map_one]
  have hx31 : f (x ^ 3) = 1 :=
    eq_one_of_mem_diagonalGroup_of_pow_two_pow_eq_one
      (torusGroup_le_diagonalGroup hx3T) hx32
  have hx3one : x ^ 3 = 1 := (MulAut.conj g).injective (hx31.trans (map_one f).symm)
  exact (pow_eq_one_iff_of_coprime ((by decide : Nat.Coprime 3 2).pow_right m)).mp ⟨hx3one,hxm⟩

theorem original_connected_centralizer_conj_le_torus
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E) :
    ∃ g ∈ adjointGroup .E6 L,
      (closedIdentityComponent (adjointGroup .E6 L ⊓ centralizer (E : Set (ModGL .E6 L)))).map
        (MulAut.conj g).toMonoidHom ≤ torusGroup .E6 L := by
  obtain ⟨g, hg, h⟩ := connected_centralizer_conj_le_torus halg hEG hE hcard hnt
  refine ⟨g, hg, ?_⟩
  rwa [← map_adjoint_centralizer_conj E hg,
    closedIdentityComponent_map_conj] at h

theorem connected_centralizer_three_torsion_mem_original
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E)
    {x : ModGL .E6 L}
    (hx : x ∈ closedIdentityComponent (adjointGroup .E6 L ⊓ centralizer (E : Set (ModGL .E6 L))))
    (hx3 : x ^ 3 = 1) : x ∈ E := by
  clear halg
  exact mem_of_mem_original_centralizer_of_cube_eq_one hEG hE hcard hnt
    (closedIdentityComponent_le _ hx) hx3

theorem isPointClosed_adjoint_centralizer (E : Subgroup (ModGL .E6 k)) :
    IsPointClosed k (transportPoints (modGLPoint .E6 k)
      ((adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k)) :
        Subgroup (ModGL .E6 k)) : Set (ModGL .E6 k))) := by
  apply isPointClosed_inf
  · have hG := (exceptional_Lang_exact_affine_group_realization k .E6).1.1
    rw [transportPoints_modGLPoint]
    exact hG
  · exact isPointClosed_centralizer _

theorem torus_original_connected_centralizer
    [CharP k 2]
    (halg : letI := ZMod.algebra k 2; Algebra.IsAlgebraic (ZMod 2) k)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E) :
    TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (closedIdentityCoordinateRing
        (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  obtain ⟨g, hg, hc⟩ := original_connected_centralizer_conj_le_torus
    halg hEG hE hcard hnt
  exact torus_closedIdentityComponent_of_conj_le_torus
    (isPointClosed_adjoint_centralizer E) g hc

theorem finrank_tangent_centralizer_le_two_of_regular
    (hchar : ringChar k ≠ 3)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEM : E ≤ monomialSubgroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 k)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 k ⟨e, hEM he⟩ ∈
      CFSG.StandardType.TableBExc.E6Three.modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 k ⟨e, hEM he⟩ ≠
      CFSG.StandardType.TableBExc.E6Three.gE6 i) :
    Module.finrank k (TangentSpace k (closedIdentityCoordinateRing
      (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))))
      (Bialgebra.counitAlgHom k _)) ≤ 2 := by
  classical
  let Z := adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))
  let S := closedIdentityComponent Z
  let H := S.map (modGLPoint .E6 k).toMonoidHom
  have hZ := isPointClosed_adjoint_centralizer E
  have hH := isConnectedAlgebraicSubgroup_closedIdentityComponent (Z := Z) hZ
  have htor := torus_closedIdentityComponent_of_conj_le_torus hZ 1 (by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one]
      using connected_centralizer_le_torus_of_regular
        hchar hEM hE hcard hET hAS hAg hx)
  have hp : (3 : k) ≠ 0 := by
    intro hp
    have : ringChar k ∣ 3 := (CharP.cast_eq_zero_iff k (ringChar k) 3).mp hp
    have h := (Nat.dvd_prime Nat.prime_three).mp this
    rcases h with h | h
    · exact (CharP.ringChar_ne_one (R := k)) h
    · exact hchar h
  obtain ⟨d, hd, ι, hi, hrange⟩ :=
    exists_finrank_tangent_primeTorsion_range_modGL (Z := Z) Nat.prime_three hp hZ htor
  have hroots : ∀ x ∈ S, ∀ m : ℕ, ∃ y ∈ S, y ^ 3 ^ m = x := by
    intro x hx m
    obtain ⟨y, hy, heq⟩ := exists_pow_mem_of_torus H hH.pointsZero_eq htor
      (pow_pos (by norm_num : 0 < 3) m)
      (mem_map_of_mem (modGLPoint .E6 k).toMonoidHom hx)
    obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp hy
    refine ⟨z, hz, (modGLPoint .E6 k).injective ?_⟩
    rw [map_pow]
    change ((modGLPoint .E6 k).toMonoidHom z) ^ 3 ^ m = _
    rw [hzval]
    exact heq
  let D : Set (ModGL .E6 k) := {x | (∀ m : ℕ, ∃ y ∈ adjointGroup .E6 k,
    (∀ e ∈ E, y * e = e * y) ∧ x = y ^ 3 ^ m) ∧ x ^ 3 = 1}
  have hD : D.encard ≤ 9 := (centralizer_clauses hchar hEM hE hcard hET hAS hAg).2.2
  have hsub : (ι.range : Set (ModGL .E6 k)) ⊆ D := by
    intro x hx
    obtain ⟨hxS, hx3⟩ := (hrange x).mp hx
    refine ⟨?_, hx3⟩
    intro m
    obtain ⟨y, hyS, hy⟩ := hroots x hxS m
    have hyZ := closedIdentityComponent_le Z hyS
    exact ⟨y, hyZ.1, fun e he => (mem_centralizer_iff.mp hyZ.2 e he).symm, hy.symm⟩
  have hnc : Nat.card ι.range ≤ 9 := by
    have h := Set.encard_le_encard hsub |>.trans hD
    change (Set.range ι).ncard ≤ 9
    exact (Set.encard_le_coe_iff_finite_ncard_le.mp h).2
  have hcardι : Nat.card ι.range = 3 ^ d := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
      Fintype.card_fin, ZMod.card]
  have hb : d ≤ 2 := by
    rw [hcardι] at hnc
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hnc
  exact hd ▸ hb

theorem finrank_tangent_original_centralizer_le_two
    [CharP k 2]
    (halg : letI := ZMod.algebra k 2; Algebra.IsAlgebraic (ZMod 2) k)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E) :
    Module.finrank k (TangentSpace k (closedIdentityCoordinateRing
      (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))))
      (Bialgebra.counitAlgHom k _)) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgG, hEM, hreg⟩ := exists_conj_regular (by decide : (2 : ℕ) ≠ 3) halg hEG
    (Set.toFinite (E : Set (ModGL .E6 k))) hE
  let E' := E.map (MulAut.conj g).toMonoidHom
  have hE' := hE.map (MulAut.conj g).toMonoidHom
  have : Finite E' := Finite.of_surjective _
    ((MulAut.conj g).toMonoidHom.subgroupMap_surjective E)
  have hcard' : Nat.card E' = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have hET : ¬ E' ≤ torusGroup .E6 k := by
    intro h
    apply hnt
    apply (CFSG.StandardType.SCFourCover.e6AdToral_map_conj hgG E).mp
    exact ⟨1, one_mem _, fun e he => by simpa using h he⟩
  have hb := finrank_tangent_centralizer_le_two_of_regular
    (by rw [ringChar.eq k 2]; decide) hEM hE' hcard' hET
      (fun e he => (hreg e he).1) (fun e he i => (hreg e he).2 i)
  let Z := adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))
  let H := (closedIdentityComponent Z).map (modGLPoint .E6 k).toMonoidHom
  have hmap : (closedIdentityComponent
      (adjointGroup .E6 k ⊓ centralizer (E' : Set (ModGL .E6 k)))).map
        (modGLPoint .E6 k).toMonoidHom =
      H.map (MulAut.conj (modGLPoint .E6 k g)).toMonoidHom := by
    rw [← map_adjoint_centralizer_conj E hgG,
      closedIdentityComponent_map_conj, map_conj_modGLPoint]
  have hfin := (tangentEquivOfBialgEquiv (L := k)
    (conjugateCoordinateBialgEquiv H (modGLPoint .E6 k g))).finrank_eq
  rw [← hmap] at hfin
  rw [← hfin]
  exact hb

theorem recipe_connected_centralizer_geometry
    {n : ℕ} (_hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2)
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E) :
    letI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
    TauCeti.torusCommHopfAlgProperty L
      (TauCeti.FiniteTypeCommHopfAlgCat.of L (closedIdentityCoordinateRing
        (adjointGroup .E6 L ⊓ centralizer (E : Set (ModGL .E6 L))))) ∧
      (∀ x ∈ closedIdentityComponent
        (adjointGroup .E6 L ⊓ centralizer (E : Set (ModGL .E6 L))), x ^ 3 = 1 → x ∈ E) ∧
      Module.finrank L (TangentSpace L (closedIdentityCoordinateRing
        (adjointGroup .E6 L ⊓ centralizer (E : Set (ModGL .E6 L))))
        (Bialgebra.counitAlgHom L _)) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow
    (p := 2) (f := 2 * n) (by
      rw [Nat.card_eq_fintype_card, ← pow_mul] at hK
      simpa only [mul_comm] using hK)
  have : CharP L 2 := (Algebra.charP_iff K L 2).mp inferInstance
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let halg := CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (k := K) (L := L)
  exact ⟨torus_original_connected_centralizer halg hEG hE hcard hnt,
    fun x hx hp => connected_centralizer_three_torsion_mem_original halg hEG hE hcard hnt hx hp,
    finrank_tangent_original_centralizer_le_two halg hEG hE hcard hnt⟩

theorem exists_conj_connected_centralizer_eq_torus_centralizer
    [CharP k 2]
    (halg : letI := ZMod.algebra k 2; Algebra.IsAlgebraic (ZMod 2) k)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E) :
    ∃ g ∈ adjointGroup .E6 k,
      (closedIdentityComponent (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k)))).map
        (MulAut.conj g).toMonoidHom =
          closedIdentityComponent (torusGroup .E6 k ⊓ centralizer
            (E.map (MulAut.conj g).toMonoidHom : Set (ModGL .E6 k))) := by
  obtain ⟨g, hg, hc⟩ := connected_centralizer_conj_le_torus halg hEG hE hcard hnt
  refine ⟨g, hg, ?_⟩
  rw [← closedIdentityComponent_map_conj, map_adjoint_centralizer_conj E hg]
  have hle : torusGroup .E6 k ≤ adjointGroup .E6 k := torusGroup_le_adjointGroup
  have hinf : (adjointGroup .E6 k ⊓ centralizer
      (E.map (MulAut.conj g).toMonoidHom : Set (ModGL .E6 k))) ⊓ torusGroup .E6 k =
        torusGroup .E6 k ⊓ centralizer
          (E.map (MulAut.conj g).toMonoidHom : Set (ModGL .E6 k)) := by
    ext x
    exact ⟨fun ⟨⟨_, he⟩, ht⟩ => ⟨ht, he⟩, fun ⟨ht, he⟩ => ⟨⟨hle ht, he⟩, ht⟩⟩
  rw [← hinf]
  exact (closedIdentityComponent_inf_eq_of_le _ _ hc).symm

theorem card_weylImage_eq_three_of_connected_torus_point
    (hchar : ringChar k ≠ 3)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEM : E ≤ monomialSubgroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 k)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 k ⟨e,hEM he⟩ ∈ CFSG.StandardType.TableBExc.E6Three.modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 k ⟨e,hEM he⟩ ≠ CFSG.StandardType.TableBExc.E6Three.gE6 i)
    (htor : TauCeti.torusCommHopfAlgProperty k (TauCeti.FiniteTypeCommHopfAlgCat.of k
      (closedIdentityCoordinateRing (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))))))
    {x : ModGL .E6 k}
    (hx : x ∈ closedIdentityComponent (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))))
    (hx1 : x ≠ 1) :
    Nat.card ((E.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k)) = 3 := by
  rcases weylImage_card_cases hEM hcard hET with h3 | h9
  · exact h3
  · exfalso
    let Z := adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))
    let S := closedIdentityComponent Z
    let SP := S.map (modGLPoint .E6 k).toMonoidHom
    have hSP := (isConnectedAlgebraicSubgroup_closedIdentityComponent (isPointClosed_adjoint_centralizer E)).pointsZero_eq
    obtain ⟨y,hy,hpow⟩ := exists_pow_mem_of_torus SP hSP htor (by decide : 0 < 3)
      (mem_map_of_mem (modGLPoint .E6 k).toMonoidHom hx)
    obtain ⟨z,hz,rfl⟩ := hy
    have hzG : z ∈ adjointGroup .E6 k := (closedIdentityComponent_le Z hz).1
    have hzC : ∀ e ∈ E, z * e = e * z := fun e he =>
      (mem_centralizer_iff.mp (closedIdentityComponent_le Z hz).2 e he).symm
    have hzE : z ∈ E := mem_of_centralizer_of_nine hchar hEM hE hcard hET hAS hAg h9 hzG hzC
    have hz3 : z ^ 3 = 1 := hE.2 z hzE
    have hp : modGLPoint .E6 k x = 1 := hpow.symm.trans (by rw [← map_pow,hz3,map_one])
    exact hx1 ((modGLPoint .E6 k).injective (hp.trans (map_one _).symm))

theorem exists_weyl_generator_toral_part_eq_fixed_space
    {ζ : kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (ModGL .E6 k)}
    (hEM : E ≤ monomialSubgroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 k)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 k ⟨e,hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 k ⟨e,hEM he⟩ ≠ gE6 i)
    (hA3 : Nat.card ((E.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k)) = 3) :
    ∃ n : ModGL .E6 k, ∃ hnE : n ∈ E, ∃ w : WeylGroup .E6,
      weylQuotientHom .E6 k ⟨n,hEM hnE⟩ = w ∧ orderOf w = 3 ∧
      ((E.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k)) = zpowers w ∧
      ∀ x : ModGL .E6 k, x ∈ E ⊓ torusGroup .E6 k ↔
        ∃ v : Fin Tag.E6.rank → ZMod 3,
          adAct .E6 3 w v = v ∧ x = rootDiagUnit .E6 (zetaVec ζ hζ v) := by
  obtain ⟨A,hAc,hEA,hAr,hA,hA1,hAgA,n,hnE,w,hnw,hAw,hw3,hw1,hwi,hwinv⟩ :=
    exists_weylGenerator hEM hE hET hAS hAg hA3
  refine ⟨n,hnE,w,hnw,orderOf_eq_prime hw3 hw1,?_,?_⟩
  · have heq : A = ((E.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k)) := by
      ext u
      rw [hEA, Subgroup.mem_map]
      constructor
      · rintro ⟨e,he,hew⟩
        exact ⟨⟨e,hEM he⟩,he,hew⟩
      · rintro ⟨e,he,hew⟩
        exact ⟨e,he,hew⟩
    exact heq.symm.trans hAw
  · intro x
    constructor
    · intro hx
      obtain ⟨b,hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx.2
      have hb3 : b ^ 3 = 1 := by
        have h := hE.2 x hx.1
        rw [hb,rootDiagUnit_pow] at h
        exact rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
      obtain ⟨v,hv⟩ := exists_zetaVec_eq (p := 3) hζo hζ hb3
      have hvx : x = rootDiagUnit .E6 (zetaVec ζ hζ v) := hb.trans (congrArg (rootDiagUnit .E6) hv.symm)
      rw [hvx] at hx
      rw [hvx]
      refine ⟨v,?_,rfl⟩
      have hc := conj_rootDiagUnit_of_mem_monoHat
        (x := (⟨n,monomial_le_monoHat (hEM hnE)⟩ : monoHat .E6 k)) (zetaVec ζ hζ v)
      rw [psiHat_of_mem_monomial (hEM hnE),hnw,weylTuple_zetaVec] at hc
      have hecomm := hE.comm hnE hx.1
      have hconj : n * rootDiagUnit .E6 (zetaVec ζ hζ v) * n⁻¹ =
          rootDiagUnit .E6 (zetaVec ζ hζ v) := by rw [hecomm,mul_inv_cancel_right]
      have heq : rootDiagUnit .E6 (zetaVec ζ hζ (adAct .E6 3 w v)) =
          rootDiagUnit .E6 (zetaVec ζ hζ v) := hc.symm.trans hconj
      exact zetaVec_injective hζo hζ (rootDiagUnit_injective heq)
    · rintro ⟨v,hvw,rfl⟩
      have hvA : ∀ a ∈ A, adAct .E6 3 a v = v := by
        intro a ha
        rw [hAw] at ha
        obtain ⟨j,rfl⟩ := ha
        have hρ : adAct .E6 3 (w ^ j) v = v := by
          have hpow : ∀ j : ℕ, adAct .E6 3 (w ^ j) v = v := by
            intro j
            induction j with
            | zero => simpa using (adAct_one v : adAct .E6 3 1 v = v)
            | succ j ih => rw [pow_succ,adAct_mul,hvw,ih]
          rcases j with j | j
          · exact hpow j
          · rw [zpow_negSucc]
            change adAct .E6 3 (w ^ (j + 1))⁻¹ v = v
            have h : adAct .E6 3 (w ^ (j + 1))⁻¹ (adAct .E6 3 (w ^ (j + 1)) v) = v := by
              rw [← adAct_mul,inv_mul_cancel,adAct_one]
            rwa [hpow] at h
        exact hρ
      exact ⟨rootDiagUnit_zetaVec_mem hζo hζ hEM hE (le_of_eq hcard.symm) hEA hAr hA1 hAgA hvA,
        rootDiagUnit_mem_torusGroup _⟩

theorem exists_original_monomial_frame_of_connected_torus_point
    [CharP k 2]
    (halg : letI := ZMod.algebra k 2; Algebra.IsAlgebraic (ZMod 2) k)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E)
    {e : ModGL .E6 k}
    (heS : e ∈ closedIdentityComponent (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))))
    (he1 : e ≠ 1) :
    ∃ y₀ ∈ adjointGroup .E6 k,
      y₀ * e * y₀⁻¹ ∈ torusGroup .E6 k ∧
      closedIdentityComponent (adjointGroup .E6 k ⊓ centralizer
        (E.map (MulAut.conj y₀).toMonoidHom : Set (ModGL .E6 k))) ≤ torusGroup .E6 k ∧
      ∃ hEM : E.map (MulAut.conj y₀).toMonoidHom ≤ monomialSubgroup .E6 k,
        Nat.card (((E.map (MulAut.conj y₀).toMonoidHom).subgroupOf (monomialSubgroup .E6 k)).map
          (weylQuotientHom .E6 k)) = 3 ∧
        ∃ (ζ : kˣ) (_hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1),
          ∃ n : ModGL .E6 k, ∃ hnE : n ∈ E.map (MulAut.conj y₀).toMonoidHom,
          ∃ w : WeylGroup .E6,
            weylQuotientHom .E6 k ⟨n,hEM hnE⟩ = w ∧ orderOf w = 3 ∧
            (((E.map (MulAut.conj y₀).toMonoidHom).subgroupOf (monomialSubgroup .E6 k)).map
              (weylQuotientHom .E6 k)) = zpowers w ∧
            ∀ x : ModGL .E6 k,
              x ∈ E.map (MulAut.conj y₀).toMonoidHom ⊓ torusGroup .E6 k ↔
              ∃ v : Fin Tag.E6.rank → ZMod 3,
                adAct .E6 3 w v = v ∧ x = rootDiagUnit .E6 (zetaVec ζ hζ v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g,hg,hEM,hreg⟩ := exists_conj_regular (by decide : (2 : ℕ) ≠ 3) halg hEG
    (Set.toFinite (E : Set (ModGL .E6 k))) hE
  let E' := E.map (MulAut.conj g).toMonoidHom
  have hE' : CFSG.Open.IsElemAbelian 3 E' := hE.map _
  have hcard' : Nat.card E' = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have : Finite E' := Finite.of_surjective _ ((MulAut.conj g).toMonoidHom.subgroupMap_surjective E)
  have hET : ¬ E' ≤ torusGroup .E6 k := by
    intro h
    apply hnt
    apply (CFSG.StandardType.SCFourCover.e6AdToral_map_conj hg E).mp
    exact ⟨1,one_mem _,fun e he => by simpa using h he⟩
  have heS' : g * e * g⁻¹ ∈ closedIdentityComponent
      (adjointGroup .E6 k ⊓ centralizer (E' : Set (ModGL .E6 k))) := by
    rw [← map_adjoint_centralizer_conj E hg,closedIdentityComponent_map_conj]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom heS
  have he1' : g * e * g⁻¹ ≠ 1 := by
    intro h
    apply he1
    have h' : (MulAut.conj g) e = (MulAut.conj g) 1 := h.trans (map_one _).symm
    exact (MulAut.conj g).injective h'
  have hEG' : E' ≤ adjointGroup .E6 k := by
    rintro x ⟨a,ha,rfl⟩
    exact mul_mem (mul_mem hg (hEG ha)) (inv_mem hg)
  have ht := torus_original_connected_centralizer halg hEG' hE' hcard'
    (fun h => hnt ((CFSG.StandardType.SCFourCover.e6AdToral_map_conj hg E).mp h))
  have hchar : ringChar k ≠ 3 := by rw [ringChar.eq k 2]; decide
  have hA3 := card_weylImage_eq_three_of_connected_torus_point hchar hEM hE' hcard' hET
    (fun a ha => (hreg a ha).1) (fun a ha i => (hreg a ha).2 i) ht heS' he1'
  have hST := connected_centralizer_le_torus_of_regular hchar hEM hE' hcard' hET
    (fun a ha => (hreg a ha).1) (fun a ha i => (hreg a ha).2 i)
  have heT : g * e * g⁻¹ ∈ torusGroup .E6 k := hST heS'
  have h3 : (3 : k) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime k Nat.prime_three (by decide)
  obtain ⟨ζ,hζo⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed h3
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  obtain ⟨n,hn,w,hnw,hw,hA,hpart⟩ := exists_weyl_generator_toral_part_eq_fixed_space hζo hζ hEM hE'
    hcard' hET (fun a ha => (hreg a ha).1) (fun a ha i => (hreg a ha).2 i) hA3
  exact ⟨g,hg,heT,hST,hEM,hA3,ζ,hζo,hζ,n,hn,w,hnw,hw,hA,hpart⟩

omit [IsAlgClosed k] in
theorem weylImage_hyperplane_eq_of_toral_complement
    {E H : Subgroup (ModGL .E6 k)} (hEM : E ≤ monomialSubgroup .E6 k)
    (e : ModGL .E6 k) (hE : E = H ⊔ zpowers e) (heT : e ∈ torusGroup .E6 k) :
    (H.subgroupOf (monomialSubgroup .E6 k)).map (CFSG.LieType.Chevalley.weylQuotientHom .E6 k) =
      (E.subgroupOf (monomialSubgroup .E6 k)).map (CFSG.LieType.Chevalley.weylQuotientHom .E6 k) := by
  let M := monomialSubgroup .E6 k
  let W := CFSG.LieType.Chevalley.weylQuotientHom .E6 k
  have heE : e ∈ E := by rw [hE]; exact mem_sup_right (mem_zpowers e)
  have heM : e ∈ M := hEM heE
  have hHM : H ≤ M := by
    apply le_trans (show H ≤ E from by rw [hE]; exact le_sup_left) hEM
  let em : M := ⟨e,heM⟩
  have heK : em ∈ W.ker := by
    rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2]
    exact heT
  have hs : E.subgroupOf M = H.subgroupOf M ⊔ zpowers em := by
    rw [hE]
    have heZ : zpowers e ≤ M := zpowers_le.mpr heM
    have hs' := Subgroup.subgroupOf_sup hHM heZ
    rw [hs']
    congr 1
    ext x
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨j,Subtype.ext hj⟩
    · rintro ⟨j,hj⟩
      exact ⟨j,congrArg Subtype.val hj⟩
  rw [hs,Subgroup.map_sup,MonoidHom.map_zpowers,show W em = 1 from heK]
  simp only [Subgroup.zpowers_one_eq_bot, sup_bot_eq]
  rfl

omit [IsAlgClosed k] in
theorem monomial_subgroup_eq_toral_sup_zpowers
    (H : Subgroup (ModGL .E6 k)) (hHM : H ≤ monomialSubgroup .E6 k)
    {x : ModGL .E6 k} (hxH : x ∈ H)
    (hgen : (H.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k) =
      zpowers (weylQuotientHom .E6 k ⟨x,hHM hxH⟩)) :
    H = H ⊓ torusGroup .E6 k ⊔ zpowers x := by
  let W := weylQuotientHom .E6 k
  let ρ : H →* WeylGroup .E6 := W.comp (Subgroup.inclusion hHM)
  have hρ : ρ.range = (H.subgroupOf (monomialSubgroup .E6 k)).map W := by
    ext w
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨⟨a,hHM a.2⟩,a.2,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  have hker : ρ.ker.map H.subtype = H ⊓ torusGroup .E6 k := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      refine ⟨b.2,?_⟩
      have hb' : (⟨(b : ModGL .E6 k),hHM b.2⟩ : monomialSubgroup .E6 k) ∈ W.ker := hb
      rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2] at hb'
      exact hb'
    · intro ha
      refine ⟨⟨a,ha.1⟩,?_,rfl⟩
      change (⟨a,hHM ha.1⟩ : monomialSubgroup .E6 k) ∈ W.ker
      rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2]
      exact ha.2
  have h : (⊤ : Subgroup H) = ρ.ker ⊔ zpowers (⟨x,hxH⟩ : H) := by
    apply CFSG.FiveTransitive.KernelImageGeneration.eq_of_kernel_image ρ ⊤ _ le_top
    · simp
    · rw [Subgroup.map_top,hρ,hgen]
      have h := Subgroup.map_mono (f := ρ) (le_sup_right : zpowers (⟨x,hxH⟩ : H) ≤
        ρ.ker ⊔ zpowers (⟨x,hxH⟩ : H))
      rw [MonoidHom.map_zpowers] at h
      exact h
  have hm := congrArg (Subgroup.map H.subtype) h
  rw [Subgroup.map_top,Subgroup.range_subtype,Subgroup.map_sup,hker,MonoidHom.map_zpowers] at hm
  exact hm
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three

theorem toral_plane_closure_eq
    (H : Subgroup (ModGL .E6 k)) (hH : CFSG.Open.IsElemAbelian 3 H)
    {ζ : kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Subgroup.closure ((fun v : Fin Tag.E6.rank → ZMod 3 => rootDiagUnit .E6 (zetaVec ζ hζ v)) ''
      (CFSG.StandardType.E6ThreeEnd.expE ζ hζ H : Set (Fin Tag.E6.rank → ZMod 3))) =
        H ⊓ torusGroup .E6 k := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro y ⟨v,hv,rfl⟩
    exact ⟨(CFSG.StandardType.E6ThreeEnd.mem_expE).mp hv,rootDiagUnit_mem_torusGroup _⟩
  · intro x hx
    obtain ⟨b,hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx.2
    have hb3 : b ^ 3 = 1 := by
      have h := hH.2 x hx.1
      rw [hb,rootDiagUnit_pow] at h
      exact rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
    obtain ⟨v,hv⟩ := exists_zetaVec_eq (p := 3) hζo hζ hb3
    have hvx : x = rootDiagUnit .E6 (zetaVec ζ hζ v) := hb.trans (congrArg (rootDiagUnit .E6) hv.symm)
    apply Subgroup.subset_closure
    exact ⟨v,(CFSG.StandardType.E6ThreeEnd.mem_expE).mpr (hvx ▸ hx.1),hvx.symm⟩

theorem monomial_subgroup_eq_closure_toral_plane_union_generator
    (H : Subgroup (ModGL .E6 k)) (hHM : H ≤ monomialSubgroup .E6 k)
    (hH : CFSG.Open.IsElemAbelian 3 H)
    {x : ModGL .E6 k} (hxH : x ∈ H)
    (hgen : (H.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k) =
      zpowers (weylQuotientHom .E6 k ⟨x,hHM hxH⟩))
    {ζ : kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    H = Subgroup.closure
      ((fun v : Fin Tag.E6.rank → ZMod 3 => rootDiagUnit .E6 (zetaVec ζ hζ v)) ''
        (CFSG.StandardType.E6ThreeEnd.expE ζ hζ H : Set (Fin Tag.E6.rank → ZMod 3)) ∪ {x}) := by
  rw [Subgroup.closure_union,toral_plane_closure_eq H hH hζo hζ,← Subgroup.zpowers_eq_closure]
  exact monomial_subgroup_eq_toral_sup_zpowers H hHM hxH hgen

omit [IsAlgClosed k] in
theorem card_expE_eq_nine_of_card_twenty_seven
    (H : Subgroup (ModGL .E6 k)) [Finite H] (hHM : H ≤ monomialSubgroup .E6 k)
    (hH : CFSG.Open.IsElemAbelian 3 H) (hcard : Nat.card H = 27)
    (hW : Nat.card ((H.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k)) = 3)
    {ζ : kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Nat.card (CFSG.StandardType.E6ThreeEnd.expE ζ hζ H) = 9 := by
  let A := (H.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k)
  have hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ H, weylQuotientHom .E6 k ⟨e,hHM he⟩ = w := by
    intro w
    constructor
    · rintro ⟨e,he,rfl⟩
      exact ⟨e,he,rfl⟩
    · rintro ⟨e,he,rfl⟩
      exact ⟨⟨e,hHM he⟩,he,rfl⟩
  have hc := card_E_eq_card_A_mul_card_expE hζo hζ hHM hH hEA
  rw [hcard,hW] at hc
  omega
omit [IsAlgClosed k] in
theorem finrank_expE_eq_two_of_card_twenty_seven
    (H : Subgroup (ModGL .E6 k)) [Finite H] (hHM : H ≤ monomialSubgroup .E6 k)
    (hH : CFSG.Open.IsElemAbelian 3 H) (hcard : Nat.card H = 27)
    (hW : Nat.card ((H.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k)) = 3)
    {ζ : kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Module.finrank (ZMod 3) (AddSubgroup.toZModSubmodule 3
      (CFSG.StandardType.E6ThreeEnd.expE ζ hζ H)) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card (AddSubgroup.toZModSubmodule 3
      (CFSG.StandardType.E6ThreeEnd.expE ζ hζ H)) = 9 := by
    have h := card_expE_eq_nine_of_card_twenty_seven H hHM hH hcard hW hζo hζ
    let e : (AddSubgroup.toZModSubmodule 3 (CFSG.StandardType.E6ThreeEnd.expE ζ hζ H)) ≃
        CFSG.StandardType.E6ThreeEnd.expE ζ hζ H :=
      { toFun := fun x => ⟨x, (AddSubgroup.mem_toZModSubmodule 3).mp x.2⟩
        invFun := fun x => ⟨x, (AddSubgroup.mem_toZModSubmodule 3).mpr x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans h
  have hpow := FiniteField.pow_finrank_eq_natCard 3
    (AddSubgroup.toZModSubmodule 3 (CFSG.StandardType.E6ThreeEnd.expE ζ hζ H))
  rw [hc] at hpow
  exact (Nat.pow_right_injective (by decide : 1 < 3))
    (hpow.trans (by norm_num : (9 : ℕ) = 3 ^ 2))

omit [IsAlgClosed k] in
theorem expE_fixed_by_weyl_generator
    (H : Subgroup (ModGL .E6 k)) (hHM : H ≤ monomialSubgroup .E6 k)
    (hH : CFSG.Open.IsElemAbelian 3 H)
    {x : ModGL .E6 k} (hxH : x ∈ H)
    {w : WeylGroup .E6} (hxw : weylQuotientHom .E6 k ⟨x,hHM hxH⟩ = w)
    {ζ : kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    ∀ v ∈ CFSG.StandardType.E6ThreeEnd.expE ζ hζ H, adAct .E6 3 w v = v := by
  intro v hv
  have hdH : rootDiagUnit .E6 (zetaVec ζ hζ v) ∈ H := (CFSG.StandardType.E6ThreeEnd.mem_expE).mp hv
  have hc := conj_rootDiagUnit_of_mem_monoHat
    (x := (⟨x,monomial_le_monoHat (hHM hxH)⟩ : monoHat .E6 k)) (zetaVec ζ hζ v)
  rw [psiHat_of_mem_monomial (hHM hxH),hxw,weylTuple_zetaVec] at hc
  have hcomm := hH.comm hxH hdH
  have hdconj : x * rootDiagUnit .E6 (zetaVec ζ hζ v) * x⁻¹ = rootDiagUnit .E6 (zetaVec ζ hζ v) := by
    rw [hcomm,mul_inv_cancel_right]
  have hEq : rootDiagUnit .E6 (zetaVec ζ hζ (adAct .E6 3 w v)) = rootDiagUnit .E6 (zetaVec ζ hζ v) := hc.symm.trans hdconj
  exact zetaVec_injective hζo hζ (rootDiagUnit_injective hEq)

theorem exists_hyperplane_toral_plane_and_weyl_generator
    (E H : Subgroup (ModGL .E6 k)) [Finite H]
    (hEM : E ≤ monomialSubgroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hHcard : Nat.card H = 27)
    (e : ModGL .E6 k) (hsplit : E = H ⊔ zpowers e) (heT : e ∈ torusGroup .E6 k)
    (w : WeylGroup .E6) (hw : orderOf w = 3)
    (hW : (E.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k) = zpowers w)
    {ζ : kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    ∃ x : ModGL .E6 k, ∃ hxH : x ∈ H, x ^ 3 = 1 ∧
      weylQuotientHom .E6 k ⟨x,hEM (by rw [hsplit]; exact mem_sup_left hxH)⟩ = w ∧
      ∃ V : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3),
        Module.finrank (ZMod 3) V = 2 ∧
        (∀ v ∈ V, adAct .E6 3 w v = v) ∧
        H = Subgroup.closure ((fun v => rootDiagUnit .E6 (zetaVec ζ hζ v)) ''
          (V : Set (Fin Tag.E6.rank → ZMod 3)) ∪ {x}) := by
  have hHE : H ≤ E := by rw [hsplit];exact le_sup_left
  have hHM : H ≤ monomialSubgroup .E6 k := hHE.trans hEM
  have hH : CFSG.Open.IsElemAbelian 3 H := hE.mono hHE
  have hWH := weylImage_hyperplane_eq_of_toral_complement hEM e hsplit heT
  rw [hW] at hWH
  have hwH : w ∈ (H.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k) := by
    rw [hWH];exact mem_zpowers w
  obtain ⟨x,hx,hwx⟩ := hwH
  have hxH : (x : ModGL .E6 k) ∈ H := hx
  have hx3 : (x : ModGL .E6 k) ^ 3 = 1 := hH.2 x hxH
  let V := AddSubgroup.toZModSubmodule 3 (CFSG.StandardType.E6ThreeEnd.expE ζ hζ H)
  have hcardW : Nat.card ((H.subgroupOf (monomialSubgroup .E6 k)).map (weylQuotientHom .E6 k)) = 3 := by
    rw [hWH,Nat.card_zpowers,hw]
  have hrank := finrank_expE_eq_two_of_card_twenty_seven H hHM hH hHcard hcardW hζo hζ
  have hfix : ∀ v ∈ V, adAct .E6 3 w v = v := by
    intro v hv
    exact expE_fixed_by_weyl_generator H hHM hH hxH hwx hζo hζ v
      ((AddSubgroup.mem_toZModSubmodule 3).mp hv)
  have hgen := monomial_subgroup_eq_closure_toral_plane_union_generator H hHM hH hxH
    (hWH.trans (congrArg zpowers hwx.symm)) hζo hζ
  have hV : (V : Set (Fin Tag.E6.rank → ZMod 3)) =
      (CFSG.StandardType.E6ThreeEnd.expE ζ hζ H : Set (Fin Tag.E6.rank → ZMod 3)) :=
    AddSubgroup.coe_toZModSubmodule 3 _
  rw [← hV] at hgen
  exact ⟨x,hxH,hx3,hwx,V,hrank,hfix,hgen⟩

end E6
end CFSG.LieType.AlgebraicGroups

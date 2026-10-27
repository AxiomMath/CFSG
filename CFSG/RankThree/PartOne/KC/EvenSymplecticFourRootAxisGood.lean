module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open Matrix

abbrev SL₂ (K : Type) [Field K] : Type := Matrix.SpecialLinearGroup (Fin 2) K

section Generic

variable {G : Type*} [Group G] {K : Type} [Field K]

structure RootAxisStructure (U A : Subgroup G) (s : SL₂ K →* G) (d : Kˣ →* G) (coord : K → G)
    (vec : G → Fin 2 → K) : Prop where
  A_le_C : A ≤ Subgroup.centralizer (U : Set G)
  s_mem_C : ∀ M : SL₂ K, s M ∈ Subgroup.centralizer (U : Set G)
  A_normal_C : ∀ g ∈ Subgroup.centralizer (U : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A
  C_decomp : ∀ g ∈ Subgroup.centralizer (U : Set G), ∃ a ∈ A, ∃ M : SL₂ K, g = a * s M
  C_unique : ∀ a ∈ A, ∀ a' ∈ A, ∀ M M' : SL₂ K, a * s M = a' * s M' → a = a' ∧ M = M'
  C_perfect : Group.IsPerfect (Subgroup.centralizer (U : Set G))
  C_pCore : CFSG.pCore 2 (Subgroup.centralizer (U : Set G)) =
    A.subgroupOf (Subgroup.centralizer (U : Set G))
  N_eq : Subgroup.normalizer (U : Set G) = Subgroup.normalizer (A : Set G)
  A_le_N : A ≤ Subgroup.normalizer (U : Set G)
  ds_mem_N : ∀ (l : Kˣ) (M : SL₂ K), d l * s M ∈ Subgroup.normalizer (U : Set G)
  A_normal_N : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A
  s_comm_d : ∀ (M : SL₂ K) (l : Kˣ), s M * d l = d l * s M
  N_decomp : ∀ g ∈ Subgroup.normalizer (U : Set G),
    ∃ a ∈ A, ∃ (l : Kˣ) (M : SL₂ K), g = a * (d l * s M)
  N_unique : ∀ a ∈ A, ∀ a' ∈ A, ∀ (l l' : Kˣ) (M M' : SL₂ K),
    a * (d l * s M) = a' * (d l' * s M') → a = a' ∧ l = l' ∧ M = M'
  quot_bijective : ∃ hs : ∀ M : SL₂ K, s M ∈ Subgroup.centralizer (U : Set G),
    Function.Bijective (fun M : SL₂ K =>
      (QuotientGroup.mk ⟨s M, hs M⟩ :
        Subgroup.centralizer (U : Set G) ⧸ A.subgroupOf (Subgroup.centralizer (U : Set G))))
  S_center : Subgroup.center (SL₂ K) = ⊥
  S_perfect : Group.IsPerfect (SL₂ K)
  S_pCore : CFSG.pCore 2 (SL₂ K) = ⊥
  coord_mem : ∀ x : K, coord x ∈ U
  coord_surj : ∀ z ∈ U, ∃ x : K, coord x = z
  vec_add : ∀ z ∈ A, ∀ w ∈ A, vec (z * w) = vec z + vec w
  vec_surj : ∀ v : Fin 2 → K, ∃ z ∈ A, vec z = v
  vec_ker : ∀ z ∈ A, (vec z = 0 ↔ z ∈ U)
  vec_conj : ∀ (M : SL₂ K) (z : G), z ∈ A →
    vec (s M * z * (s M)⁻¹) = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ vec z
  normal_eq_A : ∀ V : Subgroup G, V ≤ Subgroup.centralizer (U : Set G) →
    (∀ g ∈ Subgroup.centralizer (U : Set G), ∀ v ∈ V, g * v * g⁻¹ ∈ V) → V ≤ A → ¬ V ≤ U →
      V = A
  d_coord : ∀ (l : Kˣ) (x : K), d l * coord x * (d l)⁻¹ = coord ((l : K) ^ 2 * x)

end Generic

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem mem_centralizer_map (φ : G ≃* G') (U : Subgroup G) (g : G') :
    g ∈ Subgroup.centralizer ((U.map φ.toMonoidHom : Subgroup G') : Set G') ↔
      φ.symm g ∈ Subgroup.centralizer (U : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h u hu
    apply φ.injective
    simpa using h (φ u) (Subgroup.mem_map_of_mem _ hu)
  · intro h u' hu'
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
    have := congrArg φ (h u hu)
    simpa [map_mul] using this

theorem mem_normalizer_map (φ : G ≃* G') (H : Subgroup G) (g : G') :
    g ∈ Subgroup.normalizer ((H.map φ.toMonoidHom : Subgroup G') : Set G') ↔
      φ.symm g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  simp only [Subgroup.mem_map_equiv, map_mul, map_inv]
  constructor
  · intro h x
    simpa using h (φ x)
  · intro h x
    have := h (φ.symm x)
    simpa using this

@[expose] def subgroupEquiv (φ : G ≃* G') {C : Subgroup G} {C' : Subgroup G'}
    (h : ∀ g, g ∈ C ↔ φ g ∈ C') : C ≃* C' where
  toFun x := ⟨φ x, (h x).mp x.2⟩
  invFun y := ⟨φ.symm y, by rw [h]; simp⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply _)
  right_inv y := Subtype.ext (φ.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul φ _ _)

theorem subgroupEquiv_apply_coe (φ : G ≃* G') {C : Subgroup G} {C' : Subgroup G'}
    (h : ∀ g, g ∈ C ↔ φ g ∈ C') (x : C) : ((subgroupEquiv φ h x : C') : G') = φ x :=
  rfl

theorem isPerfect_of_mulEquiv (e : G ≃* G') (h : Group.IsPerfect G) : Group.IsPerfect G' := by
  refine ⟨?_⟩
  have h1 := h.commutator_eq_top
  rw [commutator_def] at h1 ⊢
  have h2 := congrArg (Subgroup.map e.toMonoidHom) h1
  rw [Subgroup.map_commutator, Subgroup.map_top,
    MonoidHom.range_eq_top_of_surjective _ e.surjective] at h2
  exact h2

end Transport

section Map

variable {G G' : Type*} [Group G] [Group G'] {K : Type} [Field K]

theorem RootAxisStructure.map {U A : Subgroup G} {s : SL₂ K →* G} {d : Kˣ →* G} {coord : K → G}
    {vec : G → Fin 2 → K} (h : RootAxisStructure U A s d coord vec) (φ : G ≃* G') :
    RootAxisStructure (U.map φ.toMonoidHom) (A.map φ.toMonoidHom) (φ.toMonoidHom.comp s)
      (φ.toMonoidHom.comp d) (fun x => φ (coord x)) (fun z => vec (φ.symm z)) := by
  have hC : ∀ g, g ∈ Subgroup.centralizer (U : Set G) ↔
      φ g ∈ Subgroup.centralizer ((U.map φ.toMonoidHom : Subgroup G') : Set G') := fun g => by
    rw [mem_centralizer_map, φ.symm_apply_apply]
  have hN : ∀ g, g ∈ Subgroup.normalizer (U : Set G) ↔
      φ g ∈ Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup G') : Set G') := fun g => by
    rw [mem_normalizer_map, φ.symm_apply_apply]
  have hA : ∀ g, g ∈ A ↔ φ g ∈ A.map φ.toMonoidHom := fun g => by
    rw [Subgroup.mem_map_equiv, φ.symm_apply_apply]
  have hU : ∀ g, g ∈ U ↔ φ g ∈ U.map φ.toMonoidHom := fun g => by
    rw [Subgroup.mem_map_equiv, φ.symm_apply_apply]
  have hC' : ∀ g', g' ∈ Subgroup.centralizer ((U.map φ.toMonoidHom : Subgroup G') : Set G') ↔
      φ.symm g' ∈ Subgroup.centralizer (U : Set G) := mem_centralizer_map φ U
  have hN' : ∀ g', g' ∈ Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup G') : Set G') ↔
      φ.symm g' ∈ Subgroup.normalizer (U : Set G) := mem_normalizer_map φ U
  have hA' : ∀ g', g' ∈ A.map φ.toMonoidHom ↔ φ.symm g' ∈ A := fun g' =>
    Subgroup.mem_map_equiv
  have hU' : ∀ g', g' ∈ U.map φ.toMonoidHom ↔ φ.symm g' ∈ U := fun g' =>
    Subgroup.mem_map_equiv
  have hAnC : ∀ g' ∈ Subgroup.centralizer ((U.map φ.toMonoidHom : Subgroup G') : Set G'),
      ∀ a' ∈ A.map φ.toMonoidHom, g' * a' * g'⁻¹ ∈ A.map φ.toMonoidHom := by
    intro g' hg' a' ha'
    have := h.A_normal_C (φ.symm g') ((hC' g').mp hg') (φ.symm a') ((hA' a').mp ha')
    have h2 := (hA _).mp this
    simpa using h2
  refine
    { A_le_C := fun x hx => (hC' x).mpr (h.A_le_C ((hA' x).mp hx))
      s_mem_C := fun M => (hC _).mp (h.s_mem_C M)
      A_normal_C := hAnC
      C_decomp := fun g hg => ?_
      C_unique := fun a ha a' ha' M M' hMM => ?_
      C_perfect := isPerfect_of_mulEquiv (subgroupEquiv φ hC) h.C_perfect
      C_pCore := ?_
      N_eq := ?_
      A_le_N := fun x hx => (hN' x).mpr (h.A_le_N ((hA' x).mp hx))
      ds_mem_N := fun l M => ?_
      A_normal_N := fun g hg a ha => ?_
      s_comm_d := fun M l => ?_
      N_decomp := fun g hg => ?_
      N_unique := fun a ha a' ha' l l' M M' hMM => ?_
      quot_bijective := ?_
      S_center := h.S_center
      S_perfect := h.S_perfect
      S_pCore := h.S_pCore
      coord_mem := fun x => (hU _).mp (h.coord_mem x)
      coord_surj := fun z hz => ?_
      vec_add := fun z hz w hw => ?_
      vec_surj := fun v => ?_
      vec_ker := fun z hz => ?_
      vec_conj := fun M z hz => ?_
      normal_eq_A := fun V hVC hVn hVA hVU => ?_
      d_coord := fun l x => ?_ }
  ·
    obtain ⟨a, ha, M, hgM⟩ := h.C_decomp (φ.symm g) ((hC' g).mp hg)
    refine ⟨φ a, (hA a).mp ha, M, ?_⟩
    have := congrArg φ hgM
    simpa using this
  ·
    obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨α', hα', rfl⟩ := Subgroup.mem_map.mp ha'
    have h1 : α * s M = α' * s M' := by
      apply φ.injective
      simpa using hMM
    obtain ⟨e1, e2⟩ := h.C_unique α hα α' hα' M M' h1
    exact ⟨by simp [e1], e2⟩
  ·
    ext x
    have e := pCore_map_iso 2 (subgroupEquiv φ hC)
    rw [← e, Subgroup.mem_map_equiv, h.C_pCore, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      hA' (x : G')]
    rfl
  ·
    ext g'
    rw [hN', h.N_eq, ← mem_normalizer_map φ A g']
  · show φ (d l) * φ (s M) ∈ _
    rw [← map_mul]
    exact (hN _).mp (h.ds_mem_N l M)
  · have := h.A_normal_N (φ.symm g) ((hN' g).mp hg) (φ.symm a) ((hA' a).mp ha)
    have h2 := (hA _).mp this
    simpa using h2
  · show φ (s M) * φ (d l) = φ (d l) * φ (s M)
    rw [← map_mul, ← map_mul, h.s_comm_d]
  · obtain ⟨a, ha, l, M, hgM⟩ := h.N_decomp (φ.symm g) ((hN' g).mp hg)
    refine ⟨φ a, (hA a).mp ha, l, M, ?_⟩
    have := congrArg φ hgM
    simpa using this
  · obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨α', hα', rfl⟩ := Subgroup.mem_map.mp ha'
    have h1 : α * (d l * s M) = α' * (d l' * s M') := by
      apply φ.injective
      simpa using hMM
    obtain ⟨e1, e2, e3⟩ := h.N_unique α hα α' hα' l l' M M' h1
    exact ⟨by simp [e1], e2, e3⟩
  ·
    obtain ⟨hs, hbij⟩ := h.quot_bijective
    refine ⟨fun M => (hC _).mp (hs M), ?_⟩
    have hnorm : (A.subgroupOf (Subgroup.centralizer (U : Set G))).Normal :=
      ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        simpa using h.A_normal_C g g.2 n hn⟩
    have hnorm' : ((A.map φ.toMonoidHom).subgroupOf
        (Subgroup.centralizer ((U.map φ.toMonoidHom : Subgroup G') : Set G'))).Normal :=
      ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hAnC g g.2 n hn⟩
    have hmap : (A.subgroupOf (Subgroup.centralizer (U : Set G))).map
        (subgroupEquiv φ hC).toMonoidHom = (A.map φ.toMonoidHom).subgroupOf
          (Subgroup.centralizer ((U.map φ.toMonoidHom : Subgroup G') : Set G')) := by
      ext x
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        hA' (x : G')]
      rfl
    let q := QuotientGroup.congr (A.subgroupOf (Subgroup.centralizer (U : Set G)))
      ((A.map φ.toMonoidHom).subgroupOf
        (Subgroup.centralizer ((U.map φ.toMonoidHom : Subgroup G') : Set G')))
      (subgroupEquiv φ hC) hmap
    exact q.bijective.comp hbij
  · obtain ⟨x, hx⟩ := h.coord_surj (φ.symm z) ((hU' z).mp hz)
    exact ⟨x, by simp [hx]⟩
  · simpa using h.vec_add (φ.symm z) ((hA' z).mp hz) (φ.symm w) ((hA' w).mp hw)
  · obtain ⟨z, hz, hzv⟩ := h.vec_surj v
    exact ⟨φ z, (hA z).mp hz, by simpa using hzv⟩
  · rw [(hU' z)]
    exact h.vec_ker (φ.symm z) ((hA' z).mp hz)
  · have := h.vec_conj M (φ.symm z) ((hA' z).mp hz)
    simpa using this
  ·
    set W : Subgroup G := V.comap φ.toMonoidHom with hW
    have hmemW : ∀ x, x ∈ W ↔ φ x ∈ V := fun x => Iff.rfl
    have hWV : W.map φ.toMonoidHom = V :=
      Subgroup.map_comap_eq_self_of_surjective φ.surjective V
    have hWC : W ≤ Subgroup.centralizer (U : Set G) := fun x hx => (hC x).mpr (hVC hx)
    have hWn : ∀ g ∈ Subgroup.centralizer (U : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
      intro g hg w hw
      rw [hmemW, map_mul, map_mul, map_inv]
      exact hVn (φ g) ((hC g).mp hg) (φ w) hw
    have hWA : W ≤ A := fun x hx => (hA x).mpr (hVA hx)
    have hWU : ¬ W ≤ U := fun hle => hVU (fun x' hx' => by
      have hx : φ.symm x' ∈ W := by rw [hmemW]; simpa using hx'
      exact (hU' x').mpr (hle hx))
    have := h.normal_eq_A W hWC hWn hWA hWU
    calc V = W.map φ.toMonoidHom := hWV.symm
      _ = A.map φ.toMonoidHom := by rw [this]
  · show φ (d l) * φ (coord x) * (φ (d l))⁻¹ = φ (coord ((l : K) ^ 2 * x))
    rw [← map_inv, ← map_mul, ← map_mul, h.d_coord]

theorem RootAxisStructure.map' {U A : Subgroup G} {s : SL₂ K →* G} {d : Kˣ →* G}
    {coord : K → G} {vec : G → Fin 2 → K} (h : RootAxisStructure U A s d coord vec)
    (φ : G ≃* G') {U' A' : Subgroup G'} {s' : SL₂ K →* G'} {d' : Kˣ →* G'} {coord' : K → G'}
    {vec' : G' → Fin 2 → K} (hU : U' = U.map φ.toMonoidHom) (hA : A' = A.map φ.toMonoidHom)
    (hs : ∀ M, s' M = φ (s M)) (hd : ∀ l, d' l = φ (d l)) (hc : ∀ x, coord' x = φ (coord x))
    (hv : ∀ z, vec' z = vec (φ.symm z)) : RootAxisStructure U' A' s' d' coord' vec' := by
  have hs' : s' = φ.toMonoidHom.comp s := MonoidHom.ext hs
  have hd' : d' = φ.toMonoidHom.comp d := MonoidHom.ext hd
  have hc' : coord' = fun x => φ (coord x) := funext hc
  have hv' : vec' = fun z => vec (φ.symm z) := funext hv
  subst hU hA hs' hd' hc' hv'
  exact h.map φ

end Map

end KCRootAxis

end CFSG.RankThree.PartOne

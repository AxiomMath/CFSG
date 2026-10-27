module

public import CFSG.RankThree.Lattice.SteinbergBIGenOrbitMaps
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitRankOne

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem map_conj_fixedRootSpan {w : WeylGroup τ} {x : adjointGroup τ k}
    (hxN : (x : ModGL τ k) ∈ monomialSubgroup τ k) (hxw : weylQuotientHom τ k ⟨_, hxN⟩ = w)
    (hxF : D.F x = x) {S : Set (Fin τ.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot τ γ) :
    (D.fixedRootSpan S).map (MulAut.conj x).toMonoidHom =
      D.fixedRootSpan ((fun γ => w • γ) '' S) := by
  have h1 := map_conj_rootSpan_of_mem_monomialSubgroup hxN hS
  rw [hxw] at h1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyU, hyF⟩ := D.mem_fixedRootSpan.1 hy
    refine D.mem_fixedRootSpan.2 ⟨?_, ?_⟩
    · rw [← h1]
      exact ⟨y, hyU, rfl⟩
    · show D.F (x * y * x⁻¹) = x * y * x⁻¹
      rw [map_mul, map_mul, map_inv, hxF, hyF]
  · intro hz
    obtain ⟨hzU, hzF⟩ := D.mem_fixedRootSpan.1 hz
    rw [← h1] at hzU
    obtain ⟨y', hy', hyz⟩ := hzU
    refine ⟨x⁻¹ * z * x, D.mem_fixedRootSpan.2 ⟨?_, ?_⟩, ?_⟩
    · have e : ((x⁻¹ * z * x : adjointGroup τ k) : ModGL τ k) = y' := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hyz]
        show (x : ModGL τ k)⁻¹ * ((x : ModGL τ k) * y' * (x : ModGL τ k)⁻¹) * x = y'
        group
      rw [e]
      exact hy'
    · rw [map_mul, map_mul, map_inv, hxF, hzF]
    · show x * (x⁻¹ * z * x) * x⁻¹ = z
      group

theorem exists_mulEquiv_fixedRootSpan {w : WeylGroup τ} {x : adjointGroup τ k}
    (hxN : (x : ModGL τ k) ∈ monomialSubgroup τ k) (hxw : weylQuotientHom τ k ⟨_, hxN⟩ = w)
    (hxF : D.F x = x) {S : Set (Fin τ.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot τ γ) :
    ∃ e : D.fixedRootSpan S ≃* D.fixedRootSpan ((fun γ => w • γ) '' S),
      ∀ y, (e y : adjointGroup τ k) = x * y * x⁻¹ :=
  ⟨((MulAut.conj x).subgroupMap (D.fixedRootSpan S)).trans
    (MulEquiv.subgroupCongr (D.map_conj_fixedRootSpan hxN hxw hxF hS)), fun _ => rfl⟩

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem range_orbitX {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Set.range (D.orbitX O) = Subtype.val '' (D.fixedRootSpan O : Set (adjointGroup τ k)) := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, D.orbitX_mem_fixedRootSpan hO c, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact D.exists_orbitX_eq hO hy

theorem orbitN_fixed {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.F ⟨D.orbitN O, D.orbitMap_mem_adjointGroup O _⟩ =
      ⟨D.orbitN O, D.orbitMap_mem_adjointGroup O _⟩ :=
  D.F_orbitMap hO _ rfl

theorem orbitY_eq {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (c : D.orbitField O) :
    D.orbitY O c = D.orbitN O * D.orbitX O (-c) * (D.orbitN O)⁻¹ := by
  have h := congrArg (D.orbitMapHom hO) (vSL_eq c)
  rw [map_mul, map_mul, map_inv] at h
  exact h

theorem neg_image_eq {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    (fun γ => setReflection O • γ) '' O = (fun γ => -γ) '' O :=
  D.image_setReflection_self hO

theorem range_orbitY {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Set.range (D.orbitY O) =
      Subtype.val '' (D.fixedRootSpan ((fun γ => -γ) '' O) : Set (adjointGroup τ k)) := by
  set xN : adjointGroup τ k := ⟨D.orbitN O, D.orbitMap_mem_adjointGroup O _⟩ with hxN
  have hmap := D.map_conj_fixedRootSpan (x := xN) (D.orbitN_mem_monomialSubgroup hO).1
    (D.weylQuotientHom_orbitN hO) (D.orbitN_fixed hO) (S := O)
    (fun γ hγ => D.isRoot_of_mem_orbits hO hγ)
  rw [D.neg_image_eq hO] at hmap
  rw [← hmap]
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨xN * ⟨D.orbitX O (-c), D.orbitMap_mem_adjointGroup O _⟩ * xN⁻¹,
      ⟨_, D.orbitX_mem_fixedRootSpan hO (-c), rfl⟩, ?_⟩
    rw [D.orbitY_eq hO]
    rfl
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := D.exists_orbitX_eq hO hy
    refine ⟨-c, ?_⟩
    rw [D.orbitY_eq hO, neg_neg, hc]
    rfl

@[expose] def IsOrbitLift (n : ModGL τ k) (w : WeylGroup τ) : Prop :=
  ∃ l, D.IsOrbitWord l ∧ orbitWordProd l = w ∧ n = (l.map D.orbitN).prod

theorem exists_isOrbitLift {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) : ∃ n, D.IsOrbitLift n w := by
  obtain ⟨l, hl, e⟩ := D.mem_fixedWeyl_iff_exists_word.1 hw
  exact ⟨_, l, hl, e, rfl⟩

theorem isOrbitLift_spec {n : ModGL τ k} {w : WeylGroup τ} (h : D.IsOrbitLift n w) :
    n ∈ D.orbitGroup ∧ (∃ hn : n ∈ monomialSubgroup τ k, weylQuotientHom τ k ⟨n, hn⟩ = w) ∧
      ∃ x : adjointGroup τ k, (x : ModGL τ k) = n ∧ D.F x = x := by
  obtain ⟨l, hl, rfl, rfl⟩ := h
  have key : ∀ l : List (Set (Fin τ.rank → ℤ)), D.IsOrbitWord l →
      (l.map D.orbitN).prod ∈ D.orbitGroup ∧ (l.map D.orbitN).prod ∈ monomialSubgroup τ k ∧
        MapsRootLines (l.map D.orbitN).prod (orbitWordProd l) ∧
          ∃ x : adjointGroup τ k, (x : ModGL τ k) = (l.map D.orbitN).prod ∧ D.F x = x := by
    intro l hl
    induction l with
    | nil =>
      refine ⟨one_mem _, one_mem _, by simpa [orbitWordProd] using mapsRootLines_one, 1, rfl,
        map_one _⟩
    | cons O l ih =>
      have hO := hl O List.mem_cons_self
      obtain ⟨h1, h2, h3, x, hx, hxF⟩ := ih fun P hP => hl P (List.mem_cons_of_mem _ hP)
      rw [List.map_cons, List.prod_cons, orbitWordProd_cons]
      refine ⟨mul_mem (D.orbitMap_mem_orbitGroup hO _) h1,
        mul_mem (D.orbitN_mem_monomialSubgroup hO).1 h2,
        (D.orbitN_mem_monomialSubgroup hO).2.mul h3,
        ⟨D.orbitN O, D.orbitMap_mem_adjointGroup O _⟩ * x, by rw [Subgroup.coe_mul, hx], ?_⟩
      rw [map_mul, D.orbitN_fixed hO, hxF]
  obtain ⟨h1, h2, h3, h4⟩ := key l hl
  exact ⟨h1, ⟨h2, weylQuotientHom_eq h3⟩, h4⟩

theorem exists_fixedWeyl_eqOn {u : WeylGroup τ}
    (hu : u ∈ Subgroup.closure ((fun β => setReflection (thetaOrbit D.θ β)) ''
      unionSimpleRoots D.χ Set.univ)) :
    ∃ u' ∈ D.fixedWeyl, ∀ γ ∈ D.roots, u • γ = u' • γ := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    by_cases hβΨ : β ∈ D.roots
    · exact ⟨_, D.setReflection_mem_fixedWeyl (D.thetaOrbit_mem_orbits ⟨hβ, hβΨ⟩),
        fun _ _ => rfl⟩
    · refine ⟨1, one_mem _, fun γ hγ => ?_⟩
      obtain ⟨i, -, hβi⟩ := hβ
      have hβK : β ∈ kernelRoots D.χ := (simpleRoots_subset hβi).1
      have hfin := D.finite_thetaOrbit hβK
      show setReflection (thetaOrbit D.θ β) • γ = 1 • γ
      rw [D.setReflection_thetaOrbit_eq_list_prod hβK (Finset.nodup_toList hfin.toFinset)
        (fun δ => Finset.mem_toList.trans hfin.mem_toFinset), one_smul]
      refine reflectionWordProd_smul_of_forall_iform_eq_zero
        (fun δ hδ => (D.thetaOrbit_subset_kernelRoots hβK
          ((Finset.mem_toList.trans hfin.mem_toFinset).1 hδ)).1) fun δ hδ => ?_
      have hδO := (Finset.mem_toList.trans hfin.mem_toFinset).1 hδ
      have hδK := D.thetaOrbit_subset_kernelRoots hβK hδO
      have hδΨ : δ ∉ D.roots := fun h =>
        hβΨ (D.thetaOrbit_subset_roots h (D.mem_thetaOrbit_symm hβK hδO))
      obtain ⟨j, hj, hγj⟩ := mem_unionRoots_iff.1 hγ
      have hδc : δ ∈ componentRoots D.χ ⟦⟨δ, hδK⟩⟧ := ⟨hδK, rfl⟩
      refine iform_eq_zero_of_mem_componentRoots (fun h => hδΨ ⟨hδK, ?_⟩) hδc hγj
      rw [h]
      exact hj
  | one => exact ⟨1, one_mem _, fun _ _ => rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hxe⟩ := hx
    obtain ⟨y', hy', hye⟩ := hy
    refine ⟨x' * y', mul_mem hx' hy', fun γ hγ => ?_⟩
    rw [mul_smul, mul_smul, hye γ hγ, hxe _ (smul_mem_unionRoots
      (D.mem_unionWeylGroup_of_mem_fixedWeyl hy') hγ)]
  | inv x _ hx =>
    obtain ⟨x', hx', hxe⟩ := hx
    refine ⟨x'⁻¹, inv_mem hx', fun γ hγ => ?_⟩
    have h := hxe _ (smul_mem_unionRoots (D.mem_unionWeylGroup_of_mem_fixedWeyl (inv_mem hx')) hγ)
    rw [smul_inv_smul] at h
    calc x⁻¹ • γ = x⁻¹ • (x • (x'⁻¹ • γ)) := by rw [h]
      _ = x'⁻¹ • γ := inv_smul_smul x _

theorem exists_fixedWeyl_image_eq {α : Fin τ.rank → ℤ} (hα : α ∈ D.roots) :
    ∃ w ∈ D.fixedWeyl, ∃ O ∈ D.orbits, (fun γ => w • γ) '' O = thetaOrbit D.θ α := by
  obtain ⟨u, hu, β, hβ, huα⟩ := D.orbit_reflection α hα.1
  obtain ⟨u', hu', hue⟩ := D.exists_fixedWeyl_eqOn hu
  have himg : (fun γ => u' • γ) '' thetaOrbit D.θ α = thetaOrbit D.θ β := by
    rw [← huα]
    exact Set.image_congr fun γ hγ => (hue γ (D.thetaOrbit_subset_roots hα hγ)).symm
  have hβΨ : β ∈ D.roots := by
    have h1 : β ∈ (fun γ => u' • γ) '' thetaOrbit D.θ α := by
      rw [himg]
      exact self_mem_thetaOrbit _ _
    obtain ⟨γ, hγ, rfl⟩ := h1
    exact smul_mem_unionRoots (D.mem_unionWeylGroup_of_mem_fixedWeyl hu')
      (D.thetaOrbit_subset_roots hα hγ)
  refine ⟨u'⁻¹, inv_mem hu', thetaOrbit D.θ β, D.thetaOrbit_mem_orbits ⟨hβ, hβΨ⟩, ?_⟩
  rw [← himg, Set.image_image]
  simp only [inv_smul_smul, Set.image_id']

theorem fixedRootSpan_thetaOrbit_subset_orbitGroup {α : Fin τ.rank → ℤ} (hα : α ∈ D.roots) :
    Subtype.val '' (D.fixedRootSpan (thetaOrbit D.θ α) : Set (adjointGroup τ k)) ⊆
      D.orbitGroup := by
  obtain ⟨w, hw, O, hO, hwO⟩ := D.exists_fixedWeyl_image_eq hα
  obtain ⟨n, hn⟩ := D.exists_isOrbitLift hw
  obtain ⟨hnC, ⟨hnN, hnw⟩, x, rfl, hxF⟩ := D.isOrbitLift_spec hn
  have hmap := D.map_conj_fixedRootSpan hnN hnw hxF (S := O)
    (fun γ hγ => D.isRoot_of_mem_orbits hO hγ)
  rw [hwO] at hmap
  rw [← hmap]
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  obtain ⟨c, hc⟩ := D.exists_orbitX_eq hO hy
  show (x : ModGL τ k) * y * (x : ModGL τ k)⁻¹ ∈ D.orbitGroup
  rw [← hc]
  exact mul_mem (mul_mem hnC (D.orbitMap_mem_orbitGroup hO _)) (inv_mem hnC)

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem exists_orbitFixedHom {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    ∃ R : SL2 (D.orbitField O) →* D.fixedGroup,
      ∀ A, (((R A : D.fixedGroup) : adjointGroup τ k) : ModGL τ k) = D.orbitMap O A :=
  ⟨D.orbitFixedHom hO, D.coe_orbitFixedHom hO⟩

theorem exists_mulEquiv_fixedRootSpan_thetaOrbit {α : Fin τ.rank → ℤ} {w : WeylGroup τ}
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (hwO : (fun γ => w • γ) '' O = thetaOrbit D.θ α)
    {n : ModGL τ k} (hn : D.IsOrbitLift n w) {x : adjointGroup τ k} (hx : (x : ModGL τ k) = n) :
    ∃ e : D.fixedRootSpan O ≃* D.fixedRootSpan (thetaOrbit D.θ α),
      ∀ y, (e y : adjointGroup τ k) = x * y * x⁻¹ := by
  subst hx
  obtain ⟨-, ⟨hN, hw⟩, x', hx', hx'F⟩ := D.isOrbitLift_spec hn
  have hxx : x' = x := Subtype.ext hx'
  subst hxx
  rw [← hwO]
  exact D.exists_mulEquiv_fixedRootSpan hN hw hx'F (fun γ hγ => D.isRoot_of_mem_orbits hO hγ)

end GenFixedRootDatum

end CFSG.RankThree.Lattice

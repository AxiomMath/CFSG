module

public import CFSG.RankThree.Lattice.SteinbergBIGenCells
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedBruhat

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem orbitTorus_le_orbitBorel : D.orbitTorus ≤ D.orbitBorel := fun _ ht =>
  ⟨ht.1, torusGroup_le_borelGroup ht.2⟩

theorem inv_mul_mem_orbitTorus {n n' : ModGL τ k} {w : WeylGroup τ} (hn : D.IsOrbitLift n w)
    (hn' : D.IsOrbitLift n' w) : n⁻¹ * n' ∈ D.orbitTorus := by
  obtain ⟨hnC, ⟨hN, hw⟩, -⟩ := D.isOrbitLift_spec hn
  obtain ⟨hnC', ⟨hN', hw'⟩, -⟩ := D.isOrbitLift_spec hn'
  refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hnC) hnC',
    mem_torusGroup_of_mapsRootLines_one (mul_mem (inv_mem hN) hN') ?_⟩
  have h1 := mapsRootLines_weylQuotientHom (⟨n, hN⟩ : monomialSubgroup τ k)
  have h2 := mapsRootLines_weylQuotientHom (⟨n', hN'⟩ : monomialSubgroup τ k)
  rw [hw] at h1
  rw [hw'] at h2
  simpa using h1.inv.mul h2

theorem fixedCell_eq_of_isOrbitLift {n n' : ModGL τ k} {w : WeylGroup τ}
    (hn : D.IsOrbitLift n w) (hn' : D.IsOrbitLift n' w) : D.fixedCell n = D.fixedCell n' := by
  have ht := D.orbitTorus_le_orbitBorel (D.inv_mul_mem_orbitTorus hn hn')
  ext g
  rw [mem_fixedCell, mem_fixedCell]
  constructor
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨b, hb, (n⁻¹ * n')⁻¹ * b', mul_mem (inv_mem ht) hb', by group⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨b, hb, (n⁻¹ * n') * b', mul_mem ht hb', by group⟩

theorem isOrbitLift_orbitN {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.IsOrbitLift (D.orbitN O) (setReflection O) :=
  ⟨[O], fun P hP => by rw [List.mem_singleton.1 hP]; exact hO, by simp [orbitWordProd],
    by simp⟩

theorem isOrbitLift_orbitN_mul {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {n : ModGL τ k}
    {w : WeylGroup τ} (hn : D.IsOrbitLift n w) :
    D.IsOrbitLift (D.orbitN O * n) (setReflection O * w) := by
  obtain ⟨l, hl, hlw, rfl⟩ := hn
  exact ⟨O :: l, IsOrbitWord.cons hO hl, by rw [orbitWordProd_cons, hlw], by simp⟩

theorem orbitX_mem_orbitBorel {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (c : D.orbitField O) : D.orbitX O c ∈ D.orbitBorel :=
  ⟨D.orbitMap_mem_orbitGroup hO _, Subgroup.mem_sup_right (rootSpan_le_posUnipotent
    (fun _ hα => ⟨D.isRoot_of_mem_orbits hO hα, (D.mem_posRootsJ_of_mem_orbits hO hα).2⟩)
    (D.orbitX_mem_rootSpan hO c))⟩

theorem orbitH_mem_orbitBorel {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (t : (D.orbitField O)ˣ) : D.orbitH O t ∈ D.orbitBorel :=
  D.orbitTorus_le_orbitBorel ⟨D.orbitMap_mem_orbitGroup hO _, D.orbitH_mem_torusGroup hO t⟩

theorem orbitX_zero (O : Set (Fin τ.rank → ℤ)) : D.orbitX O 0 = 1 := by
  rw [orbitX, uSL_zero_eq_one, D.orbitMap_one]

theorem inv_conj_mem_fixedRootSpan {w : WeylGroup τ} {x : adjointGroup τ k}
    (hx : D.IsOrbitLift (x : ModGL τ k) w) (hxF : D.F x = x) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot τ γ) {y : adjointGroup τ k} (hy : y ∈ D.fixedRootSpan S) :
    x⁻¹ * y * x ∈ D.fixedRootSpan ((fun γ => w⁻¹ • γ) '' S) := by
  obtain ⟨-, ⟨hN, hw⟩, -⟩ := D.isOrbitLift_spec hx
  have hN' : ((x⁻¹ : adjointGroup τ k) : ModGL τ k) ∈ monomialSubgroup τ k := inv_mem hN
  have hw' : weylQuotientHom τ k ⟨_, hN'⟩ = w⁻¹ := by
    have e : (⟨_, hN'⟩ : monomialSubgroup τ k) = (⟨_, hN⟩ : monomialSubgroup τ k)⁻¹ := rfl
    rw [e, map_inv, hw]
  have hxF' : D.F x⁻¹ = x⁻¹ := by rw [map_inv, hxF]
  have hmap := D.map_conj_fixedRootSpan hN' hw' hxF' hS
  rw [← hmap]
  exact ⟨y, hy, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩

theorem fixedRootSpan_le_fixedUnipotentM {S : Set (Fin τ.rank → ℤ)} (hS : S ⊆ D.posRootsJ)
    {y : adjointGroup τ k} (hy : y ∈ D.fixedRootSpan S) : (y : ModGL τ k) ∈ D.fixedUnipotentM :=
  ⟨y, D.mem_fixedUnipotent.2 ⟨rootSpan_mono hS (D.mem_fixedRootSpan.1 hy).1,
    (D.mem_fixedRootSpan.1 hy).2⟩, rfl⟩

theorem image_subset_posRootsJ_of_not_subset {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl)
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (h : ¬(fun γ => w • γ) '' O ⊆ negRoots D.roots) : (fun γ => w • γ) '' O ⊆ D.posRootsJ := by
  obtain ⟨β, hβ⟩ := D.nonempty_of_mem_orbits hO
  have hpos := (D.not_image_subset_negRoots_iff hw hO hβ).1 h
  rw [D.eq_thetaOrbit_of_mem_orbits hO hβ,
    D.image_smul_thetaOrbit hw (D.mem_roots_of_mem_orbits hO hβ)]
  exact D.thetaOrbit_subset_posRootsJ hpos

theorem conj_orbitX_mem_fixedUnipotentM {w : WeylGroup τ} {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits)
    (hpos : (fun γ => w⁻¹ • γ) '' O ⊆ D.posRootsJ) {x : adjointGroup τ k}
    (hx : D.IsOrbitLift (x : ModGL τ k) w) (hxF : D.F x = x) (c : D.orbitField O) :
    (x : ModGL τ k)⁻¹ * D.orbitX O c * x ∈ D.fixedUnipotentM := by
  have h := D.inv_conj_mem_fixedRootSpan hx hxF (fun γ hγ => D.isRoot_of_mem_orbits hO hγ)
    (D.orbitX_mem_fixedRootSpan hO c)
  exact D.fixedRootSpan_le_fixedUnipotentM hpos h

theorem conj_orbitY_mem_fixedUnipotentM {w : WeylGroup τ} {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits)
    (hneg : (fun γ => w⁻¹ • γ) '' O ⊆ negRoots D.roots) {x : adjointGroup τ k}
    (hx : D.IsOrbitLift (x : ModGL τ k) w) (hxF : D.F x = x) (c : D.orbitField O) :
    (x : ModGL τ k)⁻¹ * D.orbitY O c * x ∈ D.fixedUnipotentM := by
  have hY : (⟨D.orbitY O c, D.orbitMap_mem_adjointGroup O _⟩ : adjointGroup τ k) ∈
      D.fixedRootSpan ((fun γ => -γ) '' O) := by
    have h1 : D.orbitY O c ∈ Set.range (D.orbitY O) := ⟨c, rfl⟩
    rw [D.range_orbitY hO] at h1
    obtain ⟨y, hy, hye⟩ := h1
    have e : y = ⟨D.orbitY O c, D.orbitMap_mem_adjointGroup O _⟩ := Subtype.ext hye
    rwa [← e]
  have h := D.inv_conj_mem_fixedRootSpan hx hxF (S := (fun γ => -γ) '' O) (by
    rintro _ ⟨γ, hγ, rfl⟩
    exact IsRoot.neg (D.isRoot_of_mem_orbits hO hγ)) hY
  refine D.fixedRootSpan_le_fixedUnipotentM ?_ h
  rintro _ ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
  have h1 := hneg ⟨γ, hγ, rfl⟩
  show w⁻¹ • -γ ∈ D.posRootsJ
  rw [smul_neg]
  exact h1

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem fixedRootSpan_mono {S S' : Set (Fin τ.rank → ℤ)} (h : S ⊆ S') :
    D.fixedRootSpan S ≤ D.fixedRootSpan S' := fun _ hy =>
  D.mem_fixedRootSpan.2 ⟨rootSpan_mono h (D.mem_fixedRootSpan.1 hy).1, (D.mem_fixedRootSpan.1 hy).2⟩

theorem exists_fixedUnipotent_eq_mul {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {u : adjointGroup τ k} (hu : u ∈ D.fixedUnipotent) :
    ∃ u' ∈ D.fixedRootSpan (D.posRootsJ \ O), ∃ c : D.orbitField O,
      (u : ModGL τ k) = u' * D.orbitX O c := by
  classical
  have hfin : ((thetaOrbit D.θ) '' D.posRootsJ).Finite :=
    (D.finite_roots.subset fun _ h => h.1).image _
  set L₀ := (hfin.toFinset.toList).filter (fun Q => Q ≠ O) with hL₀
  have hOmem : ∃ γ ∈ D.posRootsJ, O = thetaOrbit D.θ γ :=
    ⟨orbitRoot O, D.mem_posRootsJ_of_mem_orbits hO (D.orbitRoot_mem hO),
      D.eq_thetaOrbit_orbitRoot hO⟩
  have hmemL₀ : ∀ Q, Q ∈ L₀ ↔ (∃ γ ∈ D.posRootsJ, Q = thetaOrbit D.θ γ) ∧ Q ≠ O := fun Q => by
    rw [hL₀, List.mem_filter, Finset.mem_toList, Set.Finite.mem_toFinset, decide_eq_true_iff]
    exact and_congr_left fun _ =>
      ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩
  have hLnd : (L₀ ++ [O]).Nodup := by
    rw [List.nodup_append]
    refine ⟨(Finset.nodup_toList _).filter _, List.nodup_singleton O, ?_⟩
    intro Q hQ P hP hQP
    rw [List.mem_singleton] at hP
    subst hP
    exact ((hmemL₀ Q).1 hQ).2 hQP
  have hL : ∀ Q, Q ∈ L₀ ++ [O] ↔ ∃ γ ∈ D.posRootsJ, Q = thetaOrbit D.θ γ := fun Q => by
    rw [List.mem_append, List.mem_singleton, hmemL₀]
    constructor
    · rintro (⟨h, -⟩ | rfl)
      · exact h
      · exact hOmem
    · intro h
      by_cases hQO : Q = O
      · exact Or.inr hQO
      · exact Or.inl ⟨h, hQO⟩
  have hu' : u ∈ D.fixedRootSpan D.posRootsJ := D.mem_fixedRootSpan.2 (D.mem_fixedUnipotent.1 hu)
  obtain ⟨y, hy, hyu⟩ := D.exists_fixed_block_factors le_rfl
    (fun _ h => D.thetaOrbit_subset_posRootsJ h) D.posRootsJ_closed hLnd hL hu'
  rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton] at hyu
  obtain ⟨c, hc⟩ := D.exists_orbitX_eq hO (hy O (by simp))
  refine ⟨(L₀.map y).prod, Subgroup.list_prod_mem _ fun z hz => ?_, c, ?_⟩
  · obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hz
    obtain ⟨⟨γ, hγ, rfl⟩, hQO⟩ := (hmemL₀ _).1 hQ
    refine D.fixedRootSpan_mono (S := thetaOrbit D.θ γ) (S' := D.posRootsJ \ O)
      (fun δ hδ => ⟨D.thetaOrbit_subset_posRootsJ hγ hδ, fun hδO => hQO ?_⟩)
      (hy _ (List.mem_append_left _ hQ))
    rw [D.eq_thetaOrbit_of_mem_orbits hO hδO, D.thetaOrbit_eq_of_mem hγ.1.1 hδ]
  · rw [hyu, Subgroup.coe_mul, hc]

theorem image_setReflection_posRootsJ_sdiff {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    (fun γ => setReflection O • γ) '' (D.posRootsJ \ O) = D.posRootsJ \ O := by
  apply Set.Subset.antisymm
  · rintro _ ⟨α, ⟨hα, hαO⟩, rfl⟩
    exact D.setReflection_smul_mem_posRootsJ hO hα hαO
  · intro α ⟨hα, hαO⟩
    refine ⟨setReflection O • α, D.setReflection_smul_mem_posRootsJ hO hα hαO, ?_⟩
    simp only [smul_smul, D.setReflection_mul_self hO, one_smul]

theorem conj_orbitN_mem_fixedRootSpan {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {y : adjointGroup τ k} (hy : y ∈ D.fixedRootSpan (D.posRootsJ \ O)) :
    (⟨D.orbitN O, D.orbitMap_mem_adjointGroup O _⟩ : adjointGroup τ k) * y *
      (⟨D.orbitN O, D.orbitMap_mem_adjointGroup O _⟩ : adjointGroup τ k)⁻¹ ∈
        D.fixedRootSpan (D.posRootsJ \ O) := by
  have hmap := D.map_conj_fixedRootSpan (x := ⟨D.orbitN O, D.orbitMap_mem_adjointGroup O _⟩)
    (D.orbitN_mem_monomialSubgroup hO).1 (D.weylQuotientHom_orbitN hO) (D.orbitN_fixed hO)
    (S := D.posRootsJ \ O) (fun γ hγ => isRoot_of_mem_unionRoots hγ.1.1)
  rw [D.image_setReflection_posRootsJ_sdiff hO] at hmap
  rw [← hmap]
  exact ⟨y, hy, rfl⟩

theorem conj_orbitN_mem_orbitTorus {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {t : ModGL τ k} (ht : t ∈ D.orbitTorus) :
    D.orbitN O * t * (D.orbitN O)⁻¹ ∈ D.orbitTorus := by
  have hN := D.orbitMap_mem_orbitGroup hO WSL
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hN (Subgroup.mem_inf.1 ht).1) (inv_mem hN), ?_⟩
  exact (Subgroup.mem_normalizer_iff.1 (D.orbitN_mem_normalizer hO) t).1 (Subgroup.mem_inf.1 ht).2

theorem exists_of_mem_fixedCell_mul {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {n : ModGL τ k} {g : ModGL τ k} (hg : g ∈ D.fixedCell (D.orbitN O) * D.fixedCell n) :
    ∃ b ∈ D.orbitBorel, ∃ c : D.orbitField O, ∃ b' ∈ D.orbitBorel,
      g = b * D.orbitN O * D.orbitX O c * n * b' := by
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hg
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := D.mem_fixedCell.1 hg₁
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := D.mem_fixedCell.1 hg₂
  have hb : b₂ * b₃ ∈ (D.orbitTorus : Set (ModGL τ k)) * (D.fixedUnipotentM : Set (ModGL τ k)) := by
    rw [← D.coe_orbitBorel_eq_mul]
    exact mul_mem hb₂ hb₃
  obtain ⟨t, ht, _, ⟨u, hu, rfl⟩, htu⟩ := hb
  obtain ⟨u', hu', c, huc⟩ := D.exists_fixedUnipotent_eq_mul hO hu
  set xN : adjointGroup τ k := ⟨D.orbitN O, D.orbitMap_mem_adjointGroup O _⟩ with hxN
  have h1 := D.conj_orbitN_mem_fixedRootSpan hO hu'
  have h2 : ((xN * u' * xN⁻¹ : adjointGroup τ k) : ModGL τ k) ∈ D.orbitBorel :=
    D.fixedUnipotentM_le_orbitBorel (D.fixedRootSpan_le_fixedUnipotentM
      (fun _ hα => hα.1) h1)
  have h3 := D.orbitTorus_le_orbitBorel (D.conj_orbitN_mem_orbitTorus hO ht)
  refine ⟨b₁ * (D.orbitN O * t * (D.orbitN O)⁻¹) *
      ((xN * u' * xN⁻¹ : adjointGroup τ k) : ModGL τ k), mul_mem (mul_mem hb₁ h3) h2, c, b₄, hb₄,
    ?_⟩
  have e : b₂ * b₃ = t * u' * D.orbitX O c := by
    have htu' : t * (u : ModGL τ k) = b₂ * b₃ := htu
    rw [← htu', huc, mul_assoc]
  calc b₁ * D.orbitN O * b₂ * (b₃ * n * b₄) = b₁ * D.orbitN O * (b₂ * b₃) * n * b₄ := by group
    _ = b₁ * D.orbitN O * (t * u' * D.orbitX O c) * n * b₄ := by rw [e]
    _ = _ := by
      simp only [hxN, Subgroup.coe_mul, Subgroup.coe_inv]
      group

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem orbitN_mul_orbitX {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {c : D.orbitField O}
    (hc : c ≠ 0) :
    D.orbitN O * D.orbitX O c =
      D.orbitX O (-c⁻¹) * D.orbitH O (-(Units.mk0 c hc)⁻¹) * D.orbitY O c⁻¹ := by
  rw [orbitN, orbitX, ← D.orbitMap_mul hO, WSL_mul_uSL_eq hc, D.orbitMap_mul hO,
    D.orbitMap_mul hO]
  rfl

theorem fixedCell_subset_fixedCell_mul {O : Set (Fin τ.rank → ℤ)} {n : ModGL τ k} :
    D.fixedCell (D.orbitN O * n) ⊆ D.fixedCell (D.orbitN O) * D.fixedCell n := by
  intro g hg
  obtain ⟨b, hb, b', hb', rfl⟩ := D.mem_fixedCell.1 hg
  exact ⟨b * D.orbitN O * 1, D.mem_fixedCell.2 ⟨b, hb, 1, one_mem _, rfl⟩, 1 * n * b',
    D.mem_fixedCell.2 ⟨1, one_mem _, b', hb', rfl⟩, by group⟩

theorem fixedCell_orbitN_mul_fixedCell {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) {n : ModGL τ k} (hn : D.IsOrbitLift n w) :
    (D.foldedLength (setReflection O * w) = D.foldedLength w + 1 →
      D.fixedCell (D.orbitN O) * D.fixedCell n = D.fixedCell (D.orbitN O * n)) ∧
    (D.foldedLength (setReflection O * w) ≠ D.foldedLength w + 1 →
      D.fixedCell (D.orbitN O) * D.fixedCell n = D.fixedCell (D.orbitN O * n) ∪ D.fixedCell n) := by
  obtain ⟨hnC, -, x, hx, hxF⟩ := D.isOrbitLift_spec hn
  subst hx
  have hw' := inv_mem hw
  have htest := D.foldedLength_setReflection_mul hO hw
  refine ⟨fun hlen => ?_, fun hlen => ?_⟩
  ·
    have hnot : ¬(fun γ => w⁻¹ • γ) '' O ⊆ negRoots D.roots := fun h => by
      have := htest.1.2 h
      omega
    have hpos := D.image_subset_posRootsJ_of_not_subset hw' hO hnot
    refine Set.Subset.antisymm (fun g hg => ?_) D.fixedCell_subset_fixedCell_mul
    obtain ⟨b, hb, c, b', hb', rfl⟩ := D.exists_of_mem_fixedCell_mul hO hg
    have hu := D.fixedUnipotentM_le_orbitBorel (D.conj_orbitX_mem_fixedUnipotentM hO hpos hn hxF c)
    refine D.mem_fixedCell.2 ⟨b, hb, ((x : ModGL τ k)⁻¹ * D.orbitX O c * x) * b',
      mul_mem hu hb', by group⟩
  ·
    have hneg : (fun γ => w⁻¹ • γ) '' O ⊆ negRoots D.roots := by
      by_contra h
      exact hlen (htest.2 h)
    have hcell : ∀ b ∈ D.orbitBorel, ∀ (c : D.orbitField O) (hc : c ≠ 0), ∀ b' ∈ D.orbitBorel,
        b * D.orbitN O * D.orbitX O c * x * b' ∈ D.fixedCell x := by
      intro b hb c hc b' hb'
      have hu := D.fixedUnipotentM_le_orbitBorel
        (D.conj_orbitY_mem_fixedUnipotentM hO hneg hn hxF c⁻¹)
      refine D.mem_fixedCell.2 ⟨b * D.orbitX O (-c⁻¹) * D.orbitH O (-(Units.mk0 c hc)⁻¹),
        mul_mem (mul_mem hb (D.orbitX_mem_orbitBorel hO _)) (D.orbitH_mem_orbitBorel hO _),
        ((x : ModGL τ k)⁻¹ * D.orbitY O c⁻¹ * x) * b', mul_mem hu hb', ?_⟩
      rw [mul_assoc b (D.orbitN O), D.orbitN_mul_orbitX hO hc]
      group
    refine Set.Subset.antisymm (fun g hg => ?_) (Set.union_subset D.fixedCell_subset_fixedCell_mul
      fun g hg => ?_)
    · obtain ⟨b, hb, c, b', hb', rfl⟩ := D.exists_of_mem_fixedCell_mul hO hg
      by_cases hc : c = 0
      · left
        rw [hc, D.orbitX_zero, mul_one]
        exact D.mem_fixedCell.2 ⟨b, hb, b', hb', by group⟩
      · exact Or.inr (hcell b hb c hc b' hb')
    ·
      obtain ⟨b, hb, b', hb', rfl⟩ := D.mem_fixedCell.1 hg
      have h1 : (1 : D.orbitField O) ≠ 0 := one_ne_zero
      obtain ⟨b₀, hb₀, b₀', hb₀', e₀⟩ := D.mem_fixedCell.1 (hcell 1 (one_mem _) 1 h1 1 (one_mem _))
      refine ⟨b * b₀⁻¹ * D.orbitN O * D.orbitX O 1,
        D.mem_fixedCell.2 ⟨b * b₀⁻¹, mul_mem hb (inv_mem hb₀), D.orbitX O 1,
          D.orbitX_mem_orbitBorel hO 1, by group⟩,
        x * (b₀'⁻¹ * b'), D.mem_fixedCell.2 ⟨1, one_mem _, b₀'⁻¹ * b', mul_mem (inv_mem hb₀') hb',
          by group⟩, ?_⟩
      have e₂ : D.orbitN O * D.orbitX O 1 * (x : ModGL τ k) = b₀ * x * b₀' := by
        rw [e₀]
        group
      calc b * b₀⁻¹ * D.orbitN O * D.orbitX O 1 * (x * (b₀'⁻¹ * b'))
          = b * b₀⁻¹ * (D.orbitN O * D.orbitX O 1 * x) * b₀'⁻¹ * b' := by group
        _ = b * b₀⁻¹ * (b₀ * x * b₀') * b₀'⁻¹ * b' := by rw [e₂]
        _ = b * x * b' := by group

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem fixedUnipotentM_le_unipotentJ : D.fixedUnipotentM ≤ unionUnipotent k D.χ D.J := by
  rintro _ ⟨u, hu, rfl⟩
  exact (D.mem_fixedUnipotent.1 hu).1

theorem isNilpotent_fixedUnipotentM : Group.IsNilpotent D.fixedUnipotentM := by
  have := isNilpotent_unionUnipotent (K := k) (χ := D.χ) (J := D.J)
  refine Subgroup.isNilpotent_of_ker_le_center
    (Subgroup.inclusion D.fixedUnipotentM_le_unipotentJ) ?_
  rw [(MonoidHom.ker_eq_bot_iff _).2 (Subgroup.inclusion_injective _)]
  exact bot_le

theorem finite_orbitGroup : Finite D.orbitGroup := by
  have := D.finite_fixedGroup
  refine Finite.of_injective (fun c : D.orbitGroup => (⟨_, D.orbitGroupC_le_fixedGroup
    (D.mk_mem_orbitGroupC c.2)⟩ : D.fixedGroup)) fun c c' h => Subtype.ext ?_
  have := congrArg (fun z : D.fixedGroup => ((z : adjointGroup τ k) : ModGL τ k)) h
  exact this

end GenFixedRootDatum

end CFSG.RankThree.Lattice

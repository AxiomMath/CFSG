module

public import CFSG.Monster.B.Geometry.UnitaryResidue
public import CFSG.Monster.B.Geometry.GlobalExtension

public section

namespace CFSG.Monster.B.Geometry

open Module CoxeterSystem CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding
open CFSG.LieType.Chevalley.C2E6Overlap (K bar)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def uDiag (a : Fin 3 → Kˣ) (σ : K ≃+* K) : UV →ₛₗ[(σ : K →+* K)] UV where
  toFun v := ![a 0 * σ (v 0), a 1 * σ (v 1), a 2 * σ (v 2), a 0 * σ (v 3), a 1 * σ (v 4),
    a 2 * σ (v 5)]
  map_add' v w := by funext i; fin_cases i <;> simp [mul_add]
  map_smul' c v := by funext i; fin_cases i <;> simp <;> ring

theorem uDiag_apply (a : Fin 3 → Kˣ) (σ : K ≃+* K) (v : UV) :
    uDiag a σ v = ![a 0 * σ (v 0), a 1 * σ (v 1), a 2 * σ (v 2), a 0 * σ (v 3), a 1 * σ (v 4),
      a 2 * σ (v 5)] := rfl

theorem bar_ringEquiv (σ : K ≃+* K) (x : K) : σ (bar x) = bar (σ x) := by
  simp only [C2E6Overlap.bar, map_pow]

theorem uHerm_uDiag (a : Fin 3 → Kˣ) (σ : K ≃+* K) (v w : UV) :
    uHerm (uDiag a σ v) (uDiag a σ w) = σ (uHerm v w) := by
  have h0 := mul_bar_self_of_ne_zero (a 0).ne_zero
  have h1 := mul_bar_self_of_ne_zero (a 1).ne_zero
  have h2 := mul_bar_self_of_ne_zero (a 2).ne_zero
  simp only [uHerm, uDiag_apply, Matrix.cons_val, C2E6Overlap.bar_mul, map_add, map_mul,
    bar_ringEquiv]
  linear_combination (σ (v 0) * bar (σ (w 3)) + σ (v 3) * bar (σ (w 0))) * h0 +
    (σ (v 1) * bar (σ (w 4)) + σ (v 4) * bar (σ (w 1))) * h1 +
    (σ (v 2) * bar (σ (w 5)) + σ (v 5) * bar (σ (w 2))) * h2

theorem uDiag_apply_eq_zero_iff (a : Fin 3 → Kˣ) (σ : K ≃+* K) (v : UV) (i : Fin 6) :
    uDiag a σ v i = 0 ↔ v i = 0 := by
  rw [uDiag_apply]
  fin_cases i <;> simp

theorem uDiag_bijective (a : Fin 3 → Kˣ) (σ : K ≃+* K) : Function.Bijective (uDiag a σ) := by
  refine ⟨fun v w h => ?_, fun w => ⟨![σ.symm ((a 0)⁻¹ * w 0), σ.symm ((a 1)⁻¹ * w 1),
    σ.symm ((a 2)⁻¹ * w 2), σ.symm ((a 0)⁻¹ * w 3), σ.symm ((a 1)⁻¹ * w 4),
    σ.symm ((a 2)⁻¹ * w 5)], ?_⟩⟩
  · funext i
    have := congrFun h i
    rw [uDiag_apply, uDiag_apply] at this
    fin_cases i <;> simpa using this
  · funext i
    rw [uDiag_apply]
    fin_cases i <;> simp

@[expose] noncomputable def uDiagPerm (a : Fin 3 → Kˣ) (σ : K ≃+* K) : Equiv.Perm (PFlag UData) :=
  polarFlagPerm (uDiag a σ) (uDiag_bijective a σ) fun v => by
    rw [uData_iso, uData_iso, uHerm_uDiag, map_eq_zero_iff σ σ.injective]

theorem map_uDiag_cspan (a : Fin 3 → Kˣ) (σ : K ≃+* K) (s : Finset (Fin 6)) :
    (cspan K s).map (uDiag a σ) = cspan K s := by
  ext w
  rw [Submodule.mem_map, mem_cspan]
  constructor
  · rintro ⟨v, hv, rfl⟩ i hi
    rw [mem_cspan] at hv
    exact (uDiag_apply_eq_zero_iff a σ v i).mpr (hv i hi)
  · intro hw
    obtain ⟨v, rfl⟩ := (uDiag_bijective a σ).2 w
    refine ⟨v, mem_cspan.mpr fun i hi => (uDiag_apply_eq_zero_iff a σ v i).mp (hw i hi), rfl⟩

theorem uDiagPerm_uC0 (a : Fin 3 → Kˣ) (σ : K ≃+* K) : uDiagPerm a σ uC0 = uC0 :=
  PFlag.ext (map_uDiag_cspan a σ _) (map_uDiag_cspan a σ _) (map_uDiag_cspan a σ _)

theorem uDiagPerm_uD0 (a : Fin 3 → Kˣ) (σ : K ≃+* K) : uDiagPerm a σ uD0 = uD0 :=
  PFlag.ext (map_uDiag_cspan a σ _) (map_uDiag_cspan a σ _) (map_uDiag_cspan a σ _)

theorem uDiagPerm_smul (a : Fin 3 → Kˣ) (σ : K ≃+* K) (t : Kˣ) :
    uDiagPerm (fun i => t * a i) σ = uDiagPerm a σ := by
  have hmap : ∀ U : Submodule K UV, U.map (uDiag (fun i => t * a i) σ) = U.map (uDiag a σ) := by
    intro U
    have hsmul : ∀ v, uDiag (fun i => t * a i) σ v = (t : K) • uDiag a σ v := fun v => by
      funext i
      rw [uDiag_apply, uDiag_apply]
      fin_cases i <;> simp [mul_assoc]
    ext w
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨σ.symm t • v, U.smul_mem _ hv, ?_⟩
      rw [map_smulₛₗ, hsmul]
      simp
    · rintro ⟨v, hv, rfl⟩
      refine ⟨σ.symm (t⁻¹ : Kˣ) • v, U.smul_mem _ hv, ?_⟩
      rw [map_smulₛₗ, hsmul]
      simp [smul_smul]
  ext1 x
  exact PFlag.ext (hmap _) (hmap _) (hmap _)

theorem uRho_uDiag (a : Fin 3 → Kˣ) (σ : K ≃+* K) (v : UV) :
    uRho (uDiag a σ v) =
      ((a 2 : Kˣ) : K) • planeDiagFun (a 0 * (a 2)⁻¹) (a 1 * (a 2)⁻¹) σ (uRho v) := by
  have h2 := (a 2).ne_zero
  funext i
  fin_cases i <;> simp [uRho, uDiag_apply, planeDiagFun] <;> field_simp

theorem map_uRho_map_uDiag (a : Fin 3 → Kˣ) (σ : K ≃+* K) (U : Submodule K UV) :
    (U.map (uDiag a σ)).map uRho =
      (U.map uRho).map (planeDiagSemilin (a 0 * (a 2)⁻¹) (a 1 * (a 2)⁻¹) σ) := by
  ext w
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨uRho (σ.symm (a 2 : Kˣ) • v), ⟨_, U.smul_mem _ hv, rfl⟩, ?_⟩
    rw [uRho_uDiag, map_smul, map_smulₛₗ, planeDiagSemilin_apply]
    simp
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨uDiag a σ (σ.symm ((a 2)⁻¹ : Kˣ) • v), ⟨_, U.smul_mem _ hv, rfl⟩, ?_⟩
    rw [uRho_uDiag, map_smul, ← planeDiagSemilin_apply, map_smulₛₗ]
    simp [smul_smul]

section Building

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} {p l π : ι} (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π)
  {f : C → PFlag UData} (hf : IsChamberModel cs δ (polarChamber UData p l π) f) {c₀ : C}
  (hc₀ : f c₀ = uC0)

include hf in
theorem planeResidueModel_uDiagPerm (a : Fin 3 → Kˣ) (σ : K ≃+* K)
    (hρ : Set.InjOn uRho (f c₀).V₃) {y : C} (hy : (f y).V₃ = (f c₀).V₃) (hc₀3 :
      (f c₀).V₃ = cspan K {0, 1, 2}) :
    (f (hf.perm (uDiagPerm a σ) y)).V₃ = (f c₀).V₃ ∧
    planeResidueModel f c₀ uRho hρ (hf.perm (uDiagPerm a σ) y) =
      planeDiagPerm (a 0 * (a 2)⁻¹) (a 1 * (a 2)⁻¹) σ (planeResidueModel f c₀ uRho hρ y) := by
  have hgy : f (hf.perm (uDiagPerm a σ) y) = uDiagPerm a σ (f y) := hf.apply_perm _ y
  have h3 : (f (hf.perm (uDiagPerm a σ) y)).V₃ = (f c₀).V₃ := by
    rw [hgy]
    change (f y).V₃.map (uDiag a σ) = _
    rw [hy, hc₀3, map_uDiag_cspan]
  refine ⟨h3, PlaneFlag.ext ?_ ?_⟩
  · rw [planeResidueModel_pt uRho hρ h3, planeDiagPerm_pt, planeResidueModel_pt uRho hρ hy, hgy]
    exact map_uRho_map_uDiag a σ _
  · rw [planeResidueModel_line uRho hρ h3, planeDiagPerm_line, planeResidueModel_line uRho hρ hy,
      hgy]
    exact map_uRho_map_uDiag a σ _

include hpl hlπ hpπ hf hc₀

omit [Group W] hpl hlπ hpπ hf in
theorem uC0_V₃ : (f c₀).V₃ = cspan K {0, 1, 2} := by rw [hc₀]; rfl

omit [Group W] hpl hlπ hpπ hf in
theorem planeResidueModel_c0 :
    planeResidueModel f c₀ uRho (uRho_injOn hc₀) c₀ = PlaneFlag.c K := by
  have h3 : (f c₀).V₃ = (f c₀).V₃ := rfl
  have e0 : uRho (Pi.single 0 1 : UV) = Pi.single 0 1 := by funext i; fin_cases i <;> rfl
  have e1 : uRho (Pi.single 1 1 : UV) = Pi.single 1 1 := by funext i; fin_cases i <;> rfl
  refine PlaneFlag.ext ?_ ?_
  · rw [planeResidueModel_pt uRho _ h3, hc₀]
    change (cspan K {0}).map uRho = _
    rw [map_cspan_singleton, e0]
    rfl
  · rw [planeResidueModel_line uRho _ h3, hc₀]
    change (cspan K {0, 1}).map uRho = _
    rw [map_cspan_insert, map_cspan_singleton, e0, e1]
    change _ = Submodule.span K {Pi.single 0 1, Pi.single 1 1}
    rw [Submodule.span_insert]

end Building

section Main

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  [Finite W] {C : Type*} {δ : C → C → W} (hδ : IsWeylDistanceBuilding cs δ) {p l π : ι}
  (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π) (hι : ∀ i, i = p ∨ i = l ∨ i = π)
  (hMpl : M p l = 3) (hMlπ : M l π = 4) (hMpπ : M p π = 2) {f : C → PFlag UData}
  (hf : IsChamberModel cs δ (polarChamber UData p l π) f) {c₀ d₀ : C} (hc₀ : f c₀ = uC0)
  (hd₀ : f d₀ = uD0)
include hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀

theorem unitary_oppChamber_plane :
    f (oppChamber cs δ c₀ d₀ (longest cs {p, l})) = uFlag {2} {1, 2} {0, 1, 2} := by
  have hcd := unitary_standard_opposite hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  obtain ⟨q, hq⟩ := hf.1.2 (uFlag {2} {1, 2} {0, 1, 2})
  have hqR : q ∈ residue cs δ {p, l} c₀ :=
    (polar_mem_residue_pl hf hpl hlπ hpπ).mpr (by rw [hq, hc₀]; rfl)
  have hγ : (polarChamber UData p l π).IsGallery (f q) [(π, uFlag {2} {1, 2} {1, 2, 3}),
      (l, uFlag {2} {2, 3} {1, 2, 3}), (p, uFlag {3} {2, 3} {1, 2, 3}),
      (π, uFlag {3} {2, 3} {2, 3, 4}), (l, uFlag {3} {3, 4} {2, 3, 4}), (π, uD0)] := by
    rw [hq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [polarChamber_adj_π hpπ hlπ]; exact ⟨rfl, rfl⟩
    · rw [polarChamber_adj_l hpl]; exact ⟨rfl, rfl⟩
    · rw [polarChamber_adj_p]; exact ⟨rfl, rfl⟩
    · rw [polarChamber_adj_π hpπ hlπ]; exact ⟨rfl, rfl⟩
    · rw [polarChamber_adj_l hpl]; exact ⟨rfl, rfl⟩
    · rw [polarChamber_adj_π hpπ hlπ]; exact ⟨rfl, rfl⟩
  have hlen := hf.length_le hδ hγ (by rw [hd₀]; rfl)
  have h9 := nine_le_length_longest_C3 (cs := cs) hpl hlπ hpπ hι hMpl hMlπ hMpπ
  have h3 : cs.length (longest cs {p, l}) = 3 := by
    rw [length_longest_pair hpl (by omega), hMpl]
  simp only [List.length_cons, List.length_nil] at hlen
  rw [← eq_oppChamber_of_length_le hδ hcd hqR (by omega), hq]

theorem planeResidueModel_p1 :
    planeResidueModel f c₀ uRho (uRho_injOn hc₀) (oppChamber cs δ c₀ d₀ (longest cs {p, l})) =
      PlaneFlag.d K := by
  have hq := unitary_oppChamber_plane hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  have h3 : (f (oppChamber cs δ c₀ d₀ (longest cs {p, l}))).V₃ = (f c₀).V₃ := by
    rw [hq, hc₀]; rfl
  have e1 : uRho (Pi.single 1 1 : UV) = Pi.single 1 1 := by funext i; fin_cases i <;> rfl
  have e2 : uRho (Pi.single 2 1 : UV) = Pi.single 2 1 := by funext i; fin_cases i <;> rfl
  refine PlaneFlag.ext ?_ ?_
  · rw [planeResidueModel_pt uRho _ h3, hq]
    change (cspan K {2}).map uRho = _
    rw [map_cspan_singleton, e2]
    rfl
  · rw [planeResidueModel_line uRho _ h3, hq]
    change (cspan K {1, 2}).map uRho = _
    rw [map_cspan_insert, map_cspan_singleton, e1, e2]
    change _ = Submodule.span K {Pi.single 1 1, Pi.single 2 1}
    rw [Submodule.span_insert]

theorem unitary_realize (Ψ : C → C)
    (hΨ : IsWeylIsometry δ δ (foundation cs δ 2 c₀ ∪ {d₀}) (foundation cs δ 2 c₀ ∪ {d₀}) Ψ)
    (hΨc : Ψ c₀ = c₀) (hΨd : Ψ d₀ = d₀) :
    ∃ (a b : Kˣ) (σ : K ≃+* K),
      Set.EqOn (hf.perm (uDiagPerm ![a, b, 1] σ)) Ψ (foundation cs δ 2 c₀ ∪ {d₀}) := by
  have hcd := unitary_standard_opposite hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  have hρ := uRho_injOn hc₀
  have hRP := fun y => polar_mem_residue_pl hf hpl hlπ hpπ (x := c₀) (y := y)
  have hpm := isModelResidue_planeResidueModel uRho hρ hf hpl hlπ hpπ
  have hiso_p := hΨ.isTypeIso_residue hδ hΨc (encard_pair_le_two p l)
  obtain ⟨G, hG, hG1, hG2⟩ := hpm.exists_perm (fun _ => rfl) (fun _ => rfl) hiso_p
  have hGmem : G ∈ planeTypeAut K := fun u v => ⟨hG2 u v, hG1 u v⟩
  have hq := unitary_oppChamber_plane hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  have hp₁R : oppChamber cs δ c₀ d₀ (longest cs {p, l}) ∈ residue cs δ {p, l} c₀ :=
    (hRP _).mpr (by rw [hq, hc₀]; rfl)
  have hΨp := hΨ.fix_oppChamber hδ hcd hΨc hΨd (encard_pair_le_two p l)
    (isLongest_of_finite (cs := cs) {p, l}).1
  have hGc : G (PlaneFlag.c K) = PlaneFlag.c K := by
    rw [← planeResidueModel_c0 hc₀, hG c₀ (self_mem_residue _ c₀), hΨc]
  have hGd : G (PlaneFlag.d K) = PlaneFlag.d K := by
    rw [← planeResidueModel_p1 hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀, hG _ hp₁R, hΨp]
  have hGstab : G ∈ planeOppStab K := mem_planePairStab.mpr ⟨hGmem, hGc, hGd⟩
  obtain ⟨⟨a, b, σ⟩, hab, -⟩ := existsUnique_planeDiagPerm_eq hGstab
  have hgmem : hf.perm (uDiagPerm ![a, b, 1] σ) ∈ typeAut cs δ :=
    hf.perm_mem_typeAut (polarFlagPerm_mem_typeAut _ _ _ p l π)
  have hgc : hf.perm (uDiagPerm ![a, b, 1] σ) c₀ = c₀ :=
    hf.1.1 (by rw [hf.apply_perm, hc₀, uDiagPerm_uC0])
  have hgd : hf.perm (uDiagPerm ![a, b, 1] σ) d₀ = d₀ :=
    hf.1.1 (by rw [hf.apply_perm, hd₀, uDiagPerm_uD0])
  have hagP : ∀ y ∈ residue cs δ {p, l} c₀, hf.perm (uDiagPerm ![a, b, 1] σ) y = Ψ y := by
    intro y hy
    obtain ⟨hg3, hgm⟩ := planeResidueModel_uDiagPerm hf ![a, b, 1] σ hρ ((hRP y).mp hy)
      (uC0_V₃ hc₀)
    refine hpm.1.injOn ((hRP _).mpr hg3) (hiso_p.1.mapsTo hy) ?_
    rw [hgm, ← hG y hy, ← hab]
    simp
  set g := hf.perm (uDiagPerm ![a, b, 1] σ) with hgdef
  have hϑ := hΨ.inv_comp hδ hgmem hgc hgd
  have hϑc : g⁻¹ (Ψ c₀) = c₀ := by rw [hΨc, Equiv.Perm.inv_eq_iff_eq, hgc]
  have hϑd : g⁻¹ (Ψ d₀) = d₀ := by rw [hΨd, Equiv.Perm.inv_eq_iff_eq, hgd]
  have hϑP : ∀ y ∈ residue cs δ {p, l} c₀, g⁻¹ (Ψ y) = y := fun y hy => by
    rw [Equiv.Perm.inv_eq_iff_eq, hagP y hy]
  have hϑQ : ∀ y ∈ residue cs δ {π, l} c₀, g⁻¹ (Ψ y) = y := by
    have hQ := isQuadrangleFlagResidue_uC0 hpl hlπ hpπ hf hc₀
    have hpp := oppChamber_spec hδ hcd (longest cs {π, l})
    have hpR : oppChamber cs δ c₀ d₀ (longest cs {π, l}) ∈ residue cs δ {π, l} c₀ :=
      (mem_residue_iff_mem_parabolic hδ).mpr (by rw [hpp.1]; exact (isLongest_of_finite _).1)
    exact hQ.fix hδ hlπ.symm (by rw [M.symmetric]; exact hMlπ) hpR hpp.1
      (hϑ.isTypeIso_residue hδ hϑc (encard_pair_le_two π l))
      (hϑ.fix_oppChamber hδ hcd hϑc hϑd (encard_pair_le_two π l)
        (isLongest_of_finite (cs := cs) _).1)
      fun y hy => hϑP y (residue_mono (Set.singleton_subset_iff.mpr (by simp)) c₀ hy)
  have hϑR : ∀ y ∈ residue cs δ {p, π} c₀, g⁻¹ (Ψ y) = y :=
    fix_residue_of_commute hδ hpπ hMpπ (hϑ.isTypeIso_residue hδ hϑc (encard_pair_le_two p π))
      (by
        rintro y (hy | hy)
        · exact hϑP y (residue_mono (Set.singleton_subset_iff.mpr (by simp)) c₀ hy)
        · exact hϑQ y (residue_mono (Set.singleton_subset_iff.mpr (by simp)) c₀ hy))
  refine ⟨a, b, σ, fun y hy => ?_⟩
  have key : g⁻¹ (Ψ y) = y := by
    rcases hy with hy | hy
    · rcases mem_foundation_two_of_three hpl hlπ hpπ hι hy with h | h | h
      · exact hϑP y h
      · rw [Set.pair_comm] at h
        exact hϑQ y h
      · exact hϑR y h
    · rw [Set.mem_singleton_iff.mp hy]
      exact hϑd
  rw [Equiv.Perm.inv_eq_iff_eq] at key
  exact key.symm

theorem unitary_rig₂ : Rig₂ cs δ := by
  have hcd := unitary_standard_opposite hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  refine rig₂_of_transitive hδ (unitary_transitive hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀) ?_
  intro i j hij g hg hgb hfix
  have hmem : ∀ i j : ι,
      oppChamber cs δ c₀ d₀ (longest cs {i, j}) ∈ residue cs δ {i, j} c₀ := fun i j =>
    (mem_residue_iff_mem_parabolic hδ).mpr
      ((oppChamber_spec hδ hcd _).1 ▸ (isLongest_of_finite (cs := cs) _).1)
  have hspec := fun i j : ι => (oppChamber_spec hδ hcd (longest cs {i, j})).1
  have hP := isPlaneFlagResidue_uC0 hpl hlπ hpπ hf hc₀
  have hQ := isQuadrangleFlagResidue_uC0 hpl hlπ hpπ hf hc₀
  have hMπl : M π l = 4 := by rw [M.symmetric]; exact hMlπ
  rcases hι i with hi | hi | hi <;> rcases hι j with hj | hj | hj <;>
    rw [hi, hj] at hij hg hgb hfix ⊢
  · exact absurd rfl hij
  · exact hP.fix hδ hij hMpl (hmem p l) (hspec p l) hg hgb hfix
  · exact fix_residue_of_commute hδ hij hMpπ hg hfix
  · exact hP.swap.fix hδ hij (by rw [M.symmetric]; exact hMpl) (hmem l p) (hspec l p) hg hgb
      hfix
  · exact absurd rfl hij
  · rw [Set.pair_comm l π] at hg hgb ⊢
    exact hQ.fix hδ hlπ.symm hMπl (hmem π l) (hspec π l) hg hgb fun y hy => hfix y (Or.inl hy)
  · exact fix_residue_of_commute hδ hij (by rw [M.symmetric]; exact hMpπ) hg hfix
  · exact hQ.fix hδ hij hMπl (hmem π l) (hspec π l) hg hgb fun y hy => hfix y (Or.inr hy)
  · exact absurd rfl hij

theorem unitary_stabilizer :
    (∀ (a : Fin 3 → Kˣ) (σ : K ≃+* K), hf.perm (uDiagPerm a σ) ∈ typeAut cs δ ∧
      hf.perm (uDiagPerm a σ) c₀ = c₀ ∧ hf.perm (uDiagPerm a σ) d₀ = d₀) ∧
    (∀ g ∈ typeAut cs δ, g c₀ = c₀ → g d₀ = d₀ → ∃ (a : Fin 3 → Kˣ) (σ : K ≃+* K),
      Set.EqOn g (hf.perm (uDiagPerm a σ)) (foundation cs δ 2 c₀)) ∧
    (∀ (a a' : Fin 3 → Kˣ) (σ σ' : K ≃+* K),
      Set.EqOn (hf.perm (uDiagPerm a σ)) (hf.perm (uDiagPerm a' σ')) (foundation cs δ 2 c₀) ↔
        σ = σ' ∧ ∃ t : Kˣ, ∀ i, a' i = t * a i) ∧
    Nat.card {φ : foundation cs δ 2 c₀ → C //
      ∃ g ∈ typeAut cs δ, g c₀ = c₀ ∧ g d₀ = d₀ ∧ ∀ x, φ x = g x} = 18 := by
  have hfix : ∀ (a : Fin 3 → Kˣ) (σ : K ≃+* K), hf.perm (uDiagPerm a σ) ∈ typeAut cs δ ∧
      hf.perm (uDiagPerm a σ) c₀ = c₀ ∧ hf.perm (uDiagPerm a σ) d₀ = d₀ := fun a σ =>
    ⟨hf.perm_mem_typeAut (polarFlagPerm_mem_typeAut _ _ _ p l π),
      hf.1.1 (by rw [hf.apply_perm, hc₀, uDiagPerm_uC0]),
      hf.1.1 (by rw [hf.apply_perm, hd₀, uDiagPerm_uD0])⟩
  have hreal : ∀ g ∈ typeAut cs δ, g c₀ = c₀ → g d₀ = d₀ → ∃ (a : Fin 3 → Kˣ) (σ : K ≃+* K),
      Set.EqOn g (hf.perm (uDiagPerm a σ)) (foundation cs δ 2 c₀) := by
    intro g hg hgc hgd
    have hiso : IsWeylIsometry δ δ (foundation cs δ 2 c₀ ∪ {d₀})
        (foundation cs δ 2 c₀ ∪ {d₀}) g := by
      have hmem : ∀ y, g y ∈ foundation cs δ 2 c₀ ∪ {d₀} ↔
          y ∈ foundation cs δ 2 c₀ ∪ {d₀} := fun y => by
        have := apply_mem_foundation_union_iff hδ hg (x := c₀) (d := d₀) (y := y)
        rwa [hgc, hgd] at this
      refine isWeylIsometry_of hδ hδ (fun y hy => (hmem y).mpr hy) (fun y hy => ?_)
        (fun y _ z _ => dist_typeAut hδ hg y z)
      refine ⟨g⁻¹ y, (hmem _).mp ?_, Equiv.apply_symm_apply g y⟩
      rwa [show g (g⁻¹ y) = y from Equiv.apply_symm_apply g y]
    obtain ⟨a, b, σ, hA⟩ :=
      unitary_realize hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀ g hiso hgc hgd
    exact ⟨![a, b, 1], σ, fun y hy => (hA (Or.inl hy)).symm⟩
  have hρ := uRho_injOn hc₀
  have hRP := fun y => polar_mem_residue_pl hf hpl hlπ hpπ (x := c₀) (y := y)
  have hpm := isModelResidue_planeResidueModel uRho hρ hf hpl hlπ hpπ
  have hclass : ∀ (a a' : Fin 3 → Kˣ) (σ σ' : K ≃+* K),
      Set.EqOn (hf.perm (uDiagPerm a σ)) (hf.perm (uDiagPerm a' σ')) (foundation cs δ 2 c₀) ↔
        σ = σ' ∧ ∃ t : Kˣ, ∀ i, a' i = t * a i := by
    intro a a' σ σ'
    constructor
    · intro h
      have hR : residue cs δ {p, l} c₀ ⊆ foundation cs δ 2 c₀ :=
        residue_subset_foundation (encard_pair_le_two p l) c₀
      have hperm : planeDiagPerm (a 0 * (a 2)⁻¹) (a 1 * (a 2)⁻¹) σ =
          planeDiagPerm (a' 0 * (a' 2)⁻¹) (a' 1 * (a' 2)⁻¹) σ' := by
        ext1 F
        obtain ⟨y, hy, rfl⟩ := hpm.1.surjOn (Set.mem_univ F)
        obtain ⟨-, h1⟩ := planeResidueModel_uDiagPerm hf a σ hρ ((hRP y).mp hy) (uC0_V₃ hc₀)
        obtain ⟨-, h2⟩ := planeResidueModel_uDiagPerm hf a' σ' hρ ((hRP y).mp hy) (uC0_V₃ hc₀)
        rw [← h1, ← h2, h (hR hy)]
      have hinj := planeDiagPerm_injective (k := K)
        (a₁ := (a 0 * (a 2)⁻¹, a 1 * (a 2)⁻¹, σ)) (a₂ := (a' 0 * (a' 2)⁻¹, a' 1 * (a' 2)⁻¹, σ'))
        hperm
      simp only [Prod.mk.injEq] at hinj
      obtain ⟨h0, h1, hσ⟩ := hinj
      refine ⟨hσ, a' 2 * (a 2)⁻¹, fun i => ?_⟩
      fin_cases i
      · change a' 0 = a' 2 * (a 2)⁻¹ * a 0
        have e : a' 0 = a 0 * (a 2)⁻¹ * a' 2 := by rw [h0, inv_mul_cancel_right]
        rw [e]
        ac_rfl
      · change a' 1 = a' 2 * (a 2)⁻¹ * a 1
        have e : a' 1 = a 1 * (a 2)⁻¹ * a' 2 := by rw [h1, inv_mul_cancel_right]
        rw [e]
        ac_rfl
      · change a' 2 = a' 2 * (a 2)⁻¹ * a 2
        exact (inv_mul_cancel_right _ _).symm
    · rintro ⟨rfl, t, ht⟩
      have : a' = fun i => t * a i := funext ht
      rw [this, uDiagPerm_smul]
      exact fun _ _ => rfl
  refine ⟨hfix, hreal, hclass, ?_⟩
  have hk : Nat.card K = 4 := Nat.card_eq_fintype_card.trans C2E6Overlap.card_K
  have hcard : Nat.card (Kˣ × Kˣ × (K ≃+* K)) = 18 := by
    rw [Nat.card_prod, Nat.card_prod, ProjPlane.nat_card_units_of_card_four hk,
      ProjPlane.nat_card_ringEquiv_of_card_four hk]
  rw [← hcard]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun q : Kˣ × Kˣ × (K ≃+* K) => (⟨fun x => hf.perm (uDiagPerm ![q.1, q.2.1, 1] q.2.2) x.1,
      hf.perm (uDiagPerm ![q.1, q.2.1, 1] q.2.2), (hfix _ _).1, (hfix _ _).2.1, (hfix _ _).2.2,
        fun _ => rfl⟩ :
        {φ : foundation cs δ 2 c₀ → C //
          ∃ g ∈ typeAut cs δ, g c₀ = c₀ ∧ g d₀ = d₀ ∧ ∀ x, φ x = g x}))
    ⟨fun q q' h => ?_, fun φ => ?_⟩)).symm
  · obtain ⟨hσ, t, ht⟩ := (hclass _ _ _ _).mp fun y hy =>
      congrFun (congrArg Subtype.val h) ⟨y, hy⟩
    have ht2 := ht 2
    simp only [Matrix.cons_val, mul_one] at ht2
    have ht1 : t = 1 := ht2.symm
    have h0 := ht 0
    have h1 := ht 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ht1, one_mul] at h0 h1
    exact Prod.ext h0.symm (Prod.ext h1.symm hσ)
  · obtain ⟨g, hg, hgc, hgd, hφ⟩ := φ.2
    obtain ⟨a, σ, hA⟩ := hreal g hg hgc hgd
    refine ⟨((a 2)⁻¹ * a 0, (a 2)⁻¹ * a 1, σ), Subtype.ext (funext fun x => ?_)⟩
    have e : (![(a 2)⁻¹ * a 0, (a 2)⁻¹ * a 1, 1] : Fin 3 → Kˣ) = fun i => (a 2)⁻¹ * a i := by
      funext i
      fin_cases i <;> simp
    simp only
    rw [hφ x, hA x.2, e, uDiagPerm_smul]

end Main

theorem unitary_extension {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W]
    {cs : CoxeterSystem M W} [Finite W] {C C' : Type*} {δ : C → C → W} {δ' : C' → C' → W}
    (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ') {p l π : ι}
    (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π) (hι : ∀ i, i = p ∨ i = l ∨ i = π)
    (hMpl : M p l = 3) (hMlπ : M l π = 4) (hMpπ : M p π = 2) {f : C → PFlag UData}
    (hf : IsChamberModel cs δ (polarChamber UData p l π) f) {f' : C' → PFlag UData}
    (hf' : IsChamberModel cs δ' (polarChamber UData p l π) f') :
    Rig₂ cs δ ∧ Rig₂ cs δ' ∧
    ∀ (c d : C) (c' d' : C'), δ c d = longest cs Set.univ → δ' c' d' = longest cs Set.univ →
      ∀ φ : C → C', IsWeylIsometry δ δ' (foundation cs δ 2 c ∪ {d})
          (foundation cs δ' 2 c' ∪ {d'}) φ → φ c = c' → φ d = d' →
        ∃ F : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F ∧
          Set.EqOn F φ (foundation cs δ 2 c ∪ {d}) ∧
          ∀ F' : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F' →
            Set.EqOn F' φ (foundation cs δ 2 c ∪ {d}) → F' = F := by
  obtain ⟨c₀, hc₀⟩ := hf.1.2 uC0
  obtain ⟨d₀, hd₀⟩ := hf.1.2 uD0
  obtain ⟨c₀', hc₀'⟩ := hf'.1.2 uC0
  obtain ⟨d₀', hd₀'⟩ := hf'.1.2 uD0
  have hrig := unitary_rig₂ hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  refine ⟨hrig, unitary_rig₂ hδ' hpl hlπ hpπ hι hMpl hMlπ hMpπ hf' hc₀' hd₀', ?_⟩
  intro c d c' d' hcd hcd' φ hφ hφc hφd
  have htrans := unitary_transitive hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  refine ext_of_transitive hδ hrig (transitive_of_standard htrans)
    (real_of_transitive hδ htrans fun Ψ hΨ hΨc hΨd => ?_) hδ' (hf.isTypeIso hf') hcd hcd' hφ
    hφc hφd
  obtain ⟨a, b, σ, hA⟩ := unitary_realize hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀ Ψ hΨ hΨc hΨd
  exact ⟨_, hf.perm_mem_typeAut (polarFlagPerm_mem_typeAut _ _ _ p l π), hA⟩

end CFSG.Monster.B.Geometry

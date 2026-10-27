module

public import CFSG.Monster.AxisCount.FrameStab

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.VisCert
  CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice

@[expose] noncomputable def psiAmb (g : SpaceB ≃ₗ[ℚ] SpaceB) : GLV :=
  open Classical in if h : g ∈ Gvis then psiVis ⟨g, h⟩ else 1

theorem psiAmb_of_mem {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) : psiAmb g = psiVis ⟨g, hg⟩ := by
  simp only [psiAmb, hg, ↓reduceDIte]

theorem psiAmb_one : psiAmb 1 = 1 := by
  rw [psiAmb_of_mem Gvis.one_mem]
  exact map_one psiVis

theorem psiAmb_mul {g g' : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) (hg' : g' ∈ Gvis) :
    psiAmb (g * g') = psiAmb g * psiAmb g' := by
  have e : (⟨g * g', Gvis.mul_mem hg hg'⟩ : Gvis) = ⟨g, hg⟩ * ⟨g', hg'⟩ := rfl
  rw [psiAmb_of_mem hg, psiAmb_of_mem hg', psiAmb_of_mem (Gvis.mul_mem hg hg'), e, map_mul]

theorem psiAmb_inv {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) : psiAmb g⁻¹ = (psiAmb g)⁻¹ := by
  have e : (⟨g⁻¹, Gvis.inv_mem hg⟩ : Gvis) = (⟨g, hg⟩ : Gvis)⁻¹ := rfl
  rw [psiAmb_of_mem hg, psiAmb_of_mem (Gvis.inv_mem hg), e, map_inv]

theorem mem_Nfr_iff_psiAmb {g : SpaceB ≃ₗ[ℚ] SpaceB} :
    g ∈ Nfr ↔ g ∈ Gvis ∧ psiAmb g • twoΩCls = twoΩCls := by
  constructor
  · intro h
    obtain ⟨hg, hf⟩ := mem_Nfr.1 h
    exact ⟨hg, by rwa [psiAmb_of_mem hg]⟩
  · rintro ⟨hg, hf⟩
    exact mem_Nfr.2 ⟨hg, by rwa [psiAmb_of_mem hg] at hf⟩

@[expose] def psiOrbit (U : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)) (x : L2) : Set L2 :=
  {y | ∃ u ∈ U, psiAmb u • x = y}

theorem mem_psiOrbit_self {U : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (x : L2) : x ∈ psiOrbit U x :=
  ⟨1, U.one_mem, by rw [psiAmb_one, one_smul]⟩

section Cover

variable {H U : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)}

theorem psiAmb_inv_smul_frame_of_mem_Nfr {n : SpaceB ≃ₗ[ℚ] SpaceB} (hn : n ∈ Nfr) :
    (psiAmb n)⁻¹ • twoΩCls = twoΩCls := by
  have h := (mem_Nfr_iff_psiAmb.1 hn).2
  rw [inv_smul_eq_iff]
  exact h.symm

theorem mem_doubleCoset_of_eq {h g u : SpaceB ≃ₗ[ℚ] SpaceB} (hH : H ≤ Gvis) (hU : U ≤ H)
    (hh : h ∈ H) (hg : g ∈ H) (hu : u ∈ U)
    (e : (psiAmb g)⁻¹ • twoΩCls = psiAmb u • (psiAmb h)⁻¹ • twoΩCls) :
    g ∈ DoubleCoset.doubleCoset h ((H ⊓ Nfr : Subgroup _) : Set _) (U : Set _) := by
  refine DoubleCoset.mem_doubleCoset.2 ⟨g * u * h⁻¹, ?_, u⁻¹, U.inv_mem hu, by group⟩
  have hgG := hH hg
  have huG := hH (hU hu)
  have hhG := hH hh
  refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.mul_mem hg (hU hu)) (H.inv_mem hh), ?_⟩
  refine mem_Nfr_iff_psiAmb.2 ⟨Gvis.mul_mem (Gvis.mul_mem hgG huG) (Gvis.inv_mem hhG), ?_⟩
  rw [psiAmb_mul (Gvis.mul_mem hgG huG) (Gvis.inv_mem hhG), psiAmb_mul hgG huG,
    psiAmb_inv hhG, mul_smul, mul_smul, ← e, smul_inv_smul]

theorem subset_iUnion_doubleCoset_amb {R : Type*} (hH : H ≤ Gvis) (hU : U ≤ H)
    {h : R → SpaceB ≃ₗ[ℚ] SpaceB} (hh : ∀ r, h r ∈ H)
    (hcov : ∀ g ∈ H, ∃ r, ∃ u ∈ U, (psiAmb g)⁻¹ • twoΩCls = psiAmb u • (psiAmb (h r))⁻¹ • twoΩCls) :
    (H : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ⊆ ⋃ r, DoubleCoset.doubleCoset (h r)
      ((H ⊓ Nfr : Subgroup _) : Set _) (U : Set _) := by
  intro g hg
  obtain ⟨r, u, hu, e⟩ := hcov g hg
  exact Set.mem_iUnion.2 ⟨r, mem_doubleCoset_of_eq hH hU (hh r) hg hu e⟩

theorem psiAmb_inv_smul_of_mem_doubleCoset {h g : SpaceB ≃ₗ[ℚ] SpaceB} (hH : H ≤ Gvis)
    (hU : U ≤ H) (hh : h ∈ H)
    (hg : g ∈ DoubleCoset.doubleCoset h ((H ⊓ Nfr : Subgroup _) : Set _) (U : Set _)) :
    ∃ u ∈ U, (psiAmb g)⁻¹ • twoΩCls = psiAmb u • (psiAmb h)⁻¹ • twoΩCls := by
  obtain ⟨n, hn, u, hu, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  have hnG := hH (Subgroup.mem_inf.1 hn).1
  have hhG := hH hh
  have huG := hH (hU hu)
  refine ⟨u⁻¹, U.inv_mem hu, ?_⟩
  rw [psiAmb_mul (Gvis.mul_mem hnG hhG) huG, psiAmb_mul hnG hhG, psiAmb_inv huG, mul_inv_rev,
    mul_inv_rev, mul_smul, mul_smul, psiAmb_inv_smul_frame_of_mem_Nfr (Subgroup.mem_inf.1 hn).2]

theorem disjoint_doubleCoset_amb {h h' : SpaceB ≃ₗ[ℚ] SpaceB} (hH : H ≤ Gvis) (hU : U ≤ H)
    (hh : h ∈ H) (hh' : h' ∈ H)
    (hd : Disjoint (psiOrbit U ((psiAmb h)⁻¹ • twoΩCls)) (psiOrbit U ((psiAmb h')⁻¹ • twoΩCls))) :
    Disjoint (DoubleCoset.doubleCoset h ((H ⊓ Nfr : Subgroup _) : Set _) (U : Set _))
      (DoubleCoset.doubleCoset h' ((H ⊓ Nfr : Subgroup _) : Set _) (U : Set _)) := by
  refine Set.disjoint_left.2 fun g hg hg' => ?_
  obtain ⟨u, hu, e⟩ := psiAmb_inv_smul_of_mem_doubleCoset hH hU hh hg
  obtain ⟨u', hu', e'⟩ := psiAmb_inv_smul_of_mem_doubleCoset hH hU hh' hg'
  exact Set.disjoint_left.1 hd (show (psiAmb g)⁻¹ • twoΩCls ∈ psiOrbit U _ from ⟨u, hu, e.symm⟩)
    (show (psiAmb g)⁻¹ • twoΩCls ∈ psiOrbit U _ from ⟨u', hu', e'.symm⟩)

theorem natCard_doubleCoset_amb (hH : H ≤ Gvis) (hU : U ≤ H) {h : SpaceB ≃ₗ[ℚ] SpaceB}
    (hh : h ∈ H) :
    Nat.card (DoubleCoset.doubleCoset h ((H ⊓ Nfr : Subgroup _) : Set _) (U : Set _)) =
      Nat.card (H ⊓ Nfr : Subgroup _) * Nat.card (psiOrbit U ((psiAmb h)⁻¹ • twoΩCls)) := by
  classical
  set N : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := H ⊓ Nfr with hN
  set D : Set (SpaceB ≃ₗ[ℚ] SpaceB) := DoubleCoset.doubleCoset h (N : Set _) (U : Set _) with hD
  have hDH : ∀ g ∈ D, g ∈ H := by
    intro g hg
    obtain ⟨n, hn, u, hu, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    exact H.mul_mem (H.mul_mem (Subgroup.mem_inf.1 hn).1 hh) (hU hu)
  let Φ : D → L2 := fun g => (psiAmb (g : SpaceB ≃ₗ[ℚ] SpaceB))⁻¹ • twoΩCls
  have hrange : Set.range Φ = psiOrbit U ((psiAmb h)⁻¹ • twoΩCls) := by
    ext x
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨u, hu, e⟩ := psiAmb_inv_smul_of_mem_doubleCoset hH hU hh hg
      exact ⟨u, hu, e.symm⟩
    · rintro ⟨u, hu, rfl⟩
      have hhG := hH hh
      have huG := hH (hU hu)
      refine ⟨⟨h * u⁻¹, DoubleCoset.mem_doubleCoset.2 ⟨1, N.one_mem, u⁻¹, U.inv_mem hu,
        by group⟩⟩, ?_⟩
      show (psiAmb (h * u⁻¹))⁻¹ • twoΩCls = psiAmb u • (psiAmb h)⁻¹ • twoΩCls
      rw [psiAmb_mul hhG (Gvis.inv_mem huG), psiAmb_inv huG, mul_inv_rev, inv_inv, mul_smul]
  let Φ' : D → Set.range Φ := Set.rangeFactorization Φ
  have hfib : ∀ g₀ : D, Nonempty ({g : D // Φ' g = Φ' g₀} ≃ N) := by
    intro g₀
    have hg₀G := hH (hDH g₀ g₀.2)
    have key : ∀ g : D, Φ' g = Φ' g₀ →
        (g : SpaceB ≃ₗ[ℚ] SpaceB) * (g₀ : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ ∈ N := by
      intro g hg
      have e : (psiAmb (g : SpaceB ≃ₗ[ℚ] SpaceB))⁻¹ • twoΩCls =
          (psiAmb (g₀ : SpaceB ≃ₗ[ℚ] SpaceB))⁻¹ • twoΩCls := congrArg Subtype.val hg
      have hgG := hH (hDH g g.2)
      refine Subgroup.mem_inf.2 ⟨H.mul_mem (hDH g g.2) (H.inv_mem (hDH g₀ g₀.2)),
        mem_Nfr_iff_psiAmb.2 ⟨Gvis.mul_mem hgG (Gvis.inv_mem hg₀G), ?_⟩⟩
      rw [psiAmb_mul hgG (Gvis.inv_mem hg₀G), psiAmb_inv hg₀G, mul_smul, ← e, smul_inv_smul]
    have key' : ∀ n : N, ((n : SpaceB ≃ₗ[ℚ] SpaceB) * (g₀ : SpaceB ≃ₗ[ℚ] SpaceB)) ∈ D := by
      intro n
      obtain ⟨m, hm, u, hu, hg₀'⟩ := DoubleCoset.mem_doubleCoset.1 g₀.2
      exact DoubleCoset.mem_doubleCoset.2 ⟨n * m, N.mul_mem n.2 hm, u, hu, by rw [hg₀']; group⟩
    refine ⟨{ toFun := fun g => ⟨(g : D) * (g₀ : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹, key g g.2⟩
              invFun := fun n =>
                ⟨⟨(n : SpaceB ≃ₗ[ℚ] SpaceB) * (g₀ : SpaceB ≃ₗ[ℚ] SpaceB), key' n⟩, ?_⟩
              left_inv := fun g => Subtype.ext (Subtype.ext (by simp))
              right_inv := fun n => Subtype.ext (by simp) }⟩
    apply Subtype.ext
    show (psiAmb ((n : SpaceB ≃ₗ[ℚ] SpaceB) * (g₀ : SpaceB ≃ₗ[ℚ] SpaceB)))⁻¹ • twoΩCls =
      (psiAmb (g₀ : SpaceB ≃ₗ[ℚ] SpaceB))⁻¹ • twoΩCls
    have hnG := hH (Subgroup.mem_inf.1 n.2).1
    rw [psiAmb_mul hnG hg₀G, mul_inv_rev, mul_smul,
      psiAmb_inv_smul_frame_of_mem_Nfr (Subgroup.mem_inf.1 n.2).2]
  calc Nat.card D = Nat.card (Σ y : Set.range Φ, {g : D // Φ' g = y}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv Φ').symm
    _ = Nat.card (Σ _ : Set.range Φ, N) := by
        refine Nat.card_congr (Equiv.sigmaCongrRight fun y => Classical.choice ?_)
        obtain ⟨g₀, rfl⟩ := Set.rangeFactorization_surjective y
        exact hfib g₀
    _ = Nat.card N * Nat.card (psiOrbit U ((psiAmb h)⁻¹ • twoΩCls)) := by
        rw [Nat.card_congr (Equiv.sigmaEquivProd _ _), Nat.card_prod, mul_comm, hrange]

end Cover

end CFSG.Monster.AxisCount

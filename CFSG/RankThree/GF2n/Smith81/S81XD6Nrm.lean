module

public import CFSG.RankThree.GF2n.Smith81.S81XD6Def
public import CFSG.RankThree.GF2n.Smith81.S81XE7Nrm
public import CFSG.RankThree.GF2n.Smith81.S81XD6Fin

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.D6Spin


variable {K : Type} [Field K]

theorem tor_diag {t : Gp K} (ht : t ∈ Tor K) (a : Fin e7Data.d) :
    ∃ s : K, s ≠ 0 ∧ endoE t (Finsupp.single a 1) = s • Finsupp.single a 1 := by
  obtain ⟨c, hc⟩ := endo_tor_single (K := K) ht a
  refine ⟨c, ?_, hc⟩
  intro hc0
  have hz : endoE t (Finsupp.single a 1) = 0 := by rw [hc, hc0, zero_smul]
  have h1 : endoE t⁻¹ (endoE t (Finsupp.single a 1)) = Finsupp.single a 1 := by
    rw [← Module.End.mul_apply, e7Data_valid.endo_inv_mul, Module.End.one_apply]
  rw [hz, map_zero] at h1
  have hne : (Finsupp.single a (1 : K) : Fin e7Data.d →₀ K) ≠ 0 :=
    Finsupp.single_ne_zero.2 one_ne_zero
  exact hne h1.symm

private theorem d6nrm_xm_mem_normalizer {a : Fin e7Data.d} {β : Fin (Tag.rank .E7) → ℤ}
    (hβ : IsRoot .E7 β) (hpr : pr a β ≠ -1) (c : K) :
    e7Data_valid.xm K β c ∈ Subgroup.normalizer (UA K a : Set (Gp K)) := by
  refine Subgroup.mem_normalizer_iff.2 fun z => ⟨conj_UA_xE hβ hpr c z, fun hz => ?_⟩
  have h2 := conj_UA_xE hβ hpr (-c) _ hz
  have hneg : e7Data_valid.xm K β (-c) * (e7Data_valid.xm K β c * z * (e7Data_valid.xm K β c)⁻¹) *
      (e7Data_valid.xm K β (-c))⁻¹ = z := by
    rw [← e7Data_valid.xm_neg K β c]
    group
  rwa [hneg] at h2

private theorem d6nrm_UL_normalizer {a : Fin e7Data.d}
    (hdom : ∀ β : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 β → MinData.toWeight β ⬝ᵥ theta = 0 →
      0 < height β → pr a β ≠ -1)
    {g : (Module.End K (V K))ˣ} (hg : g ∈ UL K) :
    ∃ h : g ∈ e7Data_valid.minGroup K, (⟨g, h⟩ : Gp K) ∈ Subgroup.normalizer (UA K a : Set (Gp K)) := by
  unfold UL at hg
  refine Subgroup.closure_induction (p := fun (g : (Module.End K (V K))ˣ) _ =>
    ∃ h : g ∈ e7Data_valid.minGroup K, (⟨g, h⟩ : Gp K) ∈ Subgroup.normalizer (UA K a : Set (Gp K))) ?_ ?_ ?_ ?_ hg
  · rintro x ⟨β, hβ, hzero, hpos, c, rfl⟩
    exact ⟨e7Data_valid.xu_mem K β c, d6nrm_xm_mem_normalizer hβ (hdom β hβ hzero hpos) c⟩
  · exact ⟨one_mem _, one_mem _⟩
  · rintro x y _ _ ⟨hx, hxN⟩ ⟨hy, hyN⟩
    exact ⟨mul_mem hx hy, mul_mem hxN hyN⟩
  · rintro x _ ⟨hx, hN⟩
    exact ⟨inv_mem hx, inv_mem hN⟩

variable [CharP K 2]

theorem conj_UA_ULG {u : Gp K} (hu : u ∈ ULG K) : ∀ x ∈ UA K b0, u * x * u⁻¹ ∈ UA K b0 := by
  obtain ⟨_, hN⟩ := d6nrm_UL_normalizer (a := b0) dom0 (mem_ULG.1 hu)
  intro x hx
  exact (Subgroup.mem_normalizer_iff.1 hN x).1 hx

set_option maxRecDepth 20000 in
private theorem d6nrm_UL_fix {a : Fin e7Data.d}
    (hdom : ∀ β : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 β → MinData.toWeight β ⬝ᵥ theta = 0 →
      0 < height β → pr a β ≠ -1)
    {g : (Module.End K (V K))ˣ} (hg : g ∈ UL K) :
    (g : Module.End K (V K)) (Finsupp.single a 1) = Finsupp.single a 1 := by
  unfold UL at hg
  refine Subgroup.closure_induction (p := fun (g : (Module.End K (V K))ˣ) _ =>
    (g : Module.End K (V K)) (Finsupp.single a 1) = Finsupp.single a 1) ?_ ?_ ?_ ?_ hg
  · rintro x ⟨β, hβ, hzero, hpos, c, rfl⟩
    show ((e7Data_valid.xu K β c : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1) =
      Finsupp.single a 1
    rw [e7Data_valid.xu_apply, rootOp_single (K := K) hβ a, if_neg (hdom β hβ hzero hpos), smul_zero,
      add_zero]
  · show ((1 : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1) = Finsupp.single a 1
    rw [Units.val_one, Module.End.one_apply]
  · rintro x y _ _ hx hy
    have hx' : ((x : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1) =
        Finsupp.single a 1 := hx
    have hy' : ((y : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1) =
        Finsupp.single a 1 := hy
    show ((x * y : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1) =
      Finsupp.single a 1
    rw [Units.val_mul, Module.End.mul_apply, hy', hx']
  · rintro x _ hx
    have hx' : ((x : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1) =
        Finsupp.single a 1 := hx
    show ((x⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1) =
      Finsupp.single a 1
    calc ((x⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1)
        = ((x⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
            (((x : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1)) := by rw [hx']
      _ = Finsupp.single a 1 := by
        rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

theorem ULG_fix {u : Gp K} (hu : u ∈ ULG K) :
    endoE u (Finsupp.single b0 1) = Finsupp.single b0 1 := by
  exact d6nrm_UL_fix (a := b0) dom0 (mem_ULG.1 hu)

end CFSG.RankThree.GF2n.Smith81.D6X

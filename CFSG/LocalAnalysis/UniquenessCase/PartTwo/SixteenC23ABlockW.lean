module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AEquivStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModDefs
public import CFSG.Quasithin.Background.FFC5T7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23a_blockw_kernel {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : Hyp151 D ⊥ V L)
    (f : Vtil ⊥ V hV →* Vtil (v1Sub D.M ⊥ V hV L) V hV)
    (hf : ∀ x : IntMod V hV, f (mkTil ⊥ V hV x) = mkTil (v1Sub D.M ⊥ V hV L) V hV x)
    {w : Vtil ⊥ V hV} (hw : w ∈ wTil ⊥ V hV L) :
    f w = 1 ↔ w ∈ fixV (barSub ⊥ V hV L) := by
  constructor
  · intro hf1
    obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV w
    have hxV₁ : x.val ∈ v1Sub D.M ⊥ V hV L := by
      have h1 : mkTil (v1Sub D.M ⊥ V hV L) V hV x = 1 := by
        rw [← hf x]
        exact hf1
      have h2 : mkTil (v1Sub D.M ⊥ V hV L) V hV x =
          mkTil (v1Sub D.M ⊥ V hV L) V hV 1 := by rw [h1, map_one]
      have h3 := (mkTil_eq_iff (v1Sub D.M ⊥ V hV L) V hV x 1).1 h2
      simpa using h3
    have hmem : mkTil ⊥ V hV x ∈ imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) :=
      (mem_imgTil ⊥ V hV _ _).2 ⟨x, hxV₁, rfl⟩
    have hle := s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
    rw [conjSubgroup_one] at hle
    exact hle hmem
  · intro hwFix
    obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV w
    have hxw : x.val ∈ wSub ⊥ V hV L :=
      (mem_preTil ⊥ V hV (wTil ⊥ V hV L)).2 ⟨x, rfl, hw⟩
    have hcen : x.val ∈ centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hMs : D.M ≤ stabTil ⊥ V :=
        le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
      have hgs : l ∈ stabTil ⊥ V := hMs (h.le hl)
      have hact : actTil ⊥ V hV ⟨l, hgs⟩ ∈ barSub ⊥ V hV L :=
        actTil_mem_barSub ⊥ V hV hl hgs
      have hfix := (mem_fixV.mp hwFix) (actTil ⊥ V hV ⟨l, hgs⟩) hact
      have h1 : mkTil ⊥ V hV (actStab ⊥ V hV ⟨l, hgs⟩ x) = mkTil ⊥ V hV x := by
        rw [← actTil_mk]
        exact hfix
      have h2 := (mkTil_eq_iff ⊥ V hV _ x).1 h1
      rw [Subgroup.mem_bot, mul_inv_eq_one] at h2
      have h3 := actStab_apply_val ⊥ V hV ⟨l, hgs⟩ x
      rw [h3] at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    have hxV₁ : x.val ∈ v1Sub D.M ⊥ V hV L := by
      rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
      refine (le_iSup (fun m : D.M =>
        conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) (m : G))
        ⟨1, D.M.one_mem⟩) ?_
      simpa [conjSubgroup_one] using
        (show x.val ∈ wSub ⊥ V hV L ⊓ centralizer (L : Set G) from ⟨hxw, hcen⟩)
    rw [hf x]
    rw [show (1 : Vtil (v1Sub D.M ⊥ V hV L) V hV) =
      mkTil (v1Sub D.M ⊥ V hV L) V hV 1 from (map_one _).symm]
    rw [mkTil_eq_iff]
    simpa using hxV₁

theorem c23a_block_wTil (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (h : Hyp151 D ⊥ V L)
    (hn : BinaryNaturalSL (lStar D.M ⊥ V hV L) (wStar D.M ⊥ V hV L) ⊥ 3 1) :
    C23ABlock (barSub ⊥ V hV L) (wTil ⊥ V hV L) (wTil ⊥ V hV L ⊓ fixV (barSub ⊥ V hV L)) := by
  obtain ⟨N⟩ := exists_natQuot3 hn
  obtain ⟨f, ρ, hf, hρ⟩ := c23a_equiv_star D h1217 h hV h.le rfl
  let Wtil : Subgroup (Vtil ⊥ V hV) := wTil ⊥ V hV L
  let Lbar : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV L
  have hf_mem : ∀ w ∈ Wtil, f w ∈ wStar D.M ⊥ V hV L := by
    intro w hw
    obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV w
    rw [hf x]
    refine (mem_imgTil (v1Sub D.M ⊥ V hV L) V hV (wSub ⊥ V hV L) _).2 ⟨x, ?_, rfl⟩
    exact (mem_preTil ⊥ V hV (wTil ⊥ V hV L)).2 ⟨x, rfl, hw⟩
  let fW : ↥Wtil →* ↥(wStar D.M ⊥ V hV L) :=
    (f.comp Wtil.subtype).codRestrict _ (fun u => hf_mem (u : Vtil ⊥ V hV) u.2)
  have hfW_surj : Function.Surjective fW := by
    intro s
    obtain ⟨x, hxw, hxeq⟩ :=
      (mem_imgTil (v1Sub D.M ⊥ V hV L) V hV (wSub ⊥ V hV L)
        (s : Vtil (v1Sub D.M ⊥ V hV L) V hV)).1 s.2
    obtain ⟨y, hyval, hyW⟩ := (mem_preTil ⊥ V hV (wTil ⊥ V hV L)).1 hxw
    have hyx : y = x := IntMod.val_injective hyval
    refine ⟨⟨mkTil ⊥ V hV x, hyx ▸ hyW⟩, ?_⟩
    apply Subtype.ext
    show f (mkTil ⊥ V hV x) = (s : Vtil (v1Sub D.M ⊥ V hV L) V hV)
    rw [hf x, hxeq]
  let ρ' : SL3F2 →* ↥Lbar := ρ.symm.toMonoidHom.comp N.ρ
  have hρ' : ∀ g : SL3F2, ρ (ρ' g) = N.ρ g := fun g => by
    change ρ (ρ.symm (N.ρ g)) = N.ρ g
    exact MulEquiv.apply_symm_apply ρ (N.ρ g)
  have hρ'_surj : Function.Surjective ρ' := ρ.symm.surjective.comp N.surj
  have hρ'_inj : Function.Injective ρ' := ρ.symm.injective.comp N.inj
  let θ' : ↥Wtil →* Multiplicative (Fin 3 → ZMod 2) := N.θ.comp fW
  have hθ'_surj : Function.Surjective θ' := N.θ_surj.comp hfW_surj
  have hθ'_ker : ∀ u : ↥Wtil, θ' u = 1 ↔ (u : Vtil ⊥ V hV) ∈ Wtil ⊓ fixV Lbar := by
    intro u
    change N.θ (fW u) = 1 ↔ (u : Vtil ⊥ V hV) ∈ Wtil ⊓ fixV Lbar
    rw [N.θ_ker, Subgroup.mem_bot]
    constructor
    · intro hz
      rw [Subgroup.mem_inf]
      refine ⟨u.2, ?_⟩
      exact (c23a_blockw_kernel h f hf u.2).1 (by
        change f (u : Vtil ⊥ V hV) = 1 at hz
        exact hz)
    · intro hz
      rw [Subgroup.mem_inf] at hz
      change f (u : Vtil ⊥ V hV) = 1
      exact (c23a_blockw_kernel h f hf u.2).2 hz.2
  let invP : ∀ (g : SL3F2) (u : Vtil ⊥ V hV), u ∈ Wtil →
      ((ρ' g : ↥Lbar) : MulAut (Vtil ⊥ V hV)) u ∈ Wtil := by
    intro g u hu
    have hu' : u ∈ commV Lbar := by
      rw [commV_eq_commSub]
      exact hu
    change ((ρ' g : ↥Lbar) : MulAut (Vtil ⊥ V hV)) u ∈ commSub ⊤ Lbar
    rw [← commV_eq_commSub]
    exact commV_invariant_self Lbar (ρ' g) (ρ' g).2 u hu'
  let D' : NatQuot3 (barSub ⊥ V hV L) (wTil ⊥ V hV L)
      (wTil ⊥ V hV L ⊓ fixV (barSub ⊥ V hV L)) :=
    { ρ := ρ'
      surj := hρ'_surj
      inj := hρ'_inj
      θ := θ'
      θ_surj := hθ'_surj
      θ_ker := hθ'_ker
      inv := invP
      equiv := by
        intro g u
        change N.θ (fW ⟨((ρ' g : ↥Lbar) : MulAut (Vtil ⊥ V hV)) (u : Vtil ⊥ V hV),
            invP g (u : Vtil ⊥ V hV) u.2⟩) =
          Multiplicative.ofAdd (g • Multiplicative.toAdd (N.θ (fW u)))
        have hsub : fW ⟨((ρ' g : ↥Lbar) : MulAut (Vtil ⊥ V hV)) (u : Vtil ⊥ V hV),
              invP g (u : Vtil ⊥ V hV) u.2⟩ =
            (⟨((N.ρ g : ↥(barSub (v1Sub D.M ⊥ V hV L) V hV L)) :
                MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV))
                ((fW u : ↥(wStar D.M ⊥ V hV L)) : Vtil (v1Sub D.M ⊥ V hV L) V hV),
              N.inv g ((fW u : ↥(wStar D.M ⊥ V hV L)) : Vtil (v1Sub D.M ⊥ V hV L) V hV)
                (fW u).2⟩ : ↥(wStar D.M ⊥ V hV L)) := by
          apply Subtype.ext
          change f (((ρ' g : ↥Lbar) : MulAut (Vtil ⊥ V hV)) (u : Vtil ⊥ V hV)) =
            ((N.ρ g : ↥(barSub (v1Sub D.M ⊥ V hV L) V hV L)) :
              MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV)) (f (u : Vtil ⊥ V hV))
          exact (hρ (ρ' g) (u : Vtil ⊥ V hV)).trans
            (congrArg (fun a : ↥(barSub (v1Sub D.M ⊥ V hV L) V hV L) =>
              ((a : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV)) (f (u : Vtil ⊥ V hV))))
              (hρ' g))
        rw [hsub]
        exact N.equiv g (fW u) }
  refine ⟨⟨D'⟩, ?_, rfl⟩
  · show commSub (wTil ⊥ V hV L) (barSub ⊥ V hV L) = wTil ⊥ V hV L
    unfold wTil
    rw [← commV_eq_commSub]
    exact le_antisymm (commSub_le_of_invariant (commV_invariant_self Lbar))
      (commV_le_commSub_of_perfect (perfect_of_natQuot3 D')
        (fun g hg v => Subgroup.subset_closure ⟨g, hg, v, rfl⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

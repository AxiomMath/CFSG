module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Kit1
public import CFSG.Quasithin.Background.FFC4Zmod
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.Quasithin.Vol2.KGFactSLnTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F CFSG.Assembly.LowTwoRank
open Matrix

structure Close16PtStab {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (w : W) : Prop where
  maximal : ∀ J : Subgroup (MulAut W), H ⊓ MulAction.stabilizer (MulAut W) w ≤ J → J ≤ H →
    J = H ⊓ MulAction.stabilizer (MulAut W) w ∨ J = H
  card : Nat.card ↥(H ⊓ MulAction.stabilizer (MulAut W) w) = 1344
  opp : Opp 3 (H ⊓ MulAction.stabilizer (MulAut W) w) = H ⊓ MulAction.stabilizer (MulAut W) w
  quot : ∃ f : ↥(H ⊓ MulAction.stabilizer (MulAut W) w) →*
      SpecialLinearGroup (Fin 3) (ZMod 2),
    Function.Surjective f ∧ IsPGroup 2 f.ker ∧ Nat.card f.ker = 8

private theorem close16_nat_setup {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U : Subgroup W} (hnat : BinaryNaturalSL H U ⊥ 4 1) :
    ∃ (π : ↥(StatedSL 4 (ZMod 2)) →* ↥H)
      (f : ↥U →* Multiplicative (Fin 4 → ZMod 2)),
      Function.Surjective π ∧ Function.Surjective f ∧ Function.Injective f ∧
      (∀ h : ↥H, ∀ u ∈ U, (h : MulAut W) u ∈ U) ∧
      (∀ (γ : ↥(StatedSL 4 (ZMod 2))) (u : ↥U)
        (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ U),
        f ⟨_, hu⟩ = natAct (StatedSL 4 (ZMod 2)) γ (f u)) := by
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hnat
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ
  have hfi : Function.Injective f := by
    intro a b hab
    have h1 : f (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab]
      exact mul_inv_cancel (f b)
    have h2 : (a * b⁻¹ : ↥U) = 1 :=
      Subtype.ext (Subgroup.mem_bot.1 ((hfk (a * b⁻¹)).1 h1))
    exact mul_inv_eq_one.1 h2
  exact ⟨π, f, hπ.1, hfs, hfi, hπ.2.2.2.1, hfe⟩

theorem close16_natural_transitive {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U : Subgroup W} (hnat : BinaryNaturalSL H U ⊥ 4 1) {u v : W} (hu : u ∈ U) (hv : v ∈ U)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) : ∃ h ∈ H, h u = v := by
  obtain ⟨π, f, hπs, hfs, hfi, hHU, hfe⟩ := close16_nat_setup hnat
  set x : Fin 4 → ZMod 2 := Multiplicative.toAdd (f ⟨u, hu⟩) with hxdef
  set y : Fin 4 → ZMod 2 := Multiplicative.toAdd (f ⟨v, hv⟩) with hydef
  have hxu : f ⟨u, hu⟩ ≠ 1 := by
    intro h1
    have h2 : f ⟨u, hu⟩ = f (1 : ↥U) := by rw [h1, map_one]
    exact hu1 (congrArg Subtype.val (hfi h2))
  have hyv : f ⟨v, hv⟩ ≠ 1 := by
    intro h1
    have h2 : f ⟨v, hv⟩ = f (1 : ↥U) := by rw [h1, map_one]
    exact hv1 (congrArg Subtype.val (hfi h2))
  have hx : x ≠ 0 := by
    rw [hxdef]
    intro h0
    exact hxu ((toAdd_eq_zero).1 h0)
  have hy : y ≠ 0 := by
    rw [hydef]
    intro h0
    exact hyv ((toAdd_eq_zero).1 h0)
  obtain ⟨g₁, hg₁⟩ := CFSG.Quasithin.SLnTwo.exists_mulVec_eq (n := 4) (by norm_num) hx
  obtain ⟨g₂, hg₂⟩ := CFSG.Quasithin.SLnTwo.exists_mulVec_eq (n := 4) (by norm_num) hy
  let g : SpecialLinearGroup (Fin 4) (ZMod 2) := g₂ * g₁⁻¹
  have hgx : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = y := by
    change ((g₂ * g₁⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = y
    rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, mulVec_inv_of_mulVec hg₁, hg₂]
  set γ : ↥(StatedSL 4 (ZMod 2)) := specialLinearGroupEquivStatedSL 4 (ZMod 2) g with hγdef
  have hnat : natAct (StatedSL 4 (ZMod 2)) γ (f ⟨u, hu⟩) = f ⟨v, hv⟩ := by
    have h1 : natAct (StatedSL 4 (ZMod 2)) γ (f ⟨u, hu⟩) =
        Multiplicative.ofAdd ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) := by
      simp only [natAct, hγdef, specialLinearGroupEquivStatedSL_coe]
      rfl
    rw [h1, hgx]
    exact ofAdd_toAdd (f ⟨v, hv⟩)
  have hfin : f ⟨((π γ : ↥H) : MulAut W) u, hHU (π γ) u hu⟩ = f ⟨v, hv⟩ := by
    rw [hfe γ ⟨u, hu⟩ (hHU (π γ) u hu)]
    exact hnat
  refine ⟨π γ, (π γ).2, ?_⟩
  exact congrArg Subtype.val (hfi hfin)

theorem close16_natural_stab {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U : Subgroup W}
    (hH : Nat.card H = 20160) (hnat : BinaryNaturalSL H U ⊥ 4 1) {u : W} (hu : u ∈ U)
    (hu1 : u ≠ 1) : Close16PtStab H u := by
  obtain ⟨π, f, hπs, hfs, hfi, hHU, hfe⟩ := close16_nat_setup hnat
  have hπinj : Function.Injective π := by
    have hcard : Nat.card π.ker = 1 := by
      have h := Subgroup.card_ker_mul_card_of_surjective hπs
      rw [hH, ← Nat.card_congr (specialLinearGroupEquivStatedSL 4 (ZMod 2)).toEquiv,
        card_SL_four_two] at h
      haveI : Nonempty ↥π.ker := ⟨⟨1, π.ker.one_mem⟩⟩
      have hpos : 0 < Nat.card π.ker := Nat.card_pos
      omega
    exact (MonoidHom.ker_eq_bot_iff π).1 (Subgroup.card_eq_one.1 hcard)
  set x : Fin 4 → ZMod 2 := Multiplicative.toAdd (f ⟨u, hu⟩) with hxdef
  have hxu : f ⟨u, hu⟩ ≠ 1 := by
    intro h1
    have h2 : f ⟨u, hu⟩ = f (1 : ↥U) := by rw [h1, map_one]
    exact hu1 (congrArg Subtype.val (hfi h2))
  have hx : x ≠ 0 := by
    rw [hxdef]
    intro h0
    exact hxu ((toAdd_eq_zero).1 h0)
  let σ : SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥H :=
    π.comp (specialLinearGroupEquivStatedSL 4 (ZMod 2)).toMonoidHom
  let φ : SpecialLinearGroup (Fin 4) (ZMod 2) →* MulAut W := H.subtype.comp σ
  have hσs : Function.Surjective σ :=
    hπs.comp (specialLinearGroupEquivStatedSL 4 (ZMod 2)).surjective
  have hσinj : Function.Injective σ :=
    hπinj.comp (specialLinearGroupEquivStatedSL 4 (ZMod 2)).injective
  have hφ : Function.Injective φ := by
    intro a b hab
    exact hσinj (Subtype.ext hab)
  have hφapply : ∀ g : SpecialLinearGroup (Fin 4) (ZMod 2),
      φ g = ((π (specialLinearGroupEquivStatedSL 4 (ZMod 2) g) : ↥H) : MulAut W) :=
    fun g => rfl
  have hnat : ∀ (g : SpecialLinearGroup (Fin 4) (ZMod 2))
      (y : Multiplicative (Fin 4 → ZMod 2)),
      natAct (StatedSL 4 (ZMod 2)) (specialLinearGroupEquivStatedSL 4 (ZMod 2) g) y =
        Multiplicative.ofAdd ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          Multiplicative.toAdd y) := by
    intro g y
    simp only [natAct, specialLinearGroupEquivStatedSL_coe]
  have hstep : ∀ g : SpecialLinearGroup (Fin 4) (ZMod 2),
      f ⟨(φ g : MulAut W) u, hHU (σ g) u hu⟩ =
        Multiplicative.ofAdd ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) := by
    intro g
    change f ⟨((π (specialLinearGroupEquivStatedSL 4 (ZMod 2) g) : ↥H) : MulAut W) u,
      hHU (σ g) u hu⟩ =
        Multiplicative.ofAdd ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x)
    rw [hfe (specialLinearGroupEquivStatedSL 4 (ZMod 2) g) ⟨u, hu⟩ (hHU (σ g) u hu)]
    rw [hnat g (f ⟨u, hu⟩)]
  have hfixiff : ∀ g : SpecialLinearGroup (Fin 4) (ZMod 2),
      (φ g : MulAut W) u = u ↔ g ∈ stabV x := by
    intro g
    constructor
    · intro hfix
      rw [mem_stabV]
      have h2 : f ⟨u, hu⟩ = Multiplicative.ofAdd
          ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) := by
        rw [← hstep g]
        exact congrArg f (Subtype.ext hfix.symm)
      have h3 : x = (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x :=
        congrArg Multiplicative.toAdd h2
      exact h3.symm
    · intro hg
      have hgx : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x := mem_stabV.1 hg
      have h2 : f ⟨(φ g : MulAut W) u, hHU (σ g) u hu⟩ = f ⟨u, hu⟩ := by
        rw [hstep g, hgx, hxdef, ofAdd_toAdd]
      exact congrArg Subtype.val (hfi h2)
  have hmap : (stabV x).map φ = H ⊓ MulAction.stabilizer (MulAut W) u := by
    ext h
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.2 ⟨(σ g).2, ?_⟩
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact (hfixiff g).2 hg
    · intro hh
      obtain ⟨hhH, hhfix⟩ := Subgroup.mem_inf.1 hh
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hhfix
      obtain ⟨γ, hγ⟩ := hπs ⟨h, hhH⟩
      have hφg : φ ((specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm γ) = h := by
        rw [hφapply, MulEquiv.apply_symm_apply]
        exact congrArg Subtype.val hγ
      exact ⟨_, (hfixiff _).1 (by rw [hφg]; exact hhfix), hφg⟩
  have hrange : φ.range = H := by
    have h1 : φ.range = σ.range.map H.subtype := by
      rw [show φ = H.subtype.comp σ from rfl, MonoidHom.range_comp]
    rw [h1, σ.range_eq_top_of_surjective hσs, Subgroup.map_top, Subgroup.range_subtype]
  let e : ↥(stabV x) ≃* ↥(H ⊓ MulAction.stabilizer (MulAut W) u) :=
    (Subgroup.equivMapOfInjective (stabV x) φ hφ).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro J hJ hJH
    let J' : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) := J.comap φ
    have hle : stabV x ≤ J' := by
      intro g hg
      refine hJ (Subgroup.mem_inf.2 ⟨(σ g).2, ?_⟩)
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact (hfixiff g).2 hg
    have hJr : J = J'.map φ :=
      (Subgroup.map_comap_eq_self (f := φ) (H := J) (by rw [hrange]; exact hJH)).symm
    rcases close16_sl4_stab_maximal hx hle with hJ' | hJ'
    · left
      calc J = J'.map φ := hJr
        _ = (stabV x).map φ := by rw [hJ']
        _ = H ⊓ MulAction.stabilizer (MulAut W) u := hmap
    · right
      calc J = J'.map φ := hJr
        _ = (⊤ : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))).map φ := by rw [hJ']
        _ = φ.range := Subgroup.map_top φ
        _ = H := hrange
  · rw [← Nat.card_congr e.toEquiv]
    exact card_stabV_four hx
  · rw [← hmap]
    change CFSG.RankThree.PartOne.pElementSubgroup 3 ((stabV x).map φ) = (stabV x).map φ
    rw [← s13_pElementSubgroup_map Nat.prime_three φ (stabV x)]
    rw [show CFSG.RankThree.PartOne.pElementSubgroup 3 (stabV x) = stabV x
      from close16_sl4_stab_opp hx]
  · obtain ⟨f₁, hsurj, hpgrp, hcard⟩ := close16_sl4_stab_quot hx
    have hker : (f₁.comp e.symm.toMonoidHom).ker = f₁.ker.map e.toMonoidHom := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_map]
      constructor
      · intro hy
        exact ⟨e.symm y, by simpa using hy, e.apply_symm_apply y⟩
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
    refine ⟨f₁.comp e.symm.toMonoidHom, hsurj.comp e.symm.surjective, ?_, ?_⟩
    · rw [hker]
      exact hpgrp.of_equiv (Subgroup.equivMapOfInjective f₁.ker e.toMonoidHom e.injective)
    · rw [hker, ← Nat.card_congr
        (Subgroup.equivMapOfInjective f₁.ker e.toMonoidHom e.injective).toEquiv, hcard]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

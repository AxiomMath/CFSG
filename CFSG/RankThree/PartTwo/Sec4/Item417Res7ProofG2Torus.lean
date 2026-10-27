module

public import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley

namespace Res417Seven

variable {k : Type} [Field k]

theorem g2_eq_one_of_mem_rootCharStabilizer_three
    {ζ : kˣ} (hζ : orderOf ζ = 3) {w : WeylGroup .G2}
    (hw : ∀ i, w ∈ rootCharStabilizer (Pi.mulSingle i ζ)) : w = 1 := by
  have hmod : ∀ (i : Fin Tag.G2.rank) (v : Fin Tag.G2.rank → ℤ), (w • v) i ≡ v i [ZMOD 3] := by
    intro i v
    have h0 : rootChar (Pi.mulSingle i ζ) (w • v) = rootChar (Pi.mulSingle i ζ) v := hw i v
    rw [rootChar_mulSingle_eq_zpow, rootChar_mulSingle_eq_zpow, zpow_eq_zpow_iff_modEq,
      hζ] at h0
    exact_mod_cast h0
  have k1 := hmod g2ia g2a
  have k2 := hmod g2ir g2a
  have k3 := hmod g2ia g2r
  have k4 := hmod g2ir g2r
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact weyl_G2_ext (by rw [h1, one_smul]) (by rw [h2, one_smul])
  all_goals
    exfalso
    rw [h1] at k1 k2
    rw [h2] at k3 k4
    revert k1 k2 k3 k4
    decide

theorem g2_eq_g2r_of_mem_rootCharKernel_three {ζ : kˣ}
    (hζ : orderOf ζ = 3) {α : Fin Tag.G2.rank → ℤ}
    (hα : α ∈ rootCharKernel (Pi.mulSingle g2ia ζ) ∩ {β | IsRoot .G2 β ∧ 0 < height β}) :
    α = g2r := by
  obtain ⟨⟨hroot, hchar⟩, -, hpos⟩ := hα
  rw [rootChar_mulSingle_eq_zpow, ← orderOf_dvd_iff_zpow_eq_one, hζ] at hchar
  rcases G2_root_eq_or_natAbs_ia_le hroot with rfl | rfl | ⟨h0, h2⟩
  · rfl
  · exact absurd hpos (by decide)
  · exact absurd hchar (not_dvd_of_natAbs_lt h0 (by omega))

section Bruhat


theorem g2_adjointGroup_inf_centralizer_torusTorsion_three [Finite k]
    (hpq : 3 ∣ Nat.card k - 1) :
    adjointGroup .G2 k ⊓ Subgroup.centralizer (torusTorsion k 3 : Set (ModGL .G2 k)) =
      torusGroup .G2 k := by
  have hTcomm := (triangular_borel_structure.{0, 0} .G2 k).1
  refine le_antisymm (fun z hz => ?_) (le_inf torusGroup_le_adjointGroup_G2 fun h hh =>
    Subgroup.mem_centralizer_iff.2 fun x hx => hTcomm _ (torusTorsion_le_torusGroup 3 hx) _ hh)
  obtain ⟨hzC, hzV⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one Nat.prime_three hpq
  have hX : ∀ i, z ∈ toralCentralizer .G2 k (Pi.mulSingle i ζ) := fun i =>
    mem_toralCentralizer.2 ⟨hzC, by
      rw [Subgroup.mem_centralizer_iff.1 hzV _ (rootDiagUnit_mulSingle_mem_torusTorsion hζ i),
        mul_inv_cancel_right]⟩
  have hB := Chevalley_toral_centralizer_Bruhat_factors .G2 k (Pi.mulSingle g2ia ζ)
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hz1⟩ := hB.1 z (hX g2ia)
  obtain ⟨w', hw', h', hh', u', hu', v', hv', hz2⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .G2 k (Pi.mulSingle g2ir ζ)).1 z (hX g2ir)
  obtain ⟨hww, -, -, -⟩ := hB.2.1 w w' h h' u u' v v' hh hh'
    (rootSpan_le_posUnipotent (fun α hα => hα.2) hu)
    (rootSpan_le_posUnipotent (fun α hα => hα.2) hu')
    (rootSpan_mono Set.inter_subset_right hv) (rootSpan_mono Set.inter_subset_right hv')
    (hz1.symm.trans hz2)
  rw [← hww] at hw'
  have hw1 : w = 1 := g2_eq_one_of_mem_rootCharStabilizer_three hζ fun i => by
    rcases fin_G2_cases i with rfl | rfl
    · exact hw
    · exact hw'
  subst hw1
  have hbot : rootSpan .G2 k (∅ : Set (Fin Tag.G2.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rw [inversionSet_one, Set.inter_empty, hbot, Subgroup.mem_bot] at hv
  subst hv
  have hS : rootCharKernel (Pi.mulSingle g2ia ζ) ∩ {β | IsRoot .G2 β ∧ 0 < height β} ⊆ {g2r} :=
    fun α hα => g2_eq_g2r_of_mem_rootCharKernel_three hζ hα
  have hur : u ∈ rootSubgroup .G2 k g2r := by
    have := rootSpan_mono hS hu
    rwa [rootSpan_singleton] at this
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hur
  rw [canonicalRep_one, mul_one, mul_one] at hz1
  have hfix := (mem_toralCentralizer.1 (hX g2ir)).2
  have e1 := conj_rootDiagUnit_of_mem_torusGroup (Pi.mulSingle g2ir ζ) hh
  have e2 := rootDiagUnit_conj_pinnedX (Pi.mulSingle g2ir ζ) isRoot_g2r c
  rw [rootChar_mulSingle_eq_zpow, g2r_ir, zpow_one] at e2
  have e3 : rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) * (h * pinnedX .G2 k g2r c) *
      (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ))⁻¹ = h * pinnedX .G2 k g2r ((ζ : k) * c) := by
    calc _ = (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) * h *
          (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ))⁻¹) *
          (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) * pinnedX .G2 k g2r c *
            (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ))⁻¹) := by group
      _ = _ := by rw [e1, e2]
  rw [hz1, e3] at hfix
  have hc := pinnedX_injective .G2 k g2r (mul_left_cancel hfix)
  have hζ1 : (ζ : k) ≠ 1 := fun h1 => by
    rw [show ζ = 1 from Units.ext h1, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  have hc0 : c = 0 := by
    have : ((ζ : k) - 1) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hζ1)
  rw [hz1, hc0, pinnedX_zero, mul_one]
  exact hh

theorem g2_exists_eq_mul_canonicalRep_of_mem_normalizer_three [Finite k]
    (hpq : 3 ∣ Nat.card k - 1) {g : ModGL .G2 k}
    (hg : g ∈ adjointGroup .G2 k ⊓ Subgroup.normalizer (torusTorsion k 3 : Set (ModGL .G2 k))) :
    ∃ h ∈ torusGroup .G2 k, ∃ w : WeylGroup .G2, g = h * canonicalRep (coxeterSystem .G2) k w := by
  obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
  have hTB := triangular_borel_structure.{0, 0} .G2 k
  have hB := Chevalley_toral_centralizer_Bruhat_factors .G2 k 1
  have hg1 : g ∈ toralCentralizer .G2 k 1 :=
    mem_toralCentralizer.2 ⟨hgC, by rw [rootDiagUnit_one, one_mul, inv_one, mul_one]⟩
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgeq⟩ := hB.1 g hg1
  have huU : u ∈ posUnipotent .G2 k := rootSpan_le_posUnipotent (fun α hα => hα.2) hu
  have hvI : v ∈ rootSpan .G2 k (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hnN := canonicalRep_mem_normalizer (R := k) w
  have hnC := canonicalRep_mem_adjointGroup (coxeterSystem .G2) k w
  set n := canonicalRep (coxeterSystem .G2) k w with hn
  have key : ∀ x ∈ torusTorsion k 3, g * x * g⁻¹ = n * x * n⁻¹ := by
    intro x hx
    have hxT := torusTorsion_le_torusGroup 3 hx
    have hyT := torusTorsion_le_torusGroup 3 ((Subgroup.mem_normalizer_iff.1 hgN x).1 hx)
    have htT : n * x * n⁻¹ ∈ torusGroup .G2 k := (Subgroup.mem_normalizer_iff.1 hnN x).1 hxT
    have hu' : (n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)⁻¹⁻¹ ∈ posUnipotent .G2 k :=
      (Subgroup.mem_normalizer_iff.1 (hTB.2.2.1 (inv_mem htT)) u).1 huU
    have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ rootSpan .G2 k (inversionSet w) := by
      have hmap := map_rootSpan_of_forall (S := inversionSet w)
        (f := (MulAut.conj x⁻¹).toMonoidHom) fun α hα =>
          map_conj_rootSubgroup_of_mem_torusGroup (inv_mem hxT) hα.1
      rw [← hmap]
      exact ⟨v, hvI, rfl⟩
    have heq : h * (n * x * n⁻¹) * ((n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)⁻¹⁻¹) * n *
        (x⁻¹ * v * x⁻¹⁻¹) = g * x * g⁻¹ * h * u * n * v := by
      rw [hgeq]
      group
    obtain ⟨-, h1, -⟩ := hB.2.1 w w _ _ _ _ _ _ (mul_mem hh htT) (mul_mem hyT hh) hu' huU hv' hvI
      heq
    exact (mul_left_cancel (h1.trans (hTB.1 _ hyT _ hh))).symm
  have hm : n⁻¹ * g ∈
      adjointGroup .G2 k ⊓ Subgroup.centralizer (torusTorsion k 3 : Set (ModGL .G2 k)) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hnC) hgC,
      Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    calc x * (n⁻¹ * g) = n⁻¹ * (n * x * n⁻¹) * g := by group
      _ = n⁻¹ * (g * x * g⁻¹) * g := by rw [key x hx]
      _ = n⁻¹ * g * x := by group
  rw [g2_adjointGroup_inf_centralizer_torusTorsion_three hpq] at hm
  exact ⟨n * (n⁻¹ * g) * n⁻¹, (Subgroup.mem_normalizer_iff.1 hnN _).1 hm, w, by rw [← hn]; group⟩

end Bruhat

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4

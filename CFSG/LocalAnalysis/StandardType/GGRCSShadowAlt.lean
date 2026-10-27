module

public import CFSG.LocalAnalysis.StandardType.GGRCSShadowBasic
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltCoreTwo
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionFlatFamilies
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltFamily
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionBridge
public import CFSG.LocalAnalysis.ComponentInitial.KnownFourGroupDiagonalPump

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open Equiv Equiv.Perm
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

private theorem ggShA_pullback_component
    {W : Type} [Group W] [Finite W] {n : ℕ} {H : Subgroup W}
    (e : ↥(CFSG.generalizedFitting W) ≃* ↥(alternatingGroup (Fin n)))
    (φ : ↥(H ⊓ CFSG.generalizedFitting W) ≃* ↥(ggAltImage e H))
    (hrow : ∀ C : Subgroup W,
      CFSG.Assembly.IsComponentOf C (H ⊓ CFSG.generalizedFitting W) →
      Nonempty (↥C ⧸ Subgroup.center ↥C ≃* alternatingGroup (Fin 5)))
    {C' : Subgroup (Perm (Fin n))}
    (hC' : CFSG.Assembly.IsComponentOf C' (ggAltImage e H)) :
    ∃ C : Subgroup ↥(H ⊓ CFSG.generalizedFitting W),
      C = (((C'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom).map
            (H ⊓ CFSG.generalizedFitting W).subtype).subgroupOf
            (H ⊓ CFSG.generalizedFitting W) ∧
      CFSG.Open.IsComponentOf C ⊤ ∧
      Nat.card (↥C ⧸ Subgroup.center ↥C) = 60 := by
  have hC'' : CFSG.Assembly.IsComponentOf (C'.subgroupOf (ggAltImage e H)) ⊤ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (ggAltImage e H).subtype_injective]
    have hmap : (C'.subgroupOf (ggAltImage e H)).map (ggAltImage e H).subtype = C' :=
      Subgroup.map_subgroupOf_eq_of_le hC'.1
    have htop : (⊤ : Subgroup ↥(ggAltImage e H)).map (ggAltImage e H).subtype =
        ggAltImage e H := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmap, htop]
    exact hC'
  have hD : CFSG.Assembly.IsComponentOf
      ((C'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom) ⊤ := by
    have h := ggIsComponentOf_map φ.symm.toMonoidHom hC''
      (ggNotLe_ker_of_injective φ.symm.injective (ggComponent_ne_bot hC''))
    rw [Subgroup.map_top_of_surjective φ.symm.toMonoidHom φ.symm.surjective] at h
    exact h
  set CW : Subgroup W := ((C'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom).map
    (H ⊓ CFSG.generalizedFitting W).subtype with hCWdef
  have hCW : CFSG.Assembly.IsComponentOf CW (H ⊓ CFSG.generalizedFitting W) := by
    rw [hCWdef]
    exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_subtype_top hD
  obtain ⟨e5⟩ := hrow CW hCW
  have hcardW : Nat.card (↥CW ⧸ Subgroup.center ↥CW) = 60 := by
    rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup]
    norm_num
  obtain ⟨hopen, hcard⟩ := ggShadow_open_of_isComponentOf hCW
  exact ⟨CW.subgroupOf (H ⊓ CFSG.generalizedFitting W), by rw [hCWdef], hopen,
    by rw [hcard]; exact hcardW⟩

private theorem ggShA_pullback_injective
    {W : Type} [Group W] {n : ℕ} {H : Subgroup W}
    (e : ↥(CFSG.generalizedFitting W) ≃* ↥(alternatingGroup (Fin n)))
    (φ : ↥(H ⊓ CFSG.generalizedFitting W) ≃* ↥(ggAltImage e H))
    {C₁' C₂' : Subgroup (Perm (Fin n))}
    (h₁ : C₁' ≤ ggAltImage e H) (h₂ : C₂' ≤ ggAltImage e H)
    (h : (((C₁'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom).map
          (H ⊓ CFSG.generalizedFitting W).subtype).subgroupOf
          (H ⊓ CFSG.generalizedFitting W) =
         (((C₂'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom).map
          (H ⊓ CFSG.generalizedFitting W).subtype).subgroupOf
          (H ⊓ CFSG.generalizedFitting W)) :
    C₁' = C₂' := by
  have h1 : ((C₁'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom).map
      (H ⊓ CFSG.generalizedFitting W).subtype =
      ((C₂'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom).map
      (H ⊓ CFSG.generalizedFitting W).subtype := by
    have h' := congrArg (Subgroup.map (H ⊓ CFSG.generalizedFitting W).subtype) h
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le
          ((C₁'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom)),
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le
          ((C₂'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom))] at h'
    exact h'
  have h2 : (C₁'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom =
      (C₂'.subgroupOf (ggAltImage e H)).map φ.symm.toMonoidHom :=
    Subgroup.map_injective (H ⊓ CFSG.generalizedFitting W).subtype_injective h1
  have h3 : C₁'.subgroupOf (ggAltImage e H) = C₂'.subgroupOf (ggAltImage e H) :=
    Subgroup.map_injective φ.symm.injective h2
  have h' := congrArg (Subgroup.map (ggAltImage e H).subtype) h3
  rw [Subgroup.map_subgroupOf_eq_of_le h₁, Subgroup.map_subgroupOf_eq_of_le h₂] at h'
  exact h'

theorem ggShadow_alt_two_components {W : Type} [Group W] [Finite W] {p : ℕ}
    {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat p H E)
    (hKH : ¬ CFSG.generalizedFitting W ≤ H) (hp : p = 5) {s : ℕ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4)
    (he : Nonempty (↥(CFSG.generalizedFitting W) ≃* alternatingGroup (Fin (5 * s))))
    (hrow : ∀ C : Subgroup W, CFSG.Assembly.IsComponentOf C (H ⊓ CFSG.generalizedFitting W) →
      Nonempty (↥C ⧸ Subgroup.center ↥C ≃* alternatingGroup (Fin 5))) :
    ∃ C₁ C₂ : Subgroup ↥(H ⊓ CFSG.generalizedFitting W), C₁ ≠ C₂ ∧
      CFSG.Open.IsComponentOf C₁ ⊤ ∧ CFSG.Open.IsComponentOf C₂ ⊤ ∧
      Nat.card (↥C₁ ⧸ Subgroup.center ↥C₁) = 60 ∧
      Nat.card (↥C₂ ⧸ Subgroup.center ↥C₂) = 60 := by
  obtain ⟨⟨hp', hp2, hE, hEcard, hfus⟩, ⟨hsimple, hnab, -⟩, -, -⟩ := hyp
  obtain ⟨e⟩ := he
  haveI : Fact p.Prime := ⟨hp'⟩
  have hout : ¬ p ∣ Nat.card (Outer ↥(CFSG.generalizedFitting W)) := by
    rw [ggCard_outer_congr e]
    exact ggNot_dvd_outer_alternating hp' hp2 (by omega)
  have hEK : E ≤ CFSG.generalizedFitting W := fun x hx =>
    ggMem_generalizedFitting_of_pow hp' hsimple hnab hout (hE.2 x hx)
  have hEH : E ≤ H := hfus.1
  have hMtop : ¬ alternatingGroup (Fin (5 * s)) ≤ ggAltImage e H := by
    intro hle
    apply hKH
    intro k hk
    have h1 := hle (e ⟨k, hk⟩).2
    exact (ggMem_altImage e).mp h1
  have hEM : ggAltImage e E ≤ ggAltImage e H :=
    Subgroup.map_mono (Subgroup.map_mono (Subgroup.comap_mono hEH))
  have hEab' : ∀ x ∈ ggAltImage e E, ∀ y ∈ ggAltImage e E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := (ggMem_altImage_iff e).mp hx
    obtain ⟨k', hk', rfl⟩ := (ggMem_altImage_iff e).mp hy
    have hc0 := hE.1.is_comm.comm (⟨k, hk⟩ : ↥E) ⟨k', hk'⟩
    have hc : k * k' = k' * k := Subtype.ext (by simpa using congrArg Subtype.val hc0)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]
  have hEp' : ∀ x ∈ ggAltImage e E, x ^ p = 1 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (ggMem_altImage_iff e).mp hx
    have hkp : k ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 _ hk)
    rw [← Subgroup.coe_pow, ← map_pow, hkp, map_one, Subgroup.coe_one]
  have hEcard' : Nat.card (ggAltImage e E) = p ^ 2 := by
    rw [← hEcard]
    exact (Nat.card_congr (ggAltImageEquiv e hEK).toEquiv).symm
  have hctl : ∀ g ∈ alternatingGroup (Fin (5 * s)), ∀ x ∈ ggAltImage e E, x ≠ 1 →
      g⁻¹ * x * g ∈ ggAltImage e H → g ∈ ggAltImage e H := by
    intro g hg x hx hx1 hgx
    obtain ⟨y, hyE, rfl⟩ := (ggMem_altImage_iff e).mp hx
    set k := e.symm ⟨g, hg⟩ with hkdef
    have hgk : ((e k : ↥(alternatingGroup (Fin (5 * s)))) : Perm (Fin (5 * s))) = g := by
      simp [hkdef]
    have hy1 : (y : W) ≠ 1 := by
      intro h
      apply hx1
      have : y = 1 := Subtype.ext h
      rw [this, map_one, Subgroup.coe_one]
    rw [← hgk] at hgx ⊢
    have h1 : ((e (k⁻¹ * y * k) : ↥(alternatingGroup (Fin (5 * s)))) :
        Perm (Fin (5 * s))) ∈ ggAltImage e H := by
      simpa [map_mul, map_inv] using hgx
    have h2 := (ggMem_altImage e).mp h1
    have h3 : (k : W)⁻¹ * (y : W) * (k : W) ∈ H := by simpa using h2
    exact (ggMem_altImage e).mpr ((ggControlsStrongFusion_iff.mp hfus).2 _ hyE hy1 _ h3)
  have hcore := ggAltCoreTwo (V := Fin (5 * s)) hp2 hMtop hEM hEab' hEp' hEcard' hctl
  rcases hcore with ⟨h3, -⟩ | hfive | hthird
  · exfalso
    omega
  ·
    obtain ⟨-, C₁', C₂', hne, hC₁', hC₂', -, -⟩ := hfive
    have hAlt : ggAltImage e (H ⊓ CFSG.generalizedFitting W) = ggAltImage e H := by
      unfold ggAltImage
      rw [Subgroup.inf_subgroupOf_right]
    let φ : ↥(H ⊓ CFSG.generalizedFitting W) ≃* ↥(ggAltImage e H) :=
      (ggAltImageEquiv e inf_le_right).trans (MulEquiv.subgroupCongr hAlt)
    obtain ⟨C₁, hC₁eq, hopen₁, hcard₁⟩ := ggShA_pullback_component e φ hrow hC₁'
    obtain ⟨C₂, hC₂eq, hopen₂, hcard₂⟩ := ggShA_pullback_component e φ hrow hC₂'
    refine ⟨C₁, C₂, ?_, hopen₁, hopen₂, hcard₁, hcard₂⟩
    intro h
    apply hne
    refine ggShA_pullback_injective e φ hC₁'.1 hC₂'.1 ?_
    rw [← hC₁eq, ← hC₂eq]
    exact h
  ·
    obtain ⟨C', hC', m, hm7, hm8, ⟨eC⟩⟩ := hthird
    obtain ⟨L, hLc, ⟨eL⟩⟩ := ggExists_isComponentOf_of_altImage e hC'
    have eLm : ↥L ≃* ↥(alternatingGroup (Fin m)) := eL.trans eC
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin m)) :=
      alternatingGroup.isSimpleGroup (α := Fin m) (by simp only [Nat.card_fin]; omega)
    have hnc : ¬ IsMulCommutative ↥(alternatingGroup (Fin m)) := by
      rw [alternatingGroup.isMulCommutative_iff_card_le_three]
      simp only [Nat.card_fin]
      omega
    have hnabAm : ∃ a b : ↥(alternatingGroup (Fin m)), a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact hnc ⟨⟨h⟩⟩
    have hLsimp : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr eLm).mpr inferInstance
    have hnabL : ∃ a b : ↥L, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnabAm
      exact ⟨eLm.symm a, eLm.symm b, fun h => hab (by simpa using congrArg eLm h)⟩
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hZ : Subgroup.center ↥L = ⊥ := ggCenter_eq_bot_of_simple hnabL
    have hcardL : Nat.card (↥L ⧸ Subgroup.center ↥L) = Nat.card ↥L :=
      Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
        QuotientGroup.quotientBot).toEquiv
    have hcardAm : Nat.card ↥L = Nat.factorial m / 2 := by
      rw [Nat.card_congr eLm.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    obtain ⟨e5⟩ := hrow L hLc
    have hrowCard : Nat.card (↥L ⧸ Subgroup.center ↥L) = 60 := by
      rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hm2 : Nat.factorial m / 2 = 60 := by
      rw [← hcardAm, ← hcardL]
      exact hrowCard
    have h7 : Nat.factorial 7 ≤ Nat.factorial m := Nat.factorial_le hm7
    have hdiv : Nat.factorial 7 / 2 ≤ Nat.factorial m / 2 := Nat.div_le_div_right h7
    have h7eval : Nat.factorial 7 / 2 = 2520 := by norm_num
    omega

end CFSG.StandardType

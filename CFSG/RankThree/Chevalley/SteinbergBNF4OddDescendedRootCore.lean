module

public import CFSG.RankThree.Chevalley.SteinbergBXOddF4A2PointwiseInner
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4DescendedRootCore

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial
open Subgroup

section Generic

variable {C : Type*} [Group C]

theorem aschbacherSolvableCore_le_map_of_fixes
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {p : ℕ}
    {B : Subgroup (MulAut C)} (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (x : C)
    (R R₀ : Subgroup C)
    (hinner : ∀ η : MulAut C, (∀ r ∈ R₀, η r = r) → η ∈ (MulAut.conj : C →* MulAut C).range)
    (hfixR : ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)),
      ∀ r ∈ R, (s : MulAut C) r = r)
    (hfixR₀ : ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)),
      ∀ r ∈ R₀, (s : MulAut C) r = r) :
    inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)) ≤
      (centralizer ({x} : Set C) ⊓ centralizer (R : Set C)).map
        ((MulAut.conj : C →* MulAut C).codRestrict B fun c => hB ⟨c, rfl⟩) := by
  intro s hs
  obtain ⟨c, hc⟩ := hinner (s : MulAut C) (hfixR₀ s hs)
  have hsM : s ∈ centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B) :=
    Subgroup.map_subtype_le _ hs
  refine ⟨c, Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hinj ?_),
    Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩, Subtype.ext hc⟩
  · have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hsM)
    simp only [Subgroup.coe_mul] at h1
    rw [map_mul, map_mul, hc]
    exact h1
  · have h1 := hfixR s hs r hr
    rw [← hc, MulAut.conj_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm

end Generic


theorem odd_F4_descended_root_layer_local_core_contained_in_derived_centralizer
    {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (x : adjointGroup .F4 K)
    (hRL : layer (⁅centralizer ({x} : Set (adjointGroup .F4 K)),
      centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) = ⊤)
    (R₀ : Subgroup (adjointGroup .F4 K))
    (hR₀ : R₀ ≤ ⁅centralizer ({x} : Set (adjointGroup .F4 K)),
      centralizer ({x} : Set (adjointGroup .F4 K))⁆)
    (M : Type) [Field M] (ι : K →+* M) (κ : F4A2Kind) (g : ModGL .F4 M) (P₀ : GL (Fin 2) M)
    (hRg : (R₀.map ((baseChangeGL ι).comp (adjointGroup .F4 K).subtype)).map
        (MulAut.conj g).toMonoidHom =
      ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL P₀)).map
        ((subsystemGroup Tag.F4 M {κ.i, κ.j}).subtype.comp (f4A2Iota M κ))) :
    inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)) ≤
      (centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
        centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
          centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
            Set (adjointGroup .F4 K))).map
        ((MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).codRestrict B
          fun c => hB ⟨c, rfl⟩) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hfixR := aschbacherSolvableCore_fixes_of_layer_eq_top hinj hp hB x
    (derived_centralizer_le x) (fun η hη r hr => apply_mem_derived_centralizer hη hr) hRL
  exact aschbacherSolvableCore_le_map_of_fixes hinj hB x _ R₀
    (odd_F4_descended_A2_root_SL2_pointwise_automorphisms_inner hℓ hℓ2 hf K hK M ι κ R₀ g P₀
      hRg).1 hfixR fun s hs r hr => hfixR s hs r (hR₀ hr)

theorem odd_F4_descended_root_layer_centralizer_local_core_odd
    {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (x : adjointGroup .F4 K)
    (hRL : layer (⁅centralizer ({x} : Set (adjointGroup .F4 K)),
      centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) = ⊤)
    (hodd : Odd (Nat.card (centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
      centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
        centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
          Set (adjointGroup .F4 K)) : Subgroup (adjointGroup .F4 K))))
    (R₀ : Subgroup (adjointGroup .F4 K))
    (hR₀ : R₀ ≤ ⁅centralizer ({x} : Set (adjointGroup .F4 K)),
      centralizer ({x} : Set (adjointGroup .F4 K))⁆)
    (M : Type) [Field M] (ι : K →+* M) (κ : F4A2Kind) (g : ModGL .F4 M) (P : GL (Fin 2) M)
    (hRg : (R₀.map ((baseChangeGL ι).comp (adjointGroup .F4 K).subtype)).map
        (MulAut.conj g).toMonoidHom =
      ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL P)).map
        ((subsystemGroup Tag.F4 M {κ.i, κ.j}).subtype.comp (f4A2Iota M κ))) :
    Odd (Nat.card (inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)))) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hle := odd_F4_descended_root_layer_local_core_contained_in_derived_centralizer hℓ hℓ2 hf
    K hK hp B hB x hRL R₀ hR₀ M ι κ g P hRg
  have h := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (f := (MulAut.conj : adjointGroup .F4 K →*
    MulAut (adjointGroup .F4 K)).codRestrict B fun c => hB ⟨c, rfl⟩)
    (fun c d h => hinj (congrArg Subtype.val h))] at h
  exact hodd.of_dvd_nat h

end CFSG.RankThree.Chevalley

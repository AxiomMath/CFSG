module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveCentral
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveLift
public import CFSG.OddTranspositions.PartThree.Twelve.SixPivot
public import CFSG.OddTranspositions.PartThree.Twelve.FiveDefs
public import CFSG.OddTranspositions.PartFour.LinePolar
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveCenter
public import CFSG.OddTranspositions.PartThree.Twelve.Four
public import CFSG.OddTranspositions.PartThree.Nine.ThreeSplit
public import CFSG.OddTranspositions.SevenFourEight.SevenSix
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveStab
import CFSG.Mathlib.GroupTheory.ClosureProdEqOne

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open scoped Function

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def IsFiveMarking (hC : HypothesisC D) (k : ℕ) (ε π : Bool)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      fiveProjective k ε π) : Prop :=
  ∀ x, x ∈ imageClass hC ↔ ∃ r : fiveReflectionGroup k ε π,
    (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
      (QuotientGroup.mk r : fiveProjective k ε π) = φ x

theorem fiveReflection_neg_one_notMem_of_notMem_d (hC : HypothesisC D)
    {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      fiveProjective k ε π} (hφ : IsFiveMarking hC k ε π φ)
    (hdH : hC.d ∉ Halpha D hC.alpha)
    (hinj : Function.Injective (fun x =>
      φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x)))
    (hcomm : DalphaStar D hC.alpha = commSet D hC.d) :
    (-1 : GL (Fin (k + 1)) (ZMod 5)) ∉ fiveReflectionGroup k ε π := by
  classical
  intro hneg
  obtain ⟨r, hrD, hrcomm, hrinj, hrprod⟩ := exists_frame_of_neg_one_mem hk hneg
  let ri : Fin (k + 1) → fiveReflectionGroup k ε π :=
    fun i => ⟨r i, Subgroup.subset_closure (hrD i)⟩
  have hri_inj : Function.Injective ri := fun i j hij => hrinj (Subtype.ext_iff.mp hij)
  have hlift : ∀ i, ∃ h : Halpha D hC.alpha, h ∈ DstarH hC ∧
      φ (QuotientGroup.mk' _ h) = (QuotientGroup.mk (ri i) : fiveProjective k ε π) := by
    intro i
    have hx : φ.symm (QuotientGroup.mk (ri i) : fiveProjective k ε π) ∈ imageClass hC := by
      rw [hφ]
      exact ⟨ri i, hrD i, by simp⟩
    obtain ⟨h, hh, hhx⟩ := hx
    exact ⟨h, hh, by rw [hhx, MulEquiv.apply_symm_apply]⟩
  choose h hhD hhphi using hlift
  have hcommH : ∀ i j, Commute (h i) (h j) := by
    intro i j
    have hrij : Commute (ri i) (ri j) := Subtype.ext (hrcomm i j).eq
    have h1 : φ (QuotientGroup.mk' _ (h i * h j)) =
        φ (QuotientGroup.mk' _ (h j * h i)) := by
      have hrij' := congrArg
        (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) hrij
      simp only [map_mul] at hrij' ⊢
      rw [hhphi i, hhphi j]
      exact hrij'
    exact hinj h1
  have hri_prod : (List.ofFn ri).prod = ⟨-1, hneg⟩ := by
    apply Subtype.ext
    change (Subgroup.subtype (fiveReflectionGroup k ε π)) ((List.ofFn ri).prod) = -1
    rw [map_list_prod (Subgroup.subtype (fiveReflectionGroup k ε π)) (List.ofFn ri)]
    have hmap : List.map (Subgroup.subtype (fiveReflectionGroup k ε π)) (List.ofFn ri) =
        List.ofFn r := by
      rw [← List.ofFn_comp']
      rfl
    rw [hmap, hrprod]
  have hh_prod : (List.ofFn h).prod = 1 := by
    apply hinj
    show (φ.toMonoidHom.comp (QuotientGroup.mk' _)) (List.ofFn h).prod =
      (φ.toMonoidHom.comp (QuotientGroup.mk' _)) 1
    rw [map_list_prod, map_one]
    have hmap : List.map (φ.toMonoidHom.comp (QuotientGroup.mk' _)) (List.ofFn h) =
        List.ofFn (fun i => (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))
          (ri i) : fiveProjective k ε π)) := by
      rw [List.map_ofFn]
      exact congrArg List.ofFn (funext fun i => by simpa using hhphi i)
    rw [hmap, List.ofFn_comp',
      ← map_list_prod (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π)))
        (List.ofFn ri), hri_prod]
    exact (QuotientGroup.eq_one_iff _).mpr
      ((mem_center_fiveReflectionGroup_iff hk ε π ⟨-1, hneg⟩).mpr (Or.inr rfl))
  have hf_prod : (List.ofFn (fun i => (h i : G))).prod = 1 := by
    rw [show List.ofFn (fun i => (h i : G)) = List.map (Subgroup.subtype _) (List.ofFn h) from by
      rw [List.ofFn_comp']
      rfl]
    rw [← map_list_prod, hh_prod, map_one]
  have hfinj : Function.Injective (fun i => (h i : G)) := by
    intro i j hij
    have hhh : h i = h j := Subtype.ext hij
    have h1 : (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π)) (ri i) :
        fiveProjective k ε π) =
        (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π)) (ri j) :
          fiveProjective k ε π) := by
      change (QuotientGroup.mk (ri i) : fiveProjective k ε π) =
        (QuotientGroup.mk (ri j) : fiveProjective k ε π)
      rw [← hhphi i, ← hhphi j, hhh]
    have h2 : (ri i)⁻¹ * (ri j) ∈ Subgroup.center (fiveReflectionGroup k ε π) := by
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π)))
        ((ri i)⁻¹ * ri j) = 1
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    rcases (mem_center_fiveReflectionGroup_iff hk ε π ((ri i)⁻¹ * ri j)).mp h2 with h3 | h3
    · have h5 : (ri i)⁻¹ * ri j = 1 := Subtype.ext h3
      have h4 : ri i = ri j := inv_mul_eq_one.mp h5
      exact hrinj (Subtype.ext_iff.mp h4)
    · exfalso
      have h5 : (ri i)⁻¹ * ri j = (⟨-1, hneg⟩ : fiveReflectionGroup k ε π) := Subtype.ext h3
      have h6 : ri j = ri i * (⟨-1, hneg⟩ : fiveReflectionGroup k ε π) := by
        have := congrArg (fun x => ri i * x) h5
        rw [← mul_assoc, mul_inv_cancel, one_mul] at this
        exact this
      have h7 : (ri j : GL (Fin (k + 1)) (ZMod 5)) = -r i := by
        rw [Subtype.ext_iff] at h6
        rw [h6]
        show (ri i : GL (Fin (k + 1)) (ZMod 5)) * (-1 : GL (Fin (k + 1)) (ZMod 5)) = -r i
        rw [mul_neg, mul_one]
      exact (ne_neg_of_mem_fiveReflections (k := k) (by omega) (hrD i) (hrD j)) h7
  have hfcomm : ∀ i j, Commute ((fun i => (h i : G)) i) ((fun i => (h i : G)) j) :=
    fun i j => congrArg Subtype.val (hcommH i j)
  have hFc : ∀ a ∈ Set.range (fun i => (h i : G)), ∀ b ∈ Set.range (fun i => (h i : G)),
      Commute a b := by
    rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
    exact hfcomm i j
  have hf0 : (fun i => (h i : G)) 0 ∈
      Subgroup.closure (Set.range (fun i => (h i : G)) \ {(fun i => (h i : G)) 0}) := by
    have hmem := List.mem_closure_of_prod_eq_one
      (l := List.ofFn (fun i => (h i : G))) (List.nodup_ofFn.mpr hfinj)
      (fun x hx y hy => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
        exact (hfcomm i j).eq)
      hf_prod (List.mem_ofFn.mpr ⟨0, rfl⟩)
    refine Subgroup.closure_mono ?_ hmem
    rintro x ⟨hxmem, hxne⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxmem
    exact ⟨⟨i, rfl⟩, hxne⟩
  exact hdH (by
    have hd := mem_closure_commSet_of_frame hC.setup hC.hd (F := Set.range (fun i => (h i : G)))
      (fun x hx => by
        obtain ⟨i, rfl⟩ := hx
        rw [← hcomm]
        exact (mem_DstarH_iff hC).mp (hhD i))
      hFc (⟨0, rfl⟩) hf0
    rwa [← hcomm] at hd)

section Certs


theorem twelveTen_five_center (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      fiveProjective k ε π} (hφ : IsFiveMarking hC k ε π φ)
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d) :
    (hC.d ∈ Halpha D hC.alpha ↔
        (-1 : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionGroup k ε π) ∧
      ∃ θ : Halpha D hC.alpha ≃* fiveReflectionGroup k ε π,
        (∀ x, (QuotientGroup.mk (θ x) : fiveProjective k ε π) = φ (QuotientGroup.mk x)) ∧
          (∀ x, x ∈ DstarH hC ↔ (θ x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π) ∧
            ∀ hu : hC.d ∈ Halpha D hC.alpha,
              (θ ⟨hC.d, hu⟩ : GL (Fin (k + 1)) (ZMod 5)) = -1 := by
  classical
  have h5 : IsFiveReflectionModel k ε π (imageClass hC) := by
    refine ⟨φ, fun x => ?_⟩
    rw [hφ x]
    exact exists_congr fun r => and_congr_right fun _ => eq_comm
  have hα : hC.alpha = {hC.d} := by
    have hcls := imageClass_isClass hC
    obtain ⟨s, hs⟩ := imageClass_nonempty hC
    obtain ⟨hb1, hne⟩ := subset_rootBlock_and_ne_of_isFiveReflectionModel hcls hk h5 hs
    exact alpha_eq_singleton_of_rootBlock_eq_singleton hC hMZ hs hb1 hne
      (rootBlock_eq_singleton_of_isFiveReflectionModel hcls hk h5 hs)
  have hcomm : DalphaStar D hC.alpha = commSet D hC.d :=
    DalphaStar_eq_commSet_of_alpha_eq hC hα
  have hMZeq : CFSG.solvableRadical (Halpha D hC.alpha) =
      Subgroup.center (Halpha D hC.alpha) :=
    le_antisymm hMZ (center_le_solvableRadical _)
  by_cases hdH : hC.d ∈ Halpha D hC.alpha
  ·
    let u : Halpha D hC.alpha := ⟨hC.d, hdH⟩
    have huZ : u ∈ Subgroup.center (Halpha D hC.alpha) := by
      obtain ⟨haH, hdZ⟩ := mem_center_of_mem_alpha hC hdH hC.d_mem_alpha
      have e : u = ⟨hC.d, haH⟩ := Subtype.ext rfl
      rwa [e]
    obtain ⟨hu2, hu1⟩ := mul_self_eq_one_and_ne_one_of_mem_alpha hC hC.d_mem_alpha hdH
    have hZeq : (Subgroup.center (Halpha D hC.alpha) : Set (Halpha D hC.alpha)) = {1, u} := by
      ext z
      constructor
      · intro hz
        rcases hcen z hz with h1 | hd
        · left; exact Subtype.ext h1
        · right; exact Subtype.ext hd
      · intro hz
        rcases hz with rfl | rfl
        · exact Subgroup.one_mem _
        · exact huZ
    have hcardZ : Nat.card (Subgroup.center (Halpha D hC.alpha)) = 2 := by
      rw [show Nat.card (Subgroup.center (Halpha D hC.alpha)) =
          (Subgroup.center (Halpha D hC.alpha) : Set (Halpha D hC.alpha)).ncard from
        Nat.card_coe_set_eq _]
      rw [hZeq, Set.ncard_pair (Ne.symm hu1)]
    let ζ : Halpha D hC.alpha →* fiveProjective k ε π :=
      φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
    have hζ : Function.Surjective ζ :=
      φ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker_eq : ζ.ker = CFSG.solvableRadical (Halpha D hC.alpha) := by
      ext x
      rw [MonoidHom.mem_ker]
      change φ (QuotientGroup.mk' _ x) = 1 ↔ x ∈ CFSG.solvableRadical (Halpha D hC.alpha)
      rw [← map_one φ, φ.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    have hker : ζ.ker ≤ Subgroup.center (Halpha D hC.alpha) := by
      rw [hker_eq]; exact hMZ
    have hcard : Nat.card ζ.ker = 2 := by
      rw [hker_eq, hMZeq, hcardZ]
    have himage : ζ '' DstarH hC = φ '' imageClass hC := by
      ext x
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨QuotientGroup.mk' _ h, ⟨h, hh, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
        exact ⟨h, hh, rfl⟩
    have hD : ∀ x : fiveProjective k ε π, x ∈ ζ '' DstarH hC ↔
        ∃ r : fiveReflectionGroup k ε π,
          (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
            (QuotientGroup.mk r : fiveProjective k ε π) = x := by
      intro x
      rw [himage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [hφ] at hy
        exact hy
      · rintro ⟨r, hr, hrx⟩
        refine ⟨φ.symm x, ?_, ?_⟩
        · rw [hφ]
          exact ⟨r, hr, by rwa [MulEquiv.apply_symm_apply]⟩
        · simp
    obtain ⟨θ, hθmk, hθD⟩ :=
      centralTwoExtension_fiveReflection hk ε π (Nine.setup_DstarH hC) ζ hζ hker hcard hD
    have hθuZ : θ u ∈ Subgroup.center (fiveReflectionGroup k ε π) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨h, rfl⟩ := θ.surjective r
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.mp huZ h
    have hθu_neg : (θ u : GL (Fin (k + 1)) (ZMod 5)) = -1 := by
      rcases (mem_center_fiveReflectionGroup_iff hk ε π (θ u)).mp hθuZ with h1 | hneg
      · exfalso
        apply hu1
        apply θ.injective
        rw [map_one]
        exact Subtype.ext h1
      · exact hneg
    have hneg : (-1 : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionGroup k ε π := by
      rw [← hθu_neg]
      exact (θ u).2
    refine ⟨Iff.intro (fun _ => hneg) (fun _ => hdH), θ, hθmk, hθD, fun hu => ?_⟩
    have e : (⟨hC.d, hu⟩ : Halpha D hC.alpha) = u := Subtype.ext rfl
    rw [e, hθu_neg]
  ·
    have hZbot : Subgroup.center (Halpha D hC.alpha) = ⊥ := by
      apply le_antisymm
      · intro z hz
        rw [Subgroup.mem_bot]
        rcases hcen z hz with h1 | hd
        · exact Subtype.ext h1
        · exfalso
          apply hdH
          rw [← hd]
          exact z.2
      · exact bot_le
    have hMbot : CFSG.solvableRadical (Halpha D hC.alpha) = ⊥ := by
      rw [hMZeq, hZbot]
    have hinj_mkM : Function.Injective
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hMbot])
    have hinj_zeta : Function.Injective
        (fun x => φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x)) :=
      φ.injective.comp hinj_mkM
    have hnegnot : (-1 : GL (Fin (k + 1)) (ZMod 5)) ∉ fiveReflectionGroup k ε π :=
      fiveReflection_neg_one_notMem_of_notMem_d hC hk hφ hdH hinj_zeta hcomm
    have hcenterbot : Subgroup.center (fiveReflectionGroup k ε π) = ⊥ := by
      apply le_antisymm
      · intro z hz
        rw [Subgroup.mem_bot]
        rcases (mem_center_fiveReflectionGroup_iff hk ε π z).mp hz with h1 | hneg
        · exact Subtype.ext h1
        · exact absurd (hneg ▸ z.2) hnegnot
      · exact bot_le
    have hinj_mkR : Function.Injective
        (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hcenterbot])
    have hsurj_mkR : Function.Surjective
        (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) :=
      QuotientGroup.mk'_surjective _
    let mkM : Halpha D hC.alpha ≃*
        (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
      MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨hinj_mkM, QuotientGroup.mk'_surjective _⟩
    let mkR : fiveReflectionGroup k ε π ≃* fiveProjective k ε π :=
      MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨hinj_mkR, hsurj_mkR⟩
    let θ : Halpha D hC.alpha ≃* fiveReflectionGroup k ε π :=
      (mkM.trans φ).trans mkR.symm
    have hθmk : ∀ x, (QuotientGroup.mk (θ x) : fiveProjective k ε π) =
        φ (QuotientGroup.mk x) := by
      intro x
      change mkR (θ x) = φ (mkM x)
      rw [show θ x = mkR.symm (φ (mkM x)) from rfl, MulEquiv.apply_symm_apply]
    have hθD : ∀ x, x ∈ DstarH hC ↔
        (θ x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
      intro x
      constructor
      · intro hx
        have hy : QuotientGroup.mk' _ x ∈ imageClass hC := ⟨x, hx, rfl⟩
        rw [hφ] at hy
        obtain ⟨r, hr, hrmk⟩ := hy
        have hθx : θ x = r := by
          apply hinj_mkR
          change (QuotientGroup.mk (θ x) : fiveProjective k ε π) =
            (QuotientGroup.mk r : fiveProjective k ε π)
          rw [hθmk x, hrmk]
          rfl
        rw [hθx]
        exact hr
      · intro hx
        have hφx : φ.symm (QuotientGroup.mk (θ x)) ∈ imageClass hC := by
          rw [hφ]
          exact ⟨θ x, hx, by simp⟩
        rw [hθmk x, MulEquiv.symm_apply_apply] at hφx
        obtain ⟨y, hy, hyx⟩ := hφx
        exact (hinj_mkM hyx) ▸ hy
    refine ⟨Iff.intro (fun h => absurd h hdH) (fun h => absurd h hnegnot), θ, hθmk, hθD,
      fun hu => absurd hu hdH⟩

theorem twelveTen_five_stabilizers (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      fiveProjective k ε π} (hφ : IsFiveMarking hC k ε π φ)
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d)
    (hfl : FiveLines D) {w : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (h126 : ∀ c : FiveChart hC (k + 1), ∃ z, IsFiveHyperplane c w z)
    (hnbr : ∃ v ∈ commSet D hC.d ∩ commSet D w, ∀ x ∈ lineMem D hC.d w, x ≠ hC.d →
      ∃ g ∈ hypLineGroup D hC.d v, g * w * g⁻¹ = x) :
    Halpha D hC.alpha ⊓ Subgroup.centralizer {w} = hypLineGroup D hC.d w ∧
      (∀ x ∈ lineMem D hC.d w, x ≠ hC.d →
        ∃ g ∈ Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G),
          g * w * g⁻¹ = x) ∧
        (hypLineGroup D hC.d w).relIndex
          (Halpha D hC.alpha ⊓ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)) =
            (lineMem D hC.d w).ncard - 1 := by
  classical
  have hwd' : ¬ Commute hC.d w := fun h => hwd h.symm
  have hα : hC.alpha = {hC.d} := alpha_eq_singleton_of_markingData hC hMZ hk hφ
  obtain ⟨v, hvS, hvconj⟩ := hnbr
  obtain ⟨hord, hE, hline⟩ :=
    fiveLines_apply hfl hvS.1.1 hC.hd hw hvS.1 hvS.2 hwd'
  obtain ⟨-, θ, -, hθD, -⟩ := twelveTen_five_center hC hMZ hk hφ hcen
  obtain ⟨c, hcb, hact⟩ := exists_fiveChart_of_mulEquiv hC hα θ hθD
  obtain ⟨z, hz⟩ := h126 c
  have hrel :=
    relIndex_hypLineGroup_eq_ncard_sub_one hC hα hk θ hθD c hcb hact hw hwd' hz hE hord
  have htrans : ∀ x ∈ lineMem D hC.d w, x ≠ hC.d →
      ∃ g ∈ Halpha D hC.alpha ⊓
        Subgroup.normalizer (hypLineGroup D hC.d w : Set G), g * w * g⁻¹ = x := by
    intro x hxE hxd
    obtain ⟨hxnc, hxline⟩ := hline x hxE hxd
    obtain ⟨g, hgLv, hgwx⟩ := hvconj x hxE hxd
    exact ⟨g, mem_inf_normalizer_of_mem_hypLineGroup_conj hC hα hw hwd' hxE hxnc hxline hgLv hgwx,
      hgwx⟩
  exact ⟨centralizer_eq_hypLineGroup hC hα hwd' hrel htrans, htrans, hrel⟩

end Certs

end CFSG.OddTranspositions.PartThree
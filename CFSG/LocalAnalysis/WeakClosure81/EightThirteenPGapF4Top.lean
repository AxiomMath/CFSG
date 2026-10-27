module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShapes
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPBar
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapF4TopAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2)

@[expose] def ChoiceOfKTop (M : Type) [Group M] (rk : Prop) : Prop :=
  ∀ S A : Subgroup M, IsSylowIn 2 S (⊤ : Subgroup M) →
    A ≤ S → IsElemAbelian 2 A → Nat.card A = 4 → K1In (⊤ : Subgroup M) A →
    TISIn (⊤ : Subgroup M) A →
    ∃ K : Subgroup M, K ≤ (⊤ : Subgroup M) ∧ A ≤ K ∧ ¬ A ≤ oTwoMod ⊥ K ∧
      HasQuotShape K (oTwoMod ⊥ K : Set M) (fun X _ => IsL2 X 2) ∧ IsSylowIn 2 (S ⊓ K) K ∧
      (K ⊓ ((⊤ : Subgroup M) ⊓ normalizer (S : Set M))).relIndex K = 5 ∧
      (rk → ¬ (∀ a ∈ A, ∀ s ∈ S, a * s = s * a) →
        ∃ P : Subgroup M, IsMaxParabolicMod ⊥ (⊤ : Subgroup M) P ∧ K = oddResMod ⊥ P)

theorem choiceOfKOn_of_top (Sh : ShapePred)
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), Sh L →
      ∃ (M : Type) (_ : Group M) (_ : ↥L ≃* M), ChoiceOfKTop M (RankTwoShape L)) :
    ChoiceOfKOn Sh := by
  intro Y _ _ L S A hL hS hAS hAe hA4 hK1 hTIS
  obtain ⟨M, hMgrp, e, hM⟩ := h Y L hL
  letI : Group M := hMgrp
  let φ : ↥L →* M := e.toMonoidHom
  have hφ : IsBarMap L (⊥ : Subgroup Y) φ :=
    ⟨MulEquiv.surjective e, fun k => by
      show e k = 1 ↔ (k : Y) ∈ (⊥ : Subgroup Y)
      rw [MulEquiv.map_eq_one_iff e, Subgroup.mem_bot, Subtype.ext_iff]
      simp⟩
  have hSL : S ≤ L := hS.le
  have hAL : A ≤ L := hAS.trans hSL
  have hSylSbar : IsSylowIn 2 (barSub L φ S) (⊤ : Subgroup M) := by
    refine ⟨le_top, ?_, ?_⟩
    · have h1 : IsPGroup 2 (S.subgroupOf L) :=
        hS.isPGroup.comap_of_injective L.subtype L.subtype_injective
      exact h1.map φ
    · have hker : φ.ker ≤ S.subgroupOf L := by
        intro k hk
        rw [MonoidHom.mem_ker] at hk
        rw [Subgroup.mem_subgroupOf]
        have hk1 : (k : Y) = 1 := by
          have := (hφ.ker_iff k).mp hk
          rwa [Subgroup.mem_bot] at this
        rw [hk1]
        exact S.one_mem
      rw [Subgroup.relIndex_top_right]
      change ¬ 2 ∣ ((S.subgroupOf L).map φ).index
      rw [Subgroup.index_map_eq (H := S.subgroupOf L) hφ.surjective hker]
      exact hS.not_dvd_relIndex
  have hAbarSbar : barSub L φ A ≤ barSub L φ S := wcgapt_barSub_mono hAS
  have hAbar_e : IsElemAbelian 2 (barSub L φ A) := isElemAbelian_barSub hAe φ
  have hAbar4 : Nat.card (barSub L φ A) = 4 := by
    rw [card_barSub_eq_relIndex_of_isBarMap (K := L) (N := (⊥ : Subgroup Y)) (A := A)
      hAL bot_le hφ, Subgroup.relIndex_bot_left, hA4]
  have hK1bar : K1In (⊤ : Subgroup M) (barSub L φ A) := by
    intro α hα β hβ hβ1
    obtain ⟨α₀, hα₀A, hα₀φ⟩ := mem_barSub.mp hα
    obtain ⟨β₀, hβ₀A, hβ₀φ⟩ := mem_barSub.mp hβ
    have hβ₀1 : (β₀ : Y) ≠ 1 := by
      intro h1
      apply hβ1
      have hβ₀eq : β₀ = 1 := Subtype.ext h1
      rw [← hβ₀φ, hβ₀eq, map_one]
    let s : Set Y := {γ : Y | ∃ x ∈ L ⊓ Subgroup.centralizer ({(β₀ : Y)} : Set Y),
        γ = x * (α₀ : Y) * x⁻¹}
    have hC : IsElemAbelian 2 (Subgroup.closure s) :=
      hK1 (α₀ : Y) hα₀A (β₀ : Y) hβ₀A hβ₀1
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro g hg g' hg'
      obtain ⟨x, hx, rfl⟩ := hg
      obtain ⟨x', hx', rfl⟩ := hg'
      obtain ⟨x₀, hx₀φ⟩ := hφ.surjective x
      obtain ⟨x₀', hx₀'φ⟩ := hφ.surjective x'
      have hxcen : x ∈ Subgroup.centralizer ({β} : Set M) := (Subgroup.mem_inf.mp hx).2
      have hx'cen : x' ∈ Subgroup.centralizer ({β} : Set M) := (Subgroup.mem_inf.mp hx').2
      have hxβ : β * x = x * β :=
        Subgroup.mem_centralizer_iff.mp hxcen β (Set.mem_singleton β)
      have hx'β : β * x' = x' * β :=
        Subgroup.mem_centralizer_iff.mp hx'cen β (Set.mem_singleton β)
      have hx₀β : β₀ * x₀ = x₀ * β₀ := by
        apply e.injective
        change φ (β₀ * x₀) = φ (x₀ * β₀)
        rw [map_mul, map_mul, hx₀φ, hβ₀φ]
        exact hxβ
      have hx₀'β : β₀ * x₀' = x₀' * β₀ := by
        apply e.injective
        change φ (β₀ * x₀') = φ (x₀' * β₀)
        rw [map_mul, map_mul, hx₀'φ, hβ₀φ]
        exact hx'β
      have hx₀cen : (x₀ : Y) ∈ L ⊓ Subgroup.centralizer ({(β₀ : Y)} : Set Y) :=
        Subgroup.mem_inf.mpr ⟨x₀.2, by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact congrArg Subtype.val hx₀β⟩
      have hx₀'cen : (x₀' : Y) ∈ L ⊓ Subgroup.centralizer ({(β₀ : Y)} : Set Y) :=
        Subgroup.mem_inf.mpr ⟨x₀'.2, by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact congrArg Subtype.val hx₀'β⟩
      have hg₀C : (x₀ : Y) * (α₀ : Y) * (x₀ : Y)⁻¹ ∈ Subgroup.closure s :=
        Subgroup.subset_closure ⟨(x₀ : Y), hx₀cen, rfl⟩
      have hg₀'C : (x₀' : Y) * (α₀ : Y) * (x₀' : Y)⁻¹ ∈ Subgroup.closure s :=
        Subgroup.subset_closure ⟨(x₀' : Y), hx₀'cen, rfl⟩
      have hcomm₀ : ((x₀ : Y) * (α₀ : Y) * (x₀ : Y)⁻¹) *
          ((x₀' : Y) * (α₀ : Y) * (x₀' : Y)⁻¹) =
          ((x₀' : Y) * (α₀ : Y) * (x₀' : Y)⁻¹) *
            ((x₀ : Y) * (α₀ : Y) * (x₀ : Y)⁻¹) := hC.comm hg₀C hg₀'C
      have hg_eq : x * α * x⁻¹ = φ (x₀ * α₀ * x₀⁻¹) := by
        simp only [map_mul, map_inv, hx₀φ, hα₀φ]
      have hg'_eq : x' * α * x'⁻¹ = φ (x₀' * α₀ * x₀'⁻¹) := by
        simp only [map_mul, map_inv, hx₀'φ, hα₀φ]
      rw [hg_eq, hg'_eq, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hcomm₀
    · intro g hg
      obtain ⟨x, hx, rfl⟩ := hg
      obtain ⟨x₀, hx₀φ⟩ := hφ.surjective x
      have hxcen : x ∈ Subgroup.centralizer ({β} : Set M) := (Subgroup.mem_inf.mp hx).2
      have hxβ : β * x = x * β :=
        Subgroup.mem_centralizer_iff.mp hxcen β (Set.mem_singleton β)
      have hx₀β : β₀ * x₀ = x₀ * β₀ := by
        apply e.injective
        change φ (β₀ * x₀) = φ (x₀ * β₀)
        rw [map_mul, map_mul, hx₀φ, hβ₀φ]
        exact hxβ
      have hx₀cen : (x₀ : Y) ∈ L ⊓ Subgroup.centralizer ({(β₀ : Y)} : Set Y) :=
        Subgroup.mem_inf.mpr ⟨x₀.2, by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact congrArg Subtype.val hx₀β⟩
      have hg₀C : (x₀ : Y) * (α₀ : Y) * (x₀ : Y)⁻¹ ∈ Subgroup.closure s :=
        Subgroup.subset_closure ⟨(x₀ : Y), hx₀cen, rfl⟩
      have hsqY : ((x₀ : Y) * (α₀ : Y) * (x₀ : Y)⁻¹) ^ 2 = 1 := hC.2 _ hg₀C
      have hsqL : (x₀ * α₀ * x₀⁻¹) ^ 2 = 1 := Subtype.ext (by simpa using hsqY)
      have hg_eq : x * α * x⁻¹ = φ (x₀ * α₀ * x₀⁻¹) := by
        simp only [map_mul, map_inv, hx₀φ, hα₀φ]
      rw [hg_eq, ← map_pow, hsqL, map_one]
  have hTISbar : TISIn (⊤ : Subgroup M) (barSub L φ A) := by
    intro S₂ hS₂
    let S₃ : Subgroup Y := barPre L φ S₂
    have hS₃ : IsSylowIn 2 S₃ L := by
      refine ⟨barPre_le L φ S₂, ?_, ?_⟩
      · have h1 : IsPGroup 2 (S₂.comap φ) :=
          hS₂.isPGroup.comap_of_injective φ e.injective
        exact h1.map L.subtype
      · have hle : S₃.relIndex L = S₂.relIndex ⊤ := by
          have h2 : S₃.subgroupOf L = S₂.comap φ := by
            change ((S₂.comap φ).map L.subtype).comap L.subtype = S₂.comap φ
            rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
          rw [Subgroup.relIndex_top_right]
          change (S₃.subgroupOf L).index = S₂.index
          rw [h2, Subgroup.index_comap_of_surjective S₂ hφ.surjective]
        rw [hle]
        exact hS₂.not_dvd_relIndex
    rcases hTIS S₃ hS₃ with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hyA, hyS⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨k, hkA, hkφ⟩ := mem_barSub.mp hyA
      have hkS₃ : (k : Y) ∈ S₃ := mem_barPre.mpr ⟨k.2, by rw [hkφ]; exact hyS⟩
      have hkbot : (k : Y) ∈ (⊥ : Subgroup Y) := by
        rw [← h]
        exact Subgroup.mem_inf.mpr ⟨hkA, hkS₃⟩
      rw [Subgroup.mem_bot] at hkbot
      rw [← hkφ]
      have hk1 : k = 1 := Subtype.ext hkbot
      rw [hk1, map_one]
      exact Subgroup.mem_bot.mpr rfl
    · right
      intro y hy
      obtain ⟨k, hkA, hkφ⟩ := mem_barSub.mp hy
      have hkS₃ : (k : Y) ∈ S₃ := h hkA
      obtain ⟨hkL, hkS₂⟩ := mem_barPre.mp hkS₃
      have hkS₂' : φ k ∈ S₂ := by
        rwa [show (⟨(k : Y), hkL⟩ : ↥L) = k from Subtype.ext rfl] at hkS₂
      rwa [← hkφ]
  obtain ⟨Kbar, -, hAbarKbar, hnot, hshape, hsyl, hidx, hrank⟩ :=
    hM (barSub L φ S) (barSub L φ A) hSylSbar hAbarSbar hAbar_e hAbar4 hK1bar hTISbar
  have hK_le : barPre L φ Kbar ≤ L := barPre_le L φ Kbar
  have hA_K : A ≤ barPre L φ Kbar := by
    intro a ha
    have haL : a ∈ L := hAL ha
    exact mem_barPre.mpr ⟨haL, hAbarKbar (mem_barSub.mpr ⟨⟨a, haL⟩, ha, rfl⟩)⟩
  have hnotK : ¬ A ≤ oTwoMod (⊥ : Subgroup Y) (barPre L φ Kbar) := by
    intro hA'
    apply hnot
    have h1 : barSub L φ A ≤ barSub L φ (oTwoMod (⊥ : Subgroup Y) (barPre L φ Kbar)) :=
      wcgapt_barSub_mono hA'
    rw [oTwoMod_barPre hφ bot_le Kbar,
      barSub_barPre hφ (oTwoMod (⊥ : Subgroup M) Kbar)] at h1
    exact h1
  have hshapeK : HasQuotShape (barPre L φ Kbar)
      (oTwoMod (⊥ : Subgroup Y) (barPre L φ Kbar) : Set Y) (fun X _ => IsL2 X 2) := by
    have h1 := hasQuotShape_barPre (H := L) (C := (⊥ : Subgroup Y)) hφ hshape
    rw [← oTwoMod_barPre hφ bot_le Kbar] at h1
    exact h1
  have hnorm : barSub L φ (L ⊓ Subgroup.normalizer (S : Set Y)) =
      Subgroup.normalizer (barSub L φ S : Set M) := by
    have h1 : (L ⊓ Subgroup.normalizer (S : Set Y)).subgroupOf L =
        Subgroup.normalizer (S.subgroupOf L) := by
      change ((L ⊓ Subgroup.normalizer (S : Set Y)).comap L.subtype) =
        Subgroup.normalizer (S.comap L.subtype)
      rw [Subgroup.comap_inf,
        show L.comap L.subtype = (⊤ : Subgroup ↥L) from Subgroup.subgroupOf_self L, top_inf_eq]
      exact Subgroup.subgroupOf_normalizer_eq hSL
    change ((L ⊓ Subgroup.normalizer (S : Set Y)).subgroupOf L).map φ =
      Subgroup.normalizer ((S.subgroupOf L).map φ : Set M)
    rw [h1]
    exact Subgroup.map_equiv_normalizer_eq (S.subgroupOf L) e
  have hidxK : (barPre L φ Kbar ⊓ (L ⊓ Subgroup.normalizer (S : Set Y))).relIndex
      (barPre L φ Kbar) = 5 := by
    have h1 := wcgapt_relIndex_barPre (C := (⊥ : Subgroup Y)) (Pb := Kbar)
      (X := barPre L φ Kbar ⊓ (L ⊓ Subgroup.normalizer (S : Set Y))) hφ bot_le inf_le_left
    rw [h1]
    have h2 : barSub L φ (barPre L φ Kbar ⊓ (L ⊓ Subgroup.normalizer (S : Set Y))) =
        Kbar ⊓ (⊤ ⊓ Subgroup.normalizer (barSub L φ S : Set M)) := by
      rw [wcgapt_barSub_inf e.injective, barSub_barPre hφ Kbar, hnorm, top_inf_eq]
    rw [h2]
    exact hidx
  have hEqS : S ⊓ barPre L φ Kbar = barPre L φ (barSub L φ S ⊓ Kbar) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgS, hgK⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨hgL, hgKbar⟩ := mem_barPre.mp hgK
      exact mem_barPre.mpr ⟨hgL, ⟨mem_barSub.mpr ⟨⟨g, hgL⟩, hgS, rfl⟩, hgKbar⟩⟩
    · intro g hg
      obtain ⟨hgL, hgSbar, hgKbar⟩ := mem_barPre.mp hg
      have hgS : g ∈ S := by
        obtain ⟨s, hsS, hsφ⟩ := mem_barSub.mp hgSbar
        have hs_eq : s = ⟨g, hgL⟩ := e.injective hsφ
        have : (⟨g, hgL⟩ : ↥L) ∈ S.subgroupOf L := hs_eq ▸ hsS
        exact this
      exact Subgroup.mem_inf.mpr ⟨hgS, mem_barPre.mpr ⟨hgL, hgKbar⟩⟩
  have hsylK : IsSylowIn 2 (S ⊓ barPre L φ Kbar) (barPre L φ Kbar) := by
    rw [hEqS]
    refine ⟨wcgapt_barPre_mono inf_le_right, ?_, ?_⟩
    · exact (hsyl.isPGroup.comap_of_injective φ e.injective).map L.subtype
    · rw [wcgapt_relIndex_barPre' hφ]
      exact hsyl.not_dvd_relIndex
  refine ⟨barPre L φ Kbar, hK_le, hA_K, hnotK, hshapeK, hsylK, hidxK, ?_⟩
  intro hRk hNonComm
  have hNonCommBar : ¬ (∀ a ∈ barSub L φ A, ∀ s ∈ barSub L φ S, a * s = s * a) := by
    intro hcomm
    apply hNonComm
    intro a ha s hs
    have haL : a ∈ L := hAL ha
    have hsL : s ∈ L := hSL hs
    have hbarA : φ ⟨a, haL⟩ ∈ barSub L φ A :=
      mem_barSub.mpr ⟨⟨a, haL⟩, ha, rfl⟩
    have hbarS : φ ⟨s, hsL⟩ ∈ barSub L φ S :=
      mem_barSub.mpr ⟨⟨s, hsL⟩, by simpa using hs, rfl⟩
    have hcomm' := hcomm (φ ⟨a, haL⟩) hbarA (φ ⟨s, hsL⟩) hbarS
    have heq : (⟨a, haL⟩ : ↥L) * ⟨s, hsL⟩ = ⟨s, hsL⟩ * ⟨a, haL⟩ := by
      apply e.injective
      rw [map_mul, map_mul]
      exact hcomm'
    have := congrArg Subtype.val heq
    simpa using this
  obtain ⟨Pbar, hPbar, hKbar_eq⟩ := hrank hRk hNonCommBar
  refine ⟨barPre L φ Pbar, ?_, ?_⟩
  · have h1 := isMaxParabolicMod_barPre (H := L) (C := (⊥ : Subgroup Y)) hφ bot_le hPbar
    rw [barPre_top] at h1
    exact h1
  · have h1 := oddResMod_barPre (H := L) (C := (⊥ : Subgroup Y)) hφ bot_le Pbar
    rw [← hKbar_eq] at h1
    exact h1.symm

end CFSG.LocalAnalysis.WeakClosure81

end

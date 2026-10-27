module

public import CFSG.OddTranspositions.HalphaQuotient
import CFSG.OddTranspositions.BlockGraph
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem alpha_eq_singleton (hC : HypothesisC D)
    (hinj : Set.InjOn (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
      (DstarH hC))
    (hprim : ∀ B : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      B ⊆ imageClass hC → B.Nonempty →
      (∀ g, (fun y => g * y * g⁻¹) '' B = B ∨ Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
      B.Subsingleton ∨ B = imageClass hC) :
    hC.alpha = {hC.d} := by
  let H := Halpha D hC.alpha
  let K := CFSG.solvableRadical H
  let π := QuotientGroup.mk' K
  have hHcent : ∀ a ∈ hC.alpha, ∀ x ∈ Halpha D hC.alpha, Commute a x := by
    intro a ha x hx
    rw [Halpha] at hx
    exact Subgroup.closure_induction
      (p := fun x _ => Commute a x)
      (fun y hy => by
        obtain ⟨γ, hγ, hyγ⟩ := hy
        exact hγ.2.2.2 a ha y hyγ)
      (Commute.one_right a)
      (fun y z _ _ hy hz => hy.mul_right hz)
      (fun y _ hy => hy.inv_right)
      hx
  have hHcent' : ∀ a ∈ hC.alpha, ∀ x ∈ H, Commute a x := hHcent
  have hconj_mem : ∀ γ ∈ Dalpha D hC.alpha, ∀ g ∈ Halpha D hC.alpha,
      (fun y => g * y * g⁻¹) '' γ ∈ Dalpha D hC.alpha := by
    intro γ hγ g hg
    rcases mem_Dalpha_iff.mp hγ with ⟨hclass, hsubD, hne, hcomm⟩
    refine mem_Dalpha_iff.mpr ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨k, rfl⟩ := mem_blockClass_iff.mp hclass
      rw [mem_blockClass_iff]
      refine ⟨g * k, ?_⟩
      rw [Set.image_image]
      congr 1
      ext z
      group
    · rintro y ⟨z, hz, rfl⟩
      exact hC.setup.normal g z (hsubD hz)
    · intro hEq
      have hβ_eq : γ = hC.alpha := by
        have h1 : γ = (fun y => g⁻¹ * y * g) '' ((fun y => g * y * g⁻¹) '' γ) := by
          rw [Set.image_image]
          have h3 : (fun y => g⁻¹ * (g * y * g⁻¹) * g) = id := by
            funext y
            simp only [id_eq]
            group
          rw [h3, Set.image_id]
        rw [hEq] at h1
        have h2 : (fun y => g⁻¹ * y * g) '' hC.alpha = hC.alpha := by
          ext a
          constructor
          · rintro ⟨b, hb, rfl⟩
            have hcb : Commute b g := hHcent b hb g hg
            have h : g⁻¹ * b * g = b := by
              rw [← hcb.inv_right.eq]
              group
            change g⁻¹ * b * g ∈ hC.alpha
            rwa [h]
          · intro ha
            refine ⟨g * a * g⁻¹, ?_, ?_⟩
            · have hca : Commute a g := hHcent a ha g hg
              have h : g * a * g⁻¹ = a := by rw [← hca.eq]; group
              rwa [h]
            · group
        rw [h2] at h1
        exact h1
      exact hne hβ_eq
    · intro a ha b hb
      rcases hb with ⟨y, hy, rfl⟩
      exact ((hHcent a ha g hg).mul_right (hcomm a ha y hy)).mul_right
        (hHcent a ha g hg).inv_right
  obtain ⟨x₀, hx₀⟩ := DstarH_nonempty hC
  obtain ⟨β, hβ, -⟩ := (mem_DstarH_iff hC).mp hx₀
  let βH : Set H := {x | (x : G) ∈ β}
  let B : Set (H ⧸ K) := π '' βH
  have hB_sub : B ⊆ imageClass hC := by
    rintro z ⟨y, hyβH, rfl⟩
    exact ⟨y, (mem_DstarH_iff hC).mpr (subset_DalphaStar hβ (by simpa [βH] using hyβH)), rfl⟩
  have hB_ne : B.Nonempty := by
    obtain ⟨y, hyβ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
    let yH : H := ⟨y, Subgroup.subset_closure (subset_DalphaStar hβ hyβ)⟩
    exact ⟨π yH, yH, hyβ, rfl⟩
  have hB_prim : ∀ q : H ⧸ K,
      (fun y => q * y * q⁻¹) '' B = B ∨ Disjoint ((fun y => q * y * q⁻¹) '' B) B := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K q
    have hB_conj : (fun y => π g * y * (π g)⁻¹) '' B
        = π '' ((fun y => g * y * g⁻¹) '' βH) := by
      ext z
      constructor
      · rintro ⟨y, hyB, rfl⟩
        rcases hyB with ⟨x, hxβH, rfl⟩
        refine ⟨g * x * g⁻¹, ⟨x, hxβH, rfl⟩, ?_⟩
        simp only [map_mul, map_inv]
      · rintro ⟨y, ⟨x, hxβH, rfl⟩, rfl⟩
        refine ⟨π x, ⟨x, hxβH, rfl⟩, ?_⟩
        simp only [map_mul, map_inv]
    have hγ_mem : (fun y => (g : G) * y * (g : G)⁻¹) '' β ∈ Dalpha D hC.alpha :=
      hconj_mem β hβ (g : G) g.2
    have hγ_disj_or_eq : (fun y => (g : G) * y * (g : G)⁻¹) '' β = β ∨
        Disjoint ((fun y => (g : G) * y * (g : G)⁻¹) '' β) β := by
      by_cases hinter : (((fun y => (g : G) * y * (g : G)⁻¹) '' β) ∩ β).Nonempty
      · left
        exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha hγ_mem.1 hβ.1 hinter
      · right
        exact Set.disjoint_iff_inter_eq_empty.mpr
          (Set.not_nonempty_iff_eq_empty.mp hinter)
    rcases hγ_disj_or_eq with hγ_eq | hγ_disj
    · have hγH_eq : (fun y => g * y * g⁻¹) '' βH = βH := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          have hzG : (z : G) ∈ β := hz
          have hmem : ((g : G) * (z : G) * (g : G)⁻¹) ∈ β := by
            rw [← hγ_eq]
            exact ⟨(z : G), hzG, rfl⟩
          simpa [βH] using hmem
        · intro hy
          have hyG : (y : G) ∈ β := hy
          have hmem : (y : G) ∈ (fun x => (g : G) * x * (g : G)⁻¹) '' β := by
            rw [hγ_eq]
            exact hyG
          rcases hmem with ⟨z, hzβ, hzy⟩
          have hzDstar : z ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hzβ
          let zH : H := ⟨z, Subgroup.subset_closure hzDstar⟩
          have hzHβ : zH ∈ βH := hzβ
          refine ⟨zH, hzHβ, ?_⟩
          apply Subtype.ext
          exact hzy
      left
      rw [hB_conj, hγH_eq]
    · right
      rw [hB_conj]
      rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
      intro z hz
      rcases hz with ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
      have hxy : π x = π y := hxz.trans hyz.symm
      have hxmem : x ∈ DstarH hC := by
        rcases hx with ⟨x', hx', hx'x⟩
        rw [← hx'x]
        exact DstarH_conj_mem hC (h := g) (x := x')
          ((mem_DstarH_iff hC).mpr (subset_DalphaStar hβ hx'))
      have hymem : y ∈ DstarH hC :=
        (mem_DstarH_iff hC).mpr (subset_DalphaStar hβ (by simpa [βH] using hy))
      have hx_eq_y : x = y := hinj hxmem hymem hxy
      have hxγ : (x : G) ∈ (fun y => (g : G) * y * (g : G)⁻¹) '' β := by
        rcases hx with ⟨x', hx', hx'x⟩
        exact ⟨(x' : G), hx', congrArg Subtype.val hx'x⟩
      have hxβ : (x : G) ∈ β := by
        rw [hx_eq_y]
        exact hy
      exact (Set.disjoint_left.mp hγ_disj hxγ) hxβ
  have hB_cases := hprim B hB_sub hB_ne hB_prim
  rcases hB_cases with hB_single | hB_eq
  ·
    have hβH_single : βH.Subsingleton := by
      intro x hx y hy
      have hx' : x ∈ DstarH hC :=
        (mem_DstarH_iff hC).mpr (subset_DalphaStar hβ (by simpa [βH] using hx))
      have hy' : y ∈ DstarH hC :=
        (mem_DstarH_iff hC).mpr (subset_DalphaStar hβ (by simpa [βH] using hy))
      exact hinj hx' hy' (hB_single ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
    have hβ_single : β.Subsingleton := by
      intro x hx y hy
      let xH : H := ⟨x, Subgroup.subset_closure (subset_DalphaStar hβ hx)⟩
      let yH : H := ⟨y, Subgroup.subset_closure (subset_DalphaStar hβ hy)⟩
      have hxH : xH ∈ βH := hx
      have hyH : yH ∈ βH := hy
      have : xH = yH := hβH_single hxH hyH
      exact Subtype.ext_iff.mp this
    have hα_single : hC.alpha.Subsingleton := by
      obtain ⟨c, hc⟩ := mem_blockClass_iff.mp hβ.1
      intro x hx y hy
      have hxβ : c * x * c⁻¹ ∈ β := by rw [hc]; exact ⟨x, hx, rfl⟩
      have hyβ : c * y * c⁻¹ ∈ β := by rw [hc]; exact ⟨y, hy, rfl⟩
      have h_eq : c * x * c⁻¹ = c * y * c⁻¹ := hβ_single hxβ hyβ
      have hinj_c : Function.Injective (fun z => c * z * c⁻¹) := by
        intro a b hab
        have hab' : c * a * c⁻¹ = c * b * c⁻¹ := by simpa using hab
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = c⁻¹ * (c * b * c⁻¹) * c := by rw [hab']
          _ = b := by group
      exact hinj_c h_eq
    exact Set.Subsingleton.eq_singleton_of_mem hα_single hC.d_mem_alpha
  ·
    exfalso
    have hDstarH_sub_βH : DstarH hC ⊆ βH := by
      intro x hx
      have hxB : π x ∈ B := by
        rw [hB_eq]
        exact ⟨x, hx, rfl⟩
      rcases hxB with ⟨y, hyβH, hxy⟩
      have hy' : y ∈ DstarH hC :=
        (mem_DstarH_iff hC).mpr (subset_DalphaStar hβ (by simpa [βH] using hyβH))
      have hx_eq_y : x = y := hinj hx hy' hxy.symm
      rwa [hx_eq_y]
    have hDstar_sub_β : DalphaStar D hC.alpha ⊆ β := by
      intro x hx
      have hxH : x ∈ Halpha D hC.alpha := Subgroup.subset_closure hx
      have hx' : (⟨x, hxH⟩ : H) ∈ DstarH hC := (mem_DstarH_iff hC).mpr hx
      have := hDstarH_sub_βH hx'
      change (⟨x, hxH⟩ : H) ∈ βH
      exact this
    have hDalpha_eq_singleton : Dalpha D hC.alpha = {β} := by
      ext γ
      constructor
      · intro hγ
        have hγ_sub_β : γ ⊆ β := fun z hz => hDstar_sub_β (subset_DalphaStar hγ hz)
        obtain ⟨z, hzγ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ.1
        have hinter : (γ ∩ β).Nonempty := ⟨z, hzγ, hγ_sub_β hzγ⟩
        have hγ_eq_β : γ = β :=
          eq_of_mem_of_mem_blockClass hC.isBlock_alpha hγ.1 hβ.1 hinter
        rw [hγ_eq_β]
        rfl
      · intro hγ
        rw [Set.mem_singleton_iff] at hγ
        rw [hγ]
        exact hβ
    obtain ⟨c, hc⟩ := mem_blockClass_iff.mp hβ.1
    have hDalpha_β_eq_singleton : Dalpha D β = {hC.alpha} := by
      have hα_mem : hC.alpha ∈ Dalpha D β := by
        refine mem_Dalpha_iff.mpr ⟨?_, hC.isBlock_alpha.subset, hβ.2.2.1.symm, ?_⟩
        · exact mem_blockClass_comm.mp hβ.1
        · intro a ha b hb
          exact (hβ.2.2.2 b hb a ha).symm
      have h := Dalpha_conj_image (β := hC.alpha) hC.setup.normal c
      rw [← hc, hDalpha_eq_singleton] at h
      rw [Set.image_singleton] at h
      have hα_eq : hC.alpha = (fun x => c * x * c⁻¹) '' β := by
        have : hC.alpha ∈ ({(fun x => c * x * c⁻¹) '' β} : Set (Set G)) := by
          rw [h]
          exact hα_mem
        simpa using this
      rw [← hα_eq] at h
      exact h.symm
    have hcomm_mem : ∀ a ∈ hC.alpha ∪ β, ∀ x ∈ D, Commute a x → x ∈ hC.alpha ∪ β := by
      intro a ha x hxD hax
      obtain ⟨γ, hγclass, hxγ⟩ :=
        exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hxD
      rcases ha with haα | haβ
      · by_cases hγα : γ = hC.alpha
        · rw [hγα] at hxγ
          exact Or.inl hxγ
        · obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hγclass
          have hne : (fun y => g * y * g⁻¹) '' hC.alpha ≠ hC.alpha := by
            rw [← hg]
            exact hγα
          have hxγ' : x ∈ (fun y => g * y * g⁻¹) '' hC.alpha := by
            rw [← hg]
            exact hxγ
          have hcomm := commute_block_of_mem_apply hC.setup.normal hC.setup.oddT
            hC.isBlock_alpha hne haα hxγ' hax
          have hγD : γ ⊆ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγclass
          have hγDalpha : γ ∈ Dalpha D hC.alpha := by
            refine mem_Dalpha_iff.mpr ⟨hγclass, hγD, hγα, ?_⟩
            intro a' ha' b hb
            rw [hg] at hb
            exact hcomm a' ha' b hb
          rw [hDalpha_eq_singleton] at hγDalpha
          rw [Set.mem_singleton_iff] at hγDalpha
          rw [hγDalpha] at hxγ
          exact Or.inr hxγ
      · by_cases hγβ : γ = β
        · rw [hγβ] at hxγ
          exact Or.inr hxγ
        · have hγclassβ : γ ∈ blockClass β :=
            mem_blockClass_of_mem_blockClass hβ.1 hγclass
          obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hγclassβ
          have hne : (fun y => g * y * g⁻¹) '' β ≠ β := by
            rw [← hg]
            exact hγβ
          have hxγ' : x ∈ (fun y => g * y * g⁻¹) '' β := by
            rw [← hg]
            exact hxγ
          have hβblock : IsBlock D β :=
            isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ.1
          have hcomm := commute_block_of_mem_apply hC.setup.normal hC.setup.oddT
            hβblock hne haβ hxγ' hax
          have hγD : γ ⊆ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγclass
          have hγDbeta : γ ∈ Dalpha D β := by
            refine mem_Dalpha_iff.mpr ⟨hγclassβ, hγD, hγβ, ?_⟩
            intro a' ha' b hb
            rw [hg] at hb
            exact hcomm a' ha' b hb
          rw [hDalpha_β_eq_singleton] at hγDbeta
          rw [Set.mem_singleton_iff] at hγDbeta
          rw [hγDbeta] at hxγ
          exact Or.inl hxγ
    have hD_sub : D ⊆ hC.alpha ∪ β := by
      intro x hxD
      exact mem_of_reach hcomm_mem (Or.inl hC.d_mem_alpha)
        (reach_of_not_disconnected hC.conn hC.hd hxD)
    have hD_norm : D ⊆ Subgroup.normalizer hC.alpha := by
      intro x hxD
      rcases hD_sub hxD with hxα | hxβ
      · apply (Subgroup.mem_normalizer_iff_conj_image_eq).mpr
        have hx_image : x ∈ (fun y => x * y * x⁻¹) '' hC.alpha := ⟨x, hxα, by group⟩
        have hinter : (hC.alpha ∩ (fun y => x * y * x⁻¹) '' hC.alpha).Nonempty :=
          ⟨x, hxα, hx_image⟩
        have hclass : (fun y => x * y * x⁻¹) '' hC.alpha ∈ blockClass hC.alpha :=
          mem_blockClass_iff.mpr ⟨x, rfl⟩
        have heq := eq_of_mem_of_mem_blockClass hC.isBlock_alpha
          (mem_blockClass_self hC.alpha) hclass hinter
        exact heq.symm
      · apply (Subgroup.mem_normalizer_iff_conj_image_eq).mpr
        have hcomm : ∀ a ∈ hC.alpha, Commute a x := fun a ha => hβ.2.2.2 a ha x hxβ
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          have hcz : Commute x z := (hcomm z hz).symm
          rw [MulAut.conj_apply]
          rw [show x * z * x⁻¹ = z from by rw [hcz.eq]; group]
          exact hz
        · intro hy
          have hcy : Commute x y := (hcomm y hy).symm
          refine ⟨x * y * x⁻¹, ?_, ?_⟩
          · rw [show x * y * x⁻¹ = y from by rw [hcy.eq]; group]
            exact hy
          · rw [MulAut.conj_apply]
            calc x * (x * y * x⁻¹) * x⁻¹
                = x * (x * y) * x⁻¹ * x⁻¹ := by group
              _ = x * (y * x) * x⁻¹ * x⁻¹ := by rw [hcy.eq]
              _ = x * y * x⁻¹ := by group
              _ = y * x * x⁻¹ := by rw [hcy.eq]
              _ = y := by group
    have hG_norm : Subgroup.normalizer hC.alpha = ⊤ := by
      rw [eq_top_iff, ← hC.setup.gen, Subgroup.closure_le]
      exact hD_norm
    have hD_sub_alpha : D ⊆ hC.alpha := by
      intro x hxD
      obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hxD)
      have hg_norm : g ∈ Subgroup.normalizer hC.alpha := by
        rw [hG_norm]
        exact Subgroup.mem_top g
      have hg_image : g * hC.d * g⁻¹ ∈ hC.alpha := by
        have hthis := Subgroup.mem_normalizer_iff_conj_image_eq.mp hg_norm
        rw [← hthis]
        exact ⟨hC.d, hC.d_mem_alpha, rfl⟩
      rwa [← hg]
    exact hC.isBlock_alpha.ne_univ
      (Set.Subset.antisymm hC.isBlock_alpha.subset hD_sub_alpha)

end CFSG.OddTranspositions.PartThree

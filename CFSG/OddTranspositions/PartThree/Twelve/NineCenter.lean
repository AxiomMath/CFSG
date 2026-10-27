module

public import CFSG.OddTranspositions.PartThree.Twelve.Nine
import CFSG.OddTranspositions.PartThree.Nine.Setup

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Timmesfeld.Connectivity
open CFSG.Fischer
open scoped Pointwise

variable {G : Type} [Group G] {D : Set G}

private def twinSet (D : Set G) (a : G) : Set G := {x | x ∈ D ∧ commSet D x = commSet D a}

private theorem image_conj_twinSet (hN : IsNormalSet D) (g a : G) :
    (fun x => g * x * g⁻¹) '' twinSet D a = twinSet D (g * a * g⁻¹) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyD, hy⟩, rfl⟩
    exact ⟨hN g y hyD, by rw [commSet_conj hN g y, commSet_conj hN g a, hy]⟩
  · intro hx
    refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, by group⟩
    · simpa using hN g⁻¹ x hx.1
    · have hcg : commSet D (g⁻¹ * x * g) = cimg g⁻¹ (commSet D x) := by
        simpa using commSet_conj hN g⁻¹ x
      rw [hcg, hx.2, ← commSet_conj hN g⁻¹ (g * a * g⁻¹)]
      congr 1
      group

private theorem smul_twinSet (hN : IsNormalSet D) (g : ConjAct G) (a : G) :
    g • twinSet D a = twinSet D (g • a) := by
  rw [← Set.image_smul]
  exact image_conj_twinSet hN (ConjAct.ofConjAct g) a

theorem eq_of_commSet_eq [Finite G] (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) (h : commSet D a = commSet D b) : a = b := by
  classical
  have hN : IsNormalSet D := hC.setup.normal
  set T : Set G := twinSet D a with hT
  have hTsub : T ⊆ D := fun _ hx => hx.1
  have haT : a ∈ T := ⟨ha, rfl⟩
  have hbT : b ∈ T := ⟨hb, h.symm⟩
  have hTblock : MulAction.IsBlock (ConjAct G) T := by
    rw [MulAction.isBlock_iff_smul_eq_smul_of_nonempty]
    rintro g₁ g₂ ⟨x, hx₁, hx₂⟩
    rw [hT] at hx₁ hx₂
    rw [smul_twinSet hN g₁ a] at hx₁
    rw [smul_twinSet hN g₂ a] at hx₂
    rw [hT, smul_twinSet hN g₁ a, smul_twinSet hN g₂ a]
    have heq : commSet D (g₁ • a) = commSet D (g₂ • a) := hx₁.2.symm.trans hx₂.2
    ext x
    simp only [twinSet, Set.mem_setOf_eq]
    rw [heq]
  by_cases hTD : T = D
  ·
    have hmem : ∀ x ∈ D, Commute x a → x = a := by
      intro x hxD hxa
      by_contra hne
      have hxT : x ∈ T := by rw [hTD]; exact hxD
      have hxcs : x ∉ commSet D x := fun h => h.2.2 rfl
      have hxca : x ∉ commSet D a := by
        rw [← hxT.2]
        exact hxcs
      exact hxca ⟨hxD, hxa, hne⟩
    have hreach : Reach D a b := reach_of_not_disconnected hC.conn ha hb
    have hb'a : b ∈ ({a} : Set G) :=
      mem_of_reach
        (fun x hx y hy hxy => by
          rw [Set.mem_singleton_iff] at hx ⊢
          subst hx
          exact hmem y hy hxy.symm)
        (Set.mem_singleton a) hreach
    rw [Set.mem_singleton_iff] at hb'a
    exact hb'a.symm
  ·
    obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj ha hC.hd)
    have hgD : ∀ h : ConjAct G, h • (D : Set G) = D := by
      intro h
      rw [← Set.image_smul]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [ConjAct.smul_def] using hC.setup.conj_mem (ConjAct.ofConjAct h) hy
      · intro hx
        refine ⟨ConjAct.ofConjAct h⁻¹ * x * ConjAct.ofConjAct h, ?_, ?_⟩
        · simpa [ConjAct.smul_def] using hC.setup.conj_mem (ConjAct.ofConjAct h⁻¹) hx
        · simp only [ConjAct.smul_def, ConjAct.ofConjAct_inv]
          group
    have hgTsub : ConjAct.toConjAct g • T ⊆ D := by
      intro x hx
      rw [hT, Set.mem_smul_set] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa [ConjAct.smul_def] using hC.setup.conj_mem g hy.1
    have hdT : hC.d ∈ ConjAct.toConjAct g • T := by
      rw [hT]
      refine ⟨a, ⟨ha, rfl⟩, ?_⟩
      simpa [ConjAct.smul_def] using hg
    have hαT : hC.alpha ⊆ ConjAct.toConjAct g • T := by
      rw [hα]
      exact Set.singleton_subset_iff.mpr hdT
    have hgTne : ConjAct.toConjAct g • T ≠ D := by
      intro heq
      apply hTD
      have h1 : (ConjAct.toConjAct g)⁻¹ • (ConjAct.toConjAct g • T) =
          (ConjAct.toConjAct g)⁻¹ • D := by rw [heq]
      rwa [inv_smul_smul, hgD] at h1
    have hEqα : ConjAct.toConjAct g • T = hC.alpha :=
      hC.isMaxBlock_alpha.2.2.2.2 (ConjAct.toConjAct g • T) hαT hgTsub hgTne
        (hTblock.translate _)
    have hTsing : T = {a} := by
      have h1 : (ConjAct.toConjAct g)⁻¹ • (ConjAct.toConjAct g • T) =
          (ConjAct.toConjAct g)⁻¹ • hC.alpha := by rw [hEqα]
      rw [inv_smul_smul, hα, Set.smul_set_singleton] at h1
      rw [h1]
      congr 1
      simp only [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct]
      rw [← hg]
      group
    rw [hTsing, Set.mem_singleton_iff] at hbT
    exact hbT.symm

theorem centralizer_commSet_eq_zpowers (hS : Asc72.Setup G D) (hZ : Subgroup.center G = ⊥)
    (htwin : ∀ a ∈ D, ∀ b ∈ D, commSet D a = commSet D b → a = b) {u : G} (hu : u ∈ D)
    (haxis : ∀ σ : commGraph D ≃g commGraph D, (∀ v : D, Commute (v : G) u → σ v = v) →
      (∀ v : D, σ v = v) ∨ ∀ v : D, (σ v : G) = u * v * u) :
    Subgroup.centralizer (commSet D u) = Subgroup.zpowers u := by
  have hN : IsNormalSet D := hS.normal
  have huu : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have hcenter_one : ∀ h : G, (∀ x ∈ D, Commute h x) → h = 1 := by
    intro h hh
    have hcenter : h ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hle : Subgroup.closure D ≤ Subgroup.centralizer ({h} : Set G) := by
        rw [Subgroup.closure_le]
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hh y hy).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hS.gen ▸ Subgroup.mem_top x))
    rw [hZ] at hcenter
    simpa using hcenter
  have hgu_of_centralizes : ∀ g : G, g ∈ Subgroup.centralizer (commSet D u) →
      g * u * g⁻¹ = u := by
    intro g hg
    apply htwin (g * u * g⁻¹) (hS.conj_mem g hu) u hu
    rw [commSet_conj hN g u]
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      have hyg : y * g = g * y := (Subgroup.mem_centralizer_iff.mp hg) y hy
      have hy' : g * y * g⁻¹ = y := by rw [← hyg]; group
      simpa [hy'] using hy
    · intro x hx
      refine ⟨x, hx, ?_⟩
      have hxg : x * g = g * x := (Subgroup.mem_centralizer_iff.mp hg) x hx
      show g * x * g⁻¹ = x
      rw [← hxg]
      group
  refine le_antisymm ?_ ?_
  · intro g hg
    let e : D ≃ D :=
      { toFun := fun v => ⟨g * (v : G) * g⁻¹, hN g v v.2⟩
        invFun := fun v => ⟨g⁻¹ * (v : G) * g, by simpa using hN g⁻¹ v v.2⟩
        left_inv := fun v => Subtype.ext (by group)
        right_inv := fun v => Subtype.ext (by group) }
    let cg : commGraph D ≃g commGraph D :=
      { toEquiv := e
        map_rel_iff' := by
          intro a b
          have ha : (e a : G) = g * (a : G) * g⁻¹ := rfl
          have hb : (e b : G) = g * (b : G) * g⁻¹ := rfl
          rw [commGraph_adj_iff, commGraph_adj_iff, ha, hb]
          rw [(conj_injective g).ne_iff, conj_commute_iff g (a : G) (b : G)] }
    have hgu : g * u * g⁻¹ = u := hgu_of_centralizes g hg
    have hcgfix : ∀ v : D, Commute (v : G) u → cg v = v := by
      intro v hv
      refine Subtype.ext ?_
      have hcv : (cg v : G) = g * (v : G) * g⁻¹ := rfl
      rw [hcv]
      by_cases hvu : (v : G) = u
      · rw [hvu]
        exact hgu
      · have hvcs : (v : G) ∈ commSet D u := ⟨v.2, hv, hvu⟩
        have hvcomm : (v : G) * g = g * (v : G) :=
          (Subgroup.mem_centralizer_iff.mp hg) _ hvcs
        rw [← hvcomm]
        group
    rcases haxis cg hcgfix with hall | hconj
    ·
      have hgcomm : ∀ x ∈ D, Commute g x := by
        intro x hx
        have hv := hall ⟨x, hx⟩
        have hv' : g * x * g⁻¹ = x := congrArg Subtype.val hv
        have h := congrArg (fun y => y * g) hv'
        rw [commute_iff_eq]
        simpa [mul_assoc] using h
      have hg1 : g = 1 := hcenter_one g hgcomm
      rw [hg1]
      exact Subgroup.one_mem _
    ·
      have hkcomm : ∀ x ∈ D, Commute (u⁻¹ * g) x := by
        intro x hx
        have hv := hconj ⟨x, hx⟩
        have hv' : g * x * g⁻¹ = u * x * u := hv
        have hx1 : u⁻¹ * (g * x * g⁻¹) * u = x := by
          rw [hv']
          rw [show u⁻¹ * (u * x * u) * u = x * (u * u) by group, huu, mul_one]
        have hx2 : (u⁻¹ * g) * x * (u⁻¹ * g)⁻¹ = x := by
          calc (u⁻¹ * g) * x * (u⁻¹ * g)⁻¹
              = u⁻¹ * (g * x * g⁻¹) * u := by group
            _ = x := hx1
        have h := congrArg (fun y => y * (u⁻¹ * g)) hx2
        rw [commute_iff_eq]
        simpa [mul_assoc] using h
      have hk1 : u⁻¹ * g = 1 := hcenter_one (u⁻¹ * g) hkcomm
      have hgu' : g = u := by
        have h : u * (u⁻¹ * g) = g := by group
        rw [hk1, mul_one] at h
        exact h.symm
      rw [hgu']
      exact Subgroup.mem_zpowers u
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => hx.2.1

theorem center_Halpha_le [Finite G] (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    (hZ : Subgroup.center G = ⊥)
    (haxis : ∀ σ : commGraph D ≃g commGraph D, (∀ v : D, Commute (v : G) hC.d → σ v = v) →
      (∀ v : D, σ v = v) ∨ ∀ v : D, (σ v : G) = hC.d * v * hC.d)
    {z : Halpha D hC.alpha} (hz : z ∈ Subgroup.center (Halpha D hC.alpha)) :
    (z : G) = 1 ∨ (z : G) = hC.d := by
  have htwin : ∀ a ∈ D, ∀ b ∈ D, commSet D a = commSet D b → a = b :=
    fun a ha b hb h => eq_of_commSet_eq hC hα ha hb h
  have hcent := centralizer_commSet_eq_zpowers hC.setup hZ htwin hC.hd haxis
  have hzmem : (z : G) ∈ Subgroup.centralizer (commSet D hC.d) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxH : x ∈ Halpha D hC.alpha := by
      rw [Halpha, CFSG.OddTranspositions.PartThree.Nine.DalphaStar_eq_commSet hC hα]
      exact Subgroup.subset_closure hx
    have hzcomm : (⟨x, hxH⟩ : Halpha D hC.alpha) * z = z * ⟨x, hxH⟩ :=
      (Subgroup.mem_center_iff.mp hz) _
    exact congrArg Subtype.val hzcomm
  have hmem : (z : G) ∈ Subgroup.zpowers hC.d := by
    rw [hcent] at hzmem
    exact hzmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← hk, ← zpow_mod_orderOf hC.d k, hC.setup.oddT.orderOf_eq_two hC.hd]
  rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
  · left
    rw [show k % ((2 : ℕ) : ℤ) = 0 by simpa using hk0]
    simp
  · right
    rw [show k % ((2 : ℕ) : ℤ) = 1 by simpa using hk1]
    simp

end CFSG.OddTranspositions.PartThree

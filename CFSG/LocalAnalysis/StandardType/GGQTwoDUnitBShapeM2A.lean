module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProj
public import CFSG.GH74.L5U5.ModelsPairsUnitary
public import CFSG.GH74.L5U5.IdentUnitary
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}

theorem qtwoDB3_exists_aut (hK : Nat.card F0 = (2 ^ 1) ^ 2) (hm : 5 ≤ m) {ψ : Su F0 2 1 m →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m)) :
    ∃ Φ : ↥(Subgroup.normalizer (ψ.range : Set G)) →*
        MulAut (StatedProj (StatedSU m (2 ^ 1) F0)),
      (∀ g : ↥(Subgroup.normalizer (ψ.range : Set G)),
        Φ g = 1 ↔ (g : G) ∈ Subgroup.centralizer (ψ.range : Set G)) ∧
      ∀ (g : ↥(Subgroup.normalizer (ψ.range : Set G))) (u u' : Su F0 2 1 m),
        ψ u' = (g : G) * ψ u * (g : G)⁻¹ →
          Φ g (projH _ (CFSG.GH74.L5U5.suEquiv hK m u)) =
            projH _ (CFSG.GH74.L5U5.suEquiv hK m u') := by
  have hd : 3 ≤ m := by omega
  have hdq : (m, 2 ^ 1) ≠ (3, 2) := by
    rintro h
    exact (by omega : m ≠ 3) (congrArg Prod.fst h)
  have hperfSu : Group.IsPerfect (Su F0 2 1 m) :=
    (CFSG.GH74.L5U5.isQuasisimple_su hK hd hdq).1
  haveI : Group.IsPerfect (Su F0 2 1 m) := hperfSu
  haveI hperfL : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  let q : Su F0 2 1 m →* ↥ψ.range := ψ.rangeRestrict
  have hq : Function.Surjective q := ψ.rangeRestrict_surjective
  have hqker : q.ker ≤ Subgroup.center (Su F0 2 1 m) := by
    change ψ.rangeRestrict.ker ≤ Subgroup.center (Su F0 2 1 m)
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hcomap : (Subgroup.center ↥ψ.range).comap q =
      Subgroup.center (Su F0 2 1 m) :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperfSu q hq hqker
  have hle : Subgroup.center (Su F0 2 1 m) ≤
      (Subgroup.center ↥ψ.range).comap q := by
    rw [hcomap]
  let fmap : Su F0 2 1 m ⧸ Subgroup.center (Su F0 2 1 m) →*
      ↥ψ.range ⧸ Subgroup.center ↥ψ.range :=
    QuotientGroup.map (Subgroup.center (Su F0 2 1 m))
      (Subgroup.center ↥ψ.range) q hle
  have hfmap_mk : ∀ u : Su F0 2 1 m,
      fmap (QuotientGroup.mk u) = QuotientGroup.mk (q u) := by
    intro u
    exact QuotientGroup.map_mk _ _ q hle u
  have hinj : Function.Injective fmap := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hfmap_mk u, QuotientGroup.eq_one_iff] at hx
    rw [QuotientGroup.eq_one_iff, ← hcomap]
    exact hx
  have hsurj : Function.Surjective fmap := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨u, rfl⟩ := hq y'
    exact ⟨QuotientGroup.mk u, hfmap_mk u⟩
  let eL : Su F0 2 1 m ⧸ Subgroup.center (Su F0 2 1 m) ≃*
      ↥ψ.range ⧸ Subgroup.center ↥ψ.range :=
    MulEquiv.ofBijective fmap ⟨hinj, hsurj⟩
  have heL_mk : ∀ u : Su F0 2 1 m,
      eL (QuotientGroup.mk u) = QuotientGroup.mk (q u) := by
    intro u
    change fmap (QuotientGroup.mk u) = QuotientGroup.mk (q u)
    rw [hfmap_mk u]
  let nAut : ↥(Subgroup.normalizer (ψ.range : Set G)) →* MulAut ↥ψ.range :=
    Subgroup.normalizerMonoidHom ψ.range
  let cAut : MulAut ↥ψ.range →*
      MulAut (↥ψ.range ⧸ Subgroup.center ↥ψ.range) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥ψ.range
  let α : ↥(Subgroup.normalizer (ψ.range : Set G)) →*
      MulAut (Su F0 2 1 m ⧸ Subgroup.center (Su F0 2 1 m)) :=
    (MulAut.congr eL.symm).toMonoidHom.comp (cAut.comp nAut)
  let e₁ : Su F0 2 1 m ⧸ Subgroup.center (Su F0 2 1 m) ≃*
      ↥(StatedSU m (2 ^ 1) F0) ⧸ Subgroup.center (StatedSU m (2 ^ 1) F0) :=
    QuotientGroup.congr (Subgroup.center (Su F0 2 1 m))
      (Subgroup.center (StatedSU m (2 ^ 1) F0))
      (CFSG.GH74.L5U5.suEquiv hK m)
      (Subgroup.map_center_eq (CFSG.GH74.L5U5.suEquiv hK m))
  let e₂ : ↥(StatedSU m (2 ^ 1) F0) ⧸ Subgroup.center (StatedSU m (2 ^ 1) F0) ≃*
      StatedProj (StatedSU m (2 ^ 1) F0) :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
        (F := F0) (p := 2) (f := 1) (n := m) hK hd hdq).2
  let e : Su F0 2 1 m ⧸ Subgroup.center (Su F0 2 1 m) ≃*
      StatedProj (StatedSU m (2 ^ 1) F0) := e₁.trans e₂
  have he₁ : ∀ u : Su F0 2 1 m, e₁ (QuotientGroup.mk u) =
      QuotientGroup.mk (CFSG.GH74.L5U5.suEquiv hK m u) :=
    fun u => QuotientGroup.congr_mk (Subgroup.center (Su F0 2 1 m))
      (Subgroup.center (StatedSU m (2 ^ 1) F0))
      (CFSG.GH74.L5U5.suEquiv hK m)
      (Subgroup.map_center_eq (CFSG.GH74.L5U5.suEquiv hK m)) u
  have he₂ : ∀ x : ↥(StatedSU m (2 ^ 1) F0),
      e₂ (QuotientGroup.mk x) = QuotientGroup.mk x :=
    fun x => QuotientGroup.quotientMulEquivOfEq_mk _ x
  have he_mk : ∀ u : Su F0 2 1 m,
      e (QuotientGroup.mk u) = projH (StatedSU m (2 ^ 1) F0)
        (CFSG.GH74.L5U5.suEquiv hK m u) := by
    intro u
    change e₂ (e₁ (QuotientGroup.mk u)) = projH (StatedSU m (2 ^ 1) F0)
      (CFSG.GH74.L5U5.suEquiv hK m u)
    rw [he₁ u, he₂ (CFSG.GH74.L5U5.suEquiv hK m u)]
    rfl
  let Φ : ↥(Subgroup.normalizer (ψ.range : Set G)) →*
      MulAut (StatedProj (StatedSU m (2 ^ 1) F0)) :=
    (MulAut.congr e).toMonoidHom.comp α
  refine ⟨Φ, ?_, ?_⟩
  · intro g
    constructor
    · intro hg
      have hΦ1 : MulAut.congr e (α g) = 1 := hg
      have hα : α g = 1 := (MulAut.congr e).injective (by rw [hΦ1, map_one])
      have hα' : MulAut.congr eL.symm (cAut (nAut g)) = 1 := hα
      have hc : cAut (nAut g) = 1 :=
        (MulAut.congr eL.symm).injective (by rw [hα', map_one])
      have hn : nAut g = 1 :=
        CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp
          (nAut g) hc
      have hgker : g ∈ nAut.ker := MonoidHom.mem_ker.mpr hn
      have hgker2 : g ∈ (Subgroup.normalizerMonoidHom ψ.range).ker := hgker
      rw [Subgroup.normalizerMonoidHom_ker] at hgker2
      exact Subgroup.mem_subgroupOf.mp hgker2
    · intro hg
      have hg' : g ∈ nAut.ker := by
        have h2 : g ∈ (Subgroup.normalizerMonoidHom ψ.range).ker := by
          rw [Subgroup.normalizerMonoidHom_ker]
          exact Subgroup.mem_subgroupOf.mpr hg
        exact h2
      have hn : nAut g = 1 := MonoidHom.mem_ker.mp hg'
      have hc : cAut (nAut g) = 1 := by rw [hn, map_one]
      have hα : α g = 1 := by
        change MulAut.congr eL.symm (cAut (nAut g)) = 1
        rw [hc, map_one]
      change MulAut.congr e (α g) = 1
      rw [hα, map_one]
  · intro g u u' huu
    have hconj : nAut g (q u) = q u' := by
      change (Subgroup.normalizerMonoidHom ψ.range g) (q u) = q u'
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change (g : G) * ψ u * (g : G)⁻¹ = ψ u'
      rw [huu]
    have hαu : α g (QuotientGroup.mk u) = QuotientGroup.mk u' := by
      change eL.symm (cAut (nAut g) (eL (QuotientGroup.mk u))) = QuotientGroup.mk u'
      rw [heL_mk u]
      rw [show cAut (nAut g) (QuotientGroup.mk (q u)) =
          QuotientGroup.mk (nAut g (q u)) from
        CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
          (nAut g) (q u)]
      rw [hconj, ← heL_mk u']
      exact eL.symm_apply_apply (QuotientGroup.mk u')
    have hΦu : Φ g (projH _ (CFSG.GH74.L5U5.suEquiv hK m u)) =
        projH _ (CFSG.GH74.L5U5.suEquiv hK m u') := by
      change e (α g (e.symm (projH (StatedSU m (2 ^ 1) F0)
        (CFSG.GH74.L5U5.suEquiv hK m u)))) = projH (StatedSU m (2 ^ 1) F0)
          (CFSG.GH74.L5U5.suEquiv hK m u')
      rw [← he_mk u, e.symm_apply_apply, hαu, he_mk u']
    exact hΦu

end CFSG.StandardType.QTwo

end

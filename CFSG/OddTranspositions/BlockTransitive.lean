module

public import CFSG.OddTranspositions.Blocks
public import CFSG.Timmesfeld.Bridge.OddLocalBlock

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity
open scoped Pointwise

variable {G : Type*} [Group G]

theorem IsMaxBlock.isBlock {D α : Set G} (h : IsMaxBlock D α) : IsBlock D α := by
  refine ⟨h.2.1, h.1, h.2.2.1, ?_⟩
  intro g hg
  have hne : ConjAct.toConjAct g • α ≠ α := smul_ne_self_of_not_mem_normalizer hg
  have hd := (MulAction.isBlock_iff_disjoint_smul_of_ne.mp h.2.2.2.1) hne
  have himg : ConjAct.toConjAct g • α = (fun x => g * x * g⁻¹) '' α := by
    rw [← Set.image_smul]
    rfl
  rw [himg] at hd
  exact hd.symm

theorem eq_of_mem_of_mem_blockClass {D α β γ : Set G} (hα : IsBlock D α)
    (hβ : β ∈ blockClass α) (hγ : γ ∈ blockClass α)
    (h : (β ∩ γ).Nonempty) : β = γ := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff'.mp hβ
  obtain ⟨k, rfl⟩ := mem_blockClass_iff'.mp hγ
  exact (MulAction.isBlock_iff_smul_eq_smul_of_nonempty.mp hα.isBlock) h

theorem Dalpha_subset_maxOrbit [Finite G] {D : Set G} (hS : Setup G D)
    (hconn : ¬ Connectivity.Disconnected D) {d : G} (hd : d ∈ D) {E : Set G}
    (hE : IsMaxOrbit D d E) {β : Set G}
    (hβ : β ∈ Dalpha D (normSet D E \ E)) : β ⊆ E := by
  have hreach : ∀ a ∈ D, ∀ b ∈ D, Reach D a b := by
    intro a ha b hb
    by_contra hab
    exact hconn ⟨a, ha, b, hb, hab⟩
  set α : Set G := normSet D E \ E with hα
  have hmax : IsMaxBlock D α := isMaxBlock_normSet_diff hS hreach hd hE
  have hblock : IsBlock D α := IsMaxBlock.isBlock hmax
  have hdα : d ∈ α := OddLocal.self_mem_F hS.normal hd hE
  obtain ⟨hclass, -, hne, hcomm⟩ := mem_Dalpha_iff.mp hβ
  intro b hb
  have hbD : b ∈ D := hβ.2.1 hb
  have hbd : Commute b d := (hcomm d hdα b hb).symm
  have hbnorm : b ∈ normSet D E := OddLocal.mem_normSet_of_commute hS.normal hE hbD hbd
  by_cases hbE : b ∈ E
  · exact hbE
  · exfalso
    have hbα : b ∈ α := ⟨hbnorm, hbE⟩
    have hdisj : Disjoint α β := by
      obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hclass
      rw [hg]
      by_cases hgN : g ∈ Subgroup.normalizer α
      · exact absurd (hg.trans (Subgroup.mem_normalizer_iff_conj_image_eq.mp hgN)) hne
      · exact hblock.disjoint_conj hgN
    exact (Set.disjoint_left.mp hdisj hbα) hb

theorem DalphaStar_eq_maxOrbit [Finite G] {D : Set G} (hS : Setup G D)
    (hconn : ¬ Connectivity.Disconnected D) {d : G} (hd : d ∈ D) {E : Set G}
    (hE : IsMaxOrbit D d E) :
    DalphaStar D (normSet D E \ E) = E := by
  have hreach : ∀ a ∈ D, ∀ b ∈ D, Reach D a b := by
    intro a ha b hb
    by_contra hab
    exact hconn ⟨a, ha, b, hb, hab⟩
  set α : Set G := normSet D E \ E with hα
  have hmax : IsMaxBlock D α := isMaxBlock_normSet_diff hS hreach hd hE
  have hblock : IsBlock D α := IsMaxBlock.isBlock hmax
  have hdα : d ∈ α := OddLocal.self_mem_F hS.normal hd hE
  apply Set.Subset.antisymm
  · rintro x ⟨β, hβ, hxβ⟩
    exact Dalpha_subset_maxOrbit hS hconn hd hE hβ hxβ
  · intro e he
    have heD : e ∈ D := (OddLocal.subset_commSet hS.normal hE he).1
    obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj hd heD)
    have heα : e ∉ α := fun h => h.2 he
    have hB : e ∈ (fun x => g * x * g⁻¹) '' α := ⟨d, hdα, hg⟩
    have himgne : (fun x => g * x * g⁻¹) '' α ≠ α := by
      intro himg
      exact heα (himg ▸ hB)
    have hcomm : ∀ a ∈ α, ∀ b ∈ (fun x => g * x * g⁻¹) '' α, Commute a b :=
      commute_block_of_mem_apply hS.normal hS.oddT hblock himgne hdα hB
        (OddLocal.subset_commSet hS.normal hE he).2.1.symm
    refine ⟨(fun x => g * x * g⁻¹) '' α, ?_, hB⟩
    refine ⟨mem_blockClass_iff.mpr ⟨g, rfl⟩, ?_, himgne, hcomm⟩
    rintro b ⟨a, ha, rfl⟩
    exact hS.normal g a (hmax.2.1 ha)

theorem normalizer_transitive_Dalpha_of_isMaxOrbit [Finite G] {D : Set G} (hS : Setup G D)
    (hconn : ¬ Connectivity.Disconnected D) {d : G} (hd : d ∈ D) {E : Set G}
    (hE : IsMaxOrbit D d E) :
    ∀ β ∈ Dalpha D (normSet D E \ E), ∀ γ ∈ Dalpha D (normSet D E \ E),
      ∃ g ∈ Subgroup.normalizer (normSet D E \ E), (fun x => g * x * g⁻¹) '' β = γ := by
  have hreach : ∀ a ∈ D, ∀ b ∈ D, Reach D a b := by
    intro a ha b hb
    by_contra hab
    exact hconn ⟨a, ha, b, hb, hab⟩
  set α : Set G := normSet D E \ E with hα
  have hmax : IsMaxBlock D α := isMaxBlock_normSet_diff hS hreach hd hE
  have hblock : IsBlock D α := IsMaxBlock.isBlock hmax
  intro β hβ γ hγ
  have hβE : β ⊆ E := Dalpha_subset_maxOrbit hS hconn hd hE hβ
  have hγE : γ ⊆ E := Dalpha_subset_maxOrbit hS hconn hd hE hγ
  have hβne : β.Nonempty := by
    obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβ.1
    rw [hg]
    exact hblock.nonempty.image _
  have hγne : γ.Nonempty := by
    obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hγ.1
    rw [hg]
    exact hblock.nonempty.image _
  obtain ⟨b, hbβ⟩ := hβne
  obtain ⟨c, hcγ⟩ := hγne
  have hbE : b ∈ E := hβE hbβ
  have hcE : c ∈ E := hγE hcγ
  obtain ⟨k, hk, hkc⟩ := OddLocal.orbitGen hS hE hbE c hcE
  have hkNE : k ∈ Subgroup.normalizer E :=
    OddLocal.closure_commSet_le_normalizer hE
      (Subgroup.closure_mono (fun _ hx => OddLocal.subset_commSet hS.normal hE hx) hk)
  have hkNα : k ∈ Subgroup.normalizer α := OddLocal.mem_normalizer_diff hS.normal hkNE
  have himageα : (fun x => k * x * k⁻¹) '' α = α :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp hkNα
  have hβk : (fun x => k * x * k⁻¹) '' β ∈ Dalpha D α := by
    have h := Dalpha.conj hS.normal hβ k
    rwa [himageα] at h
  have hinter : ((fun x => k * x * k⁻¹) '' β ∩ γ).Nonempty :=
    ⟨c, ⟨b, hbβ, hkc.symm⟩, hcγ⟩
  refine ⟨k, hkNα, ?_⟩
  exact eq_of_mem_of_mem_blockClass hblock hβk.1 hγ.1 hinter

theorem Halpha_transitive_DalphaStar_of_isMaxOrbit [Finite G] {D : Set G} (hS : Setup G D)
    (hconn : ¬ Connectivity.Disconnected D) {d : G} (hd : d ∈ D) {E : Set G}
    (hE : IsMaxOrbit D d E) :
    ∀ x ∈ DalphaStar D (normSet D E \ E), ∀ y ∈ DalphaStar D (normSet D E \ E),
      ∃ h ∈ Halpha D (normSet D E \ E), h * x * h⁻¹ = y := by
  have hEq : DalphaStar D (normSet D E \ E) = E :=
    DalphaStar_eq_maxOrbit hS hconn hd hE
  intro x hx y hy
  have hxE : x ∈ E := by rwa [hEq] at hx
  have hyE : y ∈ E := by rwa [hEq] at hy
  obtain ⟨k, hk, hky⟩ := OddLocal.orbitGen hS hE hxE y hyE
  exact ⟨k, by simpa [Halpha, hEq] using hk, hky.symm⟩

end CFSG.OddTranspositions

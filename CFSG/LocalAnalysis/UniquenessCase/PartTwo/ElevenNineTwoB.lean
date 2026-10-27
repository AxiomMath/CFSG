module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem commutator_mem_pCoreOf_of_mem_OInf {Y : Subgroup G} (hY : F11.O2E Y = Y) {n y : G}
    (hn : n ∈ OInf Y) (hy : y ∈ Y) : n * y * n⁻¹ * y⁻¹ ∈ pCoreOf 2 Y := by
  set π : ↥Y →* Bar2 Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hlay : CFSG.layer (Bar2 Y) = ⊤ := by
    have h1 : ((rankThreeLayer (⊤ : Subgroup (Bar2 Y))).comap π) = ⊤ := by
      apply Subgroup.map_injective Y.subtype_injective
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact hY
    have h2 : rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ := by
      rw [eq_top_iff]
      intro a _
      obtain ⟨b, rfl⟩ := hπs a
      have : b ∈ (rankThreeLayer (⊤ : Subgroup (Bar2 Y))).comap π := by rw [h1]; trivial
      exact this
    rw [uc22p22u_layer_eq_rankThreeLayer_top, h2]
  haveI : (CFSG.solvableRadical ↥Y).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  haveI : Group.IsSolvable (CFSG.solvableRadical ↥Y) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable
  set S : Subgroup (Bar2 Y) := (CFSG.solvableRadical ↥Y).map π with hS
  haveI hSn : S.Normal := Subgroup.Normal.map inferInstance π hπs
  haveI hSs : Group.IsSolvable S := by
    let f : ↥(CFSG.solvableRadical ↥Y) →* ↥S :=
      (π.comp (CFSG.solvableRadical ↥Y).subtype).codRestrict S (fun x => ⟨x, x.2, rfl⟩)
    have hf : Function.Surjective f := by
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
    exact Group.isSolvable_of_surjective hf
  have hcent := (CFSG.LocalCores.component_solvable_centralizer hSs hSn.isSubnormal).2
  rw [hlay] at hcent
  have hSc : ∀ s ∈ S, ∀ a : Bar2 Y, ⁅a, s⁆ = 1 := fun s hs a => by
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) hs
    rw [hcent] at this
    exact this
  obtain ⟨n', hn', rfl⟩ := hn
  have h1 : π ⁅n', (⟨y, hy⟩ : ↥Y)⁆ = 1 := by
    rw [map_commutatorElement, ← commutatorElement_inv, inv_eq_one]
    exact hSc _ ⟨n', hn', rfl⟩ _
  have h2 : ⁅n', (⟨y, hy⟩ : ↥Y)⁆ ∈ CFSG.pCore 2 ↥Y := (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨_, h2, by simp [commutatorElement_def]⟩

theorem isQuasisimple_bar2_of_ker_commutes {K L : Type} [Group K] [Finite K] [Group L]
    (hperf : commutator K = ⊤) (g : K →* L) (hg : Function.Surjective g)
    (hL : CFSG.Open.IsQuasisimple L) (hcore : CFSG.pCore 2 K ≤ g.ker)
    (hcomm : ∀ k ∈ g.ker, ∀ k' : K, ⁅k, k'⁆ ∈ CFSG.pCore 2 K) :
    CFSG.Open.IsQuasisimple (K ⧸ CFSG.pCore 2 K) := by
  haveI : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  let gb : K ⧸ CFSG.pCore 2 K →* L := QuotientGroup.lift (CFSG.pCore 2 K) g hcore
  have hgb : Function.Surjective gb := fun l => by
    obtain ⟨k, rfl⟩ := hg l
    exact ⟨QuotientGroup.mk k, rfl⟩
  haveI : Group.IsPerfect K := ⟨hperf⟩
  haveI : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := inferInstance
  have hker : gb.ker ≤ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have hk : k ∈ g.ker := hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 K)) ⁅k, k'⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hcomm k hk k')
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hQ : CFSG.IsQuasisimple L := (CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hL
  have hP : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective inferInstance gb hgb hker).2 hQ
  exact (CFSG.Quasithin.A3.isQuasisimple_iff_open).1 hP

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

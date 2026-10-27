module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem normal_of_generalizedFitting {L : Subgroup G} (hLF : L = CFSG.generalizedFitting G) :
    L.Normal := by
  rw [hLF]
  exact (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2

theorem index_dvd_card_outer {L : Subgroup G} (hLF : L = CFSG.generalizedFitting G)
    (hLq : CFSG.IsQuasisimple ↥L) :
    L.index ∣ Nat.card (Outer (↥L ⧸ Subgroup.center ↥L)) := by
  haveI : L.Normal := normal_of_generalizedFitting hLF
  haveI : Group.IsPerfect ↥L := hLq.1
  let π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center ↥L := QuotientGroup.ker_mk' _
  have hCL : Subgroup.centralizer (L : Set G) ≤ L := by
    rw [hLF]
    intro g hg
    exact CFSG.centralizer_generalizedFitting_le G hg
  have h1 := CentralCover.comap_inner_fullAction π hπ hker hCL
  have h2 : L.index = (OuterAutomorphisms.inner (↥L ⧸ Subgroup.center ↥L)).relIndex
      (CentralCover.fullAction π hπ hker).range := by
    have h3 := Subgroup.index_comap (OuterAutomorphisms.inner (↥L ⧸ Subgroup.center ↥L))
      (CentralCover.fullAction π hπ hker)
    rw [h1] at h3
    exact h3
  rw [h2]
  refine (Subgroup.relIndex_dvd_index_of_normal _ _).trans ?_
  exact dvd_of_eq (Subgroup.index_eq_card _)

theorem sup_eq_top_of_index_le_two {L T : Subgroup G} [L.Normal] (hT : IsSylowIn 2 T ⊤)
    (h : L.index ≤ 2) : L ⊔ T = ⊤ := by
  have hpos : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : L.index = 1 ∨ L.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    rw [h1]; exact top_sup_eq T
  ·
    have hTL : ¬ T ≤ L := by
      intro hle
      apply hT.not_dvd_relIndex
      rw [← Subgroup.relIndex_mul_relIndex T L ⊤ hle le_top, Subgroup.relIndex_top_right, h2]
      exact Dvd.intro_left _ rfl
    have hdvd : (L ⊔ T).index ∣ L.index := Subgroup.index_dvd_of_le le_sup_left
    have hne : (L ⊔ T).index ≠ 2 := by
      intro h2'
      have hm := Subgroup.relIndex_mul_index (H := L) (K := L ⊔ T) le_sup_left
      rw [h2, h2'] at hm
      have h1' : L.relIndex (L ⊔ T) = 1 := by omega
      rw [Subgroup.relIndex_eq_one] at h1'
      exact hTL (le_sup_right.trans h1')
    have : (L ⊔ T).index = 1 := by
      rw [h2] at hdvd
      have hle : (L ⊔ T).index ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hp : (L ⊔ T).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    exact Subgroup.index_eq_one.mp this


theorem card_outer_le_of_card_mulAut_le {X : Type*} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) {c : ℕ} (hA : Nat.card (MulAut X) ≤ c * Nat.card X) :
    Nat.card (Outer X) ≤ c := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    refine (MonoidHom.ker_eq_bot_iff _).mp ((Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_)
    have hcen : g ∈ Subgroup.center X := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have h1 := congrArg (fun φ : MulAut X => φ y) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = (g * y * g⁻¹) * g := by rw [h1]
        _ = g * y := by group
    rwa [hZ, Subgroup.mem_bot] at hcen
  have hinn : Nat.card (OuterAutomorphisms.inner X) = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx := (OuterAutomorphisms.inner X).index_mul_card
  rw [hinn] at hidx
  have hpos : 0 < Nat.card X := Nat.card_pos
  have h1 : (OuterAutomorphisms.inner X).index * Nat.card X ≤ c * Nat.card X := hidx ▸ hA
  exact Nat.le_of_mul_le_mul_right h1 hpos

theorem card_outer_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (Outer X) = Nat.card (Outer Y) :=
  Nat.card_congr (equivalence e).toEquiv

section M12


theorem index_le_two_of_M12 {L : Subgroup G} (hLF : L = CFSG.generalizedFitting G)
    (hLq : CFSG.IsQuasisimple ↥L) (h : IsSporadic .M12 (↥L ⧸ Subgroup.center ↥L)) :
    L.index ≤ 2 := by
  obtain ⟨e⟩ := h
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := e
  have h1 := index_dvd_card_outer hLF hLq
  rw [card_outer_eq_of_mulEquiv e', M12Cover.card_outer] at h1
  exact Nat.le_of_dvd (by norm_num) h1

end M12

section M22


theorem index_le_two_of_M22 {L : Subgroup G} (hLF : L = CFSG.generalizedFitting G)
    (hLq : CFSG.IsQuasisimple ↥L) (h : IsSporadic .M22 (↥L ⧸ Subgroup.center ↥L)) :
    L.index ≤ 2 := by
  obtain ⟨e⟩ := h
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  have h1 := index_dvd_card_outer hLF hLq
  rw [card_outer_eq_of_mulEquiv e'] at h1
  have h2 : Nat.card (Outer ↥CFSG.Blueprint.NativeSporadic.M22) ≤ 2 :=
    card_outer_le_of_card_mulAut_le CFSG.Sporadic.Schreier.m22_center_eq_bot'
      CFSG.Sporadic.Schreier.m22_mulAut_card
  exact (Nat.le_of_dvd Nat.card_pos h1).trans h2

end M22

section M24


theorem index_eq_one_of_M24 {L : Subgroup G} (hLF : L = CFSG.generalizedFitting G)
    (hLq : CFSG.IsQuasisimple ↥L) (h : IsSporadic .M24 (↥L ⧸ Subgroup.center ↥L)) :
    L.index = 1 := by
  obtain ⟨e⟩ := h
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* ↥CFSG.Blueprint.NativeSporadic.M24 := e
  have h1 := index_dvd_card_outer hLF hLq
  rw [card_outer_eq_of_mulEquiv e'] at h1
  have h2 : Nat.card (Outer ↥CFSG.Blueprint.NativeSporadic.M24) ≤ 1 :=
    card_outer_le_of_card_mulAut_le (c := 1) CFSG.Sporadic.Schreier.m24_center_eq_bot'
      (by simpa using CFSG.Sporadic.Schreier.m24_mulAut_card)
  have := (Nat.le_of_dvd Nat.card_pos h1).trans h2
  have hp : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

end M24

end CFSG.Quasithin.RonanE43

module

public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.GH74.Generic.S3.LyDiagC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem funSet_mono_of_le {X : Type} [Group X] [Finite X]
    {𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop}
    {S S' Kb : Subgroup X} (hSS' : S ≤ S') (hS' : IsPGroup 2 S')
    (h : Kb ∈ FunSet 𝔉 X S) : Kb ∈ FunSet 𝔉 X S' := by
  rw [FunSet] at h ⊢
  obtain ⟨hfund, hSyl⟩ := h
  refine ⟨hfund, ?_⟩
  have hle : S ⊓ Kb ≤ S' ⊓ Kb := inf_le_inf_right Kb hSS'
  have hS'Kb : IsPGroup 2 ↥(S' ⊓ Kb) := hS'.to_le inf_le_left
  have heq := hSyl.eq_of_le hle inf_le_right hS'Kb
  rwa [heq]


theorem funSet_map_mulEquiv {q : ℕ} {X : Type} [Group X] [Finite X] (α : X ≃* X)
    {S Kb : Subgroup X} (h : Kb ∈ FunSet (fundPred q) X S) :
    Kb.map α.toMonoidHom ∈ FunSet (fundPred q) X (S.map α.toMonoidHom) := by
  rw [FunSet] at h ⊢
  obtain ⟨hfund, hSyl⟩ := h
  refine ⟨isFundamentalOver_map_mulEquiv α hfund, ?_⟩
  rw [← Subgroup.map_inf S Kb α.toMonoidHom α.injective]
  obtain ⟨Q, hQ⟩ := hSyl
  rw [← hQ]
  refine ⟨Q.mapSurjective (α.toMonoidHom.subgroupMap_surjective Kb), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isFundamentalOver_quasisimple_shape {q : ℕ} (hq : 3 < q) {X : Type} [Group X]
    [Finite X] {Kb : Subgroup X} (h : IsFundamentalOver q Kb) :
    CFSG.IsQuasisimple ↥Kb ∧ ∃ q' : ℕ, IsL2Over17 (↥Kb ⧸ Subgroup.center ↥Kb) q' ∧
      (q' = q ∨ q' = q ^ 3) ∧ 3 < q' := by
  obtain ⟨t, n, p, e, hp, hp2, hqeq, hfund, hadm, ψ, hsurj, hker, R, hR, rfl⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hq5 : 5 ≤ p ^ e := by
    have h3 : 3 < p ^ e := by rw [← hqeq]; exact hq
    obtain ⟨k, hk⟩ := hodd
    omega
  have hmain :=
    CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      (p := p) hp2 hfund hadm hR
  have hRqs : CFSG.IsQuasisimple ↥R := by
    rcases hmain with h | ⟨rfl, h⟩
    · obtain ⟨eR⟩ := h
      exact CFSG.IsQuasisimple.of_mulEquiv eR
        (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr
          (CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two (by
            rw [GaloisField.card p e (by omega)]; omega)))
    · obtain ⟨eR⟩ := h
      exact CFSG.IsQuasisimple.of_mulEquiv eR
        (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr
          (CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two (by
            rw [GaloisField.card p (3 * e) (by omega)]
            have hle' : p ^ e ≤ p ^ (3 * e) := Nat.pow_le_pow_right hp.pos (by omega)
            omega)))
  have hnot : ¬ R ≤ ψ.ker := by
    intro hle
    have hnt : Nontrivial ↥R := CFSG.LocalCores.isQuasisimple_nontrivial hRqs
    have hperf : Group.IsPerfect ↥R := hRqs.1
    refine (Group.IsPerfect.not_isMulCommutative ↥R) ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    have ha : ((a : ↥R) : (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp).K) ∈
        Subgroup.center (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp).K :=
      hker (hle a.2)
    exact (Subgroup.mem_center_iff.mp ha (b : _)).symm
  have hKb_qs : CFSG.IsQuasisimple ↥(R.map ψ) :=
    CFSG.LocalCores.isQuasisimple_map hRqs ψ hnot
  have hkerR : (ψ.subgroupMap R).ker ≤ Subgroup.center ↥R := by
    rw [Subgroup.ker_subgroupMap]
    intro x hx
    have hxZ : (x : (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp).K) ∈
        Subgroup.center (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp).K := hker hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxZ (y : _)
  let eZ := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple (φ := ψ.subgroupMap R)
    hRqs (ψ.subgroupMap_surjective R) hkerR
  rcases hmain with h | ⟨rfl, h⟩
  · obtain ⟨eR⟩ := h
    have hcard : Nat.card (GaloisField p e) = p ^ e :=
      GaloisField.card p e (by omega)
    have hLie : LieModel (↥R ⧸ Subgroup.center ↥R) .PSL 2 p e :=
      CFSG.GH74.Generic.S3.lieModel_psl2_quot hp hp2 hq5 hcard
        (eR.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
          (GaloisField p e)))
    have hLieKb : LieModel (↥(R.map ψ) ⧸ Subgroup.center ↥(R.map ψ)) .PSL 2 p e :=
      hLie.of_mulEquiv eZ
    refine ⟨hKb_qs, p ^ e, ⟨p, e, hp, hp2, rfl, he, hLieKb⟩, Or.inl ?_, ?_⟩
    · exact hqeq.symm
    · rw [← hqeq]; exact hq
  · obtain ⟨eR⟩ := h
    have hcard : Nat.card (GaloisField p (3 * e)) = p ^ (3 * e) :=
      GaloisField.card p (3 * e) (by omega)
    have h5L : 5 ≤ p ^ (3 * e) := by
      have hle' : p ^ e ≤ p ^ (3 * e) := Nat.pow_le_pow_right hp.pos (by omega)
      omega
    have hLie : LieModel (↥R ⧸ Subgroup.center ↥R) .PSL 2 p (3 * e) :=
      CFSG.GH74.Generic.S3.lieModel_psl2_quot hp hp2 h5L hcard
        (eR.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
          (GaloisField p (3 * e))))
    have hLieKb : LieModel (↥(R.map ψ) ⧸ Subgroup.center ↥(R.map ψ)) .PSL 2 p (3 * e) :=
      hLie.of_mulEquiv eZ
    have hq3 : p ^ (3 * e) = q ^ 3 := by
      rw [hqeq, show 3 * e = e * 3 by omega, pow_mul]
    refine ⟨hKb_qs, p ^ (3 * e), ⟨p, 3 * e, hp, hp2, rfl, by omega, hLieKb⟩,
      Or.inr hq3, ?_⟩
    have hle' : p ^ e ≤ p ^ (3 * e) := Nat.pow_le_pow_right hp.pos (by omega)
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

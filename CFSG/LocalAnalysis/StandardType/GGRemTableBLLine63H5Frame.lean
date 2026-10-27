module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5ClassFrame
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Cover

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical2 CFSG.RankThree.Classical
  CFSG.StandardType.LineU CFSG.Assembly

variable {K : Type} [Field K] {n : ℕ} {G : Type} [Group G]

theorem le_range_of_frame [Finite K] [Finite G] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) (φ : ↥(unitarySU 2 n K 6) →* G)
    (hφ : ∀ s, φ s = 1 → LargeEvenProjMk (unitarySU 2 n K 6) s = 1)
    {B : Subgroup G} (hBcard : Nat.card B ≤ 3 ^ 4)
    (hSC : ∀ g ∈ Subgroup.centralizer (B : Set G), g ^ 3 = 1 → g ∈ B)
    {P : GL (Fin 6) K}
    (hP : P ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hKd
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (hdiag : ∀ b ∈ B, ∃ M, ActsAs φ b M ∧
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    ∀ g ∈ B, ∃ s, φ s = g := by
  classical
  obtain ⟨T, hTab, hTcard, hTdiag⟩ := exists_torusFive hKd hpq
  set c := TableBUE.conjSU hKd P hP with hc
  set Φ : ↥T →* G :=
    φ.comp ((c.symm : ↥(unitarySU 2 n K 6) ≃* ↥(unitarySU 2 n K 6)).toMonoidHom.comp
      T.subtype) with hΦ
  have hΦe : ∀ e : T, Φ e = φ (c.symm (e : ↥(unitarySU 2 n K 6))) := fun e => rfl
  have hΦB : ∀ e : T, Φ e ∈ B := by
    intro e
    rw [hΦe]
    apply hSC
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨M, hM, hMd⟩ := hdiag b hb
      obtain ⟨hMN, hMact⟩ := hM
      obtain ⟨σ, hσ⟩ := TableBUE.exists_diagHom_of_isDiag hMd
      obtain ⟨t, ht⟩ := hTdiag (e : ↥(unitarySU 2 n K 6)) e.2
      have hcs : conjN M hMN (c.symm (e : ↥(unitarySU 2 n K 6))) =
          c.symm (e : ↥(unitarySU 2 n K 6)) := by
        apply Subtype.ext
        rw [coe_conjN]
        show M * (P * ((e : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) * P⁻¹) * M⁻¹ =
          P * ((e : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) * P⁻¹
        have hM' : M = P * diagHom 6 σ * P⁻¹ := by rw [← hσ]; group
        have hcomm := (diagHom_commute σ t).eq
        rw [ht, hM']
        calc P * diagHom 6 σ * P⁻¹ * (P * diagHom 6 t * P⁻¹) * (P * diagHom 6 σ * P⁻¹)⁻¹
            = P * (diagHom 6 σ * diagHom 6 t * (diagHom 6 σ)⁻¹) * P⁻¹ := by group
          _ = P * diagHom 6 t * P⁻¹ := by rw [hcomm]; group
      have h1 := hMact (c.symm (e : ↥(unitarySU 2 n K 6)))
      rw [hcs] at h1
      calc b * φ (c.symm (e : ↥(unitarySU 2 n K 6)))
          = b * φ (c.symm (e : ↥(unitarySU 2 n K 6))) * b⁻¹ * b := by group
        _ = φ (c.symm (e : ↥(unitarySU 2 n K 6))) * b := by rw [h1]
    · rw [← map_pow, ← map_pow, hTab.2 (e : ↥(unitarySU 2 n K 6)) e.2, map_one, map_one]
  have hker : Nat.card Φ.ker ≤ 3 := by
    have hex : ∀ e : Φ.ker, ∃ z : rootsOfUnity 3 K,
        (((e : ↥T) : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) =
          GeneralLinearGroup.scalar (Fin 6) (z : Kˣ) := by
      intro e
      have h1 : φ (c.symm ((e : ↥T) : ↥(unitarySU 2 n K 6))) = 1 := by
        rw [← hΦe]
        exact e.2
      obtain ⟨z, hz3, hz⟩ := exists_scalar_of_proj_eq_one hKd hpq (hφ _ h1)
      refine ⟨⟨z, (mem_rootsOfUnity _ _).mpr hz3⟩, ?_⟩
      have h2 : ((c.symm ((e : ↥T) : ↥(unitarySU 2 n K 6)) : ↥(unitarySU 2 n K 6)) :
          GL (Fin 6) K) = P * (((e : ↥T) : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) * P⁻¹ := rfl
      rw [h2] at hz
      have h3 : (((e : ↥T) : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) =
          P⁻¹ * (GeneralLinearGroup.scalar (Fin 6) z) * P := by
        rw [← hz]
        group
      show (((e : ↥T) : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) =
        GeneralLinearGroup.scalar (Fin 6) z
      rw [h3, ← (TypeA.PGLTor.commute_scalar z P⁻¹).eq]
      group
    choose f hf using hex
    have hfinj : Function.Injective f := by
      intro e e' h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rw [hf e, hf e', h]
    exact (Nat.card_le_card_of_injective f hfinj).trans (card_rootsOfUnity K 3)
  have hcard := CFSG.StandardType.TableB.card_range_mul_card_ker Φ
  rw [hTcard] at hcard
  have hrange : 3 ^ 4 ≤ Nat.card Φ.range := by
    have h1 : Nat.card Φ.range * Nat.card Φ.ker ≤ Nat.card Φ.range * 3 :=
      Nat.mul_le_mul_left _ hker
    rw [hcard] at h1
    omega
  have hle : Φ.range ≤ B := by
    rintro _ ⟨e, rfl⟩
    exact hΦB e
  have heq : Φ.range = B := Subgroup.eq_of_le_of_card_ge hle (hBcard.trans hrange)
  intro g hg
  rw [← heq] at hg
  obtain ⟨e, rfl⟩ := hg
  exact ⟨c.symm (e : ↥(unitarySU 2 n K 6)), rfl⟩

end CFSG.StandardType.Line63.H5

end

module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Two

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType
  CFSG.StandardType.LineU
open scoped commutatorElement

private lemma conjProj_one_apply {K : Type} [Field K] {n d : ℕ} (h : UnitaryFieldData 2 n K)
    (hP : (1 : GL (Fin d) K) ∈ primeFormUnitary h (idGram K d))
    (r : LargeEvenProj (unitarySU 2 n K d)) : conjProj h 1 hP r = r := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ r
  rw [show (QuotientGroup.mk' _ s : LargeEvenProj (unitarySU 2 n K d)) =
    LargeEvenProjMk (unitarySU 2 n K d) s from rfl, conjProj_mk]
  congr 1
  apply Subtype.ext
  rw [coe_conjSU]
  simp

theorem exists_model {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K] [Finite K] {n : ℕ}
    (hKd : UnitaryFieldData 2 n K) {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hperfSU : commutator (unitarySU 2 n K 6) = ⊤) {P : GL (Fin 6) K}
    (hP : P ∈ primeFormUnitary hKd (idGram K 6))
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s) :
    ∃ φ : ↥(unitarySU 2 n K 6) →* L', Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 n K 6), φ g = 1 →
        ∃ c : K, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal (fun _ => c)) ∧
      (∀ (a : MulAut L') (M D : GL (Fin 6) K)
        (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
        (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
        D = P⁻¹ * M * P →
        (∀ l, TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩ (ψ l) = ψ (a l)) →
        ∀ s, a (φ s) = φ (LineU.conjN D hD s)) ∧
      (P = 1 → ∀ s, ψ (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s) := by
  set θ := TableBUE.conjProj hKd P hP with hθ
  set ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6) := θ.toMonoidHom.comp ψ with hψ''
  have hψ''s : Function.Surjective ψ'' := θ.surjective.comp hψ
  have hker'' : ψ''.ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : θ (ψ x) = θ 1 := by rw [map_one]; exact hx
    exact θ.injective hx'
  have hkerEq : ψ''.ker = ψ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, hψ'', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact EmbeddingLike.map_eq_one_iff
  obtain ⟨φ, hφ⟩ := hcov' ψ'' hψ''s hkerEq
  have hφs : Function.Surjective φ := by
    have hcomm : ⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ ≤ φ.range := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, hs⟩ : ∃ s : ↥(unitarySU 2 n K 6),
          ψ'' x = LargeEvenProjMk (unitarySU 2 n K 6) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ'' x)
        exact ⟨s0, hs0.symm⟩
      obtain ⟨s', hs'⟩ : ∃ s : ↥(unitarySU 2 n K 6),
          ψ'' y = LargeEvenProjMk (unitarySU 2 n K 6) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ'' y)
        exact ⟨s0, hs0.symm⟩
      have hz : x * (φ s)⁻¹ ∈ Subgroup.center L' := by
        apply hker''
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, ← hs, mul_inv_cancel]
      have hz' : y * (φ s')⁻¹ ∈ Subgroup.center L' := by
        apply hker''
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, ← hs', mul_inv_cancel]
      have hx : x = (x * (φ s)⁻¹) * φ s := by group
      have hy : y = (y * (φ s')⁻¹) * φ s' := by group
      rw [hx, hy, comm_mul_central hz hz']
      exact ⟨⁅s, s'⁆, by rw [map_commutatorElement]⟩
    have htop : (⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ : Subgroup L') = ⊤ := hperf
    rw [htop] at hcomm
    intro l
    obtain ⟨s, hs⟩ := hcomm (Subgroup.mem_top l)
    exact ⟨s, hs⟩
  refine ⟨φ, hφs, ?_, ?_, ?_⟩
  ·
    intro g hg
    have h1 : LargeEvenProjMk (unitarySU 2 n K 6) g = 1 := by
      rw [← hφ g, hg, map_one]
    have h2 : g ∈ (LargeEvenScalars (Fin 6) K).subgroupOf (unitarySU 2 n K 6) :=
      (QuotientGroup.eq_one_iff g).mp h1
    rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at h2
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp h2
    refine ⟨(c : K), ?_⟩
    rw [← hc]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    · simp [Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hij]
  ·
    intro a M D hM hD hDeq hc
    subst hDeq
    intro s
    have htw : ∀ l : L', ψ'' (a l) =
        TableB.projConj (unitarySU 2 n K 6) ⟨P⁻¹ * M * P, hD⟩ (ψ'' l) := by
      intro l
      have e1 : ψ'' (a l) =
          θ (TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩ (ψ l)) := by
        rw [hψ'', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hc l]
      rw [e1]
      exact TableBUD.conjProj_projConj hKd P hP ⟨M, hM⟩ hD (ψ l)
    have hfun : (MulEquiv.toMonoidHom a).comp φ =
        φ.comp (conjNHom (P⁻¹ * M * P) hD) := by
      apply CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hperfSU
      intro s
      apply hker''
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_conjNHom]
      rw [htw (φ s), hφ s, projConj_mk_eq _ hD s, ← hφ (conjN _ hD s), inv_mul_cancel]
    have := congrArg (fun f => f s) hfun
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_conjNHom] using this
  ·
    rintro rfl s
    have hθid : ∀ r, θ r = r := by
      intro r
      rw [hθ]
      exact conjProj_one_apply hKd hP r
    have hψφ : ψ'' (φ s) = ψ (φ s) := by
      rw [hψ'', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact hθid (ψ (φ s))
    rw [← hψφ, hφ s]

end CFSG.StandardType.UnitSixThreeKG

end

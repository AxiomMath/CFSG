module

public import CFSG.RankThree.PartOne.CTP.SU4EvenSU
public import CFSG.RankThree.PartOne.CTP.SU4EvenField

public section

namespace CFSG.RankThree.PartOne.CTP.SU4Even

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.Timmesfeld
open CFSG.LieType.Universal.Unitary.SUExtras (longRootHom_mem)
open CFSG.ClassicalInvolution.WeakCT.SU4 (mem_traceZero_of_eq_neg eq_neg_of_mem_traceZero'
  sl2_mem_of_tv)
open scoped Matrix MatrixGroups

section RootGroups

variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c)

theorem rootGroup_four_one_eq_longRoot_range :
    rootGroup σ hσ 4 (Pi.single 1 1) = (longRootHom σ (i := (1 : Fin 4)) (by decide)).range := by
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      exfalso
      revert hij hi hj hji hw
      fin_cases i <;> fin_cases j <;> decide
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      have hi1 : i = 1 := by
        revert hw
        fin_cases i <;> decide
      subst hi1
      exact le_rfl
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact longRootHom_mem hσ _ (by decide) c

theorem rootGroup_four_neg_one_eq_longRoot_range :
    rootGroup σ hσ 4 (-Pi.single 1 1) = (longRootHom σ (i := (2 : Fin 4)) (by decide)).range := by
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      exfalso
      revert hij hi hj hji hw
      fin_cases i <;> fin_cases j <;> decide
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      have hi1 : i = 2 := by
        revert hw
        fin_cases i <;> decide
      subst hi1
      exact le_rfl
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact longRootHom_mem hσ _ (by decide) c

end RootGroups

namespace KleinDataEven

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] [CharP F 2] {f : ℕ}
  [CharP K 2] [Finite K] {b c : F} (D : KleinDataEven F K (unitaryInvolution K 2 f) b c)
  (hF : Nat.card K = (2 ^ f) ^ 2) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hF hirr in
theorem range_PhiSUEven_eq_top : (D.PhiSUEven hirr).range = ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hD := isCTGroupDatum hF 4 (by norm_num) ζ hζ
  rw [eq_top_iff, ← hD.iSup_eq_top]
  refine iSup₂_le fun γ _ => ?_
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun _ => ?_
    rintro _ ⟨x, rfl⟩
    exact D.rootHom_mem_range_PhiSUEven hirr i j hij hi hj hji x
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun _ => ?_
    rintro _ ⟨x, rfl⟩
    exact D.longRootHom_mem_range_PhiSUEven hirr i hi x
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun _ => ?_
    exfalso
    revert hk
    fin_cases k <;> decide

include hirr in
theorem longRootHom_one_mem_map_lb (hi : (1 : Fin 4) ≠ Fin.rev 1)
    (x : Multiplicative (traceZero (unitaryInvolution K 2 f))) :
    longRootHom (unitaryInvolution K 2 f) hi x ∈
      (minusLongBlock b c).range.map (D.PhiSUEven hirr) := by
  have hc := eq_neg_of_mem_traceZero' (unitaryInvolution K 2 f) x.toAdd.2
  obtain ⟨r, hr⟩ := D.exists_algebraMap_eq_of_σ_eq (y := (x.toAdd : K) * D.δ)
    (by rw [map_mul, hc, D.σ_δ]; ring)
  refine ⟨minusLongBlock b c (tv 0 1 r), ⟨_, rfl⟩, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  rw [coe_PhiSUEven, minusLongBlock_tv01, D.PhiMon_long_e0f1, hr]
  show longRootMatrix (1 : Fin 4) (↑x.toAdd * D.δ * D.ε) = longRootMatrix (1 : Fin 4) ↑x.toAdd
  rw [mul_assoc, D.δ_mul_ε, mul_one]

include hirr in
theorem longRootHom_two_mem_map_lb (hi : (2 : Fin 4) ≠ Fin.rev 2)
    (x : Multiplicative (traceZero (unitaryInvolution K 2 f))) :
    longRootHom (unitaryInvolution K 2 f) hi x ∈
      (minusLongBlock b c).range.map (D.PhiSUEven hirr) := by
  have hc := eq_neg_of_mem_traceZero' (unitaryInvolution K 2 f) x.toAdd.2
  obtain ⟨r, hr⟩ := D.exists_algebraMap_eq_of_σ_eq (y := (x.toAdd : K) * D.ε)
    (by rw [map_mul, hc, D.σ_ε]; ring)
  refine ⟨minusLongBlock b c (tv 1 0 r), ⟨_, rfl⟩, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  rw [coe_PhiSUEven, minusLongBlock_tv10, D.PhiMon_long_e1f0, hr]
  show longRootMatrix (2 : Fin 4) (↑x.toAdd * D.ε * D.δ) = longRootMatrix (2 : Fin 4) ↑x.toAdd
  rw [mul_assoc, mul_comm D.ε, D.δ_mul_ε, mul_one]

include hF hirr in
theorem map_minusLongBlock_eq :
    (minusLongBlock b c).range.map (D.PhiSUEven hirr) =
      rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hF) 4 (Pi.single 1 1) ⊔
        rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hF) 4
          (-Pi.single 1 1) := by
  rw [rootGroup_four_one_eq_longRoot_range, rootGroup_four_neg_one_eq_longRoot_range]
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    refine sl2_mem_of_tv ((D.PhiSUEven hirr).comp (minusLongBlock b c))
      (H := (longRootHom (unitaryInvolution K 2 f) (i := (1 : Fin 4)) (by decide)).range ⊔
        (longRootHom (unitaryInvolution K 2 f) (i := (2 : Fin 4)) (by decide)).range)
      (fun x => ?_) (fun x => ?_) A
    · refine Subgroup.mem_sup_left ⟨Multiplicative.ofAdd ⟨algebraMap F K x * D.ε,
        mem_traceZero_of_eq_neg _ D.σ_ε_mul⟩, ?_⟩
      refine Subtype.ext (Units.ext ?_)
      rw [MonoidHom.comp_apply, minusLongBlock_tv01, coe_PhiSUEven, D.PhiMon_long_e0f1]
      rfl
    · refine Subgroup.mem_sup_right ⟨Multiplicative.ofAdd ⟨algebraMap F K x * D.δ,
        mem_traceZero_of_eq_neg _ D.σ_δ_mul⟩, ?_⟩
      refine Subtype.ext (Units.ext ?_)
      rw [MonoidHom.comp_apply, minusLongBlock_tv10, coe_PhiSUEven, D.PhiMon_long_e1f0]
      rfl
  · rintro _ ⟨x, rfl⟩
    exact D.longRootHom_one_mem_map_lb hirr _ x
  · rintro _ ⟨x, rfl⟩
    exact D.longRootHom_two_mem_map_lb hirr _ x


include hF hirr in
@[expose] noncomputable def phiSUEven :
    spinGroup (quadMinus 3 F b c) ≃* SU (unitaryInvolution K 2 f) 4 :=
  MulEquiv.ofBijective (D.PhiSUEven hirr)
    ⟨D.PhiSUEven_injective hirr, fun g => by
      have hg : g ∈ (D.PhiSUEven hirr).range := by
        rw [D.range_PhiSUEven_eq_top hF hirr]
        exact Subgroup.mem_top g
      exact hg⟩

include hF hirr in
theorem phiSUEven_apply (s : spinGroup (quadMinus 3 F b c)) :
    D.phiSUEven hF hirr s = D.PhiSUEven hirr s :=
  rfl

include hF hirr in
theorem map_minusLongBlock_phiSUEven :
    (minusLongBlock b c).range.map (D.phiSUEven hF hirr).toMonoidHom =
      rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hF) 4 (Pi.single 1 1) ⊔
        rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hF) 4
          (-Pi.single 1 1) :=
  D.map_minusLongBlock_eq hF hirr

end KleinDataEven

theorem exists_equiv_su_four_even {F K : Type} [Field F] [Finite F] [CharP F 2] [Field K]
    [Finite K] [CharP K 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ (_ : Algebra F K) (e : spinGroup (quadMinus 3 F b c) ≃* SU (unitaryInvolution K 2 f) 4),
      (minusLongBlock b c).range.map e.toMonoidHom =
        rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4 (Pi.single 1 1) ⊔
          rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4
            (-Pi.single 1 1) := by
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinDataEven hF hK hirr
  exact ⟨inst, D.phiSUEven hK hirr, D.map_minusLongBlock_eq hK hirr⟩

end CFSG.RankThree.PartOne.CTP.SU4Even

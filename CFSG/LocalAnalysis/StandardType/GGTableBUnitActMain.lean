module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActEnd
public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredDef
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActCore

public section

namespace CFSG.StandardType.UnitAct

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly TableB

variable {K : Type} [Field K] {n d p : ℕ}

theorem ggTableBActionSCr_unitary
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) :
    GGTableBActionSCr p (ggUnitaryTorusRank p d)
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  classical
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  refine ⟨hp2, fun L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc => ?_⟩
  have := Fact.mk hp
  have hrank : ggUnitaryTorusRank p d = d - 3 := by simp [ggUnitaryTorusRank, hpd]
  rw [hrank] at hr
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := card_ge_of_dvd hp hp2 hd hpd hnd hr h3
  have hdnd : (d, n) ≠ (6, 1) := by
    rintro ⟨rfl, rfl⟩
    have h3' : p ∣ 3 := by simpa using hpq
    exact hnd ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ := exists_diagModel hK hn hd hp hpq hpd
    (unitaryUniversalCover_holds n d K hK hd hdnd) hψ hker hperf hA hAI hcard
  have hM : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  have hd3 : 3 ≤ d := by omega
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  set H := Subgroup.closure (heartSetU φ p) with hH
  have hVA : heartSetU φ p ⊆ A := by
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_selfCent hsc hdiag hD hu
  have hHA : H ≤ A := (Subgroup.closure_le A).mpr hVA
  refine ⟨H, {x | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hM.field σ)}, hHA, ?_, ?_,
    weyl_W_prop hM.field hd3 hM.ker hAp hdiag, ?_, eq_one_of_perm_fixed hM hd3 hdiag, ?_, ?_, ?_,
    ?_⟩
  · intro hbot
    set i0 : Fin d := ⟨0, by omega⟩
    set i1 : Fin d := ⟨1, by omega⟩
    set i2 : Fin d := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have hi02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have hi12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    obtain ⟨D₁, hD₁⟩ := exists_diagSU hM.field hpq (u := TypeA.rootT ζ i0 i1)
      (fun k => TypeA.rootT_pow hζ.pow_eq_one i0 i1 k) (TypeA.prod_rootT hζ0 h01)
    have he₁ : MulAut.conj (φ D₁) ∈ H :=
      Subgroup.subset_closure ⟨D₁, _, hD₁, TypeA.rootT_pow hζ.pow_eq_one i0 i1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at he₁
    have h2 : ActsDiagU φ (MulAut.conj (φ D₁)) (fun _ => (1 : K)) := by
      rw [he₁]
      exact actsDiagU_one φ
    have h3' := (actsDiagU_conj (φ := φ) hD₁).ratio_eq hM.field hd3 hM.ker h2 i0 i2
    rw [TypeA.rootT_left, TypeA.rootT_other ζ (Ne.symm hi02) (Ne.symm hi12)] at h3'
    simp only [inv_one, mul_one] at h3'
    exact hζ1 h3'
  · intro w hw h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      exact Subgroup.subset_closure
        (conj_mem_heart_of_normalizes hM hK hp hp2 hpq hd hA hsc hdiag hw hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have e : MulAut.conj w * (x * y) * (MulAut.conj w)⁻¹ =
          (MulAut.conj w * x * (MulAut.conj w)⁻¹) * (MulAut.conj w * y * (MulAut.conj w)⁻¹) := by
        group
      rw [e]
      exact H.mul_mem hx hy
    | inv x _ hx =>
      have e : MulAut.conj w * x⁻¹ * (MulAut.conj w)⁻¹ =
          (MulAut.conj w * x * (MulAut.conj w)⁻¹)⁻¹ := by group
      rw [e]
      exact H.inv_mem hx
  · intro A' hA'A hA'ne hinv
    obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA'ne
    have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
    refine (Subgroup.closure_le A').mpr ?_
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_invariant hM hp hpq hd hA'A hsc hdiag hAp
      (fun σ a ha => hinv _ ⟨σ, rfl⟩ a ha) ha₀ ha₀1' hD hu
  · rintro x ⟨σ, rfl⟩ a ha
    exact conj_mul_inv_mem_heart hM hp hpq hd3 hAp hdiag σ ha
  · intro w hw
    exact exists_weyl_fix hM hK hp hp2 hpq (by omega) hA hsc hdiag hw
  · rintro x ⟨σ, rfl⟩
    exact perm_image_mem_closure hM.field φ σ
  · intro f hfH hfmul hfW
    exact heart_end_pow hM hp hp2 hpq hd hA hsc hdiag f hfH hfmul hfW

end CFSG.StandardType.UnitAct

namespace CFSG.StandardType

open CFSG.Assembly TableB LineU

theorem largeEvenLabelAll_unitDvd_action
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvdLabelNo63 p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTableBActionSCr p r R I := by
  obtain ⟨hn, hd5, hpd, hpq, h63, hdq⟩ := unitDvdLabel_arith hp hlab h
  obtain ⟨⟨ht, -, -, -⟩, -⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn hd5 hpd hpq h63 hdq
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', ggUnitaryTorusRank p (l + 1),
    ggTorusLift_unitary hK hn (by omega) hdq hp hpq,
    UnitAct.ggTableBActionSCr_unitary hK hn hd5 hp hpq hpd h63⟩⟩

section Results


theorem ggTableBActionInputOn_unitDvd_of_lid {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitDvdLabelNo63 p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBActionInputOn S :=
  ggTableBActionInputOn_of_labelsSCr hD
    fun _ _ hp hlab h => largeEvenLabelAll_unitDvd_action hp hlab (hS _ _ h)

theorem ggTableBActionInputOn_unitDvdCoprimeN_holds :
    GGTableBActionInputOn GGUnitDvdCoprimeNLabel :=
  ggTableBActionInputOn_unitDvd_of_lid (fun _ _ h => h.1) ggBstarInnerDiagLInputOn_unitDvd_coprimeN

theorem ggTableBActionInputOn_unitDvdNo63 (hF : GGBstarInnerDiagLInputOn GGUnitDvdFieldLabel) :
    GGTableBActionInputOn GGUnitDvdLabelNo63 :=
  ggTableBActionInputOn_unitDvd_of_lid (fun _ _ h => h) (ggBstarInnerDiagLInputOn_unitDvdNo63 hF)

theorem ggTableBActionInputOn_of_not_unitDvdCoprimeN {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab) :
    GGTableBActionInputOn S :=
  (ggTableBActionInputOn_unitDvdCoprimeN_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGUnitDvdCoprimeNLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBActionInputOn_of_not_unitDvdNo63 (hF : GGBstarInnerDiagLInputOn GGUnitDvdFieldLabel)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGUnitDvdLabelNo63 p lab) :
    GGTableBActionInputOn S :=
  ((ggTableBActionInputOn_unitDvdNo63 hF).or h).mono fun p lab hlab => by
    by_cases hl : GGUnitDvdLabelNo63 p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

end Results

end CFSG.StandardType

end

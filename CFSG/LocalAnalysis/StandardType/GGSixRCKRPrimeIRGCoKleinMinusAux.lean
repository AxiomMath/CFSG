module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.RankThree.PartOne.CTP.SU4EvenBridge
public import CFSG.RankThree.PartOne.CTP.SU4EvenField
public import CFSG.ClassicalInvolution.Models.TwistedPairs.SpinMinus
public import CFSG.LieType.Universal.Spin.Roots.TypeB
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSURoot
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSU

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.CurtisTits
open CFSG.LieType.Universal.Unitary.SUExtras (longRootHom_mem)
open CFSG.RankThree.PartOne.CTP.SU4Even CFSG.RankThree.PartOne.CTP.SU4Even.KleinDataEven
open CFSG.ClassicalInvolution.Models.TwistedPairs
open CFSG.ClassicalInvolution.WeakCT.SU4 (mem_traceZero_of_eq_neg eq_neg_of_mem_traceZero')
open scoped Matrix MatrixGroups

private theorem irgK2_exists_long_of_ggLongRoot_minus_three {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {γ : Fin 2 → ℤ}
    (hγ : GGLongRoot (minusDatum 3 hirr) γ) :
    ∃ (s t : Bool),
      toStdB 2 γ = Pi.single (0 : Fin 2) (boolSign s) +
        Pi.single (1 : Fin 2) (boolSign t) := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hγ
  obtain ⟨i, j, hij, s, t, hst⟩ := RootCentOmega.exists_long_weylAction w
    (by
      rcases exists_toStdB_eq_of_mem_roots 3 hγ₀ with h | ⟨k, s, hk⟩
      · exact h
      · exfalso
        set e : Fin (3 - 1) → ℤ :=
          Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1 with he
        have h01 : (⟨0, by omega⟩ : Fin (3 - 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
        have hδ := ofStdB_mem_rootsB (n := 3 - 1) (e := e)
          (Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, 1, 1, h01, Or.inl rfl, Or.inl rfl, rfl⟩)
        have h1 : @CFSG.LieType.Steinberg.ht (Fin (3 - 1)) _ (ofStdB (3 - 1) e) ≤
            @CFSG.LieType.Steinberg.ht (Fin (3 - 1)) _ γ₀ := hmax _ hδ
        have h2 := ht_of_toStdB_eq_add (n := 3 - 1) (toStdB_ofStdB (3 - 1) e)
        have h3 := ht_of_toStdB_eq_single (n := 3 - 1) hk
        have hk' := k.isLt
        cases s <;> simp [boolSign] at h1 h2 h3 <;> omega)
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨s, t, hst⟩
  · exact ⟨t, s, hst.trans (add_comm _ _)⟩
  · exact absurd rfl hij

private theorem irgK2_exists_algebraMap_mul_eq {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite F] [CharP F 2] {f : ℕ} [CharP K 2] [Finite K] {b c : F}
    (D : KleinDataEven F K (unitaryInvolution K 2 f) b c)
    {e : K} (he : unitaryInvolution K 2 f e = -e) (he0 : e ≠ 0) {y : K}
    (hy : unitaryInvolution K 2 f y = -y) :
    ∃ r : F, algebraMap F K r * e = y := by
  have hz : unitaryInvolution K 2 f (y * e⁻¹) = y * e⁻¹ := by
    rw [map_mul, hy, map_inv₀, he]
    ring
  obtain ⟨r, hr⟩ := D.exists_algebraMap_eq_of_σ_eq hz
  exact ⟨r, by rw [hr, mul_assoc, inv_mul_cancel₀ he0, mul_one]⟩

private theorem irgK2_eps_ne_zero {F K : Type} [Field F] [Field K] [Algebra F K] {f : ℕ}
    [CharP K 2] [Finite K] {b c : F}
    (D : KleinDataEven F K (unitaryInvolution K 2 f) b c) : D.ε ≠ 0 := by
  intro h
  have := D.δ_mul_ε
  rw [h, mul_zero] at this
  exact zero_ne_one this

private theorem irgK2_delta_ne_zero {F K : Type} [Field F] [Field K] [Algebra F K] {f : ℕ}
    [CharP K 2] [Finite K] {b c : F}
    (D : KleinDataEven F K (unitaryInvolution K 2 f) b c) : D.δ ≠ 0 := by
  intro h
  have := D.δ_mul_ε
  rw [h, zero_mul] at this
  exact zero_ne_one this

private theorem irgK2_rootGroup_four_top {K : Type} [Field K] {σ : K ≃+* K}
    (hσ : ∀ c, σ (σ c) = c) :
    rootGroup σ hσ 4 (ggTopRoot 4) =
      (longRootHom σ (i := (0 : Fin 4)) (by decide)).range := by
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      exfalso
      revert hij hi hj hji hw
      fin_cases i <;> fin_cases j <;> decide
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      have hi0 : i = 0 := by
        revert hw
        fin_cases i <;> decide
      subst hi0
      exact le_rfl
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact longRootHom_mem hσ _ (by decide) c

private theorem irgK2_rootGroup_four_neg_top {K : Type} [Field K] {σ : K ≃+* K}
    (hσ : ∀ c, σ (σ c) = c) :
    rootGroup σ hσ 4 (-ggTopRoot 4) =
      (longRootHom σ (i := (3 : Fin 4)) (by decide)).range := by
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      exfalso
      revert hij hi hj hji hw
      fin_cases i <;> fin_cases j <;> decide
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      have hi3 : i = 3 := by
        revert hw
        fin_cases i <;> decide
      subst hi3
      exact le_rfl
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact longRootHom_mem hσ _ (by decide) c

private theorem irgK2_map_e0e1 {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F]
    [CharP F 2] {f : ℕ} [CharP K 2] [Finite K] {b c : F}
    (D : KleinDataEven F K (unitaryInvolution K 2 f) b c)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    (((minusFrame 3 b c).longRoot fin_zero_ne_one true true).range).map
        (D.phiSUEven hK hirr).toMonoidHom =
      rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4 (ggTopRoot 4) := by
  rw [irgK2_rootGroup_four_top (unitaryInvolution_involutive hK)]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    refine ⟨Multiplicative.ofAdd ⟨algebraMap F K a.toAdd * D.δ, mem_traceZero_of_eq_neg _ D.σ_δ_mul⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [show (D.phiSUEven hK hirr).toMonoidHom = D.PhiSUEven hirr from rfl, D.coe_PhiSUEven, coe_longRootHom]
    rw [show a = Multiplicative.ofAdd a.toAdd from rfl, D.PhiMon_long_e0e1]
    rfl
  · rintro _ ⟨w, rfl⟩
    obtain ⟨r, hr⟩ := irgK2_exists_algebraMap_mul_eq (D := D) (e := D.δ) D.σ_δ
      (irgK2_delta_ne_zero D) (y := w.toAdd) (eq_neg_of_mem_traceZero' _ w.toAdd.2)
    refine ⟨(minusFrame 3 b c).longRoot fin_zero_ne_one true true (Multiplicative.ofAdd r),
      ⟨_, rfl⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [show (D.phiSUEven hK hirr).toMonoidHom = D.PhiSUEven hirr from rfl, D.coe_PhiSUEven, coe_longRootHom, D.PhiMon_long_e0e1, hr]

private theorem irgK2_map_e0f1 {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F]
    [CharP F 2] {f : ℕ} [CharP K 2] [Finite K] {b c : F}
    (D : KleinDataEven F K (unitaryInvolution K 2 f) b c)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    (((minusFrame 3 b c).longRoot fin_zero_ne_one true false).range).map
        (D.phiSUEven hK hirr).toMonoidHom =
      rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4
        (Pi.single (1 : Fin 2) 1) := by
  rw [rootGroup_four_one_eq_longRoot_range]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    refine ⟨Multiplicative.ofAdd ⟨algebraMap F K a.toAdd * D.ε, mem_traceZero_of_eq_neg _ D.σ_ε_mul⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [show (D.phiSUEven hK hirr).toMonoidHom = D.PhiSUEven hirr from rfl, D.coe_PhiSUEven, coe_longRootHom]
    rw [show a = Multiplicative.ofAdd a.toAdd from rfl, D.PhiMon_long_e0f1]
    rfl
  · rintro _ ⟨w, rfl⟩
    obtain ⟨r, hr⟩ := irgK2_exists_algebraMap_mul_eq (D := D) (e := D.ε) D.σ_ε
      (irgK2_eps_ne_zero D) (y := w.toAdd) (eq_neg_of_mem_traceZero' _ w.toAdd.2)
    refine ⟨(minusFrame 3 b c).longRoot fin_zero_ne_one true false (Multiplicative.ofAdd r),
      ⟨_, rfl⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [show (D.phiSUEven hK hirr).toMonoidHom = D.PhiSUEven hirr from rfl, D.coe_PhiSUEven, coe_longRootHom, D.PhiMon_long_e0f1, hr]

private theorem irgK2_map_e1f0 {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F]
    [CharP F 2] {f : ℕ} [CharP K 2] [Finite K] {b c : F}
    (D : KleinDataEven F K (unitaryInvolution K 2 f) b c)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    (((minusFrame 3 b c).longRoot fin_zero_ne_one.symm true false).range).map
        (D.phiSUEven hK hirr).toMonoidHom =
      rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4
        (-Pi.single (1 : Fin 2) 1) := by
  rw [rootGroup_four_neg_one_eq_longRoot_range]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    refine ⟨Multiplicative.ofAdd ⟨algebraMap F K a.toAdd * D.δ, mem_traceZero_of_eq_neg _ D.σ_δ_mul⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [show (D.phiSUEven hK hirr).toMonoidHom = D.PhiSUEven hirr from rfl, D.coe_PhiSUEven, coe_longRootHom]
    rw [show a = Multiplicative.ofAdd a.toAdd from rfl, D.PhiMon_long_e1f0]
    rfl
  · rintro _ ⟨w, rfl⟩
    obtain ⟨r, hr⟩ := irgK2_exists_algebraMap_mul_eq (D := D) (e := D.δ) D.σ_δ
      (irgK2_delta_ne_zero D) (y := w.toAdd) (eq_neg_of_mem_traceZero' _ w.toAdd.2)
    refine ⟨(minusFrame 3 b c).longRoot fin_zero_ne_one.symm true false (Multiplicative.ofAdd r),
      ⟨_, rfl⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [show (D.phiSUEven hK hirr).toMonoidHom = D.PhiSUEven hirr from rfl, D.coe_PhiSUEven, coe_longRootHom, D.PhiMon_long_e1f0, hr]

private theorem irgK2_map_f0f1 {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F]
    [CharP F 2] {f : ℕ} [CharP K 2] [Finite K] {b c : F}
    (D : KleinDataEven F K (unitaryInvolution K 2 f) b c)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    (((minusFrame 3 b c).longRoot fin_zero_ne_one false false).range).map
        (D.phiSUEven hK hirr).toMonoidHom =
      rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4
        (-ggTopRoot 4) := by
  rw [irgK2_rootGroup_four_neg_top (unitaryInvolution_involutive hK)]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    refine ⟨Multiplicative.ofAdd
      ⟨-(algebraMap F K a.toAdd * D.ε), mem_traceZero_of_eq_neg _ (by rw [map_neg, D.σ_ε_mul])⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [show (D.phiSUEven hK hirr).toMonoidHom = D.PhiSUEven hirr from rfl, D.coe_PhiSUEven, coe_longRootHom]
    rw [show a = Multiplicative.ofAdd a.toAdd from rfl, D.PhiMon_long_f0f1]
    rfl
  · rintro _ ⟨w, rfl⟩
    obtain ⟨r, hr⟩ := irgK2_exists_algebraMap_mul_eq (D := D) (e := D.ε) D.σ_ε
      (irgK2_eps_ne_zero D) (y := -w.toAdd) (by rw [map_neg, eq_neg_of_mem_traceZero' _ w.toAdd.2])
    refine ⟨(minusFrame 3 b c).longRoot fin_zero_ne_one false false (Multiplicative.ofAdd r),
      ⟨_, rfl⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [show (D.phiSUEven hK hirr).toMonoidHom = D.PhiSUEven hirr from rfl, D.coe_PhiSUEven, coe_longRootHom, D.PhiMon_long_f0f1]
    rw [hr, neg_neg]


private theorem irgK2_ggLongRoot_weylAction_iff {K : Type} [Group K] (D : UniversalRootDatum K)
    (w : GGWeyl D) (γ : Fin D.rank → ℤ) :
    GGLongRoot D (weylAction D.isFiniteType w γ) ↔ GGLongRoot D γ := by
  constructor
  · rintro ⟨w', γ₀, hγ₀, hmax, hγw⟩
    refine ⟨w⁻¹ * w', γ₀, hγ₀, hmax, ?_⟩
    rw [weylAction_mul_apply, ← hγw, weylAction_inv_apply_apply]
  · rintro ⟨w', γ₀, hγ₀, hmax, hγw⟩
    exact ⟨w * w', γ₀, hγ₀, hmax, by rw [weylAction_mul_apply, hγw]⟩

theorem irgK2_compat_psiSUEven {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F]
    [CharP F 2] {f : ℕ} [CharP K 2] [Finite K] {b c : F}
    (D : KleinDataEven F K (unitaryInvolution K 2 f) b c)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∀ β' ∈ (minusDatum 3 hirr).roots, GGLongRoot (minusDatum 3 hirr) β' →
      ∃ γ, (γ ∈ (Unitary.rootDatum hK 4).roots ∧
              GGLongRoot (Unitary.rootDatum hK 4) γ) ∧
        ∃ w : SU (unitaryInvolution K 2 f) 4,
          ((minusDatum 3 hirr).rootGroup β').map (D.phiSUEven hK hirr).toMonoidHom =
              ((Unitary.rootDatum hK 4).rootGroup γ).map (MulAut.conj w).toMonoidHom ∧
            ((minusDatum 3 hirr).rootGroup (-β')).map (D.phiSUEven hK hirr).toMonoidHom =
              ((Unitary.rootDatum hK 4).rootGroup (-γ)).map (MulAut.conj w).toMonoidHom := by
  have hθ : GGLongRoot (Unitary.rootDatum hK 4) (ggTopRoot 4) :=
    CFSG.StandardType.RestSU.ggTopRoot_longRoot (F := K) (f := f) hK (by norm_num)
  have hrootθ : ggTopRoot 4 ∈ (Unitary.rootDatum hK 4).roots :=
    ggTopRoot_mem_roots (n := 4) (by norm_num)
  let s0 : GGWeyl (Unitary.rootDatum hK 4) :=
    (coxeterMatrix (isFiniteType_cartan 4)).toCoxeterSystem.simple (0 : Fin 2)
  let s1 : GGWeyl (Unitary.rootDatum hK 4) :=
    (coxeterMatrix (isFiniteType_cartan 4)).toCoxeterSystem.simple (1 : Fin 2)
  have hw1 : (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) =
      weylAction (isFiniteType_cartan 4) ((coxeterMatrix (isFiniteType_cartan 4)).toCoxeterSystem.simple (0 : Fin 2)) (ggTopRoot 4) := by
    simp only [weylAction_simple, reflection_apply]
    decide +kernel
  have hlong1 : GGLongRoot (Unitary.rootDatum hK 4) (Pi.single (1 : Fin 2) 1) := by
    exact hw1.symm ▸ (irgK2_ggLongRoot_weylAction_iff _ s0 _).2 hθ
  have hroot1 : Pi.single (1 : Fin 2) 1 ∈ (Unitary.rootDatum hK 4).roots :=
    hw1.symm ▸ weylAction_mem_roots hrootθ s0
  have hw2 : (-Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) =
      weylAction (isFiniteType_cartan 4) ((coxeterMatrix (isFiniteType_cartan 4)).toCoxeterSystem.simple (1 : Fin 2)) (Pi.single (1 : Fin 2) 1) := by
    simp only [weylAction_simple, reflection_apply]
    decide +kernel
  have hlong2 : GGLongRoot (Unitary.rootDatum hK 4) (-Pi.single (1 : Fin 2) 1) := by
    exact hw2.symm ▸ (irgK2_ggLongRoot_weylAction_iff _ s1 _).2 hlong1
  have hroot2 : -Pi.single (1 : Fin 2) 1 ∈ (Unitary.rootDatum hK 4).roots :=
    hw2.symm ▸ weylAction_mem_roots hroot1 s1
  have hw3 : (-ggTopRoot 4 : Fin 2 → ℤ) =
      weylAction (isFiniteType_cartan 4) ((coxeterMatrix (isFiniteType_cartan 4)).toCoxeterSystem.simple (0 : Fin 2)) (-Pi.single (1 : Fin 2) 1) := by
    simp only [weylAction_simple, reflection_apply]
    decide +kernel
  have hlong3 : GGLongRoot (Unitary.rootDatum hK 4) (-ggTopRoot 4) := by
    exact hw3.symm ▸ (irgK2_ggLongRoot_weylAction_iff _ s0 _).2 hlong2
  have hroot3 : -ggTopRoot 4 ∈ (Unitary.rootDatum hK 4).roots :=
    hw3.symm ▸ weylAction_mem_roots hroot2 s0
  intro β' _ hlong
  obtain ⟨s, t, hst⟩ := irgK2_exists_long_of_ggLongRoot_minus_three hirr hlong
  cases s <;> cases t
  · have hβ : (minusDatum 3 hirr).rootGroup β' = _ := minusRootGroup_eq_long 3 hirr fin_zero_ne_one false false hst
    have hn : toStdB 2 (-β') =
        Pi.single (0 : Fin 2) (boolSign true) + Pi.single (1 : Fin 2) (boolSign true) := by
      rw [show toStdB 2 (-β') = -toStdB 2 β' from toStdB_neg 2 β', hst]
      ext j <;> fin_cases j <;> simp [boolSign]
    have hβn : (minusDatum 3 hirr).rootGroup (-β') = _ := minusRootGroup_eq_long 3 hirr fin_zero_ne_one true true hn
    refine ⟨-ggTopRoot 4, ⟨hroot3, hlong3⟩, 1, ?_, ?_⟩
    · rw [hβ, irgK2_map_f0f1 D hK hirr]
      rw [show (Unitary.rootDatum hK 4).rootGroup =
          rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4 from rfl,
        show (MulAut.conj (1 : SU (unitaryInvolution K 2 f) 4)).toMonoidHom =
          MonoidHom.id _ from by ext x; simp [MulAut.conj], Subgroup.map_id] <;> exact congrArg (rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4) (by funext i; first | rfl | exact (neg_neg _).symm)
    · rw [hβn, irgK2_map_e0e1 D hK hirr]
      rw [show (Unitary.rootDatum hK 4).rootGroup =
          rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4 from rfl,
        show (MulAut.conj (1 : SU (unitaryInvolution K 2 f) 4)).toMonoidHom =
          MonoidHom.id _ from by ext x; simp [MulAut.conj], Subgroup.map_id] <;> exact congrArg (rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4) (by funext i; first | rfl | exact (neg_neg _).symm)
  · have hst' : toStdB 2 β' =
        Pi.single (1 : Fin 2) (boolSign true) + Pi.single (0 : Fin 2) (boolSign false) := by
      rw [hst, add_comm]
    have hβ : (minusDatum 3 hirr).rootGroup β' = _ := minusRootGroup_eq_long 3 hirr fin_zero_ne_one.symm true false hst'
    have hn : toStdB 2 (-β') =
        Pi.single (0 : Fin 2) (boolSign true) + Pi.single (1 : Fin 2) (boolSign false) := by
      rw [show toStdB 2 (-β') = -toStdB 2 β' from toStdB_neg 2 β', hst]
      ext j <;> fin_cases j <;> simp [boolSign]
    have hβn : (minusDatum 3 hirr).rootGroup (-β') = _ := minusRootGroup_eq_long 3 hirr fin_zero_ne_one true false hn
    refine ⟨-Pi.single (1 : Fin 2) 1, ⟨hroot2, hlong2⟩, 1, ?_, ?_⟩
    · rw [hβ, irgK2_map_e1f0 D hK hirr]
      rw [show (Unitary.rootDatum hK 4).rootGroup =
          rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4 from rfl,
        show (MulAut.conj (1 : SU (unitaryInvolution K 2 f) 4)).toMonoidHom =
          MonoidHom.id _ from by ext x; simp [MulAut.conj], Subgroup.map_id] <;> exact congrArg (rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4) (by funext i; first | rfl | exact (neg_neg _).symm)
    · rw [hβn, irgK2_map_e0f1 D hK hirr]
      rw [show (Unitary.rootDatum hK 4).rootGroup =
          rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4 from rfl,
        show (MulAut.conj (1 : SU (unitaryInvolution K 2 f) 4)).toMonoidHom =
          MonoidHom.id _ from by ext x; simp [MulAut.conj], Subgroup.map_id] <;> exact congrArg (rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4) (by funext i; first | rfl | exact (neg_neg _).symm)
  · have hβ : (minusDatum 3 hirr).rootGroup β' = _ := minusRootGroup_eq_long 3 hirr fin_zero_ne_one true false hst
    have hn : toStdB 2 (-β') =
        Pi.single (0 : Fin 2) (boolSign false) + Pi.single (1 : Fin 2) (boolSign true) := by
      rw [show toStdB 2 (-β') = -toStdB 2 β' from toStdB_neg 2 β', hst]
      ext j <;> fin_cases j <;> simp [boolSign]
    have hn' : toStdB 2 (-β') =
        Pi.single (1 : Fin 2) (boolSign true) + Pi.single (0 : Fin 2) (boolSign false) := by
      rw [hn, add_comm]
    have hβn : (minusDatum 3 hirr).rootGroup (-β') = _ := minusRootGroup_eq_long 3 hirr fin_zero_ne_one.symm true false hn'
    refine ⟨Pi.single (1 : Fin 2) 1, ⟨hroot1, hlong1⟩, 1, ?_, ?_⟩
    · rw [hβ, irgK2_map_e0f1 D hK hirr]
      rw [show (Unitary.rootDatum hK 4).rootGroup =
          rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4 from rfl,
        show (MulAut.conj (1 : SU (unitaryInvolution K 2 f) 4)).toMonoidHom =
          MonoidHom.id _ from by ext x; simp [MulAut.conj], Subgroup.map_id] <;> exact congrArg (rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4) (by funext i; first | rfl | exact (neg_neg _).symm)
    · rw [hβn, irgK2_map_e1f0 D hK hirr]
      rw [show (Unitary.rootDatum hK 4).rootGroup =
          rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4 from rfl,
        show (MulAut.conj (1 : SU (unitaryInvolution K 2 f) 4)).toMonoidHom =
          MonoidHom.id _ from by ext x; simp [MulAut.conj], Subgroup.map_id] <;> exact congrArg (rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4) (by funext i; first | rfl | exact (neg_neg _).symm)
  · have hβ : (minusDatum 3 hirr).rootGroup β' = _ := minusRootGroup_eq_long 3 hirr fin_zero_ne_one true true hst
    have hn : toStdB 2 (-β') =
        Pi.single (0 : Fin 2) (boolSign false) + Pi.single (1 : Fin 2) (boolSign false) := by
      rw [show toStdB 2 (-β') = -toStdB 2 β' from toStdB_neg 2 β', hst]
      ext j <;> fin_cases j <;> simp [boolSign]
    have hβn : (minusDatum 3 hirr).rootGroup (-β') = _ := minusRootGroup_eq_long 3 hirr fin_zero_ne_one false false hn
    refine ⟨ggTopRoot 4, ⟨hrootθ, hθ⟩, 1, ?_, ?_⟩
    · rw [hβ, irgK2_map_e0e1 D hK hirr]
      rw [show (Unitary.rootDatum hK 4).rootGroup =
          rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4 from rfl,
        show (MulAut.conj (1 : SU (unitaryInvolution K 2 f) 4)).toMonoidHom =
          MonoidHom.id _ from by ext x; simp [MulAut.conj], Subgroup.map_id] <;> exact congrArg (rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4) (by funext i; first | rfl | exact (neg_neg _).symm)
    · rw [hβn, irgK2_map_f0f1 D hK hirr]
      rw [show (Unitary.rootDatum hK 4).rootGroup =
          rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4 from rfl,
        show (MulAut.conj (1 : SU (unitaryInvolution K 2 f) 4)).toMonoidHom =
          MonoidHom.id _ from by ext x; simp [MulAut.conj], Subgroup.map_id] <;> exact congrArg (rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4) (by funext i; first | rfl | exact (neg_neg _).symm)

end CFSG.StandardType.RCKRP

module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankKG
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.LocalAnalysis.StandardType.KGLangTorALangElt
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniLift
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearDescent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem kgLangTorAUniFrameAux_gu_descend {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd0 : 0 < d)
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F} (hσ : orderOf σ = p)
    {M : GL (Fin d) (semilinearFixedSubfield σ)}
    (hM : Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M ∈
      LargeEvenGUSet (Fin d) F (2 ^ n)) :
    M ∈ LargeEvenGUSet (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p)) := by
  obtain ⟨ν, hν0, hνq, hν⟩ := hM
  have hpow : ∀ x : semilinearFixedSubfield σ,
      ((x : F) ^ 2 ^ (n / p)) = (x : F) ^ 2 ^ n :=
    fun x => (kgLangTorA_pow_eq_on_fixed hn hp hp2 hF hσ x).symm
  have hmap : (((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map
        (fun x : semilinearFixedSubfield σ => x ^ 2 ^ (n / p))).map
        (semilinearFixedSubfield σ).subtype) =
      (((Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F).map (· ^ 2 ^ n)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply]
    exact hpow ((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) i j)
  have hNmat : (Matrix.transpose (((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map
        (fun x : semilinearFixedSubfield σ => x ^ 2 ^ (n / p)))) *
        (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ))).map
        (semilinearFixedSubfield σ).subtype = ν • (1 : Matrix (Fin d) (Fin d) F) := by
    rw [Matrix.map_mul, Matrix.transpose_map, hmap]
    exact hν
  set μ : semilinearFixedSubfield σ :=
    (Matrix.transpose (((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map
      (fun x : semilinearFixedSubfield σ => x ^ 2 ^ (n / p)))) *
      (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ))) ⟨0, hd0⟩ ⟨0, hd0⟩ with hμ
  have hμν : (μ : F) = ν := by
    have h := congrFun (congrFun hNmat ⟨0, hd0⟩) ⟨0, hd0⟩
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at h
    rwa [← hμ] at h
  have hNdiag : Matrix.transpose ((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map
      (fun x : semilinearFixedSubfield σ => x ^ 2 ^ (n / p))) *
      (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) =
      μ • (1 : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) := by
    apply Matrix.map_injective (semilinearFixedSubfield σ).subtype_injective
    change (Matrix.transpose (((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map
        (fun x : semilinearFixedSubfield σ => x ^ 2 ^ (n / p)))) *
        (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ))).map
          (semilinearFixedSubfield σ).subtype =
      (μ • (1 : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ))).map
        (semilinearFixedSubfield σ).subtype
    rw [hNmat, Matrix.map_smul' (semilinearFixedSubfield σ).subtype μ
        (1 : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) (fun a b => map_mul _ _ _),
      Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    exact hμν.symm
  refine ⟨μ, ?_, ?_, hNdiag⟩
  · intro hμ0
    apply hν0
    rw [← hμν, hμ0]
    rfl
  · apply (semilinearFixedSubfield σ).subtype_injective
    show (μ : F) ^ 2 ^ (n / p) = (μ : F)
    rw [hpow μ, hμν, hνq]

private theorem kgLangTorAUniFrameAux_scalar_descend {d : ℕ} {F : Type} [Field F]
    {σ : F ≃+* F} (hd : 0 < d) {M : GL (Fin d) (semilinearFixedSubfield σ)}
    (h : Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M ∈
      LargeEvenScalars (Fin d) F) :
    M ∈ LargeEvenScalars (Fin d) (semilinearFixedSubfield σ) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨c, hc⟩ := h
  have hentry : ∀ i j : Fin d,
      (semilinearFixedSubfield σ).subtype
        ((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) i j) =
        (if i = j then (c : F) else 0) := by
    intro i j
    have h1 := congrArg (fun A : GL (Fin d) F => (A : Matrix (Fin d) (Fin d) F) i j) hc
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.GeneralLinearGroup.map_apply] at h1
    exact h1.symm
  let a : semilinearFixedSubfield σ :=
    (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) ⟨0, hd⟩ ⟨0, hd⟩
  have hdiag : (semilinearFixedSubfield σ).subtype a = (c : F) := by
    have h1 := hentry ⟨0, hd⟩ ⟨0, hd⟩
    simpa [a] using h1
  have ha0 : a ≠ 0 := by
    intro h0
    have h2 : (c : F) = 0 := by rw [← hdiag, h0]; rfl
    exact c.ne_zero h2
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_mk0]
    exact (semilinearFixedSubfield σ).subtype_injective (by rw [hentry i i, if_pos rfl, hdiag])
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ hij]
    exact (semilinearFixedSubfield σ).subtype_injective (by
      rw [hentry i j, if_neg hij, map_zero])

private theorem kgLangTorAUniFrameAux_eq_projConj_of_graph {d : ℕ} {F : Type} [Field F]
    {S : Subgroup (GL (Fin d) F)} {B : GL (Fin d) F}
    (hBnorm : B ∈ Subgroup.normalizer (S : Set (GL (Fin d) F)))
    {x : MulAut (LargeEvenProj S)}
    (hx : LargeEvenGraphAut (LargeEvenProjMk S)
      (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x) :
    x = TableB.projConj S ⟨B, hBnorm⟩ := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [TableB.projConj_mk]
    exact hx g ⟨B * (g : GL (Fin d) F) * B⁻¹,
      (Subgroup.mem_normalizer_iff.mp hBnorm g).mp g.2⟩ rfl

private theorem kgLangTorAUniFrameAux_projConj_mk {d : ℕ} {F : Type} [Field F]
    (H : Subgroup (GL (Fin d) F))
    (A : Subgroup.normalizer (H : Set (GL (Fin d) F))) (h : H) :
    TableB.projConj H A (LargeEvenProjMk H h) =
      LargeEvenProjMk H (H.normalizerMonoidHom A h) :=
  TableB.projConj_mk H A h

theorem kgLangTorA_uni_frame_group {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F} (hσ : orderOf σ = p)
    {X : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))))}
    (hX : IsElemAbelian p X)
    (hXI : ∀ x ∈ X, x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))) (LargeEvenGUSet (Fin d) F (2 ^ n)))
    {f₀ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hf₀ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ) f₀)
    (hXf : ∀ x ∈ X, f₀ * x = x * f₀) :
    ∃ X₀ : Subgroup (MulAut (LinearFlag.projectiveSL d (semilinearFixedSubfield σ))),
      IsElemAbelian p X₀ ∧
      (∀ y ∈ X₀, ∃ M ∈ LargeEvenGUSet (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p)),
        LinearFlag.conjAut d (semilinearFixedSubfield σ) M = y) ∧
      Nat.card X ≤ Nat.card X₀ ∧
      ∀ B ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x ∈ X,
        LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
          (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x →
        ∃ (c : Fˣ) (M : GL (Fin d) (semilinearFixedSubfield σ)),
          LinearFlag.conjAut d (semilinearFixedSubfield σ) M ∈ X₀ ∧
          B = Matrix.GeneralLinearGroup.scalar (Fin d) c *
            Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M := by
  classical
  have hd0 : 0 < d := by omega
  haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  haveI : CharP F 2 := (unitaryFieldData_of_card hn hF).charP
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (semilinearFixedSubfield σ) := Fintype.ofFinite _
  let H : Subgroup (GL (Fin d) F) := LargeEvenSUGroup (Fin d) F (2 ^ n)
  let N : Subgroup (GL (Fin d) F) := Subgroup.normalizer (H : Set (GL (Fin d) F))
  let N₀ : Subgroup (GL (Fin d) (semilinearFixedSubfield σ)) :=
    N.comap (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype)
  let φ : N₀ →* N :=
    { toFun := fun M => ⟨Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
          (M : GL (Fin d) (semilinearFixedSubfield σ)), M.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp }
  let ρ : N₀ →* MulAut (LargeEvenProj H) := (TableB.projConj H).comp φ
  let G₀ : Subgroup N₀ := (X.comap (TableB.projConj H)).comap φ
  let χ : N₀ →* MulAut (LinearFlag.projectiveSL d (semilinearFixedSubfield σ)) :=
    (LinearFlag.conjAut d (semilinearFixedSubfield σ)).comp N₀.subtype
  let X₀ : Subgroup (MulAut (LinearFlag.projectiveSL d (semilinearFixedSubfield σ))) := G₀.map χ
  have hmemG : ∀ M : N₀, M ∈ G₀ ↔ ρ M ∈ X := by
    intro M
    show M ∈ (X.comap (TableB.projConj H)).comap φ ↔ _
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    rfl
  have hU2 : ∀ M : N, TableB.projConj H M = 1 →
      (M : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F :=
    fun M hM => kgLangTorA_uni_scalar hF hn hd hdq (by simpa [H] using hM)
  have hscal : ∀ M : N₀, ρ M = 1 →
      (M : GL (Fin d) (semilinearFixedSubfield σ)) ∈
        LargeEvenScalars (Fin d) (semilinearFixedSubfield σ) := by
    intro M hM
    have h1 : (φ M : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
      apply hU2
      show TableB.projConj H (φ M) = 1
      simpa [ρ] using hM
    exact kgLangTorAUniFrameAux_scalar_descend hd0 (by simpa [φ] using h1)
  have hχscal : ∀ M : N₀,
      (M : GL (Fin d) (semilinearFixedSubfield σ)) ∈
        LargeEvenScalars (Fin d) (semilinearFixedSubfield σ) →
      χ M = 1 := by
    intro M hM
    obtain ⟨u, hu⟩ := hM
    show LinearFlag.conjAut d (semilinearFixedSubfield σ)
      (M : GL (Fin d) (semilinearFixedSubfield σ)) = 1
    rw [← hu, LinearFlag.conjAut_scalar]
  have hSgu : LargeEvenGUSet (Fin d) F (2 ^ n) ⊆ (N : Set (GL (Fin d) F)) :=
    TableBUE.gu_subset_normalizer (d := d) (unitaryFieldData_of_card hn hF)
  refine ⟨X₀, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, M, hM, rfl⟩ ⟨_, M', hM', rfl⟩
      apply Subtype.ext
      have hρ1 : ρ (M * M' * M⁻¹ * M'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        have hc : ρ M * ρ M' = ρ M' * ρ M := congrArg Subtype.val
          (hX.1.is_comm.comm ⟨ρ M, (hmemG M).mp hM⟩ ⟨ρ M', (hmemG M').mp hM'⟩)
        rw [hc]
        group
      have hsc := hscal _ hρ1
      have hχ1 : χ (M * M' * M⁻¹ * M'⁻¹) = 1 := hχscal _ hsc
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hχ1
      show χ M * χ M' = χ M' * χ M
      calc χ M * χ M' = χ M * χ M' * (χ M)⁻¹ * (χ M')⁻¹ * (χ M' * χ M) := by group
        _ = χ M' * χ M := by rw [hχ1, one_mul]
    · rintro _ ⟨M, hM, rfl⟩
      rw [← map_pow]
      have hρ1 : ρ (M ^ p) = 1 := by
        rw [map_pow]
        exact hX.2 (ρ M) ((hmemG M).mp hM)
      have hsc := hscal _ hρ1
      have hχ1 : χ (M ^ p) = 1 := hχscal _ hsc
      simpa using hχ1
  ·
    intro y hy
    obtain ⟨M, hM, rfl⟩ := Subgroup.mem_map.mp hy
    have hρX : ρ M ∈ X := (hmemG M).mp hM
    obtain ⟨B, hBgu, hBeq⟩ := TableB.exists_eq_projConj hSgu (hXI (ρ M) hρX)
    have hBnorm : B ∈ N := hSgu hBgu
    have hz : TableB.projConj H (φ M * ⟨B, hBnorm⟩⁻¹) = 1 := by
      rw [map_mul, map_inv]
      rw [show TableB.projConj H (φ M) = ρ M from rfl, hBeq]
      simp
    have hzsc := hU2 _ hz
    obtain ⟨c, hc⟩ := hzsc
    have hφgu : (φ M : GL (Fin d) F) ∈ LargeEvenGUSet (Fin d) F (2 ^ n) := by
      have hceq : (φ M : GL (Fin d) F) = Matrix.GeneralLinearGroup.scalar (Fin d) c * B := by
        rw [hc]
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hceq]
      exact kgLangTorA_gu_scalar_mul hF hBgu c
    refine ⟨(M : GL (Fin d) (semilinearFixedSubfield σ)), ?_, ?_⟩
    · exact kgLangTorAUniFrameAux_gu_descend hF hn hd0 hp hp2 hσ (by simpa [φ] using hφgu)
    · rfl
  ·
    let f : G₀ →* MulAut (LargeEvenProj H) := ρ.comp G₀.subtype
    let g : G₀ →* MulAut (LinearFlag.projectiveSL d (semilinearFixedSubfield σ)) :=
      χ.comp G₀.subtype
    have hfrange : f.range = X := by
      apply le_antisymm
      · rintro _ ⟨M, rfl⟩
        exact (hmemG (M : N₀)).mp M.2
      · intro x hxX
        obtain ⟨B, hBgu, hBeq⟩ :=
          TableB.exists_eq_projConj hSgu (hXI x hxX)
        have hBnorm : B ∈ N := hSgu hBgu
        have hBgraph : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
            (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x := by
          intro g g' hgg'
          rw [hBeq, kgLangTorAUniFrameAux_projConj_mk]
          exact congrArg (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
            (Subtype.ext hgg'.symm)
        obtain ⟨c, hc⟩ := kgLangTorA_uni_semifixed hF hn hd hdq hf₀ hBgu hBgraph (hXf x hxX)
        have hc' : ((Matrix.GeneralLinearGroup.map (σ : F →+* F) B : GL (Fin d) F) :
            Matrix (Fin d) (Fin d) F) = (c : F) • (B : Matrix (Fin d) (Fin d) F) := by
          have hh := congrArg (fun z : GL (Fin d) F => (z : Matrix (Fin d) (Fin d) F)) hc
          rw [TableB.coe_scalar_mul] at hh
          exact hh
        obtain ⟨μ, M, hM⟩ : ∃ (μ : Fˣ) (M : GL (Fin d) (semilinearFixedSubfield σ)),
            ((Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M : GL (Fin d) F) :
              Matrix (Fin d) (Fin d) F) = (μ : F) • (B : Matrix (Fin d) (Fin d) F) :=
          LinearFieldFix.exists_descend_of_map_eq_smul σ B c hc'
        have hMgl : Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M =
            Matrix.GeneralLinearGroup.scalar (Fin d) μ * B := by
          apply Units.ext
          rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
            ← Matrix.smul_eq_diagonal_mul]
          exact hM
        have hzμ : Matrix.GeneralLinearGroup.scalar (Fin d) μ ∈ LargeEvenScalars (Fin d) F :=
          ⟨μ, rfl⟩
        have hMnorm : M ∈ N₀ := by
          show Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M ∈ N
          rw [hMgl]
          exact Subgroup.mul_mem _ (TableB.scalar_mem_normalizer H hzμ) hBnorm
        have hMρ : ρ ⟨M, hMnorm⟩ = x := by
          rw [show ρ ⟨M, hMnorm⟩ =
            TableB.projConj H ⟨Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M,
              hMnorm⟩ from rfl]
          have heq : (⟨Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M,
              hMnorm⟩ : N) =
              (⟨Matrix.GeneralLinearGroup.scalar (Fin d) μ,
                TableB.scalar_mem_normalizer H hzμ⟩ : N) * ⟨B, hBnorm⟩ := by
            apply Subtype.ext
            exact hMgl
          rw [heq, map_mul, TableB.projConj_of_scalar H hzμ, one_mul]
          exact hBeq.symm
        exact ⟨⟨⟨M, hMnorm⟩, (hmemG _).mpr (hMρ ▸ hxX)⟩, hMρ⟩
    have hgrange : g.range = X₀ := by
      ext y
      constructor
      · rintro ⟨M, rfl⟩
        exact Subgroup.mem_map.mpr ⟨(M : N₀), M.2, rfl⟩
      · rintro ⟨M, hM, rfl⟩
        exact ⟨⟨M, hM⟩, rfl⟩
    have hker : f.ker = g.ker := by
      ext M
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      show ρ (M : N₀) = 1 ↔ χ (M : N₀) = 1
      constructor
      · intro h1
        exact hχscal _ (hscal _ h1)
      · intro h1
        have hsc : ((M : N₀) : GL (Fin d) (semilinearFixedSubfield σ)) ∈
            LargeEvenScalars (Fin d) (semilinearFixedSubfield σ) := by
          obtain ⟨c₀, hc₀⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
          obtain ⟨u, hu⟩ := TypeA.exists_unit_of_scalar hd0 hc₀
          exact ⟨u, hu.symm⟩
        have h1' : ρ (M : N₀) = 1 := by
          have hφsc : (φ (M : N₀) : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
            obtain ⟨u, hu⟩ := hsc
            refine ⟨Units.map (semilinearFixedSubfield σ).subtype u, ?_⟩
            show Matrix.GeneralLinearGroup.scalar (Fin d)
                (Units.map (semilinearFixedSubfield σ).subtype u) = (φ (M : N₀) : GL (Fin d) F)
            rw [show (φ (M : N₀) : GL (Fin d) F) =
                Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
                  ((M : N₀) : GL (Fin d) (semilinearFixedSubfield σ)) from rfl,
              ← hu, Matrix.GeneralLinearGroup.map_scalar]
          have hproj : TableB.projConj H (φ (M : N₀)) = 1 :=
            TableB.projConj_of_scalar H hφsc
          show ρ (M : N₀) = 1
          simpa [ρ] using hproj
        exact h1'
    have hcard : Nat.card X = Nat.card X₀ := by
      have h1 := Subgroup.card_ker_mul_card_range f
      have h2 := Subgroup.card_ker_mul_card_range g
      rw [hfrange] at h1
      rw [hgrange] at h2
      rw [← hker] at h2
      exact Nat.mul_left_cancel (Nat.card_pos (α := f.ker)) (h1.trans h2.symm)
    exact hcard.le
  ·
    intro B hBgu x hxX hBx
    have hBnorm : B ∈ N := hSgu hBgu
    obtain ⟨c, hc⟩ := kgLangTorA_uni_semifixed hF hn hd hdq hf₀ hBgu hBx (hXf x hxX)
    have hc' : ((Matrix.GeneralLinearGroup.map (σ : F →+* F) B : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) = (c : F) • (B : Matrix (Fin d) (Fin d) F) := by
      have hh := congrArg (fun z : GL (Fin d) F => (z : Matrix (Fin d) (Fin d) F)) hc
      rw [TableB.coe_scalar_mul] at hh
      exact hh
    obtain ⟨μ, M, hM⟩ : ∃ (μ : Fˣ) (M : GL (Fin d) (semilinearFixedSubfield σ)),
        ((Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M : GL (Fin d) F) :
          Matrix (Fin d) (Fin d) F) = (μ : F) • (B : Matrix (Fin d) (Fin d) F) :=
      LinearFieldFix.exists_descend_of_map_eq_smul σ B c hc'
    have hMgl : Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M =
        Matrix.GeneralLinearGroup.scalar (Fin d) μ * B := by
      apply Units.ext
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
      exact hM
    have hzμ : Matrix.GeneralLinearGroup.scalar (Fin d) μ ∈ LargeEvenScalars (Fin d) F :=
      ⟨μ, rfl⟩
    have hMnorm : M ∈ N₀ := by
      show Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M ∈ N
      rw [hMgl]
      exact Subgroup.mul_mem _ (TableB.scalar_mem_normalizer H hzμ) hBnorm
    have hMρ : ρ ⟨M, hMnorm⟩ = x := by
      rw [show ρ ⟨M, hMnorm⟩ =
        TableB.projConj H ⟨Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M,
          hMnorm⟩ from rfl]
      have heq : (⟨Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M,
          hMnorm⟩ : N) =
          (⟨Matrix.GeneralLinearGroup.scalar (Fin d) μ,
            TableB.scalar_mem_normalizer H hzμ⟩ : N) * ⟨B, hBnorm⟩ := by
        apply Subtype.ext
        exact hMgl
      rw [heq, map_mul, TableB.projConj_of_scalar H hzμ, one_mul]
      have hBgraph : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
          (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x := hBx
      have hBeq : x = TableB.projConj H ⟨B, hBnorm⟩ :=
        kgLangTorAUniFrameAux_eq_projConj_of_graph hBnorm hBgraph
      exact hBeq.symm
    have hMG : (⟨M, hMnorm⟩ : N₀) ∈ G₀ := (hmemG _).mpr (by rw [hMρ]; exact hxX)
    refine ⟨μ⁻¹, M, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨M, hMnorm⟩, hMG, rfl⟩
    · rw [hMgl, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

end CFSG.StandardType

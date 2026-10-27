module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniFrame
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniLift
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem kgLangS1AUniFixedAux_scalar_descend {d : ℕ} {F : Type} [Field F]
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

private theorem kgLangS1AUniFixedAux_eq_projConj_of_graph {d : ℕ} {F : Type} [Field F]
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

private theorem kgLangS1AUniFixedAux_map_injective {d : ℕ} {F₀ F : Type} [Field F₀] [Field F]
    {ι : F₀ →+* F} (hι : Function.Injective ι) :
    Function.Injective
      (Matrix.GeneralLinearGroup.map ι : GL (Fin d) F₀ → GL (Fin d) F) := by
  intro A B hAB
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply hι
  have h := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F) i j) hAB
  simpa [Matrix.GeneralLinearGroup.map_apply] using h

private theorem kgLangS1AUniFixedAux_map_fixed {d : ℕ} {F : Type} [Field F]
    (σ : F ≃+* F) (M : GL (Fin d) (semilinearFixedSubfield σ)) :
    Matrix.GeneralLinearGroup.map (σ : F →+* F)
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M) =
      Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
  exact RingHom.mem_eqLocusField.mp
    ((M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) i j).2

theorem kgLangS1A_uni_fixed_group {d n p : ℕ} {F : Type} [Field F] [Finite F]
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
    ∃ S : Subgroup (GL (Fin d) (semilinearFixedSubfield σ)),
      (∀ M : GL (Fin d) (semilinearFixedSubfield σ), M ∈ S ↔
        ∃ hM : Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M ∈
            Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)),
          TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨_, hM⟩ ∈ X) ∧
      TypeA.PGLTor.IsProjElem p S ∧
      Nat.card S = Nat.card X * (Nat.card (semilinearFixedSubfield σ) - 1) ∧
      (∀ M ∈ S, M ∈ LargeEvenGUSet (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p))) ∧
      ∀ B ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x ∈ X,
        LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
          (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x →
        ∃ (c : Fˣ) (M : GL (Fin d) (semilinearFixedSubfield σ)), M ∈ S ∧
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
  let ι : GL (Fin d) (semilinearFixedSubfield σ) →* GL (Fin d) F :=
    Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
  let N₀ : Subgroup (GL (Fin d) (semilinearFixedSubfield σ)) := N.comap ι
  let φ : N₀ →* N :=
    { toFun := fun M => ⟨ι (M : GL (Fin d) (semilinearFixedSubfield σ)), M.2⟩
      map_one' := by apply Subtype.ext; simp [ι]
      map_mul' := by intro a b; apply Subtype.ext; simp [ι] }
  let ρ : N₀ →* MulAut (LargeEvenProj H) := (TableB.projConj H).comp φ
  let G₀ : Subgroup N₀ := (X.comap (TableB.projConj H)).comap φ
  let S : Subgroup (GL (Fin d) (semilinearFixedSubfield σ)) := G₀.map N₀.subtype
  have hmemG : ∀ M : N₀, M ∈ G₀ ↔ ρ M ∈ X := by
    intro M
    show M ∈ (X.comap (TableB.projConj H)).comap φ ↔ _
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    rfl
  have hSgu : LargeEvenGUSet (Fin d) F (2 ^ n) ⊆ (N : Set (GL (Fin d) F)) :=
    TableBUE.gu_subset_normalizer (d := d) (unitaryFieldData_of_card hn hF)
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
    exact kgLangS1AUniFixedAux_scalar_descend hd0 (by simpa [φ, ι] using h1)
  have hz : ∀ u : (semilinearFixedSubfield σ)ˣ,
      ι (Matrix.GeneralLinearGroup.scalar (Fin d) u) ∈ LargeEvenScalars (Fin d) F :=
    fun u => ⟨Units.map (semilinearFixedSubfield σ).subtype u,
      (Matrix.GeneralLinearGroup.map_scalar (semilinearFixedSubfield σ).subtype u).symm⟩
  let scal0 : (semilinearFixedSubfield σ)ˣ → N₀ := fun u =>
    ⟨Matrix.GeneralLinearGroup.scalar (Fin d) u, TableB.scalar_mem_normalizer H (hz u)⟩
  have hρscal : ∀ u, ρ (scal0 u) = 1 := by
    intro u
    show TableB.projConj H (φ (scal0 u)) = 1
    rw [show φ (scal0 u) =
        (⟨ι (Matrix.GeneralLinearGroup.scalar (Fin d) u),
          TableB.scalar_mem_normalizer H (hz u)⟩ : N) from rfl,
      TableB.projConj_of_scalar H (hz u)]
  have hscalG : ∀ u, scal0 u ∈ G₀ := fun u =>
    (hmemG (scal0 u)).mpr (by rw [hρscal u]; exact X.one_mem)
  have hmemS : ∀ M : GL (Fin d) (semilinearFixedSubfield σ), M ∈ S ↔
      ∃ hM : ι M ∈ N, TableB.projConj H ⟨ι M, hM⟩ ∈ X := by
    intro M
    constructor
    · intro hMS
      obtain ⟨x, hxG, hxM⟩ := Subgroup.mem_map.mp hMS
      have hMn : ι M ∈ N := by rw [← hxM]; exact x.2
      refine ⟨hMn, ?_⟩
      have hxeq : (⟨ι M, hMn⟩ : N) = φ x := by
        apply Subtype.ext
        show ι M = ι (x : GL (Fin d) (semilinearFixedSubfield σ))
        rw [← hxM]
        rfl
      rw [hxeq]
      exact (hmemG x).mp hxG
    · rintro ⟨hM, hMX⟩
      refine Subgroup.mem_map.mpr ⟨⟨M, hM⟩, ?_, rfl⟩
      exact (hmemG ⟨M, hM⟩).mpr (by simpa [ρ, φ] using hMX)
  have hprojS : TypeA.PGLTor.IsProjElem p S := by
    refine ⟨?_, ?_, ?_⟩
    · intro u
      exact Subgroup.mem_map.mpr ⟨scal0 u, hscalG u, rfl⟩
    · intro M hMS
      obtain ⟨x, hxG, hxM⟩ := Subgroup.mem_map.mp hMS
      have hρx : ρ x ∈ X := (hmemG x).mp hxG
      have hρxp : ρ (x ^ p) = 1 := by
        rw [map_pow]
        exact hX.2 (ρ x) hρx
      obtain ⟨u, hu⟩ := hscal (x ^ p) hρxp
      refine ⟨u, ?_⟩
      rw [hu, Subgroup.coe_pow]
      exact (congrArg (· ^ p) hxM).symm
    · intro M hMS N hNS
      obtain ⟨x, hxG, hxM⟩ := Subgroup.mem_map.mp hMS
      obtain ⟨y, hyG, hyM⟩ := Subgroup.mem_map.mp hNS
      have hρx : ρ x ∈ X := (hmemG x).mp hxG
      have hρy : ρ y ∈ X := (hmemG y).mp hyG
      have hcomm : ρ (x * y * (y * x)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, map_mul]
        rw [show ρ x * ρ y = ρ y * ρ x from
          congrArg Subtype.val (hX.1.is_comm.comm ⟨ρ x, hρx⟩ ⟨ρ y, hρy⟩)]
        group
      obtain ⟨u, hu⟩ := hscal _ hcomm
      refine ⟨u, ?_⟩
      have hcoeeq : ((x * y * (y * x)⁻¹ : N₀) :
          GL (Fin d) (semilinearFixedSubfield σ)) = M * N * (N * M)⁻¹ := by
        have h1 : N₀.subtype (x * y * (y * x)⁻¹) = M * N * (N * M)⁻¹ := by
          rw [map_mul, map_mul, map_inv, map_mul, hxM, hyM]
        simpa using h1
      rw [hu, hcoeeq]
      group
  obtain ⟨X₀, -, -, -, hlast⟩ :=
    kgLangTorA_uni_frame_group hF hn hd hdq hp hp2 hσ hX hXI hf₀ hXf
  have hdecomp : ∀ B ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x ∈ X,
      LargeEvenGraphAut (LargeEvenProjMk H)
        (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x →
      ∃ (c : Fˣ) (M : GL (Fin d) (semilinearFixedSubfield σ)),
        B = Matrix.GeneralLinearGroup.scalar (Fin d) c * ι M := by
    intro B hBgu x hxX hBx
    obtain ⟨c, M, -, hB⟩ := hlast B hBgu x hxX hBx
    exact ⟨c, M, hB⟩
  have hkey : ∀ B ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x ∈ X,
      LargeEvenGraphAut (LargeEvenProjMk H)
        (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x →
      ∃ (c : Fˣ) (M : GL (Fin d) (semilinearFixedSubfield σ)) (hM : ι M ∈ N),
        B = Matrix.GeneralLinearGroup.scalar (Fin d) c * ι M ∧
        TableB.projConj H ⟨ι M, hM⟩ = x := by
    intro B hBgu x hxX hBx
    obtain ⟨c, M, hB⟩ := hdecomp B hBgu x hxX hBx
    have hBnorm : B ∈ N := hSgu hBgu
    have hBeq : x = TableB.projConj H ⟨B, hBnorm⟩ :=
      kgLangS1AUniFixedAux_eq_projConj_of_graph hBnorm hBx
    have hιM : ι M = Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ * B := by
      rw [hB, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    have hMnorm' : Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ * B ∈ N :=
      Subgroup.mul_mem _ (TableB.scalar_mem_normalizer H ⟨c⁻¹, rfl⟩) hBnorm
    have hMnorm : ι M ∈ N := by rw [hιM]; exact hMnorm'
    refine ⟨c, M, hMnorm, hB, ?_⟩
    have heq : (⟨ι M, hMnorm⟩ : N) =
        (⟨Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ * B, hMnorm'⟩ : N) :=
      Subtype.ext hιM
    rw [heq]
    have heq2 : (⟨Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ * B, hMnorm'⟩ : N) =
        (⟨Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹,
          TableB.scalar_mem_normalizer H ⟨c⁻¹, rfl⟩⟩ : N) * ⟨B, hBnorm⟩ :=
      Subtype.ext rfl
    rw [heq2, map_mul, TableB.projConj_of_scalar H ⟨c⁻¹, rfl⟩, one_mul]
    exact hBeq.symm
  refine ⟨S, hmemS, hprojS, ?_, ?_, ?_⟩
  · let f : G₀ →* MulAut (LargeEvenProj H) := ρ.comp G₀.subtype
    have hfrange : f.range = X := by
      ext x
      constructor
      · rintro ⟨M, rfl⟩
        exact (hmemG (M : N₀)).mp M.2
      · intro hxX
        obtain ⟨B, hBgu, hBgraph⟩ := hXI x hxX
        obtain ⟨c, M, hMnorm, -, hMproj⟩ := hkey B hBgu x hxX hBgraph
        exact ⟨⟨⟨M, hMnorm⟩,
          (hmemG ⟨M, hMnorm⟩).mpr (by
            change TableB.projConj H ⟨ι M, hMnorm⟩ ∈ X
            rw [hMproj]
            exact hxX)⟩, hMproj⟩
    have hker : Nat.card f.ker = Nat.card (semilinearFixedSubfield σ) - 1 := by
      rw [← Nat.card_units (semilinearFixedSubfield σ)]
      symm
      let g : (semilinearFixedSubfield σ)ˣ → f.ker := fun u =>
        ⟨⟨scal0 u, hscalG u⟩, by
          rw [MonoidHom.mem_ker]
          show ρ (scal0 u) = 1
          exact hρscal u⟩
      refine Nat.card_eq_of_bijective g ⟨?_, ?_⟩
      · intro u v huv
        have h1 : Matrix.GeneralLinearGroup.scalar (Fin d) u =
            Matrix.GeneralLinearGroup.scalar (Fin d) v :=
          congrArg (fun z : f.ker =>
            (((z : G₀) : N₀) : GL (Fin d) (semilinearFixedSubfield σ))) huv
        exact TypeA.PGLTor.scalar_injective h1
      · rintro ⟨⟨M, hMG⟩, hMker⟩
        have hMρ : ρ M = 1 := MonoidHom.mem_ker.mp hMker
        obtain ⟨u, hu⟩ := hscal M hMρ
        refine ⟨u, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact hu
    have hcardG : Nat.card G₀ =
        Nat.card X * (Nat.card (semilinearFixedSubfield σ) - 1) := by
      have h1 := Subgroup.card_ker_mul_card_range f
      rw [hfrange, hker] at h1
      rw [← h1, mul_comm]
    have hcardS : Nat.card S = Nat.card G₀ :=
      Subgroup.card_map_of_injective (K := G₀) (f := N₀.subtype) N₀.subtype_injective
    rw [hcardS, hcardG]
  · intro M hMS
    obtain ⟨x, hxG, hxM⟩ := Subgroup.mem_map.mp hMS
    have hρx : ρ x ∈ X := (hmemG x).mp hxG
    have hguF : (φ x : GL (Fin d) F) ∈ LargeEvenGUSet (Fin d) F (2 ^ n) := by
      obtain ⟨B, hBgu, hBeq⟩ := TableB.exists_eq_projConj hSgu (hXI (ρ x) hρx)
      have hBnorm : B ∈ N := hSgu hBgu
      have hz1 : TableB.projConj H (φ x * ⟨B, hBnorm⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, show TableB.projConj H (φ x) = ρ x from rfl, hBeq]
        simp
      obtain ⟨c, hc⟩ := hU2 _ hz1
      have hceq : (φ x : GL (Fin d) F) =
          Matrix.GeneralLinearGroup.scalar (Fin d) c * B := by
        rw [hc]
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hceq]
      exact kgLangTorA_gu_scalar_mul hF hBgu c
    obtain ⟨M', hM'gu, hM'eq⟩ :=
      kgLangTorA_uni_descend hF hn hp hp2 hσ hguF
        (kgLangS1AUniFixedAux_map_fixed σ
          (x : GL (Fin d) (semilinearFixedSubfield σ)))
    have hM'M : M' = M := by
      have h1 : ι M' = ι M := by
        rw [hM'eq]
        exact congrArg ι hxM
      exact kgLangS1AUniFixedAux_map_injective
        (ι := (semilinearFixedSubfield σ).subtype)
        (semilinearFixedSubfield σ).subtype_injective h1
    rwa [hM'M] at hM'gu
  · intro B hBgu x hxX hBx
    obtain ⟨c, M, hMnorm, hB, hMproj⟩ := hkey B hBgu x hxX hBx
    exact ⟨c, M, (hmemS M).mpr ⟨hMnorm, by rw [hMproj]; exact hxX⟩, hB⟩

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockCore
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldSUDelta
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagUnitary
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepWitt
public import CFSG.Open.StatedSUFieldChange
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.RankThree.PartOne.CTP.PhanBridge

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open (StatedLieTag)
open Matrix
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)


private lemma rckConverseSU_map_primeFormUnitary_eq_GUFull {m g : ℕ} {F E : Type}
    [Field F] [Field E] (σ : F ≃+* E) (h : UnitaryFieldData 2 (g + 1) F) :
    (primeFormUnitary h (1 : GL (Fin m) F)).map
        (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m) σ).toMonoidHom =
      ClassicalBlocks.GUFull m (2 ^ (g + 1)) E := by
  let Q := 2 ^ (g + 1)
  have hbarMap : ∀ A : Matrix (Fin m) (Fin m) F, A.map h.bar = A.map (· ^ Q) := by
    intro A
    ext i j
    simp only [Matrix.map_apply, h.bar_apply, Q]
  apply le_antisymm
  · rintro B ⟨A, hA, rfl⟩
    have hA' := mem_primeFormUnitary.mp hA
    have hA'' : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ *
        (A : Matrix (Fin m) (Fin m) F) = 1 := by
      simpa only [Units.val_one, Matrix.mul_one] using hA'
    rw [ClassicalBlocks.GUFull]
    refine Subgroup.subset_closure ?_
    rw [Set.mem_setOf_eq]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [CFSG.Adapters.RankTwoModelTransports.glCongr_coe,
      CFSG.Adapters.RankTwoModelTransports.hermitian_map_ringEquiv,
      ← hbarMap A, hA'', Matrix.map_one _ (map_zero σ) (map_one σ)]
  · rw [ClassicalBlocks.GUFull, Subgroup.closure_le]
    intro B hB
    let A : GL (Fin m) F :=
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m) σ).symm B
    have hBA : CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m) σ A = B :=
      MulEquiv.apply_symm_apply _ B
    have hA : A ∈ primeFormUnitary h (1 : GL (Fin m) F) := by
      rw [mem_primeFormUnitary]
      have hBA' : (A : Matrix (Fin m) (Fin m) F).map σ =
          (B : Matrix (Fin m) (Fin m) E) := by
        rw [← CFSG.Adapters.RankTwoModelTransports.glCongr_coe σ A, hBA]
      have hmap := CFSG.Adapters.RankTwoModelTransports.hermitian_map_ringEquiv σ Q
        (A : Matrix (Fin m) (Fin m) F)
      rw [hBA', hB] at hmap
      have h1 : ((A : Matrix (Fin m) (Fin m) F).map (· ^ Q))ᵀ *
          (A : Matrix (Fin m) (Fin m) F) = 1 := by
        have h2 := congrArg (fun M => M.map σ.symm) hmap.symm
        simpa [Matrix.map_map, Matrix.map_id, Function.comp_def] using h2
      rw [hbarMap]
      simpa only [Units.val_one, Matrix.mul_one] using h1
    exact Subgroup.mem_map.mpr ⟨A, hA, hBA⟩

private lemma rckConverseSU_statedSU_le_primeFormUnitary {m g : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 (g + 1) F) :
    CFSG.Open.StatedSU m (2 ^ (g + 1)) F ≤ primeFormUnitary h (1 : GL (Fin m) F) := by
  rw [CFSG.Open.StatedSU, Subgroup.closure_le]
  intro A hA
  refine mem_primeFormUnitary.mpr ?_
  have hbar : (A : Matrix (Fin m) (Fin m) F).map h.bar =
      (A : Matrix (Fin m) (Fin m) F).map (· ^ (2 ^ (g + 1))) := by
    ext i j
    simp [Matrix.map_apply, h.bar_apply]
  rw [hbar]
  simpa only [Units.val_one, Matrix.mul_one] using hA.2

private lemma rckConverseSU_exists_preimage {m g : ℕ} {F E : Type} [Field F] [Field E]
    (σ : F ≃+* E) (h : UnitaryFieldData 2 (g + 1) F) :
    ∀ c ∈ ClassicalBlocks.GUFull m (2 ^ (g + 1)) E,
      ∃ A : GL (Fin m) F, A ∈ primeFormUnitary h (1 : GL (Fin m) F) ∧
        CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m) σ A = c := by
  intro c hc
  rw [← rckConverseSU_map_primeFormUnitary_eq_GUFull (m := m) (g := g) σ h] at hc
  exact hc

private lemma rckConverseSU_exists_kappa {m g : ℕ} {E : Type} [Field E]
    [Fact (Nat.Prime 2)]
    (hF : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2)
    (h : UnitaryFieldData 2 (g + 1) (GaloisField 2 (2 * (g + 1))))
    (σ : GaloisField 2 (2 * (g + 1)) ≃+* E)
    (P : GL (Fin m) (GaloisField 2 (2 * (g + 1))))
    (hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * (g + 1)))) *
      (P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * (g + 1)))) = antidiag m) :
    ∃ κ : (ggU .PSU m (g + 1)).K →*
        ↥(ClassicalBlocks.GUFull m (2 ^ (g + 1)) E),
      Function.Injective κ ∧
      κ.range = (CFSG.Open.StatedSU m (2 ^ (g + 1)) E).subgroupOf
        (ClassicalBlocks.GUFull m (2 ^ (g + 1)) E) ∧
      (∀ z, (κ z : GL (Fin m) E) =
        CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m) σ
          (SURep.ggFrameEquiv hF P hP z)) := by
  let e := SURep.ggFrameEquiv hF P hP
  let μ : GL (Fin m) (GaloisField 2 (2 * (g + 1))) ≃* GL (Fin m) E :=
    CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m) σ
  have hGU := rckConverseSU_map_primeFormUnitary_eq_GUFull (m := m) (g := g)
    (F := GaloisField 2 (2 * (g + 1))) σ h
  have hSUleU := rckConverseSU_statedSU_le_primeFormUnitary (m := m) (g := g)
    (F := GaloisField 2 (2 * (g + 1))) h
  have hmem : ∀ A ∈ CFSG.Open.StatedSU m (2 ^ (g + 1)) (GaloisField 2 (2 * (g + 1))),
      μ A ∈ ClassicalBlocks.GUFull m (2 ^ (g + 1)) E := by
    intro A hA
    rw [← hGU]
    exact Subgroup.mem_map_of_mem μ.toMonoidHom (hSUleU hA)
  let κ₁ : ↥(CFSG.Open.StatedSU m (2 ^ (g + 1)) (GaloisField 2 (2 * (g + 1)))) →*
      ↥(ClassicalBlocks.GUFull m (2 ^ (g + 1)) E) :=
    { toFun := fun A => ⟨μ A, hmem A A.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun A B => by
        apply Subtype.ext
        simp }
  let κ : (ggU .PSU m (g + 1)).K →*
      ↥(ClassicalBlocks.GUFull m (2 ^ (g + 1)) E) := κ₁.comp e.toMonoidHom
  have hκe : ∀ z, (κ z : GL (Fin m) E) =
      CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m) σ
        (SURep.ggFrameEquiv hF P hP z) := fun z => rfl
  refine ⟨κ, ?_, ?_, hκe⟩
  · intro z z' hzz'
    have h1 : e z = e z' := by
      apply Subtype.ext
      exact μ.injective (congrArg
        (fun y : ↥(ClassicalBlocks.GUFull m (2 ^ (g + 1)) E) =>
          (y : GL (Fin m) E)) hzz')
    exact e.injective h1
  · ext y
    constructor
    · intro hy
      rw [MonoidHom.mem_range] at hy
      obtain ⟨z, rfl⟩ := hy
      rw [Subgroup.mem_subgroupOf]
      change μ (e z) ∈ CFSG.Open.StatedSU m (2 ^ (g + 1)) E
      rw [← CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU σ m (2 ^ (g + 1))]
      exact Subgroup.mem_map_of_mem μ.toMonoidHom (e z).2
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      rw [MonoidHom.mem_range]
      rw [← CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU σ m (2 ^ (g + 1))] at hy
      obtain ⟨A, hA, hAy⟩ := Subgroup.mem_map.mp hy
      obtain ⟨z, hz⟩ := e.surjective ⟨A, hA⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change μ (e z) = (y : GL (Fin m) E)
      rw [hz]
      simpa using hAy

private lemma rckConverseSU_converse {m g : ℕ} {E X : Type} [Field E] [Group X]
    [Fact (Nat.Prime 2)]
    (hm : 4 ≤ m)
    (hF : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2)
    (h : UnitaryFieldData 2 (g + 1) (GaloisField 2 (2 * (g + 1))))
    (σ : GaloisField 2 (2 * (g + 1)) ≃+* E)
    (P : GL (Fin m) (GaloisField 2 (2 * (g + 1))))
    (hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * (g + 1)))) *
      (P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * (g + 1)))) = antidiag m)
    {κ : (ggU .PSU m (g + 1)).K →*
      ↥(ClassicalBlocks.GUFull m (2 ^ (g + 1)) E)}
    (hκe : ∀ z, (κ z : GL (Fin m) E) =
      CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m) σ
        (SURep.ggFrameEquiv hF P hP z))
    {c : ↥(ClassicalBlocks.GUFull m (2 ^ (g + 1)) E)}
    {φ : (ggU .PSU m (g + 1)).K →* X} {b : X}
    (hb : ∀ z z', κ z' = c * κ z * c⁻¹ → b⁻¹ * φ z * b = φ z')
    {A : GL (Fin m) (GaloisField 2 (2 * (g + 1)))}
    (hA : A ∈ primeFormUnitary h (1 : GL (Fin m) (GaloisField 2 (2 * (g + 1)))))
    (hcA : CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m) σ A =
      (c : GL (Fin m) E)) :
    GGPsiInnerDiag (ggU .PSU m (g + 1)).D φ b := by
  let φ' : SU (unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) m →* X := φ
  have hy : ∀ x x' : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (g + 1)
      (GaloisField 2 (2 * (g + 1))) m),
      (x' : GL (Fin m) (GaloisField 2 (2 * (g + 1)))) = A * x * A⁻¹ →
      b⁻¹ * SURep.ggFrameU hF φ' P hP x * b = SURep.ggFrameU hF φ' P hP x' := by
    intro x x' hxx'
    have hκ : κ (show (ggU .PSU m (g + 1)).K from (SURep.ggFrameEquiv hF P hP).symm x') =
        c * κ (show (ggU .PSU m (g + 1)).K from (SURep.ggFrameEquiv hF P hP).symm x) * c⁻¹ := by
      apply Subtype.ext
      change (κ (show (ggU .PSU m (g + 1)).K from (SURep.ggFrameEquiv hF P hP).symm x') : GL (Fin m) E) =
        (c : GL (Fin m) E) *
          (κ (show (ggU .PSU m (g + 1)).K from (SURep.ggFrameEquiv hF P hP).symm x) : GL (Fin m) E) *
          (c : GL (Fin m) E)⁻¹
      rw [hκe, hκe]
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hxx', map_mul, map_mul,
        map_inv, hcA]
    have hb' := hb (show (ggU .PSU m (g + 1)).K from (SURep.ggFrameEquiv hF P hP).symm x)
      (show (ggU .PSU m (g + 1)).K from (SURep.ggFrameEquiv hF P hP).symm x') hκ
    change b⁻¹ * φ ((SURep.ggFrameEquiv hF P hP).symm x) * b =
      φ ((SURep.ggFrameEquiv hF P hP).symm x')
    exact hb'
  exact CFSG.StandardType.OrdPFieldNsUD.ggPsiInnerDiag_of_frame_conj hF h hm hP hA hy

theorem exists_rckModelConverse_SU {m g : ℕ} (hm : 4 ≤ m) {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ (g + 1)) ^ 2) :
    ∃ κ : (ggU .PSU m (g + 1)).K →* ↥(ClassicalBlocks.GUFull m (2 ^ (g + 1)) E),
      RCKModelConverse ((CFSG.Open.StatedSU m (2 ^ (g + 1)) E).subgroupOf
        (ClassicalBlocks.GUFull m (2 ^ (g + 1)) E)) .PSU m (g + 1) κ := by
  let F := GaloisField 2 (2 * (g + 1))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hF : Nat.card F = (2 ^ (g + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (g + 1) (by omega)
  let h : UnitaryFieldData 2 (g + 1) F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨σ⟩ : Nonempty (F ≃+* E) :=
    CFSG.RankThree.PartOne.CTP.nonempty_ringEquiv_of_natCard_eq (hF.trans hE.symm)
  obtain ⟨P, hP⟩ := Unitary.exists_wittMatrix hF m
  obtain ⟨κ, hinj, hrange, hκe⟩ :=
    rckConverseSU_exists_kappa (m := m) (g := g) (E := E) hF h σ P hP
  have hpre := rckConverseSU_exists_preimage (m := m) (g := g) (F := F) (E := E) σ h
  refine ⟨κ, hinj, hrange, ?_⟩
  intro c _ X _ φ b hb
  obtain ⟨A, hA, hcA⟩ := hpre (c : GL (Fin m) E) c.2
  exact rckConverseSU_converse (m := m) (g := g) (E := E) (X := X) hm hF h σ P hP
    hκe hb hA hcA

end CFSG.StandardType.RCKRP

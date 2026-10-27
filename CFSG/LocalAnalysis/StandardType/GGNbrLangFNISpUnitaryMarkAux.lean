module

public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagUnitary
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestUnitary
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpPrimary
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization
public import CFSG.GroupTheory.PerfectCentralizer
public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryComponent
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09Field

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.ClassicalBlocks
open CFSG.Open (StatedSU StatedSL)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormFieldHom isPrimeFormGram_one)
open CFSG.StandardType.InndiagSU (projEquiv projEquiv_mk projEquiv_symm_mk)
open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Steinberg (fixedSubfield hypElt coe_hypElt hypMat)
open CFSG.LieType.Universal.Unitary (SUid_eq_statedSU conjEquiv)
open CFSG.LieType.BorelTits (exists_unitaryInvolution_eq_neg unitaryInvolution)
open CFSG.LocalAnalysis.GLTheoremA.YS09Field (su_map_mem)

theorem kgfniSpUMark_symm_primeFormFieldHom_graph {K : Type} [Field K] {d n : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K) (hd : 1 ≤ d)
    (σ : K ≃+* K) :
    LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (fun s s' => ((s' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ)
      ((MulAut.congr (projEquiv (h := h) hd)).symm
        (primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ)) := by
  intro s s' hss'
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  change (projEquiv (h := h) hd).symm
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldAut h
        (isPrimeFormGram_one (K := K) (n := d)) σ
        (projEquiv (h := h) hd (s : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) =
      (s' : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
  rw [projEquiv_mk, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldAut_mk,
    projEquiv_symm_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  change ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ (s : GL (Fin d) K) :
      GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = _
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]
  exact hss'.symm


theorem kgfniSpUMark_not_induced_high {m f : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hK : Nat.card E = (2 ^ f) ^ 2) (hm : 3 ≤ m) (h32 : (m, 2 ^ f) ≠ (3, 2))
    (B : GL (Fin m) E) (hB : B ∈ GUFull m (2 ^ f) E)
    (τ : E ≃+* E) (hτ : τ ≠ 1) (hτodd : Odd (orderOf τ))
    (g : MulAut ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)))
    (hg : ∀ x : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)),
      ((g x : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f))) : GL (Fin m) E) =
        B * Matrix.GeneralLinearGroup.map τ.toRingHom
          ((x : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f))) : GL (Fin m) E) * B⁻¹)
    (hsimple : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin m) E (2 ^ f))))
    (hna : ∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin m) E (2 ^ f)), a * b ≠ b * a)
    (hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) =
      (LargeEvenScalars (Fin m) E).subgroupOf (LargeEvenSUGroup (Fin m) E (2 ^ f))) :
    ¬ ∃ φ ∈ Subgroup.closure
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin m) E (2 ^ f)))
          (LargeEvenGUSet (Fin m) E (2 ^ f))),
      LargeEvenInduces (QuotientGroup.quotientMulEquivOfEq hcenter)
        (fun j k : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) => k = g j) φ := by
  classical
  let SU := LargeEvenSUGroup (Fin m) E (2 ^ f)
  let R := LargeEvenProj SU
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk SU)
      (LargeEvenGUSet (Fin m) E (2 ^ f))
  let F : Set (MulAut R) :=
    LargeEvenMatFieldImage (LargeEvenProjMk SU)
  let θ : SU ⧸ Subgroup.center SU ≃* R := QuotientGroup.quotientMulEquivOfEq hcenter
  have hd1 : 1 ≤ m := by omega
  have hUF : UnitaryFieldData 2 f E :=
    ⟨Nat.prime_two, by
      rcases Nat.eq_zero_or_pos f with h0 | h
      · rw [h0, pow_zero, one_pow] at hK
        have := Finite.one_lt_card (α := E)
        omega
      · exact h,
      by rw [hK, pow_two, ← pow_add]; ring⟩
  have hne1 : orderOf τ ≠ 1 := by
    simpa [orderOf_eq_one_iff] using hτ
  have h32' : ¬(m = 3 ∧ 2 ^ f = 2) := fun h => h32 (by rw [h.1, h.2])
  have hraw := RecipeFieldSU.ggRawInnField_unitary (h := hUF) (hK := hK) (hd := hm)
    (hq := h32') (p := orderOf τ) hne1
  have hdata := hraw hsimple hna
  obtain ⟨hmul, hinv, hinn, hFnot⟩ := hdata
  let φτ : MulAut R := (MulAut.congr (projEquiv (h := hUF) hd1)).symm
    (primeFormFieldHom hUF (isPrimeFormGram_one (K := E) (n := m)) τ)
  have hφτ_mem : φτ ∈ F := RawAutSU.symm_primeFormFieldHom_mem (h := hUF) (d := m) hd1 τ
  have hφτ_graph : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin m) E (2 ^ f)))
      (fun s s' : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) =>
        ((s' : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) =
          ((s : GL (Fin m) E) : Matrix (Fin m) (Fin m) E).map τ) φτ :=
    kgfniSpUMark_symm_primeFormFieldHom_graph (h := hUF) hd1 τ
  have hφτord : orderOf φτ = orderOf τ := by
    have h2 : orderOf (primeFormFieldHom hUF (isPrimeFormGram_one (K := E) (n := m)) τ) =
        orderOf τ :=
      orderOf_injective _ (RecipeFieldSpU.primeFormFieldHom_injective (h := hUF) hm h32') τ
    rw [show φτ = (MulAut.congr (projEquiv (h := hUF) hd1)).symm
      (primeFormFieldHom hUF (isPrimeFormGram_one (K := E) (n := m)) τ) from rfl,
      MulEquiv.orderOf_eq, h2]
  have hφτnotI : φτ ∉ I := hFnot φτ hφτ_mem hφτord
  rintro ⟨φ, hφcl, hφind⟩
  have hφI : φ ∈ I := by
    let J : Subgroup (MulAut R) :=
      { carrier := I
        one_mem' := by simpa using hinn 1
        mul_mem' := fun ha hb => hmul _ ha _ hb
        inv_mem' := fun hx => hinv _ hx }
    exact (Subgroup.closure_le (K := J)).mpr subset_rfl hφcl
  have hBinv : B⁻¹ ∈ GUFull m (2 ^ f) E := (GUFull m (2 ^ f) E).inv_mem hB
  obtain ⟨φB, hφBI, hφBind⟩ :=
    unitaryMarking_conj_mem_of_mem_unitaryFull (m := m) (Q := 2 ^ f) (p := 2) (f := f)
      hUF rfl hcenter hBinv
  have hφeq : φ = φB * φτ := by
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hgl : Matrix.GeneralLinearGroup.map τ.toRingHom ((x : SU) : GL (Fin m) E) ∈ SU :=
      su_map_mem τ ((x : SU) : GL (Fin m) E) x.2
    let y : SU := ⟨Matrix.GeneralLinearGroup.map τ.toRingHom ((x : SU) : GL (Fin m) E), hgl⟩
    have hy : B * Matrix.GeneralLinearGroup.map τ.toRingHom ((x : SU) : GL (Fin m) E) * B⁻¹ ∈ SU :=
      guFull_conj_mem_statedSU (m := m) (Q := 2 ^ f) (p := 2) (f := f) hUF rfl hB y y.2
    let z : SU :=
      ⟨B * Matrix.GeneralLinearGroup.map τ.toRingHom ((x : SU) : GL (Fin m) E) * B⁻¹, hy⟩
    have hφτx : φτ (θ (QuotientGroup.mk x)) = θ (QuotientGroup.mk y) :=
      hφτ_graph x y rfl
    have hφBx : φB (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk z) := by
      apply hφBind y z
      change ((z : SU) : GL (Fin m) E) = (B⁻¹)⁻¹ * ((y : SU) : GL (Fin m) E) * B⁻¹
      simp [z, y]
    have hzx : z = g x := by
      apply Subtype.ext
      change B * Matrix.GeneralLinearGroup.map τ.toRingHom ((x : SU) : GL (Fin m) E) * B⁻¹ =
        ((g x : SU) : GL (Fin m) E)
      rw [hg x]
    calc φ (θ (QuotientGroup.mk x)) = θ (QuotientGroup.mk (g x)) := hφind x (g x) rfl
      _ = θ (QuotientGroup.mk z) := by rw [hzx]
      _ = φB (φτ (θ (QuotientGroup.mk x))) := by rw [hφτx, hφBx]
  have hφτeq : φτ = φB⁻¹ * φ := by
    rw [hφeq]
    group
  have hφτI : φτ ∈ I := by
    rw [hφτeq]
    exact hmul (φB⁻¹) (hinv φB hφBI) φ hφI
  exact hφτnotI hφτI

theorem kgfniSpUMark_marking_high {m f : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hK : Nat.card E = (2 ^ f) ^ 2) (hm : 3 ≤ m) (h32 : (m, 2 ^ f) ≠ (3, 2))
    (B : GL (Fin m) E) (hB : B ∈ GUFull m (2 ^ f) E)
    (τ : E ≃+* E) (hτ : τ ≠ 1) (hτodd : Odd (orderOf τ))
    (g : MulAut ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)))
    (hg : ∀ x : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)),
      ((g x : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f))) : GL (Fin m) E) =
        B * Matrix.GeneralLinearGroup.map τ.toRingHom
          ((x : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f))) : GL (Fin m) E) * B⁻¹) :
    LargeEvenMarking ↥(LargeEvenSUGroup (Fin m) E (2 ^ f))
      (fun _ _ _ I _ θ => ¬ ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ (fun j k => k = g j) φ) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqs := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := f) (F := E) (n := m) hK hm h32
  have hperf : Group.IsPerfect ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) := hqs.1.1
  have hsimp : IsSimpleGroup
      (↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) ⧸
        Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ f))) := hqs.1.2.1
  have hnab : ∃ a b : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) ⧸
      Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)), a * b ≠ b * a := hqs.1.2.2
  have hlab : LargeEvenInLambda2 (⟨.twA, m - 1, f⟩ : LargeEvenLabel) :=
    (unitaryLabel_data (p := 2) (Q := 2 ^ f) (E := E) (m := m) (f := f) rfl hK rfl hm h32).2
  refine ⟨Group.isPerfect_def.mp hperf, ⟨⟨.twA, m - 1, f⟩, hlab, ?_⟩⟩
  change LargeEvenRawDatum (⟨.twA, m - 1, f⟩ : LargeEvenLabel) _
  simp only [LargeEvenRawDatum, LargeEvenRecipeUnitary]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  refine ⟨E, inferInstance, inferInstance, hK, ?_⟩
  let SU := LargeEvenSUGroup (Fin m) E (2 ^ f)
  let R := LargeEvenProj SU
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk SU)
      (LargeEvenGUSet (Fin m) E (2 ^ f))
  let θ : SU ⧸ Subgroup.center SU ≃* R := QuotientGroup.quotientMulEquivOfEq hqs.2
  letI : IsSimpleGroup (SU ⧸ Subgroup.center SU) := hsimp
  have hna : ∃ a b : R, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨θ a, θ b, ?_⟩
    intro h
    apply hab
    have h1 : θ (a * b) = θ (b * a) := by simpa only [map_mul] using h
    exact θ.injective h1
  refine ⟨?_, hna, ⟨θ, ?_⟩⟩
  · exact θ.symm.isSimpleGroup
  · exact kgfniSpUMark_not_induced_high hK hm h32 B hB τ hτ hτodd g hg
      θ.symm.isSimpleGroup hna hqs.2

theorem kgfniSpUMark_fixedSubfield_restricts {f : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hK : Nat.card E = (2 ^ f) ^ 2) (τ : E ≃+* E) (hτ : τ ≠ 1) (hτodd : Odd (orderOf τ)) :
    ∃ a : CFSG.LieType.Steinberg.fixedSubfield E 2 f, τ (a : E) ≠ (a : E) := by
  let F := CFSG.LieType.Steinberg.fixedSubfield E 2 f
  by_contra h
  push Not at h
  have hcardF : Nat.card F = 2 ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield (p := 2) (f := f) hK
  have hfixcard := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf E τ
  have hmem : ∀ a : F, (a : E) ∈ FixedPoints.subfield (Subgroup.zpowers τ) E := by
    intro a
    change (a : E) ∈ MulAction.fixedPoints (Subgroup.zpowers τ) E
    rw [MulAction.mem_fixedPoints]
    intro m
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp m.2
    have hfix : (a : E) ∈ MulAction.fixedBy E τ := h a
    have hfixj := MulAction.mem_fixedBy_zpow hfix j
    change (m : E ≃+* E) • (a : E) = (a : E)
    rw [show (m : E ≃+* E) = τ ^ j from hj.symm]
    exact hfixj
  have hle : Nat.card F ≤ Nat.card (FixedPoints.subfield (Subgroup.zpowers τ) E) := by
    refine Nat.card_le_card_of_injective
      (fun a : F => (⟨(a : E), hmem a⟩ : FixedPoints.subfield (Subgroup.zpowers τ) E)) ?_
    intro a b hab
    exact Subtype.ext (congrArg (fun x : FixedPoints.subfield (Subgroup.zpowers τ) E =>
      (x : E)) hab)
  have hpow : (2 ^ f) ^ orderOf τ ≤ (2 ^ f) ^ 2 := by
    calc (2 ^ f) ^ orderOf τ = Nat.card F ^ orderOf τ := by rw [hcardF]
      _ ≤ Nat.card (FixedPoints.subfield (Subgroup.zpowers τ) E) ^ orderOf τ :=
          Nat.pow_le_pow_left hle _
      _ = Nat.card E := hfixcard.symm
      _ = (2 ^ f) ^ 2 := hK
  have hbase : 1 < 2 ^ f := by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by
        rcases Nat.eq_zero_or_pos f with h0 | h
        · rw [h0, pow_zero, one_pow] at hK
          have := Finite.one_lt_card (α := E)
          omega
        · exact h)
  have hn2 : orderOf τ ≤ 2 := (Nat.pow_le_pow_iff_right hbase).mp hpow
  have hn1 : orderOf τ ≠ 1 := by
    simpa [orderOf_eq_one_iff] using hτ
  rcases hτodd with ⟨k, hk⟩
  omega

end CFSG.StandardType


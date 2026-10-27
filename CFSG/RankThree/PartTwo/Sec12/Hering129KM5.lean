module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofSolv
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projImage)
open CFSG.Open (StatedScalars)
open Matrix (ProjGenLinGroup)

namespace Hering129KM5

theorem exists_mem_ker_of_isPerfect {G G' A : Type*} [Group G] [Group G'] [CommGroup A]
    (ψ : G →* G') (φ : G →* A) {S : Subgroup G} {X : Subgroup G'} (hX : Group.IsPerfect X)
    (hXS : X ≤ S.map ψ) {m : G'} (hm : m ∈ X) : ∃ s ∈ S, φ s = 1 ∧ ψ s = m := by
  have hP : (S ⊓ X.comap ψ).map ψ = X := by
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact hs.2
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := hXS hx
      exact ⟨s, ⟨hs, hx⟩, rfl⟩
  have hPP : ⁅S ⊓ X.comap ψ, S ⊓ X.comap ψ⁆ ≤ S ⊓ φ.ker := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha.1 hb.1) (inv_mem ha.1)) (inv_mem hb.1)
    · rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_comm (φ a) (φ b), mul_inv_cancel_right, mul_inv_cancel]
  have hm' : m ∈ (⁅S ⊓ X.comap ψ, S ⊓ X.comap ψ⁆).map ψ := by
    rw [Subgroup.map_commutator, hP, Subgroup.isPerfect_iff.mp hX]
    exact hm
  obtain ⟨s, hs, rfl⟩ := hm'
  exact ⟨s, (hPP hs).1, (hPP hs).2, rfl⟩

theorem shape_of_quad {K : Type} [Field K] {a b c e : K} (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (ha : (a - 1) * (a - e) = 0) (hb : (b - 1) * (b - e) = 0) (hc : (c - 1) * (c - e) = 0)
    (hdet : a * b * c = e) :
    (a = e ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = e ∧ c = 1) ∨ (a = 1 ∧ b = 1 ∧ c = e) := by
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he3
  have key : ∀ u : K, (u - 1) * (u - e) = 0 → u = 1 ∨ u = e := fun u hu =>
    (mul_eq_zero.mp hu).imp sub_eq_zero.mp sub_eq_zero.mp
  have h2 : e * e ≠ e := fun h => he1 (mul_left_cancel₀ he0 (by rw [h, mul_one]))
  have h3 : e * e * e ≠ e := fun h => by
    have hee : e * e = 1 := mul_left_cancel₀ he0 (by rw [← mul_assoc, h, mul_one])
    exact he1 (by linear_combination he3 - e * hee)
  rcases key a ha with ha' | ha' <;> rcases key b hb with hb' | hb' <;>
    rcases key c hc with hc' | hc' <;> rw [ha', hb', hc'] at hdet ⊢
  · exact absurd (by linear_combination -hdet) he1
  · exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact absurd (by linear_combination hdet) h2
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact absurd (by linear_combination hdet) h2
  · exact absurd (by linear_combination hdet) h2
  · exact absurd hdet h3

variable {K : Type} [Field K]

theorem mem_centMod_of_commute {L : Subgroup (GL (Fin 3) K)} {y l : GL (Fin 3) K} (hl : l ∈ L)
    (h : ProjGenLinGroup.mk l * ProjGenLinGroup.mk y =
      ProjGenLinGroup.mk y * ProjGenLinGroup.mk l) :
    l ∈ Sec4.centMod L y := by
  refine Sec4.mem_centMod_iff_scalar.mpr ⟨hl, l * y * l⁻¹ * y⁻¹, ?_, by group⟩
  rw [← Sec4.mk_eq_one_iff_mem_statedScalars]
  simp only [map_mul, map_inv]
  rw [h]
  group

theorem le_map_centMod {L : Subgroup (GL (Fin 3) K)} {y : GL (Fin 3) K}
    {Xm : Subgroup (ProjGenLinGroup (Fin 3) K)} (hXL : Xm ≤ projImage L)
    (hXc : Xm ≤ Subgroup.centralizer ({ProjGenLinGroup.mk y} : Set (ProjGenLinGroup (Fin 3) K))) :
    Xm ≤ (Sec4.centMod L y).map ProjGenLinGroup.mk := by
  intro m hm
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp (hXL hm)
  exact ⟨l, mem_centMod_of_commute hl (Subgroup.mem_centralizer_singleton_iff.mp (hXc hm)), rfl⟩

theorem not_isSolvable_centMod {L : Subgroup (GL (Fin 3) K)} {y : GL (Fin 3) K}
    {Xm : Subgroup (ProjGenLinGroup (Fin 3) K)} (hXns : ¬ Group.IsSolvable Xm)
    (hle : Xm ≤ (Sec4.centMod L y).map ProjGenLinGroup.mk) :
    ¬ Group.IsSolvable (Sec4.centMod L y) := by
  intro hs
  have : Group.IsSolvable ((Sec4.centMod L y).map ProjGenLinGroup.mk) :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
  exact hXns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))

theorem blockHom_eq_one_of_mem_statedScalars {B : GL (Fin 2) K}
    (hB : Matrix.GeneralLinearGroup.det B = 1)
    (hs : Sec4.blockHom B ∈ StatedScalars (Fin 3) K) : Sec4.blockHom B = 1 := by
  obtain ⟨c, hc⟩ := hs
  have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Sec4.coe_blockHom, hB, inv_one, Units.val_one] at h00
  have hc1 : c = 1 := Units.ext (by simpa [Sec4.blockMat] using h00)
  rw [← hc, hc1, map_one]

theorem exists_shape {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {e : Kˣ} (he3 : (e : K) ^ 3 = 1)
    (he1 : e ≠ 1) {g : GL (Fin 3) K}
    (hc : g⁻¹ * Sec4.diagE e * g * Sec4.diagTau hτ =
      Sec4.diagTau hτ * (g⁻¹ * Sec4.diagE e * g)) :
    ∃ a b c : Kˣ, ((a = e ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = e ∧ c = 1) ∨ (a = 1 ∧ b = 1 ∧ c = e)) ∧
      g⁻¹ * Sec4.diagE e * g = Sec4.diagUnits a b c := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  set M : Matrix (Fin 3) (Fin 3) K :=
    ((g⁻¹ * Sec4.diagE e * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hcm : M * Matrix.diagonal ![τ, τ ^ 2, 1] = Matrix.diagonal ![τ, τ ^ 2, 1] * M := by
    rw [hM, ← Sec4.coe_diagTau_eq_diagonal hτ, ← Units.val_mul, ← Units.val_mul, hc]
  have z := fun i j (hij : (![τ, τ ^ 2, 1] : Fin 3 → K) i ≠ ![τ, τ ^ 2, 1] j) =>
    Sec4.entry_eq_zero_of_commute_diagonal hcm hij
  have m01 : M 0 1 = 0 := z 0 1 (by simpa using hττ2)
  have m02 : M 0 2 = 0 := z 0 2 (by simpa using hτ1)
  have m10 : M 1 0 = 0 := z 1 0 (by simpa using hττ2.symm)
  have m12 : M 1 2 = 0 := z 1 2 (by simpa using hτ2)
  have m20 : M 2 0 = 0 := z 2 0 (by simpa using hτ1.symm)
  have m21 : M 2 1 = 0 := z 2 1 (by simpa using hτ2.symm)
  set G : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) with hGdef
  set Gi : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hGidef
  set N : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![(e : K), 1, 1] with hNdef
  have hG : Gi * G = 1 := by rw [hGidef, hGdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hG' : G * Gi = 1 := by rw [hGidef, hGdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMe : M = Gi * N * G := by rw [hM, Units.val_mul, Units.val_mul, Sec4.coe_diagE]
  have hN : (N - 1) * (N - (e : K) • 1) = 0 := by
    rw [hNdef]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.diagonal_apply]
  have hquad : (M - 1) * (M - (e : K) • 1) = 0 := by
    have h1 : M - 1 = Gi * (N - 1) * G := by
      rw [hMe, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hG]
    have h2 : M - (e : K) • 1 = Gi * (N - (e : K) • 1) * G := by
      rw [hMe, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        hG]
    rw [h1, h2]
    calc Gi * (N - 1) * G * (Gi * (N - (e : K) • 1) * G) =
        Gi * ((N - 1) * (G * Gi) * (N - (e : K) • 1)) * G := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hG', Matrix.mul_one, hN, Matrix.mul_zero, Matrix.zero_mul]
  have q : ∀ i : Fin 3, ((M - 1) * (M - (e : K) • 1)) i i = 0 := fun i => by rw [hquad]; rfl
  have q0 : (M 0 0 - 1) * (M 0 0 - e) = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, m01, m02] using q 0
  have q1 : (M 1 1 - 1) * (M 1 1 - e) = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, m10, m12] using q 1
  have q2 : (M 2 2 - 1) * (M 2 2 - e) = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, m20, m21] using q 2
  have hdet : M 0 0 * M 1 1 * M 2 2 = e := by
    have h := congrArg Units.val (Sec4.det_inv_conj g (Sec4.diagE e))
    rw [Sec4.det_diagE, Matrix.GeneralLinearGroup.val_det_apply, ← hM, Matrix.det_fin_three,
      m01, m02, m10, m12, m20, m21] at h
    simpa using h
  have hshape := shape_of_quad he3 (fun h => he1 (Units.ext h)) q0 q1 q2 hdet
  have h0 : M 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact e.ne_zero hdet.symm
  have h1 : M 1 1 ≠ 0 := fun h => by
    rw [h, mul_zero, zero_mul] at hdet
    exact e.ne_zero hdet.symm
  have h2 : M 2 2 ≠ 0 := fun h => by
    rw [h, mul_zero] at hdet
    exact e.ne_zero hdet.symm
  refine ⟨Units.mk0 _ h0, Units.mk0 _ h1, Units.mk0 _ h2, ?_, ?_⟩
  · simp only [Units.ext_iff, Units.val_mk0, Units.val_one]
    exact hshape
  · apply Units.ext
    change M = _
    rw [Sec4.coe_diagUnits]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m01, m02, m10, m12, m20, m21]

variable {p f : ℕ} {π : Bool}

theorem exists_block (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    {y z g₁ : GL (Fin 3) K} {e : Kˣ} (he3 : (e : K) ^ 3 = 1) (he1 : e ≠ 1)
    (hz : z ∈ StatedScalars (Fin 3) K) (hg₁ : g₁ ∈ Sec4.glPi π 3 (p ^ f) K)
    (hD : g₁⁻¹ * (y * z) * g₁ = Sec4.diagE e) {m : ProjGenLinGroup (Fin 3) K}
    (hmL : m ∈ projImage (Sec4.slPi π 3 (p ^ f) K))
    (hmc : m * ProjGenLinGroup.mk y = ProjGenLinGroup.mk y * m) :
    ∃ B ∈ Sec4.glPi π 2 (p ^ f) K, m = ProjGenLinGroup.mk (g₁ * Sec4.blockHom B * g₁⁻¹) := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := fun h => by
    subst h
    exact hK.unitary
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hmL
  have hl' : g₁⁻¹ * l * g₁ ∈ Sec4.slPi π 3 (p ^ f) K := by
    simpa using Sec4.conj_mem_slPi hπ (inv_mem hg₁) hl
  have hmz : ProjGenLinGroup.mk z = 1 := Sec4.mk_eq_one_iff_mem_statedScalars.mpr hz
  have hcomm : ProjGenLinGroup.mk (g₁⁻¹ * l * g₁) * ProjGenLinGroup.mk (Sec4.diagE e) =
      ProjGenLinGroup.mk (Sec4.diagE e) * ProjGenLinGroup.mk (g₁⁻¹ * l * g₁) := by
    rw [← hD]
    simp only [map_mul, map_inv, hmz, mul_one]
    calc (ProjGenLinGroup.mk g₁)⁻¹ * ProjGenLinGroup.mk l * ProjGenLinGroup.mk g₁ *
          ((ProjGenLinGroup.mk g₁)⁻¹ * ProjGenLinGroup.mk y * ProjGenLinGroup.mk g₁) =
        (ProjGenLinGroup.mk g₁)⁻¹ * (ProjGenLinGroup.mk l * ProjGenLinGroup.mk y) *
          ProjGenLinGroup.mk g₁ := by group
      _ = (ProjGenLinGroup.mk g₁)⁻¹ * (ProjGenLinGroup.mk y * ProjGenLinGroup.mk l) *
          ProjGenLinGroup.mk g₁ := by rw [hmc]
      _ = (ProjGenLinGroup.mk g₁)⁻¹ * ProjGenLinGroup.mk y * ProjGenLinGroup.mk g₁ *
          ((ProjGenLinGroup.mk g₁)⁻¹ * ProjGenLinGroup.mk l * ProjGenLinGroup.mk g₁) := by group
  have hC := mem_centMod_of_commute hl' hcomm
  rw [Sec4.centMod_diagE_eq (p := p) (f := f) π he3 (hK.three_ne_zero hq),
    Sec4.centralizer_diagE_eq hK he1] at hC
  obtain ⟨B, hB, hBl⟩ := Subgroup.mem_map.mp hC
  refine ⟨B, hB, ?_⟩
  rw [hBl]
  congr 1
  group

end Hering129KM5


theorem exists_frame {K : Type} [Field K] {p f : ℕ} {π : Bool}
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ Sec4.glPi π 3 (p ^ f) K) (hyZ : y ∉ StatedScalars (Fin 3) K)
    (hy3 : y ^ 3 ∈ StatedScalars (Fin 3) K)
    {m₀ : ProjGenLinGroup (Fin 3) K} (hm₀L : m₀ ∈ projImage (Sec4.slPi π 3 (p ^ f) K))
    (hm₀1 : m₀ ≠ 1) (hm₀3 : m₀ ^ 3 = 1)
    {Xm : Subgroup (ProjGenLinGroup (Fin 3) K)} (hXL : Xm ≤ projImage (Sec4.slPi π 3 (p ^ f) K))
    (hXc : Xm ≤ Subgroup.centralizer ({ProjGenLinGroup.mk y} : Set (ProjGenLinGroup (Fin 3) K)))
    (hXp : Group.IsPerfect Xm) (hXns : ¬ Group.IsSolvable Xm) (hm₀X : m₀ ∈ Xm) :
    ∃ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 ∧ ∃ g ∈ Sec4.glPi π 3 (p ^ f) K,
      m₀ = ProjGenLinGroup.mk (g * Sec4.diagTau hτ * g⁻¹) ∧
      ∃ (e : Kˣ) (a b c : Kˣ), (e : K) ^ 3 = 1 ∧ e ≠ 1 ∧
        ((a = e ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = e ∧ c = 1) ∨ (a = 1 ∧ b = 1 ∧ c = e)) ∧
        ProjGenLinGroup.mk y = ProjGenLinGroup.mk (g * Sec4.diagUnits a b c * g⁻¹) := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := fun h => by
    subst h
    exact hK.unitary
  have hq' : π = false → Sec4.ModThree false (p ^ f) := fun h => by
    subst h
    exact hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hzPi := Sec4.zPi_eq hπ hq' hτ hτ1
  have hyZ' : y ∉ Sec4.zPi π 3 (p ^ f) K := fun h => hyZ (by
    rw [hzPi] at h
    exact h.2)
  have hy3' : y ^ 3 ∈ Sec4.zPi π 3 (p ^ f) K := by
    rw [hzPi]
    exact ⟨pow_mem hyH 3, hy3⟩
  have hns := Hering129KM5.not_isSolvable_centMod hXns (Hering129KM5.le_map_centMod hXL hXc)
  obtain ⟨e, he3, he1, z, hz, g₁, hg₁, hD⟩ : Sec4.Type123 π (p ^ f) K y 2 := by
    rcases Sec4.type123_exhaust hK hq hyH hyZ' hy3' with h | h | h
    · exact absurd (Sec4.Res424Six.isSolvable_centMod_of_type13 hK hq hyH hyZ' hy3' (Or.inl h))
        hns
    · exact h
    · exact absurd (Sec4.Res424Six.isSolvable_centMod_of_type13 hK hq hyH hyZ' hy3' (Or.inr h))
        hns
  have hzS : z ∈ StatedScalars (Fin 3) K := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  let ψ : GL (Fin 2) K →* ProjGenLinGroup (Fin 3) K :=
    MonoidHom.comp ProjGenLinGroup.mk ((MulAut.conj g₁).toMonoidHom.comp Sec4.blockHom)
  have hXψ : Xm ≤ (Sec4.glPi π 2 (p ^ f) K).map ψ := by
    intro m hm
    obtain ⟨B, hB, rfl⟩ := Hering129KM5.exists_block hK hq he3 he1 hzS hg₁ hD (hXL hm)
      (Subgroup.mem_centralizer_singleton_iff.mp (hXc hm))
    exact ⟨B, hB, rfl⟩
  obtain ⟨B, hB, hBdet, hBm⟩ :=
    Hering129KM5.exists_mem_ker_of_isPerfect ψ Matrix.GeneralLinearGroup.det hXp hXψ hm₀X
  have hm₀x : m₀ = ProjGenLinGroup.mk (g₁ * Sec4.blockHom B * g₁⁻¹) := hBm.symm
  have hxL : Sec4.blockHom B ∈ Sec4.slPi π 3 (p ^ f) K := Sec4.blockHom_mem_slPi hK hB
  have hconj : ∀ w : GL (Fin 3) K, ProjGenLinGroup.mk (g₁ * w * g₁⁻¹) = 1 →
      w ∈ StatedScalars (Fin 3) K := by
    intro w hw
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars]
    have h : ProjGenLinGroup.mk w = (ProjGenLinGroup.mk g₁)⁻¹ *
        ProjGenLinGroup.mk (g₁ * w * g₁⁻¹) * ProjGenLinGroup.mk g₁ := by
      simp only [map_mul, map_inv]
      group
    rw [h, hw]
    group
  have hx3 : Sec4.blockHom B ^ 3 = 1 := by
    have hs : Sec4.blockHom B ^ 3 ∈ StatedScalars (Fin 3) K :=
      hconj _ (by rw [← conj_pow, map_pow, ← hm₀x, hm₀3])
    rw [← map_pow] at hs ⊢
    exact Hering129KM5.blockHom_eq_one_of_mem_statedScalars (by rw [map_pow, hBdet, one_pow]) hs
  have hxZ : Sec4.blockHom B ∉ Sec4.zPi π 3 (p ^ f) K := by
    intro h
    apply hm₀1
    rw [hm₀x, map_mul, map_mul, Sec4.mk_eq_one_iff_mem_statedScalars.mpr
      (Sec4.mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h), mul_one, map_inv, mul_inv_cancel]
  have hx1 : Sec4.blockHom B ≠ 1 := fun h => hxZ (h ▸ one_mem _)
  have hxo : orderOf (Sec4.blockHom B) = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨g₂, hg₂, hx₂⟩ := Sec4.rank3II_4_10_three hK hq hτ hτ1 hxL hxZ hxo
  have hc : g₂⁻¹ * Sec4.diagE e * g₂ * Sec4.diagTau hτ =
      Sec4.diagTau hτ * (g₂⁻¹ * Sec4.diagE e * g₂) := by
    rw [← hx₂]
    calc g₂⁻¹ * Sec4.diagE e * g₂ * (g₂⁻¹ * Sec4.blockHom B * g₂) =
        g₂⁻¹ * (Sec4.diagE e * Sec4.blockHom B) * g₂ := by group
      _ = g₂⁻¹ * (Sec4.blockHom B * Sec4.diagE e) * g₂ := by rw [Sec4.blockHom_commute e B]
      _ = g₂⁻¹ * Sec4.blockHom B * g₂ * (g₂⁻¹ * Sec4.diagE e * g₂) := by group
  obtain ⟨a, b, c, hshape, habc⟩ := Hering129KM5.exists_shape hτ hτ1 he3 he1 hc
  refine ⟨τ, hτ, hτ1, g₁ * g₂, mul_mem hg₁ hg₂, ?_, e, a, b, c, he3, he1, hshape, ?_⟩
  · rw [hm₀x, ← hx₂]
    congr 1
    group
  · rw [← habc]
    have hyz : y * z = g₁ * Sec4.diagE e * g₁⁻¹ := by
      rw [← hD]
      group
    calc ProjGenLinGroup.mk y = ProjGenLinGroup.mk (y * z) := by
          rw [map_mul, Sec4.mk_eq_one_iff_mem_statedScalars.mpr hzS, mul_one]
      _ = ProjGenLinGroup.mk (g₁ * g₂ * (g₂⁻¹ * Sec4.diagE e * g₂) * (g₁ * g₂)⁻¹) := by
          rw [hyz]
          congr 1
          group

end CFSG.RankThree.PartTwo.Sec12

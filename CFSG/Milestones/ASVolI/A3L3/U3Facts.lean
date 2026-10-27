module

public import CFSG.Milestones.ASVolI.A3L3.U3Data
public import CFSG.Milestones.ASVolI.A3L3.Finish
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts

variable {p : ℕ} {K : Type} [Field K]

theorem burnsideA315y_u3_block (two_ne : (2 : K) ≠ 0) {g : GL (Fin 3) K}
    (hg : g * negDiag3 K = negDiag3 K * g) :
    (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 :=
  block_eq_zero_of_commute_negDiag two_ne
    (by rw [← coe_negDiag3, ← Units.val_mul, hg, Units.val_mul])

theorem burnsideA315y_u3_norm22 (hU : UnitaryFieldData p 1 K) (two_ne : (2 : K) ≠ 0)
    {g : ↥(unitaryIsom3 hU)} (hg : (g : GL (Fin 3) K) * negDiag3 K = negDiag3 K * g) :
    hU.bar (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2) *
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  obtain ⟨h02, h12, -, -⟩ := burnsideA315y_u3_block two_ne hg
  have h := burnsideA315y_u3_entry hU g 2 2
  rw [h02, h12] at h
  simpa using h

theorem burnsideA315y_u3_hΓscal (hU : UnitaryFieldData p 1 K) (two_ne : (2 : K) ≠ 0) :
    ∀ g : ↥(unitaryIsom3 hU), (g : GL (Fin 3) K) * negDiag3 K = negDiag3 K * g → ∀ μ : Kˣ,
      (μ : K) = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 →
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∈ unitaryIsom3 hU := by
  intro g hg μ hμ
  exact burnsideA315y_u3_scalar_mem hU (by rw [hμ]; exact burnsideA315y_u3_norm22 hU two_ne hg)

theorem burnsideA315y_u3_hΓdiag (hU : UnitaryFieldData p 1 K) (two_ne : (2 : K) ≠ 0) :
    ∀ g : ↥(unitaryIsom3 hU), (g : GL (Fin 3) K) * negDiag3 K = negDiag3 K * g →
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 → ∀ (n : ℕ) (s : Kˣ),
        (s : K) = (ulBlock ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).det ^ n →
          burnsideA315y_dgl s ∈ unitaryIsom3 hU := by
  intro g hg h22 n s hs
  obtain ⟨h02, h12, h20, h21⟩ := burnsideA315y_u3_block two_ne hg
  have hdet : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (ulBlock ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_two, h02, h12, h20, h21, h22]
    simp only [ulBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    ring
  have hn := burnsideA315y_u3_norm_det hU g
  rw [hdet] at hn
  refine burnsideA315y_u3_dgl_mem hU ?_
  rw [hs, map_pow, ← mul_pow, hn, one_pow]

theorem burnsideA315y_u3_N1 (hU : UnitaryFieldData p 1 K) {u : Kˣ}
    (hu : u ∈ (Units.map hU.normHom).ker) : hU.bar (u : K) * u = 1 := by
  rw [mul_comm]
  exact hU.mem_ker_normUnits.mp hu

theorem burnsideA315y_u3_mem_N1 (hU : UnitaryFieldData p 1 K) {u : Kˣ}
    (hu : hU.bar (u : K) * u = 1) : u ∈ (Units.map hU.normHom).ker := by
  rw [hU.mem_ker_normUnits, UnitaryFieldData.norm, mul_comm]
  exact hu

theorem burnsideA315y_u3_card_N1 (hU : UnitaryFieldData p 1 K) :
    Nat.card ↥(Units.map hU.normHom).ker = p + 1 := by
  rw [hU.card_ker_normUnits_and_surjective.1, pow_one]

theorem burnsideA315y_u3_diag_comm_blk (A : Matrix (Fin 2) (Fin 2) K) (u w : K) :
    blkMat A 1 * diagonal ![u, u, w] = diagonal ![u, u, w] * blkMat A 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat, mul_comm]

theorem burnsideA315y_u3_negDiag_blk :
    diagonal ![(-1 : K), -1, 1] = blkMat (-1 : Matrix (Fin 2) (Fin 2) K) 1 :=
  burnsideA315y_blkMat_neg_one.symm

section Model

variable (hU : UnitaryFieldData p 1 K) [Finite K] (two_ne : (2 : K) ≠ 0) {x y cc : K}
  (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) (hx : hU.bar x = x) (hy : hU.bar y = y)
  (hc : hU.bar cc = -cc)

local notation "MU" => burnsideA315y_u3Model hU two_ne hdet hx hy hc

theorem burnsideA315y_u3_diag_mem_D₀ {g : ↥(MU).Γ} {u w : K}
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![u, u, w]) :
    g ∈ (MU).D₀ := by
  show g ∈ Subgroup.centralizer ({(MU).zh, (MU).Da, (MU).Db} : Set ↥(MU).Γ)
  rw [Subgroup.mem_centralizer_iff]
  have key : ∀ (A : Matrix (Fin 2) (Fin 2) K) (h : ↥(MU).Γ),
      ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = blkMat A 1 → h * g = g * h := by
    intro A h hA
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hA, hg]
    exact burnsideA315y_u3_diag_comm_blk A u w
  rintro h (rfl | rfl | rfl)
  · exact key (-1) _ (by
      show ((negDiag3 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
      rw [coe_negDiag3, burnsideA315y_u3_negDiag_blk])
  · exact key _ _ (MU).Da_val
  · exact key _ _ (MU).Db_val

theorem burnsideA315y_u3_e22_range : (MU).e22.range = (Units.map hU.normHom).ker := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    refine burnsideA315y_u3_mem_N1 hU ?_
    rw [burnsideA315y_Model.e22_apply]
    exact burnsideA315y_u3_norm22 hU two_ne ((MU).C₁_comm g.2)
  · intro u hu
    have hu' := burnsideA315y_u3_N1 hU hu
    have hu0 : (u : K) ≠ 0 := u.ne_zero
    set A : Matrix (Fin 3) (Fin 3) K := diagonal ![(u : K)⁻¹, 1, (u : K)] with hAdef
    have hA : (A.map hU.bar)ᵀ * A = 1 := by
      have hbu : hU.bar (u : K) ≠ 0 := (hU.bar_eq_zero_iff).not.mpr hu0
      have hinv : (hU.bar (u : K))⁻¹ * (u : K)⁻¹ = 1 := by
        rw [← mul_inv, hu', inv_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hAdef, hu', hinv, map_inv₀]
    set g := burnsideA315y_u3Mk hU A hA with hgdef
    have hgC : g ∈ (MU).C₁ := by
      refine ⟨?_, ?_⟩
      · show (A : Matrix (Fin 3) (Fin 3) K).det = 1
        rw [hAdef, det_diagonal, Fin.prod_univ_three]
        simp [hu0]
      · apply Subtype.ext
        apply Units.ext
        show A * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * A
        rw [hAdef, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext k
        exact mul_comm _ _
    refine ⟨⟨g, hgC⟩, Units.ext ?_⟩
    rw [burnsideA315y_Model.e22_apply]
    show A 2 2 = (u : K)
    simp [hAdef]

theorem burnsideA315y_u3_card_D₀C₁ :
    Nat.card ↥((MU).D₀ ⊓ (MU).C₁) = Nat.card ↥(Units.map hU.normHom).ker := by
  symm
  have hmat : ∀ u : ↥(Units.map hU.normHom).ker,
      ((diagonal ![((u : Kˣ) : K), (u : Kˣ), ((u : Kˣ) : K)⁻¹ ^ 2]).map hU.bar)ᵀ *
        diagonal ![((u : Kˣ) : K), (u : Kˣ), ((u : Kˣ) : K)⁻¹ ^ 2] = 1 := by
    intro u
    have hu' := burnsideA315y_u3_N1 hU u.2
    have hinv : (hU.bar ((u : Kˣ) : K) ^ 2)⁻¹ * (((u : Kˣ) : K) ^ 2)⁻¹ = 1 := by
      rw [← mul_inv, ← mul_pow, hu', one_pow, inv_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hu', hinv, map_inv₀]
  let f : ↥(Units.map hU.normHom).ker → ↥((MU).D₀ ⊓ (MU).C₁) := fun u =>
    ⟨burnsideA315y_u3Mk hU _ (hmat u), burnsideA315y_u3_diag_mem_D₀ hU two_ne hdet hx hy hc rfl,
      by
        refine ⟨?_, ?_⟩
        · show (diagonal ![((u : Kˣ) : K), (u : Kˣ), ((u : Kˣ) : K)⁻¹ ^ 2]).det = 1
          rw [det_diagonal, Fin.prod_univ_three]
          have hu0 : ((u : Kˣ) : K) ≠ 0 := (u : Kˣ).ne_zero
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons]
          field_simp
        · apply Subtype.ext
          apply Units.ext
          show diagonal ![((u : Kˣ) : K), (u : Kˣ), ((u : Kˣ) : K)⁻¹ ^ 2] *
              diagonal ![-1, -1, 1] =
            diagonal ![-1, -1, 1] * diagonal ![((u : Kˣ) : K), (u : Kˣ), ((u : Kˣ) : K)⁻¹ ^ 2]
          rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
          congr 1
          funext k
          exact mul_comm _ _⟩
  refine Nat.card_eq_of_bijective f ⟨fun u v huv => ?_, fun d => ?_⟩
  · have h := congrArg (fun g : ↥((MU).D₀ ⊓ (MU).C₁) =>
      (((g : ↥(MU).Γ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) huv
    simp only [f] at h
    rw [burnsideA315y_u3Mk_val, burnsideA315y_u3Mk_val] at h
    simp only [diagonal_apply_eq, Matrix.cons_val_zero] at h
    exact Subtype.ext (Units.ext h)
  · obtain ⟨d, hdD, hdC⟩ := d
    obtain ⟨d01, d10, d11, d02, d12, d20, d21⟩ := (MU).D₀_form hdD
    have hn := burnsideA315y_u3_entry hU d 0 0
    set D := (((d : ↥(MU).Γ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hD
    rw [d10, d20] at hn
    simp only [map_zero, zero_mul, add_zero, Matrix.one_apply_eq] at hn
    have hu0 : D 0 0 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hn
      exact zero_ne_one hn
    set u : Kˣ := Units.mk0 (D 0 0) hu0 with hudef
    have huN : u ∈ (Units.map hU.normHom).ker := burnsideA315y_u3_mem_N1 hU hn
    have hdet1 : D.det = 1 := hdC.1
    have h22 : D 2 2 = (D 0 0)⁻¹ ^ 2 := by
      rw [Matrix.det_fin_three, d01, d10, d11, d02, d12, d20, d21] at hdet1
      field_simp
      linear_combination hdet1
    refine ⟨⟨u, huN⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    show diagonal ![(u : K), (u : K), (u : K)⁻¹ ^ 2] = D
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hudef, d01, d10, d11, d02, d12, d20, d21, h22]

theorem burnsideA315y_u3_K₀_equiv : Nonempty (↥(unitarySU p 1 K 2) ≃* ↥(MU).K₀) := by
  have hmem : ∀ A : ↥(unitarySU p 1 K 2),
      ((blkMat ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1).map hU.bar)ᵀ *
        blkMat ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 = 1 :=
    fun A => burnsideA315y_u3_blkMat_mem hU ((mem_unitarySU_iff hU).mp A.2).2
  let φ : ↥(unitarySU p 1 K 2) →* ↥(MU).Γ :=
    { toFun := fun A => burnsideA315y_u3Mk hU _ (hmem A)
      map_one' := by
        apply Subtype.ext
        apply Units.ext
        show blkMat (((1 : ↥(unitarySU p 1 K 2)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 =
          1
        rw [Subgroup.coe_one, Units.val_one, blkMat_one]
      map_mul' := fun A B => by
        apply Subtype.ext
        apply Units.ext
        show blkMat (((A * B : ↥(unitarySU p 1 K 2)) : GL (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) 1 =
          blkMat ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 *
            blkMat ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1
        rw [blkMat_mul, mul_one, Subgroup.coe_mul, Units.val_mul] }
  have hφ : ∀ A, (((φ A : ↥(MU).Γ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blkMat ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 := fun A => rfl
  have hinj : Function.Injective φ := by
    intro A B hAB
    have h := congrArg (fun g : ↥(MU).Γ =>
      ulBlock (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) hAB
    simp only [hφ, ulBlock_blkMat] at h
    exact Subtype.ext (Units.ext h)
  have hrange : φ.range = (MU).K₀ := by
    apply le_antisymm
    · rintro _ ⟨A, rfl⟩
      refine ⟨?_, ?_⟩
      · show (((φ A : ↥(MU).Γ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
        rw [hφ, det_blkMat, mul_one]
        exact ((mem_unitarySU_iff hU).mp A.2).1
      · show burnsideA315y_Model.burnsideA315y_IsK
          (((φ A : ↥(MU).Γ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        rw [hφ]
        simp [burnsideA315y_Model.burnsideA315y_IsK, blkMat]
    · intro g hg
      obtain ⟨hdet, h02, h12, h20, h21, h22⟩ := hg
      set G := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hG
      have hGblk : G = blkMat (ulBlock G) 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [blkMat, ulBlock, h02, h12, h20, h21, h22]
      have hAdet : (ulBlock G).det = 1 := by
        rw [hGblk, det_blkMat, mul_one] at hdet
        exact hdet
      have hAu : ((ulBlock G).map hU.bar)ᵀ * ulBlock G = 1 := by
        have h1 := burnsideA315y_u3_mem hU g
        rw [← hG, hGblk, burnsideA315y_u3_blkMat_conjTr, blkMat_mul, mul_one] at h1
        have h2 := congrArg ulBlock h1
        rwa [ulBlock_blkMat, ulBlock_one] at h2
      let Agl : GL (Fin 2) K := ⟨ulBlock G, ((ulBlock G).map hU.bar)ᵀ,
        mul_eq_one_comm.mp hAu, hAu⟩
      have hAS : Agl ∈ unitarySU p 1 K 2 := (mem_unitarySU_iff hU).mpr ⟨hAdet, hAu⟩
      exact ⟨⟨Agl, hAS⟩, Subtype.ext (Units.ext hGblk.symm)⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem burnsideA315y_u3_hK [Fact p.Prime] (hcard : Nat.card K = p ^ 2) :
    Nonempty (↥(MU).K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  obtain ⟨e₁⟩ := burnsideA315y_u3_K₀_equiv hU two_ne hdet hx hy hc
  obtain ⟨e₂⟩ := CFSG.Quasithin.A312U3.exists_su2_equiv (p := p) (F := K) hcard
  exact ⟨(MU).K₀EquivK.symm.trans (e₁.symm.trans e₂.symm)⟩

theorem burnsideA315y_u3_card_K₀ [Fact p.Prime] (hcard : Nat.card K = p ^ 2) :
    Nat.card ↥(MU).K₀ = p * (p ^ 2 - 1) := by
  obtain ⟨e⟩ := burnsideA315y_u3_hK hU two_ne hdet hx hy hc hcard
  rw [← (MU).card_K, Nat.card_congr e.toEquiv, burnsideA315y_card_SL2,
    CFSG.GorensteinWalter.pgl2_card_formula, Nat.card_zmod]

theorem burnsideA315y_u3_card_C₁ [Fact p.Prime] (hcard : Nat.card K = p ^ 2) :
    Nat.card ↥(MU).C₁ = p * (p ^ 2 - 1) * (p + 1) := by
  rw [(MU).card_C₁, burnsideA315y_u3_card_K₀ hU two_ne hdet hx hy hc hcard,
    burnsideA315y_u3_e22_range hU two_ne hdet hx hy hc, burnsideA315y_u3_card_N1]

theorem burnsideA315y_u3_card_Γ₁ : Nat.card ↥(MU).Γ₁ = Nat.card ↥(unitarySU p 1 K 3) := by
  have h : (MU).Γ₁.map (MU).Γ.subtype = unitarySU p 1 K 3 := by
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact (mem_unitarySU_iff hU).mpr ⟨hg', g'.2⟩
    · intro hg
      exact ⟨⟨g, unitarySU_le_unitaryIsom3 (h := hU) hg⟩, ((mem_unitarySU_iff hU).mp hg).1, rfl⟩
  calc Nat.card ↥(MU).Γ₁ = Nat.card ↥((MU).Γ₁.map (MU).Γ.subtype) :=
        (Subgroup.card_map_of_injective (MU).Γ.subtype_injective).symm
    _ = Nat.card ↥(unitarySU p 1 K 3) := Nat.card_congr (MulEquiv.subgroupCongr h).toEquiv

end Model

theorem burnsideA315y_u3_card_SU3 (hU : UnitaryFieldData p 1 K) :
    (Nat.card ↥(unitarySU p 1 K 3) : ℤ) =
      (p : ℤ) ^ 3 * (((p : ℤ) ^ 2 - 1) * ((p : ℤ) ^ 3 + 1)) := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hU
  have h1 : Nat.card ↥(unitarySU p 1 K 3) = Nat.card ↥(hypSU hU 1 1) :=
    (Nat.card_congr (hypTransport hU hR).toEquiv).symm
  rw [h1, (card_hypSU hU (r := 1) (ε := 1) (by norm_num)).1]
  have hIcc : Finset.Icc 2 (2 * 1 + 1) = {2, 3} := by decide
  rw [hIcc, Finset.prod_pair (by norm_num)]
  norm_num

section Model2

variable (hU : UnitaryFieldData p 1 K) [Finite K] (two_ne : (2 : K) ≠ 0) {x y cc : K}
  (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) (hx : hU.bar x = x) (hy : hU.bar y = y)
  (hc : hU.bar cc = -cc)

local notation "MU" => burnsideA315y_u3Model hU two_ne hdet hx hy hc

theorem burnsideA315y_u3_hC₁ [Fact p.Prime] (hp2 : p ≠ 2) (hcard : Nat.card K = p ^ 2) :
    ¬ 2 ∣ (MU).C₁.relIndex (MU).Γ₁ := by
  have hp : p.Prime := Fact.out
  have h1 := Subgroup.relIndex_mul_card (MU).C₁ (MU).Γ₁
  rw [inf_eq_left.mpr (MU).C₁_le_Γ₁, burnsideA315y_u3_card_C₁ hU two_ne hdet hx hy hc hcard,
    burnsideA315y_u3_card_Γ₁ hU two_ne hdet hx hy hc] at h1
  have h2 := burnsideA315y_u3_card_SU3 hU
  set r := (MU).C₁.relIndex (MU).Γ₁ with hr
  have hp2' : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have h3 : (r : ℤ) * ((p : ℤ) * ((p : ℤ) ^ 2 - 1) * ((p : ℤ) + 1)) =
      (p : ℤ) ^ 3 * (((p : ℤ) ^ 2 - 1) * ((p : ℤ) ^ 3 + 1)) := by
    rw [← h2, ← h1]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp2', Nat.cast_pow]
  have hp2z : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hne : (p : ℤ) * ((p : ℤ) ^ 2 - 1) * ((p : ℤ) + 1) ≠ 0 := by
    have ha : (0 : ℤ) < p := by omega
    have hb : (0 : ℤ) < (p : ℤ) ^ 2 - 1 := by nlinarith
    have hc' : (0 : ℤ) < (p : ℤ) + 1 := by omega
    positivity
  have h4 : (r : ℤ) = (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 - p + 1) := by
    apply mul_right_cancel₀ hne
    rw [h3]
    ring
  intro h2r
  have h5 : (2 : ℤ) ∣ (r : ℤ) := by exact_mod_cast h2r
  rw [h4] at h5
  have hpo : Odd (p : ℤ) := by
    obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  have hodd : Odd ((p : ℤ) ^ 2 * ((p : ℤ) ^ 2 - p + 1)) := by
    refine hpo.pow.mul ?_
    have he : Even ((p : ℤ) * ((p : ℤ) - 1)) := Int.even_mul_pred_self _
    rw [show (p : ℤ) ^ 2 - p + 1 = (p : ℤ) * ((p : ℤ) - 1) + 1 by ring]
    exact he.add_one
  exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h5)

theorem burnsideA315y_u3_hΓ₁ : ¬ p ∣ (MU).Γ₁.index := by
  let det' : ↥(MU).Γ →* Kˣ := Matrix.GeneralLinearGroup.det.comp (MU).Γ.subtype
  have hdet' : ∀ g : ↥(MU).Γ,
      ((det' g : Kˣ) : K) = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := fun g => rfl
  have hker : (MU).Γ₁ = det'.ker := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      apply Units.ext
      rw [hdet', Units.val_one]
      exact h
    · intro h
      have h1 := congrArg Units.val h
      rw [hdet', Units.val_one] at h1
      exact h1
  rw [hker, Subgroup.index_ker]
  have hle : det'.range ≤ (Units.map hU.normHom).ker := by
    rintro _ ⟨g, rfl⟩
    refine burnsideA315y_u3_mem_N1 hU ?_
    rw [hdet']
    exact burnsideA315y_u3_norm_det hU g
  have h1 := Subgroup.card_dvd_of_le hle
  rw [burnsideA315y_u3_card_N1] at h1
  intro hp
  have h2 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp (hp.trans h1)
  exact hU.prime.one_lt.ne' (Nat.dvd_one.mp h2)

theorem burnsideA315y_u3_dgl_diag (s : Kˣ) :
    ((burnsideA315y_dgl s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(s : K), s, 1] := by
  rw [burnsideA315y_dgl_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat]

theorem burnsideA315y_u3_D₀ :
    IsCyclic ↥((MU).D₀.map (MU).c) ∧ Nat.card ↥((MU).D₀.map (MU).c) ∣ p + 1 := by
  let ψ : ↥(Units.map hU.normHom).ker →* ↥(MU).Γ :=
    { toFun := fun u => ⟨burnsideA315y_dgl (u : Kˣ),
        burnsideA315y_u3_dgl_mem hU (burnsideA315y_u3_N1 hU u.2)⟩
      map_one' := by
        apply Subtype.ext
        apply Units.ext
        show ((burnsideA315y_dgl (((1 : ↥(Units.map hU.normHom).ker) : Kˣ)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = 1
        rw [burnsideA315y_dgl_val, OneMemClass.coe_one, Units.val_one, one_smul, blkMat_one]
      map_mul' := fun u v => by
        apply Subtype.ext
        apply Units.ext
        show ((burnsideA315y_dgl (((u * v : ↥(Units.map hU.normHom).ker)) : Kˣ) :
          GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            ((burnsideA315y_dgl ((u : Kˣ)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              ((burnsideA315y_dgl ((v : Kˣ)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        rw [burnsideA315y_dgl_val, burnsideA315y_dgl_val, burnsideA315y_dgl_val, blkMat_mul,
          smul_mul_smul_comm, Matrix.one_mul, mul_one, Subgroup.coe_mul, Units.val_mul] }
  have hψ : ∀ u, ψ u ∈ (MU).D₀ := fun u =>
    burnsideA315y_u3_diag_mem_D₀ hU two_ne hdet hx hy hc (burnsideA315y_u3_dgl_diag _)
  have hsurj : ∀ d ∈ (MU).D₀, ∃ u, (MU).c (ψ u) = (MU).c d := by
    intro d hd
    obtain ⟨d01, d10, d11, d02, d12, d20, d21⟩ := (MU).D₀_form hd
    have hn0 := burnsideA315y_u3_entry hU d 0 0
    have hn2 := burnsideA315y_u3_entry hU d 2 2
    set D := (((d : ↥(MU).Γ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hD
    rw [d10, d20] at hn0
    rw [d02, d12] at hn2
    simp only [map_zero, zero_mul, add_zero, zero_add, Matrix.one_apply_eq] at hn0 hn2
    have hu0 : D 0 0 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hn0
      exact zero_ne_one hn0
    have hw0 : D 2 2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hn2
      exact zero_ne_one hn2
    set u : Kˣ := Units.mk0 (D 0 0) hu0 with hudef
    set w : Kˣ := Units.mk0 (D 2 2) hw0 with hwdef
    have hbw : hU.bar (D 2 2) ≠ 0 := (hU.bar_eq_zero_iff).not.mpr hw0
    have hg : u * w⁻¹ ∈ (Units.map hU.normHom).ker := by
      refine burnsideA315y_u3_mem_N1 hU ?_
      simp only [hudef, hwdef, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_mul,
        map_inv₀]
      calc hU.bar (D 0 0) * (hU.bar (D 2 2))⁻¹ * (D 0 0 * (D 2 2)⁻¹) =
          (hU.bar (D 0 0) * D 0 0) * (hU.bar (D 2 2) * D 2 2)⁻¹ := by
            field_simp
        _ = 1 := by rw [hn0, hn2, inv_one, mul_one]
    have hσ : Matrix.GeneralLinearGroup.scalar (Fin 3) w ∈ (MU).Γ :=
      burnsideA315y_u3_scalar_mem hU (by simpa [hwdef] using hn2)
    have hdec : d = ψ ⟨u * w⁻¹, hg⟩ * ⟨_, hσ⟩ := by
      apply Subtype.ext
      apply Units.ext
      show D = ((burnsideA315y_dgl (u * w⁻¹) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((Matrix.GeneralLinearGroup.scalar (Fin 3) w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      rw [burnsideA315y_u3_dgl_diag, Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hudef, hwdef, d01, d10, d11, d02, d12, d20, d21, Matrix.scalar_apply, hw0]
    refine ⟨⟨u * w⁻¹, hg⟩, ?_⟩
    rw [hdec, map_mul, ((MU).ker_c ⟨_, hσ⟩).mpr ⟨w, rfl⟩, mul_one]
  obtain ⟨h1, h2⟩ := (MU).D₀_cyclic ψ hψ hsurj
  exact ⟨h1, by rwa [burnsideA315y_u3_card_N1] at h2⟩

theorem burnsideA315y_u3_hLeq :
    (MU).L = (MulAut.conj : unitaryPSU hU 3 →* MulAut (unitaryPSU hU 3)).range := by
  ext φ
  rw [burnsideA315y_Model.mem_L]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgS : (g : GL (Fin 3) K) ∈ unitarySU p 1 K 3 := (mem_unitarySU_iff hU).mpr ⟨hg, g.2⟩
    refine ⟨((⟨(g : GL (Fin 3) K), hgS⟩ : ↥(unitarySU p 1 K 3)) : unitaryPSU hU 3), ?_⟩
    rw [conj_mk_eq_psuConj]
    rfl
  · rintro ⟨q, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨(g : GL (Fin 3) K), unitarySU_le_unitaryIsom3 (h := hU) g.2⟩,
      ((mem_unitarySU_iff hU).mp g.2).1, ?_⟩
    rw [conj_mk_eq_psuConj]
    rfl

theorem burnsideA315y_u3_hoddc :
    ∀ φ : MulAut (unitaryPSU hU 3), Odd (orderOf φ) → φ ∈ (MU).c.range := by
  intro φ hodd
  have hp := hU.prime
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · exfalso
      have hp2 : p = 2 := by omega
      subst hp2
      have : (2 : K) = 0 := by
        have : CharP K 2 := hU.charP
        exact_mod_cast CharP.cast_eq_zero K 2
      exact two_ne this
    · exact h
  have hq : 2 < p ^ 1 := by rw [pow_one]; omega
  obtain ⟨A, σ, hφ⟩ := exists_psuConj_mul_psuField hq φ
  have hcard : Nat.card K = p ^ 2 := by rw [hU.card]
  have hσ2 : σ ^ 2 = 1 := by
    have h2 := (card_ringAut_and_isCyclic hp K hcard).1
    rw [← h2]
    exact pow_card_eq_one'
  have hσσ : psuField hU σ * psuField hU σ = 1 := by rw [← map_mul, ← sq, hσ2, map_one]
  have hσinv : (psuField hU σ)⁻¹ = psuField hU σ := inv_eq_of_mul_eq_one_right hσσ
  have hsq : φ ^ 2 ∈ (psuConj hU).range := by
    refine ⟨A * ⟨CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ A,
      glAut_mem_unitaryIsom3 σ A.2⟩, ?_⟩
    rw [map_mul, ← psuField_mul_psuConj_mul_inv σ A, hσinv, hφ, sq]
    simp only [mul_assoc]
  obtain ⟨k, hk⟩ := hodd
  have hφk : φ = (φ ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf φ + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hφk]
  exact Subgroup.pow_mem _ hsq _

theorem burnsideA315y_u3_noE (B' : Subgroup (MulAut (unitaryPSU hU 3))) : ¬ (MU).DichE B' := by
  rintro ⟨E, hE, -, hshape, -⟩
  apply hE
  rw [eq_bot_iff]
  intro e he
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Subgroup.coe_one]
  rcases hshape with h | h
  · obtain ⟨a00, a01, a10, a11, a20, a21, a22⟩ := h e he
    have e02 := burnsideA315y_u3_entry hU e 0 2
    have e12 := burnsideA315y_u3_entry hU e 1 2
    rw [a00, a10, a20] at e02
    rw [a01, a11, a21] at e12
    simp at e02 e12
    exact burnsideA315y_eq_one_of_isUW (h e he) e02 e12
  · obtain ⟨a00, a01, a02, a10, a11, a12, a22⟩ := h e he
    have e20 := burnsideA315y_u3_entry hU e 2 0
    have e21 := burnsideA315y_u3_entry hU e 2 1
    rw [a02, a12, a22] at e20 e21
    simp at e20 e21
    exact burnsideA315y_eq_one_of_isUl (h e he) e20 e21

end Model2

end CFSG.ASVolI

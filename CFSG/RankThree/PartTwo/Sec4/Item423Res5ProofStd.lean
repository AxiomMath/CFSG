module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res5ProofMat
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCent
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofInndiag
public import CFSG.RankThree.PartTwo.Sec4.Item423Res5ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

namespace Res423Five

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

section Blocks

variable (hK : PiField π p f K)

include hK in
theorem cyc_mem_glPi (m : Fin 3) : cyc (K := K) m ∈ glPi π 3 (p ^ f) K :=
  slPi_le_glPi (fun h => by subst h; exact hK.unitary)
    (cyc_mem_slPi (fun h => by subst h; exact hK.unitary) m)

@[expose] noncomputable def blockAut (m : Fin 3) :
    slPi π 2 (p ^ f) K →* MulAut (projImage (slPi π 3 (p ^ f) K)) :=
  (pglConj hK).comp
    ((Subgroup.inclusion (slPi_le_glPi (fun h => by subst h; exact hK.unitary))).comp
      (Sec11.KS11LieProof.blockConj hK (cyc_mem_glPi hK m)))

theorem blockAut_apply (m : Fin 3) (B : slPi π 2 (p ^ f) K) :
    blockAut hK m B = pglConj hK ⟨cyc m * blockHom (B : GL (Fin 2) K) * (cyc m)⁻¹,
      mul_mem (mul_mem (cyc_mem_glPi hK m) (slPi_le_glPi (fun h => by subst h; exact hK.unitary)
        (blockHom_mem_slPi hK (slPi_le_glPi (fun h => by subst h; exact hK.unitary) B.2))))
        (inv_mem (cyc_mem_glPi hK m))⟩ :=
  rfl

theorem blockAut_mem_range_conj (m : Fin 3) (B : slPi π 2 (p ^ f) K) :
    blockAut hK m B ∈ (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →*
      MulAut (projImage (slPi π 3 (p ^ f) K))).range := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hL : cyc m * blockHom (B : GL (Fin 2) K) * (cyc m)⁻¹ ∈ slPi π 3 (p ^ f) K :=
    conj_mem_slPi hπ (cyc_mem_glPi hK m) (blockHom_mem_slPi hK (slPi_le_glPi hπ B.2))
  rw [blockAut_apply, ← conj_mk_eq_pglConj hK hL]
  exact ⟨_, rfl⟩

theorem blockAut_injective (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) (m : Fin 3) :
    Function.Injective (blockAut hK m) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  rw [blockAut_apply, pglConj_eq_one_iff hK hq hq2] at hB
  have h1 := Sec11.KS11LieProof.conj_mem_statedScalars_iff.mp hB
  exact Subtype.ext (Sec11.KS11LieProof.eq_one_of_blockHom_mem_statedScalars
    (Sec11.KS11LieProof.det_eq_one_of_mem_slPi hK B.2) h1)

theorem isQuasisimple_range_blockAut (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) (m : Fin 3) :
    IsQuasisimple (blockAut hK m).range :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (blockAut_injective hK hq hq2 m))
    (Sec11.KS11LieProof.isQuasisimple_slPi_two hK hq hq2)

end Blocks

section Ident

theorem blockHom_diagTwo (μ : Kˣ) :
    blockHom (Sec11.KS11LieProof.diagTwo μ : GL (Fin 2) K) = diagUnits 1 μ μ⁻¹ := by
  have hdet : GeneralLinearGroup.det (Sec11.KS11LieProof.diagTwo μ : GL (Fin 2) K) = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply, Sec11.KS11LieProof.coe_diagTwo,
      det_diagonal, Fin.prod_univ_two]; simp)
  apply Units.ext
  rw [Sec11.KS11LieProof.coe_blockHom_of_det hdet, Sec11.KS11LieProof.coe_diagTwo, coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem mk_diagUnits_smul (x a b c : Kˣ) :
    ProjGenLinGroup.mk (diagUnits (x * a) (x * b) (x * c)) =
      ProjGenLinGroup.mk (diagUnits a b c : GL (Fin 3) K) := by
  have h : diagUnits (x * a) (x * b) (x * c) =
      GeneralLinearGroup.scalar (Fin 3) x * (diagUnits a b c : GL (Fin 3) K) := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagUnits, coe_diagUnits,
      Matrix.scalar_apply, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [h, map_mul, mk_eq_one_iff_mem_statedScalars.mpr ⟨x, rfl⟩, one_mul]

theorem mk_cyc_blockHom_diagTwo {τ : Kˣ} (hτ : τ ^ 3 = 1) (m : Fin 3) :
    ProjGenLinGroup.mk (cyc m * blockHom (Sec11.KS11LieProof.diagTwo τ : GL (Fin 2) K) *
      (cyc m)⁻¹) = ProjGenLinGroup.mk (diagUnits 1 τ (τ ^ 2) : GL (Fin 3) K) := by
  have hinv : τ⁻¹ = τ ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hτ]
  rw [blockHom_diagTwo, hinv]
  fin_cases m
  · change ProjGenLinGroup.mk (1 * diagUnits 1 τ (τ ^ 2) * 1⁻¹) = _
    rw [inv_one, one_mul, mul_one]
  · change ProjGenLinGroup.mk (cycThree * diagUnits 1 τ (τ ^ 2) * cycThree⁻¹) = _
    rw [cycThree_conj_diagUnits]
    have h : diagUnits (τ ^ 2) 1 τ = diagUnits (τ ^ 2 * 1) (τ ^ 2 * τ) (τ ^ 2 * τ ^ 2) := by
      congr 1
      · rw [mul_one]
      · rw [← pow_succ, hτ]
      · rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hτ, one_mul, pow_one]
    rw [h, mk_diagUnits_smul]
  · change ProjGenLinGroup.mk (cycThree⁻¹ * diagUnits 1 τ (τ ^ 2) * cycThree⁻¹⁻¹) = _
    rw [inv_inv, cycThree_inv_conj_diagUnits]
    have h : diagUnits τ (τ ^ 2) 1 = diagUnits (τ * 1) (τ * τ) (τ * τ ^ 2) := by
      congr 1
      · rw [mul_one]
      · rw [← sq]
      · rw [← pow_succ', hτ]
    rw [h, mk_diagUnits_smul]

theorem cyc_diagE_eq (m : Fin 3) (r : Kˣ) :
    cyc m * diagE r * (cyc m)⁻¹ =
      diagUnits (if m = 0 then r else 1) (if m = 1 then r else 1) (if m = 2 then r else 1) := by
  apply Units.ext
  rw [coe_cyc_diagE, coe_diagUnits]
  congr 1
  funext i
  fin_cases m <;> fin_cases i <;> simp

end Ident

section Data

variable (hK : PiField π p f K) (hq : ModThree π (p ^ f))

theorem exists_cyc_diagE {st : rootsOfUnity 3 K × rootsOfUnity 3 K} (h1 : st ≠ 1)
    (h2 : ¬ (st.1 ≠ 1 ∧ st.2 ≠ 1 ∧ st.1 ≠ st.2)) :
    ∃ (m : Fin 3) (r : Kˣ), r ^ 3 = 1 ∧ r ≠ 1 ∧
      ProjGenLinGroup.mk ((stdDiag hK hq st : glPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        ProjGenLinGroup.mk (cyc m * diagE r * (cyc m)⁻¹) := by
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := st
  have hs3 : s ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hs
  have ht3 : t ^ 3 = 1 := (mem_rootsOfUnity _ _).mp ht
  simp only [ne_eq, not_and, not_not] at h2
  rw [coe_stdDiag]
  by_cases hs1 : (⟨s, hs⟩ : rootsOfUnity 3 K) = 1
  ·
    have hs1' : s = 1 := congrArg Subtype.val hs1
    have ht1 : t ≠ 1 := fun h => h1 (Prod.ext hs1 (Subtype.ext h))
    refine ⟨2, t, ht3, ht1, ?_⟩
    rw [cyc_diagE_eq]
    simp [hs1']
  · by_cases ht1 : (⟨t, ht⟩ : rootsOfUnity 3 K) = 1
    ·
      have ht1' : t = 1 := congrArg Subtype.val ht1
      have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
      refine ⟨1, s, hs3, hs1', ?_⟩
      rw [cyc_diagE_eq]
      simp [ht1']
    ·
      have hst : s = t := congrArg Subtype.val (h2 hs1 ht1)
      have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
      refine ⟨0, s⁻¹, by rw [inv_pow, hs3, inv_one], inv_ne_one.mpr hs1', ?_⟩
      rw [cyc_diagE_eq]
      simp only [ite_true, show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
        ite_false]
      rw [← hst, ← mk_diagUnits_smul s s⁻¹ 1 1, mul_inv_cancel, mul_one]

include hq in
theorem exists_blockHom_of_commute (hq2 : 2 < p ^ f) (m : Fin 3) {r : Kˣ} (hr3 : r ^ 3 = 1)
    (hr1 : r ≠ 1) (g y : glPi π 3 (p ^ f) K) (hg : (g : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K)
    (hy : (y : GL (Fin 3) K) = cyc m * diagE r * (cyc m)⁻¹)
    (hc : pglConj hK g * pglConj hK y = pglConj hK y * pglConj hK g) :
    ∃ A ∈ glPi π 2 (p ^ f) K, (cyc m)⁻¹ * (g : GL (Fin 3) K) * cyc m = blockHom A := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hsc := (pglConj_commute_iff hK hq hq2 _ _).mp hc
  rw [hy] at hsc
  have hg'L : (cyc m)⁻¹ * (g : GL (Fin 3) K) * cyc m ∈ slPi π 3 (p ^ f) K := by
    have := conj_mem_slPi hπ (inv_mem (cyc_mem_glPi hK m)) hg
    rwa [inv_inv] at this
  have hsc' : (cyc m)⁻¹ * (g : GL (Fin 3) K) * cyc m * diagE r *
      ((cyc m)⁻¹ * (g : GL (Fin 3) K) * cyc m)⁻¹ * (diagE r)⁻¹ ∈ StatedScalars (Fin 3) K := by
    have h1 := Sec11.KS11LieProof.conj_mem_statedScalars_iff (h := (cyc m)⁻¹).mpr hsc
    have e : (cyc m)⁻¹ * ((g : GL (Fin 3) K) * (cyc m * diagE r * (cyc m)⁻¹) *
        (g : GL (Fin 3) K)⁻¹ * (cyc m * diagE r * (cyc m)⁻¹)⁻¹) * (cyc m)⁻¹⁻¹ =
        (cyc m)⁻¹ * (g : GL (Fin 3) K) * cyc m * diagE r *
          ((cyc m)⁻¹ * (g : GL (Fin 3) K) * cyc m)⁻¹ * (diagE r)⁻¹ := by
      group
    rwa [e] at h1
  obtain ⟨z, hz⟩ := hsc'
  have hcm : (cyc m)⁻¹ * (g : GL (Fin 3) K) * cyc m ∈ centMod (slPi π 3 (p ^ f) K) (diagE r) := by
    refine mem_centMod_iff_scalar.mpr ⟨hg'L, GeneralLinearGroup.scalar (Fin 3) z, ⟨z, rfl⟩, ?_⟩
    rw [hz]
    group
  have hr3' : (r : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hr3, Units.val_one]
  rw [centMod_diagE_eq π hr3' (hK.three_ne_zero hq), centralizer_diagE_eq hK hr1] at hcm
  obtain ⟨A, hA, hAg⟩ := hcm
  exact ⟨A, hA, hAg.symm⟩

end Data

section Elements

variable (hK : PiField π p f K) (hq : ModThree π (p ^ f))

include hK hq in
theorem diagTwo_mem_slPi_of_cube {μ : Kˣ} (hμ : μ ^ 3 = 1) :
    (Sec11.KS11LieProof.diagTwo μ : GL (Fin 2) K) ∈ slPi π 2 (p ^ f) K :=
  Sec11.KS11LieProof.diagTwo_mem_slPi hK fun hπ => by
    subst hπ
    exact pow_succ_eq_one_of_modThree hq (by rw [← Units.val_pow_eq_pow_val, hμ, Units.val_one])

theorem blockAut_diagTwo (m : Fin 3) (τ : rootsOfUnity 3 K) :
    blockAut hK m ⟨Sec11.KS11LieProof.diagTwo (τ : Kˣ),
      diagTwo_mem_slPi_of_cube hK hq ((mem_rootsOfUnity _ _).mp τ.2)⟩ =
      pglConj hK (stdDiag hK hq (τ, τ ^ 2)) := by
  rw [blockAut_apply]
  apply pglConj_eq_of_mk_eq
  rw [coe_stdDiag]
  exact mk_cyc_blockHom_diagTwo ((mem_rootsOfUnity _ _).mp τ.2) m

@[expose] def stE (τ : rootsOfUnity 3 K) (m : Fin 3) : rootsOfUnity 3 K × rootsOfUnity 3 K :=
  ![(τ⁻¹, τ⁻¹), (τ, 1), (1, τ)] m

theorem mk_stdDiag_stE (τ : rootsOfUnity 3 K) (m : Fin 3) :
    ProjGenLinGroup.mk ((stdDiag hK hq (stE τ m) : glPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      ProjGenLinGroup.mk (cyc m * diagE (τ : Kˣ) * (cyc m)⁻¹) := by
  rw [coe_stdDiag, cyc_diagE_eq]
  fin_cases m
  · change ProjGenLinGroup.mk (diagUnits 1 ((τ⁻¹ : rootsOfUnity 3 K) : Kˣ)
      ((τ⁻¹ : rootsOfUnity 3 K) : Kˣ)) = _
    simp only [ite_true, show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      ite_false, Fin.zero_eta, Fin.isValue]
    rw [← mk_diagUnits_smul (τ : Kˣ) 1 _ _, mul_one, InvMemClass.coe_inv, mul_inv_cancel]
  · change ProjGenLinGroup.mk (diagUnits 1 (τ : Kˣ) ((1 : rootsOfUnity 3 K) : Kˣ)) = _
    simp
  · change ProjGenLinGroup.mk (diagUnits 1 ((1 : rootsOfUnity 3 K) : Kˣ) (τ : Kˣ)) = _
    simp

theorem stE_not_typeOne (τ : rootsOfUnity 3 K) (m : Fin 3) :
    ¬ ((stE τ m).1 ≠ 1 ∧ (stE τ m).2 ≠ 1 ∧ (stE τ m).1 ≠ (stE τ m).2) := by
  fin_cases m <;> simp [stE]

theorem not_mem_zpowers_typeOne (hq2 : 2 < p ^ f) {τ : rootsOfUnity 3 K} (hτ : τ ≠ 1)
    {st : rootsOfUnity 3 K × rootsOfUnity 3 K} (h2 : ¬ (st.1 ≠ 1 ∧ st.2 ≠ 1 ∧ st.1 ≠ st.2)) :
    pglConj hK (stdDiag hK hq (τ, τ ^ 2)) ∉
      Subgroup.zpowers (pglConj hK (stdDiag hK hq st)) := by
  rintro ⟨k, hk⟩
  have hk' : ((pglConj hK).comp (stdDiag hK hq)) (st ^ k) =
      ((pglConj hK).comp (stdDiag hK hq)) (τ, τ ^ 2) := by
    rw [map_zpow]
    exact hk
  have heq := pglConj_stdDiag_injective hK hq hq2 hk'
  have h1 : st.1 ^ k = τ := congrArg Prod.fst heq
  have h2' : st.2 ^ k = τ ^ 2 := congrArg Prod.snd heq
  have hτ3 : τ ^ 3 = 1 := Subtype.ext ((mem_rootsOfUnity _ _).mp τ.2)
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ
    calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hτ3, h]; group
  have hττ : τ ≠ τ ^ 2 := by
    intro h
    apply hτ
    calc τ = τ ^ 2 * τ⁻¹ := by group
      _ = 1 := by rw [← h]; group
  simp only [ne_eq, not_and, not_not] at h2
  by_cases hs : st.1 = 1
  · rw [hs, _root_.one_zpow] at h1
    exact hτ h1.symm
  · by_cases ht : st.2 = 1
    · rw [ht, _root_.one_zpow] at h2'
      exact hτ2 h2'.symm
    · rw [h2 hs ht] at h1
      exact hττ (h1.symm.trans h2')

end Elements

section Core

variable (hK : PiField π p f K) (hq : ModThree π (p ^ f))
  {Y : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K)))}

theorem typeTwoAt_blockIn (hq2 : 2 < p ^ f)
    (hY : (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →*
      MulAut (projImage (slPi π 3 (p ^ f) K))).range ≤ Y)
    (hBY : stdPlane hK hq ≤ Y) {b : Y} (hbB : b ∈ (stdPlane hK hq).subgroupOf Y) (hb1 : b ≠ 1)
    (m : Fin 3) {r : Kˣ} (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) (y : glPi π 3 (p ^ f) K)
    (hy : (y : GL (Fin 3) K) = cyc m * diagE r * (cyc m)⁻¹) (hb : (b : MulAut _) = pglConj hK y)
    {τ : rootsOfUnity 3 K}
    (hnot : pglConj hK (stdDiag hK hq (τ, τ ^ 2)) ∉ Subgroup.zpowers (b : MulAut _)) :
    TypeTwoAt ((MulAut.conj : projImage (slPi π 3 (p ^ f) K) →*
        MulAut (projImage (slPi π 3 (p ^ f) K))).range.subgroupOf Y)
      ((stdPlane hK hq).subgroupOf Y) b ((blockAut hK m).range.subgroupOf Y) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  have hRY : (blockAut hK m).range ≤ Y := by
    rintro _ ⟨B, rfl⟩
    exact hY (blockAut_mem_range_conj hK m B)
  have hXB : ∀ B : slPi π 2 (p ^ f) K, cyc m * blockHom (B : GL (Fin 2) K) * (cyc m)⁻¹ ∈
      glPi π 3 (p ^ f) K := fun B =>
    mul_mem (mul_mem (cyc_mem_glPi hK m) (slPi_le_glPi hπ
      (blockHom_mem_slPi hK (slPi_le_glPi hπ B.2)))) (inv_mem (cyc_mem_glPi hK m))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRY).symm
      (isQuasisimple_range_blockAut hK hq hq2 m)
  ·
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨B, hB⟩ := hx
    rw [← hB]
    exact blockAut_mem_range_conj hK m B
  ·
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨B, hB⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hb, ← hB, blockAut_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hy]
    have hc := blockHom_commute r (B : GL (Fin 2) K)
    have key : cyc m * diagE r * (cyc m)⁻¹ * (cyc m * blockHom (B : GL (Fin 2) K) * (cyc m)⁻¹) =
        cyc m * blockHom (B : GL (Fin 2) K) * (cyc m)⁻¹ * (cyc m * diagE r * (cyc m)⁻¹) :=
      calc cyc m * diagE r * (cyc m)⁻¹ * (cyc m * blockHom (B : GL (Fin 2) K) * (cyc m)⁻¹) =
          cyc m * (diagE r * blockHom (B : GL (Fin 2) K)) * (cyc m)⁻¹ := by group
        _ = cyc m * (blockHom (B : GL (Fin 2) K) * diagE r) * (cyc m)⁻¹ := by rw [hc]
        _ = cyc m * blockHom (B : GL (Fin 2) K) * (cyc m)⁻¹ * (cyc m * diagE r * (cyc m)⁻¹) := by
            group
    first | exact key | exact key.symm
  ·
    intro x hx hxb
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨w, hw⟩ := hx
    obtain ⟨g, hgL, hgH, hgw⟩ := exists_conj_eq_pglConj hK w
    have hxg : (x : MulAut _) = pglConj hK ⟨g, hgH⟩ := hw.symm.trans hgw
    have hc : pglConj hK ⟨g, hgH⟩ * pglConj hK y = pglConj hK y * pglConj hK ⟨g, hgH⟩ := by
      have := congrArg Subtype.val hxb
      simp only [Subgroup.coe_mul] at this
      rwa [hxg, hb] at this
    obtain ⟨A, hA, hAg⟩ := exists_blockHom_of_commute hK hq hq2 m hr3 hr1 ⟨g, hgH⟩ y hgL hy hc
    have hgA : g = cyc m * blockHom A * (cyc m)⁻¹ := by
      rw [← hAg]
      group
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨B, hB⟩ := hn
    have hABA : A * (B : GL (Fin 2) K) * A⁻¹ ∈ slPi π 2 (p ^ f) K := by
      have hB' := (mem_slPi_iff hπ).mp B.2
      refine (mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hA hB'.1) (inv_mem hA), ?_⟩
      rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
      exact hB'.2
    refine ⟨⟨_, hABA⟩, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxg, ← hB]
    rw [blockAut_apply, blockAut_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hgA]
    group
  ·
    have hτS : (⟨pglConj hK (stdDiag hK hq (τ, τ ^ 2)), hBY ⟨_, rfl⟩⟩ : Y) ∈
        (blockAut hK m).range.subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨_, blockAut_diagTwo hK hq m τ⟩
    have hτB : (⟨pglConj hK (stdDiag hK hq (τ, τ ^ 2)), hBY ⟨_, rfl⟩⟩ : Y) ∈
        (stdPlane hK hq).subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨_, rfl⟩
    have hnot' : (⟨pglConj hK (stdDiag hK hq (τ, τ ^ 2)), hBY ⟨_, rfl⟩⟩ : Y) ∉
        Subgroup.zpowers b := by
      rintro ⟨k, hk⟩
      apply hnot
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    have hB3 : ∀ x ∈ (stdPlane hK hq).subgroupOf Y, x ^ 3 = 1 := fun x hx =>
      Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact pow_three_of_mem_stdPlane hK hq _ (Subgroup.mem_subgroupOf.mp hx))
    have hB9 : Nat.card ((stdPlane hK hq).subgroupOf Y) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv, card_stdPlane hK hq hq2]
    refine (le_zpowers_sup hB3 hB9 hbB hb1 hτB hnot').trans (sup_le_sup_left ?_ _)
    exact Subgroup.zpowers_le.mpr hτS

theorem thetaAlpha_stdPlane (hq2 : 2 < p ^ f)
    (hY : (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →*
      MulAut (projImage (slPi π 3 (p ^ f) K))).range ≤ Y)
    (hBY : stdPlane hK hq ≤ Y) : thetaAlpha 3 ((stdPlane hK hq).subgroupOf Y) = ⊥ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  obtain ⟨τ, hτ⟩ : ∃ τ : rootsOfUnity 3 K, τ ≠ 1 := by
    have h3 := card_rootsOfUnity_three hK hq
    have : Nontrivial (rootsOfUnity 3 K) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [h3]; norm_num)
    exact exists_ne 1
  have hτ3 : (τ : Kˣ) ^ 3 = 1 := (mem_rootsOfUnity _ _).mp τ.2
  have hτ1 : (τ : Kˣ) ≠ 1 := fun h => hτ (Subtype.ext h)
  have hdiagE : ∀ (m : Fin 3) {r : Kˣ}, r ^ 3 = 1 →
      cyc m * diagE r * (cyc m)⁻¹ ∈ glPi π 3 (p ^ f) K := fun m r hr3 =>
    mul_mem (mul_mem (cyc_mem_glPi hK m) (Sec11.KS11LieProof.diagE_mem_glPi hK fun hπf => by
      subst hπf
      exact pow_succ_eq_one_of_modThree hq (by
        rw [← Units.val_pow_eq_pow_val, hr3, Units.val_one]))) (inv_mem (cyc_mem_glPi hK m))
  refine thetaAlpha_eq_bot_of_types (I := (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →*
      MulAut (projImage (slPi π 3 (p ^ f) K))).range.subgroupOf Y)
    (Δ := (Sec14.inndiagPi π (p ^ f) K).subgroupOf Y)
    ((conj_range_normal (p := p) (f := f) (K := K) (π := π)).subgroupOf Y)
    ((Sec14.ks142InndiagNormal π p f K hK hq hq2).subgroupOf Y)
    (Subgroup.subgroupOf_mono _ (stdPlane_le_inndiagPi hK hq))
    (fun x hx y hy => Subtype.ext (stdPlane_comm hK hq _ (Subgroup.mem_subgroupOf.mp hx) _
      (Subgroup.mem_subgroupOf.mp hy)))
    (fun x => ⟨1, by
      rw [pow_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact pow_three_of_mem_stdPlane hK hq _ (Subgroup.mem_subgroupOf.mp x.2)⟩) ?_ ?_
  ·
    intro b hb hb1
    obtain ⟨st, hst⟩ := Subgroup.mem_subgroupOf.mp hb
    have hst1 : st ≠ 1 := by
      rintro rfl
      apply hb1
      apply Subtype.ext
      rw [← hst, map_one]
      rfl
    by_cases h1 : st.1 ≠ 1 ∧ st.2 ≠ 1 ∧ st.1 ≠ st.2
    ·
      left
      intro d hd hdb hd3 x hx
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      refine typeOne_stdPlane hK hq hq2 h1.1 h1.2.1 h1.2.2 (Subgroup.mem_subgroupOf.mp hd) ?_
        (by rwa [Subgroup.orderOf_coe]) _ (Subgroup.mem_subgroupOf.mp hx)
      have := congrArg Subtype.val hdb
      simp only [Subgroup.coe_mul] at this
      rw [← hst] at this
      exact this
    ·
      right
      obtain ⟨m, r, hr3, hr1, hmk⟩ := exists_cyc_diagE hK hq hst1 h1
      refine ⟨_, typeTwoAt_blockIn hK hq hq2 hY hBY hb hb1 m hr3 hr1 ⟨_, hdiagE m hr3⟩ rfl ?_
        (τ := τ) ?_⟩
      · rw [← hst]
        exact pglConj_eq_of_mk_eq hK hmk
      · rw [← hst]
        exact not_mem_zpowers_typeOne hK hq hq2 hτ h1
  ·
    intro x hx
    have hblock : ∀ (m : Fin 3) (B : slPi π 2 (p ^ f) K),
        (x : MulAut (projImage (slPi π 3 (p ^ f) K))) * blockAut hK m B =
          blockAut hK m B * (x : MulAut (projImage (slPi π 3 (p ^ f) K))) := by
      intro m B
      have hbm : (⟨pglConj hK (stdDiag hK hq (stE τ m)), hBY ⟨_, rfl⟩⟩ : Y) ∈
          (stdPlane hK hq).subgroupOf Y := Subgroup.mem_subgroupOf.mpr ⟨_, rfl⟩
      have hbm1 : (⟨pglConj hK (stdDiag hK hq (stE τ m)), hBY ⟨_, rfl⟩⟩ : Y) ≠ 1 := by
        intro h
        have h' := congrArg Subtype.val h
        rw [Subgroup.coe_one] at h'
        have h'' := (pglConj_eq_one_iff hK hq hq2 _).mp h'
        rw [stdDiag_mem_statedScalars_iff] at h''
        apply stE_not_typeOne τ m
        rw [h'']
        fin_cases m <;> simp [stE] at h'' <;> simp_all
      have hT := typeTwoAt_blockIn hK hq hq2 hY hBY hbm hbm1 m hτ3 hτ1 ⟨_, hdiagE m hτ3⟩ rfl
        (pglConj_eq_of_mk_eq hK (mk_stdDiag_stE hK hq τ m))
        (not_mem_zpowers_typeOne hK hq hq2 hτ (stE_not_typeOne τ m))
      have hmem : (⟨blockAut hK m B, hY (blockAut_mem_range_conj hK m B)⟩ : Y) ∈
          (blockAut hK m).range.subgroupOf Y := Subgroup.mem_subgroupOf.mpr ⟨B, rfl⟩
      have := hx _ hbm hbm1 _ hT _ hmem
      exact congrArg Subtype.val this
    set H : Subgroup (GL (Fin 3) K) :=
      ((Subgroup.centralizer {(x : MulAut (projImage (slPi π 3 (p ^ f) K)))}).comap
        (pglConj hK)).map (glPi π 3 (p ^ f) K).subtype with hH
    have hgen : slPi π 3 (p ^ f) K ≤ H := by
      refine (slPi_le_closure_blockSet hK hq hq2).trans ((Subgroup.closure_le H).mpr ?_)
      rintro _ ⟨m, B, hB, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨_, mul_mem (mul_mem (cyc_mem_glPi hK m) (slPi_le_glPi hπ
        (blockHom_mem_slPi hK (slPi_le_glPi hπ hB)))) (inv_mem (cyc_mem_glPi hK m))⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (hblock m ⟨B, hB⟩).symm
    have hZ := CFSG.RankThree.PartTwo.Sec13.center_projImage_slPi hK hq hq2
    apply Subtype.ext
    ext w
    rw [Subgroup.coe_one, MulAut.one_apply]
    obtain ⟨g, hgL, hgH, hgw⟩ := exists_conj_eq_pglConj hK w
    obtain ⟨g', hg', hg'g⟩ := Subgroup.mem_map.mp (hgen hgL)
    have hg'eq : g' = ⟨g, hgH⟩ := Subtype.ext hg'g
    rw [hg'eq, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← hgw] at hg'
    exact congrArg Subtype.val (fix_of_mul_conj_eq hZ hg'.symm)

end Core

end Res423Five

end CFSG.RankThree.PartTwo.Sec4

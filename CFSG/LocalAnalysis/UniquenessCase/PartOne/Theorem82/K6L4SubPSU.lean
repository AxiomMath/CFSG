module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Sub
public import CFSG.GH74.L5U5.ModelsBasic
public import CFSG.Open.StatedCenterThree
public import CFSG.Adapters.StatedQuasisimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open Subgroup

variable {K : Type} [Field K] [Finite K]

private noncomputable def sl2Congr {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv A := by ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' A B := map_mul _ A B

private theorem diagUnit_eq_diagGL (u : Fin 4 → Kˣ) (h01 : u 0 = u 1) (h23 : u 2 = u 3) :
    diagUnit u = CFSG.GH74.L5U5.diagGL
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (u 0))
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (u 2)) := by
  have e0 : (CFSG.GH74.L5U5.e4.symm 0 : Fin 2 ⊕ Fin 2) = Sum.inl 0 := rfl
  have e1 : (CFSG.GH74.L5U5.e4.symm 1 : Fin 2 ⊕ Fin 2) = Sum.inl 1 := rfl
  have e2 : (CFSG.GH74.L5U5.e4.symm 2 : Fin 2 ⊕ Fin 2) = Sum.inr 0 := rfl
  have e3 : (CFSG.GH74.L5U5.e4.symm 3 : Fin 2 ⊕ Fin 2) = Sum.inr 1 := rfl
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagUnit, CFSG.GH74.L5U5.diagGL, CFSG.GH74.L5U5.blk4,
      CFSG.GH74.L5U5.blk4_eq_reindex, Matrix.coe_reindexAlgEquiv,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, h01, h23, e0, e1, e2, e3]

private theorem diagGL_scalar (c : Kˣ) :
    CFSG.GH74.L5U5.diagGL (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
  rw [← diagUnit_eq_diagGL (fun _ => c) rfl rfl]
  rfl

private theorem scalar_neg_one : Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : Kˣ) =
    (-1 : GL (Fin 4) K) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.neg_apply,
      Matrix.one_apply]

private theorem diagGL_neg_one : CFSG.GH74.L5U5.diagGL (-1 : GL (Fin 2) K) (-1) =
    (-1 : GL (Fin 4) K) := by
  apply Units.ext
  rw [CFSG.GH74.L5U5.coe_diagGL]
  have h2 : ((-1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -1 := by
    rw [Units.val_neg, Units.val_one]
  have h4 : ((-1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1 := by
    rw [Units.val_neg, Units.val_one]
  rw [h2, h4, CFSG.GH74.L5U5.blk4_neg, CFSG.GH74.L5U5.blk4_one]

private theorem diagGL_mul_scalar (a b : GL (Fin 2) K) (c c' : Kˣ) :
    CFSG.GH74.L5U5.diagGL a b *
        CFSG.GH74.L5U5.diagGL (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c') =
      CFSG.GH74.L5U5.diagGL (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c') *
        CFSG.GH74.L5U5.diagGL a b := by
  rw [CFSG.GH74.L5U5.diagGL_mul, CFSG.GH74.L5U5.diagGL_mul,
    (Matrix.GeneralLinearGroup.scalar_commute c a).symm,
    (Matrix.GeneralLinearGroup.scalar_commute c' b).symm]

private theorem d₁_eq_diagGL (ζ : CubeRoot K) :
    d₁ ζ = CFSG.GH74.L5U5.diagGL
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (ζ.pow (1 : ZMod 3)))
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (ζ.pow (-1 : ZMod 3))) := by
  have hsum : (∑ j : Fin 4, (![1, 1, -1, -1] : Fin 4 → ZMod 3) j) = 0 := by decide
  have hu : (fun i => ζ.pow ((![1, 1, -1, -1] : Fin 4 → ZMod 3) i -
      ∑ j, (![1, 1, -1, -1] : Fin 4 → ZMod 3) j)) =
      fun i => ζ.pow ((![1, 1, -1, -1] : Fin 4 → ZMod 3) i) := by
    funext i
    rw [hsum]
    exact congrArg ζ.pow (sub_zero _)
  have h01 : (fun i => ζ.pow ((![1, 1, -1, -1] : Fin 4 → ZMod 3) i)) 0 =
      (fun i => ζ.pow ((![1, 1, -1, -1] : Fin 4 → ZMod 3) i)) 1 := rfl
  have h23 : (fun i => ζ.pow ((![1, 1, -1, -1] : Fin 4 → ZMod 3) i)) 2 =
      (fun i => ζ.pow ((![1, 1, -1, -1] : Fin 4 → ZMod 3) i)) 3 := rfl
  rw [d₁, show stdDiagHom ζ (Multiplicative.ofAdd ![1, 1, -1, -1]) =
    diagUnit (fun i => ζ.pow ((![1, 1, -1, -1] : Fin 4 → ZMod 3) i -
      ∑ j, (![1, 1, -1, -1] : Fin 4 → ZMod 3) j)) from rfl, hu]
  exact diagUnit_eq_diagGL _ h01 h23

private theorem injective_blockEmbed {r : ℕ}
    (φ : StatedSU 2 r K × StatedSU 2 r K →* StatedSU 4 r K)
    (hφ : ∀ x, ((φ x : StatedSU 4 r K) : GL (Fin 4) K) =
      CFSG.GH74.L5U5.diagGL x.1 x.2) : Function.Injective φ := by
  intro x y h
  have hx := congrArg (fun z : StatedSU 4 r K => (z : GL (Fin 4) K)) h
  rw [hφ x, hφ y] at hx
  obtain ⟨hA, hB⟩ := CFSG.GH74.L5U5.diagGL_inj hx
  exact Prod.ext (Subtype.ext hA) (Subtype.ext hB)

private theorem blockEmbed_mem_eq_one_or_neg_one {r : ℕ}
    (φ : StatedSU 2 r K × StatedSU 2 r K →* StatedSU 4 r K)
    (hφ : ∀ x, ((φ x : StatedSU 4 r K) : GL (Fin 4) K) =
      CFSG.GH74.L5U5.diagGL x.1 x.2) {g : StatedSU 4 r K}
    (hg : g ∈ φ.range ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K)) :
    (g : GL (Fin 4) K) = 1 ∨ (g : GL (Fin 4) K) = -1 := by
  obtain ⟨hzr, hzs⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hzr
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hzs)
  have hgl : CFSG.GH74.L5U5.diagGL z.1 z.2 =
      CFSG.GH74.L5U5.diagGL (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    rw [← hφ z, hz, ← hc, ← diagGL_scalar c]
  obtain ⟨h1, -⟩ := CFSG.GH74.L5U5.diagGL_inj hgl
  have hdet : ((z.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSU z.1.2
  have hcval : (c : K) ^ 2 = 1 := by
    have h := congrArg Matrix.GeneralLinearGroup.det h1
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
    have hdet' : Matrix.GeneralLinearGroup.det (z.1 : GL (Fin 2) K) = 1 := by
      apply Units.ext
      simpa using hdet
    rw [hdet'] at h
    have := congrArg (fun u : Kˣ => (u : K)) h.symm
    simpa using this
  have hc1 : c = 1 ∨ c = -1 := by
    rcases sq_eq_one_iff.mp hcval with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  rcases hc1 with hc1 | hc1
  · left
    rw [← hc, hc1, map_one]
  · right
    rw [← hc, hc1]
    exact scalar_neg_one

private theorem card_scalar_inter {r : ℕ} [Fact r.Prime] (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (φ : StatedSU 2 r K × StatedSU 2 r K →* StatedSU 4 r K)
    (hφ : ∀ x, ((φ x : StatedSU 4 r K) : GL (Fin 4) K) =
      CFSG.GH74.L5U5.diagGL x.1 x.2)
    (hneg2 : (-1 : GL (Fin 2) K) ∈ StatedSU 2 r K)
    (hneg4 : (-1 : GL (Fin 4) K) ∈ StatedSU 4 r K) :
    Nat.card ↥(φ.range ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K)) = 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (2 < r) := ⟨by omega⟩
  have hcardK : Fintype.card K = r ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K r := charP_of_card_eq_prime_pow (p := r) (f := 2) hcardK
  let m2 : StatedSU 2 r K := ⟨-1, hneg2⟩
  let m4 : StatedSU 4 r K := ⟨-1, hneg4⟩
  have hx2range : m4 ∈ φ.range := by
    rw [MonoidHom.mem_range]
    refine ⟨(m2, m2), ?_⟩
    apply Subtype.ext
    rw [hφ (m2, m2)]
    exact diagGL_neg_one
  have hx2scal : m4 ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K) := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨-1, scalar_neg_one⟩
  let x₂ : ↥(φ.range ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K)) :=
    ⟨m4, Subgroup.mem_inf.mpr ⟨hx2range, hx2scal⟩⟩
  refine Nat.card_eq_two_iff.mpr ⟨1, x₂, ?_, ?_⟩
  · intro h
    have h1 : (1 : GL (Fin 4) K) = -1 := by
      have := congrArg (fun z : ↥(φ.range ⊓
        (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K)) =>
        ((z : StatedSU 4 r K) : GL (Fin 4) K)) h
      simpa [x₂] using this
    have h2 := congrArg (fun A : GL (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K) 0 0) h1
    simp at h2
    exact (CharP.neg_one_ne_one (R := K) r) h2.symm
  · ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases blockEmbed_mem_eq_one_or_neg_one φ hφ g.2 with h | h
    · left
      apply Subtype.ext
      apply Subtype.ext
      simpa using h
    · right
      apply Subtype.ext
      apply Subtype.ext
      show ((g : StatedSU 4 r K) : GL (Fin 4) K) = -1
      exact h

private theorem blockGL_mem_SUid' {k m : ℕ} {σ : K ≃+* K} {A : GL (Fin k) K}
    (hA : A ∈ CFSG.LieType.Universal.Unitary.SUid σ k) :
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL K k m A ∈
      CFSG.LieType.Universal.Unitary.SUid σ (k + m) := by
  rw [CFSG.LieType.Universal.Unitary.mem_SUid]
  obtain ⟨hdet, huni⟩ := (CFSG.LieType.Universal.Unitary.mem_SUid).1 hA
  refine ⟨?_, ?_⟩
  · rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.det_blockGL]
    exact hdet
  · have hY : CFSG.GH74.Filter.ClassicalOdd.IsUni (σ : K →+* K)
        (1 : Matrix (Fin m) (Fin m) K) := CFSG.GH74.Filter.ClassicalOdd.IsUni.one
    have hX : CFSG.GH74.Filter.ClassicalOdd.IsUni (σ : K →+* K)
        (A : Matrix (Fin k) (Fin k) K) := huni
    have h := CFSG.GH74.Filter.ClassicalOdd.IsUni.diagBlock (σ := (σ : K →+* K)) hX hY
    change CFSG.LieType.Universal.Unitary.conjTr σ
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.diagBlock
        (A : Matrix (Fin k) (Fin k) K) 1) *
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.diagBlock
        (A : Matrix (Fin k) (Fin k) K) 1 = 1
    exact h

private theorem blockGL_injective' {k m : ℕ} :
    Function.Injective (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL K k m) := by
  intro X Y h
  ext i j
  have h1 := congrFun (congrFun (congrArg
    (fun M : GL (Fin (k + m)) K => (M : Matrix (Fin (k + m)) (Fin (k + m)) K)) h)
    (finSumFinEquiv (Sum.inl i))) (finSumFinEquiv (Sum.inl j))
  rwa [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL_apply_inl,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL_apply_inl] at h1

theorem su2_equiv_sl2 {r : ℕ} [Fact r.Prime] (hK : Nat.card K = r ^ 2) :
    Nonempty (StatedSU 2 r K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = r ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K r := charP_of_card_eq_prime_pow (p := r) (f := 2) hcardK
  have hF : Nat.card K = (r ^ 1) ^ 2 := by simpa using hK
  obtain ⟨e⟩ := CFSG.GH74.L5U5.nonempty_sl2_equiv_uni_H2 (F := K) (p := r) (f := 1) hF
  have hcard : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K r 1) = r := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := r) (f := 1) hF, pow_one]
  let _ : Fintype (CFSG.LieType.Steinberg.fixedSubfield K r 1) := Fintype.ofFinite _
  let _ : Fintype (ZMod r) := ZMod.fintype r
  let ε : CFSG.LieType.Steinberg.fixedSubfield K r 1 ≃+* ZMod r :=
    FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hcard, ZMod.card])
  have hH2 : (CFSG.GH74.L5U5.ModelData.uni hF).H2 = StatedSU 2 r K := by
    change StatedSU 2 (r ^ 1) K = StatedSU 2 r K
    rw [pow_one]
  exact ⟨(MulEquiv.subgroupCongr hH2).symm.trans (e.symm.trans (sl2Congr ε))⟩

theorem su_blockEmbed {r : ℕ} [Fact r.Prime] (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (d : StatedSU 4 r K) (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    ∃ φ : StatedSU 2 r K × StatedSU 2 r K →* StatedSU 4 r K, Function.Injective φ ∧
      (∀ x, φ x ∈ Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) ∧
      Nat.card ↥(φ.range ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K)) = 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = r ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K r := charP_of_card_eq_prime_pow (p := r) (f := 2) hcardK
  have hF : Nat.card K = (r ^ 1) ^ 2 := by simpa using hK
  let M : CFSG.GH74.L5U5.ModelData K := CFSG.GH74.L5U5.ModelData.uni (p := r) (f := 1) hF
  have hH2 : M.H2 = StatedSU 2 r K := by
    change StatedSU 2 (r ^ 1) K = StatedSU 2 r K
    rw [pow_one]
  have hK4 : M.K4 = StatedSU 4 r K := by
    change StatedSU 4 (r ^ 1) K = StatedSU 4 r K
    rw [pow_one]
  let eH : M.H2 ≃* StatedSU 2 r K := MulEquiv.subgroupCongr hH2
  let ψ : M.H2 × M.H2 →* M.K4 :=
    ((CFSG.GH74.L5U5.diagGLHom K).comp (M.H2.subtype.prodMap M.H2.subtype)).codRestrict M.K4
      (fun x => by
        change CFSG.GH74.L5U5.diagGL (x.1 : GL (Fin 2) K) (x.2 : GL (Fin 2) K) ∈ M.K4
        rw [CFSG.GH74.L5U5.ModelData.diagGL_mem_K4_iff]
        obtain ⟨hx1, hx2⟩ := (M.mem_H2 (x.1 : GL (Fin 2) K)).1 x.1.2
        obtain ⟨hy1, hy2⟩ := (M.mem_H2 (x.2 : GL (Fin 2) K)).1 x.2.2
        exact ⟨hx1, hy1, by rw [hx2, hy2, one_mul]⟩)
  let φ : StatedSU 2 r K × StatedSU 2 r K →* StatedSU 4 r K :=
    (MulEquiv.subgroupCongr hK4).toMonoidHom.comp (ψ.comp (eH.prodCongr eH).symm.toMonoidHom)
  have hφ : ∀ x, ((φ x : StatedSU 4 r K) : GL (Fin 4) K) =
      CFSG.GH74.L5U5.diagGL x.1 x.2 := fun _ => rfl
  have hneg2 : (-1 : GL (Fin 2) K) ∈ StatedSU 2 r K := by
    rw [← hH2]
    exact M.neg_one_mem_H2
  have hneg4 : (-1 : GL (Fin 4) K) ∈ StatedSU 4 r K := by
    rw [← hK4, ← diagGL_neg_one]
    exact M.xGL_mem_K4
  refine ⟨φ, injective_blockEmbed φ hφ, ?_, card_scalar_inter h5 hK φ hφ hneg2 hneg4⟩
  intro x
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hφ x, hd, d₁_eq_diagGL]
  exact diagGL_mul_scalar x.1 x.2 (ζ.pow 1) (ζ.pow (-1))

theorem sub8_block_su {r : ℕ} [Fact r.Prime] (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (d : StatedSU 4 r K) (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    ∃ K₁ : Subgroup (StatedSU 4 r K), K₁ ≤ Subgroup.centralizer ({d} : Set (StatedSU 4 r K)) ∧
      Nonempty (K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r) ×
        Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) ∧
      Nat.card ↥(K₁ ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K)) = 2 := by
  obtain ⟨φ, hinj, hcent, hz⟩ := su_blockEmbed h5 hK ζ d hd
  obtain ⟨e⟩ := su2_equiv_sl2 (K := K) hK
  refine ⟨φ.range, ?_, ⟨(MonoidHom.ofInjective hinj).symm.trans (e.prodCongr e)⟩, hz⟩
  rintro _ ⟨x, rfl⟩
  exact hcent x

theorem sub8Fact_su {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) : Sub8Fact (StatedSU 4 r K) ζ r := by
  haveI : Fact r.Prime := ⟨hr⟩
  intro d hd
  obtain ⟨K₁, hle, ⟨e⟩, hz⟩ := sub8_block_su h5 hK ζ d hd
  obtain ⟨hperf, hns, hcard⟩ := sl2sq_perfect hr h5 (Nat.card_zmod r) e
  have hZc : K₁ ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K) ≤
      Subgroup.center (StatedSU 4 r K) :=
    inf_le_right.trans (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
  refine ⟨K₁, hle, hperf, hns, hcard, hz, fun N h1 h2 h3 h4 => ?_⟩
  exact (sl2sq_odd hr h5 (Nat.card_zmod r) e inf_le_left hZc hz N h1 h2 h3 h4).trans inf_le_right

private theorem blockEmbed31_mem_centralizer {r : ℕ}
    (ζ : CubeRoot K) (d : StatedSU 4 r K) (hd : (d : GL (Fin 4) K) = d₃ ζ)
    (φ : StatedSU 3 r K →* StatedSU 4 r K)
    (hφ : ∀ A : StatedSU 3 r K, ((φ A : StatedSU 4 r K) : GL (Fin 4) K) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL K 3 1 (A : GL (Fin 3) K)) :
    ∀ A, φ A ∈ Subgroup.centralizer ({d} : Set (StatedSU 4 r K)) := by
  intro A
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hφ A, hd]
  let u : Fin 4 → Kˣ := fun i => ζ.pow ((![1, 1, 1, 0] : Fin 4 → ZMod 3) i -
    ∑ j, (![1, 1, 1, 0] : Fin 4 → ZMod 3) j)
  have hd3 : d₃ ζ = diagUnit u := rfl
  rw [hd3]
  apply Units.ext
  have hconst : ∀ i j : Fin 3,
      (u (finSumFinEquiv (m := 3) (n := 1) (Sum.inl i)) : K) =
      (u (finSumFinEquiv (m := 3) (n := 1) (Sum.inl j)) : K) := fun i j => by
    fin_cases i <;> fin_cases j <;> rfl
  exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL_mul_diagonal_comm
    (K := K) (k := 3) (m := 1) (X := (A : GL (Fin 3) K)) (d := fun i => (u i : K)) hconst

private theorem blockEmbed31_inter_scalars_eq_bot {r : ℕ}
    (φ : StatedSU 3 r K →* StatedSU 4 r K)
    (hφ : ∀ A : StatedSU 3 r K, ((φ A : StatedSU 4 r K) : GL (Fin 4) K) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL K 3 1 (A : GL (Fin 3) K)) :
    φ.range ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxK, hxs⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hxK
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hxs)
  have hc1 : c = 1 := by
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin 4) c =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL K 3 1 (A : GL (Fin 3) K) := by
      rw [hc, ← hA, hφ A]
    have hval := congrArg (fun M : GL (Fin 4) K =>
      (M : Matrix (Fin 4) (Fin 4) K)
        (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inr (0 : Fin 1)))) hc'
    simp only [Matrix.GeneralLinearGroup.coe_scalar,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalar_apply_finSumFinEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL_apply_inr,
      Matrix.one_apply_eq] at hval
    simpa using hval
  apply Subtype.ext
  show ((x : StatedSU 4 r K) : GL (Fin 4) K) = 1
  rw [← hc, hc1, map_one]

theorem sub9_block_su {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (d : StatedSU 4 r K) (hd : (d : GL (Fin 4) K) = d₃ ζ) :
    ∃ K₃ : Subgroup (StatedSU 4 r K), K₃ ≤ Subgroup.centralizer ({d} : Set (StatedSU 4 r K)) ∧
      Nonempty (K₃ ≃* StatedSU 3 r K) ∧
      K₃ ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K) = ⊥ := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = r ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K r := charP_of_card_eq_prime_pow (p := r) (f := 2) hcardK
  have hF : Nat.card K = (r ^ 1) ^ 2 := by simpa using hK
  let σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K r 1
  have hS3 : StatedSU 3 r K = CFSG.LieType.Universal.Unitary.SUid σ 3 := by
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 3, pow_one]
  have hS4 : StatedSU 4 r K = CFSG.LieType.Universal.Unitary.SUid σ 4 := by
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4, pow_one]
  let ψ : CFSG.LieType.Universal.Unitary.SUid σ 3 →*
      CFSG.LieType.Universal.Unitary.SUid σ 4 :=
    ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL K 3 1).comp
        (CFSG.LieType.Universal.Unitary.SUid σ 3).subtype).codRestrict
      (CFSG.LieType.Universal.Unitary.SUid σ 4)
      (fun A => blockGL_mem_SUid' (σ := σ) A.2)
  let φ : StatedSU 3 r K →* StatedSU 4 r K :=
    (MulEquiv.subgroupCongr hS4).symm.toMonoidHom.comp
      (ψ.comp (MulEquiv.subgroupCongr hS3).toMonoidHom)
  have hφ : ∀ A : StatedSU 3 r K,
      ((φ A : StatedSU 4 r K) : GL (Fin 4) K) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL K 3 1 (A : GL (Fin 3) K) :=
    fun _ => rfl
  have hinj : Function.Injective φ := by
    intro A B h
    have h1 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL K 3 1 (A : GL (Fin 3) K) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockGL K 3 1 (B : GL (Fin 3) K) := by
      rw [← hφ A, ← hφ B, h]
    exact Subtype.ext (blockGL_injective' h1)
  refine ⟨φ.range, ?_, ⟨(MonoidHom.ofInjective hinj).symm⟩, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact blockEmbed31_mem_centralizer ζ d hd φ hφ A
  · exact blockEmbed31_inter_scalars_eq_bot φ hφ

theorem su3_block_data {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    {K₃ : Subgroup (StatedSU 4 r K)} (e : K₃ ≃* StatedSU 3 r K) :
    ⁅K₃, K₃⁆ = K₃ ∧ IsSimpleGroup (K₃ ⧸ Subgroup.center K₃) ∧ 2 ∣ Nat.card K₃ := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = r ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K r := charP_of_card_eq_prime_pow (p := r) (f := 2) hcardK
  haveI : Fact (2 < r) := ⟨by omega⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.IsQuasisimple ↥(StatedSU 3 r K) :=
    CFSG.Open.StatedAPI.isQuasisimple_statedSU_three_of_prime hr (by omega) K hK
  have hq3 : CFSG.IsQuasisimple ↥K₃ := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  refine ⟨Subgroup.isPerfect_iff.mp hq3.1, hq3.2.1, ?_⟩
  have hOdd : Odd r := hr.odd_of_ne_two (by rintro rfl; omega)
  have hEven : Even (r + 1) := hOdd.add_one
  have ha : (-1 : Kˣ) ^ (r + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact Even.neg_one_pow hEven
  have hmem : CFSG.Open.StatedCenterThree.diagGL (-1 : Kˣ) ∈ StatedSU 3 r K :=
    CFSG.Open.StatedCenterThree.diagGL_mem hr.ne_zero ha
  have horder : orderOf (CFSG.Open.StatedCenterThree.diagGL (-1 : Kˣ)) = 2 := by
    apply orderOf_eq_prime
    · apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [CFSG.Open.StatedCenterThree.diagGL, pow_two, Matrix.diagonal_mul_diagonal]
    · intro h
      have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
      simp [CFSG.Open.StatedCenterThree.diagGL] at this
      exact (CharP.neg_one_ne_one (R := K) r) this
  have h2 : 2 ∣ Nat.card ↥(StatedSU 3 r K) := by
    have := Subgroup.orderOf_dvd_natCard (StatedSU 3 r K) hmem
    rwa [horder] at this
  rw [Nat.card_congr e.toEquiv]
  exact h2

theorem sub9Fact_su {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) : Sub9Fact (StatedSU 4 r K) ζ := by
  intro d hd
  obtain ⟨K₃, hle, ⟨e⟩, hz⟩ := sub9_block_su hr h5 hK ζ d hd
  obtain ⟨hp, hs, hev⟩ := su3_block_data hr h5 hK e
  obtain ⟨hns, hN⟩ := quasisimple_facts hp hs hev
  exact ⟨K₃, hle, hns, hz, hN⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

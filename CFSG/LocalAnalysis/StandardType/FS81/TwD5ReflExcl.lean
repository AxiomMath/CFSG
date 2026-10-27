module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Refl
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthRows
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatWt
public import CFSG.LocalAnalysis.StandardType.FS81.Realized

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def transE0 : Fin 6 → ZMod 3 := Pi.single 0 1

@[expose] def transE45 : Fin 6 → ZMod 3 := Pi.single 4 1 + Pi.single 5 1

@[expose] def translMat (u : Fin 6 → ZMod 3) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  1 + Matrix.vecMulVec u transE0

theorem translMat_zero : translMat (0 : Fin 6 → ZMod 3) = 1 := by
  simp [translMat]

theorem translMat_mul (u v : Fin 6 → ZMod 3) (hv : v 0 = 0) :
    translMat u * translMat v = translMat (u + v) := by
  unfold translMat
  have hdot : transE0 ⬝ᵥ v = 0 := by
    rw [transE0, single_dotProduct, one_mul]
    exact hv
  have hAB : Matrix.vecMulVec u transE0 * Matrix.vecMulVec v transE0 = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hdot, zero_smul, Matrix.vecMulVec_zero]
  calc
    (1 + Matrix.vecMulVec u transE0) * (1 + Matrix.vecMulVec v transE0) =
        1 + Matrix.vecMulVec u transE0 + Matrix.vecMulVec v transE0 +
          Matrix.vecMulVec u transE0 * Matrix.vecMulVec v transE0 := by noncomm_ring
    _ = 1 + Matrix.vecMulVec u transE0 + Matrix.vecMulVec v transE0 := by rw [hAB, add_zero]
    _ = 1 + (Matrix.vecMulVec u transE0 + Matrix.vecMulVec v transE0) := by abel
    _ = 1 + Matrix.vecMulVec (u + v) transE0 := by rw [Matrix.add_vecMulVec]

theorem translMat_mul_neg (u : Fin 6 → ZMod 3) (hu : u 0 = 0) :
    translMat u * translMat (-u) = 1 := by
  rw [translMat_mul u (-u) (by simpa using hu), add_neg_cancel, translMat_zero]

theorem translMat_neg_mul (u : Fin 6 → ZMod 3) (hu : u 0 = 0) :
    translMat (-u) * translMat u = 1 := by
  rw [translMat_mul (-u) u hu, neg_add_cancel, translMat_zero]

@[expose] def translUnit (u : Fin 6 → ZMod 3) (hu : u 0 = 0) : GL (Fin 6) (ZMod 3) :=
  Units.mk (translMat u) (translMat (-u)) (translMat_mul_neg u hu) (translMat_neg_mul u hu)

@[simp] theorem translUnit_coe (u : Fin 6 → ZMod 3) (hu : u 0 = 0) :
    (translUnit u hu : Matrix (Fin 6) (Fin 6) (ZMod 3)) = translMat u :=
  rfl

theorem translMat_injective {u v : Fin 6 → ZMod 3} (h : translMat u = translMat v) : u = v := by
  have h' := congrArg (fun M => M *ᵥ transE0) h
  simp only [translMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec] at h'
  have hdot : transE0 ⬝ᵥ transE0 = 1 := by
    rw [transE0, single_dotProduct, one_mul, Pi.single_eq_same]
  rw [hdot] at h'
  simpa [op_smul_eq_smul] using add_left_cancel h'

def translSubgroup : Subgroup (GL (Fin 6) (ZMod 3)) where
  carrier := {A | ∃ u : Fin 6 → ZMod 3, u 0 = 0 ∧
    (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = translMat u}
  one_mem' := ⟨0, rfl, by rw [translMat_zero, Units.val_one]⟩
  mul_mem' := by
    rintro A B ⟨u, hu, hAu⟩ ⟨v, hv, hBv⟩
    refine ⟨u + v, by simp [hu, hv], ?_⟩
    rw [Units.val_mul, hAu, hBv, translMat_mul u v hv]
  inv_mem' := by
    rintro A ⟨u, hu, hAu⟩
    refine ⟨-u, by simpa using hu, ?_⟩
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hAu, translMat_mul_neg u hu]

theorem translUnit_mem (u : Fin 6 → ZMod 3) (hu : u 0 = 0) :
    translUnit u hu ∈ translSubgroup :=
  ⟨u, hu, rfl⟩

noncomputable def translSubtypeEquiv : {u : Fin 6 → ZMod 3 // u 0 = 0} ≃ translSubgroup :=
  Equiv.ofBijective
    (fun u : {u : Fin 6 → ZMod 3 // u 0 = 0} =>
      (⟨translUnit u.1 u.2, ⟨u.1, u.2, rfl⟩⟩ : translSubgroup))
    (by
      constructor
      · rintro ⟨u, hu⟩ ⟨v, hv⟩ h
        apply Subtype.ext
        apply translMat_injective
        have h' := congrArg (fun x : translSubgroup =>
          (x.1 : GL (Fin 6) (ZMod 3))) h
        have h'' := congrArg (fun x : GL (Fin 6) (ZMod 3) =>
          (x : Matrix (Fin 6) (Fin 6) (ZMod 3))) h'
        simpa only [translUnit_coe] using h''
      · intro A
        obtain ⟨u, hu, hAu⟩ := A.2
        refine ⟨⟨u, hu⟩, ?_⟩
        apply Subtype.ext
        apply Units.ext
        rw [translUnit_coe, hAu])

theorem card_translSubtype : Nat.card {u : Fin 6 → ZMod 3 // u 0 = 0} = 3 ^ 5 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem translSubgroup_card : Nat.card translSubgroup = 3 ^ 5 := by
  rw [← Nat.card_congr translSubtypeEquiv]
  exact card_translSubtype

theorem spMat_vecMul_e0 (σ : Equiv.Perm (Fin 6)) (s : Fin 6 → ZMod 3)
    (hσ : σ 0 = 0) :
    transE0 ᵥ* spMat σ s = s 0 • transE0 := by
  funext j
  rw [Matrix.vecMul_apply_eq_sum, Finset.sum_eq_single (0 : Fin 6)]
  · by_cases hj : j = 0
    · subst hj
      simp [spMat_apply, transE0, hσ]
    · have hσj : ¬ (0 = σ j) := by
        intro h
        apply hj
        exact σ.injective (by rw [hσ]; exact h.symm)
      simp [spMat_apply, transE0, hσj, Pi.single_eq_of_ne hj]
  · intro b _ hb
    have hb0 : transE0 b = 0 := by simp [transE0, Pi.single_eq_of_ne hb]
    rw [hb0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem spMat_mul_translMat (σ : Equiv.Perm (Fin 6)) (s : Fin 6 → ZMod 3)
    (u : Fin 6 → ZMod 3) (hσ : σ 0 = 0) (hs : IsSign s) :
    spMat σ s * translMat u =
      translMat (s 0 • (spMat σ s *ᵥ u)) * spMat σ s := by
  unfold translMat
  rw [mul_add, mul_one, Matrix.mul_vecMulVec, add_mul, one_mul,
    Matrix.vecMulVec_mul, spMat_vecMul_e0 σ s hσ]
  rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_smul]
  have hs0 : s 0 * s 0 = 1 := by
    rcases hs 0 with h | h <;> rw [h] <;> decide
  rw [hs0, one_smul]

theorem spMat_smul_mulVec_zero (σ : Equiv.Perm (Fin 6)) (s : Fin 6 → ZMod 3)
    (u : Fin 6 → ZMod 3) (hσ : σ 0 = 0) (hu : u 0 = 0) :
    (s 0 • (spMat σ s *ᵥ u)) 0 = 0 := by
  have hsymm : σ.symm 0 = 0 := (Equiv.symm_apply_eq σ).mpr hσ.symm
  simp [spMat_mulVec, hsymm, hu]

theorem spMat_conj_translUnit {A : GL (Fin 6) (ZMod 3)}
    {σ : Equiv.Perm (Fin 6)} {s : Fin 6 → ZMod 3} (hA :
      (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = spMat σ s)
    (hσ : σ 0 = 0) (hs : IsSign s) (u : Fin 6 → ZMod 3) (hu : u 0 = 0) :
    A * translUnit u hu * A⁻¹ =
      translUnit (s 0 • (spMat σ s *ᵥ u)) (spMat_smul_mulVec_zero σ s u hσ hu) := by
  have hmat : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) * translMat u =
      translMat (s 0 • (spMat σ s *ᵥ u)) * (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
    rw [hA]
    exact spMat_mul_translMat σ s u hσ hs
  have hGL : A * translUnit u hu =
      translUnit (s 0 • (spMat σ s *ᵥ u)) (spMat_smul_mulVec_zero σ s u hσ hu) * A := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, translUnit_coe, translUnit_coe]
    exact hmat
  calc A * translUnit u hu * A⁻¹ =
      translUnit (s 0 • (spMat σ s *ᵥ u)) (spMat_smul_mulVec_zero σ s u hσ hu) * A * A⁻¹ := by
        rw [hGL]
    _ = translUnit (s 0 • (spMat σ s *ᵥ u)) (spMat_smul_mulVec_zero σ s u hσ hu) := by
        rw [mul_assoc, mul_inv_cancel, mul_one]

theorem mem_normalizer_translSubgroup_of_eq_spMat {A : GL (Fin 6) (ZMod 3)}
    {σ : Equiv.Perm (Fin 6)} {s : Fin 6 → ZMod 3}
    (hA : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = spMat σ s)
    (hσ : σ 0 = 0) (hs : IsSign s) :
    A ∈ Subgroup.normalizer (translSubgroup : Set (GL (Fin 6) (ZMod 3))) := by
  refine Subgroup.mem_normalizer_fintype (S := (translSubgroup : Set (GL (Fin 6) (ZMod 3)))) ?_
  intro k hk
  obtain ⟨u, hu, hkmat⟩ := hk
  have hkunit : k = translUnit u hu := Units.ext (by rw [hkmat, translUnit_coe])
  rw [hkunit]
  refine ⟨s 0 • (spMat σ s *ᵥ u), spMat_smul_mulVec_zero σ s u hσ hu, ?_⟩
  rw [spMat_conj_translUnit hA hσ hs u hu]
  rfl

theorem transE45_zero : transE45 0 = 0 := by
  simp [transE45]

theorem translMat_transE45_ne_one : translMat transE45 ≠ 1 := by
  intro h
  have h' := congrFun (congrFun h 4) 0
  norm_num [translMat, transE45, transE0, Matrix.vecMulVec, Matrix.add_apply,
    Matrix.one_apply, Pi.single_apply] at h'

@[expose] def spSign45 : Fin 6 → ZMod 3 := ![1, 1, 1, 1, -1, -1]

theorem r35_eq_translMat_mul_spMat :
    r35 = translMat transE45 * spMat (Equiv.swap 4 5) spSign45 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem rD6_eq_spMat : rD6 = spMat (Equiv.swap 0 5) (fun _ => (1 : ZMod 3)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

@[expose] def spMatSubgroup : Subgroup (GL (Fin 6) (ZMod 3)) where
  carrier := {A | (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ spSet (fun _ _ => True)}
  one_mem' := ⟨1, fun _ => 1, fun _ => Or.inl rfl, trivial, spMat_one.symm⟩
  mul_mem' := by
    rintro A B ⟨σ, s, hs, -, hA⟩ ⟨τ, t, ht, -, hB⟩
    refine ⟨σ * τ, fun j => s (τ j) * t j, ?_, trivial, ?_⟩
    · intro j
      change s (τ j) * t j = 1 ∨ s (τ j) * t j = -1
      rcases hs (τ j) with h | h <;> rcases ht j with h' | h' <;>
        rw [h, h'] <;> decide +kernel
    · rw [Units.val_mul, hA, hB, spMat_mul]
  inv_mem' := by
    rintro A ⟨σ, s, hs, -, hA⟩
    let t : Fin 6 → ZMod 3 := fun j => (s (σ.symm j))⁻¹
    have ht : IsSign t := by
      intro j
      rcases hs (σ.symm j) with h | h
      · left
        rw [show t j = (s (σ.symm j))⁻¹ from rfl, h, inv_one]
      · right
        rw [show t j = (s (σ.symm j))⁻¹ from rfl, h]
        exact ZMod.inv_neg_one 3
    have hleft : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) * spMat σ.symm t = 1 := by
      rw [hA, spMat_mul]
      have hsign : (fun j => s (σ.symm j) * t j) = (fun _ => (1 : ZMod 3)) := by
        funext j
        rcases hs (σ.symm j) with h | h
        · rw [show t j = (s (σ.symm j))⁻¹ from rfl, h, inv_one, mul_one]
        · rw [show t j = (s (σ.symm j))⁻¹ from rfl, h]
          exact mul_inv_cancel₀ (by norm_num : (-1 : ZMod 3) ≠ 0)
      rw [show σ * σ.symm = 1 from mul_inv_cancel σ, hsign, spMat_one]
    refine ⟨σ.symm, t, ht, trivial, ?_⟩
    exact Units.inv_eq_of_mul_eq_one_right hleft

theorem spMatSubgroup_card_le : Nat.card spMatSubgroup ≤ 2 ^ 6 * Nat.factorial 6 := by
  have hinj : Function.Injective
      (fun A : spMatSubgroup =>
        (⟨((A : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)),
          (show ((A : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈
            spSet (fun _ _ => True) from A.2)⟩ :
          ↥(spSet (fun _ _ => True)))) := by
    intro A B hAB
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val hAB
  exact (Nat.card_le_card_of_injective _ hinj).trans (card_spSet_le 6 _)

theorem evenFix0_five_subset_evenAll0 : evenFix0 5 ⊆ evenAll0 5 := by
  rintro A ⟨σ, s, hs, ⟨hσ, hs0, hps⟩, rfl⟩
  refine ⟨σ, s, hs, ⟨hσ, ?_⟩, rfl⟩
  rw [Fin.prod_univ_succ, hs0, hps, one_mul]

theorem mulVec_e0_of_mem_evenAll0 {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hM : M ∈ evenAll0 5) :
    M *ᵥ Pi.single 0 1 = Pi.single 0 1 ∨ M *ᵥ Pi.single 0 1 = -Pi.single 0 1 := by
  obtain ⟨σ, s, hs, ⟨hσ, -⟩, rfl⟩ := hM
  rw [spMat_mulVec_single, hσ, mul_one]
  rcases hs 0 with h | h
  · left
    rw [h]
  · right
    rw [h]
    exact Pi.single_neg 0 1

theorem false_of_eq_closure_r35 {H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    (hH : H ⊆ evenAll0 5) (hD5 : evenFix0 5 ⊆ H) {Xg : Subgroup (GL (Fin 6) (ZMod 3))}
    (h : StabMatHyp 5 H Xg)
    (hX : Xg = Subgroup.closure {A : GL (Fin 6) (ZMod 3) |
      (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ H ∨ (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = r35}) :
    False := by
  have hs45 : IsSign spSign45 := by
    intro i
    fin_cases i <;> decide
  have hswap0 : (Equiv.swap 4 5 : Equiv.Perm (Fin 6)) 0 = 0 := by decide
  have hdSp : spMat (Equiv.swap 4 5) spSign45 ∈ evenFix0 5 := by
    refine ⟨Equiv.swap 4 5, spSign45, hs45, ⟨hswap0, rfl, ?_⟩, rfl⟩
    decide
  obtain ⟨d, hdX, hdMat⟩ := h.sub (spMat (Equiv.swap 4 5) spSign45) (hD5 hdSp)
  let A0 : GL (Fin 6) (ZMod 3) := translUnit transE45 transE45_zero * d
  have hA0mat : (A0 : Matrix (Fin 6) (Fin 6) (ZMod 3)) = r35 := by
    dsimp only [A0]
    rw [Units.val_mul, translUnit_coe, hdMat]
    exact r35_eq_translMat_mul_spMat.symm
  have hA0X : A0 ∈ Xg := by
    rw [hX]
    exact Subgroup.subset_closure (Or.inr hA0mat)
  have hTX : translUnit transE45 transE45_zero ∈ Xg := by
    have hmem : A0 * d⁻¹ ∈ Xg := mul_mem hA0X (inv_mem hdX)
    have heq : A0 * d⁻¹ = translUnit transE45 transE45_zero := by
      dsimp only [A0]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    rwa [heq] at hmem
  have hle : Xg ≤ Subgroup.normalizer (translSubgroup : Set (GL (Fin 6) (ZMod 3))) := by
    rw [hX]
    rw [Subgroup.closure_le]
    rintro A (hA | hA)
    · obtain ⟨σ, s, hs, hp, hAs⟩ := hH hA
      exact mem_normalizer_translSubgroup_of_eq_spMat hAs hp.1 hs
    · have hAeq : A = translUnit transE45 transE45_zero * d := by
        apply Units.ext
        rw [hA, Units.val_mul, translUnit_coe, hdMat]
        exact r35_eq_translMat_mul_spMat
      rw [hAeq]
      exact mul_mem (Subgroup.le_normalizer (translUnit_mem transE45 transE45_zero))
        (mem_normalizer_translSubgroup_of_eq_spMat hdMat hswap0 hs45)
  have hNn : (translSubgroup.subgroupOf Xg).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hle
  have hNcard_dvd : Nat.card (translSubgroup.subgroupOf Xg) ∣ Nat.card translSubgroup := by
    have hleMap : (translSubgroup.subgroupOf Xg).map Xg.subtype ≤ translSubgroup := by
      rintro - ⟨x, hx, rfl⟩
      exact hx
    have hcard : Nat.card (translSubgroup.subgroupOf Xg) =
        Nat.card ((translSubgroup.subgroupOf Xg).map Xg.subtype) := by
      rw [Subgroup.card_map_of_injective Xg.subtype_injective]
    rw [hcard]
    exact Subgroup.card_dvd_of_le hleMap
  have hNodd : Odd (Nat.card (translSubgroup.subgroupOf Xg)) := by
    refine Odd.of_dvd_nat ?_ hNcard_dvd
    rw [translSubgroup_card]
    norm_num
  have hKmem : translUnit transE45 transE45_zero ∈ translSubgroup :=
    translUnit_mem transE45 transE45_zero
  have hmemN : (⟨translUnit transE45 transE45_zero, hTX⟩ : ↥Xg) ∈
      translSubgroup.subgroupOf Xg :=
    (Subgroup.mem_subgroupOf).mpr hKmem
  have hne : (⟨translUnit transE45 transE45_zero, hTX⟩ : ↥Xg) ≠ 1 := by
    intro hone
    have hgl : translUnit transE45 transE45_zero = 1 := congrArg Subtype.val hone
    have hmat : translMat transE45 = 1 := by
      rw [← translUnit_coe transE45 transE45_zero, hgl, Units.val_one]
    exact translMat_transE45_ne_one hmat
  have hbot := h.odd (translSubgroup.subgroupOf Xg) hNn hNodd
  rw [hbot] at hmemN
  exact hne (Subgroup.mem_bot.mp hmemN)

theorem card_le_of_eq_closure_rD6 {Xg : Subgroup (GL (Fin 6) (ZMod 3))}
    (hX : Xg = Subgroup.closure {A : GL (Fin 6) (ZMod 3) |
      (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ evenAll0 5 ∨
        (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = rD6}) :
    Nat.card Xg ≤ 2 ^ 6 * Nat.factorial 6 := by
  have hXS : Xg ≤ spMatSubgroup := by
    rw [hX]
    rw [Subgroup.closure_le]
    rintro A (hA | hA)
    · obtain ⟨σ, s, hs, -, hAs⟩ := hA
      exact ⟨σ, s, hs, trivial, hAs⟩
    · refine ⟨Equiv.swap 0 5, fun _ => 1, fun _ => Or.inl rfl, trivial, ?_⟩
      exact hA.trans rD6_eq_spMat
  exact (Subgroup.card_le_of_le hXS).trans spMatSubgroup_card_le

end CFSG.StandardType.FrameRoute.FS81

end

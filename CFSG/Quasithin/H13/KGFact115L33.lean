module

public import CFSG.Quasithin.H13.KG14726LTools
public import CFSG.GH74.KGroups.L33
public import CFSG.CGT.PushingUpLit.LIT.Foote.GroupAux
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.H13.KG14726Elim

public section

namespace CFSG.Quasithin.H13.KG115L33

open Matrix Subgroup CFSG.Quasithin.H13.KG14726

local notation "M2" => Matrix (Fin 2) (Fin 2) (ZMod 3)
local notation "M3" => Matrix (Fin 3) (Fin 3) (ZMod 3)
local notation "SL3" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)
local notation "GL2" => GL (Fin 2) (ZMod 3)

@[expose] def blk (A : M2) (d : ZMod 3) : M3 :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, d]

theorem blk_mul (A B : M2) (d e : ZMod 3) : blk A d * blk B e = blk (A * B) (d * e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem det_blk (A : M2) (d : ZMod 3) : (blk A d).det = A.det * d := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blk]
  ring

theorem blk_one : blk 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem det_ne_zero_of_gl (A : GL2) : (A : M2).det ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det A).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h

@[expose] noncomputable def blkHom : GL2 →* SL3 where
  toFun A := ⟨blk (A : M2) (A : M2).det⁻¹, by
    rw [det_blk, mul_inv_cancel₀ (det_ne_zero_of_gl A)]⟩
  map_one' := by
    apply Subtype.ext
    simp [blk_one]
  map_mul' A B := by
    apply Subtype.ext
    change blk ((A * B : GL2) : M2) ((A * B : GL2) : M2).det⁻¹ =
      blk (A : M2) (A : M2).det⁻¹ * blk (B : M2) (B : M2).det⁻¹
    rw [blk_mul, Units.val_mul, Matrix.det_mul, mul_inv]

theorem coe_blkHom (A : GL2) : ((blkHom A : SL3) : M3) = blk (A : M2) (A : M2).det⁻¹ := rfl

theorem blkHom_injective : Function.Injective blkHom := by
  intro A B h
  have h1 := congrArg (fun g : SL3 => (g : M3)) h
  simp only [coe_blkHom] at h1
  apply Units.ext
  ext i j
  have := congrFun (congrFun h1 (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [blk] using this

@[expose] noncomputable def z : SL3 := blkHom (-1)

theorem coe_z : (z : M3) = !![2, 0, 0; 0, 2, 0; 0, 0, 1] := by
  rw [z, coe_blkHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk] <;> decide

theorem eq_zero_of_eq_two_mul : ∀ x : ZMod 3, x = 2 * x → x = 0 := by decide

theorem eq_zero_of_eq_mul_two : ∀ x : ZMod 3, x = x * 2 → x = 0 := by decide

theorem centralizer_z_eq : centralizer {z} = blkHom.range := by
  apply le_antisymm
  · intro y hy
    have hc : y * z = z * y := mem_centralizer_singleton_iff.mp hy
    have hm := congrArg (fun g : SL3 => (g : M3)) hc
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_z] at hm
    have e : ∀ i j, (y : M3) i j * !![(2 : ZMod 3), 0, 0; 0, 2, 0; 0, 0, 1] j j =
        !![(2 : ZMod 3), 0, 0; 0, 2, 0; 0, 0, 1] i i * (y : M3) i j := by
      intro i j
      have := congrFun (congrFun hm i) j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three] at this ⊢ <;> linear_combination this
    have h02 : (y : M3) 0 2 = 0 := eq_zero_of_eq_two_mul _ (by simpa using e 0 2)
    have h12 : (y : M3) 1 2 = 0 := eq_zero_of_eq_two_mul _ (by simpa using e 1 2)
    have h20 : (y : M3) 2 0 = 0 := eq_zero_of_eq_mul_two _ (by simpa using (e 2 0).symm)
    have h21 : (y : M3) 2 1 = 0 := eq_zero_of_eq_mul_two _ (by simpa using (e 2 1).symm)
    set A : M2 := !![(y : M3) 0 0, (y : M3) 0 1; (y : M3) 1 0, (y : M3) 1 1] with hA
    have hy3 : (y : M3) = blk A ((y : M3) 2 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blk, hA, h02, h12, h20, h21]
    have hdet : A.det * (y : M3) 2 2 = 1 := by
      rw [← det_blk, ← hy3]
      exact y.2
    have hA0 : A.det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA0, ?_⟩
    apply Subtype.ext
    rw [coe_blkHom, hy3]
    congr 1
    exact (eq_inv_of_mul_eq_one_right hdet).symm
  · rintro _ ⟨A, rfl⟩
    rw [mem_centralizer_singleton_iff, z, ← map_mul, ← map_mul, mul_neg_one, neg_one_mul]

theorem card_centralizer_z : Nat.card (centralizer {z} : Subgroup SL3) = 48 := by
  rw [centralizer_z_eq, MonoidHom.range_eq_map, card_map_of_injective blkHom_injective,
    card_top, Matrix.card_GL_field]
  simp [ZMod.card, Fin.prod_univ_two]

@[expose] def sd16 : List M2 :=
  [!![0,1;1,0], !![0,1;2,0], !![0,2;1,0], !![0,2;2,0], !![1,0;0,1], !![1,0;0,2], !![1,1;1,2],
   !![1,1;2,1], !![1,2;1,1], !![1,2;2,2], !![2,0;0,1], !![2,0;0,2], !![2,1;1,1], !![2,1;2,2],
   !![2,2;1,2], !![2,2;2,1]]

theorem sd16_mul : ∀ M ∈ sd16, ∀ N ∈ sd16, M * N ∈ sd16 := by decide +kernel

theorem sd16_inv : ∀ M ∈ sd16, ∃ N ∈ sd16, M * N = 1 := by decide +kernel

theorem sd16_card : sd16.toFinset.card = 16 := by decide +kernel

theorem sd16_det : ∀ M ∈ sd16, M.det ≠ 0 := by decide +kernel

theorem sd16_comm : ∀ A : M2, A * !![1,1;2,1] = !![1,1;2,1] * A →
    A * !![1,0;0,2] = !![1,0;0,2] * A → A = 0 ∨ A = 1 ∨ A = 2 := by
  decide

@[expose] def P₂ : Subgroup GL2 where
  carrier := {A | (A : M2) ∈ sd16}
  mul_mem' {A B} hA hB := by
    show ((A * B : GL2) : M2) ∈ sd16
    rw [Units.val_mul]
    exact sd16_mul _ hA _ hB
  one_mem' := by
    show ((1 : GL2) : M2) ∈ sd16
    rw [Units.val_one]
    decide +kernel
  inv_mem' {A} hA := by
    show ((A⁻¹ : GL2) : M2) ∈ sd16
    obtain ⟨N, hN, hAN⟩ := sd16_inv _ hA
    have : (A⁻¹ : GL2).val = N := by
      calc (A⁻¹ : GL2).val = (A⁻¹ : GL2).val * ((A : M2) * N) := by rw [hAN, mul_one]
        _ = N := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [this]
    exact hN

theorem mem_P₂ {A : GL2} : A ∈ P₂ ↔ (A : M2) ∈ sd16 := Iff.rfl

theorem card_P₂ : Nat.card P₂ = 16 := by
  have h : (Units.val : GL2 → M2) '' (P₂ : Set GL2) = ((sd16.toFinset : Finset M2) : Set M2) := by
    ext M
    simp only [Set.mem_image, SetLike.mem_coe, mem_P₂, List.mem_toFinset]
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact hA
    · intro hM
      exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (sd16_det M hM), hM, rfl⟩
  have h2 := Nat.card_image_of_injective Units.val_injective (P₂ : Set GL2)
  rw [h, Nat.card_eq_card_toFinset, Finset.toFinset_coe, sd16_card] at h2
  exact h2.symm

@[expose] noncomputable def S₀ : Subgroup SL3 := P₂.map blkHom

theorem card_S₀ : Nat.card S₀ = 16 := by
  rw [S₀, card_map_of_injective blkHom_injective, card_P₂]

theorem card_SL3 : Nat.card SL3 = 5616 := by
  rw [Matrix.card_SL_field 3]
  norm_num [ZMod.card, Fin.prod_univ_three]

theorem isPGroup_S₀ : IsPGroup 2 S₀ := IsPGroup.of_card (n := 4) (by rw [card_S₀]; norm_num)

theorem not_two_dvd_index_S₀ : ¬ 2 ∣ S₀.index := by
  have h := S₀.card_mul_index
  rw [card_S₀, card_SL3] at h
  have h351 : S₀.index = 351 := by omega
  rw [h351]
  decide

theorem eq_one_or_eq_z (y : SL3) (hy : ∀ s ∈ S₀, s * y = y * s) : y = 1 ∨ y = z := by
  have hz : z ∈ S₀ := ⟨-1, by
    show ((-1 : GL2) : M2) ∈ sd16
    rw [Units.val_neg, Units.val_one]
    decide +kernel, rfl⟩
  have hyz : y ∈ centralizer {z} := mem_centralizer_singleton_iff.mpr (hy z hz).symm
  rw [centralizer_z_eq] at hyz
  obtain ⟨B, rfl⟩ := hyz
  have hcomm : ∀ A ∈ P₂, (A : M2) * B = B * A := by
    intro A hA
    have h1 := hy (blkHom A) ⟨A, hA, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Units.val (blkHom_injective h1)
  have ha := hcomm (Matrix.GeneralLinearGroup.mkOfDetNeZero !![1,1;2,1] (by decide))
    (by show (!![1,1;2,1] : M2) ∈ sd16; decide +kernel)
  have hb := hcomm (Matrix.GeneralLinearGroup.mkOfDetNeZero !![1,0;0,2] (by decide))
    (by show (!![1,0;0,2] : M2) ∈ sd16; decide +kernel)
  rcases sd16_comm (B : M2) ha.symm hb.symm with h | h | h
  · exact absurd (h ▸ det_ne_zero_of_gl B) (by simp)
  · left
    rw [show B = 1 from Units.ext h, map_one]
  · right
    rw [z]
    congr 1
    apply Units.ext
    rw [h, Units.val_neg, Units.val_one]
    decide

theorem exists_conj {S : Subgroup SL3} (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) :
    ∃ g : SL3, ∀ x : SL3, x ∈ S ↔ g⁻¹ * x * g ∈ S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL3 (isPGroup_S₀.toSylow not_two_dvd_index_S₀)
    (hS.toSylow hSi)
  refine ⟨g, fun x => ?_⟩
  have h2 : ((g • isPGroup_S₀.toSylow not_two_dvd_index_S₀ : Sylow 2 SL3) : Subgroup SL3) = S := by
    rw [hg, IsPGroup.toSylow_coe]
  rw [← h2, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply, IsPGroup.toSylow_coe]

theorem card_centralizer_conj {G : Type*} [Group G] (g x : G) :
    Nat.card (centralizer {g * x * g⁻¹} : Subgroup G) =
      Nat.card (centralizer {x} : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨g⁻¹ * c * g, ?_⟩
      invFun := fun c => ⟨g * c * g⁻¹, ?_⟩
      left_inv := fun c => Subtype.ext (by simp [mul_assoc])
      right_inv := fun c => Subtype.ext (by simp [mul_assoc]) }
  · have hc := mem_centralizer_singleton_iff.mp c.2
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * c * g * x = g⁻¹ * ((c : G) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * c) * g := by rw [hc]
      _ = x * (g⁻¹ * c * g) := by group
  · have hc := mem_centralizer_singleton_iff.mp c.2
    rw [mem_centralizer_singleton_iff]
    calc g * c * g⁻¹ * (g * x * g⁻¹) = g * ((c : G) * x) * g⁻¹ := by group
      _ = g * (x * c) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * (g * c * g⁻¹) := by group

theorem comm_conj {S : Subgroup SL3} {g : SL3} (hg : ∀ x : SL3, x ∈ S ↔ g⁻¹ * x * g ∈ S₀)
    {y : SL3} (hy : ∀ s ∈ S, s * y = y * s) : ∀ s ∈ S₀, s * (g⁻¹ * y * g) = g⁻¹ * y * g * s := by
  intro s hs
  have hs' : g * s * g⁻¹ ∈ S := (hg _).mpr (by simpa [mul_assoc] using hs)
  have h := hy _ hs'
  calc s * (g⁻¹ * y * g) = g⁻¹ * ((g * s * g⁻¹) * y) * g := by group
    _ = g⁻¹ * (y * (g * s * g⁻¹)) * g := by rw [h]
    _ = g⁻¹ * y * g * s := by group

theorem z_mul_z : z * z = 1 := by
  rw [z, ← map_mul, neg_one_mul, neg_neg, map_one]

@[expose] noncomputable def pslEquiv : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3) ≃* SL3 :=
  (QuotientGroup.quotientMulEquivOfEq CFSG.GH74.KGroups.L33.center_bot).trans
    QuotientGroup.quotientBot

theorem index_inner :
    (MulAut.conj : SL3 →* MulAut SL3).range.index = 2 := by
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.L33.equiv_psl_P13
  obtain ⟨e2⟩ := CFSG.GH74.KGroups.L33.equiv_P13_P
  have hAut := CFSG.GH74.KGroups.L33.card_mulAut ((pslEquiv.symm.trans e1).trans e2)
  have hinj : Function.Injective (MulAut.conj : SL3 →* MulAut SL3) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conj_eq_center, CFSG.GH74.KGroups.L33.center_bot]
  have hI : Nat.card (MulAut.conj : SL3 →* MulAut SL3).range = 5616 := by
    rw [MonoidHom.range_eq_map, card_map_of_injective hinj, card_top, card_SL3]
  have h := (MulAut.conj : SL3 →* MulAut SL3).range.card_mul_index
  rw [hI, hAut] at h
  omega

theorem kg115Excluded_SL3 : KG115Excluded SL3 := by
  refine kg115Excluded_of_at CFSG.GH74.KGroups.L33.center_bot ?_ ?_
  · intro S hS hSi y hy3 hyS
    obtain ⟨g, hg⟩ := exists_conj hS hSi
    rcases eq_one_or_eq_z _ (comm_conj hg hyS) with h1 | h1
    · have hy1 : y = 1 := by
        have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        rw [this, h1]
        group
      rw [hy1, orderOf_one] at hy3
      exact absurd hy3 (by decide)
    · have hy2 : y ^ 2 = 1 := by
        have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        rw [this, h1, pow_two]
        calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
          _ = 1 := by rw [z_mul_z]; group
      have := orderOf_dvd_of_pow_eq_one hy2
      rw [hy3] at this
      exact absurd this (by decide)
  · intro S hS hSi l _ hlc hl1
    apply kg115At_of_card
    obtain ⟨g, hg⟩ := exists_conj hS hSi
    rcases eq_one_or_eq_z _ (comm_conj hg hlc) with h1 | h1
    · exfalso
      apply hl1
      have : l = g * (g⁻¹ * l * g) * g⁻¹ := by group
      rw [this, h1]
      group
    · have hl : l = g * z * g⁻¹ := by
        have : l = g * (g⁻¹ * l * g) * g⁻¹ := by group
        rw [this, h1]
      rw [hl, card_centralizer_conj, card_centralizer_z, index_inner]
      decide

theorem kg115L33Input_holds : KG115L33Input := by
  intro X _ hX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated (F := ZMod 3) 3 3 1 (by norm_num)
    CFSG.GH74.KGroups.L33.card_F hX
  exact kg115Excluded_of_mulEquiv (e.trans pslEquiv) kg115Excluded_SL3

end CFSG.Quasithin.H13.KG115L33

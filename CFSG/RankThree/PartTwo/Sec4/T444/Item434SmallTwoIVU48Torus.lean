module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Model
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVTorus
public import CFSG.RankThree.PartOne.SEITZ2.SUnBlocks
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Phan CFSG.RankThree.PartOne.SEITZ2
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc torusSnoc_last
  prod_torusSnoc torusSnoc_mem diagHom_mem_su pow_eq_one_of_mem_rootsOfUnity
  card_rootsOfUnity_of_dvd_card_units)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)

abbrev μ3 : Subgroup Kˣ := rootsOfUnity 3 K

theorem card_μ3 : Nat.card μ3 = 3 :=
  card_rootsOfUnity_of_dvd_card_units (by rw [card_units_K]; norm_num)

@[expose] def torusGL : (Fin 3 → μ3) →* GL (Fin 4) K :=
  (CFSG.RankThree.PartTwo.Sec4.Census.diagHom (K := K) (ι := Fin 4)).comp
    ((torusSnoc (K := K) 3).comp (μ3.subtype.compLeft (Fin 3)))

theorem torusGL_mem (a : Fin 3 → μ3) : torusGL a ∈ SUid σ4 4 := by
  have hU9 : ∀ u ∈ μ3, u ^ (2 ^ 3 + 1) = 1 := fun u hu =>
    pow_eq_one_of_mem_rootsOfUnity (by norm_num) hu
  have h := diagHom_mem_su 2 3 (n := 4) (d := torusSnoc 3 (fun i => (a i : Kˣ)))
    (prod_torusSnoc 3 _) fun j => hU9 _ (torusSnoc_mem 3 (fun i => (a i).2) j)
  rw [SU4_eq_stated]
  refine Subgroup.subset_closure ⟨?_, h.2⟩
  have h1 := congrArg Units.val h.1
  rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h1

@[expose] def torusSU4 : (Fin 3 → μ3) →* SU4 :=
  torusGL.codRestrict _ torusGL_mem

theorem coe_torusSU4 (a : Fin 3 → μ3) :
    (((torusSU4 a : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal fun k => (torusSnoc 3 (fun i => (a i : Kˣ)) k : K) :=
  rfl

theorem torusSU4_injective : Function.Injective torusSU4 := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : (((torusSU4 a : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [ha]
    rfl
  rw [coe_torusSU4] at h1
  funext i
  apply Subtype.ext
  apply Units.ext
  have h2 := congrFun (congrFun h1 i.castSucc) i.castSucc
  rw [diagonal_apply_eq, one_apply_eq, torusSnoc_castSucc] at h2
  exact h2

@[expose] def Dstd : Subgroup SU4 := torusSU4.range

theorem card_Dstd : Nat.card Dstd = 27 := by
  unfold Dstd
  rw [← Nat.card_congr (MonoidHom.ofInjective torusSU4_injective).toEquiv, Nat.card_fun,
    Nat.card_fin, card_μ3]
  norm_num

theorem commute_Dstd : ∀ x ∈ Dstd, ∀ y ∈ Dstd, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg torusSU4 (mul_comm a b)

theorem pow_three_Dstd : ∀ x ∈ Dstd, x ^ 3 = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow]
  have : a ^ 3 = 1 := funext fun i => CFSG.RankThree.PartTwo.Census.rootsOfUnity_pow_eq_one (a i)
  rw [this, map_one]

theorem isElemAbelian_Dstd : CFSG.Assembly.IsElemAbelian 3 Dstd :=
  ⟨⟨⟨fun x y => Subtype.ext (commute_Dstd x x.2 y y.2)⟩⟩, pow_three_Dstd⟩

@[expose] def entryChar (k : Fin 4) : (Fin 3 → μ3) →* Kˣ :=
  (Pi.evalMonoidHom (fun _ => Kˣ) k).comp
    ((torusSnoc (K := K) 3).comp (μ3.subtype.compLeft (Fin 3)))

theorem entryChar_apply (k : Fin 4) (a : Fin 3 → μ3) :
    entryChar k a = torusSnoc 3 (fun i => (a i : Kˣ)) k :=
  rfl

@[expose] def eqChar (i : Fin 3) : (Fin 3 → μ3) →* Kˣ :=
  entryChar i.castSucc / entryChar i.succ

theorem eqChar_apply (i : Fin 3) (a : Fin 3 → μ3) :
    eqChar i a = entryChar i.castSucc a / entryChar i.succ a :=
  rfl

@[expose] def Bsub (i : Fin 3) : Subgroup SU4 :=
  (eqChar i).ker.map torusSU4

theorem Bsub_le_Dstd (i : Fin 3) : Bsub i ≤ Dstd :=
  Subgroup.map_le_range _ _

theorem card_Bsub (i : Fin 3) : 9 ≤ Nat.card (Bsub i) := by
  unfold Bsub
  rw [Subgroup.card_map_of_injective torusSU4_injective]
  have h27 : Nat.card (Fin 3 → μ3) = 27 := by
    rw [Nat.card_fun, Nat.card_fin, card_μ3]
    norm_num
  have h1 := Subgroup.card_ker_mul_card_range (eqChar i)
  rw [h27] at h1
  have hr : (eqChar i).range ≤ μ3 := by
    rintro _ ⟨a, rfl⟩
    rw [eqChar_apply, entryChar_apply, entryChar_apply, mem_rootsOfUnity]
    have hU : ∀ k, torusSnoc 3 (fun j => (a j : Kˣ)) k ∈ μ3 := fun k =>
      torusSnoc_mem 3 (fun j => (a j).2) k
    rw [div_pow, (mem_rootsOfUnity 3 _).mp (hU _), (mem_rootsOfUnity 3 _).mp (hU _), div_one]
  have h3 : Nat.card (eqChar i).range ≤ 3 := by
    have := Subgroup.card_le_of_le hr
    rwa [card_μ3] at this
  have : Nat.card (eqChar i).ker * Nat.card (eqChar i).range ≤ Nat.card (eqChar i).ker * 3 :=
    Nat.mul_le_mul_left _ h3
  omega

theorem diagonal_mul_blockMat {F : Type*} [Field F] {m k i : ℕ} (d : Fin m → F) (c : F)
    (hd : ∀ (a : Fin m) (j : Fin k), a.val = i + j.val → d a = c)
    (A : Matrix (Fin k) (Fin k) F) :
    diagonal d * CFSG.ClassicalInvolution.Phan.blockMat m i A =
      CFSG.ClassicalInvolution.Phan.blockMat m i A * diagonal d := by
  have h1 : diagonal d * blockSel F m k i = c • blockSel F m k i := by
    ext a j
    rw [diagonal_mul, Matrix.smul_apply, smul_eq_mul, blockSel_apply]
    split_ifs with h
    · rw [hd a j h]
    · simp
  have h2 : (blockSel F m k i)ᵀ * diagonal d = c • (blockSel F m k i)ᵀ := by
    ext j a
    rw [mul_diagonal, Matrix.smul_apply, smul_eq_mul, transpose_apply, blockSel_apply]
    split_ifs with h
    · rw [hd a j h, one_mul, mul_one]
    · simp
  unfold CFSG.ClassicalInvolution.Phan.blockMat
  have e1 : diagonal d * (1 + blockSel F m k i * (A - 1) * (blockSel F m k i)ᵀ) =
      diagonal d + c • (blockSel F m k i * (A - 1) * (blockSel F m k i)ᵀ) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1,
      Matrix.smul_mul, Matrix.smul_mul]
  have e2 : (1 + blockSel F m k i * (A - 1) * (blockSel F m k i)ᵀ) * diagonal d =
      diagonal d + c • (blockSel F m k i * (A - 1) * (blockSel F m k i)ᵀ) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_assoc]
  rw [e1, e2]

theorem coe_coe_blockEmb2 {n : ℕ} (i : Fin n) (X : Su K 2 3 2) :
    (((blockEmb2 K 2 3 n i X : Su K 2 3 (n + 1)) : GL (Fin (n + 1)) K) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      CFSG.ClassicalInvolution.Phan.blockMat (n + 1) i
        (((X : Su K 2 3 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem mem_Bsub_comm_block (i : Fin 3) {b : SU4} (hb : b ∈ Bsub i) (X : Su K 2 3 2) :
    b * blockEmb2 K 2 3 3 i X = blockEmb2 K 2 3 3 i X * b := by
  obtain ⟨a, ha, rfl⟩ := hb
  have hker : entryChar i.castSucc a = entryChar i.succ a :=
    div_eq_one.mp ((MonoidHom.mem_ker).mp ha)
  apply Subtype.ext
  apply Units.ext
  change (((torusSU4 a : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (((blockEmb2 K 2 3 3 i X : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    (((blockEmb2 K 2 3 3 i X : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (((torusSU4 a : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  rw [coe_torusSU4, coe_coe_blockEmb2]
  refine diagonal_mul_blockMat _ ((entryChar i.castSucc a : Kˣ) : K) ?_ _
  intro x j hxj
  fin_cases j
  · have : x = i.castSucc := Fin.ext (by simpa using hxj)
    rw [this]
    rfl
  · have : x = i.succ := Fin.ext (by simpa using hxj)
    rw [this]
    exact congrArg (fun u : Kˣ => (u : K)) hker.symm

theorem tv_mul_self {X : Su K 2 3 2} (hX : X ∈ tvSet (unitaryInvolution K 2 3) 2) : X * X = 1 := by
  obtain ⟨a, c, ha, -, hv⟩ := hX
  apply ext_smul
  intro v
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hXa : X • a = a := by rw [hv a, ha, mul_zero, zero_smul, add_zero]
  rw [mul_smul, one_smul, hv v, smul_add, smul_comm X (c * herm (unitaryInvolution K 2 3) a v) a,
    hXa, hv v, add_assoc, ← two_smul K, h2, zero_smul, add_zero]

theorem closure_coprime_centralized_eq_top :
    Subgroup.closure {x : SU4 | Nat.Coprime (orderOf x) 3 ∧
      ∃ i : Fin 3, ∀ b ∈ Bsub i, b * x = x * b} = ⊤ := by
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
    (K := K) (p := 2) (f := 3) card_K
  refine eq_top_of_blocks (K := K) (f := 3) (n := 3) card_K (by norm_num) fun i => ?_
  rintro _ ⟨X, rfl⟩
  have hT : X ∈ T (unitaryInvolution K 2 3) 2 := by
    rw [T_two_eq_top hσ]
    trivial
  induction hT using Subgroup.closure_induction with
  | mem t ht =>
    refine Subgroup.subset_closure ⟨?_, i, fun b hb => mem_Bsub_comm_block i hb t⟩
    have h2 : blockEmb2 K 2 3 3 i t ^ 2 = 1 := by
      rw [pow_two, ← map_mul, tv_mul_self ht, map_one]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2) (by norm_num)
  | one =>
    rw [map_one]
    exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [map_inv]
    exact Subgroup.inv_mem _ hx

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48

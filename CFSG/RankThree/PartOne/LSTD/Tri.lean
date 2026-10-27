module

public import CFSG.RankThree.PartOne.CTP.LStd
public import CFSG.RankThree.PartOne.KF.SymTorus
public import CFSG.RankThree.PartOne.LSTD.Lines

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP
open CFSG.ClassicalInvolution.Phan (blockSel blockSel_apply blockMat blockEmb blockMat_injective
  range_blockEmb3 blockGL coe_blockGL blockGL_mem_SUid blockMat_apply_of_not_mem_left
  blockMat_apply)
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)

variable {f : ℕ} {K : Type} [Field K]

theorem e3_val (a : Fin 3) : (e3 a : ℕ) = a := rfl

theorem e3_injective : Function.Injective e3 := fun a b h =>
  Fin.ext (by simpa [e3_val] using congrArg Fin.val h)

theorem e3_ne {a b : Fin 3} (hab : a ≠ b) : e3 a ≠ e3 b := e3_injective.ne hab

theorem blockSel_mul_coordIncl (a b : Fin 3) :
    blockSel K 5 3 0 * coordIncl K a b = coordIncl K (e3 a) (e3 b) := by
  have key : ∀ (t : Fin 3) (k : Fin 5), ∑ j : Fin 3,
      (if (k : ℕ) = 0 + (j : ℕ) then (1 : K) else 0) * (if j = t then 1 else 0) =
        if k = e3 t then 1 else 0 := by
    intro t k
    rw [Finset.sum_eq_single t]
    · simp [Fin.ext_iff, e3_val]
    · intro j _ hj
      simp [hj]
    · simp
  ext k c
  simp only [Matrix.mul_apply, blockSel_apply, coordIncl, Matrix.of_apply]
  fin_cases c
  · exact key a k
  · exact key b k

theorem blockMat_coordEmbed (a b : Fin 3) (X : Matrix (Fin 2) (Fin 2) K) :
    blockMat 5 0 (coordEmbed K a b X) = coordEmbed K (e3 a) (e3 b) X := by
  have hLI := blockSel_mul_coordIncl (K := K) a b
  unfold blockMat coordEmbed coordProj
  rw [add_sub_cancel_left, ← hLI, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem mem_blk_e3_iff (hU : UnitaryFieldData 2 f K) {a b : Fin 3} (hab : a ≠ b)
    (g : GL (Fin 3) K) :
    blockGL (F := K) 5 0 (by omega) g ∈ blk hU (e3_ne hab) ↔ g ∈ blk hU hab := by
  constructor
  · intro hg
    obtain ⟨X, hX, hgX⟩ := (mem_blk_iff (e3_ne hab)).mp hg
    refine (mem_blk_iff hab).mpr ⟨X, hX, ?_⟩
    apply blockMat_injective (m := 5) (i := 0) (by omega)
    rw [← coe_blockGL (by omega : 0 + 3 ≤ 5), hgX, blockMat_coordEmbed]
  · intro hg
    obtain ⟨X, hX, hgX⟩ := (mem_blk_iff hab).mp hg
    refine (mem_blk_iff (e3_ne hab)).mpr ⟨X, hX, ?_⟩
    rw [coe_blockGL (by omega : 0 + 3 ≤ 5), hgX, blockMat_coordEmbed]

theorem blockGL_mem_unitarySU (hU : UnitaryFieldData 2 f K) {g : GL (Fin 3) K}
    (hg : g ∈ unitarySU 2 f K 3) : blockGL (F := K) 5 0 (by omega) g ∈ unitarySU 2 f K 5 := by
  have := hU.finite
  have : CharP K 2 := hU.charP
  have hK : Nat.card K = (2 ^ f) ^ 2 := hU.card_eq_sq
  have hg' : g ∈ SUid (unitaryInvolution K 2 f) 3 := by
    rw [SUid_eq_statedSU hK 3]
    exact hg
  have := blockGL_mem_SUid (unitaryInvolution K 2 f) (m := 5) (k := 3) (i := 0) (by omega) hg'
  rw [SUid_eq_statedSU hK 5] at this
  exact this

@[expose] noncomputable def emb3 (hU : UnitaryFieldData 2 f K) :
    ↥(unitarySU 2 f K 3) →* ↥(unitarySU 2 f K 5) :=
  ((blockGL (F := K) 5 0 (by omega)).comp (unitarySU 2 f K 3).subtype).codRestrict _
    fun g => blockGL_mem_unitarySU hU g.2

theorem coe_emb3 (hU : UnitaryFieldData 2 f K) (A : ↥(unitarySU 2 f K 3)) :
    ((emb3 hU A : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) =
      blockGL (F := K) 5 0 (by omega) (A : GL (Fin 3) K) := rfl

theorem emb3_injective (hU : UnitaryFieldData 2 f K) : Function.Injective (emb3 hU) := by
  intro A B h
  have h1 := congrArg (fun x : ↥(unitarySU 2 f K 5) =>
    ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) h
  simp only [coe_emb3, coe_blockGL] at h1
  exact Subtype.ext (Units.ext (blockMat_injective (m := 5) (i := 0) (by omega) h1))

theorem emb3_entry_four (hU : UnitaryFieldData 2 f K) (A : ↥(unitarySU 2 f K 3)) :
    (((emb3 hU A : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4 = 1 := by
  show blockMat 5 0 ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 4 4 = 1
  rw [blockMat_apply_of_not_mem_left _ (by decide)]
  simp

theorem scalar_eq_one_of_entry (hU : UnitaryFieldData 2 f K) (A : ↥(unitarySU 2 f K 3))
    {z : ↥(unitarySU 2 f K 5)} (hz : z ∈ scalarsU K f)
    (h44 : (((emb3 hU A * z : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) 4 4 = 1) :
    z = 1 := by
  obtain ⟨c, hc⟩ := exists_of_mem_scalarsU hz
  have h1 : (c : K) = 1 := by
    rw [Subgroup.coe_mul, Units.val_mul, hc, diagU_val, Matrix.mul_diagonal,
      emb3_entry_four hU A, one_mul] at h44
    exact h44
  have hc1 : c = 1 := Units.ext h1
  apply Subtype.ext
  rw [hc, hc1]
  exact diagU_one

theorem emb3_mem_Bk_iff (hU : UnitaryFieldData 2 f K) {a b : Fin 3} (hab : a ≠ b)
    (A : ↥(unitarySU 2 f K 3)) :
    emb3 hU A ∈ Bk hU (e3_ne hab) ↔ (A : GL (Fin 3) K) ∈ blk hU hab := by
  rw [mem_Bk_iff, coe_emb3]
  exact mem_blk_e3_iff hU hab _

@[expose] noncomputable def theta3 (hU : UnitaryFieldData 2 f K) :
    ↥(unitarySU 2 f K 3) →* StatedProj (unitarySU 2 f K 5) :=
  (projU K f).comp (emb3 hU)

theorem theta3_apply (hU : UnitaryFieldData 2 f K) (A : ↥(unitarySU 2 f K 3)) :
    theta3 hU A = projU K f (emb3 hU A) := rfl

theorem theta3_injective (hU : UnitaryFieldData 2 f K) : Function.Injective (theta3 hU) := by
  intro A B h
  obtain ⟨z, hz, hzAB⟩ := projU_eq_iff.mp h
  have hz1 : z = 1 := by
    apply scalar_eq_one_of_entry hU B hz
    rw [← hzAB]
    exact emb3_entry_four hU A
  apply emb3_injective hU
  rw [hzAB, hz1, mul_one]

theorem theta3_mem_Jfun_iff (hU : UnitaryFieldData 2 f K) {a b : Fin 3} (hab : a ≠ b)
    (A : ↥(unitarySU 2 f K 3)) :
    theta3 hU A ∈ Jfun hU (e3 a) (e3 b) ↔ (A : GL (Fin 3) K) ∈ blk hU hab := by
  rw [theta3_apply, Jfun_of_ne hU (e3_ne hab), mem_map_projU_iff]
  constructor
  · rintro ⟨z, hz, hzB⟩
    have h4a : (4 : Fin 5) ≠ e3 a := fun h => by
      have := congrArg Fin.val h
      rw [e3_val] at this
      have := a.isLt
      simp at *
      omega
    have h4b : (4 : Fin 5) ≠ e3 b := fun h => by
      have := congrArg Fin.val h
      rw [e3_val] at this
      have := b.isLt
      simp at *
      omega
    have hz1 : z = 1 := by
      apply scalar_eq_one_of_entry hU A hz
      obtain ⟨X, -, hX⟩ := (mem_blk_iff (e3_ne hab)).mp ((mem_Bk_iff hU (e3_ne hab)).mp hzB)
      have e1 := congrFun (congrFun hX 4) 4
      rw [coordEmbed_apply_of_not_mem_left h4a h4b] at e1
      rw [e1]
      simp
    rw [hz1, mul_one] at hzB
    exact (emb3_mem_Bk_iff hU hab A).mp hzB
  · intro h
    exact ⟨1, one_mem _, by rw [mul_one]; exact (emb3_mem_Bk_iff hU hab A).mpr h⟩

theorem blk_zero_one_sup_blk_one_two_five [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 2 ^ f ≠ 2) :
    blk h (show (0 : Fin 5) ≠ 1 by decide) ⊔ blk h (show (1 : Fin 5) ≠ 2 by decide) =
      (blockEmb K 2 f 5 3 0 (by omega)).range.map (SUid (unitaryInvolution K 2 f) 5).subtype := by
  rw [blk_eq_map_blockEmb_adjacent h (m := 5) (i := 0) (by omega) (a := 0) (b := 1) rfl rfl
    (by decide), blk_eq_map_blockEmb_adjacent h (m := 5) (i := 1) (by omega) (a := 1) (b := 2)
    rfl rfl (by decide), ← Subgroup.map_sup]
  congr 1
  exact (range_blockEmb3 hK hq 4 0 (by decide)).symm

theorem range_emb3 (hU : UnitaryFieldData 2 f K) (hf2 : 2 ≤ f) :
    (emb3 hU).range = Bk hU (show (0 : Fin 5) ≠ 1 by decide) ⊔
      Bk hU (show (1 : Fin 5) ≠ 2 by decide) := by
  have := hU.finite
  have : CharP K 2 := hU.charP
  have hK : Nat.card K = (2 ^ f) ^ 2 := hU.card_eq_sq
  have hq : 2 ^ f ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  unfold Bk
  rw [← Subgroup.subgroupOf_sup (blk_le_unitarySU _) (blk_le_unitarySU _),
    blk_zero_one_sup_blk_one_two_five hU hK hq]
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨A, rfl⟩
    have hA : (A : GL (Fin 3) K) ∈ SUid (unitaryInvolution K 2 f) 3 := by
      rw [SUid_eq_statedSU hK 3]
      exact A.2
    exact ⟨blockEmb K 2 f 5 3 0 (by omega) ⟨A, hA⟩, ⟨_, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨B, rfl⟩, hyx⟩
    have hB : (B : GL (Fin 3) K) ∈ unitarySU 2 f K 3 :=
      (Subgroup.ext_iff.mp (SUid_eq_statedSU hK 3) (B : GL (Fin 3) K)).mp B.2
    exact ⟨⟨(B : GL (Fin 3) K), hB⟩, Subtype.ext hyx⟩

theorem blockGL_injective : Function.Injective (blockGL (F := K) 5 0 (by omega : 0 + 3 ≤ 5)) := by
  intro g h hgh
  apply Units.ext
  apply blockMat_injective (m := 5) (i := 0) (by omega)
  have := congrArg (fun x : GL (Fin 5) K => (x : Matrix (Fin 5) (Fin 5) K)) hgh
  simpa [coe_blockGL] using this

@[expose] def extU (d : Fin 3 → Kˣ) : Fin 5 → Kˣ :=
  fun i => if h : (i : ℕ) < 3 then d ⟨i, h⟩ else 1

theorem extU_e3 (d : Fin 3 → Kˣ) (a : Fin 3) : extU d (e3 a) = d a := by
  simp [extU, e3_val]

theorem extU_three (d : Fin 3 → Kˣ) : extU d 3 = 1 := by simp [extU]

theorem extU_four (d : Fin 3 → Kˣ) : extU d 4 = 1 := by simp [extU]

theorem blockGL_diagU (d : Fin 3 → Kˣ) :
    blockGL (F := K) 5 0 (by omega) (diagU d) = diagU (extU d) := by
  apply Units.ext
  rw [coe_blockGL, diagU_val, diagU_val]
  ext a b
  rw [blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp [extU]

theorem extU_mem {d : Fin 3 → Kˣ} (hd : d ∈ torusVec 5 3 K) : extU d ∈ torusVec 5 5 K := by
  have e0 : extU d 0 = d 0 := by simp [extU]
  have e1 : extU d 1 = d 1 := by simp [extU]
  have e2 : extU d 2 = d 2 := by simp [extU]
  refine ⟨fun i => ?_, ?_⟩
  · by_cases h : (i : ℕ) < 3
    · simp only [extU, h, dite_true]
      exact hd.1 _
    · simp [extU, h]
  · have := hd.2
    rw [Fin.prod_univ_three] at this
    rw [Fin.prod_univ_five, e0, e1, e2, extU_three, extU_four, mul_one, mul_one]
    exact this

theorem theta3_mem_torusBar_iff (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (A : ↥(unitarySU 2 f K 3)) :
    theta3 hU A ∈ torusBar K f ↔ (A : GL (Fin 3) K) ∈ torusSU 5 3 K := by
  constructor
  · intro hA
    obtain ⟨v, hv, hAv⟩ := (mem_torusBar_iff hU h5).mp hA
    obtain ⟨z, hz, hzeq⟩ := projU_eq_iff.mp
      (show projU K f (emb3 hU A) = projU K f (tSU hU h5 v hv) from hAv)
    obtain ⟨c, hc⟩ := exists_of_mem_scalarsU hz
    have hc5 : c ^ 5 = 1 := pow_five_eq_one_of_mem_scalarsU hU hc
    have hGL : blockGL (F := K) 5 0 (by omega) (A : GL (Fin 3) K) =
        diagU (v * fun _ : Fin 5 => c) := by
      have := congrArg (fun x : ↥(unitarySU 2 f K 5) => (x : GL (Fin 5) K)) hzeq
      simp only [coe_emb3, Subgroup.coe_mul, coe_tSU, hc, diagU_mul] at this
      exact this
    have hent : ∀ k : Fin 5, ¬ ((0 : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < 0 + 3) →
        (v * fun _ : Fin 5 => c) k = 1 := by
      intro k hk
      have := congrArg (fun x : GL (Fin 5) K => (x : Matrix (Fin 5) (Fin 5) K) k k) hGL
      simp only [coe_blockGL, diagU_val, Matrix.diagonal_apply_eq] at this
      rw [blockMat_apply_of_not_mem_left _ hk] at this
      exact Units.ext (by simpa using this.symm)
    have h3 := hent 3 (by decide)
    have h4 := hent 4 (by decide)
    set w : Fin 5 → Kˣ := v * fun _ : Fin 5 => c with hw
    set d : Fin 3 → Kˣ := fun a => w (e3 a) with hd
    have hext : extU d = w := by
      funext i
      fin_cases i
      · simp [extU, hd, e3, Fin.castLE]
      · simp [extU, hd, e3, Fin.castLE]
      · simp [extU, hd, e3, Fin.castLE]
      · show extU d 3 = w 3
        rw [extU_three, h3]
      · show extU d 4 = w 4
        rw [extU_four, h4]
    have hA' : (A : GL (Fin 3) K) = diagU d := by
      apply blockGL_injective
      rw [hGL, blockGL_diagU, hext]
    refine mem_torusSU_iff.mpr ⟨d, ?_, ?_, hA'.symm⟩
    · intro a
      simp only [hd, hw, Pi.mul_apply, mul_pow, hv.1, hc5, one_mul]
    · have hdet := ((mem_unitarySU_iff hU).mp A.2).1
      rw [hA', det_diagU] at hdet
      exact Units.ext (by simpa using hdet)
  · intro hA
    obtain ⟨d, hd1, hd2, hdA⟩ := mem_torusSU_iff.mp hA
    refine (mem_torusBar_iff hU h5).mpr ⟨extU d, extU_mem ⟨hd1, hd2⟩, ?_⟩
    rw [theta3_apply]
    congr 1
    apply Subtype.ext
    rw [coe_emb3, coe_tSU, ← hdA, blockGL_diagU]

theorem Bk_e3_le_range (hU : UnitaryFieldData 2 f K) {a b : Fin 3} (hab : a ≠ b) :
    Bk hU (e3_ne hab) ≤ (emb3 hU).range := by
  intro y hy
  obtain ⟨X, hX, hyX⟩ := (mem_blk_iff (e3_ne hab)).mp ((mem_Bk_iff hU (e3_ne hab)).mp hy)
  have hg : (Units.map (coordEmbedHom K a b hab) X : GL (Fin 3) K) ∈ blk hU hab :=
    (mem_blk_iff hab).mpr ⟨X, hX, rfl⟩
  refine ⟨⟨_, blk_le_unitarySU hab hg⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show blockMat 5 0 (coordEmbed K a b (X : Matrix (Fin 2) (Fin 2) K)) = _
  rw [blockMat_coordEmbed]
  exact hyX.symm

theorem Kbar_eq_range (hU : UnitaryFieldData 2 f K) (hf2 : 2 ≤ f) :
    Jfun hU 0 1 ⊔ Jfun hU 1 2 = (theta3 hU).range := by
  rw [Jfun_of_ne hU (by decide : (0 : Fin 5) ≠ 1), Jfun_of_ne hU (by decide : (1 : Fin 5) ≠ 2),
    ← Subgroup.map_sup, ← range_emb3 hU hf2, theta3, MonoidHom.range_comp]

theorem Jfun_e3_le_range (hU : UnitaryFieldData 2 f K) {a b : Fin 3} (hab : a ≠ b) :
    Jfun hU (e3 a) (e3 b) ≤ (theta3 hU).range := by
  rw [Jfun_of_ne hU (e3_ne hab), theta3, MonoidHom.range_comp]
  exact Subgroup.map_mono (Bk_e3_le_range hU hab)

theorem torusBar_inf_Kbar (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (hf2 : 2 ≤ f) :
    torusBar K f ⊓ (Jfun hU 0 1 ⊔ Jfun hU 1 2) =
      ((torusSU 5 3 K).subgroupOf (unitarySU 2 f K 3)).map (theta3 hU) := by
  rw [Kbar_eq_range hU hf2]
  ext x
  constructor
  · rintro ⟨hxT, A, rfl⟩
    exact ⟨A, (theta3_mem_torusBar_iff hU h5 A).mp hxT, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨(theta3_mem_torusBar_iff hU h5 A).mpr hA, A, rfl⟩

theorem card_torusBar_inf_Kbar [Finite K] (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (hf2 : 2 ≤ f) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) :
    Nat.card ↥(torusBar K f ⊓ (Jfun hU 0 1 ⊔ Jfun hU 1 2)) = 25 := by
  rw [torusBar_inf_Kbar hU h5 hf2, Subgroup.card_map_of_injective (theta3_injective hU),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (torusSU_le_unitarySU hU h5)).toEquiv, torusSU,
    Subgroup.card_map_of_injective diagU_injective]
  exact KFU.card_torusVec_eq (by norm_num) hζ 2

end CFSG.RankThree.PartOne.LSTD

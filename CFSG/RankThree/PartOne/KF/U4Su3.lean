module

public import CFSG.RankThree.PartOne.KF.U4Blk
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryCoord
open CFSG.ClassicalInvolution.Phan (blockSel blockSel_apply blockMat blockEmb blockEmb_injective
  range_blockEmb3)
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)

section Adjacent

variable {K : Type} [Field K]

theorem coordIncl_eq_blockSel_adjacent {m i : ℕ} (hi : i + 1 < m) :
    coordIncl K (⟨i, by omega⟩ : Fin m) ⟨i + 1, hi⟩ = blockSel K m 2 i := by
  ext k a
  fin_cases a
  · by_cases hk : (k : ℕ) = i <;> simp [coordIncl, blockSel_apply, Fin.ext_iff, hk]
  · by_cases hk : (k : ℕ) = i + 1 <;> simp [coordIncl, blockSel_apply, Fin.ext_iff, hk]

theorem coordEmbed_eq_blockMat_adjacent {m i : ℕ} (hi : i + 1 < m)
    (X : Matrix (Fin 2) (Fin 2) K) :
    coordEmbed K (⟨i, by omega⟩ : Fin m) ⟨i + 1, hi⟩ X = blockMat m i X := by
  unfold coordEmbed coordProj blockMat
  rw [coordIncl_eq_blockSel_adjacent hi]

end Adjacent

section PhanBlocks

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem mem_gramSU_idGram_iff_mem_SUid {n : ℕ} {X : GL (Fin n) K} :
    X ∈ gramSU h (idGram K n) ↔ X ∈ SUid (unitaryInvolution K 2 f) n := by
  rw [SUid_eq_statedSU h.card_eq_sq n]
  change X ∈ gramSU h (idGram K n) ↔ X ∈ unitarySU 2 f K n
  rw [unitarySU_eq_gramSU h n]
  exact Iff.rfl

theorem blk_eq_map_blockEmb_adjacent {m i : ℕ} (hi : i + 1 < m) {a b : Fin m}
    (ha : a.val = i) (hb : b.val = i + 1) (hab : a ≠ b) :
    blk h hab = (blockEmb K 2 f m 2 i (by omega)).range.map
      (SUid (unitaryInvolution K 2 f) m).subtype := by
  obtain ⟨a, halt⟩ := a
  obtain ⟨b, hblt⟩ := b
  obtain rfl : a = i := ha
  obtain rfl : b = a + 1 := hb
  ext g
  constructor
  · intro hg
    obtain ⟨X, hX, hgX⟩ := (mem_blk_iff hab).mp hg
    refine ⟨blockEmb K 2 f m 2 a (by omega) ⟨X, (mem_gramSU_idGram_iff_mem_SUid h).mp hX⟩,
      ⟨_, rfl⟩, ?_⟩
    apply Units.ext
    rw [hgX, coordEmbed_eq_blockMat_adjacent hi]
    rfl
  · rintro ⟨y, ⟨A, rfl⟩, rfl⟩
    refine (mem_blk_iff hab).mpr
      ⟨(A : GL (Fin 2) K), (mem_gramSU_idGram_iff_mem_SUid h).mpr A.2, ?_⟩
    rw [coordEmbed_eq_blockMat_adjacent hi]
    rfl

theorem blk_zero_one_sup_blk_one_two (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 2 ^ f ≠ 2) :
    blk h (show (0 : Fin 4) ≠ 1 by decide) ⊔ blk h (show (1 : Fin 4) ≠ 2 by decide) =
      (blockEmb K 2 f 4 3 0 (by omega)).range.map (SUid (unitaryInvolution K 2 f) 4).subtype := by
  rw [blk_eq_map_blockEmb_adjacent h (m := 4) (i := 0) (by omega) (a := 0) (b := 1) rfl rfl
    (by decide), blk_eq_map_blockEmb_adjacent h (m := 4) (i := 1) (by omega) (a := 1) (b := 2)
    rfl rfl (by decide), ← Subgroup.map_sup]
  congr 1
  exact (range_blockEmb3 hK hq 3 0 (by decide)).symm

end PhanBlocks

section Perm

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def coordPerm (K : Type) [Field K] (σ : Equiv.Perm (Fin n)) :
    GL (Fin n) K ≃* GL (Fin n) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K σ).toMulEquiv

theorem coe_coordPerm (σ : Equiv.Perm (Fin n)) (g : GL (Fin n) K) :
    ((coordPerm K σ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K).submatrix σ.symm σ.symm :=
  rfl

theorem coordIncl_submatrix_perm (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (coordIncl K i j).submatrix σ.symm id = coordIncl K (σ i) (σ j) := by
  ext k a
  fin_cases a
  · by_cases hk : k = σ i <;> simp [coordIncl, Equiv.symm_apply_eq, hk]
  · by_cases hk : k = σ j <;> simp [coordIncl, Equiv.symm_apply_eq, hk]

theorem coordEmbed_submatrix_perm (σ : Equiv.Perm (Fin n)) (i j : Fin n)
    (X : Matrix (Fin 2) (Fin 2) K) :
    (coordEmbed K i j X).submatrix σ.symm σ.symm = coordEmbed K (σ i) (σ j) X := by
  have hL := coordIncl_submatrix_perm (K := K) σ i j
  have h1 : ∀ M : Matrix (Fin n) (Fin n) K,
      (1 + M).submatrix σ.symm σ.symm = 1 + M.submatrix σ.symm σ.symm := fun M => by
    rw [show (1 + M).submatrix σ.symm σ.symm =
      (1 : Matrix (Fin n) (Fin n) K).submatrix σ.symm σ.symm + M.submatrix σ.symm σ.symm from rfl,
      Matrix.submatrix_one_equiv]
  unfold coordEmbed coordProj
  rw [h1, ← hL]
  congr 1

variable {f : ℕ} (h : UnitaryFieldData 2 f K)

theorem map_blk_coordPerm (σ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    (blk h hij).map (coordPerm K σ).toMonoidHom = blk h (σ.injective.ne hij) := by
  ext g
  constructor
  · rintro ⟨g₀, hg₀, rfl⟩
    obtain ⟨X, hX, hgX⟩ := (mem_blk_iff hij).mp hg₀
    refine (mem_blk_iff _).mpr ⟨X, hX, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, coe_coordPerm, hgX, coordEmbed_submatrix_perm]
  · intro hg
    obtain ⟨X, hX, hgX⟩ := (mem_blk_iff _).mp hg
    refine ⟨(coordPerm K σ).symm g, ?_, (coordPerm K σ).apply_symm_apply g⟩
    refine (mem_blk_iff hij).mpr ⟨X, hX, ?_⟩
    have h2 := congrArg (fun g' : GL (Fin n) K => (g' : Matrix (Fin n) (Fin n) K))
      ((coordPerm K σ).apply_symm_apply g)
    simp only [coe_coordPerm] at h2
    have h3 : (coordEmbed K i j X).submatrix σ.symm σ.symm = g := by
      rw [coordEmbed_submatrix_perm, hgX]
    have h4 := h2.trans h3.symm
    ext a b
    have := congrFun (congrFun h4 (σ a)) (σ b)
    simpa using this

theorem map_blk_coordPerm_of_eq (σ : Equiv.Perm (Fin n)) {i j i' j' : Fin n} (hij : i ≠ j)
    (hi : σ i = i') (hj : σ j = j') (hij' : i' ≠ j') :
    (blk h hij).map (coordPerm K σ).toMonoidHom = blk h hij' := by
  subst hi hj
  exact map_blk_coordPerm h σ hij

end Perm

theorem exists_perm_zero_one_two : ∀ a b c : Fin 4, a ≠ b → b ≠ c → a ≠ c →
    ∃ σ : Equiv.Perm (Fin 4), σ a = 0 ∧ σ b = 1 ∧ σ c = 2 := by
  decide

theorem blk_sup_blk_mulEquiv_su3 {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (hf : 2 ≤ f) {a b c : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Nonempty (↥(blk h hab ⊔ blk h hbc) ≃* ↥(unitarySU 2 f K 3)) := by
  have := h.finite
  have := h.charP
  have hK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  have hq : 2 ^ f ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨σ, hσa, hσb, hσc⟩ := exists_perm_zero_one_two a b c hab hbc hac
  have hmap : (blk h hab ⊔ blk h hbc).map (coordPerm K σ).toMonoidHom =
      blk h (show (0 : Fin 4) ≠ 1 by decide) ⊔ blk h (show (1 : Fin 4) ≠ 2 by decide) := by
    rw [Subgroup.map_sup, map_blk_coordPerm_of_eq h σ hab hσa hσb (by decide),
      map_blk_coordPerm_of_eq h σ hbc hσb hσc (by decide)]
  let Φ : CFSG.ClassicalInvolution.Phan.Su K 2 f 3 →* GL (Fin 4) K :=
    (SUid (unitaryInvolution K 2 f) 4).subtype.comp (blockEmb K 2 f 4 3 0 (by omega))
  have hΦ : Function.Injective Φ := Subtype.val_injective.comp (blockEmb_injective _)
  have hrange : blk h (show (0 : Fin 4) ≠ 1 by decide) ⊔ blk h (show (1 : Fin 4) ≠ 2 by decide) =
      Φ.range := by
    rw [blk_zero_one_sup_blk_one_two h hK hq]
    exact (MonoidHom.range_comp _ _).symm
  exact ⟨((Subgroup.equivMapOfInjective _ (coordPerm K σ).toMonoidHom
    (coordPerm K σ).injective).trans (MulEquiv.subgroupCongr hmap)).trans
    ((MulEquiv.subgroupCongr hrange).trans ((MonoidHom.ofInjective hΦ).symm.trans
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3))))⟩

end CFSG.RankThree.PartOne.KFU

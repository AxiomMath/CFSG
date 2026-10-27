module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aShA
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4Block
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.QuasithinUnique.Setup.X6 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {Q : Type} [Group Q]

theorem parabPair_of_l34Parabs [Finite Q] [IsSimpleGroup Q] {S : Subgroup Q}
    {P : Fin 2 → Subgroup Q} (h : L34Parabs S P) : ParabPair S P := by
  have hle : ∀ i j : Fin 2, i ≠ j → ¬ P i ≤ P j := by
    intro i j hij hle
    have e := ((h.covBy i).eq_or_eq hle le_top).resolve_right (h.covBy j).lt.ne
    apply h.ne
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact e.symm
    · exact e
    · exact absurd rfl hij
  have hne : ∀ j, P j ≠ ⊥ := fun j e => by
    have hc := h.card j
    rw [e, Subgroup.card_bot] at hc
    norm_num at hc
  have hpc : CFSG.pCore 2 ↥(⊤ : Subgroup Q) = ⊥ := by
    have : IsSimpleGroup ↥(⊤ : Subgroup Q) := Subgroup.topEquiv.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥(⊤ : Subgroup Q)) with e | e
    · exact e
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 ↥(CFSG.pCore 2 ↥(⊤ : Subgroup Q)) := CFSG.pCore_isPGroup
      rw [e] at hp
      have hQ : IsPGroup 2 Q := (hp.of_equiv Subgroup.topEquiv).of_equiv Subgroup.topEquiv
      have := hQ.isNilpotent
      have hQs : Group.IsSolvable ↥(⊤ : Subgroup Q) :=
        Group.isSolvable_of_isSolvable_injective (f := (⊤ : Subgroup Q).subtype)
          (⊤ : Subgroup Q).subtype_injective
      exact hne 0 (eq_bot_of_perfect_of_le_solvable (h.perfect 0) le_top hQs)
  exact ⟨fun j => (h.covBy j).lt.ne, hle 0 1 (by decide), hle 1 0 (by decide), h.classify,
    ParabPair.top_not_of_pCore hpc, h.perfect, hne, fun j => (h.le j).trans Subgroup.le_normalizer⟩

theorem exists_parabPair_l34 [Finite Q] (hQ : IsPSL 3 2 2 Q) {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) : ∃ B : Fin 2 → Subgroup Q, ParabPair S B := by
  have := (CFSG.LieType.Simplicity.fam_PSL_simplicity Q 3 2 2 hQ).2
  obtain ⟨P, hP⟩ := exists_l34Parabs hQ hS
  exact ⟨P, parabPair_of_l34Parabs hP⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem map_spLevi_ne_bot (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    (spLevi (K := K) j).range.map (proj 2 K) ≠ ⊥ := by
  intro h
  obtain ⟨A, B, hAB⟩ := sl2_nonabelian (K := K) hK4
  have hmem : ∀ C : Matrix.SpecialLinearGroup (Fin 2) K, spLevi j C ∈ spScalars 2 K := fun C => by
    rw [← ker_proj, MonoidHom.mem_ker]
    have : proj 2 K (spLevi j C) ∈ (spLevi (K := K) j).range.map (proj 2 K) := ⟨_, ⟨C, rfl⟩, rfl⟩
    rw [h] at this
    exact this
  have hc : ∀ x y : StatedSp 2 K, x ∈ spScalars 2 K → x * y = y * x := by
    intro x y hx
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar, Subgroup.mem_center_iff] at hx
    exact Subtype.ext (hx (y : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K)).symm
  have hinj : Function.Injective (spLevi (K := K) j) := fun C D e =>
    Subtype.ext (by rw [← blkIdx_spLevi j C, ← blkIdx_spLevi j D, e])
  apply hAB
  apply hinj
  rw [map_mul, map_mul]
  exact hc _ _ (hmem A)

omit [Finite K] in
theorem dInf_projStabilizer_ne_bot (hK4 : ∃ s : Finset K, s.card = 4) {Q : Type} [Group Q]
    [Finite Q] (φ : Q ≃* StatedProj (StatedSp 2 K)) (j : Fin 2) :
    dInf ((projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map φ.symm.toMonoidHom) ≠ ⊥ := by
  intro h
  apply map_spLevi_ne_bot hK4 j
  have hR : Group.IsPerfect ↥((spLevi (K := K) j).range) :=
    Subgroup.isPerfect_iff.mpr (spLevi_range_perfect hK4 j)
  have hle : (spLevi (K := K) j).range ≤ Q2 K j := by
    rintro _ ⟨A, rfl⟩
    exact spLevi_mem j A
  have hX : ((spLevi (K := K) j).range.map (proj 2 K)).map φ.symm.toMonoidHom ≤
      dInf ((projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map φ.symm.toMonoidHom) :=
    le_dInf_of_perfect (map_isPerfect (map_isPerfect hR (proj 2 K)) φ.symm.toMonoidHom)
      (Subgroup.map_mono (f := φ.symm.toMonoidHom) (Subgroup.map_mono (f := proj 2 K) hle))
  rw [h] at hX
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.symm.injective).mp (le_bot_iff.mp hX)

theorem exists_parabPair_sp4 {Q : Type} [Group Q] [Finite Q] {f : ℕ} (hf : 2 ≤ f)
    (hQ : StatedClassicalModel Q .PSp 2 2 f) {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) : ∃ B : Fin 2 → Subgroup Q, ParabPair S B := by
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Q 2 2 f hQ
  obtain ⟨K, _, _, _, φ, hK, -, hres, -⟩ := even_rank_two_residual_symplectic hQ hS
  have hK4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four (by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
  exact ⟨_, parabPair_of_residual hS hres fun j => dInf_projStabilizer_ne_bot hK4 φ j⟩

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

module

public import CFSG.Quasithin.EmptyFaithful.S151ZR
public import CFSG.Quasithin.EmptyFaithful.S151ZC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {A : Type} [Group A]

theorem exists_surjBorel_of_surj [Finite A] {L B : Subgroup A} {n : ℕ} (hn : 1 ≤ n)
    (e₁ : ↥L →* SLt n) (he₁ : Function.Surjective e₁) (hker₁ : e₁.ker = CFSG.pCore 2 ↥L)
    (hB : IsSylowTwoOf B L) : ∃ D : SurjBorel n L B, D.e.ker = CFSG.pCore 2 ↥L := by
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hB
  let Q : Sylow 2 (SLt n) := Sylow.mapSurjective (f := e₁) he₁ P
  have hQ : (Q : Subgroup (SLt n)) = (P : Subgroup ↥L).map e₁ :=
    Sylow.coe_mapSurjective (f := e₁) he₁ P
  obtain ⟨g, hg⟩ := exists_conj_eq_unitriangular hn Q
  let e : ↥L →* SLt n := (MulAut.conj g⁻¹).toMonoidHom.comp e₁
  have hker : e.ker = CFSG.pCore 2 ↥L := by
    rw [← hker₁]
    ext x
    simp only [e, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hKP : CFSG.pCore 2 ↥L ≤ (P : Subgroup ↥L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).le_sylow_of_normal P
  refine ⟨⟨e, (MulAut.conj g⁻¹).surjective.comp he₁, hB.1, ?_, ?_⟩, hker⟩
  · show e.ker ≤ B.subgroupOf L
    rw [hker, ← hP]
    exact hKP
  · have h1 : (B.subgroupOf L).map e₁ = FLc.conjSub g (Ut n) := by
      rw [← hP, ← hQ, hg]
      rfl
    have h2 : (B.subgroupOf L).map e = FLc.conjSub g⁻¹ ((B.subgroupOf L).map e₁) := by
      rw [FLc.conjSub, Subgroup.map_map]
    show (B.subgroupOf L).map e = Ut n
    rw [h2, h1, CFSG.Quasithin.FLc.conjSub_inv_conjSub]

theorem surjBorel_normalizer_le {L B : Subgroup A} {n : ℕ} (D : SurjBorel n L B) :
    L ⊓ Subgroup.normalizer (B : Set A) ≤ B := by
  rintro x ⟨hxL, hxN⟩
  set x₀ : ↥L := ⟨x, hxL⟩ with hx₀
  have hN : D.e x₀ ∈ Subgroup.normalizer ((Ut n : Subgroup (SLt n)) : Set (SLt n)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨z, rfl⟩ := D.surj y
    have e1 : D.e x₀ * D.e z * (D.e x₀)⁻¹ = D.e (x₀ * z * x₀⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [e1, ← D.model_B, D.mem_model le_rfl, D.mem_model le_rfl]
    have := Subgroup.mem_normalizer_iff.mp hxN (z : A)
    simpa using this
  rw [normalizer_unitriangular, upperTriangular_eq_Ut] at hN
  have := (D.mem_model (le_refl B) x₀).mp (by rw [D.model_B]; exact hN)
  exact this

theorem cuts_of_max_three {L B : Subgroup A} (D : SurjBorel 3 L B) {K : Subgroup A}
    (hK : IsMaxSubgroupIn L K) (hBK : B ≤ K) : ∃ i, IsNode 3 i ∧ D.cutsOf K = {i} := by
  have hKL : K ≤ L := hK.1.le
  have hsub : ∀ x ∈ D.cutsOf K, x = 1 ∨ x = 2 := fun x hx => by
    have := D.isNode_of_mem_cutsOf hx
    unfold IsNode at this
    omega
  by_cases h1 : 1 ∈ D.cutsOf K
  · by_cases h2 : 2 ∈ D.cutsOf K
    · exfalso
      have hKB : K = B := by
        apply D.eq_of_cutsOf_eq hBK hKL le_rfl D.le_L
        rw [D.cutsOf_B]
        ext x
        constructor
        · intro hx
          exact D.isNode_of_mem_cutsOf hx
        · intro hx
          have hx' : IsNode 3 x := hx
          unfold IsNode at hx'
          have : x = 1 ∨ x = 2 := by omega
          rcases this with rfl | rfl
          · exact h1
          · exact h2
      obtain ⟨K₁, hBK₁, hK₁L, hK₁c⟩ := D.exists_cutsOf_eq (I := ({1} : Set ℕ)) (by
        intro i hi
        rw [Set.mem_singleton_iff.mp hi]
        exact ⟨le_rfl, by omega⟩)
      have hlt : K < K₁ := by
        refine lt_of_le_of_ne (hKB ▸ hBK₁) fun h => ?_
        have h3 : D.cutsOf K = D.cutsOf K₁ := by rw [h]
        rw [hK₁c] at h3
        have : 2 ∈ ({1} : Set ℕ) := h3 ▸ h2
        simp at this
      have hK₁eq : K₁ = L := hK.2 K₁ hlt hK₁L
      have : D.cutsOf K₁ = D.cutsOf L := by rw [hK₁eq]
      rw [hK₁c, D.cutsOf_L] at this
      have h4 : (1 : ℕ) ∈ (∅ : Set ℕ) := this ▸ Set.mem_singleton 1
      exact h4
    · refine ⟨1, ⟨le_rfl, by omega⟩, ?_⟩
      ext x
      constructor
      · intro hx
        rcases hsub x hx with rfl | rfl
        · rfl
        · exact absurd hx h2
      · intro hx
        rw [Set.mem_singleton_iff.mp hx]
        exact h1
  · by_cases h2 : 2 ∈ D.cutsOf K
    · refine ⟨2, ⟨by omega, by omega⟩, ?_⟩
      ext x
      constructor
      · intro hx
        rcases hsub x hx with rfl | rfl
        · exact absurd hx h1
        · rfl
      · intro hx
        rw [Set.mem_singleton_iff.mp hx]
        exact h2
    · exfalso
      have hKL' : K = L := by
        apply D.eq_of_cutsOf_eq hBK hKL D.le_L le_rfl
        rw [D.cutsOf_L]
        ext x
        constructor
        · intro hx
          rcases hsub x hx with rfl | rfl
          · exact absurd hx h1
          · exact absurd hx h2
        · intro hx
          exact absurd hx (Set.notMem_empty x)
      exact hK.1.ne hKL'

theorem input15122Rank2Lat_L3 (G : Type) [Group G] [Finite G] (L B : Subgroup G)
    (h : IsLnBlock L 3) (hB : IsSylowTwoOf B L) :
    L ⊓ Subgroup.normalizer (B : Set G) ≤ B ∧
      ∀ M' : Subgroup G, IsMaxSubgroupIn L M' → B ≤ M' → ∃ P : Subgroup G, OtherPar L B M' P := by
  obtain ⟨-, α, hα, hker, -⟩ := h
  let φ := (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm
  let e₁ : ↥L →* SLt 3 := φ.toMonoidHom.comp α
  have he₁ : Function.Surjective e₁ := φ.surjective.comp hα
  have hker₁ : e₁.ker = CFSG.pCore 2 ↥L := by
    rw [← hker]
    ext x
    simp only [e₁, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  obtain ⟨D, hD⟩ := exists_surjBorel_of_surj (by norm_num) e₁ he₁ hker₁ hB
  refine ⟨surjBorel_normalizer_le D, fun M' hM' hBM' => ?_⟩
  obtain ⟨i, hi, hMi⟩ := cuts_of_max_three D hM' hBM'
  have hex : ∃ j, IsNode 3 j ∧ j ≠ i := by
    obtain ⟨hi1, hi2⟩ := hi
    by_cases hi' : i = 1
    · exact ⟨2, ⟨by omega, by omega⟩, by omega⟩
    · exact ⟨1, ⟨le_rfl, by omega⟩, by omega⟩
  obtain ⟨j, hj, hji⟩ := hex
  obtain ⟨P, hBP, hPL, hPc⟩ := D.exists_cutsOf_eq (I := ({j} : Set ℕ)) (by
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hj)
  have hBL : B ≤ L := hB.1
  have hjP : j ∈ D.cutsOf P := by rw [hPc]; exact Set.mem_singleton j
  refine ⟨P, ?_, hBP, ?_, ?_, ?_, ?_, ?_⟩
  · exact D.isMax_of_cuts_insert hBL le_rfl hBP hPL (x := j) (by rw [D.cutsOf_L]; exact Set.notMem_empty j)
      (by rw [D.cutsOf_L, hPc]; ext x; simp)
  · intro hP
    have h1 : D.cutsOf P = D.cutsOf M' := by rw [hP]
    rw [hPc, hMi] at h1
    exact hji (Set.singleton_eq_singleton_iff.mp h1)
  · intro K hK hBK
    obtain ⟨i', hi', hKi⟩ := cuts_of_max_three D hK hBK
    have hKL : K ≤ L := hK.1.le
    have hM'L : M' ≤ L := hM'.1.le
    by_cases hii : i' = i
    · left
      exact D.eq_of_cutsOf_eq hBK hKL hBM' hM'L (by rw [hKi, hMi, hii])
    · right
      have hij : i' = j := by
        obtain ⟨hi1, hi2⟩ := hi
        obtain ⟨hj1, hj2⟩ := hj
        obtain ⟨hi'1, hi'2⟩ := hi'
        omega
      exact D.eq_of_cutsOf_eq hBK hKL hBP hPL (by rw [hKi, hPc, hij])
  ·
    have hrel : B.relIndex P = 3 := by
      have h1 := zr_relIndex_eq D hBP hPL
      have hmodel : D.model P = QI 3 (D.cutsOf P) := eq_QI_cuts (D.Ut_le_model hBP)
      have hset : D.cutsOf P = nodeSet 3 \ {i} := by
        rw [hPc]
        ext x
        simp only [Set.mem_singleton_iff, Set.mem_sdiff, mem_nodeSet]
        obtain ⟨hi1, hi2⟩ := hi
        obtain ⟨hj1, hj2⟩ := hj
        constructor
        · rintro rfl
          exact ⟨⟨hj1, hj2⟩, hji⟩
        · rintro ⟨⟨hx1, hx2⟩, hxi⟩
          omega
      rw [h1, hmodel, hset]
      exact index_single hi
    have h2 := Subgroup.relIndex_mul_card B P
    rw [inf_of_le_left hBP, hrel] at h2
    exact h2.symm
  ·
    intro hPN
    have hPB : P ≤ B := (le_inf hPL hPN).trans (surjBorel_normalizer_le D)
    have hPeq : P = B := le_antisymm hPB hBP
    have hrel : B.relIndex P = 3 := by
      have h1 := zr_relIndex_eq D hBP hPL
      have hmodel : D.model P = QI 3 (D.cutsOf P) := eq_QI_cuts (D.Ut_le_model hBP)
      have hset : D.cutsOf P = nodeSet 3 \ {i} := by
        rw [hPc]
        ext x
        simp only [Set.mem_singleton_iff, Set.mem_sdiff, mem_nodeSet]
        obtain ⟨hi1, hi2⟩ := hi
        obtain ⟨hj1, hj2⟩ := hj
        constructor
        · rintro rfl
          exact ⟨⟨hj1, hj2⟩, hji⟩
        · rintro ⟨⟨hx1, hx2⟩, hxi⟩
          omega
      rw [h1, hmodel, hset]
      exact index_single hi
    rw [hPeq, Subgroup.relIndex_self] at hrel
    omega
  · exact parBig_of_cut D hD hBP hPL hjP

end CFSG.Quasithin

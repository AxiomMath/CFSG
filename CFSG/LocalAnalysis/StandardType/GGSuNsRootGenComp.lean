module

public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenBlock
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeElt
public import CFSG.LieType.SeitzGeneration.UnitaryBlocksNe

public section

namespace CFSG.StandardType

namespace SuNsRootGen

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.LieType.SeitzGeneration

variable {K : Type} [Field K] {n d p : ℕ}

theorem swapU_mem_blockSU (h : UnitaryFieldData 2 n K) (i j : Fin d) :
    SURep.swapU h i j ∈ TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d)) := by
  rw [TableBUE.mem_blockSU, coe_swapU_eq_permGL]
  exact TableBUE.isBlockOn_permGL_swap (S := ({i, j} : Finset (Fin d))) (by simp) (by simp)

private theorem eq_pair_of_eq_pair {a b i₀ j₀ : Fin d} (hab : a ≠ b)
    (h : ({a, b} : Finset (Fin d)) = {i₀, j₀}) :
    (a = i₀ ∧ b = j₀) ∨ (a = j₀ ∧ b = i₀) := by
  have ha : a = i₀ ∨ a = j₀ := by
    have h' : a ∈ ({i₀, j₀} : Finset (Fin d)) := h ▸ Finset.mem_insert_self a {b}
    simpa using h'
  have hb : b = i₀ ∨ b = j₀ := by
    have h' : b ∈ ({i₀, j₀} : Finset (Fin d)) :=
      h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    simpa using h'
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hab

private theorem mem_blockSU_pair_of_isCoordBlockOn {a b : Fin d}
    {g : ↥(unitarySU 2 n K d)}
    (h : IsCoordBlockOn a b ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    g ∈ TableBUE.blockSU (K := K) (n := n) ({a, b} : Finset (Fin d)) := by
  rw [TableBUE.mem_blockSU]
  intro i j hij
  have hij' : (i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b) := by
    rcases hij with hi | hj
    · refine Or.inl ⟨?_, ?_⟩
      · intro hia
        exact hi (by rw [hia]; simp)
      · intro hib
        exact hi (by rw [hib]; simp)
    · refine Or.inr ⟨?_, ?_⟩
      · intro hja
        exact hj (by rw [hja]; simp)
      · intro hjb
        exact hj (by rw [hjb]; simp)
  rw [h i j hij', Matrix.one_apply]

theorem iSup_blockSU_pairs (h : UnitaryFieldData 2 n K) (hq : 4 ≤ 2 ^ n) (hd : 3 ≤ d)
    (i₀ j₀ : Fin d) :
    (⨆ (i : Fin d) (j : Fin d) (_ : i ≠ j ∧ ({i, j} : Finset (Fin d)) ≠ {i₀, j₀}),
      TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))) = ⊤ := by
  classical
  let S : Subgroup ↥(unitarySU 2 n K d) :=
    ⨆ (i : Fin d) (j : Fin d) (_ : i ≠ j ∧ ({i, j} : Finset (Fin d)) ≠ {i₀, j₀}),
      TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))
  let M : Subgroup (GL (Fin d) K) := S.map (unitarySU 2 n K d).subtype
  change S = ⊤
  have hSUle : unitarySU 2 n K d ≤ M := by
    refine unitarySU_le_of_blocks_ne (ℓ := 2) (f := n) (n := d) h hq hd i₀ j₀ M ?_
    intro a b hab hne1 hne2 g hg hblk
    have hpair : ({a, b} : Finset (Fin d)) ≠ {i₀, j₀} := by
      intro he
      rcases eq_pair_of_eq_pair hab he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne1 ⟨rfl, rfl⟩
      · exact hne2 ⟨rfl, rfl⟩
    let g' : ↥(unitarySU 2 n K d) := ⟨g, hg⟩
    exact Subgroup.mem_map.mpr ⟨g', Subgroup.mem_iSup_of_mem a
      (Subgroup.mem_iSup_of_mem b (Subgroup.mem_iSup_of_mem ⟨hab, hpair⟩
        (mem_blockSU_pair_of_isCoordBlockOn (g := g') hblk))), rfl⟩
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hSUle x.2)
  have hzx' : z = x := Subtype.ext hzx
  rwa [← hzx']

private theorem exists_notMem_triple (hd : 4 ≤ d) (a b c : Fin d) :
    ∃ m : Fin d, m ≠ a ∧ m ≠ b ∧ m ≠ c := by
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c} : Finset (Fin d))) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      have h3 : ({a, b, c} : Finset (Fin d)).card ≤ 3 := Finset.card_le_three
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  exact ⟨m, hm.1, hm.2.1, hm.2.2⟩

private theorem mem_blockSU_of_diagHom {S : Finset (Fin d)} {t : Fin d → Kˣ}
    (ht : ∀ k, k ∉ S → t k = 1) (hmem : diagHom d t ∈ unitarySU 2 n K d) :
    (⟨diagHom d t, hmem⟩ : ↥(unitarySU 2 n K d)) ∈
      TableBUE.blockSU (K := K) (n := n) S := by
  rw [TableBUE.mem_blockSU]
  intro a b hab
  change ((diagHom d t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) a b =
    (1 : Matrix (Fin d) (Fin d) K) a b
  rw [coe_diagHom]
  by_cases h : a = b
  · have ha : a ∉ S := by
      rcases hab with ha | hb
      · exact ha
      · rwa [← h] at hb
    subst h
    rw [Matrix.diagonal_apply_eq, ht a ha, Units.val_one, Matrix.one_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

private theorem conj_mem_blockSU_pair (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d) {i j : Fin d}
    {c x : ↥(unitarySU 2 n K d)}
    (hc : c ∈ pairCentU (n := n) (p := p) (K := K) i j)
    (hx : x ∈ TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))) :
    c * x * c⁻¹ ∈ TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d)) := by
  classical
  change c ∈ Subgroup.centralizer {D : ↥(unitarySU 2 n K d) | ∃ σ : Fin d → Kˣ,
    (D : GL (Fin d) K) = diagHom d σ ∧ σ i = σ j ∧ ∀ k, σ k ^ p = 1} at hc
  obtain ⟨u, huo, -⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one (ℓ := 2) (f := n) h hp hpq
  have hup : u ^ p = 1 := huo ▸ pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at huo
    exact hp.ne_one huo.symm
  have huinv : u ≠ u⁻¹ := by
    intro he
    have h2 : u ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [he]
      exact mul_inv_cancel u
    have hdvd : p ∣ 2 := by
      have := orderOf_dvd_of_pow_eq_one h2
      rwa [huo] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  let T : Set (Fin d → Kˣ) := {σ | diagHom d σ ∈ unitarySU 2 n K d ∧ σ i = σ j ∧
    ∀ k, σ k ^ p = 1}
  have hconst : ∀ σ ∈ T, ∀ a ∈ ({i, j} : Finset (Fin d)),
      ∀ b ∈ ({i, j} : Finset (Fin d)), σ a = σ b := by
    intro σ hσ a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hσ.2.1
    · exact hσ.2.1.symm
    · rfl
  have hsep : ∀ k ∉ ({i, j} : Finset (Fin d)), ∀ l, l ≠ k →
      ∃ σ ∈ T, σ k ≠ σ l := by
    intro k hk l hkl
    have hki' : k ≠ i := fun h' => hk (by rw [h']; simp)
    have hkj' : k ≠ j := fun h' => hk (by rw [h']; simp)
    have key : ∀ m : Fin d, m ≠ i → m ≠ j → m ≠ k →
        ∃ σ : Fin d → Kˣ, diagHom d σ ∈ unitarySU 2 n K d ∧ σ i = σ j ∧
          (∀ x, σ x ^ p = 1) ∧ σ k = u ∧ σ m = u⁻¹ ∧
          (∀ x, x ≠ k → x ≠ m → σ x = 1) := by
      intro m hmi hmj hmk
      let σ : Fin d → Kˣ := Pi.mulSingle k u * Pi.mulSingle m u⁻¹
      have hkm : k ≠ m := hmk.symm
      have hσk : σ k = u := by simp [σ, hkm]
      have hσm : σ m = u⁻¹ := by simp [σ, hkm.symm]
      have hσi : σ i = 1 := by simp [σ, hki'.symm, hmi.symm]
      have hσj : σ j = 1 := by simp [σ, hkj'.symm, hmj.symm]
      have hσother : ∀ x, x ≠ k → x ≠ m → σ x = 1 := by
        intro x hxk hxm
        simp [σ, hxk, hxm]
      have hσpow : ∀ x, σ x ^ p = 1 := by
        intro x
        by_cases hxk : x = k
        · rw [hxk, hσk, hup]
        · by_cases hxm : x = m
          · rw [hxm, hσm, inv_pow, hup, inv_one]
          · rw [hσother x hxk hxm, one_pow]
      have hprod : ∏ x, σ x = 1 := by
        simp only [σ, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
        exact mul_inv_cancel u
      have hnorm : ∀ x, σ x ^ (2 ^ n + 1) = 1 := by
        intro x
        obtain ⟨c, hc⟩ := hpq
        rw [hc, pow_mul, hσpow x, one_pow]
      have hdmem : diagHom d σ ∈ unitarySU 2 n K d :=
        TableBUE.diagHom_mem_unitarySU h hnorm hprod
      exact ⟨σ, hdmem, by rw [hσi, hσj], hσpow, hσk, hσm, hσother⟩
    by_cases hl : l ∈ ({i, j} : Finset (Fin d))
    · obtain ⟨m, hmi, hmj, hmk⟩ := exists_notMem_triple hd i j k
      obtain ⟨σ, hdmem, hσij, hσpow, hσk, -, hσother⟩ := key m hmi hmj hmk
      have hlm : l ≠ m := by
        intro h'
        have hmS : m ∈ ({i, j} : Finset (Fin d)) := h' ▸ hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmS
        rcases hmS with h | h
        · exact hmi h
        · exact hmj h
      refine ⟨σ, ⟨hdmem, hσij, hσpow⟩, ?_⟩
      rw [hσk, hσother l hkl hlm]
      exact hu1
    · have hli : l ≠ i := fun h' => hl (by rw [h']; simp)
      have hlj : l ≠ j := fun h' => hl (by rw [h']; simp)
      obtain ⟨σ, hdmem, hσij, hσpow, hσk, hσl, -⟩ := key l hli hlj hkl
      refine ⟨σ, ⟨hdmem, hσij, hσpow⟩, ?_⟩
      rw [hσk, hσl]
      exact huinv
  have hg : ∀ σ ∈ T, (c : GL (Fin d) K) * diagHom d σ = diagHom d σ * c := by
    intro σ hσ
    have hDmem : (⟨diagHom d σ, hσ.1⟩ : ↥(unitarySU 2 n K d)) ∈
        {D : ↥(unitarySU 2 n K d) | ∃ τ : Fin d → Kˣ,
          (D : GL (Fin d) K) = diagHom d τ ∧ τ i = τ j ∧ ∀ k, τ k ^ p = 1} :=
      ⟨σ, rfl, hσ.2.1, hσ.2.2⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hDmem
    exact (congrArg Subtype.val hcomm).symm
  exact conj_mem_blockSU_of_family (K := K) (n := n) hsep hconst hg hx

theorem isComponentOf_blockSU_pair (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d) {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'}
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker)
    {i j : Fin d} (hij : i ≠ j) :
    IsComponentOf
      ((TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ)
      ((pairCentU (n := n) (p := p) (K := K) i j).map φ) := by
  classical
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one (by omega) hpq
  have hJC : TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d)) ≤
      pairCentU (n := n) (p := p) (K := K) i j := by
    intro x hx
    change x ∈ Subgroup.centralizer {D : ↥(unitarySU 2 n K d) | ∃ σ : Fin d → Kˣ,
      (D : GL (Fin d) K) = diagHom d σ ∧ σ i = σ j ∧ ∀ k, σ k ^ p = 1}
    rw [Subgroup.mem_centralizer_iff]
    intro D hD
    obtain ⟨σ, hDσ, hσij, -⟩ := hD
    have hσconst : ∀ a ∈ ({i, j} : Finset (Fin d)),
        ∀ b ∈ ({i, j} : Finset (Fin d)), σ a = σ b := by
      intro a ha b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hσij
      · exact hσij.symm
      · rfl
    have hcomm := TableBUE.diagHom_mul_comm_of_isBlockOn hσconst
      (TableBUE.mem_blockSU.mp hx)
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hDσ]
      exact hcomm)
  have hJF : (TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ ≤
      (pairCentU (n := n) (p := p) (K := K) i j).map φ :=
    Subgroup.map_mono hJC
  have hJn : ∀ c ∈ pairCentU (n := n) (p := p) (K := K) i j,
      ∀ x ∈ TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d)),
      c * x * c⁻¹ ∈ TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d)) :=
    fun c hc x hx => conj_mem_blockSU_pair h hp hp2 hpq hd hc hx
  have hJn' : (((TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map
      φ).subgroupOf ((pairCentU (n := n) (p := p) (K := K) i j).map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJF]
    rintro _ f ⟨y, hy, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨c * y * c⁻¹, hJn c hc y hy, by rw [map_mul, map_mul, map_inv]⟩
  have hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) :=
    fun g hg => TableBUE.ker_projMk_le_center (K := K) (n := n) (d := d) (hφker g hg)
  have hq : CFSG.Assembly.IsQuasisimple
      ↥((TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ) :=
    SURepair.isQuasisimple_map_blockSU_of_two_le (f := n) (n := d) h hn hker
      (S := ({i, j} : Finset (Fin d))) (by rw [Finset.card_pair hij])
  exact ⟨hJF, IsSubnormal.step hJF hJn' (IsSubnormal.refl _), hq⟩

private theorem eq_one_of_mem_blockSU_of_mem_ker {S : Finset (Fin d)}
    {x : ↥(unitarySU 2 n K d)} (hm : ∃ m : Fin d, m ∉ S)
    (hx : x ∈ TableBUE.blockSU (K := K) (n := n) S)
    (hker : x ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker) : x = 1 := by
  obtain ⟨m, hm⟩ := hm
  have hz' : x ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker := hker
  rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, largeEvenScalars_def,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
  obtain ⟨u, hu⟩ := hz'
  have h2 := congrFun (congrFun (congrArg (fun g : GL (Fin d) K =>
    (g : Matrix (Fin d) (Fin d) K)) hu) m) m
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h2
  have h3 := (TableBUE.mem_blockSU.mp hx) m m (Or.inl hm)
  have hu1 : (u : K) = 1 := by
    rw [h2]
    simpa using h3
  apply Subtype.ext
  apply Units.ext
  rw [← hu]
  have : u = 1 := Units.ext hu1
  rw [this]
  simp

theorem dvd_card_blockSU_pair (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 3 ≤ d)
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker)
    {i j : Fin d} (hij : i ≠ j) :
    p ∣ Nat.card
      ((TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ) := by
  classical
  obtain ⟨u, huo, -⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one (ℓ := 2) (f := n) h hp hpq
  have hup : u ^ p = 1 := huo ▸ pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at huo
    exact hp.ne_one huo.symm
  let σ : Fin d → Kˣ := Pi.mulSingle i u * Pi.mulSingle j u⁻¹
  have hσi : σ i = u := by simp [σ, hij]
  have hσj : σ j = u⁻¹ := by simp [σ, hij.symm]
  have hσother : ∀ k, k ≠ i → k ≠ j → σ k = 1 := by
    intro k hki hkj
    simp [σ, hki, hkj]
  have hσpow : ∀ k, σ k ^ p = 1 := by
    intro k
    by_cases hki : k = i
    · rw [hki, hσi, hup]
    · by_cases hkj : k = j
      · rw [hkj, hσj, inv_pow, hup, inv_one]
      · rw [hσother k hki hkj, one_pow]
  have hprod : ∏ k, σ k = 1 := by
    simp only [σ, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
    exact mul_inv_cancel u
  have hnorm : ∀ k, σ k ^ (2 ^ n + 1) = 1 := by
    intro k
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, hσpow k, one_pow]
  have hdmem : diagHom d σ ∈ unitarySU 2 n K d :=
    TableBUE.diagHom_mem_unitarySU h hnorm hprod
  let D₁ : ↥(unitarySU 2 n K d) := ⟨diagHom d σ, hdmem⟩
  have hD1_coe : (D₁ : GL (Fin d) K) = diagHom d σ := rfl
  have hD1_mem : D₁ ∈ TableBUE.blockSU (K := K) (n := n)
      ({i, j} : Finset (Fin d)) := by
    refine mem_blockSU_of_diagHom (K := K) (n := n) (S := ({i, j} : Finset (Fin d))) ?_ hdmem
    intro k hk
    exact hσother k (fun h' => hk (by rw [h']; simp)) (fun h' => hk (by rw [h']; simp))
  have hD1_pow : D₁ ^ p = 1 := by
    apply Subtype.ext
    change (diagHom d σ : GL (Fin d) K) ^ p = 1
    rw [← map_pow, show σ ^ p = 1 from funext hσpow, map_one]
  have hD1_ne_one : D₁ ≠ 1 := by
    intro h1
    have h2 : (((D₁ : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) i i = 1 := by
      rw [congrArg Subtype.val h1]
      simp
    rw [hD1_coe, coe_diagHom, Matrix.diagonal_apply_eq] at h2
    have h3 : σ i = 1 := Units.ext h2
    exact hu1 (hσi.symm.trans h3)
  have hφD1_ne : φ D₁ ≠ 1 := by
    intro h1
    obtain ⟨m, hmi, hmj⟩ := SURep.exists_ne_ne hd i j
    exact hD1_ne_one (eq_one_of_mem_blockSU_of_mem_ker ⟨m, by simp [hmi, hmj]⟩ hD1_mem
      (hφker D₁ h1))
  have hφD1_pow : (φ D₁) ^ p = 1 := by
    rw [← map_pow, hD1_pow, map_one]
  haveI : Fact p.Prime := ⟨hp⟩
  have horder : orderOf (φ D₁) = p := orderOf_eq_prime hφD1_pow hφD1_ne
  have hmem : φ D₁ ∈
      (TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ :=
    ⟨D₁, hD1_mem, rfl⟩
  have hdvd := ((TableBUE.blockSU (K := K) (n := n)
    ({i, j} : Finset (Fin d))).map φ).orderOf_dvd_natCard hmem
  rwa [horder] at hdvd

end SuNsRootGen

end CFSG.StandardType

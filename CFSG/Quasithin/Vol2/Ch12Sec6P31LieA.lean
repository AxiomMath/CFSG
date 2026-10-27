module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

private theorem psl34a_mem_zpowers_three_exists {G : Type*} [Group G] {g x : G} (hg : g ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers g) : ∃ i : ℕ, i < 3 ∧ g ^ i = x := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨(m % 3).toNat, by omega, ?_⟩
  rw [zpow_eq_zpow_emod' m hg, ← zpow_natCast]
  congr 1
  omega

private theorem psl34a_zpowers_inf_eq_bot {G : Type*} [Group G]
    (E : CFSG.RankThree.Asc83Table.E9Basis G) :
    Subgroup.zpowers E.a ⊓ Subgroup.zpowers E.b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨i, hi, rfl⟩ := psl34a_mem_zpowers_three_exists E.ha hxa
  obtain ⟨j, hj, hij⟩ := psl34a_mem_zpowers_three_exists E.hb hxb
  have h1 : CFSG.RankThree.Asc83Table.basisProd E.vec ![(i : ZMod 3), 0] =
      CFSG.RankThree.Asc83Table.basisProd E.vec ![0, (j : ZMod 3)] := by
    rw [E.basisProd_vec, E.basisProd_vec]
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hij.symm
  have h2 := congrFun (E.basisProd_injective h1) 0
  simp only [Matrix.cons_val_zero] at h2
  have hi0 : i = 0 := by
    interval_cases i
    · rfl
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
  subst hi0
  simp

private theorem psl34a_transfer {K G : Type} [Group K] [Group G] (e : K ≃* G)
    (E : CFSG.RankThree.Asc83Table.E9Basis G) (ha1 : E.a ≠ 1) (hb1 : E.b ≠ 1) :
    ∃ A B : Subgroup K, Nat.card A = 3 ∧ Nat.card B = 3 ∧
      A ≤ Subgroup.centralizer (B : Set K) ∧ A ⊓ B = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  refine ⟨(Subgroup.zpowers E.a).map e.symm.toMonoidHom,
    (Subgroup.zpowers E.b).map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, Nat.card_zpowers, orderOf_eq_prime E.ha ha1]
  · rw [Subgroup.card_map_of_injective hinj, Nat.card_zpowers, orderOf_eq_prime E.hb hb1]
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    rw [← map_mul, ← map_mul, (E.hab.zpow_zpow m n).symm.eq]
  · rw [← Subgroup.map_inf_eq _ _ _ hinj, psl34a_zpowers_inf_eq_bot E, Subgroup.map_bot]

theorem psl34_three_rank {K : Type} [Group K] [Finite K] (hK : IsPSL 3 2 2 K) :
    ∃ A B : Subgroup K, Nat.card A = 3 ∧ Nat.card B = 3 ∧
      A ≤ Subgroup.centralizer (B : Set K) ∧ A ⊓ B = ⊥ := by
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hK
  have hk4 : Nat.card k = 4 := by rw [hk]; norm_num
  let ε : K ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 k :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 k).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k)
  obtain ⟨u, hu⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_units_ne_one hk4
  have ha1 := CFSG.RankThree.PartTwo.KFacts.L34.aP_ne_one hk4 hu
  have hb1 : (CFSG.RankThree.PartTwo.KFacts.L34.bP :
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 k) ≠ 1 := by
    intro h
    apply ha1
    have h2 := CFSG.RankThree.PartTwo.KFacts.L34.fP_conj_aP hk4 hu
    rw [h] at h2
    simpa using h2
  exact psl34a_transfer ε (CFSG.RankThree.PartTwo.KFacts.L34.eZeroBasis hk4 hu) ha1 hb1

private theorem sl34a_E9_basis {F : Type} [Field F] (hF : Nat.card F = 4) :
    ∃ E : CFSG.RankThree.Asc83Table.E9Basis (Matrix.SpecialLinearGroup (Fin 3) F),
      E.a ≠ 1 ∧ E.b ≠ 1 := by
  obtain ⟨w, hw0, hw1⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.exists_ne_zero_ne_one hF
  have hw3 : w * w * w = 1 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.omega_cube hF hw0
  have hw3' : w ^ 3 = 1 := by rw [pow_three']; exact hw3
  let x : Matrix.SpecialLinearGroup (Fin 3) F :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.hMat w hw3
  let y : Matrix.SpecialLinearGroup (Fin 3) F :=
    ⟨Matrix.scalar (Fin 3) w, by simp [Matrix.scalar_apply, Matrix.det_diagonal, hw3']⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [x, CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.hMat,
        CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.hM, pow_three, Matrix.mul_apply,
        Fin.sum_univ_three]
    all_goals first
      | linear_combination hw3
      | linear_combination (w * w * w + 1) * hw3
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    show (Matrix.scalar (Fin 3) w) ^ 3 = 1
    rw [← map_pow, hw3', map_one]
  have hxy : Commute x y := by
    show x * y = y * x
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact (Matrix.scalar_commute (n := Fin 3) w (fun _ => Commute.all _ _) _).symm.eq
  have hx1 : x ≠ 1 := by
    intro h
    have h00 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
    simp [x, CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.hMat,
      CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.hM] at h00
    exact hw1 h00
  have hy1 : y ≠ 1 := by
    intro h
    have h11 := congrFun (congrFun (congrArg Subtype.val h) 1) 1
    simp [y] at h11
    exact hw1 h11
  have hyx : y ≠ x := by
    intro h
    have h11 := congrFun (congrFun (congrArg Subtype.val h) 1) 1
    simp [x, y, CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.hMat,
      CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.hM] at h11
    exact hw1 h11
  have hyx2 : y ≠ x ^ 2 := by
    intro h
    have h11 := congrFun (congrFun (congrArg Subtype.val h) 1) 1
    have hsq : ((x ^ 2 : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (x : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) := by
      rw [sq]
      rfl
    rw [hsq] at h11
    simp [x, y, CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.hMat,
      CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.hM, Matrix.mul_apply,
      Fin.sum_univ_three] at h11
    exact hw1 h11
  exact ⟨CFSG.RankThree.Asc83Table.E9Basis.ofNe hx3 hy3 hxy hx1 hy1 hyx hyx2, hx1, hy1⟩

theorem sl34_three_rank {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : K ≃* ↥(StatedSL 3 F)) :
    ∃ A B : Subgroup K, Nat.card A = 3 ∧ Nat.card B = 3 ∧
      A ≤ Subgroup.centralizer (B : Set K) ∧ A ⊓ B = ⊥ := by
  obtain ⟨E, ha1, hb1⟩ := sl34a_E9_basis hF
  exact psl34a_transfer
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm) E ha1 hb1

end CFSG.Quasithin.H13.S126P31

module

public import CFSG.Quasithin.Vol2.Ch11SecE3LieL2Up
public import CFSG.Quasithin.Vol2.Ch11SecE3Sz
public import CFSG.Quasithin.Vol2.Ch11SecE3LieSzGen
public import CFSG.Quasithin.EmptyFaithful.E111RMemC

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin.Vol2.Ch11
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem autRank_bound_of_inn [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ}
    (h : ∀ B : Subgroup (MulAut X), IsPGroup 2 ↥B →
      SecE3.AlmostSimple (CFSG.generalizedFitting ↥((MulAut.conj : X →* MulAut X).range ⊔ B)) →
      ∀ A : Subgroup ↥((MulAut.conj : X →* MulAut X).range ⊔ B), IsElemAbelian 2 A →
        Nat.card ↥A ≤ 2 ^ n) :
    ∀ B : Subgroup (MulAut X), IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ n := by
  intro B hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := (MulAut.conj : X →* MulAut X).range ⊔ B
  have hB2 : IsPGroup 2 ↥B := fun b => ⟨1, Subtype.ext (by simpa using hB.2 b b.2)⟩
  have hT2 : IsPGroup 2 ↥(B.subgroupOf Z) :=
    hB2.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  set e := SecB.generalizedFittingEquiv hnab B
  have hs : IsSimpleGroup ↥(CFSG.generalizedFitting ↥Z) := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnab
  have hnab' : ∃ a b : ↥(CFSG.generalizedFitting ↥Z), a * b ≠ b * a :=
    ⟨e.symm a, e.symm b, fun he => hab (by simpa using congrArg e he)⟩
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab' hT2
    (SecB.generalizedFitting_sup_sup ⟨a, b, hab⟩ B)
  have hA : IsElemAbelian 2 (B.subgroupOf Z) :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (by
      have := congrArg Subtype.val (hB.1.is_comm.comm ⟨_, x.2⟩ ⟨_, y.2⟩)
      simpa using this))⟩⟩, fun x hx => Subtype.ext (by
        simpa using hB.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
  have h1 := h B hB2 hAS (B.subgroupOf Z) hA
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at h1

theorem exists_involution_sl2 {K : Type} [Field K] [CharP K 2] :
    ∃ x : SL(2, K), x ≠ 1 ∧ x ^ 2 = 1 := by
  let M : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1]
  have hM : M.det = 1 := by simp [M, Matrix.det_fin_two]
  have hMM : M * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  let x : SL(2, K) := ⟨M, hM⟩
  have hx : (x : Matrix (Fin 2) (Fin 2) K) = M := rfl
  refine ⟨x, fun h => ?_, ?_⟩
  · have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp [x, M] at this
  · ext1
    rw [Matrix.SpecialLinearGroup.coe_pow, hx, pow_two, hMM, Matrix.SpecialLinearGroup.coe_one]

theorem autRankLe_of_isPSL22 [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ}
    (h : IsPSL 2 2 n X) : AutRankLe n X := by
  obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ := SecE3.exists_sl2_of_isPSL22 h
  obtain ⟨x, hx1, hx2⟩ := exists_involution_sl2 (K := K)
  refine ⟨⟨e.symm x, fun h => hx1 (by simpa using congrArg e h), by
    rw [← map_pow, hx2, map_one]⟩, autRank_bound_of_inn hnab fun B _ hAS A hA => ?_⟩
  exact SecE3.card_le_of_isElemAbelian_sl2 hAS ((SecB.generalizedFittingEquiv hnab B).trans e)
    hK hA

theorem card_le_of_isSz_socle {Z : Type} [Group Z] [Finite Z] {L : Subgroup Z}
    (hAS : SecE3.AlmostSimple L) {n : ℕ} (hSz : IsSz n ↥L) {A : Subgroup Z}
    (hA : IsElemAbelian 2 A) : Nat.card ↥A ≤ 2 ^ n := by
  have hOut := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 n
    hSz).1.2.2
  obtain ⟨-, a, -, K, _, _, hn, hK, ⟨e⟩⟩ := hSz
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hn ▸ hK
  have := hAS.normal
  have hAL : A ≤ L := fun x hx => by
    have hx2 : x ^ 2 = 1 := hA.2 x hx
    exact SecE3.mem_of_pow_two_pow_eq_one hAS.centralizer_eq hOut (k := 1) (by simpa using hx2)
  have hA' := SecE3.isElemAbelian_map e.toMonoidHom (SecE3.isElemAbelian_subgroupOf hA L)
  have h1 : Nat.card ↥((A.subgroupOf L).map e.toMonoidHom) = Nat.card A := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  rw [← h1, ← hK]
  exact SecE3.card_le_of_isElemAbelian_suzuki hK' hA'

theorem autRankLe_of_isSz [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ}
    (h : IsSz n X) : AutRankLe n X := by
  have h' := h
  obtain ⟨-, a, -, K, _, _, hn, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hn ▸ hK
  obtain ⟨y, hy1, hy2⟩ : ∃ y : CFSG.Blueprint.suzukiGroup a K, y ≠ 1 ∧ y ^ 2 = 1 := by
    refine ⟨CFSG.LieType.Ree.suzukiSElt a K 0 1, fun h1 => ?_, ?_⟩
    · rw [← CFSG.LieType.Ree.suzukiSElt_zero_zero hK', CFSG.LieType.Ree.suzukiSElt_inj] at h1
      exact one_ne_zero h1.2
    · exact (SecE3.isElemAbelian_suzukiZ0 (a := a) hK').2 _
        ((CFSG.LieType.Ree.mem_suzukiZ0_iff hK').2 ⟨1, rfl⟩)
  refine ⟨⟨e.symm y, fun h1 => hy1 (by simpa using congrArg e h1), by
    rw [← map_pow, hy2, map_one]⟩, autRank_bound_of_inn hnab fun B _ hAS A hA => ?_⟩
  exact card_le_of_isSz_socle hAS
    (CFSG.SectionRank.suzukiModel_of_mulEquiv (SecB.generalizedFittingEquiv hnab B) h') hA

end CFSG.Quasithin.E2.E22N

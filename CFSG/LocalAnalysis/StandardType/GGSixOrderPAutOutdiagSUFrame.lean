module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagSUTwisted
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestSURank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.RankThree.Classical2 (expHom expHom_apply expHom_injective
  diagHom_expHom_mem_unitarySU exists_orderOf_eq_norm_one)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

theorem OrdPOutSU.div_add_one_lt_sub_two {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n)
    (hn4 : 4 ≤ n) : n / p + 1 < n - 2 := by
  obtain ⟨m, rfl⟩ := hpn
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rw [Nat.mul_div_cancel_left m hp.pos]
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      omega
    · exact h
  rcases Nat.lt_or_ge p 5 with h5 | hp5
  · have hp3' : p = 3 := by
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    subst hp3'
    have : 2 ≤ m := by omega
    omega
  · have : 5 * m ≤ p * m := Nat.mul_le_mul_right m hp5
    omega

namespace UnitModel

variable {G : Type} [Group G] {n f : ℕ}

theorem exists_frame_of_su_gen [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn4 : 4 ≤ n)
    (hbig' : n / p + 1 < n - 2) (hpq : p ∣ 2 ^ (f + 1) + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n →* G}
    (hker : ψ.ker ≤
      Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBsM : Bs ≤ Subgroup.normalizer (ψ.range : Set G)) (hBsE : IsElemAbelian p Bs)
    (hBsI : ∀ b ∈ Bs, GGPsiInnerDiag (Unitary.rootDatum
      (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) n) ψ b)
    (hU : GGBstarUniqueIn p (Subgroup.normalizer (ψ.range : Set G)) Bs) :
    ∃ (P : GL (Fin n) (GaloisField 2 (2 * (f + 1))))
      (hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
        (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n),
      (∀ b ∈ Bs, SURep.GGFrameDiagU (SURep.ggFrameU
        (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) b) := by
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have : NeZero n := ⟨by omega⟩
  have hnq : (n, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : n = 3 := congrArg Prod.fst h'
    omega
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set ψ₁ := SURep.ggFrameU hF ψ P₀ hP₀ with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SURep.range_ggFrameU hF ψ P₀ hP₀
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hEB : ∀ b ∈ Bs, ∃ B', B' ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) ∧
      (b, B') ∈ SUTorus.suPairs ψ₁ := by
    intro b hb
    obtain ⟨A, hA, hAc⟩ := InnerDiagSU.suInnerDiagConj hF hn4 G ψ hker b⁻¹
      (hBsI b⁻¹ (Bs.inv_mem hb))
    refine ⟨P₀ * A * P₀⁻¹,
      SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP₀ hA),
      SUTorus.mem_suPairs_transfer P₀ hP₀ (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n)
        hA fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  have hEA : ∀ b ∈ Bs, ∃ A, (b, A) ∈ SUTorus.suPairs ψ₁ := fun b hb => by
    obtain ⟨B', -, hB'⟩ := hEB b hb
    exact ⟨B', hB'⟩
  have hEC : Bs ⊓ Subgroup.centralizer (ψ₁.range : Set G) = ⊥ := by
    rw [hr₁, hC, inf_bot_eq]
  obtain ⟨E, hEr, hEel, hEcard⟩ := exists_elemAbelian_diagU h hp hpq (by omega)
    (SURep.ggFrameKer_of_ker_le_center hF (by omega) hnq hker₁)
  have hEM : E ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [← hr₁]
    exact hEr.trans (Subgroup.le_normalizer)
  have hlow : p ^ (n - 2) ≤ Nat.card Bs := by
    rw [← hEcard]
    exact LinModel.card_le_of_bstarUniqueIn hp hBsE hBsM hU hEel hEM
  have hbig : p ^ (n / p + 1) < Nat.card Bs :=
    lt_of_lt_of_le (Nat.pow_lt_pow_right hp.one_lt hbig') hlow
  have hT := SUTorus.isToral_inducedMatrices h (by omega) hnq hp hp2 hpq hker₁ hBsE hbig hEA hEC
  obtain ⟨Q, hQ, hQd⟩ := SUTorus.exists_unitary_frame h hp hp2 hpq
    (SUTorus.isProjElem_inducedMatrices h (by omega) hnq hp hpq hker₁ hBsE) hT
  have hQi : Q⁻¹ ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) :=
    (primeFormUnitary h _).inv_mem hQ
  have hQQ : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
      (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
      (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = 1 := by
    have h1 := mem_primeFormUnitary.mp hQi
    rw [idGram, Units.val_one, Matrix.mul_one] at h1
    rw [SURep.conjTr_eq_bar h]
    exact h1
  have hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
      (((Q⁻¹ * P₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
      (((Q⁻¹ * P₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n := by
    rw [Units.val_mul, CFSG.LieType.Universal.Unitary.conjTr_mul]
    calc conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
          (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
            (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
              Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          ((((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
            Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
            (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1))))) =
        conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
          (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
            (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
              Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
            Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1))))) *
            (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) := by
          simp only [Matrix.mul_assoc]
      _ = antidiag n := by rw [hQQ, Matrix.mul_one, hP₀]
  have hdiag : ∀ b ∈ Bs, SURep.GGFrameDiagU (SURep.ggFrameU hF ψ (Q⁻¹ * P₀) hP) b := by
    intro b hb
    obtain ⟨B', hB'U, hB'⟩ := hEB b hb
    obtain ⟨d, hd⟩ := hQd B' (SUTorus.mem_inducedMatrices.mpr ⟨b, hb, hB'⟩) hB'U
    have hdU : diagHom n d ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) := by
      rw [← hd]
      exact (primeFormUnitary h _).mul_mem ((primeFormUnitary h _).mul_mem hQi hB'U) hQ
    have hnorm : ∀ i, ((d i : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) ^
        (2 ^ (f + 1) + 1) = 1 := by
      intro i
      have h1 := mem_primeFormUnitary.mp hdU
      rw [idGram, Units.val_one, Matrix.mul_one, coe_diagHom, diagonal_map (map_zero _),
        diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one] at h1
      have h2 : h.bar ((d i : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) *
          ((d i : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) = 1 := by
        simpa using congrFun (diagonal_injective h1) i
      rw [UnitaryFieldData.bar_apply] at h2
      rw [pow_succ]
      exact h2
    refine ⟨d, hnorm, fun s s' hs' => ?_⟩
    have hQN := SUTorus.mem_normalizer_of_mem_primeFormUnitary h hQ
    set u : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
      ⟨Q * s * Q⁻¹, (Subgroup.mem_normalizer_iff.mp hQN s).mp s.2⟩ with hu
    set v : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
      ⟨Q * s' * Q⁻¹, (Subgroup.mem_normalizer_iff.mp hQN s').mp s'.2⟩ with hv
    have hφs : ∀ (s₀ : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n))
        (u₀ : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)),
        (u₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) = Q * s₀ * Q⁻¹ →
        SURep.ggFrameU hF ψ (Q⁻¹ * P₀) hP s₀ = ψ₁ u₀ := by
      intro s₀ u₀ hu₀
      have hsu : (SURep.ggFrameEquiv hF (Q⁻¹ * P₀) hP).symm s₀ =
          (SURep.ggFrameEquiv hF P₀ hP₀).symm u₀ := by
        apply Subtype.ext
        rw [SURep.coe_ggFrameEquiv_symm, SURep.coe_ggFrameEquiv_symm, hu₀]
        group
      exact (SURep.ggFrameU_apply hF ψ (Q⁻¹ * P₀) hP s₀).trans
        ((congrArg ψ hsu).trans (SURep.ggFrameU_apply hF ψ P₀ hP₀ u₀).symm)
    rw [hφs s u rfl, hφs s' v rfl]
    refine hB'.2 u v ?_
    have hB'eq : B' = Q * diagHom n d * Q⁻¹ := by rw [← hd]; group
    change Q * s' * Q⁻¹ = B' * (Q * s * Q⁻¹) * B'⁻¹
    rw [hs', hB'eq]
    group
  exact ⟨Q⁻¹ * P₀, hP, hdiag⟩

end UnitModel

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepToral
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelBasic

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

namespace UnitModel

variable {G : Type} [Group G] {n f : ℕ} {F : Type} [Field F]

theorem exists_elemAbelian_diagU (h : UnitaryFieldData 2 f F) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) (hn : 3 ≤ n) {φ : ↥(unitarySU 2 f F n) →* G}
    (hker : SURep.GGFrameKer φ) :
    ∃ E : Subgroup G, E ≤ φ.range ∧ IsElemAbelian p E ∧ Nat.card E = p ^ (n - 2) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, hζN⟩ := exists_orderOf_eq_norm_one h hp hpq
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  set m := n - 2 with hm
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set c : Fin m → Fin n → Fˣ := fun j =>
    Pi.mulSingle i0 ζ * Pi.mulSingle (⟨(j : ℕ) + 1, by omega⟩ : Fin n) ζ⁻¹ with hcdef
  have hsingle : ∀ (j : Fin m) (i : Fin n), (i : ℕ) ≠ 0 → (i : ℕ) ≠ j + 1 → c j i = 1 := by
    intro j i h0 h1
    simp only [hcdef, Pi.mul_apply]
    rw [Pi.mulSingle_eq_of_ne (fun h => h0 (by rw [h])),
      Pi.mulSingle_eq_of_ne (fun h => h1 (by rw [h])), one_mul]
  have hcp : ∀ j i, c j i ^ p = 1 := by
    intro j i
    simp only [hcdef, Pi.mul_apply, mul_pow, Pi.mulSingle_apply]
    split_ifs <;> simp [hζp]
  have hcnorm : ∀ j i, c j i ^ (2 ^ f + 1) = 1 := by
    intro j i
    simp only [hcdef, Pi.mul_apply, mul_pow, Pi.mulSingle_apply]
    split_ifs <;> simp [hζN]
  have hcprod : ∀ j, ∏ i, c j i = 1 := by
    intro j
    simp only [hcdef, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
      Finset.mem_univ, ite_true, mul_inv_cancel]
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p := by
    intro j
    refine ⟨⟨(j : ℕ) + 1, by omega⟩, fun j' hj' => hsingle j' _ (by simp)
      (fun h => hj' (Fin.ext (by simp at h; omega)).symm), ?_⟩
    have h1 : c j ⟨(j : ℕ) + 1, by omega⟩ = ζ⁻¹ := by
      simp only [hcdef, Pi.mul_apply, Pi.mulSingle_eq_same]
      rw [Pi.mulSingle_eq_of_ne (by simp [hi0, Fin.ext_iff]), one_mul]
    rw [h1, orderOf_inv, hζ]
  let θ : Multiplicative (Fin m → ZMod p) →* ↥(unitarySU 2 f F n) :=
    { toFun := fun a => ⟨diagHom n (expHom c hcp a),
        diagHom_expHom_mem_unitarySU h c hcp hcprod hcnorm a⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul] }
  have hθ : ∀ a, ((θ a : ↥(unitarySU 2 f F n)) : GL (Fin n) F) = diagHom n (expHom c hcp a) :=
    fun _ => rfl
  have hlast : ∀ a, expHom c hcp a ⟨n - 1, by omega⟩ = 1 := by
    intro a
    rw [expHom_apply]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [hsingle j _ (by simp; omega) (by simp; omega), one_pow]
  have hinj : Function.Injective (φ.comp θ) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨s, hs⟩ := hker (θ a) ha
    have h1 := congrFun (congrFun hs ⟨n - 1, by omega⟩) ⟨n - 1, by omega⟩
    rw [hθ, coe_diagHom, diagonal_apply_eq, hlast, Units.val_one, Matrix.scalar_apply,
      diagonal_apply_eq] at h1
    have hs1 : ((θ a : ↥(unitarySU 2 f F n)) : GL (Fin n) F) = 1 := by
      apply Units.ext
      rw [hs, ← h1, map_one, Units.val_one]
    apply expHom_injective c hcp hpriv
    apply diagHom_injective n
    rw [← hθ, hs1, map_one, map_one]
  refine ⟨(φ.comp θ).range, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨θ x, rfl⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, rfl⟩ := a
      obtain ⟨_, y, rfl⟩ := b
      apply Subtype.ext
      change (φ.comp θ) x * (φ.comp θ) y = (φ.comp θ) y * (φ.comp θ) x
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have hx : x ^ p = 1 := by
        apply Multiplicative.toAdd.injective
        funext j
        simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul,
          ZMod.natCast_self, zero_mul]
      rw [hx, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem exists_frame_of_su [Finite G] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hnp : n = p)
    (hpq : p ∣ 2 ^ (f + 1) + 1)
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
        (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) b) ∧
      Nat.card Bs ≤ p ^ (n - 1) := by
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hp2 : p ≠ 2 := by omega
  have hn4 : 4 ≤ n := by omega
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
  have hbig : p ^ (n / p + 1) < Nat.card Bs := by
    rw [hnp, Nat.div_self hp.pos]
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right hp.one_lt (by omega)) (hnp ▸ hlow)
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
  refine ⟨Q⁻¹ * P₀, hP, hdiag, ?_⟩
  have hcent : Subgroup.centralizer
      ((SURep.ggFrameU hF ψ (Q⁻¹ * P₀) hP).range : Set G) = ⊥ := by
    rw [SURep.range_ggFrameU]
    exact hC
  have hpF : p ∣ Nat.card (GaloisField 2 (2 * (f + 1))) - 1 := by
    rw [hF]
    have h1 : (2 ^ (f + 1)) ^ 2 - 1 = (2 ^ (f + 1) + 1) * (2 ^ (f + 1) - 1) := by
      rw [← Nat.sq_sub_sq, one_pow]
    rw [h1]
    exact Dvd.dvd.mul_right hpq _
  have h1 := SURep.card_le_of_frameU hp hpF h (by omega)
    (SURep.ggFrameKer_ggFrameU hF ψ (Q⁻¹ * P₀) hP (by omega) hnq hker) hcent
    (fun b hb => hBsE.2 b hb) hdiag (S := {(⟨0, by omega⟩ : Fin n)}) (i₀ := ⟨0, by omega⟩)
    (fun b _ τ _ i hi => by rw [Finset.mem_singleton.mp hi])
  rwa [Finset.card_compl, Finset.card_singleton, Fintype.card_fin] at h1

end UnitModel

end CFSG.StandardType

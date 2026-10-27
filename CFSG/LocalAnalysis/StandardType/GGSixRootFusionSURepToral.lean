module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepMain
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (expHom expHom_apply expHom_injective
  diagHom_expHom_mem_unitarySU exists_orderOf_eq_norm_one permGL_mul_diagHom_mul_inv)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace SURep

variable {G : Type} [Group G] [Finite G] {n f : ℕ} {F : Type} [Field F]

theorem sub_three_le_twoLocalRankU (h : UnitaryFieldData 2 f F) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hn : 4 ≤ n) {φ : ↥(unitarySU 2 f F n) →* G}
    (hker : GGFrameKer φ) : n - 3 ≤ LargeEvenTwoLocalRank p G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, hζN⟩ := exists_orderOf_eq_norm_one h hp hpq
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  set m := n - 3 with hm
  set c : Fin m → Fin n → Fˣ := fun j i =>
    if (i : ℕ) = 0 ∨ (i : ℕ) = 1 then ζ else if (i : ℕ) = j + 2 then ζ⁻¹ ^ 2 else 1 with hcdef
  have hcp : ∀ j i, c j i ^ p = 1 := by
    intro j i
    simp only [hcdef]
    split_ifs
    · exact hζp
    · rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζp, inv_one, one_pow]
    · exact one_pow p
  have hcnorm : ∀ j i, c j i ^ (2 ^ f + 1) = 1 := by
    intro j i
    simp only [hcdef]
    split_ifs
    · exact hζN
    · rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζN, inv_one, one_pow]
    · exact one_pow _
  have hcprod : ∀ j, ∏ i, c j i = 1 := by
    intro j
    set i0 : Fin n := ⟨0, by omega⟩
    set i1 : Fin n := ⟨1, by omega⟩
    set i2 : Fin n := ⟨(j : ℕ) + 2, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    have hfun : c j = Function.update (Function.update (Function.update (fun _ => (1 : Fˣ)) i0
        ζ) i1 ζ) i2 (ζ⁻¹ ^ 2) := by
      funext i
      simp only [hcdef, Function.update_apply, i0, i1, i2, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [hfun, SLRep.prod_update_update_update_one h01 h02 h12, inv_pow]
    group
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p := by
    intro j
    refine ⟨⟨(j : ℕ) + 2, by omega⟩, fun j' hj' => ?_, ?_⟩
    · have hne : ¬ ((j : ℕ) + 2 = j' + 2) := fun h' => hj' (Fin.ext (by omega)).symm
      simp only [hcdef, show ¬ ((j : ℕ) + 2 = 0 ∨ (j : ℕ) + 2 = 1) by omega, hne, ite_false]
    · simp only [hcdef, show ¬ ((j : ℕ) + 2 = 0 ∨ (j : ℕ) + 2 = 1) by omega, ite_false,
        ite_true]
      rw [Nat.Coprime.orderOf_pow (by rw [orderOf_inv, hζ]; exact
        (Nat.coprime_primes hp Nat.prime_two).mpr hp2), orderOf_inv, hζ]
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
    have h1 : c j ⟨n - 1, by omega⟩ = 1 := by
      simp only [hcdef, show ¬ (n - 1 = 0 ∨ n - 1 = 1) by omega,
        show ¬ (n - 1 = (j : ℕ) + 2) by omega, ite_false]
    rw [h1, one_pow]
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
  set E := (φ.comp θ).range with hE
  have hEcard : Nat.card E = p ^ m := by
    rw [hE, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hEel : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
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
  set w := swapU h (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ with hw
  set U₀ := Subgroup.zpowers (φ w) with hU₀
  have hw2 : w ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hw]
    change (permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) : GL (Fin n) F) ^ 2 = 1
    rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]
  have hφw1 : φ w ≠ 1 := by
    intro h1
    obtain ⟨s, hs⟩ := hker w h1
    have h2 := congrFun (congrFun hs ⟨0, by omega⟩) ⟨1, by omega⟩
    rw [Matrix.scalar_apply, diagonal_apply_ne _ (by simp [Fin.ext_iff])] at h2
    have h3 : ((w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 := by
      rw [hw]
      change ((permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) ⟨0, by omega⟩ ⟨1, by omega⟩ = 1
      rw [TableBUE.permGL_apply, Equiv.swap_inv, Equiv.swap_apply_left, ite_eq_left rfl]
    rw [h3] at h2
    exact one_ne_zero h2
  have hφw2 : φ w ^ 2 = 1 := by rw [← map_pow, hw2, map_one]
  have hord : orderOf (φ w) = 2 := orderOf_eq_prime hφw2 hφw1
  have hU2 : IsPGroup 2 U₀ := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hU₀, Nat.card_zpowers, hord, pow_one]
  have hU1 : U₀ ≠ ⊥ := by
    intro hbot
    apply hφw1
    have hmem : φ w ∈ U₀ := Subgroup.mem_zpowers _
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hc01 : ∀ a, expHom c hcp a ∘ (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩).symm =
      expHom c hcp a := by
    intro a
    funext i
    rw [Function.comp_apply, Equiv.symm_swap, expHom_apply, expHom_apply]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    simp only [hcdef]
    by_cases hi0 : (i : ℕ) = 0
    · have : Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ i = ⟨1, by omega⟩ := by
        rw [show i = ⟨0, by omega⟩ from Fin.ext hi0, Equiv.swap_apply_left]
      rw [this]
      simp [hi0]
    by_cases hi1 : (i : ℕ) = 1
    · have : Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ i = ⟨0, by omega⟩ := by
        rw [show i = ⟨1, by omega⟩ from Fin.ext hi1, Equiv.swap_apply_right]
      rw [this]
      simp [hi1]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun h' => hi0 (by rw [h'])) (fun h' => hi1 (by rw [h']))]
  have hcomm : ∀ a, (φ.comp θ) a * φ w = φ w * (φ.comp θ) a := by
    intro a
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hθ, hw]
    change diagHom n (expHom c hcp a) * permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) =
      permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) * diagHom n (expHom c hcp a)
    have h1 := permGL_mul_diagHom_mul_inv (K := F)
      (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) (expHom c hcp a)
    rw [hc01 a, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hEN : E ≤ Subgroup.normalizer (U₀ : Set G) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hc : Commute ((φ.comp θ) a) (φ w) := hcomm a
    constructor
    · intro hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact hg
    · intro hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hg' : g = (φ w) ^ k := by
        have h1 : g = ((φ.comp θ) a)⁻¹ * ((φ.comp θ) a * g * ((φ.comp θ) a)⁻¹) *
            (φ.comp θ) a := by group
        rw [h1, ← hk, ((hc.inv_left).zpow_right k).eq, inv_mul_cancel_right]
      rw [hg']
      exact Subgroup.zpow_mem_zpowers _ k
  have hk := TableB.le_pRank_of_le hp.one_lt hEN hEel hEcard
  exact TableB.le_twoLocalRank hp.one_lt ⟨U₀, hU1, hU2, rfl⟩ hk

end SURep

section Input

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem ggSUBstarFrameInput_holds : GGSUBstarFrameInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hpq
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn4 : 4 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
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
      (hctx.2.2.2.2.2.2.1.2 b⁻¹ (Bs.inv_mem hb))
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
    rw [hr₁, hrange, s1.1, inf_bot_eq]
  have hm3 : n - 3 ≤ LargeEvenTwoLocalRank p G :=
    SURep.sub_three_le_twoLocalRankU h hp hp2 hpq hn4
      (SURep.ggFrameKer_of_ker_le_center hF (by omega) hnq hker₁)
  have hm4 : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
  have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1
  have hdiv : n / p ≤ n / 3 := Nat.div_le_div_left hp3 (by norm_num)
  have hbig : p ^ (n / p + 1) < Nat.card Bs := by
    have hlt : n / p + 1 < LargeEvenTwoLocalRank p G := by omega
    exact (Nat.pow_lt_pow_right hp.one_lt hlt).trans_le (hBcard ▸ hBle)
  have hBsel : IsElemAbelian p Bs := hctx.2.1.2.1
  have hT := SUTorus.isToral_inducedMatrices h (by omega) hnq hp hp2 hpq hker₁ hBsel hbig hEA hEC
  obtain ⟨Q, hQ, hQd⟩ := SUTorus.exists_unitary_frame h hp hp2 hpq
    (SUTorus.isProjElem_inducedMatrices h (by omega) hnq hp hpq hker₁ hBsel) hT
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
  refine ⟨Q⁻¹ * P₀, hP, fun b hb => ?_⟩
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

theorem ggSixRootFusionSURepInput_of_nonsplit_residual
    (hN : GGSixRootFusionSURepNonsplitInput) (hR : GGSixRootFusionSURepResidualInput) :
    GGSixRootFusionSURepInput :=
  ggSixRootFusionSURepInput_of_frame ggSUBstarFrameInput_holds hN hR

end Input

end CFSG.StandardType

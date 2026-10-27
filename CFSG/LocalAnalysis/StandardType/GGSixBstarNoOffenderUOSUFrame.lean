module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepair
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairLocal
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalSp
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUO

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

namespace NoOffUO

section Frame

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem exists_suFrameDiag (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (n f : ℕ) (ψ : (ggU .PSU n (f + 1)).K →* G)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ)
    (hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥) (hpq : p ∣ 2 ^ (f + 1) + 1) :
    ∃ (P : GL (Fin n) (GaloisField 2 (2 * (f + 1))))
      (hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
        (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n),
      ∀ b ∈ Bs, SURep.GGFrameDiagU (SURep.ggFrameU
        (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) b := by
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
    rw [hr₁, hrange, hC, inf_bot_eq]
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

theorem exists_uFrame (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (m f : ℕ) (ψ : (ggU .PSU (m + 1) (f + 1)).K →* G)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSU (m + 1) (f + 1)).D .PSU (m + 1) (f + 1) ψ)
    (hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥) (hpq : p ∣ 2 ^ (f + 1) + 1) :
    ∃ Q : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1))),
      UFusion.IsUFrame (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) Q ∧
        Bs ≤ UFusion.uFrameTorus ψ Q := by
  obtain ⟨P, hP, hB⟩ := exists_suFrameDiag G p B Bs x L D J (m + 1) f ψ hctx hC hpq
  exact ⟨P, hP, fun b hb => UFusion.mem_uFrameTorus_of_frameDiagU _ hP (hB b hb)⟩

end Frame

section Aut

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormConjHom primeFormConjHom_mk
  primeFormUnitary mem_primeFormUnitary primeFormFieldHom primeFormPsi primeFormPsi_apply
  primeFormPsi_eq_one_iff conj_mem_gramSU)

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
  {n : ℕ} {G : Type} [Group G]

@[expose] noncomputable def inducedAut (hn : 4 ≤ n) {ψ : SU (unitaryInvolution K 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ↥(Subgroup.normalizer (ψ.range : Set G)) →* MulAut (AutPSU.PJ h n) :=
  (MulAut.congr (AutPSU.projEquivU h hn hker hC).symm).toMonoidHom.comp
    ψ.range.normalizerMonoidHom

theorem inducedAut_spec (hn : 4 ≤ n) {ψ : SU (unitaryInvolution K 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (y : ↥(Subgroup.normalizer (ψ.range : Set G))) (z : AutPSU.PJ h n) :
    ((AutPSU.projEquivU h hn hker hC (inducedAut h hn hker hC y z) : ψ.range) : G) =
      (y : G) * (AutPSU.projEquivU h hn hker hC z : G) * (y : G)⁻¹ := by
  simp only [inducedAut, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  rfl

theorem mem_normalizer_of_mem_suInducedPairs {ψ : SU (unitaryInvolution K 2 f) n →* G} {z : G}
    {X : GL (Fin n) K} (hX : (z, X) ∈ UFusion.suInducedPairs ψ) :
    z ∈ Subgroup.normalizer (ψ.range : Set G) := by
  have hX' := (UFusion.suInducedPairs ψ).inv_mem hX
  rw [Prod.inv_mk] at hX'
  refine Subgroup.mem_normalizer_iff.mpr fun r => ⟨?_, ?_⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨hJ, hu⟩ := hX
    exact ⟨_, (hu u).symm⟩
  · rintro ⟨u, hu⟩
    obtain ⟨hJ', hu'⟩ := hX'
    refine ⟨InnerDiagSU.conjSU X⁻¹ hJ' u, ?_⟩
    rw [← hu' u, hu]
    group

theorem inducedAut_eq_conj (hn : 4 ≤ n) {ψ : SU (unitaryInvolution K 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {z : G} {X : GL (Fin n) K}
    (hJ : InnerDiagSU.IsJUnitary (unitaryInvolution K 2 f) X)
    (hX : ∀ u, z * ψ u * z⁻¹ = ψ (InnerDiagSU.conjSU X hJ u))
    (hz : z ∈ Subgroup.normalizer (ψ.range : Set G)) :
    inducedAut h hn hker hC ⟨z, hz⟩ =
      primeFormConjHom h _ ⟨X, SURepair.mem_primeFormUnitary_of_isJUnitary h hJ⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΘu : ∀ u, AutPSU.projEquivU h hn hker hC (AutPSU.projU h u) =
      ⟨ψ u, MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩ := fun u =>
    Subtype.ext (AutPSU.projEquivU_projU h hn hker hC u)
  apply MulEquiv.ext
  intro w
  induction w using QuotientGroup.induction_on with
  | H x =>
    set u := (AutPSU.suEquiv h).symm x with hu
    have hxu : (x : AutPSU.PJ h n) = AutPSU.projU h u := by
      rw [AutPSU.projU_apply, hu, MulEquiv.apply_symm_apply]
    have e : ((⟨(X : GL (Fin n) K) * (x : GL (Fin n) K) * X⁻¹,
        conj_mem_gramSU h _ (SURepair.mem_primeFormUnitary_of_isJUnitary h hJ) x.2⟩ :
          ↥(AutPSU.XJ h n)) : AutPSU.PJ h n) =
        AutPSU.projU h (InnerDiagSU.conjSU X hJ u) := by
      rw [AutPSU.projU_apply]
      congr 1
    apply (AutPSU.projEquivU h hn hker hC).injective
    apply Subtype.ext
    rw [primeFormConjHom_mk, e, hΘu, inducedAut_spec, hxu, hΘu]
    exact hX u

omit [Finite K] [CharP K 2] in
theorem eq_scalar_of_conj_eq_one (hn : 4 ≤ n)
    {W : primeFormUnitary h ((AutPSU.gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hW : primeFormConjHom h _ W = 1) :
    ∃ c : Kˣ, (W : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hPsi : primeFormPsi h AutPSU.isPrimeFormGram_gramJ ⟨W, 1⟩ = 1 := by
    rw [primeFormPsi_apply, hW, one_mul, map_one]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h AutPSU.isPrimeFormGram_gramJ (by omega)
    _).mp hPsi
  exact ⟨c, hc⟩

include h in
theorem eq_scalar_of_suInducedPairs (hn : 4 ≤ n) {ψ : SU (unitaryInvolution K 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {z : G} {X Y : GL (Fin n) K}
    (hX : (z, X) ∈ UFusion.suInducedPairs ψ) (hY : (z, Y) ∈ UFusion.suInducedPairs ψ) :
    ∃ c : Kˣ, X⁻¹ * Y = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hW := (UFusion.suInducedPairs ψ).mul_mem ((UFusion.suInducedPairs ψ).inv_mem hX) hY
  rw [Prod.inv_mk, Prod.mk_mul_mk, inv_mul_cancel] at hW
  have h1 := mem_normalizer_of_mem_suInducedPairs hW
  obtain ⟨hJ, hW'⟩ := hW
  have e := inducedAut_eq_conj h hn hker hC hJ hW' h1
  have e1 : inducedAut h hn hker hC ⟨1, h1⟩ = 1 := by
    rw [show (⟨1, h1⟩ : ↥(Subgroup.normalizer (ψ.range : Set G))) = 1 from rfl, map_one]
  rw [e1] at e
  exact eq_scalar_of_conj_eq_one h hn e.symm

end Aut

end NoOffUO

end CFSG.StandardType

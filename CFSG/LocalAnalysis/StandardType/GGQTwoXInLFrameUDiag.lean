module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

private lemma ggQTUf_exists_diagUnits {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} {a : MulAut L'} {t : Fin d → K}
    (ha : LineU.ActsDiagU φ a t) :
    ∃ (σ : Fin d → Kˣ) (hD : diagHom d σ ∈
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
      ∀ s : ↥(unitarySU 2 n K d), a (φ s) = φ (LineU.conjN (diagHom d σ) hD s) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  have h0 : ∀ k, t k ≠ 0 := fun k => LineU.diag_ne_zero_of_eq hDt k
  set σ : Fin d → Kˣ := fun k => Units.mk0 (t k) (h0 k) with hσ
  have hDσ : D = diagHom d σ := by
    apply Units.ext
    rw [hDt, CFSG.SectionRank.OddCover.coe_diagHom]
    rfl
  subst hDσ
  exact ⟨σ, hD, hact⟩

private lemma ggQTUf_scalar_mem_center {K : Type} [Field K] {n d : ℕ}
    {g : ↥(unitarySU 2 n K d)} {c : K}
    (hc : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) :
    g ∈ Subgroup.center ↥(unitarySU 2 n K d) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  apply Units.ext
  ext i j
  simp only [Units.val_mul, hc, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact mul_comm _ c

theorem ggQTwoXInLU_frame
    {N : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hperf : commutator ↥(ggG0 3 B x L D J) = ⊤)
    (hN : 7 ≤ N) (M : GGXInL.lup8f_UnitaryMarking Bs (ggG0 3 B x L D J) N K) :
    Nonempty (GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K) := by
  classical
  let X : Subgroup G := ggG0 3 B x L D J
  have hperfX : commutator ↥X = ⊤ := hperf
  have hBN : Bs ≤ Subgroup.normalizer (X : Set G) := M.normalizes
  obtain ⟨-, hBs, -, -, -⟩ := hS.1.1.tableB_facts
  have hK4 : Nat.card K = (2 ^ 1) ^ 2 := by rw [M.card_K]; norm_num
  have hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card hK4 le_rfl
  have hψs : Function.Surjective (ggQuotHom M.theta) := ggQuotHom_surjective M.theta
  have hψker : (ggQuotHom M.theta).ker ≤ Subgroup.center ↥X := by
    rw [ker_ggQuotHom]
  have hA : CFSG.Open.IsElemAbelian 3 (ggGamma X hBN).range :=
    isElemAbelian_range (fun a b => hBs.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hBs.2 a a.2)) (ggGamma X hBN)
  have hAI : ∀ a ∈ (ggGamma X hBN).range,
      ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K N))
        (LargeEvenGUSet (Fin N) K (2 ^ 1)), ∀ l : ↥X,
        x (ggQuotHom M.theta l) = ggQuotHom M.theta (a l) := by
    rintro a ⟨b, rfl⟩
    exact ⟨ggBeta X M.theta hBN b, ggBeta_mem X M.theta hBN M.action b,
      fun l => ggBeta_ggQuotHom X hBN M.theta b l⟩
  have hcardA : Nat.card ↥(ggGamma X hBN).range = Nat.card ↥Bs := by
    have hker : (ggGamma X hBN).ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro b hb
      rw [MonoidHom.mem_ker] at hb
      have hmem : (b : G) ∈ Bs ⊓ Subgroup.centralizer (X : Set G) :=
        ⟨b.2, (ggGamma_eq_one_iff X hBN b).mp hb⟩
      have hbot : Bs ⊓ Subgroup.centralizer (X : Set G) = ⊥ :=
        bstar_inf_centralizer_ggG0_eq_bot hS.1.1
      rw [hbot] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    have h := Subgroup.card_ker_mul_card_range (ggGamma X hBN)
    rw [hker, Subgroup.card_bot] at h
    simpa using h
  have hcov : LineU.UnitaryCoverAt 1 N K :=
    LineU.unitaryCoverAt (n := 1) (d := N) hK4 (by omega) (by rintro ⟨h, -⟩; omega)
  have hdiag : ∃ φ : ↥(unitarySU 2 1 K N) →* ↥X, Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 1 K N), φ g = 1 →
        ∃ c : K, ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
          diagonal (fun _ => c)) ∧
      ∀ a ∈ (ggGamma X hBN).range, ∃ t : Fin N → K, LineU.ActsDiagU φ a t := by
    by_cases h3 : 3 ∣ N
    · have hle : N / 3 + 2 ≤ N - 3 := by
        obtain ⟨k, rfl⟩ := h3
        omega
      have hlift : GGTorusLift 3 (ggUnitaryTorusRank 3 N)
          (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)) :=
        ggTorusLift_unitary (n := 1) (d := N) (p := 3) hK4 le_rfl (by omega)
          (by rintro ⟨h, -⟩; omega) Nat.prime_three (by norm_num)
      have hpow := pow_le_card_bstar_of_torusLift hS.1.1 hperfX M.theta hlift
      have hrank : ggUnitaryTorusRank 3 N = N - 3 := by
        simp only [ggUnitaryTorusRank, if_pos h3]
      rw [hrank] at hpow
      have hcard : 3 ^ (N / 3 + 2) ≤ Nat.card ↥(ggGamma X hBN).range := by
        rw [hcardA]
        exact (Nat.pow_le_pow_right (by norm_num) hle).trans hpow
      exact LineU.exists_diagModel (L' := ↥X) (K := K) (n := 1) (d := N) (p := 3)
        hK4 le_rfl (by omega) Nat.prime_three (by norm_num) h3 hcov
        hψs hψker hperfX hA hAI hcard
    · exact LineU.exists_diagModel_coprime (L' := ↥X) (K := K) (n := 1) (d := N) (p := 3)
        hK4 le_rfl (by omega) Nat.prime_three (by norm_num) h3 hcov
        hψs hψker hperfX hA hAI
  obtain ⟨φ, hφs, hφker, hφdiag⟩ := hdiag
  have hex : ∀ b : ↥Bs, ∃ (σ : Fin N → Kˣ) (hD : diagHom N σ ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))),
      ∀ s : ↥(unitarySU 2 1 K N), ggGamma X hBN b (φ s) =
        φ (LineU.conjN (diagHom N σ) hD s) := by
    intro b
    obtain ⟨t, ht⟩ := hφdiag (ggGamma X hBN b) ⟨b, rfl⟩
    exact ggQTUf_exists_diagUnits ht
  choose σ hσD hσact using hex
  refine ⟨{ field := hfield
            φ := X.subtype.comp φ
            range_eq := ?_
            ker_le := ?_
            δ := fun b => if hb : b ∈ Bs then σ ⟨b, hb⟩ else 1
            pair := ?_ }⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφs, Subgroup.map_top]
    exact Subgroup.range_subtype X
  · rw [MonoidHom.ker_comp_of_injective φ X.subtype X.subtype_injective]
    intro g hg
    obtain ⟨c, hc⟩ := hφker g hg
    exact ggQTUf_scalar_mem_center hc
  · intro b hb
    rw [dif_pos hb]
    refine SUTorus.mem_suPairs.mpr ⟨hσD ⟨b, hb⟩, ?_⟩
    intro u v huv
    have hvu : v = LineU.conjN (diagHom N (σ ⟨b, hb⟩)) (hσD ⟨b, hb⟩) u :=
      Subtype.ext (by rw [LineU.coe_conjN]; exact huv)
    rw [hvu]
    show b * ((φ u : ↥X) : G) * b⁻¹ =
      ((φ (LineU.conjN (diagHom N (σ ⟨b, hb⟩)) (hσD ⟨b, hb⟩) u) : ↥X) : G)
    rw [← ggGamma_coe X hBN ⟨b, hb⟩ (φ u), hσact ⟨b, hb⟩ u]

end CFSG.StandardType

end

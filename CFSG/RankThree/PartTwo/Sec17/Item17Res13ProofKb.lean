module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res12ProofKb
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofDelta
public import CFSG.RankThree.PartTwo.Sec17.Item17Res12ProofSolv
import CFSG.RankThree.PartTwo.Sec14.Item146General

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

@[expose] noncomputable def Step174KbM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ X : Subgroup G, X = delta A (lB A) X → ¬ 3 ∣ Nat.card X →
      ∀ K ∈ thetaComponentsIn X,
        (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) →
        CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K →
        (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
          (CFSG.Open.pCoreOf 2 Y₀) →
        A ≤ Subgroup.normalizer (K : Set G) →
        (∀ Y ∈ scriptY3 A (lB A), Y ≤ Subgroup.normalizer (Y₀ : Set G)) →
        ∀ b ∈ A ⊓ L, b ≠ 1 →
          CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
          inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤
              pPrimeCoreOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) ∧
            ∀ d ∈ delta A (lB A) (Subgroup.centralizer ({b} : Set G)),
              (inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G))).map
                (MulAut.conj d).toMonoidHom ≤ Subgroup.normalizer (Y₀ : Set G)

namespace Proof17Res13

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

open Proof17Res12 in
theorem delta_le_of_conj_le
    (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    {X : Subgroup G} (hXQ : X ∈ scriptQ A (lB A)) {K : Subgroup G} (hKX : K ≤ X) {n : ℕ}
    (hn : CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n)
    (hθ : CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K)
    (hcen : (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hY3 : ∀ Y ∈ scriptY3 A (lB A), Y ≤ Subgroup.normalizer (Y₀ : Set G)) {b : G}
    (hb : b ∈ A ⊓ L) (hb1 : b ≠ 1)
    (hJO : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      pPrimeCoreOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))))
    (hJM : ∀ d ∈ delta A (lB A) (Subgroup.centralizer ({b} : Set G)),
      (inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G))).map
        (MulAut.conj d).toMonoidHom ≤ Subgroup.normalizer (Y₀ : Set G)) :
    delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := isE27_of_std h
  set D := delta A (lB A) (Subgroup.centralizer ({b} : Set G)) with hD
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set J := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) with hJdef
  have hb3 : orderOf b = 3 := orderOf_eq_prime (pow_three_of_std h hb.1) hb1
  have hJK : J ≤ K := (Subgroup.map_subtype_le _).trans inf_le_left
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha hb.1)
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    (Late.le_normalizer_inf hAK (hAb.trans Subgroup.le_normalizer)).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains _)
  have hJQ : J ∈ scriptQ A (lB A) := mem_scriptQ_of_le hXQ (hJK.trans hKX) hAJ
  have hn2 : CFSG.Blueprint.SuzukiModel (↥K ⧸ CFSG.pCore 2 ↥K) 2 n :=
    suzukiModel_quot_of_eq hθ.symm hn
  have hJ2 : 2 ∣ Nat.card J := two_dvd_card_perfectResidual hcen hn2 (h.le_y0 hb.2) (hAK hb.1) hb3
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := Sec14.le_normalizer_delta _
  have hDΔ : D = delta A (lB A) D := (delta_delta _).symm
  have hDO : D ≤ Subgroup.normalizer (pPrimeCoreOf 3 D : Set G) := le_normalizer_pPrimeCoreOf 3 D
  set E : Subgroup G := ⨆ d : D, J.map (MulAut.conj (d : G)).toMonoidHom with hEdef
  have hmemE : ∀ d ∈ D, ∀ j ∈ J, d * j * d⁻¹ ∈ E := fun d hd j hj =>
    Subgroup.mem_iSup_of_mem (⟨d, hd⟩ : D) ⟨j, hj, rfl⟩
  have hEM : E ≤ M := iSup_le fun d => hJM d d.2
  have hJE : J ≤ E := fun j hj => by simpa using hmemE 1 D.one_mem j hj
  have hEO : E ≤ pPrimeCoreOf 3 D := by
    refine iSup_le fun d => ?_
    rintro _ ⟨j, hj, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hDO d.2) j).mp (hJO hj)
  have hE3 : Nat.Coprime 3 (Nat.card E) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hEO) (coprime_card_pPrimeCoreOf 3 D)
  have hconjE : ∀ g : G, (∀ d ∈ D, ∀ j ∈ J, g * (d * j * d⁻¹) * g⁻¹ ∈ E) →
      g ∈ Subgroup.normalizer (E : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    refine Subgroup.iSup_induction (C := fun x => g * x * g⁻¹ ∈ E) _ hx ?_ ?_ ?_
    · rintro ⟨d, hd⟩ _ ⟨j, hj, rfl⟩
      exact hg d hd j hj
    · simp only [mul_one, mul_inv_cancel]
      exact E.one_mem
    · intro x y hx hy
      have := E.mul_mem hx hy
      convert this using 1
      group
  have hDE : D ≤ Subgroup.normalizer (E : Set G) := by
    intro g hg
    refine hconjE g fun d hd j hj => ?_
    have h1 := hmemE (g * d) (D.mul_mem hg hd) j hj
    convert h1 using 1
    group
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := by
    intro a ha
    refine hconjE a fun d hd j hj => ?_
    have h1 := hmemE (a * d * a⁻¹) ((Subgroup.mem_normalizer_iff.mp (hAD ha) d).mp hd)
      (a * j * a⁻¹) ((Subgroup.mem_normalizer_iff.mp (hAJ ha) j).mp hj)
    convert h1 using 1
    group
  have hEinv : E ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three E).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hE3), hAE⟩
  have hΔE : D ≤ Subgroup.normalizer (delta A (lB A) E : Set G) := by
    have := delta_le_normalizer_delta (fun Z hZ => delta_mem_scriptQ hA h146 hZ) hEinv hDE
    rwa [← hDΔ] at this
  have hJΔE : J ≤ delta A (lB A) E := le_delta hJQ hJE
  have hEΔ : E ≤ delta A (lB A) E := by
    refine iSup_le fun d => ?_
    rintro _ ⟨j, hj, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hΔE d.2) j).mp (hJΔE hj)
  have hEQ : E ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146 hEinv
    rwa [le_antisymm (delta_le E) hEΔ] at this
  have hE2 : 2 ∣ Nat.card E := hJ2.trans (Subgroup.card_dvd_of_le hJE)
  obtain ⟨T, hTA, hT1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two A E hA.isPGroup hAE hE3 hE2
  set T' := (T : Subgroup E).map E.subtype with hT'
  have hT'syl : CFSG.ABGLocalTools.IsSylowOf 2 T' E := ⟨T, rfl⟩
  have hT'E : T' ≤ E := Subgroup.map_subtype_le _
  have hT'Q : T' ∈ scriptQ A (lB A) := mem_scriptQ_of_le hEQ hT'E hTA
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map _
  have hNT : delta A (lB A) (Subgroup.normalizer (T' : Set G)) ≤ M :=
    hY3 _ (delta_normalizer_mem_scriptY3 h hT'Q hT'2 hT1 hT'E
      (ne_top_of_not_three_dvd h ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hE3)))
  refine sSup_le fun Q hQ => ?_
  have hQD : Q ≤ D := le_delta hQ.1 hQ.2
  have hQE : Q ≤ Subgroup.normalizer (E : Set G) := hQD.trans hDE
  have hHinv : Q ⊔ E ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, isPiSubgroup_piCompl_sup hQ.1.1.2.1 hEinv.2.1 hQE,
      Sec14.le_normalizer_sup hQ.1.1.2.2 hAE⟩
  have hHQ : Q ⊔ E ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146 hHinv
    rwa [le_antisymm (delta_le _)
      (sup_le (le_delta hQ.1 le_sup_left) (le_delta hEQ le_sup_right))] at this
  have hfr := le_sup_inf_normalizer (H := Q ⊔ E) le_sup_right
    (sup_le hQE Subgroup.le_normalizer) hT'syl
  have hAN : A ≤ Subgroup.normalizer
      ((Subgroup.normalizer (T' : Set G) : Subgroup G) : Set G) :=
    hTA.trans Subgroup.le_normalizer
  have hHNT : (Q ⊔ E) ⊓ Subgroup.normalizer (T' : Set G) ≤
      delta A (lB A) (Subgroup.normalizer (T' : Set G)) :=
    le_delta (mem_scriptQ_of_le hHQ inf_le_left (Late.le_normalizer_inf hHQ.1.2.2 hAN))
      inf_le_right
  exact (le_sup_left.trans hfr).trans (sup_le hEM (hHNT.trans hNT))

end Proof17Res13

open Proof17Res12 Proof17Res13 in
theorem rank3II_17_4_of_printM {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (h166 : Item166 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h168 : Item168 A (lB A) c L) (h146 : Item146 A (lB A)) (h172 : Item172 A (lB A))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hKF : KFact174) (hC : Claim174)
    (hKb : Step174KbM) : Item174 A (lB A) := by
  intro X hXΔ hX3
  by_contra hns
  obtain ⟨K, hK, n, hn⟩ := hKF G A c L Y₀ h X hXΔ hX3 hns
  refine false_of_delta_le h h166 hbot h168 h146 h172 h9 hC hXΔ hX3 hK hn ?_
  intro hXQ hθ hcen hAK hY3 b hb hb1 hO2
  obtain ⟨hJO, hJM⟩ := hKb G A c L Y₀ h X hXΔ hX3 K hK ⟨n, hn⟩ hθ hcen hAK hY3 b hb hb1 hO2
  exact delta_le_of_conj_le h h146 hXQ (le_of_mem_thetaComponentsIn hK) hn hθ hcen hAK hY3 hb
    hb1 hJO hJM

theorem item174_of_printM (h166 : Item166S17)
    (hbot : Item145BotS17) (h168 : Item168S17) (h146 : Item146S14) (h172 : Item172S17)
    (h9 : CardInfNineS17) (hKF : KFact174) (hC : Claim174) (hKb : Step174KbM) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item174 A (lB A) :=
  fun G _ _ A c L Y₀ h => rank3II_17_4_of_printM h (h166 G A c L Y₀ h) (hbot G A c L Y₀ h)
    (h168 G A c L Y₀ h) (h146 G A c L h.toSec14Std) (h172 G A c L Y₀ h) (h9 G A c L Y₀ h)
    hKF hC hKb

theorem sec17OThreeSolv_of_printM (h166 : Item166S17)
    (hbot : Item145BotS17) (h168 : Item168S17) (h146 : Item146S14) (h172 : Item172S17)
    (h9 : CardInfNineS17) (hKF : KFact174) (hC : Claim174) (hKb : Step174KbM) :
    Sec17OThreeSolv :=
  sec17OThreeSolv_of_item174 (item174_of_printM h166 hbot h168 h146 h172 h9 hKF hC hKb)

theorem step177OThreeSolv_of_printM (h166 : Item166S17)
    (hbot : Item145BotS17) (h168 : Item168S17) (h146 : Item146S14) (h172 : Item172S17)
    (h9 : CardInfNineS17) (hKF : KFact174) (hC : Claim174) (hKb : Step174KbM) :
    Step177OThreeSolv :=
  step177OThreeSolv_of_sec17 (sec17OThreeSolv_of_printM h166 hbot h168 h146 h172 h9 hKF hC hKb)

end CFSG.RankThree.PartTwo.Sec17

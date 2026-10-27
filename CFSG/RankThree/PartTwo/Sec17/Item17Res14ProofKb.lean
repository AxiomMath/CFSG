module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res13ProofKb
public import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofKF
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
import CFSG.RankThree.PartTwo.Sec14.Item146General

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

@[expose] noncomputable def Step174KbO : Prop :=
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
            pPrimeCoreOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G)))

@[expose] noncomputable def Step174KbOThree : Prop :=
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
          3 ∣ Nat.card (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) →
          inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤
            pPrimeCoreOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G)))

@[expose] noncomputable def Step174KbOOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) →
      ∀ X : Subgroup G, X = delta A (lB A) X → ¬ 3 ∣ Nat.card X →
      ∀ K ∈ thetaComponentsIn X,
        (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) →
        CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K →
        (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
          (CFSG.Open.pCoreOf 2 Y₀) →
        A ≤ Subgroup.normalizer (K : Set G) →
        (∀ Y ∈ scriptY3 A (lB A), Y ≤ Subgroup.normalizer (Y₀ : Set G)) →
        ∀ b ∈ A ⊓ L, b ≠ 1 → Subgroup.zpowers b ∈ omegaA A →
          CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
          3 ∣ Nat.card (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) →
          inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤
            pPrimeCoreOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G)))

@[expose] noncomputable def Step174KbOHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ X : Subgroup G, X = delta A (lB A) X → ¬ 3 ∣ Nat.card X →
      ∀ K ∈ thetaComponentsIn X,
        (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) →
        CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K →
        (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
          (CFSG.Open.pCoreOf 2 Y₀) →
        A ≤ Subgroup.normalizer (K : Set G) →
        (∀ Y ∈ scriptY3 A (lB A), Y ≤ Subgroup.normalizer (Y₀ : Set G)) →
        ∀ b ∈ A ⊓ L, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
          (∃ (b' : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A ∧ Lb ∈ lA A b' ∧
            Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2)) →
          CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
          3 ∣ Nat.card (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) →
          inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤
            pPrimeCoreOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G)))

theorem step174KbO_of_kbM (h : Step174KbM) : Step174KbO :=
  fun G _ _ A c L Y₀ hs X hXΔ hX3 K hK hSz hθ hcen hAK hY3 b hb hb1 hO2 =>
    (h G A c L Y₀ hs X hXΔ hX3 K hK hSz hθ hcen hAK hY3 b hb hb1 hO2).1

namespace Proof17Res14

section Tools

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem not_isSolvable_of_suzukiModel_quot {H : Type} [Group H]
    [Finite H] (N : Subgroup H) [N.Normal] {n : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (H ⧸ N) 2 n) : ¬ Group.IsSolvable H := by
  intro hs
  obtain ⟨hperf, h2⟩ := Proof1619.isPerfect_and_two_dvd_of_suzukiModel hSz
  have : Group.IsSolvable (H ⧸ N) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hpos : 0 < Nat.card (H ⧸ N) := Nat.card_pos
  have : Nontrivial (H ⧸ N) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    obtain ⟨k, hk⟩ := h2
    omega
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := H ⧸ N)).ne
    hperf.commutator_eq_top

theorem mem_normalizer_sSup_thetaComponentsIn {D : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer ((sSup (thetaComponentsIn D) : Subgroup G) : Set G) := by
  set E := sSup (thetaComponentsIn D) with hE
  have hmap : E.map (MulAut.conj g).toMonoidHom ≤ E := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (Proof1423.map_conj_mem_thetaComponentsIn1423 hg hK)
  exact Subgroup.mem_normalizer_fintype fun x hx => hmap ⟨x, hx, rfl⟩

theorem not_isSolvable_perfectResidual {K : Subgroup G}
    (hcen : (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀)) (hθ : CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K) {n : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) {b : G}
    (hbY : b ∈ Y₀) (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hb : orderOf b = 3) :
    ¬ Group.IsSolvable
      ↥(inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G))) := by
  obtain ⟨eJ⟩ := Proof17Res12.nonempty_quotTheta_perfectResidual hcen hθ hSz hbY hbK hb
  exact not_isSolvable_of_suzukiModel_quot _ (Proof17Res12.suzukiModel_of_mulEquiv' eJ hSz)

theorem perfectResidual_mem_scriptQ (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    {X K : Subgroup G} (hXΔ : X = delta A (lB A) X) (hX3 : ¬ 3 ∣ Nat.card X)
    (hK : K ∈ thetaComponentsIn X) (hAK : A ≤ Subgroup.normalizer (K : Set G)) {b : G}
    (hb : b ∈ A) :
    inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) ∈ scriptQ A (lB A) ∧
      inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤
        delta A (lB A) (Subgroup.centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := isE27_of_std h
  set J := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) with hJdef
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
    have := Sec14.le_normalizer_delta (A := A) (LB := lB A) X
    rwa [← hXΔ] at this
  have hXQ : X ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146
      ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three X).mpr hX3, hAX⟩
    rwa [← hXΔ] at this
  have hJK : J ≤ K := (Subgroup.map_subtype_le _).trans inf_le_left
  have hJC : J ≤ Subgroup.centralizer ({b} : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha hb)
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    (Late.le_normalizer_inf hAK (hAb.trans Subgroup.le_normalizer)).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains _)
  have hJQ : J ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hXQ (hJK.trans (le_of_mem_thetaComponentsIn hK)) hAJ
  exact ⟨hJQ, le_delta hJQ hJC⟩

theorem not_three_dvd_card_sup_pPrimeCoreOf {b : G} (hb : b ∈ A) :
    ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) : Set G) :=
    (pPrimeCoreOf_le 3 _).trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb)).trans
      (le_normalizer_pPrimeCoreOf 3 _))
  rw [sup_comm]
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans (card_sup_dvd_card_mul hle)) with
    h1 | h1
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _) h1
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _) h1

end Tools

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem le_M_of_le_pPrimeCoreOf (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A))
    (h146 : Item146 A (lB A))
    (hY3 : ∀ Y ∈ scriptY3 A (lB A), Y ≤ Subgroup.normalizer (Y₀ : Set G)) {D J : Subgroup G}
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) (hDΔ : D = delta A (lB A) D)
    (hJQ : J ∈ scriptQ A (lB A)) (hJO : J ≤ pPrimeCoreOf 3 D) (hJs : ¬ Group.IsSolvable J) :
    D ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := isE27_of_std h
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set O := pPrimeCoreOf 3 D with hOdef
  have hOinv : O ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three O).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 D)),
      hAD.trans (normalizer_le_normalizer_pPrimeCoreOf 3 D)⟩
  set F := delta A (lB A) O with hFdef
  have hFQ : F ∈ scriptQ A (lB A) := delta_mem_scriptQ hA h146 hOinv
  have hJF : J ≤ F := le_delta hJQ hJO
  have hF3 : ¬ 3 ∣ Nat.card F := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 D)
      (h3.trans (Subgroup.card_dvd_of_le (delta_le O)))
  have hFtop : F ≠ ⊤ := Proof17Res12.ne_top_of_not_three_dvd h hF3
  have hAF : A ≤ Subgroup.normalizer (F : Set G) := Sec14.le_normalizer_delta _
  have hFΔ : F = delta A (lB A) F := (delta_delta _).symm
  have hFs : ¬ Group.IsSolvable F := fun hs =>
    hJs (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJF)
      (Subgroup.inclusion_injective hJF))
  have hDF : D ≤ Subgroup.normalizer (F : Set G) := by
    have := delta_le_normalizer_delta (fun Z hZ => delta_mem_scriptQ hA h146 hZ) hOinv
      (le_normalizer_pPrimeCoreOf 3 D)
    rwa [← hDΔ] at this
  set E : Subgroup G := sSup (thetaComponentsIn F) with hEdef
  have hEF : E ≤ F := sSup_le fun K hK => le_of_mem_thetaComponentsIn hK
  have hEM : E ≤ M := by
    refine sSup_le fun K hK => ?_
    obtain ⟨n, hn⟩ := exists_suzukiModel_of_mem_thetaComponentsIn h.toTheoremFourHyp hFtop hF3 hK
    obtain ⟨-, hcen⟩ := (h166 Y₀ h.mem_y0Star).1 F ⟨hFtop, hAF⟩ hFΔ K hK ⟨n, hn⟩
    exact fun x hx => (hcen hx).1
  have hDE : D ≤ Subgroup.normalizer (E : Set G) := fun d hd =>
    mem_normalizer_sSup_thetaComponentsIn (hDF hd)
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := fun a ha =>
    mem_normalizer_sSup_thetaComponentsIn (hAF ha)
  have hEQ : E ∈ scriptQ A (lB A) := mem_scriptQ_of_le hFQ hEF hAE
  have hE3 : Nat.Coprime 3 (Nat.card E) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hF3 (h3.trans (Subgroup.card_dvd_of_le hEF))
  have hE2 : 2 ∣ Nat.card E := by
    obtain ⟨K', hK'⟩ := Proof1423.exists_mem_thetaComponents_of_not_isSolvable hF3 hFs
    have hK : K'.map F.subtype ∈ thetaComponentsIn F := ⟨K', hK', rfl⟩
    obtain ⟨n, hn⟩ := exists_suzukiModel_of_mem_thetaComponentsIn h.toTheoremFourHyp hFtop hF3 hK
    have h2 : 2 ∣ Nat.card (K'.map F.subtype) :=
      (Proof1619.isPerfect_and_two_dvd_of_suzukiModel hn).2.trans
        (Subgroup.card_quotient_dvd_card _)
    exact h2.trans (Subgroup.card_dvd_of_le (le_sSup hK))
  obtain ⟨T, hTA, hT1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two A E hA.isPGroup hAE hE3 hE2
  set T' := (T : Subgroup E).map E.subtype with hT'
  have hT'syl : CFSG.ABGLocalTools.IsSylowOf 2 T' E := ⟨T, rfl⟩
  have hT'E : T' ≤ E := Subgroup.map_subtype_le _
  have hT'Q : T' ∈ scriptQ A (lB A) := mem_scriptQ_of_le hEQ hT'E hTA
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map _
  have hNT : delta A (lB A) (Subgroup.normalizer (T' : Set G)) ≤ M :=
    hY3 _ (Proof17Res12.delta_normalizer_mem_scriptY3 h hT'Q hT'2 hT1 hT'E
      (Proof17Res12.ne_top_of_not_three_dvd h
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hE3)))
  have hAN : A ≤ Subgroup.normalizer
      ((Subgroup.normalizer (T' : Set G) : Subgroup G) : Set G) :=
    hTA.trans Subgroup.le_normalizer
  have key : delta A (lB A) D ≤ M := by
    refine sSup_le fun Q hQ => ?_
    have hQE : Q ≤ Subgroup.normalizer (E : Set G) := hQ.2.trans hDE
    have hHinv : Q ⊔ E ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
      ⟨le_top, isPiSubgroup_piCompl_sup hQ.1.1.2.1 hEQ.1.2.1 hQE,
        Sec14.le_normalizer_sup hQ.1.1.2.2 hAE⟩
    have hHQ : Q ⊔ E ∈ scriptQ A (lB A) := by
      have := delta_mem_scriptQ hA h146 hHinv
      rwa [le_antisymm (delta_le _)
        (sup_le (le_delta hQ.1 le_sup_left) (le_delta hEQ le_sup_right))] at this
    have hfr := Proof17Res12.le_sup_inf_normalizer (H := Q ⊔ E) le_sup_right
      (sup_le hQE Subgroup.le_normalizer) hT'syl
    have hHNT : (Q ⊔ E) ⊓ Subgroup.normalizer (T' : Set G) ≤
        delta A (lB A) (Subgroup.normalizer (T' : Set G)) :=
      le_delta (mem_scriptQ_of_le hHQ inf_le_left (Late.le_normalizer_inf hHQ.1.2.2 hAN))
        inf_le_right
    exact (le_sup_left.trans hfr).trans (sup_le hEM (hHNT.trans hNT))
  calc D = delta A (lB A) D := hDΔ
    _ ≤ M := key

end Certified

end Proof17Res14

open Proof17Res14 in
theorem step174KbO_of_three (h146 : Item146S14) (h3 : Step174KbOThree) : Step174KbO := by
  intro G _ _ A c L Y₀ h X hXΔ hX3 K hK hSz hθ hcen hAK hY3 b hb hb1 hO2
  by_cases hD3 : 3 ∣ Nat.card (delta A (lB A) (Subgroup.centralizer ({b} : Set G)))
  · exact h3 G A c L Y₀ h X hXΔ hX3 K hK hSz hθ hcen hAK hY3 b hb hb1 hO2 hD3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hJD⟩ :=
    perfectResidual_mem_scriptQ h (h146 G A c L h.toSec14Std) hXΔ hX3 hK hAK hb.1
  exact hJD.trans (le_pPrimeCoreOf le_rfl Subgroup.le_normalizer
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD3))

section Certified

open Proof17Res14 in
theorem step174KbM_of_O (h166 : Item166S17) (h146 : Item146S14) (hO : Step174KbO) :
    Step174KbM := by
  intro G _ _ A c L Y₀ h X hXΔ hX3 K hK hSz hθ hcen hAK hY3 b hb hb1 hO2
  have hJO := hO G A c L Y₀ h X hXΔ hX3 K hK hSz hθ hcen hAK hY3 b hb hb1 hO2
  obtain ⟨n, hn⟩ := hSz
  set D := delta A (lB A) (Subgroup.centralizer ({b} : Set G)) with hD
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set J := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) with hJdef
  have h146' := h146 G A c L h.toSec14Std
  obtain ⟨hJQ, -⟩ := perfectResidual_mem_scriptQ h h146' hXΔ hX3 hK hAK hb.1
  have hb3 : orderOf b = 3 := orderOf_eq_prime (pow_three_of_std h hb.1) hb1
  have hJs := not_isSolvable_perfectResidual hcen hθ hn (h.le_y0 hb.2) (hAK hb.1) hb3
  have hDM : D ≤ M := le_M_of_le_pPrimeCoreOf h (h166 G A c L Y₀ h) h146' hY3
    (Sec14.le_normalizer_delta _) (delta_delta _).symm hJQ hJO hJs
  have hJK : J ≤ K := (Subgroup.map_subtype_le _).trans inf_le_left
  have hJM : J ≤ M := fun x hx => (hcen (hJK hx)).1
  refine ⟨hJO, fun d hd => ?_⟩
  rintro _ ⟨j, hj, rfl⟩
  exact M.mul_mem (M.mul_mem (hDM hd) (hJM hj)) (M.inv_mem (hDM hd))

end Certified

end CFSG.RankThree.PartTwo.Sec17

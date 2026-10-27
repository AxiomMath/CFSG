module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step142DeltaS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) ∧
        Q = k142 A (lB A) c ∧
        Nat.card (k142 A (lB A) c) =
          2 * Nat.card (pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) ∨
      (L ≤ k142 A (lB A) c ∧
        k142 A (lB A) c ≤ L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))

@[expose] noncomputable def Step142LowerS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) ∧
        (∀ V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
          (piCompl 3), V ≤ Q) ∧
        Nat.card Q =
          2 * Nat.card (pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) ∨
      L ≤ sSup (invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3))

@[expose] noncomputable def Step142UpperPGLS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → A ≠ Subgroup.zpowers c ⊔ (A ⊓ L) →
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) ∧
        (∀ V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
          (piCompl 3), V ≤ Q) ∧
        Nat.card Q =
          2 * Nat.card (pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) ∨
      ∀ V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
          (piCompl 3),
        V ≤ L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))

@[expose] noncomputable def Step142TypesS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec14Std G A c L),
    letI := ker142_normal (LB := lB A) h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
        (((IsLThreePi ↥(img142 A (lB A) c L) ∨
              Nonempty (↥(img142 A (lB A) c L) ≃*
                alternatingGroup (Fin 7)) ∨
              Nonempty (↥(img142 A (lB A) c L) ≃*
                CFSG.Blueprint.NativeSporadic.M12)) ∧
            ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
              img142 A (lB A) c Q =
                thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c) ∨
          (Nonempty (↥(img142 A (lB A) c L) ≃*
              CFSG.Blueprint.NativeSporadic.M22) ∧
            (CFSG.Assembly.IsElemAbelian 2 (img142 A (lB A) c Q) ∧
              Nat.card (img142 A (lB A) c Q) = 16) ∧
            ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
              Subgroup.closure {alpha142 A (lB A) c a ha, alpha142 A (lB A) c b hb} =
                img142 A (lB A) c A ∧
              img142 A (lB A) c Q =
                thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔
                  thetaC142 A (lB A) c (alpha142 A (lB A) c b hb) ∧
              thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊓
                  thetaC142 A (lB A) c (alpha142 A (lB A) c b hb) = ⊥) ∨
          (Nonempty (↥(img142 A (lB A) c L) ≃*
              CFSG.Blueprint.NativeSporadic.J2) ∧
            (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
              Nonempty (↥(img142 A (lB A) c Q) ≃*
                ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
            ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) (d : G) (hd : d ∈ A),
              Subgroup.closure {alpha142 A (lB A) c a ha, alpha142 A (lB A) c b hb} =
                img142 A (lB A) c A ∧
              alpha142 A (lB A) c d hd ≠ 1 ∧
              IsThreeCentralIn (img142 A (lB A) c L) (alpha142 A (lB A) c d hd) ∧
              Subgroup.zpowers (alpha142 A (lB A) c a ha) ≠
                Subgroup.zpowers (alpha142 A (lB A) c d hd) ∧
              Subgroup.zpowers (alpha142 A (lB A) c b hb) ≠
                Subgroup.zpowers (alpha142 A (lB A) c d hd) ∧
              img142 A (lB A) c Q =
                thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔
                    thetaC142 A (lB A) c (alpha142 A (lB A) c b hb) ⊔
                  (img142 A (lB A) c Q ⊓
                    Subgroup.centralizer {alpha142 A (lB A) c d hd})))

namespace Item148Point

variable {G : Type} [Group G] [Finite G]

theorem le_k142_of_concl142 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h142 : Concl142 A LB) {c : G} (hcΩ : Subgroup.zpowers c ∈ omegaA A) {V : Subgroup G}
    (hV : V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) :
    V ≤ k142 A LB c := by
  obtain ⟨Qs, hQs, hVQs⟩ := exists_le_mem_maxInvariantPiSubgroups hV
  exact le_delta (mem_scriptQ_of_le (h142 c hcΩ Qs hQs).1 hVQs hV.2.2) hV.1

theorem pPrimeCoreOf_sup_le_k142 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h142 : Concl142 A LB) {c : G} (hcΩ : Subgroup.zpowers c ∈ omegaA A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ k142 A LB c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hcΩ).1
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ H := centralizer_singleton_le_normalizer_zpowers c
  have hAC : A ≤ Subgroup.centralizer (A : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAab y hy x hx
  have hAH : A ≤ H := fun x hx =>
    hCH (Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx c hcA))
  have hCAH : Subgroup.centralizer (A : Set G) ≤ H :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)).trans hCH
  have hπ : ∀ X : Subgroup G, IsPiSubgroup (piCompl 3) (pPrimeCoreOf 3 X) := fun X =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X))
  refine sup_le (le_k142_of_concl142 h142 hcΩ ⟨pPrimeCoreOf_le 3 H, hπ H,
    hAH.trans (le_normalizer_pPrimeCoreOf 3 H)⟩) (le_k142_of_concl142 h142 hcΩ
    ⟨(pPrimeCoreOf_le 3 _).trans hCAH, hπ _, hAC.trans (le_normalizer_pPrimeCoreOf 3 _)⟩)

omit [Finite G] in
theorem k142_le_of_forall {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    {M : Subgroup G}
    (hM : ∀ V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), V ≤ M) :
    k142 A LB c ≤ M :=
  sSup_le fun Q hQ => hM Q ⟨hQ.2, hQ.1.1.2.1, hQ.1.1.2.2⟩

theorem sSup_le_k142_of_concl142 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h142 : Concl142 A LB) {c : G} (hcΩ : Subgroup.zpowers c ∈ omegaA A) :
    sSup (invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) ≤ k142 A LB c :=
  sSup_le fun _ hV => le_k142_of_concl142 h142 hcΩ hV

theorem le_sup_of_eq_zpowers_sup142 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) {V : Subgroup G}
    (hV : V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) :
    V ≤ L ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  have hD := h.toSec13Data
  have hcA : c ∈ A := hD.mem_A
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact (zpowers_mem_omegaA_iff.mp hD.zpowers_mem_omegaA).2.1
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hD.mem_lA.1
  have h3 : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h h3
  have hVc : V ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_invariantPiSubgroups hcA hc3 hV
  have hV3 : ¬ 3 ∣ Nat.card V := (isPiSubgroup_piCompl_iff Nat.prime_three V).mp hV.2.1
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hD.isElemAbelian.2 a a.2)⟩
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
    Nat.prime_three A V hA3 hV3 hV.2.2]
  exact sup_le ((commutator_le_of_eq_zpowers_sup hAc hcA hAab hLc hVc (hVc.trans hCL)).trans
    le_sup_left) ((inf_centralizer_le_xA (Sec14Std.maximal_isElemAbelian h) hV3).trans
    le_sup_right)

end Item148Point

theorem item142AllS14_of_delta (h1 : Concl142S14) (h2 : Step142DeltaS14)
    (h3 : Step142TypesS14) : Item142AllS14 := by
  intro G _ _ A c L h
  have hc := h.toSec13Data.zpowers_mem_omegaA
  have h142 := h1 G A c L h
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => h.toSec13Data.commute hx hy
  have hle := Item148Point.pPrimeCoreOf_sup_le_k142 h142 hc hAab
  intro Q hQ
  refine ⟨h142 c hc Q hQ, ?_⟩
  rcases h2 G A c L h Q hQ with ⟨hiso, hQK, hcard⟩ | ⟨hLK, hKle⟩
  · exact Or.inl ⟨hiso, hQK, le_sup_left.trans hle, hcard⟩
  · have hKeq : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer
        (Subgroup.zpowers c : Set G)) ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
      le_antisymm hKle (sup_le (sup_le hLK (le_sup_left.trans hle)) (le_sup_right.trans hle))
    exact Or.inr ⟨hKeq, h3 G A c L h Q hQ hKeq⟩

theorem step142DeltaS14_of (h1 : Concl142S14) (hLow : Step142LowerS14)
    (hUp : Step142UpperPGLS14) : Step142DeltaS14 := by
  intro G _ _ A c L h Q hQ
  have hc := h.toSec13Data.zpowers_mem_omegaA
  have h142 := h1 G A c L h
  have hQK : Q ≤ k142 A (lB A) c := Item148Point.le_k142_of_concl142 h142 hc hQ.prop
  have hexc : ∀ (_ : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
      (_ : ∀ V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3), V ≤ Q)
      (_ : Nat.card Q =
        2 * Nat.card (pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))),
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) ∧
        Q = k142 A (lB A) c ∧
        Nat.card (k142 A (lB A) c) =
          2 * Nat.card (pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))) := by
    intro hiso hall hcard
    have hKQ : Q = k142 A (lB A) c := le_antisymm hQK (Item148Point.k142_le_of_forall hall)
    exact ⟨hiso, hKQ, hKQ ▸ hcard⟩
  rcases hLow G A c L h Q hQ with ⟨hiso, hall, hcard⟩ | hL
  · exact Or.inl (hexc hiso hall hcard)
  · have hLK : L ≤ k142 A (lB A) c := hL.trans (Item148Point.sSup_le_k142_of_concl142 h142 hc)
    by_cases hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)
    · refine Or.inr ⟨hLK, Item148Point.k142_le_of_forall fun V hV => ?_⟩
      exact (Item148Point.le_sup_of_eq_zpowers_sup142 h hAc hV).trans
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    · rcases hUp G A c L h hAc Q hQ with ⟨hiso, hall, hcard⟩ | hall
      · exact Or.inl (hexc hiso hall hcard)
      · exact Or.inr ⟨hLK, Item148Point.k142_le_of_forall hall⟩

theorem item142AllS14_of (h1 : Concl142S14) (hLow : Step142LowerS14)
    (hUp : Step142UpperPGLS14) (h3 : Step142TypesS14) : Item142AllS14 :=
  item142AllS14_of_delta h1 (step142DeltaS14_of h1 hLow hUp) h3

end CFSG.RankThree.PartTwo.Sec14

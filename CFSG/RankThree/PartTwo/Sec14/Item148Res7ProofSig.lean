module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeC
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
import CFSG.RankThree.PartTwo.Sec14.Item148PointProofPGL
import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofAlpha

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

structure Sig148 {Γ : Type} [Group Γ] [Finite Γ] (A L K : Subgroup Γ) (e : Γ) : Prop where
  isE27 : Late.IsE27 A
  mem : e ∈ A
  ne_one : e ≠ 1
  le_centralizer : L ≤ Subgroup.centralizer ({e} : Set Γ)
  le_normalizer_L : A ≤ Subgroup.normalizer (L : Set Γ)
  le : K ≤ L
  le_normalizer_K : A ≤ Subgroup.normalizer (K : Set Γ)
  isPerfect : Group.IsPerfect ↥K
  isQuasisimple : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K)
  le_iSup : K ≤ ⨆ (x : Γ) (_ : x ∈ A) (_ : x ∉ Subgroup.zpowers e),
    pPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ))

namespace Res7Sig

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_iSup148 {ι : Sort*} {X : Subgroup G} {S : ι → Subgroup G}
    (h : ∀ i, X ≤ Subgroup.normalizer (S i : Set G)) :
    X ≤ Subgroup.normalizer ((⨆ i, S i : Subgroup G) : Set G) := by
  have key : ∀ g ∈ X, ∀ c ∈ ⨆ i, S i, g * c * g⁻¹ ∈ ⨆ i, S i := by
    intro g hg c hc
    have hle : (⨆ i, S i) ≤ (⨆ i, S i).comap (MulAut.conj g).toMonoidHom := by
      refine iSup_le fun i => ?_
      intro d hd
      rw [Subgroup.mem_comap]
      exact le_iSup S i ((Subgroup.mem_normalizer_iff.mp (h i hg) d).mp hd)
    exact hle hc
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this

theorem mem_centralizer_of_hyperplane148 {A H : Subgroup G} {e q : G} (hA : Late.IsE27 A)
    (hH : IsHyperplane A H) (heA : e ∈ A) (heH : e ∉ H)
    (hqH : q ∈ Subgroup.centralizer (H : Set G)) (hqe : q ∈ Subgroup.centralizer ({e} : Set G)) :
    q ∈ Subgroup.centralizer (A : Set G) := by
  have hAeq : A = H ⊔ Subgroup.zpowers e :=
    eq_sup_of_not_le hA hH (Subgroup.zpowers_le.mpr heA)
      fun h => heH (h (Subgroup.mem_zpowers e))
  have hqe' : q ∈ Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    rw [centralizer_zpowers148]
    exact hqe
  have h1 : H ⊔ Subgroup.zpowers e ≤
      Subgroup.centralizer ((Subgroup.zpowers q : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hqH))
      (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hqe'))
  have h2 := Subgroup.le_centralizer_iff.mp h1
  rw [hAeq]
  exact h2 (Subgroup.mem_zpowers q)

theorem le_iSup_pPrimeCoreOf148 {A Y K : Subgroup G} {e : G} (hA : Late.IsE27 A)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') (heA : e ∈ A)
    (he1 : e ≠ 1) (hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G))
    (hKΔ : K = deltaZero A (lB A) K) :
    K ≤ ⨆ (x : G) (_ : x ∈ A) (_ : x ∉ Subgroup.zpowers e),
      pPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
  set R : Subgroup G := ⨆ (x : G) (_ : x ∈ A) (_ : x ∉ Subgroup.zpowers e),
    pPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) with hRdef
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.1.2 g g.2)⟩
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_eq_deltaZero hKΔ
  have hAC : ∀ x ∈ A, A ≤ Subgroup.centralizer ({x} : Set G) := fun x hx a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha x hx)
  have hKY' : K ≤ Y := hKY.trans inf_le_left
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := hKY.trans inf_le_right
  have he3 : Nat.card (Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA.1.2 e heA) he1
  have hRle : ∀ x ∈ A, x ∉ Subgroup.zpowers e →
      pPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) ≤ R := fun x hx hxe =>
    le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hxe le_rfl))
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    refine le_normalizer_iSup148 fun x => le_normalizer_iSup148 fun hx =>
      le_normalizer_iSup148 fun _ => ?_
    intro a ha
    exact normalizer_le_normalizer_pPrimeCoreOf 3 _
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hAK ha, Subgroup.le_normalizer (hAC x hx ha)⟩)
  calc K = deltaZero A (lB A) K := hKΔ
    _ ≤ R := by
      refine sSup_le fun Q hQ => ?_
      obtain ⟨⟨hQs, hQA⟩, hQK⟩ := hQ
      have hQ3 : ¬ 3 ∣ Nat.card Q := fun h => (hQs.1.2.1 ⟨3, Nat.prime_three⟩ h) rfl
      have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQs.1.2.2
      have hcop : Nat.Coprime 3 (Nat.card Q) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3
      set C₀ := Q ⊓ Subgroup.centralizer (A : Set G) with hC₀def
      have hC₀A : C₀ ≤ Subgroup.centralizer (A : Set G) := inf_le_right
      have hC₀R : C₀ ≤ Subgroup.normalizer (R : Set G) := by
        refine le_normalizer_iSup148 fun x => le_normalizer_iSup148 fun hx =>
          le_normalizer_iSup148 fun _ => ?_
        have h1 : C₀ ≤ K ⊓ Subgroup.centralizer ({x} : Set G) :=
          le_inf (inf_le_left.trans hQK)
            (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx)))
        exact h1.trans (le_normalizer_pPrimeCoreOf 3 _)
      have hQRC : Q ≤ R ⊔ C₀ := by
        have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes
          Nat.prime_three (A := A) (X := Q) ⟨hA.1.1, hA.1.2⟩ (by rw [hA.2]; norm_num) hAQ hcop
        refine (le_of_eq hgen.symm).trans (iSup₂_le fun H hH => ?_)
        have hHyp : IsHyperplane A H := hH
        have hAH : A ≤ Subgroup.centralizer (H : Set G) := fun a ha =>
          Subgroup.mem_centralizer_iff.mpr fun h hh => (hcomm h (hHyp.1 hh) a ha)
        by_cases heH : e ∈ H
        · obtain ⟨x, hxH, hxe, hHcl⟩ := exists_closure_pair_of_mem hA hHyp heH he3
          set QH := Q ⊓ Subgroup.centralizer (H : Set G) with hQHdef
          have hAQH : A ≤ Subgroup.normalizer (QH : Set G) := fun a ha =>
            Subgroup.inf_normalizer_le_normalizer_inf ⟨hAQ ha, Subgroup.le_normalizer (hAH ha)⟩
          have hQH3 : ¬ 3 ∣ Nat.card QH := fun h =>
            hQ3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
          have hcommR : ⁅QH, A⁆ ≤ R := by
            set Q₁ := ⁅QH, A⁆ with hQ₁def
            have hQ₁QH : Q₁ ≤ QH := Subgroup.le_normalizer_iff_commutator_le_left.mp hAQH
            have hAQ₁ : A ≤ Subgroup.normalizer (Q₁ : Set G) :=
              Subgroup.normalizer_commutator_ge_right QH A
            have hQ₁0 : Q₁ ∈ scriptQZero A (lB A) :=
              ⟨mem_scriptQ_of_le hQs (hQ₁QH.trans inf_le_left) hAQ₁,
                (CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
                  Nat.prime_three A QH hAp hQH3 hAQH).symm⟩
            have hQ₁Y : Q₁ ≤ Y ⊓ Subgroup.centralizer (H : Set G) :=
              le_inf (hQ₁QH.trans (inf_le_left.trans (hQK.trans hKY')))
                (hQ₁QH.trans inf_le_right)
            have hQ₁O : Q₁ ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (H : Set G)) :=
              (le_deltaZero hQ₁0 hQ₁Y).trans (hYB H hHyp)
            have hCxH : K ⊓ Subgroup.centralizer ({x} : Set G) ≤
                Subgroup.centralizer (H : Set G) := by
              intro g hg
              rw [hHcl, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
              rintro h (rfl | rfl)
              · exact (Subgroup.mem_centralizer_singleton_iff.mp (hKe hg.1)).symm
              · exact (Subgroup.mem_centralizer_singleton_iff.mp hg.2).symm
            have hHx : Subgroup.centralizer (H : Set G) ≤
                Subgroup.centralizer ({x} : Set G) :=
              Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxH)
            set N₁ := pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (H : Set G)) ⊓
              (K ⊓ Subgroup.centralizer ({x} : Set G)) with hN₁def
            have hQ₁N₁ : Q₁ ≤ N₁ :=
              le_inf hQ₁O (le_inf (hQ₁QH.trans (inf_le_left.trans hQK))
                (hQ₁QH.trans (inf_le_right.trans hHx)))
            have hN₁ : N₁ ≤ pPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
              refine le_pPrimeCoreOf inf_le_right ?_ ?_
              · intro g hg
                refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer hg⟩
                exact le_normalizer_pPrimeCoreOf 3 _
                  (Subgroup.mem_inf.mpr ⟨hKY' hg.1, hCxH hg⟩)
              · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
                  (coprime_card_pPrimeCoreOf 3 _)
            exact hQ₁N₁.trans (hN₁.trans (hRle x (hHyp.1 hxH) hxe))
          intro q hq
          obtain ⟨f, hf, t, ht, hft⟩ :=
            CFSG.LargeEvenClassification.Helpers.coprime_normalized_fixed_decomposition
              Nat.prime_three A QH hAp hQH3 hAQH ⟨q, hq⟩
          have hq' : q = (f : G) * (t : G) := by rw [← Subgroup.coe_mul, hft]
          rw [hq']
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨f.2.1, hf⟩))
            (Subgroup.mem_sup_left (hcommR ht))
        · intro q hq
          exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hq.1,
            mem_centralizer_of_hyperplane148 hA hHyp heA heH hq.2 (hKe (hQK hq.1))⟩)
      calc Q = ⁅Q, A⁆ := hQA
        _ ≤ ⁅R ⊔ C₀, A⁆ := Subgroup.commutator_mono hQRC le_rfl
        _ ≤ R := commutator_sup_le148 hAR hC₀R hC₀A

omit [Finite G] in
theorem ne_bot_of_isQuasisimple148 {K : Subgroup G}
    (hK : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K)) : K ≠ ⊥ := by
  have : Nontrivial (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hK
  rintro rfl
  obtain ⟨u, v, huv⟩ :=
    exists_pair_ne (↥(⊥ : Subgroup G) ⧸ aschbacherSolvableCore 3 ↥(⊥ : Subgroup G))
  apply huv
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  rw [Subsingleton.elim u' v']

theorem sig148_of_isPoint148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G}
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B Q K Le : Subgroup G} {e : G} (hP : IsPoint148 A (lB A) Y B Q e K Le) :
    Sig148 A Le K e := by
  obtain ⟨hB, -, -, heB, he1, hK, hKΔ, hKLe, hLe, -⟩ := hP
  have hKY := le_of_mem_thetaComponentsIn hK
  have heA : e ∈ A := hB.1 heB
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha heA)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_eq_deltaZero hKΔ
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hKp := isPerfect_of_mem_thetaComponentsIn hK
  exact
    { isE27 := h.isE27'
      mem := heA
      ne_one := he1
      le_centralizer := le_centralizer_of_mem_thetaComponentsAt hLe
      le_normalizer_L := Item148Point.le_normalizer_of_perfect_le148 hAe hLe hKLe hAK hKp
        (ne_bot_of_isQuasisimple148 hKq)
      le := hKLe
      le_normalizer_K := hAK
      isPerfect := hKp
      isQuasisimple := hKq
      le_iSup := le_iSup_pPrimeCoreOf148 h.isE27' hYB heA he1 hKY hKΔ }

end Res7Sig

@[expose] def KF148SigHJ : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L K : Subgroup Γ) (e : Γ), Sig148 A L K e →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers e : Set Γ) →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* CFSG.Blueprint.NativeSporadic.J2)

@[expose] def KF148SigL3 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L K : Subgroup Γ) (e : Γ), Sig148 A L K e →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers e : Set Γ) →
    IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    (∃ (X' : Type) (_ : Group X') (_ : Finite X'), Sec4.IsList46 X' ∧
      Nonempty (X' ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L)) →
    KThetaC148 K L

@[expose] def KF148SigA7 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L K : Subgroup Γ) (e : Γ), Sig148 A L K e →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers e : Set Γ) →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* alternatingGroup (Fin 7))

@[expose] def KF148SigM22 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L K : Subgroup Γ) (e : Γ), Sig148 A L K e →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers e : Set Γ) →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
    Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* alternatingGroup (Fin 7))

@[expose] def KF148SigM12 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L K : Subgroup Γ) (e : Γ), Sig148 A L K e →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers e : Set Γ) →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) →
    Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* CFSG.Blueprint.NativeSporadic.M12)

@[expose] def KF148SigON : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L K : Subgroup Γ) (e : Γ), Sig148 A L K e →
    Sec4.IsTripleCover (↥L ⧸ aschbacherSolvableCore 3 ↥L) CFSG.Blueprint.NativeSporadic.ON →
    Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 7)) ∨
      (∃ _ : Fact (Nat.Prime 7), Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))

@[expose] def Step148KThetaONCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → c' ∈ B →
        L' ∈ lA A c' →
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) →
        IsThreeCentralIn L' e →
        Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON →
        Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 7)) ∨
          (∃ _ : Fact (Nat.Prime 7), Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))

theorem step148KThetaHJ_of_sig (hKF : KF148SigHJ) : Step148KThetaHJ := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP he hLe hJ2
  obtain ⟨φ⟩ := hKF G A Le K e (Res7Sig.sig148_of_isPoint148 h hYB hP) hLe.2.2.1 hJ2
  obtain ⟨ψ⟩ := hJ2
  exact Or.inl ⟨φ.trans ψ.symm⟩

theorem step148KThetaL3_of_sig (h46 : Sec4.Item4_6) (hKF : KF148SigL3) : Step148KThetaL3 := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP he hLe hL3
  have hD : Sec13Data G A e Le := { h.toSec13Data with zpowers_mem_omegaA := he, mem_lA := hLe }
  exact hKF G A Le K e (Res7Sig.sig148_of_isPoint148 h hYB hP) hLe.2.2.1 hL3
    (Sec13.Res4Proof.exists_isList46 h46 hD)

theorem step148KThetaA7_of_sig (hKF : KF148SigA7) : Step148KThetaA7 := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP he hLe hA7
  obtain ⟨φ⟩ := hKF G A Le K e (Res7Sig.sig148_of_isPoint148 h hYB hP) hLe.2.2.1 hA7
  obtain ⟨ψ⟩ := hA7
  exact Or.inl ⟨φ.trans ψ.symm⟩

theorem step148KThetaM22_of_sig (hKF : KF148SigM22) : Step148KThetaM22 := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP he hLe hM22
  rcases hKF G A Le K e (Res7Sig.sig148_of_isPoint148 h hYB hP) hLe.2.2.1 hM22 with
    ⟨⟨φ⟩⟩ | hA7
  · obtain ⟨ψ⟩ := hM22
    exact Or.inl ⟨φ.trans ψ.symm⟩
  · exact Or.inr (Or.inl ⟨Or.inl hM22, hA7⟩)

theorem step148KThetaM12_of_sig (hKF : KF148SigM12) : Step148KThetaM12 := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP he hLe hM12
  obtain ⟨φ⟩ := hKF G A Le K e (Res7Sig.sig148_of_isPoint148 h hYB hP) hLe.2.2.1 hM12
  obtain ⟨ψ⟩ := hM12
  exact Or.inl ⟨φ.trans ψ.symm⟩

theorem step148KThetaONCover_of_sig (hKF : KF148SigON) : Step148KThetaONCover := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP c' L' hc' hc'B hL' hJ2 hd hON3
  exact hKF G A Le K e (Res7Sig.sig148_of_isPoint148 h hYB hP) hON3

theorem step148KType_of_sig
    (hθ : Step148KTheta) (h46 : Sec4.Item4_6)
    (hHJ : KF148SigHJ) (hL3 : KF148SigL3) (hA7 : KF148SigA7) (hM22 : KF148SigM22)
    (hM12 : KF148SigM12) (hON : Step148KThetaON) : Step148KType :=
  step148KType_of_theta_types hθ (step148KThetaHJ_of_sig hHJ) (step148KThetaL3_of_sig h46 hL3)
    (step148KThetaA7_of_sig hA7) (step148KThetaM22_of_sig hM22) (step148KThetaM12_of_sig hM12)
    hON

end CFSG.RankThree.PartTwo.Sec14

module

public import CFSG.RankThree.PartTwo.Sec19.Step1917StepsPush
public import CFSG.RankThree.PartTwo.Sec19.Step1915Proof
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith
import CFSG.RankThree.PartTwo.Sec19.Step1917StepsOrders
import CFSG.RankThree.PartTwo.Sec19.Step1917StepsBasic
import CFSG.RankThree.PartTwo.Sec19.Step1917ProofTools
import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2Tools
import CFSG.RankThree.PartTwo.Sec19.Step1918ProofTools
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartTwo.Late.Item2010
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.Fitting.CharacteristicP
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def Step1917EqCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → L ≤ M → ∀ d ∈ A ⊓ E, d ∉ Subgroup.zpowers c →
      ¬ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ M →
      ∀ H ∈ scriptM (Subgroup.normalizer (Subgroup.zpowers d : Set G) : Set G), H ≠ M →
      ∀ K ∈ oTwoComponentsIn M, L ≤ K → K = L ⊔ CFSG.Open.pCoreOf 2 K → K ≤ H →
      ∀ X ∈ oTwoComponentsIn H, L ≤ X → K ≤ X → c ∈ Subgroup.normalizer (X : Set G) →
        ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X

namespace Step1917EqProof

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_normalizer {K X L : Subgroup G}
    (hKq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)) (hKp : Group.IsPerfect K)
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) (hLK : L ≤ K) (hLX : L ≤ X)
    (hLp : Group.IsPerfect L) (hL1 : L ≠ ⊥) : K ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup K := X.subgroupOf K with hNdef
  have hNn : N.Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hKX k.2) n).mp hn⟩
  set f := QuotientGroup.mk' (CFSG.pCore 2 K) with hf
  have hN'n : (N.map f).Normal := hNn.map f (QuotientGroup.mk'_surjective _)
  set L' : Subgroup K := L.subgroupOf K with hL'
  have hL'N : L' ≤ N := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hLX (Subgroup.mem_subgroupOf.mp hx))
  have hL'p : Group.IsPerfect L' := by
    have := hLp
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hLK).symm.toMonoidHom) (MulEquiv.surjective _)
  have hL'nt : Nontrivial L' := by
    have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL1
    exact (Subgroup.subgroupOfEquivOfLe hLK).toEquiv.nontrivial
  have htop : N.map f = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hN'n with h | h
    · exact h
    · exfalso
      have hcen : L'.map f ≤ Subgroup.center (K ⧸ CFSG.pCore 2 K) :=
        (Subgroup.map_mono hL'N).trans h
      have hperf : Group.IsPerfect (L'.map f) :=
        Group.IsPerfect.ofSurjective (f := f.subgroupMap L') (f.subgroupMap_surjective L')
      have hcomm : IsMulCommutative (L'.map f) :=
        ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp (hcen a.2) b).symm)⟩⟩
      have hsub : Subsingleton (L'.map f) := Group.IsPerfect.subsingleton_of_isMulCommutative
      have hL'le : L' ≤ CFSG.pCore 2 K := by
        intro x hx
        have h1 : (⟨f x, Subgroup.mem_map_of_mem f hx⟩ : L'.map f) = 1 := Subsingleton.elim _ _
        have h2 : f x = 1 := congrArg Subtype.val h1
        rwa [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have h2 : IsPGroup 2 L' := (CFSG.pCore_isPGroup (p := 2) (G := K)).to_le hL'le
      have : Group.IsSolvable L' := by
        have := h2.isNilpotent
        infer_instance
      exact Group.IsPerfect.not_isSolvable L' this
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' N).comp (CFSG.pCore 2 K).subtype) := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hk : f k ∈ N.map f := htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnk⟩ := hk
    refine ⟨⟨n⁻¹ * k, ?_⟩, ?_⟩
    · have := QuotientGroup.eq.mp hnk
      exact this
    · change ((n⁻¹ * k : K) : K ⧸ N) = (k : K ⧸ N)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n⁻¹).mpr (N.inv_mem hn), one_mul]
  have h2 : IsPGroup 2 (K ⧸ N) :=
    (CFSG.pCore_isPGroup (p := 2) (G := K)).of_surjective _ hsurj
  have : Group.IsPerfect K := hKp
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    have : Group.IsSolvable (K ⧸ N) := by
      have := h2.isNilpotent
      infer_instance
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) this
  intro x hx
  have h1 : ((⟨x, hx⟩ : K) : K ⧸ N) = 1 := Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

@[expose] noncomputable def psiX {K X : Subgroup G} (hKX : K ≤ X) : K →* X ⧸ CFSG.pCore 2 X :=
  (QuotientGroup.mk' (CFSG.pCore 2 X)).comp (Subgroup.inclusion hKX)

omit [Finite G] in
theorem ker_psiX_le {K X : Subgroup G} (hKX : K ≤ X) : (psiX hKX).ker ≤ CFSG.pCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (psiX hKX).ker := by
    intro x
    have hx : Subgroup.inclusion hKX (x : K) ∈ CFSG.pCore 2 X := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) (Subgroup.inclusion hKX (x : K)) = 1 :=
        MonoidHom.mem_ker.mp x.2
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := X) ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : CFSG.pCore 2 X => ((y : X) : G)) hk
    simpa using this
  exact le_sSup ⟨inferInstance, h2⟩

theorem card_dvd_card_range {K X : Subgroup G} (hKX : K ≤ X) :
    Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card (psiX hKX).range := by
  set ψ := psiX hKX
  have h1 : Nat.card K = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have h2 : Nat.card K = Nat.card (K ⧸ CFSG.pCore 2 K) * Nat.card (CFSG.pCore 2 K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le (ker_psiX_le hKX)
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  refine ⟨t, ?_⟩
  have : Nat.card ψ.range * Nat.card ψ.ker =
      Nat.card (K ⧸ CFSG.pCore 2 K) * t * Nat.card ψ.ker := by
    rw [← h1, h2, ht]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem card_dvd_of_le {K X : Subgroup G} (hKX : K ≤ X) :
    Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card (X ⧸ CFSG.pCore 2 X) :=
  (card_dvd_card_range hKX).trans (Subgroup.card_subgroup_dvd_card _)

theorem eq_sup_of_card_eq {K X : Subgroup G} (hKX : K ≤ X)
    (hcard : Nat.card (X ⧸ CFSG.pCore 2 X) = Nat.card (K ⧸ CFSG.pCore 2 K)) :
    X = K ⊔ CFSG.Open.pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := psiX hKX
  have hr : ψ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card _)
      (hcard ▸ card_dvd_card_range hKX)
  apply le_antisymm
  · intro x hx
    have hq : (QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hx⟩) ∈ ψ.range := hr ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := hq
    have h1 : (Subgroup.inclusion hKX k)⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 X := QuotientGroup.eq.mp hk
    have h2 : (((Subgroup.inclusion hKX k)⁻¹ * ⟨x, hx⟩ : X) : G) ∈ CFSG.Open.pCoreOf 2 X :=
      (Sec18.mem_pCore_iff_mem_pCoreOf _).mp h1
    have e : x = (k : G) * (((Subgroup.inclusion hKX k)⁻¹ * ⟨x, hx⟩ : X) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup k.2 h2
  · exact sup_le hKX (CFSG.LieType.BorelTits.pCoreOf_le 2 X)

theorem eq_of_le_M
    (h1913 : Step1913) {A L E M H K X : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K) (hKH : K ≤ H) (hX : X ∈ oTwoComponentsIn H)
    (hLX : L ≤ X) (hXM : X ≤ M) : K = X := by
  have hKMH : K ∈ oTwoComponentsIn (M ⊓ H) := by
    obtain ⟨hKM, -, hKsn, -⟩ := mem_oTwoComponentsIn_iff.mp hK
    exact Sec18.mem_oTwoComponentsIn_of_quasisimple (le_inf hKM hKH)
      (Sec18.isSubnormal_subgroupOf_of_le hKsn inf_le_left)
      (Sec18.commutator_eq_of_mem_oTwoComponentsIn hK)
      (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK)
  have hXMH : X ∈ oTwoComponentsIn (M ⊓ H) := by
    obtain ⟨hXH, -, hXsn, -⟩ := mem_oTwoComponentsIn_iff.mp hX
    exact Sec18.mem_oTwoComponentsIn_of_quasisimple (le_inf hXM hXH)
      (Sec18.isSubnormal_subgroupOf_of_le hXsn inf_le_right)
      (Sec18.commutator_eq_of_mem_oTwoComponentsIn hX)
      (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hX)
  exact Step1917Steps.eq_of_mem_oTwoComponentsIn h1913 hctx hKMH hXMH hLK hLX

theorem eq_of_card_eq
    (h1913 : Step1913) {A L E M H K X : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (hH : IsMaximalTwoLocal H) (hEH : E ≤ H) (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K)
    (hKH : K ≤ H) (hX : X ∈ oTwoComponentsIn H) (hLX : L ≤ X) (hKX : K ≤ X)
    (hcard : Nat.card (X ⧸ CFSG.pCore 2 X) = Nat.card (K ⧸ CFSG.pCore 2 K)) : K = X := by
  have hE := Step1916Proof2.isE27_E hctx
  have hOH : CFSG.Open.pCoreOf 2 H ≤ M := by
    rw [← hctx.hyp191 E M H hE hctx.mem_scriptM hEH (pCoreOf_ne_bot_of_isMaximalTwoLocal hH)]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hXM : X ≤ M := by
    rw [eq_sup_of_card_eq hKX hcard]
    exact sup_le (le_of_mem_oTwoComponentsIn hK)
      ((Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hX).trans hOH)
  exact eq_of_le_M h1913 hctx hK hLK hKH hX hLX hXM

theorem xStar_of_census
    (h1913 : Step1913) (hC : Census1915) {A L E M H X : Subgroup G} {c d : G}
    (hctx : Ctx1912 G A c L E M) (hdD : d ∈ A ⊓ E)
    (hH : H ∈ scriptM (Subgroup.normalizer (Subgroup.zpowers d : Set G) : Set G))
    (hX : X ∈ oTwoComponentsIn H) (hLX : L ≤ X)
    (hnc : ¬ ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) :
    (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) p e ∧
        Sec4.IsoLThreePi (X ⧸ CFSG.pCore 2 X) p (3 * e) ∧ KFacts.InducesStdKind X c .field) ∨
      ∃ (n : ℕ) (_ : 1 ≤ n) (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = (2 ^ n) ^ 3 ∧ ∃ σ : F ≃+* F, (∀ x, σ x = x ^ 2 ^ n) ∧
          Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃*
            CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 F
              σ.toRingHom) ∧
          Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) 2 n ∧
          CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ CFSG.pCore 2 X) .trialityD4 2 n ∧
          Sec4.InducesOuterTheta c X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  obtain ⟨hθ, hZ, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
  obtain ⟨F, hFL, hF, hF9⟩ := Step1918Proof.exists_elemAbelian_nine h1913 hctx
  have hL : L ∈ thetaComponentsAt 3 c := hctx.mem_lA.1
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := fun h hh =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Step1917Proof.map_conj_eq_of_mem_of_isMaximalTwoLocal hst hH.1 hZ hX hLX hFL hF hF9 hh)
  have hA := Step1916Proof2.isE27_A hctx
  have hcA := Step1916Proof2.mem_A hctx
  have hc3 := Step1916Proof2.orderOf_eq hctx
  have hAH : A ≤ H := Step1917Steps.le_H hA.1.1 hdD.1 hH.2
  have hXH : X ≤ H := le_of_mem_oTwoComponentsIn hX
  have hHtop : H ≠ ⊤ := by
    have : IsSimpleGroup G := hst.isSimpleGroup
    exact ne_top_of_pCoreOf_ne_bot hst.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal hH.1)
  have hXA4 : SectionFourHyp ↥(X ⊔ A) := hst.toTheoremFourHyp.sectionFourHyp
    (fun h => hHtop (top_le_iff.mp (h ▸ sup_le hXH hAH)))
  have hO2X : CFSG.Open.pCoreOf 2 X ≠ ⊥ :=
    pCoreOf_ne_bot_of_mem_oTwoComponentsIn hst.charTwoType hH.1.1 hX
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hLsn : (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).IsSubnormal :=
    PartOne.isSubnormal_of_mem_thetaComponentsAt hL
  have hOeq : (CFSG.pCore 2 L).map L.subtype = CFSG.Open.pCoreOf 2 L := by
    rfl
  have hsec : ∀ a ∈ A, (∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) →
      a ∈ Subgroup.zpowers c := by
    intro a ha h
    have hmem : a ∈ Late.sectionCentralizer A L
        ((aschbacherSolvableCore 3 L).map L.subtype) := by
      refine ⟨ha, fun l hl => ?_⟩
      rw [hθ, hOeq]
      exact h l hl
    have := hctx.mem_lA.2.2.1
    rw [this] at hmem
    exact hmem
  exact hC G X L A c hXA4 hO2X (isPerfect_of_mem_oTwoComponentsIn hX)
    (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hX) (hAH.trans hHX) hA.1 hA.2 hcA hc3 hnc
    hLX hLc (Sec18.isSubnormal_subgroupOf_of_le hLsn inf_le_right) hLp hctx.mem_lA.2.1 hsec
    (h1913 G A c L E M hctx)

theorem eq_of_census
    (h1913 : Step1913) (hC : Census1915) (hcen : Step1917EqCentral)
    {A L E M H K X : Subgroup G} {c d : G} (hctx : Ctx1912 G A c L E M) (hLM : L ≤ M)
    (hdD : d ∈ A ⊓ E) (hdc : d ∉ Subgroup.zpowers c)
    (hN : ¬ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ M)
    (hH : H ∈ scriptM (Subgroup.normalizer (Subgroup.zpowers d : Set G) : Set G)) (hHM : H ≠ M)
    (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K) (halt : Step1917Proof.Alt1915W L K c)
    (hKH : K ≤ H) (hX : X ∈ oTwoComponentsIn H) (hLX : L ≤ X)
    (hcX : c ∈ Subgroup.normalizer (X : Set G))
    (hnc : ¬ ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) : K = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  obtain ⟨hθ, hZ, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
  obtain ⟨F, hFL, hF, hF9⟩ := Step1918Proof.exists_elemAbelian_nine h1913 hctx
  have hL : L ∈ thetaComponentsAt 3 c := hctx.mem_lA.1
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hL1 : L ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card F ≤ Nat.card (⊥ : Subgroup G) := Subgroup.card_le_of_le hFL
    rw [Subgroup.card_bot] at h1
    omega
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := fun h hh =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Step1917Proof.map_conj_eq_of_mem_of_isMaximalTwoLocal hst hH.1 hZ hX hLX hFL hF hF9 hh)
  have hKX : K ≤ X := le_of_le_normalizer (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK)
    (isPerfect_of_mem_oTwoComponentsIn hK) (hKH.trans hHX) hLK hLX hLp hL1
  have hEH : E ≤ H := Step1917Steps.E_le_H hctx hdD.2 hH.2
  have hdvd := card_dvd_of_le hKX
  have hXpos : 0 < Nat.card (X ⧸ CFSG.pCore 2 X) := Nat.card_pos
  rcases halt with hKL | ⟨p', e', hp', he', hLiso', hKiso', -⟩ | ⟨n', hn', hLiso', hD4', -⟩
  ·
    exact absurd (hcen G A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK hKL hKH X hX hLX hKX
      hcX) hnc
  all_goals have hcensus := xStar_of_census h1913 hC hctx hdD hH hX hLX hnc
  ·
    rcases hcensus with ⟨p, e, hp, he, hLiso, hXiso, -⟩ |
      ⟨n, hn, F', _, _, hF', σ, hσ, -, hLiso, hD4, -⟩
    ·
      have hq := eq_of_isoLThreePi he he' hLiso hLiso'
      have hQ : p ^ (3 * e) = p' ^ (3 * e') := by
        rw [mul_comm 3 e, mul_comm 3 e', pow_mul, pow_mul, hq]
      refine eq_of_card_eq h1913 hctx hH.1 hEH hK hLK hKH hX hLX hKX ?_
      rcases Step1917Steps.three_mul_card_of_isoLThreePi (by omega : 1 ≤ 3 * e) hXiso with
        ⟨h1, hf, -⟩ | ⟨h1, hf⟩ <;>
      rcases Step1917Steps.three_mul_card_of_isoLThreePi (by omega : 1 ≤ 3 * e') hKiso' with
        ⟨h1', hf', -⟩ | ⟨h1', hf'⟩
      · rw [hQ] at hf
        omega
      · rw [hQ] at h1
        omega
      · rw [hQ] at h1
        omega
      · rw [hQ] at hf
        omega
    ·
      exfalso
      have hq := eq_of_isoLThreePi hn he' hLiso hLiso'
      obtain ⟨-, -, hXc⟩ := Step1911Proof.card_of_trialityD4 hD4
      rw [hXc] at hdvd
      have hQ : p' ^ (3 * e') = (2 ^ n) ^ 3 := by
        rw [mul_comm 3 e', pow_mul, hq]
      have h2n : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
      refine not_dvd_ordTrialityD4 h2n ?_ hdvd
      rcases Step1917Steps.three_mul_card_of_isoLThreePi (by omega : 1 ≤ 3 * e') hKiso' with
        ⟨-, hf, -⟩ | ⟨-, hf⟩
      · rw [hQ] at hf
        exact Or.inl hf.symm
      · rw [hQ] at hf
        exact Or.inr hf.symm
  ·
    obtain ⟨-, -, hKc⟩ := Step1911Proof.card_of_trialityD4 hD4'
    rcases hcensus with ⟨p, e, hp, he, hLiso, hXiso, -⟩ |
      ⟨n, hn, F', _, _, hF', σ, hσ, -, hLiso, hD4, -⟩
    ·
      exfalso
      have hq := eq_of_isoLThreePi he hn' hLiso hLiso'
      have hQ : p ^ (3 * e) = (2 ^ n') ^ 3 := by
        rw [mul_comm 3 e, pow_mul, hq]
      have h2n : 2 ≤ 2 ^ n' := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn')
      have hle : Nat.card (K ⧸ CFSG.pCore 2 K) ≤ Nat.card (X ⧸ CFSG.pCore 2 X) :=
        Nat.le_of_dvd hXpos hdvd
      rw [hKc] at hle
      rcases Step1917Steps.three_mul_card_of_isoLThreePi (by omega : 1 ≤ 3 * e) hXiso with
        ⟨-, hf, -⟩ | ⟨-, hf⟩
      · rw [hQ] at hf
        have := sl3Order_cube_lt h2n
        omega
      · rw [hQ] at hf
        have := su3Order_cube_lt h2n
        omega
    ·
      have hq := eq_of_isoLThreePi hn hn' hLiso hLiso'
      have hnn : n = n' := Nat.pow_right_injective le_rfl hq
      obtain ⟨-, -, hXc⟩ := Step1911Proof.card_of_trialityD4 hD4
      refine eq_of_card_eq h1913 hctx hH.1 hEH hK hLK hKH hX hLX hKX ?_
      rw [hXc, hKc, hnn]

end Step1917EqProof

open Step1917EqProof in
theorem step1917PushEq_of
    (h1913 : Step1913) (hC : Census1915) (hcen : Step1917EqCentral) : Step1917PushEq := by
  intro G _ _ A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK halt hKH _ X hX hLX hcX hnc
  exact eq_of_census h1913 hC hcen hctx hLM hdD hdc hN hH hHM hK hLK halt hKH hX hLX hcX hnc

open Step1917EqProof in
theorem step1917LiftEq_of
    (h1913 : Step1913) (hC : Census1915) (hcen : Step1917EqCentral) : Step1917LiftEq := by
  intro G _ _ A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK halt hKH _ _ X hX hLX hcX hnc
  exact eq_of_census h1913 hC hcen hctx hLM hdD hdc hN hH hHM hK hLK halt hKH hX hLX hcX hnc

end CFSG.RankThree.PartTwo.Sec19

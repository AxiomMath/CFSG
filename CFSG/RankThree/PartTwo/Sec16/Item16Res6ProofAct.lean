module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res6ProofActComp
public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofKDTwo
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofKP1End
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res6Act

open CFSG CFSG.RankThree.PartTwo

section QuotAct

variable {S Y : Type*} [Group S] [Group Y]

@[expose] noncomputable def quotAct (ψ : S →* MulAut Y) (N : Subgroup Y) [N.Normal]
    (hN : ∀ s, N.map (ψ s).toMonoidHom = N) : S →* MulAut (Y ⧸ N) where
  toFun s := QuotientGroup.congr N N (ψ s) (hN s)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      show (((ψ 1) y : Y) : Y ⧸ N) = (y : Y ⧸ N)
      rw [map_one]
      rfl
  map_mul' := by
    intro a b
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      show (((ψ (a * b)) y : Y) : Y ⧸ N) = (((ψ a) ((ψ b) y) : Y) : Y ⧸ N)
      rw [map_mul]
      rfl

end QuotAct

theorem layer_normal (X : Type*) [Group X] : (CFSG.layer X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : CFSG.layer X ≤ (CFSG.layer X).comap (MulAut.conj g).toMonoidHom := by
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact CFSG.LocalCores.component_le_layer (CFSG.LocalCores.isComponent_map_mulEquiv _ hJ)
  exact hle hn

theorem generalizedFitting_normal (X : Type*) [Group X] : (CFSG.generalizedFitting X).Normal := by
  have := layer_normal X
  change (CFSG.fittingSubgroup X ⊔ CFSG.layer X).Normal
  infer_instance

theorem eq_one_of_fix_generalizedFitting {X S : Type} [Group X] [Finite X] [Group S]
    [Group.IsPerfect S] (φ : S →* MulAut X)
    (hfix : ∀ s, ∀ x ∈ CFSG.generalizedFitting X, φ s x = x) : φ = 1 := by
  have hFn := generalizedFitting_normal X
  refine MonoidHom.ext fun s => MulEquiv.ext fun x => ?_
  have hcen : ∀ t, x⁻¹ * φ t x ∈ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
    intro t
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hf : x * g * x⁻¹ ∈ CFSG.generalizedFitting X := hFn.conj_mem g hg x
    have h1 : φ t (x * g * x⁻¹) = x * g * x⁻¹ := hfix t _ hf
    rw [map_mul, map_mul, map_inv, hfix t g hg] at h1
    calc g * (x⁻¹ * φ t x) = x⁻¹ * (x * g * x⁻¹) * φ t x := by group
      _ = x⁻¹ * (φ t x * g * (φ t x)⁻¹) * φ t x := by rw [h1]
      _ = x⁻¹ * φ t x * g := by group
  have hF : ∀ t, x⁻¹ * φ t x ∈ CFSG.generalizedFitting X := fun t =>
    CFSG.centralizer_generalizedFitting_le X (hcen t)
  let d : S →* X :=
    { toFun := fun t => x⁻¹ * φ t x
      map_one' := by simp
      map_mul' := by
        intro a b
        have h2 : φ a (x⁻¹ * φ b x) = x⁻¹ * φ b x := hfix a _ (hF b)
        have h3 : φ (a * b) x = φ a (x * (x⁻¹ * φ b x)) := by
          rw [mul_inv_cancel_left, map_mul]
          rfl
        rw [h3, map_mul, h2]
        group }
  have hcomm : ⁅d.range, d.range⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hcen a) _ (hF b)
  have : Group.IsPerfect d.range := Group.IsPerfect.range d
  have hbot : d.range = ⊥ := by rw [← Subgroup.commutator_eq_self (H := d.range), hcomm]
  have h3 : x⁻¹ * φ s x = 1 := by
    have h4 : d s ∈ d.range := ⟨s, rfl⟩
    rw [hbot] at h4
    exact Subgroup.mem_bot.mp h4
  rw [inv_mul_eq_one] at h3
  rw [← h3]
  rfl

section Abstract

theorem act_eq_one {X S : Type} [Group X] [Finite X] [Group S] [Finite S] (hS : ActHyp S)
    (hK : CFSG.IsKGroup X) (h3 : ¬ 3 ∣ Nat.card X) (h2 : CFSG.pCore 2 X = ⊥)
    (hrank : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 2)
    (φ : S →* MulAut X) : φ = 1 := by
  have := hS.1
  refine eq_one_of_fix_generalizedFitting φ fun s => ?_
  suffices h : CFSG.generalizedFitting X ≤ fixedSubgroupOf (φ s) from fun x hx => h hx
  change CFSG.fittingSubgroup X ⊔ CFSG.layer X ≤ fixedSubgroupOf (φ s)
  refine sup_le ?_ ?_
  · rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun p => ?_
    intro x hx
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have : Fact (p : ℕ).Prime := ⟨hp⟩
    by_cases hp2 : (p : ℕ) = 2
    · have hx' : x ∈ CFSG.pCore 2 X := hp2 ▸ hx
      rw [h2, Subgroup.mem_bot] at hx'
      rw [hx', mem_fixedSubgroupOf, map_one]
    by_cases hp3 : (p : ℕ) = 3
    · have hP : IsPGroup (p : ℕ) (CFSG.pCore (p : ℕ) X) := CFSG.pCore_isPGroup
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
      have hn0 : n = 0 := by
        by_contra hne
        apply h3
        rw [← hp3]
        exact (dvd_pow_self (p : ℕ) hne).trans
          (hn ▸ Subgroup.card_subgroup_dvd_card (CFSG.pCore (p : ℕ) X))
      rw [hn0, pow_zero] at hn
      have hbot := Subgroup.card_eq_one.mp hn
      rw [hbot, Subgroup.mem_bot] at hx
      rw [hx, mem_fixedSubgroupOf, map_one]
    · exact fix_pCore hS φ hp2 (hrank p hp (by have := hp.two_le; omega)) s hx
  · refine sSup_le fun J hJ x hx => ?_
    exact fix_component hS φ hK h3 (hrank 5 (by norm_num) (by norm_num)) hJ s hx

end Abstract

theorem isKGroup_of_le {G : Type} [Group G] {M R : Subgroup G} (hM : CFSG.IsKGroup ↥M)
    (hRM : R ≤ M) : CFSG.IsKGroup ↥R :=
  hM.of_injective (Subgroup.inclusion hRM) (Subgroup.inclusion_injective hRM)

end CFSG.RankThree.PartTwo.Sec16.Res6Act

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree.PartTwo Res6Act
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Main

theorem ks1624MaxLocalAct_holds : KS1624MaxLocalAct := by
  intro G _ _ M R K V m hMK _ hrank hRM hMR hR3 hKM hKp hVK _ hVe hVc hF4 hquot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  set Q' := Q.subgroupOf R with hQ'
  have hQ'n : Q'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hQ', Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hMQ (hRM g.2)) _).mp hn
  have hQ'2 : IsPGroup 2 Q' := hQ2.comap_subtype
  let ψ₀ : ↥M →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion hMR)
  have hψ₀ : ∀ (g : ↥M) (r : ↥R), ((ψ₀ g r : ↥R) : G) = (g : G) * r * (g : G)⁻¹ := fun g r =>
    Subgroup.normalizerMonoidHom_apply_apply_coe R _ r
  have hQinv : ∀ g, Q'.map (ψ₀ g).toMonoidHom = Q' := by
    intro g
    have hle : Q'.map (ψ₀ g).toMonoidHom ≤ Q' := by
      rintro _ ⟨q, hq, rfl⟩
      have hq' : (q : G) ∈ Q := hq
      show ((ψ₀ g q : ↥R) : G) ∈ Q
      rw [hψ₀]
      exact (Subgroup.mem_normalizer_iff.mp (hMQ g.2) _).mp hq'
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (f := (ψ₀ g).toMonoidHom) (ψ₀ g).injective])
  let ψ : ↥M →* MulAut (↥R ⧸ Q') := quotAct ψ₀ Q' hQinv
  let φ : ↥K →* MulAut (↥R ⧸ Q') := ψ.comp (Subgroup.inclusion hKM)
  have hS : ActHyp ↥K := actHyp_of_data hKp hVK hVe hVc hF4 hquot
  have hXK : CFSG.IsKGroup (↥R ⧸ Q') :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient (isKGroup_of_le hMK hRM) Q'
  have hX3 : ¬ 3 ∣ Nat.card (↥R ⧸ Q') := fun h =>
    hR3 (h.trans (Subgroup.card_quotient_dvd_card Q'))
  have hX2 : CFSG.pCore 2 (↥R ⧸ Q') = ⊥ := by
    set P := CFSG.pCore 2 (↥R ⧸ Q') with hPdef
    have hPinv : ∀ g, P.map (ψ g).toMonoidHom = P := map_eq_of_characteristic ψ P
    set Pt := P.comap (QuotientGroup.mk' Q') with hPt
    have hPt2 : IsPGroup 2 Pt := IsPGroup.comap_of_ker_isPGroup CFSG.pCore_isPGroup _
      (by rw [QuotientGroup.ker_mk']; exact hQ'2)
    set Ph := Pt.map R.subtype with hPh
    have hPh2 : IsPGroup 2 Ph := hPt2.map _
    have hPhM : Ph ≤ M := (Subgroup.map_subtype_le _).trans hRM
    have hMPh : M ≤ Subgroup.normalizer (Ph : Set G) := by
      intro g hg
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := hz
      have hy' : QuotientGroup.mk' Q' y ∈ P := hy
      have h1 : ψ ⟨g, hg⟩ (QuotientGroup.mk' Q' y) ∈ P := by
        rw [← hPinv ⟨g, hg⟩]
        exact ⟨_, hy', rfl⟩
      refine ⟨ψ₀ ⟨g, hg⟩ y, ?_, hψ₀ ⟨g, hg⟩ y⟩
      exact h1
    have hPhQ : Ph ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPhM hMPh hPh2
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Q' z
    have hy : y ∈ Pt := hz
    have hyQ : (y : G) ∈ Q := hPhQ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hyQ
  have hXrank : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r (⊤ : Subgroup (↥R ⧸ Q')) ≤ 2 := by
    intro r hr hr3
    have : Fact r.Prime := ⟨hr⟩
    have hrQ' : ¬ r ∣ Nat.card Q' := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ'2
      rw [hk]
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
      omega
    rw [CFSG.SectionRank.pRank_quotient_eq Q' hrQ']
    calc CFSG.Open.pRank r (⊤ : Subgroup ↥R)
        ≤ CFSG.Open.pRank r ((⊤ : Subgroup ↥R).map R.subtype) :=
          CFSG.SectionRank.pRank_le_map hr.one_lt R.subtype R.subtype_injective ⊤
      _ ≤ CFSG.Open.pRank r M :=
          CFSG.SectionRank.pRank_mono hr.one_lt ((Subgroup.map_subtype_le _).trans hRM)
      _ ≤ 2 := hrank r hr hr3
  have hφ := act_eq_one hS hXK hX3 hX2 hXrank φ
  rw [Subgroup.commutator_le]
  intro k hk r hr
  have h1 : φ ⟨k, hk⟩ (((⟨r, hr⟩ : ↥R)) : ↥R ⧸ Q') = (((⟨r, hr⟩ : ↥R)) : ↥R ⧸ Q') := by
    rw [hφ]
    rfl
  have h2 : φ ⟨k, hk⟩ (((⟨r, hr⟩ : ↥R)) : ↥R ⧸ Q') =
      (((ψ₀ ⟨k, hKM hk⟩ ⟨r, hr⟩ : ↥R)) : ↥R ⧸ Q') := rfl
  rw [h2, QuotientGroup.eq_iff_div_mem, hQ', Subgroup.mem_subgroupOf] at h1
  have h3 : ((ψ₀ ⟨k, hKM hk⟩ ⟨r, hr⟩ / ⟨r, hr⟩ : ↥R) : G) = ⁅k, r⁆ := by
    rw [Subgroup.coe_div, hψ₀]
    simp [commutatorElement_def, div_eq_mul_inv]
  rw [← h3]
  exact h1

theorem step1624KDTwo_of_1623 (h1623 : Step1623) : Step1624KDTwo :=
  step1624KDTwo_of h1623 ks1624ParaKP1 ks1624MaxLocalAct_holds

theorem step1624_of_schreier (h1622 : Step1622) (h316 : Sec19.Item316) (h1623 : Step1623)
    (hS : SchreierCycThree) : Step1624 :=
  step1624_of h1622 h316 h1623 (ks1624Para_of ks1624ParaKP1) (step1624KDThree_of_schreier hS)
    (step1624KDTwo_of_1623 h1623)

end Main

end CFSG.RankThree.PartTwo.Sec16

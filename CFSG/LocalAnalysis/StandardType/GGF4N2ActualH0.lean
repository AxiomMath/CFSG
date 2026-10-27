module

public import CFSG.LocalAnalysis.StandardType.GGF4N2JPacket
public import CFSG.LocalAnalysis.StandardType.GGF4N2Alignment
import CFSG.ClassicalInvolution.WeakCT.Center
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Quot
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyElement
import CFSG.LocalAnalysis.StandardType.GGF4N2L323
import CFSG.LocalAnalysis.StandardType.GGF4N2Rank
import CFSG.RankThree.PartOne.K159.PerfNormalizer
import CFSG.LocalAnalysis.GLTheoremA.S12.Lemma126
import CFSG.Holt.General.OrbitCountBasic
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift3
import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.AllPSubgroupsIsCyclicOfPRankLeOne
import CFSG.LocalAnalysis.StandardType.GGF4N2Schreier
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsAbsorb
import CFSG.LocalAnalysis.StandardType.GGE0ShapeConjAux
public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartCommute
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogOmegaOrth
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift1
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift2
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotUnitaryEven
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogLift
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatU6Assembly
import CFSG.RankThree.PartOne.S12.Sec1511Y3

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.RankThree.PartOne CFSG.ClassicalInvolution.WeakCT

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[expose] def ggN2H0 (M : Subgroup G) : Subgroup G :=
  LargeEvenPLayer 5 (Subgroup.centralizer (M : Set G))

omit [Finite G] in
@[expose] def GGN2NoPSL216 (H : Subgroup G) (u₁ u₂ : G) : Prop :=
  ∀ u ∈ Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂, u ∉ Subgroup.zpowers u₁ →
    u ∉ Subgroup.zpowers u₂ → ∀ K : Subgroup G,
      CFSG.Open.IsComponentOf K (LargeEvenPLayer 5 (H ⊓ Subgroup.centralizer {u})) →
      IsEmpty (↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4))

omit [Finite G] in
@[expose] def GGN2ChartAlt (X : Subgroup G) (u₁ u₂ : G) : Prop :=
  (∀ a ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer {u₁}),
      ∀ b ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer {u₂}), Commute a b) ∨
    ∃ u ∈ Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂, u ∉ Subgroup.zpowers u₁ ∧
      u ∉ Subgroup.zpowers u₂ ∧ ∃ K : Subgroup G,
        CFSG.Open.IsComponentOf K (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer {u})) ∧
        Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))

theorem ggN2_isComponentOf_pLayer_of_layer {p : ℕ} [Fact p.Prime] {H : Subgroup G} (u : G)
    {K : Subgroup G}
    (hK : CFSG.Open.IsComponentOf K
      (LargeEvenPLayer p (LargeEvenPLayer p H ⊓ Subgroup.centralizer {u}))) :
    CFSG.Open.IsComponentOf K (LargeEvenPLayer p (H ⊓ Subgroup.centralizer {u})) := by
  have hle : LargeEvenPLayer p H ≤ H := by
    rw [largeEvenPLayer_eq_lBalancePLayer]
    exact lBalancePLayer_le p H
  refine ggN2_isComponentOf_pLayer_of_normal hle ?_ u hK
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h x hh hx
  exact conj_mem_largeEvenPLayer hx hh

theorem ggN2_hM_of_actualH0 {M M₁ M₂ : Subgroup G} {u₁ u₂ : G}
    (hs₁ : LargeEvenPLayer 5 (ggN2H0 M ⊓ Subgroup.centralizer {u₁}) = M₁)
    (hs₂ : LargeEvenPLayer 5 (ggN2H0 M ⊓ Subgroup.centralizer {u₂}) = M₂)
    (hM14 : GGN2NoPSL216 (Subgroup.centralizer (M : Set G)) u₁ u₂)
    (hcomm : GGN2ChartAlt (ggN2H0 M) u₁ u₂) :
    ∀ a ∈ M₁, ∀ b ∈ M₂, a * b = b * a := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases hcomm with h | ⟨u, hu, hu₁, hu₂, K, hK, ⟨e⟩⟩
  · intro a ha b hb
    rw [← hs₁] at ha
    rw [← hs₂] at hb
    exact (h a ha b hb).eq
  · exact ((hM14 u hu hu₁ hu₂ K (ggN2_isComponentOf_pLayer_of_layer u hK)).false
      (e.trans (CFSG.ComponentClassification.GMS78.u3SL2EquivPSL2 _))).elim

omit [Finite G] in
theorem ggN2_actualH0_inputs {M M₁ M₂ : Subgroup G} {u₁ u₂ : G}
    (hs₁ : LargeEvenPLayer 5 (ggN2H0 M ⊓ Subgroup.centralizer {u₁}) = M₁)
    (hs₂ : LargeEvenPLayer 5 (ggN2H0 M ⊓ Subgroup.centralizer {u₂}) = M₂)
    (e₁ : ↥M₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (e₂ : ↥M₂ ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (hx₁ : u₂ ∈ M₁) (hx₂ : u₁ ∈ M₂) :
    u₁ ∈ ggN2H0 M ∧ u₂ ∈ ggN2H0 M ∧
      u₂ ∈ LargeEvenPLayer 5 (ggN2H0 M ⊓ Subgroup.centralizer {u₁}) ∧
      u₁ ∈ LargeEvenPLayer 5 (ggN2H0 M ⊓ Subgroup.centralizer {u₂}) ∧
      Nonempty (↥(LargeEvenPLayer 5 (ggN2H0 M ⊓ Subgroup.centralizer {u₁})) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
      Nonempty (↥(LargeEvenPLayer 5 (ggN2H0 M ⊓ Subgroup.centralizer {u₂})) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := by
  have hle : ∀ {X : Subgroup G} {u y : G}, y ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer {u}) →
      y ∈ X := fun {X u y} hy => by
    rw [largeEvenPLayer_eq_lBalancePLayer] at hy
    exact (lBalancePLayer_le 5 _ hy).1
  refine ⟨hle (hs₂ ▸ hx₂), hle (hs₁ ▸ hx₁), hs₁ ▸ hx₁, hs₂ ▸ hx₂,
    ⟨(MulEquiv.subgroupCongr hs₁).trans e₁⟩, ⟨(MulEquiv.subgroupCongr hs₂).trans e₂⟩⟩

omit [Finite G] in
theorem ggN2_nonempty_blockSL_map_equiv
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) {i : ℕ} (h : i + 3 ≤ 6) :
    Nonempty (↥((blockSL (GaloisField 2 2) 6 3 i h).range.map ψ) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := by
  rw [← MonoidHom.range_comp]
  exact ⟨(MonoidHom.ofInjective (comp_blockSL_injective hψ h (by norm_num))).symm⟩

omit [Finite G] in
private theorem ggN2_mem_normalizer_of_map_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨x', hx', hxx⟩ := hx
    have : x' = x := by simpa [MulAut.conj_apply] using hxx
    rwa [← this]

private theorem ggN2_mem_normalizer_of_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  apply ggN2_mem_normalizer_of_map_eq
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hcard : Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

omit [Finite G] in
private theorem ggN2_mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  apply ggN2_mem_normalizer_of_map_eq
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hH, map_conj_eq_of_mem_normalizer hK]

omit [Finite G] in
private theorem ggN2_commutator_le_self (C : Subgroup G) : ⁅C, C⁆ ≤ C :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb)

theorem ggN2_pLayer_le_of_sStar {B K E : Subgroup G} {u : G} (hS : LargeEvenSStar 5 B u K)
    (hu : orderOf u = 5)
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K))
    (hEK : E ≤ K) (hE : IsElemAbelian 5 E) (hEcard : 5 < Nat.card E) {Y : Subgroup G}
    (hY : Y ≤ Subgroup.centralizer {u}) : LargeEvenPLayer 5 Y ≤ K := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({u} : Set G)) := hS.2.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 5 S →
      IsCyclic S := hS.2.2.2.2
  have hKu : K ≤ Subgroup.centralizer ({u} : Set G) := hcomp.1
  have hN : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    ggF4N2_centralizer_le_normalizer_of_isComponentOf_of_cyclic hcomp hcyc hEK hE hEcard
  set P := LargeEvenPLayer 5 Y with hPdef
  have hPY : P ≤ Y := by
    rw [hPdef, largeEvenPLayer_eq_lBalancePLayer]
    exact lBalancePLayer_le 5 Y
  have hPu : P ≤ Subgroup.centralizer ({u} : Set G) := hPY.trans hY
  have hperf : ⁅P, P⁆ = P := by
    rw [hPdef, largeEvenPLayer_eq_lBalancePLayer]
    exact Subgroup.isPerfect_iff.mp (CFSG.ComponentClassification.LBalance.pLayer_perfect 5 Y)
  have hPN : P ≤ Subgroup.normalizer (K : Set G) := hPu.trans hN
  have h1 : P ≤ K ⊔ Subgroup.centralizer (K : Set G) :=
    CFSG.RankThree.PartOne.K159.le_sup_centralizer_of_outer_solvable
      (Subgroup.isPerfect_iff.mpr hperf) hPN hOut
  set A := Subgroup.centralizer (K : Set G) ⊓ Subgroup.centralizer ({u} : Set G) with hA
  set N₀ := CFSG.Open.GLAPPrimeCoreOf 5 A with hN₀
  have huA : u ∈ A := ⟨Subgroup.mem_centralizer_iff.mpr fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKu hk),
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hpow : ∀ a ∈ A, ∃ n : ℕ, a ^ (5 ^ n) ∈ N₀ :=
    CFSG.LocalAnalysis.GLTheoremA.S12.normal_pcomplement_cyclic Nat.prime_five huA hu
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mp ha.2)
      (fun S hS hSp => hcyc S (hS.trans inf_le_left) hSp)
  have hKC : ∀ a ∈ K, ∀ b ∈ Subgroup.centralizer (K : Set G), Commute a b :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha
  have hdec : ∀ g ∈ P, ∃ k ∈ K, ∃ c ∈ A, k * c = g := by
    intro g hg
    obtain ⟨k, hk, c, hc, rfl⟩ := (CFSG.mem_sup_of_commute hKC).mp (h1 hg)
    refine ⟨k, hk, c, ⟨hc, ?_⟩, rfl⟩
    have hg' := Subgroup.mem_centralizer_singleton_iff.mp (hPu hg)
    have hk' := Subgroup.mem_centralizer_singleton_iff.mp (hKu hk)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc c * u = k⁻¹ * (k * c * u) := by group
      _ = k⁻¹ * (u * (k * c)) := by rw [hg']
      _ = k⁻¹ * (u * k) * c := by group
      _ = k⁻¹ * (k * u) * c := by rw [hk']
      _ = u * c := by group
  have hN₀A : N₀ ≤ A := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le (p := 5) A
  have hN₀K : ∀ n ∈ N₀, ∀ k ∈ K, k * n = n * k := fun n hn k hk =>
    Subgroup.mem_centralizer_iff.mp (hN₀A hn).1 k hk
  have hPN' : P ≤ Subgroup.normalizer ((K ⊔ N₀ : Subgroup G) : Set G) := by
    intro g hg
    obtain ⟨k, hk, c, hc, rfl⟩ := hdec g hg
    refine ggN2_mem_normalizer_sup (hPN hg) (ggN2_mem_normalizer_of_conj_mem fun n hn => ?_)
    have hcn := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem c hc n hn
    have hkn := hN₀K _ hcn k hk
    have heq : k * c * n * (k * c)⁻¹ = c * n * c⁻¹ := by
      calc k * c * n * (k * c)⁻¹ = k * (c * n * c⁻¹) * k⁻¹ := by group
        _ = c * n * c⁻¹ * k * k⁻¹ := by rw [hkn]
        _ = c * n * c⁻¹ := by group
    rw [heq]
    exact hcn
  have hPpow : ∀ g ∈ P, ∃ n : ℕ, g ^ 5 ^ n ∈ K ⊔ N₀ := by
    intro g hg
    obtain ⟨k, hk, c, hc, rfl⟩ := hdec g hg
    obtain ⟨n, hn⟩ := hpow c hc
    refine ⟨n, ?_⟩
    rw [(hKC k hk c hc.1).mul_pow]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ hk _))
      (Subgroup.mem_sup_right hn)
  have h2 : P ≤ K ⊔ N₀ :=
    CFSG.Holt.General.le_of_isPerfect_of_forall_pow_mem hperf hPN' hPpow
  have hpp : CFSG.LocalAnalysis.GLTheoremA.S10.PPrimePerfect 5 P := by
    have h := CFSG.LocalAnalysis.GLTheoremA.S10.pPrimePerfect_glaPLayer 5 Y
    rwa [CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_eq,
      ← largeEvenPLayer_eq_lBalancePLayer] at h
  refine CFSG.LocalAnalysis.GLTheoremA.H301.le_of_pPrimePerfect_of_le_sup hpp hPN ?_ ?_ h2
  · intro k hk
    exact ggN2_mem_normalizer_of_conj_mem fun n hn => by
      rw [hN₀K n hn k hk, mul_inv_cancel_right]
      exact hn
  · exact (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf
      Nat.prime_five A).symm

theorem ggN2_le_pLayer_of_normal_quasisimple {p : ℕ} [Fact p.Prime] {Y N : Subgroup G}
    (hNY : N ≤ Y) (hN : (N.subgroupOf Y).Normal) (hq : CFSG.Open.IsQuasisimple ↥N)
    (hp : p ∣ Nat.card N) : N ≤ LargeEvenPLayer p Y := by
  have hcomp : CFSG.Open.IsComponentOf N Y :=
    ⟨hNY, CFSG.Open.IsSubnormal.step hNY hN (CFSG.Open.IsSubnormal.refl _), hq⟩
  rw [largeEvenPLayer_eq_lBalancePLayer]
  exact le_sSup (lBalanceIsPComponent_of_isComponentOf
    (CFSG.Assembly.isComponentOf_iff_open.mpr hcomp) (not_le_lBalancePrimeCore_of_dvd hp))

theorem ggN2_pLayer_le_of_normal {p : ℕ} [Fact p.Prime] {A B : Subgroup G} (hAB : A ≤ B)
    (hA : (A.subgroupOf B).Normal) : LargeEvenPLayer p A ≤ LargeEvenPLayer p B := by
  rw [largeEvenPLayer_eq_lBalancePLayer, largeEvenPLayer_eq_lBalancePLayer]
  exact sSup_le fun L hL => le_sSup (lBalanceIsPComponent_of_normal hAB
    (ggN2_le_of_isSubnormal hL.1) hL)

theorem ggN2_pLayer_inf_centralizer_le {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : CFSG.ComponentClassification.LBalance.SchreierSections ↥H) {x : G} (hxH : x ∈ H)
    (hx : ∃ n : ℕ, x ^ p ^ n = 1) :
    LargeEvenPLayer p (H ⊓ Subgroup.centralizer {x}) ≤ LargeEvenPLayer p H := by
  rw [largeEvenPLayer_eq_lBalancePLayer, largeEvenPLayer_eq_lBalancePLayer]
  have hx' : ∃ n : ℕ, (⟨x, hxH⟩ : H) ^ p ^ n = 1 :=
    hx.imp fun n hn => Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hn)
  have hC : (H ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf H =
      Subgroup.centralizer ({(⟨x, hxH⟩ : H)} : Set H) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, SetLike.coe_mem, true_and,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [← CFSG.ComponentClassification.LBalance.pLayer_nested_map p
      (H ⊓ Subgroup.centralizer ({x} : Set G)) H inf_le_left, hC,
    ← CFSG.ComponentClassification.LBalance.pLayer_nested_map p H H le_rfl,
    Subgroup.subgroupOf_self]
  exact Subgroup.map_mono
    (CFSG.ComponentClassification.LBalance.lBalancePLayer_centralizer_element_le hH hx')

omit [Finite G] in
theorem ggN2_schreierSections_of_sections {Q : Subgroup G}
    (hsec : ∀ A B : Subgroup G, B ≤ A → A ≤ Q → ∀ [(B.subgroupOf A).Normal],
      IsSimpleGroup (A ⧸ B.subgroupOf A) → (∃ x y : A ⧸ B.subgroupOf A, x * y ≠ y * x) →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (A ⧸ B.subgroupOf A))) :
    CFSG.ComponentClassification.LBalance.SchreierSections ↥Q := by
  intro A B _ _ hs hnc
  let A' : Subgroup G := A.map Q.subtype
  let e : ↥A ≃* ↥A' := A.equivMapOfInjective Q.subtype Q.subtype_injective
  let f : ↥A' →* ↥A ⧸ B.subgroupOf A :=
    (QuotientGroup.mk' (B.subgroupOf A)).comp e.symm.toMonoidHom
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp e.symm.surjective
  let B' : Subgroup G := f.ker.map A'.subtype
  have hB : B'.subgroupOf A' = f.ker :=
    Subgroup.comap_map_eq_self_of_injective A'.subtype_injective _
  have : (B'.subgroupOf A').Normal := by
    rw [hB]
    infer_instance
  let e' : ↥A' ⧸ B'.subgroupOf A' ≃* ↥A ⧸ B.subgroupOf A :=
    (QuotientGroup.quotientMulEquivOfEq hB).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hs' : IsSimpleGroup (↥A' ⧸ B'.subgroupOf A') := e'.isSimpleGroup
  have hnc' : ∃ a b : ↥A' ⧸ B'.subgroupOf A', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e'.symm a, e'.symm b, fun h => hab (by simpa using congrArg e' h)⟩
  have := hsec A' B' (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _) hs' hnc'
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e'

omit [Finite G] in
theorem ggN2_complement_normal (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (ψ.range : Set G))
    (hYM : Y ≤ Subgroup.centralizer
      (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G))
    (hM'Y : (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ ≤ Y) :
    (((blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hM'Y]
  intro a y ha hy
  rw [ggSL6Chart_complement_eq_commutator_centralizer ψ hψ] at ha ⊢
  set C := ψ.range ⊓ Subgroup.centralizer
    (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G) with hCdef
  have hC : C.map (MulAut.conj y).toMonoidHom = C := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hYN hy) c).mp hc.1, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
      have hym := Subgroup.mem_centralizer_iff.mp (hYM hy) m hm
      have hcm := Subgroup.mem_centralizer_iff.mp hc.2 m hm
      have hym' : y * m * y⁻¹ = m := by rw [← hym]; group
      show m * (y * c * y⁻¹) = y * c * y⁻¹ * m
      calc m * (y * c * y⁻¹) = m * y * c * y⁻¹ := by group
        _ = y * (m * c) * y⁻¹ := by rw [hym]; group
        _ = y * (c * m) * y⁻¹ := by rw [hcm]
        _ = y * c * y⁻¹ * (y * m * y⁻¹) := by group
        _ = y * c * y⁻¹ * m := by rw [hym']
    · intro c hc
      have hy' : y⁻¹ ∈ Y := Y.inv_mem hy
      refine ⟨y⁻¹ * c * y, ⟨?_, ?_⟩, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hYN hy') c).mp hc.1
        rwa [inv_inv] at this
      · refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
        have hym := Subgroup.mem_centralizer_iff.mp (hYM hy) m hm
        have hcm := Subgroup.mem_centralizer_iff.mp hc.2 m hm
        have hym' : y⁻¹ * m * y = m := by rw [mul_assoc, hym]; group
        calc m * (y⁻¹ * c * y) = y⁻¹ * (y * m * y⁻¹) * c * y := by group
          _ = y⁻¹ * m * c * y := by rw [show y * m * y⁻¹ = m by rw [← hym]; group]
          _ = y⁻¹ * (c * m) * y := by rw [mul_assoc y⁻¹ m c, hcm]
          _ = y⁻¹ * c * y * (y⁻¹ * m * y) := by group
          _ = y⁻¹ * c * y * m := by rw [hym']
      · show y * (y⁻¹ * c * y) * y⁻¹ = c
        group
  have hmem : (MulAut.conj y).toMonoidHom a ∈ (⁅C, C⁆).map (MulAut.conj y).toMonoidHom :=
    ⟨a, ha, rfl⟩
  rw [Subgroup.map_commutator, hC] at hmem
  simpa [MulAut.conj_apply] using hmem

omit [Finite G] in
theorem ggN2_pLayer_le_complement
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} {Y : Subgroup G}
    (hYM : Y ≤ Subgroup.centralizer
      (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G))
    (hYK : LargeEvenPLayer p Y ≤ ψ.range) :
    LargeEvenPLayer p Y ≤ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ := by
  have hperf : ⁅LargeEvenPLayer p Y, LargeEvenPLayer p Y⁆ = LargeEvenPLayer p Y := by
    rw [largeEvenPLayer_eq_lBalancePLayer]
    exact Subgroup.isPerfect_iff.mp (CFSG.ComponentClassification.LBalance.pLayer_perfect p Y)
  have hPY : LargeEvenPLayer p Y ≤ Y := by
    rw [largeEvenPLayer_eq_lBalancePLayer]
    exact lBalancePLayer_le p Y
  have hle := le_inf hYK (hPY.trans hYM)
  rw [ggSL6Chart_complement_eq_commutator_centralizer ψ hψ, ← hperf]
  exact Subgroup.commutator_mono hle hle

theorem ggN2_card_SL3 :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = 60480 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have h4 : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [Matrix.card_SL_field, h4]
  simp [Fin.prod_univ_three]

theorem ggN2_blockSL_map_quasisimple
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) {i : ℕ} (h : i + 3 ≤ 6) :
    CFSG.Open.IsQuasisimple ↥((blockSL (GaloisField 2 2) 6 3 i h).range.map ψ) ∧
      5 ∣ Nat.card ↥((blockSL (GaloisField 2 2) 6 3 i h).range.map ψ) := by
  obtain ⟨e⟩ := ggN2_nonempty_blockSL_map_equiv ψ hψ h
  refine ⟨ggN2_isQuasisimple_of_equiv_SL3 e, ?_⟩
  rw [Nat.card_congr e.toEquiv, ggN2_card_SL3]
  norm_num

theorem ggN2_slice_centralizer_eq
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) {u : G}
    (hKu : ψ.range ≤ Subgroup.centralizer {u})
    (hN : Subgroup.centralizer {u} ≤ Subgroup.normalizer (ψ.range : Set G))
    (hL : LargeEvenPLayer 5 (Subgroup.centralizer
      (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G) ⊓
        Subgroup.centralizer {u}) ≤ ψ.range) :
    LargeEvenPLayer 5 (Subgroup.centralizer
      (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G) ⊓
        Subgroup.centralizer {u}) = (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hM'C : (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ ≤
      ψ.range ⊓ Subgroup.centralizer
        (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G) := by
    rw [ggSL6Chart_complement_eq_commutator_centralizer ψ hψ]
    exact ggN2_commutator_le_self _
  have hM'Y : (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ ≤
      Subgroup.centralizer
        (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G) ⊓
        Subgroup.centralizer {u} := fun x hx => ⟨(hM'C hx).2, hKu (hM'C hx).1⟩
  obtain ⟨hq, h5⟩ := ggN2_blockSL_map_quasisimple ψ hψ (i := 3) (by norm_num)
  refine le_antisymm (ggN2_pLayer_le_complement ψ hψ inf_le_left hL)
    (ggN2_le_pLayer_of_normal_quasisimple hM'Y ?_ hq h5)
  exact ggN2_complement_normal ψ hψ (inf_le_right.trans hN) inf_le_left hM'Y

theorem ggN2_slice_H0_eq {M M' : Subgroup G} {u : G}
    (hs : LargeEvenPLayer 5 (Subgroup.centralizer (M : Set G) ⊓ Subgroup.centralizer {u}) = M')
    (hbal : M' ≤ ggN2H0 M) (hq : CFSG.Open.IsQuasisimple ↥M') (h5 : 5 ∣ Nat.card M') :
    LargeEvenPLayer 5 (ggN2H0 M ⊓ Subgroup.centralizer {u}) = M' := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hH₀H : ggN2H0 M ≤ Subgroup.centralizer (M : Set G) := by
    rw [ggN2H0, largeEvenPLayer_eq_lBalancePLayer]
    exact lBalancePLayer_le 5 _
  have hH₀n : ((ggN2H0 M).subgroupOf (Subgroup.centralizer (M : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hH₀H]
    intro h x hh hx
    exact conj_mem_largeEvenPLayer hx hh
  have hAB : ggN2H0 M ⊓ Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.centralizer (M : Set G) ⊓ Subgroup.centralizer ({u} : Set G) :=
    inf_le_inf_right _ hH₀H
  have hAn : ((ggN2H0 M ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
      (Subgroup.centralizer (M : Set G) ⊓ Subgroup.centralizer ({u} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAB]
    intro a m ha hm
    exact ⟨(Subgroup.normal_subgroupOf_iff hH₀H).mp hH₀n a m ha.1 hm.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hm.2 ha.2) (Subgroup.inv_mem _ hm.2)⟩
  have hM'B : M' ≤ Subgroup.centralizer (M : Set G) ⊓ Subgroup.centralizer ({u} : Set G) := by
    rw [← hs, largeEvenPLayer_eq_lBalancePLayer]
    exact lBalancePLayer_le 5 _
  have hM'Bn : (M'.subgroupOf
      (Subgroup.centralizer (M : Set G) ⊓ Subgroup.centralizer ({u} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hM'B]
    intro a m ha hm
    rw [← hs] at ha ⊢
    exact conj_mem_largeEvenPLayer hm ha
  have hM'A : M' ≤ ggN2H0 M ⊓ Subgroup.centralizer ({u} : Set G) :=
    le_inf hbal (hM'B.trans inf_le_right)
  have hM'An : (M'.subgroupOf (ggN2H0 M ⊓ Subgroup.centralizer ({u} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hM'A]
    intro a m ha hm
    exact (Subgroup.normal_subgroupOf_iff hM'B).mp hM'Bn a m ha (hAB hm)
  refine le_antisymm ?_ (ggN2_le_pLayer_of_normal_quasisimple hM'A hM'An hq h5)
  calc LargeEvenPLayer 5 (ggN2H0 M ⊓ Subgroup.centralizer {u}) ≤
        LargeEvenPLayer 5 (Subgroup.centralizer (M : Set G) ⊓ Subgroup.centralizer {u}) :=
      ggN2_pLayer_le_of_normal hAB hAn
    _ = M' := hs

theorem ggN2_slice_eq_of_sStar
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) {B E K : Subgroup G} {u : G} (hKψ : ψ.range = K)
    (hS : LargeEvenSStar 5 B u K) (hu : orderOf u = 5)
    (huM : u ∈ Subgroup.centralizer
      (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G))
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K))
    (hEK : E ≤ K) (hE : IsElemAbelian 5 E) (hEcard : 5 < Nat.card E)
    (hsch : CFSG.ComponentClassification.LBalance.SchreierSections ↥(Subgroup.centralizer
      (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G))) :
    LargeEvenPLayer 5 (ggN2H0 ((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ) ⊓
      Subgroup.centralizer {u}) = (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  subst hKψ
  have hcomp : CFSG.Assembly.IsComponentOf ψ.range (Subgroup.centralizer ({u} : Set G)) :=
    hS.2.2.2.1
  have hN : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (ψ.range : Set G) :=
    ggF4N2_centralizer_le_normalizer_of_isComponentOf_of_cyclic hcomp hS.2.2.2.2 hEK hE hEcard
  have hs := ggN2_slice_centralizer_eq ψ hψ hcomp.1 hN
    (ggN2_pLayer_le_of_sStar hS hu hOut hEK hE hEcard inf_le_right)
  obtain ⟨hq, h5⟩ := ggN2_blockSL_map_quasisimple ψ hψ (i := 3) (by norm_num)
  refine ggN2_slice_H0_eq hs ?_ hq h5
  rw [← hs]
  exact ggN2_pLayer_inf_centralizer_le hsch huM ⟨1, by rw [pow_one, ← hu, pow_orderOf_eq_one]⟩

theorem ggN2_H0_le_of_sStar {M B K E : Subgroup G} {u : G} (hS : LargeEvenSStar 5 B u K)
    (hu : orderOf u = 5) (huM : u ∈ M)
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K))
    (hEK : E ≤ K) (hE : IsElemAbelian 5 E) (hEcard : 5 < Nat.card E) : ggN2H0 M ≤ K :=
  ggN2_pLayer_le_of_sStar hS hu hOut hEK hE hEcard fun _ hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz u huM).symm

omit [Finite G] in
theorem ggN2_centralizer_eq_of_zpowers_eq {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have key : ∀ {a b : G}, b ∈ Subgroup.zpowers a →
      Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro a b hb c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hc) k).eq
  refine le_antisymm (key ?_) (key ?_)
  · rw [h]
    exact Subgroup.mem_zpowers b
  · rw [← h]
    exact Subgroup.mem_zpowers a

theorem ggN2_blockSL30_le_blockSL40 :
    (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range ≤
      (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)).range := by
  rw [ggBlockSL_range_eq_blockSpecialLinear _ ({0, 1, 2} : Finset (Fin 6)) (by decide),
    ggBlockSL_range_eq_blockSpecialLinear _ ({0, 1, 2, 3} : Finset (Fin 6)) (by decide)]
  exact CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_mono (by decide)

omit [Finite G] in
theorem ggF4N2_map_blockSL30_eq
    {ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G}
    (hblock : ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
      ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))) :
    (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₂ =
      (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ := by
  have h30 := ggN2_blockSL30_le_blockSL40
  have hagree : ∀ a ∈ (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)).range, ψ₂ a = ψ₁ a := by
    rintro _ ⟨b, rfl⟩
    exact DFunLike.congr_fun hblock b
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (hagree a (h30 ha)).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, hagree a (h30 ha)⟩

theorem ggN2_quadMat_blockGamma (c : GaloisField 2 2)
    (C : Matrix.GeneralLinearGroup (Fin 4) (GaloisField 2 2)) {δ : ℕ} (hδ : δ ≤ 1)
    (z : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) :
    N2Chart.quadMat c ((N2KFieldCoefficient.blockGamma C δ z :
      Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) = 0 ↔
      N2Chart.quadMat c (z : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with rfl | rfl
  · simp only [N2KFieldCoefficient.blockGamma, pow_zero, mul_one]
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    exact N2Chart.quadMat_conj_GL c C _
  · simp only [N2KFieldCoefficient.blockGamma, pow_one, MulAut.mul_apply]
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
      N2Chart.quadMat_conj_GL, CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
    exact N2Chart.quadMat_invTranspose_SL c z

abbrev ggN2BlockSwap : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5

theorem ggN2_blockSwap_inv : ggN2BlockSwap⁻¹ = ggN2BlockSwap := by decide

theorem ggN2_blockSwap_conj_mem (a : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :
    ggPermSL ggN2BlockSwap * blockSL (GaloisField 2 2) 6 3 3 (by norm_num) a *
        (ggPermSL ggN2BlockSwap)⁻¹ ∈ (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range := by
  rw [ggBlockSL_range_eq_blockSpecialLinear _ ({0, 1, 2} : Finset (Fin 6)) (by decide)]
  have hx : blockSL (GaloisField 2 2) 6 3 3 (by norm_num) a ∈
      CFSG.SeitzReduction.LinearPilot.blockSpecialLinear ({3, 4, 5} : Finset (Fin 6)) := by
    rw [← ggBlockSL_range_eq_blockSpecialLinear (by norm_num : 3 + 3 ≤ 6)
      ({3, 4, 5} : Finset (Fin 6)) (by decide)]
    exact ⟨a, rfl⟩
  have h := CFSG.SeitzReduction.SymplecticPilot.reindex_mem_blockSpecialLinear
    (F := GaloisField 2 2) ggN2BlockSwap.symm hx
  have hset : ({3, 4, 5} : Finset (Fin 6)).map ggN2BlockSwap.symm.toEmbedding = {0, 1, 2} := by
    decide
  rw [hset] at h
  convert h using 1
  apply Subtype.ext
  rw [coe_ggPermSL_conj]
  show _ = Matrix.reindex ggN2BlockSwap.symm ggN2BlockSwap.symm _
  rw [Matrix.reindex_apply, Equiv.symm_symm]

omit [Finite G] in
theorem ggF4N2_mixed_type_iff {K : Subgroup G} {y g : G}
    {ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G}
    (h₁ : ψ₁.ker ≤ Subgroup.center _) (hK₁ : ψ₁.range = K) (h₂ : ψ₂.ker ≤ Subgroup.center _)
    (hK₂ : ψ₂.range = K.map (MulAut.conj g).toMonoidHom)
    (hblock : ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
      ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)))
    (hKy : K ≤ Subgroup.centralizer {y}) (hgg : g * (g * y * g⁻¹) * g⁻¹ = y)
    {C : Matrix.GeneralLinearGroup (Fin 4) (GaloisField 2 2)} {δ : ℕ} (hδ : δ ≤ 1)
    (hΓ : ∀ z : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2),
      g * ψ₁ (blockSL (GaloisField 2 2) 6 4 0 (by norm_num) z) * g⁻¹ =
        ψ₁ (blockSL (GaloisField 2 2) 6 4 0 (by norm_num) (N2KFieldCoefficient.blockGamma C δ z)))
    (hu : g * y * g⁻¹ ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁)
    (hu5 : (g * y * g⁻¹) ^ 5 = 1) (c : GaloisField 2 2)
    {s₁ s₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2)}
    (hs₁ : ((MulAut.conj (ψ₁ (ggPermSL ggN2BlockSwap))).toMonoidHom.comp ψ₂) s₁ = y)
    (hs₁5 : s₁ ^ 5 = 1)
    (hs₂ : ((MulAut.conj (ψ₁ (ggPermSL ggN2BlockSwap))).toMonoidHom.comp ψ₂) s₂ = g * y * g⁻¹)
    (hs₂5 : s₂ ^ 5 = 1) :
    N2Chart.quadMat c (s₁ : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) = 0 ↔
      N2Chart.quadMat c (s₂ : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) = 0 := by
  classical
  set P : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) := ggPermSL ggN2BlockSwap with hPdef
  set h := ψ₁ P with hhdef
  have hPinv : P⁻¹ = P := by rw [hPdef, ggPermSL_inv, ggN2_blockSwap_inv]
  have hhinv : h⁻¹ = h := by rw [hhdef, ← map_inv, hPinv]
  have hhh : h * h = 1 := by
    calc h * h = h * h⁻¹ := by rw [hhinv]
      _ = 1 := mul_inv_cancel h
  have hψ₃ : ∀ s, ((MulAut.conj h).toMonoidHom.comp ψ₂) s = h * ψ₂ s * h := fun s => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hhinv]
  have hker₃ : ((MulAut.conj h).toMonoidHom.comp ψ₂).ker ≤ Subgroup.center _ := by
    intro z hz
    apply h₂
    rw [MonoidHom.mem_ker] at hz ⊢
    rw [hψ₃] at hz
    calc ψ₂ z = h * (h * ψ₂ z * h) * h := by
          rw [← mul_assoc, ← mul_assoc, hhh, one_mul, mul_assoc, hhh, mul_one]
      _ = 1 := by rw [hz, mul_one, hhh]
  have hhy : h * y = y * h := Subgroup.mem_centralizer_singleton_iff.mp (hKy (hK₁ ▸ ⟨P, rfl⟩))
  obtain ⟨_, ⟨a, rfl⟩, hau⟩ := hu
  obtain ⟨b, hb⟩ := ggN2_blockSL30_le_blockSL40 (ggN2_blockSwap_conj_mem a)
  have ha5 : a ^ 5 = 1 := by
    apply CFSG.ClassicalInvolution.WeakCT.comp_blockSL_injective h₁ (by norm_num : 3 + 3 ≤ 6)
      (by norm_num : 3 < 6)
    rw [MonoidHom.comp_apply, map_pow, map_pow, hau, hu5, MonoidHom.comp_apply, map_one, map_one]
  have hb5 : b ^ 5 = 1 := by
    apply CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := GaloisField 2 2)
      (by norm_num : 0 + 4 ≤ 6)
    rw [map_pow, hb, conj_pow, ← map_pow, ha5, map_one, mul_one, mul_inv_cancel, map_one]
  have hψb : ψ₁ (blockSL (GaloisField 2 2) 6 4 0 (by norm_num) b) = h * (g * y * g⁻¹) * h := by
    rw [hb, map_mul, map_mul, map_inv, hau, ← hhdef, hhinv]
  have hu₃ : ((MulAut.conj h).toMonoidHom.comp ψ₂)
      (blockSL (GaloisField 2 2) 6 4 0 (by norm_num) b) = g * y * g⁻¹ := by
    rw [hψ₃, ← MonoidHom.comp_apply ψ₂, hblock, MonoidHom.comp_apply, hψb]
    calc h * (h * (g * y * g⁻¹) * h) * h = (h * h) * (g * y * g⁻¹) * (h * h) := by group
      _ = g * y * g⁻¹ := by rw [hhh, one_mul, mul_one]
  have hs₂eq : s₂ = blockSL (GaloisField 2 2) 6 4 0 (by norm_num) b :=
    N2Chart.lift_five_unique hker₃ (hs₂.trans hu₃.symm) hs₂5 (by rw [← map_pow, hb5, map_one])
  have hu' : g * (h * (g * y * g⁻¹) * h) * g⁻¹ = ψ₁ (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)
      (N2KFieldCoefficient.blockGamma C δ b)) := by
    rw [← hΓ, hψb]
  have hh' : g * h * g⁻¹ ∈ ψ₂.range := by
    rw [hK₂]
    exact ⟨h, hK₁ ▸ ⟨P, rfl⟩, rfl⟩
  obtain ⟨m, hm⟩ := hh'
  have hyl : ψ₂ (m⁻¹ * blockSL (GaloisField 2 2) 6 4 0 (by norm_num)
      (N2KFieldCoefficient.blockGamma C δ b) * m) = y := by
    rw [map_mul, map_mul, map_inv, hm, ← MonoidHom.comp_apply ψ₂, hblock, MonoidHom.comp_apply,
      ← hu']
    calc (g * h * g⁻¹)⁻¹ * (g * (h * (g * y * g⁻¹) * h) * g⁻¹) * (g * h * g⁻¹) =
        g * (h⁻¹ * h) * (g * y * g⁻¹) * (h * h) * g⁻¹ := by group
      _ = g * (g * y * g⁻¹) * g⁻¹ := by rw [inv_mul_cancel, hhh]; group
      _ = y := hgg
  have hy₃ : ((MulAut.conj h).toMonoidHom.comp ψ₂) (m⁻¹ * blockSL (GaloisField 2 2) 6 4 0
      (by norm_num) (N2KFieldCoefficient.blockGamma C δ b) * m) = y := by
    rw [hψ₃, hyl, hhy, mul_assoc, hhh, mul_one]
  have hmm : m⁻¹ * blockSL (GaloisField 2 2) 6 4 0 (by norm_num)
      (N2KFieldCoefficient.blockGamma C δ b) * m = m⁻¹ * blockSL (GaloisField 2 2) 6 4 0
        (by norm_num) (N2KFieldCoefficient.blockGamma C δ b) * m⁻¹⁻¹ := by
    rw [inv_inv]
  have hX5 : (m⁻¹ * blockSL (GaloisField 2 2) 6 4 0 (by norm_num)
      (N2KFieldCoefficient.blockGamma C δ b) * m) ^ 5 = 1 := by
    rw [hmm, conj_pow, ← map_pow, ← map_pow, hb5, map_one, map_one, mul_one, mul_inv_cancel]
  have hs₁eq := N2Chart.lift_five_unique hker₃ (hs₁.trans hy₃.symm) hs₁5 hX5
  rw [hs₁eq, hs₂eq, hmm, N2Chart.quadMat_conj_SL, N2Chart.quadMat_blockSL,
    N2Chart.quadMat_blockSL, ggN2_quadMat_blockGamma c C hδ]

section Ingress

theorem ggF4N2_mixed_ingress {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    {ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G}
    (h₂ : ψ₂.ker ≤ Subgroup.center _) (hK₂ : ψ₂.range = K.map (MulAut.conj g).toMonoidHom)
    (hgyM₁ : g * y * g⁻¹ ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁) :
    ((MulAut.conj (ψ₁ (ggPermSL ggN2BlockSwap))).toMonoidHom.comp ψ₂).ker ≤
        Subgroup.center _ ∧
      ggN2H0 ((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁) ≤
        ((MulAut.conj (ψ₁ (ggPermSL ggN2BlockSwap))).toMonoidHom.comp ψ₂).range := by
  obtain ⟨-, -, hyo, -, -, -⟩ := ggF4N2_x_data hR hNbr
  have hKg : GGCentralImage .PSL 6 2 (K.map (MulAut.conj g).toMonoidHom) :=
    GGCentralImage.of_eq_map_conj (h := g⁻¹)
      (by rw [map_conj_map_conj, inv_mul_cancel, map_conj_eq_of_mem K.one_mem]) hK
  have hgyo : orderOf (g * y * g⁻¹) = 5 := by
    rw [← SemiconjBy.orderOf_eq g (show SemiconjBy g y (g * y * g⁻¹) by
      rw [SemiconjBy]
      group)]
    exact hyo
  set h := ψ₁ (ggPermSL ggN2BlockSwap) with hhdef
  have hu₃M : h * (g * y * g⁻¹) * h⁻¹ ∈
      (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ := by
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hgyM₁
    obtain ⟨b, hb⟩ := ggN2_blockSwap_conj_mem a
    refine ⟨_, ⟨b, rfl⟩, ?_⟩
    rw [hb, map_mul, map_mul, map_inv, ha]
  have hS₃ := shapeConj_largeEvenSStar_map_conj (ggF4N2_sStar_map_conj hR hNbr hL hK hgN) h
  have hK₃ : GGCentralImage .PSL 6 2 ((K.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj h).toMonoidHom) :=
    GGCentralImage.of_eq_map_conj (h := h⁻¹)
      (by rw [map_conj_map_conj, inv_mul_cancel, map_conj_eq_of_mem (Subgroup.one_mem _)]) hKg
  obtain ⟨T₃, -, hTK₃, -, -, -, hTel₃, hTcard₃, -, -, -⟩ := ggF4N2_psl6_block_torus_data hK₃
  have hT5₃ : 5 < Nat.card T₃ := by
    rw [hTcard₃]
    norm_num
  have hu₃o : orderOf (h * (g * y * g⁻¹) * h⁻¹) = 5 := by
    rw [← SemiconjBy.orderOf_eq h (show SemiconjBy h (g * y * g⁻¹)
      (h * (g * y * g⁻¹) * h⁻¹) by
        rw [SemiconjBy]
        group)]
    exact hgyo
  have hingress := ggN2_H0_le_of_sStar hS₃ hu₃o hu₃M
    (isSolvable_outer_of_centralImage_PSL_six_two hK₃) hTK₃ hTel₃ hT5₃
  refine ⟨fun z hz => h₂ ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hz ⊢
    have hz' : h * ψ₂ z * h⁻¹ = 1 := hz
    calc ψ₂ z = h⁻¹ * (h * ψ₂ z * h⁻¹) * h := by group
      _ = 1 := by rw [hz']; group
  · rw [MonoidHom.range_comp, hK₂]
    exact hingress

end Ingress

section MixedConsumer

theorem ggF4N2_mixed_slices_of_charts {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hinv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hxg : g * x * g⁻¹ = x)
    {ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G}
    (h₁ : ψ₁.ker ≤ Subgroup.center _) (hK₁ : ψ₁.range = K)
    (hJ₁ : (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J)
    (h₂ : ψ₂.ker ≤ Subgroup.center _) (hK₂ : ψ₂.range = K.map (MulAut.conj g).toMonoidHom)
    (hblock : ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
      ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))) :
    ∃ v : G, v ∈ D ⊓ K ∧ orderOf v = 5 ∧ D = Subgroup.zpowers y ⊔ Subgroup.zpowers v ∧
      g * y * g⁻¹ ∈ Subgroup.zpowers v ∧
      v ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁ ∧
      y ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂ ∧
      orderOf y = 5 ∧ y * v = v * y ∧ v ∉ Subgroup.zpowers y ∧
      LargeEvenPLayer 5 (ggN2H0 ((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁) ⊓
          Subgroup.centralizer {y}) = (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁ ∧
      LargeEvenPLayer 5 (ggN2H0 ((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁) ⊓
          Subgroup.centralizer {v}) = (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂ ∧
      (∃ ψ₃ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G,
        ψ₃.ker ≤ Subgroup.center _ ∧ ggN2H0 ((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁) ≤ ψ₃.range) ∧
      (GGN2NoPSL216 (Subgroup.centralizer (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ : Subgroup G) : Set G)) y (g * y * g⁻¹) →
        ∀ a ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁,
          ∀ b ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂, a * b = b * a) := by
  obtain ⟨v, hvDK, hvo, hDyv, hgy, hvM₁, hyM₂⟩ :=
    ggF4N2_mixed_charts_cross hR hNbr hL hK hF4 hgL hgN hinv hxg h₁ hK₁ hJ₁ h₂ hK₂ hblock
  obtain ⟨-, -, hyo, -, hDcard, hDel⟩ := ggF4N2_x_data hR hNbr
  have hyD : y ∈ D := by
    rw [hDyv]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hyv : y * v = v * y :=
    congrArg Subtype.val (hDel.1.is_comm.comm (⟨y, hyD⟩ : ↥D) ⟨v, hvDK.1⟩)
  have hvy : v ∉ Subgroup.zpowers y := by
    intro hv
    have hDy : D = Subgroup.zpowers y := by
      rw [hDyv]
      exact sup_eq_left.mpr (Subgroup.zpowers_le.mpr hv)
    rw [hDy, Nat.card_zpowers, hyo] at hDcard
    norm_num at hDcard
  have hM₂ := ggF4N2_map_blockSL30_eq hblock
  have hMJ : (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ ≤ J := by
    rw [← hJ₁, MonoidHom.range_comp]
    exact Subgroup.map_mono ggN2_blockSL30_le_blockSL40
  have hDC : ∀ d ∈ D, d ∈ Subgroup.centralizer
      (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ : Subgroup G) : Set G) := by
    intro d hd
    rw [ggF4N2_D_eq_Bs_inf_centralizer_J hR hL] at hd
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hMJ) hd.2
  have hQ : Subgroup.centralizer
      (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    have hsimple : IsSimpleGroup G := hR.1.1.1
    obtain ⟨a, b, hab⟩ := hR.1.1.2.1
    have hZ : Subgroup.center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · exact h
      · have ha : a ∈ Subgroup.center G := by
          rw [h]
          exact Subgroup.mem_top a
        exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
    have hMbot : (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ = ⊥ := by
      rw [eq_bot_iff, ← hZ]
      intro m hm
      refine Subgroup.mem_center_iff.mpr fun z => ?_
      have hz : z ∈ Subgroup.centralizer
          (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ : Subgroup G) : Set G) := by
        rw [htop]
        exact Subgroup.mem_top z
      exact (Subgroup.mem_centralizer_iff.mp hz m hm).symm
    obtain ⟨-, h5⟩ := ggN2_blockSL_map_quasisimple ψ₁ h₁ (i := 0) (by norm_num)
    rw [hMbot, Subgroup.card_bot] at h5
    norm_num at h5
  have hsch := ggN2_schreierSections_of_sections
    (ggN2_sectionSchreier hR.1.1.2.2.1 hQ)
  obtain ⟨T, -, hTK, -, -, -, hTel, hTcard, -, -, -⟩ := ggF4N2_psl6_block_torus_data hK
  have hT5 : 5 < Nat.card T := by
    rw [hTcard]
    norm_num
  have hs₁ := ggN2_slice_eq_of_sStar ψ₁ h₁ hK₁ (ggF4N2_sStar_K hR hNbr hL hK) hyo (hDC y hyD)
    (isSolvable_outer_of_centralImage_PSL_six_two hK) hTK hTel hT5 hsch
  have hKg : GGCentralImage .PSL 6 2 (K.map (MulAut.conj g).toMonoidHom) :=
    GGCentralImage.of_eq_map_conj (h := g⁻¹)
      (by rw [map_conj_map_conj, inv_mul_cancel, map_conj_eq_of_mem K.one_mem]) hK
  obtain ⟨T', -, hTK', -, -, -, hTel', hTcard', -, -, -⟩ := ggF4N2_psl6_block_torus_data hKg
  have hT5' : 5 < Nat.card T' := by
    rw [hTcard']
    norm_num
  have hgyo : orderOf (g * y * g⁻¹) = 5 := by
    rw [← SemiconjBy.orderOf_eq g (show SemiconjBy g y (g * y * g⁻¹) by
      rw [SemiconjBy]
      group)]
    exact hyo
  have hzp : Subgroup.zpowers (g * y * g⁻¹) = Subgroup.zpowers v :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgy)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hgyo, hvo])
  have hgyD : g * y * g⁻¹ ∈ D := by
    rw [hDyv]
    exact Subgroup.mem_sup_right hgy
  have hs₂ := ggN2_slice_eq_of_sStar ψ₂ h₂ hK₂ (ggF4N2_sStar_map_conj hR hNbr hL hK hgN) hgyo
    (by rw [hM₂]; exact hDC _ hgyD) (isSolvable_outer_of_centralImage_PSL_six_two hKg)
    hTK' hTel' hT5' (by rw [hM₂]; exact hsch)
  rw [hM₂, ggN2_centralizer_eq_of_zpowers_eq hzp] at hs₂
  have hgyM₁ : g * y * g⁻¹ ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁ :=
    (Subgroup.zpowers_le.mpr hvM₁) hgy
  obtain ⟨hker₃, hrange₃⟩ := ggF4N2_mixed_ingress hR hNbr hL hK hgN h₂ hK₂ hgyM₁
  obtain ⟨e₁⟩ := ggN2_nonempty_blockSL_map_equiv ψ₁ h₁ (i := 3) (by norm_num)
  obtain ⟨e₂⟩ := ggN2_nonempty_blockSL_map_equiv ψ₂ h₂ (i := 3) (by norm_num)
  obtain ⟨hyX, hvX, hx₁, hx₂, hi₁, hi₂⟩ := ggN2_actualH0_inputs hs₁ hs₂ e₁ e₂ hvM₁ hyM₂
  refine ⟨v, hvDK, hvo, hDyv, hgy, hvM₁, hyM₂, hyo, hyv, hvy, hs₁, hs₂, ⟨_, hker₃, hrange₃⟩,
    fun h14 => ggN2_hM_of_actualH0 hs₁ hs₂ ?_
      (N2Chart.ggN2_actualChart_commute_of_inputs _ hker₃ hrange₃ hyX hvX hyo hvo hyv hvy
        hi₁ hi₂ hx₁ hx₂)⟩
  unfold GGN2NoPSL216 at h14 ⊢
  rw [← hzp]
  exact h14

theorem ggF4N2_mixed_hM_of_goodLine {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hinv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hxg : g * x * g⁻¹ = x)
    {ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G}
    (h₁ : ψ₁.ker ≤ Subgroup.center _) (hK₁ : ψ₁.range = K)
    (hJ₁ : (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J)
    (h₂ : ψ₂.ker ≤ Subgroup.center _) (hK₂ : ψ₂.range = K.map (MulAut.conj g).toMonoidHom)
    (hblock : ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
      ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)))
    (hgood : ∀ I : Subgroup G, CFSG.Open.IsComponentOf I (LargeEvenPLayer 5
      (Subgroup.centralizer (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ :
        Subgroup G) : Set G) ⊓ Subgroup.centralizer {y * (g * y * g⁻¹)})) →
      IsEmpty (↥I ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    ∀ a ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁,
      ∀ b ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂, a * b = b * a := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨v, -, hvo, hDyv, hgy, hvM₁, hyM₂, hyo, hyv, hvy, hs₁, hs₂, -, -⟩ :=
    ggF4N2_mixed_slices_of_charts hR hNbr hL hK hF4 hgL hgN hinv hxg h₁ hK₁ hJ₁ h₂ hK₂ hblock
  have hgyM₁ : g * y * g⁻¹ ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁ :=
    (Subgroup.zpowers_le.mpr hvM₁) hgy
  obtain ⟨hker₃, hrange₃⟩ := ggF4N2_mixed_ingress hR hNbr hL hK hgN h₂ hK₂ hgyM₁
  have hgyo : orderOf (g * y * g⁻¹) = 5 := by
    rw [← SemiconjBy.orderOf_eq g (show SemiconjBy g y (g * y * g⁻¹) by
      rw [SemiconjBy]
      group)]
    exact hyo
  have hzp : Subgroup.zpowers (g * y * g⁻¹) = Subgroup.zpowers v :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgy)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hgyo, hvo])
  have hs₂u : LargeEvenPLayer 5 (ggN2H0 ((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁) ⊓
      Subgroup.centralizer {g * y * g⁻¹}) =
        (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂ := by
    rw [ggN2_centralizer_eq_of_zpowers_eq hzp]
    exact hs₂
  obtain ⟨e₁⟩ := ggN2_nonempty_blockSL_map_equiv ψ₁ h₁ (i := 3) (by norm_num)
  obtain ⟨e₂⟩ := ggN2_nonempty_blockSL_map_equiv ψ₂ h₂ (i := 3) (by norm_num)
  obtain ⟨hyX, huX, hx₁, hx₂, hi₁, hi₂⟩ := ggN2_actualH0_inputs hs₁ hs₂u e₁ e₂ hgyM₁ hyM₂
  have hc : Commute y (g * y * g⁻¹) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgy
    rw [← hk]
    exact Commute.zpow_right hyv k
  have hD : g * y * g⁻¹ ∉ Subgroup.zpowers y := fun h => hvy
    (Subgroup.zpowers_le.mpr h (by rw [hzp]; exact Subgroup.mem_zpowers _))
  have hinj4 : Function.Injective (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))) :=
    CFSG.ClassicalInvolution.WeakCT.comp_blockSL_injective h₁ (by norm_num) (by norm_num)
  obtain ⟨C, δ, hδ, hΓ⟩ := ggF4N2L_swap_field_free hR hNbr hL hK
    ((MulEquiv.subgroupCongr hJ₁).symm.trans (MonoidHom.ofInjective hinj4).symm) hgL hinv hxg
  have hKy : K ≤ Subgroup.centralizer {y} :=
    (CFSG.Assembly.isComponentOf_iff_open.mp (ggF4N2_sStar_K hR hNbr hL hK).2.2.2.1).1
  have hyD : y ∈ D := by
    rw [hDyv]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hgg : g * (g * y * g⁻¹) * g⁻¹ = y := by
    have h2 : y * (g * g) = g * g * y := by
      rw [← pow_two]
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (ggF4N2L_swap_sq_centralizes hR hL hgL hinv hxg hyD)
    calc g * (g * y * g⁻¹) * g⁻¹ = g * g * y * (g⁻¹ * g⁻¹) := by simp only [mul_assoc]
      _ = y * (g * g) * (g⁻¹ * g⁻¹) := by rw [h2]
      _ = y := by simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  have hu5 : (g * y * g⁻¹) ^ 5 = 1 := by
    rw [← hgyo]
    exact pow_orderOf_eq_one _
  rcases N2Chart.ggN2_actualChart_commute_of_matching _ hker₃ hrange₃ hyX huX hyo hgyo hc hD
      hi₁ hi₂ hx₁ hx₂ (fun c s₁ s₂ hs₁' hs₁5 hs₂' hs₂5 =>
        ggF4N2_mixed_type_iff h₁ hK₁ h₂ hK₂ hblock hKy hgg hδ (fun z => hΓ z) hgyM₁ hu5 c hs₁'
          hs₁5 hs₂' hs₂5) with h | ⟨I, hI, ⟨e⟩⟩
  · intro a ha b hb
    rw [← hs₁] at ha
    rw [← hs₂u] at hb
    exact (h a ha b hb).eq
  · exact ((hgood I (ggN2_isComponentOf_pLayer_of_layer _ hI)).false
      (e.trans (CFSG.ComponentClassification.GMS78.u3SL2EquivPSL2 _))).elim

end MixedConsumer

end CFSG.StandardType

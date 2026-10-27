module

public import CFSG.RankThree.PartTwo.Sec6.Item65Two
import CFSG.RankThree.PartTwo.Sec6.Item66
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

@[expose] def BThreeProperty : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), SectionFourHyp H →
    ∀ X ∈ thetaComponentsIn H, ∀ b ∈ H, b ^ 3 = 1 → b ∈ Subgroup.normalizer (X : Set G) →
    ∀ Y : Subgroup G, Y ≤ X ⊓ Subgroup.centralizer {b} → Group.IsPerfect Y →
      (Y.subgroupOf (X ⊓ Subgroup.centralizer {b})).IsSubnormal →
      IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y) →
      ⁅inSubgroup (aschbacherSolvableCore 3) Y, Y⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X

@[expose] def BThreePropertyCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), SectionFourHyp H →
    3 ∣ Nat.card (Subgroup.center H) →
    ∀ X ∈ thetaComponentsIn H, ∀ b ∈ H, b ^ 3 = 1 → b ∈ Subgroup.normalizer (X : Set G) →
    ∀ Y : Subgroup G, Y ≤ X ⊓ Subgroup.centralizer {b} → Group.IsPerfect Y →
      (Y.subgroupOf (X ⊓ Subgroup.centralizer {b})).IsSubnormal →
      IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y) →
      ⁅inSubgroup (aschbacherSolvableCore 3) Y, Y⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X

theorem bThreePropertyCentral_of_bThreeProperty (h : BThreeProperty) : BThreePropertyCentral := by
  intro G _ _ H hH _ X hX b hbH hb3 hbX Y hYXC hYp hYsn hYq
  exact h G H hH X hX b hbH hb3 hbX Y hYXC hYp hYsn hYq

variable {G : Type} [Group G] [Finite G]

structure Ctx65 (G : Type) [Group G] [Finite G] (A L B E : Subgroup G) (a₀ : G) : Prop where
  standing : PartTwoStanding G
  mem_S : A ∈ partTwoS G
  a₀_mem : a₀ ∈ A
  a₀_ne : a₀ ≠ 1
  mem_L : L ∈ thetaComponentsAt 3 a₀
  elemB : CFSG.Assembly.IsElemAbelian 3 B
  cardB : Nat.card B = 9
  B_le : B ≤ A ⊓ thetaQuotCentralizer L
  mem_E : E ∈ collectionIn (partTwoE G) (A ⊔ L)
  B_le_E : B ≤ E
  neg : ∀ b ∈ B, b ≠ 1 → ∀ K ∈ thetaComponentsAt 3 b,
    inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K →
    ∀ S ∈ invariantPiSubgroups K E (piOf 2), S ≠ ⊥ → ⁅S, B⁆ ≠ S

theorem residual_inf_centralizer_le_residual {L B : Subgroup G} {a : G} (haB : a ∈ B) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (B : Set G)) ≤
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) :=
  inSubgroup_perfectResidual_mono ((inf_le_inf_left L
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB))).trans le_sup_left)

omit [Finite G] in
theorem map_conj_mul (g k : G) (H : Subgroup G) :
    H.map (MulAut.conj (g * k)).toMonoidHom =
      (H.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem fusionIsSylowIn_map_conj {p : ℕ} {S M : Subgroup G}
    (hS : CFSG.Open.fusionIsSylowIn p S M) {z : G} (hz : z ∈ Subgroup.normalizer (M : Set G)) :
    CFSG.Open.fusionIsSylowIn p (S.map (MulAut.conj z).toMonoidHom) M := by
  obtain ⟨hSM, hSp, hmax⟩ := hS
  refine ⟨?_, hSp.map _, fun Q hQM hQ hSQ => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hz s).mp (hSM hs)
  · have hz' : z⁻¹ ∈ Subgroup.normalizer (M : Set G) := inv_mem hz
    have h1 : Q.map (MulAut.conj z⁻¹).toMonoidHom ≤ M := by
      rintro _ ⟨q, hq, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hz' q).mp (hQM hq)
    have h2 : S ≤ Q.map (MulAut.conj z⁻¹).toMonoidHom := by
      intro s hs
      refine ⟨z * s * z⁻¹, hSQ ⟨s, hs, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h3 := hmax _ h1 (hQ.map _) h2
    rw [← h3, ← map_conj_mul, mul_inv_cancel]
    ext x
    simp

omit [Finite G] in
theorem le_normalizer_map_conj {P B : Subgroup G} {z : G}
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) (hzB : z ∈ Subgroup.centralizer (B : Set G)) :
    B ≤ Subgroup.normalizer ((P.map (MulAut.conj z).toMonoidHom : Subgroup G) : Set G) := by
  have key : ∀ β ∈ B, ∀ x ∈ P.map (MulAut.conj z).toMonoidHom,
      β * x * β⁻¹ ∈ P.map (MulAut.conj z).toMonoidHom := by
    rintro β hβ _ ⟨p, hp, rfl⟩
    have hzβ : z * β = β * z := (Subgroup.mem_centralizer_iff.mp hzB β hβ).symm
    refine ⟨β * p * β⁻¹, (Subgroup.mem_normalizer_iff.mp (hBP hβ) p).mp hp, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hzβ' : z⁻¹ * β = β * z⁻¹ := by
      calc z⁻¹ * β = z⁻¹ * (β * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * β) * z⁻¹ := by rw [hzβ]
        _ = β * z⁻¹ := by group
    calc z * (β * p * β⁻¹) * z⁻¹ = (z * β) * p * (β⁻¹ * z⁻¹) := by group
      _ = (β * z) * p * (z⁻¹ * β⁻¹) := by
        rw [hzβ, show β⁻¹ * z⁻¹ = z⁻¹ * β⁻¹ by
          rw [← mul_inv_rev, ← mul_inv_rev, hzβ]]
      _ = β * (z * p * z⁻¹) * β⁻¹ := by group
  exact le_normalizer_of_forall_conj_mem key

omit [Finite G] in
theorem inv_mul_mem_normalizer_of_map_conj_eq {P : Subgroup G} {z c : G}
    (h : P.map (MulAut.conj z).toMonoidHom = P.map (MulAut.conj c).toMonoidHom) :
    c⁻¹ * z ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : z * x * z⁻¹ ∈ P.map (MulAut.conj c).toMonoidHom := h ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    rw [show c⁻¹ * z * x * (c⁻¹ * z)⁻¹ = c⁻¹ * (z * x * z⁻¹) * c by group, ← hyx]
    simpa [mul_assoc] using hy
  · intro hx
    have h1 : c * (c⁻¹ * z * x * (c⁻¹ * z)⁻¹) * c⁻¹ ∈ P.map (MulAut.conj z).toMonoidHom :=
      h.symm ▸ ⟨_, hx, rfl⟩
    rw [show c * (c⁻¹ * z * x * (c⁻¹ * z)⁻¹) * c⁻¹ = z * x * z⁻¹ by group] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by
      have := congrArg (fun w => z⁻¹ * w * z) hyx
      simpa [mul_assoc] using this
    rw [← this]
    exact hy

theorem exists_mem_centralizer_inv_mul_mem {B P Θ : Subgroup G} (hB3 : IsPGroup 3 B)
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) (hBΘ : B ≤ Subgroup.normalizer (Θ : Set G))
    (hPΘ : P ≤ Subgroup.normalizer (Θ : Set G)) (hΘ3 : ¬ 3 ∣ Nat.card Θ) {c : G}
    (hc : c ∈ P ⊔ Θ) (hcB : c ∈ Subgroup.centralizer (B : Set G)) :
    ∃ p ∈ P, p ∈ Subgroup.centralizer (B : Set G) ∧ p⁻¹ * c ∈ Θ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc' : c ∈ (P : Set G) * (Θ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right P Θ hPΘ]
    exact hc
  obtain ⟨p₀, hp₀, t₀, ht₀, rfl⟩ := hc'
  have h3 : ¬ 3 ∣ Nat.card (P ⊓ Θ : Subgroup G) := fun h =>
    hΘ3 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  set α : B →* MulAut G := MulAut.conj.comp B.subtype
  obtain ⟨p, hp, hpfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hB3 α
    (P ⊓ Θ) h3 p₀).2 (by
      intro a x hx
      change p₀⁻¹ * ((a : G) * x * (a : G)⁻¹) ∈ P ⊓ Θ
      have hxP : x ∈ P := by
        have := P.mul_mem hp₀ hx.1
        simpa using this
      have ha := hcB
      rw [Subgroup.mem_centralizer_iff] at ha
      have hca : (a : G) * (p₀ * t₀) * (a : G)⁻¹ = p₀ * t₀ := by
        have h0 := ha a a.2
        simp only at h0
        rw [h0]
        group
      refine ⟨P.mul_mem (P.inv_mem hp₀) ((Subgroup.mem_normalizer_iff.mp (hBP a.2) x).mp hxP), ?_⟩
      have h1 : (a : G) * (p₀⁻¹ * x) * (a : G)⁻¹ ∈ Θ :=
        (Subgroup.mem_normalizer_iff.mp (hBΘ a.2) _).mp hx.2
      have h2 : (a : G) * t₀⁻¹ * (a : G)⁻¹ ∈ Θ :=
        (Subgroup.mem_normalizer_iff.mp (hBΘ a.2) _).mp (Θ.inv_mem ht₀)
      have e : p₀⁻¹ * ((a : G) * x * (a : G)⁻¹) =
          (t₀ * ((a : G) * t₀⁻¹ * (a : G)⁻¹)) * ((a : G) * (p₀⁻¹ * x) * (a : G)⁻¹) := by
        have hca' : p₀⁻¹ * ((a : G) * p₀ * (a : G)⁻¹) = t₀ * ((a : G) * t₀⁻¹ * (a : G)⁻¹) := by
          calc p₀⁻¹ * ((a : G) * p₀ * (a : G)⁻¹)
              = p₀⁻¹ * ((a : G) * (p₀ * t₀) * (a : G)⁻¹) * ((a : G) * t₀⁻¹ * (a : G)⁻¹) := by
                group
            _ = p₀⁻¹ * (p₀ * t₀) * ((a : G) * t₀⁻¹ * (a : G)⁻¹) := by rw [hca]
            _ = t₀ * ((a : G) * t₀⁻¹ * (a : G)⁻¹) := by group
        calc p₀⁻¹ * ((a : G) * x * (a : G)⁻¹)
            = p₀⁻¹ * ((a : G) * p₀ * (a : G)⁻¹) * ((a : G) * (p₀⁻¹ * x) * (a : G)⁻¹) := by group
          _ = _ := by rw [hca']
      rw [e]
      exact Θ.mul_mem (Θ.mul_mem ht₀ h2) h1)
  refine ⟨p, ?_, ?_, ?_⟩
  · have := P.mul_mem hp₀ hp.1
    simpa using this
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : a * p * a⁻¹ = p := hpfix ⟨a, ha⟩
    calc a * p = (a * p * a⁻¹) * a := by group
      _ = p * a := by rw [h1]
  · rw [show p⁻¹ * (p₀ * t₀) = (p₀⁻¹ * p)⁻¹ * t₀ by group]
    exact Θ.mul_mem (Θ.inv_mem hp.2) ht₀

theorem isQuasisimple_of_mem_thetaComponentsIn {M K : Subgroup G}
    (hK : K ∈ thetaComponentsIn M) : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) := by
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  set e := Subgroup.subgroupOfEquivOfLe hKM
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
      Nat.prime_three e)) hK'.2.2

theorem not_isPGroup_two_of_isPerfect {Y : Subgroup G} (hYp : Group.IsPerfect Y) (hY1 : Y ≠ ⊥)
    (hY2 : IsPGroup 2 Y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent Y := hY2.isNilpotent
  have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot _).mpr hY1
  have := hYp
  exact Group.IsPerfect.not_isSolvable Y inferInstance

namespace Ctx65

variable {A L B E : Subgroup G} {a₀ : G} (h : Ctx65 G A L B E a₀)
include h

theorem B_le_A : B ≤ A := h.B_le.trans inf_le_left

theorem B_le_C : B ≤ thetaQuotCentralizer L := h.B_le.trans inf_le_right

theorem elemA : CFSG.Assembly.IsElemAbelian 3 A := h.mem_S.1.1

theorem elemE : CFSG.Assembly.IsElemAbelian 3 E := h.mem_E.1.1

theorem cardE : Nat.card E = 27 := h.mem_E.1.2.1

theorem isPGroup_B : IsPGroup 3 B := Sec5.isPGroup_of_isElemAbelian h.elemB

theorem isPGroup_E : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian h.elemE

theorem E_le_centralizer {a : G} (haB : a ∈ B) : E ≤ Subgroup.centralizer ({a} : Set G) :=
  fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (h.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨a, h.B_le_E haB⟩))

theorem A_le_centralizer {a : G} (haA : a ∈ A) : A ≤ Subgroup.centralizer ({a} : Set G) :=
  fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (h.elemA.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))

theorem E_le_normalizer_B : E ≤ Subgroup.normalizer (B : Set G) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro β
  have hc : ∀ β ∈ B, e * β * e⁻¹ = β := fun β hβ => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (h.E_le_centralizer hβ he)]
    group
  constructor
  · intro hβ
    rw [hc β hβ]
    exact hβ
  · intro hβ
    have := hc _ hβ
    have hβ' : β = e * β * e⁻¹ := by
      calc β = e⁻¹ * (e * β * e⁻¹) * e := by group
        _ = e⁻¹ * (e * (e * β * e⁻¹) * e⁻¹) * e := by rw [this]
        _ = e * β * e⁻¹ := by group
    rw [hβ']
    exact hβ

theorem E_le_centralizer_B : E ≤ Subgroup.centralizer (B : Set G) :=
  fun _ hx => Subgroup.mem_centralizer_iff.mpr fun _ hβ =>
    (Subgroup.mem_centralizer_singleton_iff.mp (h.E_le_centralizer hβ hx)).symm

theorem A_le_normalizer (h45 : Sec4.Item4_5) {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) :
    ∀ K ∈ thetaComponentsAt 3 a, A ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_of_mem_thetaComponentsAt h45 h.standing.toTheoremFourHyp h.elemA (h.B_le_A haB) ha1

theorem E_le_normalizer (h45 : Sec4.Item4_5) {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) :
    ∀ K ∈ thetaComponentsAt 3 a, E ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_of_mem_thetaComponentsAt h45 h.standing.toTheoremFourHyp h.elemE (h.B_le_E haB) ha1

theorem commutator_eq_bot (h45 : Sec4.Item4_5) {a : G} (haB : a ∈ B) (ha1 : a ≠ 1)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    (hLK : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K)
    {S : Subgroup G} (hS : S ∈ invariantPiSubgroups K E (piOf 2)) : ⁅S, B⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSK, hS2, hES⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hS
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := h.B_le_E.trans hES
  have hS'S : ⁅S, B⁆ ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hBS
  have hS'2 : IsPGroup 2 (⁅S, B⁆ : Subgroup G) := hS2.to_le hS'S
  have hES' : E ≤ Subgroup.normalizer ((⁅S, B⁆ : Subgroup G) : Set G) := fun e he =>
    Source.mem_normalizer_commutator (hES he) (h.E_le_normalizer_B he)
  have hBS' : B ≤ Subgroup.normalizer ((⁅S, B⁆ : Subgroup G) : Set G) := h.B_le_E.trans hES'
  have hS'eq : ⁅⁅S, B⁆, B⁆ = ⁅S, B⁆ := by
    have hcop : (Nat.card B).Coprime (Nat.card S) := by
      obtain ⟨k, hk⟩ := hS2.exists_card_eq
      rw [h.cardB, hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    exact CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime S B hcop hBS
  rcases lt_or_eq_of_le hLK with hlt | heq
  · by_contra hne
    exact h.neg a haB ha1 K hK hlt ⁅S, B⁆
      ((mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨hS'S.trans hSK, hS'2, hES'⟩) hne hS'eq
  · have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
      h.B_le_A.trans (h.A_le_normalizer h45 haB ha1 K hK)
    have hBa : B ≤ Subgroup.centralizer ({a} : Set G) := (h.E_le_centralizer haB).trans' h.B_le_E
    have hBKC := le_thetaQuotCentralizer_of_residual_eq h.B_le_C hBa hK hBK heq
    have hSθ : ⁅S, B⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a}) := by
      have h1 : ⁅K, B⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K :=
        (commutator_le_theta_iff hBK).mpr hBKC
      rw [theta_eq_inf_of_mem_thetaComponentsAt hK] at h1
      exact (Subgroup.commutator_mono hSK le_rfl).trans (h1.trans inf_le_right)
    have h0 := commutator_eq_bot_of_mem_partTwoS h.mem_S (h.B_le_A haB) ha1 h.B_le_A hSθ hS'2 hBS'
    rw [hS'eq] at h0
    exact h0

theorem B_le_centralizer {a : G} (haB : a ∈ B) : B ≤ Subgroup.centralizer ({a} : Set G) :=
  h.B_le_E.trans (h.E_le_centralizer haB)

theorem sectionFourHyp {a : G} (ha1 : a ≠ 1) :
    SectionFourHyp (Subgroup.centralizer ({a} : Set G)) :=
  h.standing.toTheoremFourHyp.sectionFourHyp
    (centralizer_ne_top_of_ne_one h.standing.toTheoremFourHyp ha1)

theorem three_dvd_card_center {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) :
    3 ∣ Nat.card (Subgroup.center (Subgroup.centralizer ({a} : Set G))) := by
  set a' : Subgroup.centralizer ({a} : Set G) :=
    ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have ha'3 : orderOf a' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (h.elemB.2 a haB) ha1
  have hle : Subgroup.zpowers a' ≤ Subgroup.center (Subgroup.centralizer ({a} : Set G)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, ha'3] at this

theorem le_sup_thetaQuotCentralizer (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) {a : G}
    (haB : a ∈ B) (ha1 : a ≠ 1) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    {V : Subgroup G} (hV2 : IsPGroup 2 V) (hVa : V ≤ Subgroup.centralizer {a})
    (hEV : E ≤ Subgroup.normalizer (V : Set G)) (hVB : V ≤ ⁅V, B⁆) :
    V ≤ Subgroup.normalizer (K : Set G) ∧ V ≤ K ⊔ thetaQuotCentralizer K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAK := h.A_le_normalizer h45 haB ha1
  have hVK : V ≤ Subgroup.normalizer (K : Set G) :=
    hVB.trans (commutator_le_normalizer_of_mem_thetaComponentsAt (X := V) hVa
      (fun L' hL' => h.B_le_A.trans (hAK L' hL')) hK)
  refine ⟨hVK, ?_⟩
  set H := Subgroup.centralizer ({a} : Set G) with hH
  obtain ⟨hKH, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have hBH : B ≤ H := h.B_le_centralizer haB
  have hH4 : SectionFourHyp H := h.sectionFourHyp ha1
  have h3Z : 3 ∣ Nat.card (Subgroup.center H) := by
    set a' : H := ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have ha'3 : orderOf a' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (h.elemB.2 a haB) ha1
    have hle : Subgroup.zpowers a' ≤ Subgroup.center H := by
      rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, ha'3] at this
  have hXK : ∀ K' ∈ thetaComponents 3 H, B.subgroupOf H ≤ Subgroup.normalizer (K' : Set H) := by
    intro K' hK'' x hx
    exact mem_normalizer_of_mem_normalizer_map
      (h.B_le_A.trans (hAK (K'.map H.subtype) ⟨K', hK'', rfl⟩) (Subgroup.mem_subgroupOf.mp hx))
  have hBV : ⁅B, V⁆ = V := by
    rw [Subgroup.commutator_comm]
    exact le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (h.B_le_E.trans hEV)) hVB
  have hV' : V.subgroupOf H ∈ invariantPiSubgroups ⊤ (B.subgroupOf H) (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top,
      hV2.comap_of_injective H.subtype H.subtype_injective,
      subgroupOf_le_normalizer_subgroupOf (h.B_le_E.trans hEV)⟩
  have hVB' : ⁅B.subgroupOf H, V.subgroupOf H⁆ = V.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hBH,
      Subgroup.map_subgroupOf_eq_of_le hVa]
    exact hBV
  have h49' := h49 H hH4 h3Z (K.subgroupOf H) hK' (B.subgroupOf H)
    (h.isPGroup_B.comap_of_injective H.subtype H.subtype_injective) hXK (V.subgroupOf H) hV' hVB'
  have h1 := Subgroup.map_mono (f := H.subtype) h49'
  rw [Subgroup.map_subgroupOf_eq_of_le hVa, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hKH] at h1
  refine h1.trans (sup_le_sup_left ?_ K)
  have h2 := map_thetaQuotCentralizer_le (K.subgroupOf H)
  rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at h2

theorem le_thetaQuotCentralizer (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) {a : G}
    (haB : a ∈ B) (ha1 : a ≠ 1) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    (hLK : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K)
    {V : Subgroup G} (hV2 : IsPGroup 2 V) (hVa : V ≤ Subgroup.centralizer {a})
    (hEV : E ≤ Subgroup.normalizer (V : Set G)) (hVB : V ≤ ⁅V, B⁆) :
    V ≤ thetaQuotCentralizer K := by
  obtain ⟨hVK, hVLC⟩ := h.le_sup_thetaQuotCentralizer h45 h49 haB ha1 hK hV2 hVa hEV hVB
  by_contra hVC
  obtain ⟨U, hU, hUB⟩ := exists_invariant_two_subgroup_not_le_theta_of_le h.isPGroup_E
    (h.E_le_normalizer h45 haB ha1 K hK) hV2 hEV hVK hVLC h.B_le_E hVB hVC
  rw [h.commutator_eq_bot h45 haB ha1 hK hLK hU] at hUB
  exact hUB bot_le

theorem A_le_centralizer_B : A ≤ Subgroup.centralizer (B : Set G) :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr fun β hβ =>
    congrArg Subtype.val (h.elemA.1.is_comm.comm ⟨β, h.B_le_A hβ⟩ ⟨x, hx⟩)

theorem exists_ne_one : ∃ b ∈ B, b ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
  have := h.cardB
  rw [hbot, Subgroup.card_bot] at this
  norm_num at this

theorem sectionFourHyp_B : SectionFourHyp (Subgroup.centralizer (B : Set G)) := by
  obtain ⟨b, hbB, hb1⟩ := h.exists_ne_one
  refine h.standing.toTheoremFourHyp.sectionFourHyp fun htop => ?_
  apply centralizer_ne_top_of_ne_one h.standing.toTheoremFourHyp hb1
  rw [eq_top_iff, ← htop]
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)

theorem exists_Z' (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) :
    ∃ Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)),
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (B : Set G)) ≤ Z' ∧
      E ≤ Subgroup.normalizer (Z' : Set G) ∧
      ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
        inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K → Z' ≤ K := by
  set Z := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (B : Set G)) with hZdef
  have hZ := residual_inf_centralizer_mem_thetaComponentsIn h.mem_L h.isPGroup_B h.B_le_C
  have hLp := isPerfect_of_mem_thetaComponentsAt h.mem_L
  have hLq := isQuasisimple_of_mem_thetaComponentsAt h.mem_L
  have hZp : Group.IsPerfect Z := isPerfect_inSubgroup_perfectResidual _
  have hZ1 : Z ≠ ⊥ := residual_inf_centralizer_ne_bot hLp hLq h.isPGroup_B h.B_le_C
  have hAn := exists_card_eq_of_mem_partTwoF h.mem_S.1
  obtain ⟨Z', hZ', hZZ'⟩ := exists_le_mem_thetaComponentsIn h48 h.sectionFourHyp_B
    h.A_le_centralizer_B h.elemA hAn h.a₀_mem h.a₀_ne hZ
  refine ⟨Z', hZ', hZZ', ?_, ?_⟩
  · exact le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 h.sectionFourHyp_B
      h.E_le_centralizer_B h.elemE ⟨3, le_rfl, by rw [h.cardE]; norm_num⟩ Z' hZ'
  · intro a haB ha1 K hK hLK
    obtain ⟨a', ha'B, ha'1, -, hCeq⟩ := exists_centralizer_eq_inf h.elemB h.cardB haB ha1
    have hZ'' : Z' ∈ thetaComponentsIn
        (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {a'}) := hCeq ▸ hZ'
    obtain ⟨K'', hK'', hZ'K''⟩ := exists_le_mem_thetaComponentsIn h48 (h.sectionFourHyp ha1)
      (h.A_le_centralizer (h.B_le_A haB)) h.elemA hAn (h.B_le_A ha'B) ha'1 hZ''
    have heq := eq_of_mem_thetaComponentsIn_of_le hK'' hK hZp hZ1 (hZZ'.trans hZ'K'')
      ((residual_inf_centralizer_le_residual haB).trans hLK)
    exact heq ▸ hZ'K''

theorem exists_R₀ : ∃ b ∈ B, b ≠ 1 ∧ ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ IsPGroup 2 R₀ ∧
    R₀ ≤ Subgroup.centralizer {b} ∧ E ≤ Subgroup.normalizer (R₀ : Set G) ∧ ⁅R₀, B⁆ = R₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U₀, hU₀1, hU₀2, hEU₀⟩ := h.mem_E.1.2.2
  set N₀ := Subgroup.normalizer (U₀ : Set G) with hN₀
  set Q₀ := inSubgroup (CFSG.pCore 2) N₀ with hQ₀
  have hQ₀2 : IsPGroup 2 Q₀ := CFSG.pCore_isPGroup.map _
  have hN₀Q₀ : N₀ ≤ Subgroup.normalizer (Q₀ : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 N₀))
  have hEQ₀ : E ≤ Subgroup.normalizer (Q₀ : Set G) := hEU₀.trans hN₀Q₀
  have hBQ₀ : B ≤ Subgroup.normalizer (Q₀ : Set G) := h.B_le_E.trans hEQ₀
  have hfaith : B ⊓ Subgroup.centralizer (Q₀ : Set G) = ⊥ := by
    have hc := h.standing.charTwoType N₀ ⟨U₀, hU₀1, hU₀2, rfl⟩
    rw [pCoreOf_two_eq_inSubgroup] at hc
    rw [eq_bot_iff]
    intro β hβ
    have hβQ : β ∈ Q₀ := hc ⟨hEU₀ (h.B_le_E hβ.1), hβ.2⟩
    exact Subgroup.mem_bot.mpr (Source.eq_one_of_pow_three_eq_one hQ₀2 hβQ (h.elemB.2 β hβ.1))
  have hcop : Nat.Coprime 3 (Nat.card Q₀) := by
    obtain ⟨k, hk⟩ := hQ₀2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hex : ∃ b ∈ B, b ≠ 1 ∧ ⁅Q₀ ⊓ Subgroup.centralizer {b}, B⁆ ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hQB : Q₀ ≤ Subgroup.centralizer (B : Set G) :=
      Sec5.le_of_forall_inf_centralizer_le Nat.prime_three h.elemB (by rw [h.cardB]; norm_num)
        hBQ₀ hcop
        fun b hb hb1 => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hno b hb hb1)
    have hBC : B ≤ Subgroup.centralizer (Q₀ : Set G) := Subgroup.le_centralizer_iff.mp hQB
    have hB1 : B = ⊥ := by rw [← inf_eq_left.mpr hBC, hfaith]
    have := h.cardB
    rw [hB1, Subgroup.card_bot] at this
    norm_num at this
  obtain ⟨b, hbB, hb1, hR⟩ := hex
  set S₀ := Q₀ ⊓ Subgroup.centralizer ({b} : Set G) with hS₀
  have hEb := h.E_le_centralizer hbB
  have hES₀ : E ≤ Subgroup.normalizer (S₀ : Set G) :=
    (le_inf hEQ₀ (hEb.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hBS₀ : B ≤ Subgroup.normalizer (S₀ : Set G) := h.B_le_E.trans hES₀
  have hRS₀ : ⁅S₀, B⁆ ≤ S₀ := Subgroup.le_normalizer_iff_commutator_le_left.mp hBS₀
  have hS₀2 : IsPGroup 2 S₀ := hQ₀2.to_le inf_le_left
  refine ⟨b, hbB, hb1, ⁅S₀, B⁆, hR, hS₀2.to_le hRS₀, hRS₀.trans inf_le_right, fun e he =>
    Source.mem_normalizer_commutator (hES₀ he) (h.E_le_normalizer_B he), ?_⟩
  have hcop' : (Nat.card B).Coprime (Nat.card S₀) := by
    obtain ⟨k, hk⟩ := hS₀2.exists_card_eq
    rw [h.cardB, hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  exact CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime S₀ B hcop' hBS₀

theorem exists_R_Y (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    {Z' : Subgroup G} (hZ' : Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (hZZ' : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (B : Set G)) ≤ Z')
    (hEZ' : E ≤ Subgroup.normalizer (Z' : Set G))
    (hZ'K : ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K → Z' ≤ K) :
    ∃ R Y : Subgroup G, R ≠ ⊥ ∧ IsPGroup 2 R ∧ E ≤ Subgroup.normalizer (R : Set G) ∧
      Group.IsPerfect Y ∧ Y ≠ ⊥ ∧ Y ≤ Z' ∧
      Z' ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)) ∧
      Y ≤ Subgroup.centralizer (R : Set G) ∧ E ≤ Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hbB, hb1, R₀, hR₀1, hR₀2, hR₀b, hER₀, hR₀B⟩ := h.exists_R₀
  obtain ⟨K, hK, hLK⟩ := exists_mem_thetaComponentsAt_residual_le h48 h.standing h.mem_S.1
    h.a₀_mem h.a₀_ne (h.B_le_A hbB) hb1 h.mem_L (h.B_le_C hbB)
  have hR₀C : R₀ ≤ thetaQuotCentralizer K :=
    h.le_thetaQuotCentralizer h45 h49 hbB hb1 hK hLK hR₀2 hR₀b hER₀ hR₀B.ge
  have hR₀K : R₀ ≤ Subgroup.normalizer (K : Set G) :=
    (h.le_sup_thetaQuotCentralizer h45 h49 hbB hb1 hK hR₀2 hR₀b hER₀ hR₀B.ge).1
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set θb := inSubgroup (aschbacherSolvableCore 3) Cb with hθb
  set N := R₀ ⊔ θb with hN
  have hEb := h.E_le_centralizer hbB
  have hBb : B ≤ Cb := h.B_le_E.trans hEb
  have hKb : K ≤ Cb := le_centralizer_of_mem_thetaComponentsAt hK
  have hR₀θb : R₀ ≤ Subgroup.normalizer (θb : Set G) := hR₀b.trans (le_normalizer_theta Cb)
  have hN3 : ¬ 3 ∣ Nat.card N := not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hR₀2
    hR₀θb (theta_solvable_and_not_dvd Cb).2
  have hNb : N ≤ Cb := sup_le hR₀b (theta_le Cb)
  have hEN : E ≤ Subgroup.normalizer (N : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro e he x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hER₀ he) x).mp hx)
    · intro e he x hx
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta Cb (hEb he)) x).mp hx)
  obtain ⟨P, hPsyl, hR₀P, hEP⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two h.isPGroup_E hN3 hEN le_sup_left hR₀2 hER₀
  have hPN : P ≤ N := hPsyl.1
  have hP2 : IsPGroup 2 P := hPsyl.2.1
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := h.B_le_E.trans hEP
  set R := ⁅P, B⁆ with hRdef
  have hRP : R ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hBP
  have hR2 : IsPGroup 2 R := hP2.to_le hRP
  have hER : E ≤ Subgroup.normalizer (R : Set G) := fun e he =>
    Source.mem_normalizer_commutator (hEP he) (h.E_le_normalizer_B he)
  have hR₀R : R₀ ≤ R := by
    rw [← hR₀B]
    exact Subgroup.commutator_mono hR₀P le_rfl
  have hR1 : R ≠ ⊥ := fun h0 => hR₀1 (le_bot_iff.mp (h0 ▸ hR₀R))
  have hPθ : P ⊓ θb ≤ Subgroup.centralizer (B : Set G) := by
    have hBPθ : B ≤ Subgroup.normalizer ((P ⊓ θb : Subgroup G) : Set G) :=
      (le_inf hBP (hBb.trans (le_normalizer_theta Cb))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_mem_partTwoS h.mem_S (h.B_le_A hbB) hb1 h.B_le_A inf_le_right
        (hP2.to_le inf_le_left) hBPθ)
  have hKR₀ : ⁅K, R₀⁆ ≤ θb := by
    have h1 := (commutator_le_theta_iff hR₀K).mpr hR₀C
    rw [theta_eq_inf_of_mem_thetaComponentsAt hK] at h1
    exact h1.trans inf_le_right
  set CB := Subgroup.centralizer (B : Set G) with hCB
  set T := inSubgroup (aschbacherSolvableCore 3) CB with hT
  set D := Subgroup.normalizer (P : Set G) ⊓ CB with hD
  have hZ'C : Z' ≤ CB := le_of_mem_thetaComponentsIn hZ'
  have hZ'K' : Z' ≤ K := hZ'K b hbB hb1 K hK hLK
  have hCBb : CB ≤ Cb := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)
  have hZ'N : Z' ≤ Subgroup.normalizer (N : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro z hz r hr
      have h1 : ⁅z, r⁆ ∈ θb := hKR₀ (Subgroup.commutator_mem_commutator (hZ'K' hz) hr)
      rw [show z * r * z⁻¹ = ⁅z, r⁆ * r by rw [commutatorElement_def]; group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hr)
    · intro z hz x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_theta Cb (hCBb (hZ'C hz))) x).mp hx)
  have hθCB : θb ⊓ CB ≤ T := by
    have hn : CB ≤ Subgroup.normalizer ((θb ⊓ CB : Subgroup G) : Set G) :=
      (le_inf (hCBb.trans (le_normalizer_theta Cb)) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have := (theta_solvable_and_not_dvd Cb).1
    have hsol : Group.IsSolvable (θb ⊓ CB : Subgroup G) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective _)
    have h3 : ¬ 3 ∣ Nat.card (θb ⊓ CB : Subgroup G) := fun h3 =>
      (theta_solvable_and_not_dvd Cb).2 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    exact le_theta_of_normal inf_le_right hn hsol h3
  have hDT : D ≤ Subgroup.normalizer (T : Set G) := inf_le_right.trans (le_normalizer_theta CB)
  have hPθb : P ≤ Subgroup.normalizer (θb : Set G) := (hPN.trans hNb).trans (le_normalizer_theta Cb)
  have hNP : N ≤ P ⊔ θb := by
    obtain ⟨P₀, hP₀⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hPsyl
    have h1 := le_sylow_sup_of_forall_pow_mem (Y := N) (le_sup_right : θb ≤ N)
      (sup_le hR₀θb Subgroup.le_normalizer) (fun y hy => exists_pow_mem_of_mem_sup hR₀2 hR₀θb hy)
      P₀
    rwa [hP₀] at h1
  have hFrat : Z' ≤ D ⊔ T := by
    intro z hz
    have hzC := hZ'C hz
    have hS' := fusionIsSylowIn_map_conj hPsyl (hZ'N hz)
    have hBPz : B ≤ Subgroup.normalizer
        ((P.map (MulAut.conj z).toMonoidHom : Subgroup G) : Set G) :=
      le_normalizer_map_conj hBP hzC
    obtain ⟨c, ⟨hcN, hcB⟩, hceq⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
      Nat.prime_three Nat.prime_two h.isPGroup_B hN3 (h.B_le_E.trans hEN) hPsyl hS' hBP hBPz
    have hd : c⁻¹ * z ∈ D :=
      ⟨inv_mul_mem_normalizer_of_map_conj_eq hceq, CB.mul_mem (CB.inv_mem hcB) hzC⟩
    obtain ⟨p, hpP, hpB, hpc⟩ := exists_mem_centralizer_inv_mul_mem h.isPGroup_B hBP
      (hBb.trans (le_normalizer_theta Cb)) hPθb (theta_solvable_and_not_dvd Cb).2
      (hNP hcN) hcB
    have hpD : p ∈ D := ⟨Subgroup.le_normalizer hpP, hpB⟩
    have htT : p⁻¹ * c ∈ T := hθCB ⟨hpc, CB.mul_mem (CB.inv_mem hpB) hcB⟩
    rw [show z = p * (p⁻¹ * c) * (c⁻¹ * z) by group]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hpD)
      (Subgroup.mem_sup_right htT)) (Subgroup.mem_sup_left hd)
  set W := (Z' ⊔ T) ⊓ D with hW
  set Y := inSubgroup perfectResidual W with hY
  have hYp : Group.IsPerfect Y := isPerfect_inSubgroup_perfectResidual W
  have hYW : Y ≤ W := inSubgroup_perfectResidual_le W
  have hYD : Y ≤ D := hYW.trans inf_le_right
  have hYZ' : Y ≤ Z' := le_of_isPerfect_of_le_sup_theta hZ' hYp (hYW.trans inf_le_left)
  have hZ'p := isPerfect_of_mem_thetaComponentsIn hZ'
  have hZ'W : Z' ≤ W ⊔ T := by
    intro z hz
    have hz' : z ∈ (D : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D T hDT]
      exact hFrat hz
    obtain ⟨d, hd, t, ht, rfl⟩ := hz'
    have hdW : d ∈ W := by
      refine ⟨?_, hd⟩
      rw [show d = d * t * t⁻¹ by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right (T.inv_mem ht))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hdW) (Subgroup.mem_sup_right ht)
  have hZ'Y : Z' ≤ Y ⊔ T := le_perfectResidual_sup hZ'p (inf_le_right.trans hDT) hZ'W
  have hZ1 : inSubgroup perfectResidual (L ⊓ CB) ≠ ⊥ :=
    residual_inf_centralizer_ne_bot (isPerfect_of_mem_thetaComponentsAt h.mem_L)
      (isQuasisimple_of_mem_thetaComponentsAt h.mem_L) h.isPGroup_B h.B_le_C
  have hY1 : Y ≠ ⊥ := by
    intro hY0
    rw [hY0, bot_sup_eq] at hZ'Y
    have := (theta_solvable_and_not_dvd CB).1
    have hsol : Group.IsSolvable Z' := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hZ'Y) (Subgroup.inclusion_injective _)
    have hZ'1 : Z' ≠ ⊥ := fun h0 => hZ1 (le_bot_iff.mp (h0 ▸ hZZ'))
    have : Nontrivial Z' := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ'1
    have := hZ'p
    exact Group.IsPerfect.not_isSolvable Z' hsol
  have hEW : E ≤ Subgroup.normalizer (W : Set G) := by
    have hE1 : E ≤ Subgroup.normalizer ((Z' ⊔ T : Subgroup G) : Set G) := by
      apply le_normalizer_sup_of_conj
      · intro e he x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hEZ' he) x).mp hx)
      · intro e he x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
          (le_normalizer_theta CB (h.E_le_centralizer_B he)) x).mp hx)
    have hE2 : E ≤ Subgroup.normalizer (D : Set G) :=
      (le_inf (hEP.trans (normalizer_le_normalizer_normalizer P))
        (h.E_le_centralizer_B.trans Subgroup.le_normalizer)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf hE1 hE2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) :=
    hEW.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hYC : Y ≤ CB := hYZ'.trans hZ'C
  have hYP : ⁅P, Y⁆ ≤ P :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hYD.trans inf_le_left)
  have hPYθ : ⁅P, Y⁆ ≤ θb := by
    calc ⁅P, Y⁆ ≤ ⁅R₀ ⊔ θb, K⁆ := Subgroup.commutator_mono hPN (hYZ'.trans hZ'K')
      _ ≤ ⁅R₀, K⁆ ⊔ θb :=
          commutator_sup_le_of_le_normalizer hR₀θb (hKb.trans (le_normalizer_theta Cb))
      _ ≤ θb := sup_le (by rw [Subgroup.commutator_comm]; exact hKR₀) le_rfl
  have h1 : ⁅⁅B, Y⁆, P⁆ = ⊥ := by
    have : ⁅B, Y⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYC
    rw [this, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅Y, P⁆, B⁆ = ⊥ := by
    rw [Subgroup.commutator_comm Y P]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ((le_inf hYP hPYθ).trans hPθ)
  have h3 : ⁅⁅P, B⁆, Y⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hYR : Y ≤ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.commutator_comm] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  exact ⟨R, Y, hR1, hR2, hER, hYp, hY1, hYZ', hZ'Y, hYR, hEY⟩

theorem false_of_R_Y_central (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : BThreePropertyCentral) {Z' R Y : Subgroup G}
    (hZ' : Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (hZ'K : ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K → Z' ≤ K)
    (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hER : E ≤ Subgroup.normalizer (R : Set G))
    (hYp : Group.IsPerfect Y) (hY1 : Y ≠ ⊥) (hYZ' : Y ≤ Z')
    (hZ'Y : Z' ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)))
    (hYR : Y ≤ Subgroup.centralizer (R : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set CB := Subgroup.centralizer (B : Set G) with hCB
  set T := inSubgroup (aschbacherSolvableCore 3) CB with hT
  set NR := Subgroup.normalizer (R : Set G) with hNR
  set W := inSubgroup (CFSG.pCore 2) NR with hW
  have hW2 : IsPGroup 2 W := CFSG.pCore_isPGroup.map _
  have hcopW : Nat.Coprime 3 (Nat.card W) := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hNRW : NR ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 NR))
  have hEW : E ≤ Subgroup.normalizer (W : Set G) := hER.trans hNRW
  have hBW : B ≤ Subgroup.normalizer (W : Set G) := h.B_le_E.trans hEW
  have hYNR : Y ≤ NR := hYR.trans (Subgroup.centralizer_le_normalizer _)
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := hYNR.trans hNRW
  have hZ'C : Z' ≤ CB := le_of_mem_thetaComponentsIn hZ'
  have hYC : Y ≤ CB := hYZ'.trans hZ'C
  have hBY : ⁅B, Y⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYC
  have hBNY : B ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBY).trans
      (Subgroup.centralizer_le_normalizer _)
  have hYNB : Y ≤ Subgroup.normalizer (B : Set G) :=
    hYC.trans (Subgroup.centralizer_le_normalizer _)
  have hWY : ⁅W, Y⁆ ≠ ⊥ := by
    intro h0
    rw [Subgroup.commutator_comm] at h0
    have hYCW : Y ≤ Subgroup.centralizer (W : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    have hc := h.standing.charTwoType NR ⟨R, hR1, hR2, rfl⟩
    rw [pCoreOf_two_eq_inSubgroup] at hc
    exact not_isPGroup_two_of_isPerfect hYp hY1 (hW2.to_le ((le_inf hYNR hYCW).trans hc))
  have hVa : ∀ a ∈ B, a ≠ 1 → ⁅⁅W ⊓ Subgroup.centralizer {a}, B⁆, Y⁆ = ⊥ := by
    intro a haB ha1
    obtain ⟨K, hK, hLK⟩ := exists_mem_thetaComponentsAt_residual_le h48 h.standing h.mem_S.1
      h.a₀_mem h.a₀_ne (h.B_le_A haB) ha1 h.mem_L (h.B_le_C haB)
    set S := W ⊓ Subgroup.centralizer ({a} : Set G) with hS
    have hEa := h.E_le_centralizer haB
    have hES : E ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf hEW (hEa.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hBS : B ≤ Subgroup.normalizer (S : Set G) := h.B_le_E.trans hES
    set V := ⁅S, B⁆ with hV
    have hVS : V ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hBS
    have hS2 : IsPGroup 2 S := hW2.to_le inf_le_left
    have hV2 : IsPGroup 2 V := hS2.to_le hVS
    have hVa' : V ≤ Subgroup.centralizer {a} := hVS.trans inf_le_right
    have hEV : E ≤ Subgroup.normalizer (V : Set G) := fun e he =>
      Source.mem_normalizer_commutator (hES he) (h.E_le_normalizer_B he)
    have hVB : ⁅V, B⁆ = V := by
      have hcop : (Nat.card B).Coprime (Nat.card S) := by
        obtain ⟨k, hk⟩ := hS2.exists_card_eq
        rw [h.cardB, hk]
        exact Nat.Coprime.pow_right k (by norm_num)
      exact CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime S B hcop hBS
    have hVC : V ≤ thetaQuotCentralizer K :=
      h.le_thetaQuotCentralizer h45 h49 haB ha1 hK hLK hV2 hVa' hEV hVB.ge
    have hVK : V ≤ Subgroup.normalizer (K : Set G) :=
      hVC.trans (thetaQuotCentralizer_le_normalizer K)
    have hYK : Y ≤ K := hYZ'.trans (hZ'K a haB ha1 K hK hLK)
    have hCBa : CB ≤ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
    have hYS : Y ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf hYW ((hYC.trans hCBa).trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hYV : Y ≤ Subgroup.normalizer (V : Set G) := fun y hy =>
      Source.mem_normalizer_commutator (hYS hy) (hYNB hy)
    have hVYV : ⁅V, Y⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hYV
    have hVYθ : ⁅V, Y⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a}) := by
      have h1 := (commutator_le_theta_iff hVK).mpr hVC
      rw [theta_eq_inf_of_mem_thetaComponentsAt hK] at h1
      calc ⁅V, Y⁆ ≤ ⁅V, K⁆ := Subgroup.commutator_mono le_rfl hYK
        _ = ⁅K, V⁆ := Subgroup.commutator_comm _ _
        _ ≤ _ := h1.trans inf_le_right
    have hBVY : B ≤ Subgroup.normalizer ((⁅V, Y⁆ : Subgroup G) : Set G) := fun β hβ =>
      Source.mem_normalizer_commutator (h.B_le_E.trans hEV hβ) (hBNY hβ)
    have h0 := commutator_eq_bot_of_mem_partTwoS h.mem_S (h.B_le_A haB) ha1 h.B_le_A hVYθ
      (hV2.to_le hVYV) hBVY
    have h1 : ⁅⁅B, Y⁆, V⁆ = ⊥ := by rw [hBY, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅Y, V⁆, B⁆ = ⊥ := by rw [Subgroup.commutator_comm Y V]; exact h0
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hVB] at h3
  set V₀ := W ⊓ CB with hV₀
  have hU : ⁅V₀, Y⁆ ≠ ⊥ := by
    intro hU0
    apply hWY
    have hWY' : W ≤ Subgroup.centralizer (Y : Set G) := by
      refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three h.elemB
        (by rw [h.cardB]; norm_num) hBW hcopW fun a haB ha1 => ?_
      set S := W ⊓ Subgroup.centralizer ({a} : Set G) with hS
      have hBS : B ≤ Subgroup.normalizer (S : Set G) :=
        (le_inf hBW ((h.B_le_centralizer haB).trans Subgroup.le_normalizer)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hcopS : Nat.Coprime 3 (Nat.card S) := by
        obtain ⟨k, hk⟩ := (hW2.to_le inf_le_left : IsPGroup 2 S).exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k (by norm_num)
      have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
        Nat.prime_three B S h.isPGroup_B hBS hcopS
      rw [← hfac]
      refine sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hVa a haB ha1)) ?_
      exact (inf_le_inf_right CB inf_le_left).trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hU0)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWY'
  have hV₀2 : IsPGroup 2 V₀ := hW2.to_le inf_le_left
  have hV₀sol : Group.IsSolvable V₀ := by
    have : Group.IsNilpotent V₀ := hV₀2.isNilpotent
    infer_instance
  have hYV₀ : Y ≤ Subgroup.normalizer (V₀ : Set G) :=
    (le_inf hYW (hYC.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hV₀Z' : V₀ ≤ Subgroup.normalizer (Z' : Set G) :=
    le_normalizer_of_isPerfect_le_of_mem_thetaComponentsIn hZ' hYZ' hYp hY1 inf_le_right hV₀sol
      hYV₀
  set θZ' := inSubgroup (aschbacherSolvableCore 3) Z' with hθZ'
  have hθZ'eq : θZ' = Z' ⊓ T := theta_eq_inf_of_mem_thetaComponentsIn hZ'
  have hZ'p := isPerfect_of_mem_thetaComponentsIn hZ'
  have hZ'q := isQuasisimple_of_mem_thetaComponentsIn hZ'
  have hZ'Yθ : Z' ≤ Y ⊔ θZ' := by
    intro z hz
    have hz' : z ∈ (Y : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y T
        (hYC.trans (le_normalizer_theta CB))]
      exact hZ'Y hz
    obtain ⟨y, hy, t, ht, rfl⟩ := hz'
    have htZ' : t ∈ Z' := by
      have := Z'.mul_mem (Z'.inv_mem (hYZ' hy)) hz
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
      (Subgroup.mem_sup_right (hθZ'eq ▸ ⟨htZ', ht⟩))
  set U := ⁅V₀, Y⁆ with hUdef
  have hUV₀ : U ≤ V₀ := Subgroup.le_normalizer_iff_commutator_le_left.mp hYV₀
  have hU2 : IsPGroup 2 U := hV₀2.to_le hUV₀
  have hUZ' : U ≤ Z' := by
    calc U ≤ ⁅V₀, Z'⁆ := Subgroup.commutator_mono le_rfl hYZ'
      _ = ⁅Z', V₀⁆ := Subgroup.commutator_comm _ _
      _ ≤ Z' := Subgroup.le_normalizer_iff_commutator_le_left.mp hV₀Z'
  have hYθZ' : Y ≤ Subgroup.normalizer (θZ' : Set G) := hYZ'.trans (le_normalizer_theta Z')
  have hV₀θZ' : V₀ ≤ Subgroup.normalizer (θZ' : Set G) :=
    hV₀Z'.trans (normalizer_le_normalizer_theta Z')
  have hUθ : ⁅U ⊔ θZ', Z'⁆ ≤ θZ' := by
    have hXZ' : U ⊔ θZ' ≤ Z' := sup_le hUZ' (theta_le Z')
    have hZ'X : Z' ≤ Subgroup.normalizer ((U ⊔ θZ' : Subgroup G) : Set G) := by
      refine hZ'Yθ.trans (sup_le ?_ ?_)
      · apply le_normalizer_sup_of_conj
        · intro y hy x hx
          exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
            (le_normalizer_commutator_right V₀ Y hy) x).mp hx)
        · intro y hy x hx
          exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hYθZ' hy) x).mp hx)
      · apply le_normalizer_sup_of_conj
        · intro t ht u hu
          have h1 : u⁻¹ * t * u⁻¹⁻¹ ∈ θZ' := (Subgroup.mem_normalizer_iff.mp
            (le_normalizer_theta Z' (Z'.inv_mem (hUZ' hu))) t).mp ht
          rw [show t * u * t⁻¹ = u * ((u⁻¹ * t * u⁻¹⁻¹) * t⁻¹) by group]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
            (Subgroup.mem_sup_right (θZ'.mul_mem h1 (θZ'.inv_mem ht)))
        · intro t ht x hx
          exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
            (le_normalizer_theta Z' (theta_le Z' ht)) x).mp hx)
    rcases sup_theta_eq_or_commutator_le hZ'q hXZ' hZ'X with hcov | hcen
    · exfalso
      have hUθN : U ≤ Subgroup.normalizer (θZ' : Set G) :=
        hUZ'.trans (le_normalizer_theta Z')
      have hUsol : Group.IsSolvable U := by
        have : Group.IsNilpotent U := hU2.isNilpotent
        infer_instance
      have hXsol := isSolvable_sup_of_le_normalizer hUθN (theta_solvable_and_not_dvd Z').1 hUsol
      rw [sup_assoc, sup_idem] at hcov
      rw [sup_comm] at hXsol
      have hsol : Group.IsSolvable Z' := hcov ▸ hXsol
      have hZ'1 : Z' ≠ ⊥ := fun h0 => hY1 (le_bot_iff.mp (h0 ▸ hYZ'))
      have : Nontrivial Z' := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ'1
      have := hZ'p
      exact Group.IsPerfect.not_isSolvable Z' hsol
    · exact hcen
  have hZ'V₀ : ⁅Z', V₀⁆ ≤ θZ' := by
    have hA : ⁅Z', V₀⁆ ≤ U ⊔ θZ' := by
      calc ⁅Z', V₀⁆ ≤ ⁅Y ⊔ θZ', V₀⁆ := Subgroup.commutator_mono hZ'Yθ le_rfl
        _ ≤ ⁅Y, V₀⁆ ⊔ θZ' := commutator_sup_le_of_le_normalizer hYθZ' hV₀θZ'
        _ = U ⊔ θZ' := by rw [Subgroup.commutator_comm Y V₀]
    have h1 : ⁅⁅Z', V₀⁆, Z'⁆ ≤ θZ' := (Subgroup.commutator_mono hA le_rfl).trans hUθ
    have h2 : ⁅⁅V₀, Z'⁆, Z'⁆ ≤ θZ' := by rw [Subgroup.commutator_comm V₀ Z']; exact h1
    have h3 := three_subgroups_mod (X := Z') (Y := V₀) (Z := Z') (N := θZ')
      (le_normalizer_theta Z') hV₀θZ' (le_normalizer_theta Z') h1 h2
    rwa [commutator_self_eq_of_isPerfect hZ'p] at h3
  have hUa : ∀ a ∈ B, a ≠ 1 →
      U ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
    intro a haB ha1
    obtain ⟨K, hK, hLK⟩ := exists_mem_thetaComponentsAt_residual_le h48 h.standing h.mem_S.1
      h.a₀_mem h.a₀_ne (h.B_le_A haB) ha1 h.mem_L (h.B_le_C haB)
    have hZ'Ka : Z' ≤ K := hZ'K a haB ha1 K hK hLK
    have hYK : Y ≤ K := hYZ'.trans hZ'Ka
    obtain ⟨a', ha'B, -, -, hCeq⟩ := exists_centralizer_eq_inf h.elemB h.cardB haB ha1
    have hCBa : CB ≤ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
    have hV₀K : V₀ ≤ Subgroup.normalizer (K : Set G) :=
      le_normalizer_of_isPerfect_le_of_mem_thetaComponentsIn hK hYK hYp hY1
        (inf_le_right.trans hCBa) hV₀sol hYV₀
    have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := le_centralizer_of_mem_thetaComponentsAt hK
    have hle : K ⊓ Subgroup.centralizer ({a'} : Set G) ≤ CB := by
      rw [hCB, hCeq]
      exact inf_le_inf_right _ hKa
    have hZ'le : Z' ≤ K ⊓ Subgroup.centralizer ({a'} : Set G) :=
      le_inf hZ'Ka (hZ'C.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha'B)))
    have hsn : (Z'.subgroupOf (K ⊓ Subgroup.centralizer ({a'} : Set G))).IsSubnormal := by
      have heq : Z'.subgroupOf (K ⊓ Subgroup.centralizer ({a'} : Set G)) =
          (Z'.subgroupOf CB).comap (Subgroup.inclusion hle) := by
        ext m
        simp [Subgroup.mem_subgroupOf]
      rw [heq]
      exact (mem_thetaComponentsIn_iff.mp hZ').2.2.1.comap _
    have hB3' := hB3 G (Subgroup.centralizer ({a} : Set G)) (h.sectionFourHyp ha1)
      (h.three_dvd_card_center haB ha1) K hK a' (h.B_le_centralizer haB ha'B) (h.elemB.2 a' ha'B)
      (h.B_le_A.trans (h.A_le_normalizer h45 haB ha1 K hK) ha'B) Z' hZ'le hZ'p hsn hZ'q
    set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
    have hZ'θK : Z' ≤ Subgroup.normalizer (θK : Set G) := hZ'Ka.trans (le_normalizer_theta K)
    have hV₀θK : V₀ ≤ Subgroup.normalizer (θK : Set G) :=
      hV₀K.trans (normalizer_le_normalizer_theta K)
    have h1 : ⁅⁅Z', V₀⁆, Z'⁆ ≤ θK := (Subgroup.commutator_mono hZ'V₀ le_rfl).trans hB3'
    have h2 : ⁅⁅V₀, Z'⁆, Z'⁆ ≤ θK := by rw [Subgroup.commutator_comm V₀ Z']; exact h1
    have h3 := three_subgroups_mod (X := Z') (Y := V₀) (Z := Z') (N := θK) hZ'θK hV₀θK hZ'θK h1 h2
    rw [commutator_self_eq_of_isPerfect hZ'p] at h3
    have hθKa :
        θK ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
      rw [hθK, theta_eq_inf_of_mem_thetaComponentsAt hK]
      exact inf_le_right
    calc U ≤ ⁅V₀, Z'⁆ := Subgroup.commutator_mono le_rfl hYZ'
      _ = ⁅Z', V₀⁆ := Subgroup.commutator_comm _ _
      _ ≤ θK := h3
      _ ≤ _ := hθKa
  have hUT : U ≤ thetaT 3 B := by
    simp only [thetaT]
    exact le_iInf fun a => le_iInf fun haB => le_iInf fun ha1 => hUa a haB ha1
  have hodd : Odd (Nat.card (thetaT 3 B)) := h.mem_S.2.2 B h.B_le_A h.cardB
  obtain ⟨k, hk⟩ := hU2.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le hUT
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
  rw [hk0, pow_zero] at hk
  exact hU (Subgroup.eq_bot_of_card_eq _ hk)

theorem false_of_R_Y (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : BThreeProperty) {Z' R Y : Subgroup G}
    (hZ' : Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (hZ'K : ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K → Z' ≤ K)
    (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hER : E ≤ Subgroup.normalizer (R : Set G))
    (hYp : Group.IsPerfect Y) (hY1 : Y ≠ ⊥) (hYZ' : Y ≤ Z')
    (hZ'Y : Z' ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)))
    (hYR : Y ≤ Subgroup.centralizer (R : Set G)) : False :=
  h.false_of_R_Y_central h45 h48 h49 (bThreePropertyCentral_of_bThreeProperty hB3) hZ' hZ'K hR1
    hR2 hER hYp hY1 hYZ' hZ'Y hYR

end Ctx65

theorem rank3II_6_5_one (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : BThreeProperty) (hG : PartTwoStanding G) {A : Subgroup G} (hA : A ∈ partTwoS G)
    {L : Subgroup G} (hL : L ∈ thetaComponentFamily 3 A) {B : Subgroup G}
    (hBab : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBAL : B ≤ A ⊓ thetaQuotCentralizer L) {E : Subgroup G}
    (hE : E ∈ collectionIn (partTwoE G) (A ⊔ L)) (hBE : B ≤ E) :
    ∃ b ∈ B, b ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 b,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K ∧
      ∃ S ∈ invariantPiSubgroups K E (piOf 2), S ≠ ⊥ ∧ ⁅S, B⁆ = S := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀A, ha₀1, hLa₀⟩ := mem_thetaComponentFamily_iff.mp hL
  have h : Ctx65 G A L B E a₀ := ⟨hG, hA, ha₀A, ha₀1, hLa₀, hBab, hB9, hBAL, hE, hBE, hcon⟩
  obtain ⟨Z', hZ', hZZ', hEZ', hZ'K⟩ := h.exists_Z' h45 h48
  obtain ⟨R, Y, hR1, hR2, hER, hYp, hY1, hYZ', hZ'Y, hYR, -⟩ :=
    h.exists_R_Y h45 h48 h49 hZ' hZZ' hEZ' hZ'K
  exact h.false_of_R_Y h45 h48 h49 hB3 hZ' hZ'K hR1 hR2 hER hYp hY1 hYZ' hZ'Y hYR

theorem rank3II_6_5 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : BThreeProperty) : Item6_5 := by
  intro G _ _ hG A hA L hL B hBab hB9 hBAL
  exact ⟨fun E hE hBE => rank3II_6_5_one h45 h48 h49 hB3 hG hA hL hBab hB9 hBAL hE hBE,
    fun hno => rank3II_6_5_two h45 h48 hG hA hL hBab hB9 hBAL hno⟩

theorem rank3II_6_6_of_inputs (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : BThreeProperty) : Item6_6 :=
  rank3II_6_6 (rank3II_6_5 h45 h48 h49 hB3)

theorem rank3II_6_5_one_central (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : BThreePropertyCentral) (hG : PartTwoStanding G) {A : Subgroup G}
    (hA : A ∈ partTwoS G) {L : Subgroup G} (hL : L ∈ thetaComponentFamily 3 A) {B : Subgroup G}
    (hBab : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBAL : B ≤ A ⊓ thetaQuotCentralizer L) {E : Subgroup G}
    (hE : E ∈ collectionIn (partTwoE G) (A ⊔ L)) (hBE : B ≤ E) :
    ∃ b ∈ B, b ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 b,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K ∧
      ∃ S ∈ invariantPiSubgroups K E (piOf 2), S ≠ ⊥ ∧ ⁅S, B⁆ = S := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀A, ha₀1, hLa₀⟩ := mem_thetaComponentFamily_iff.mp hL
  have h : Ctx65 G A L B E a₀ := ⟨hG, hA, ha₀A, ha₀1, hLa₀, hBab, hB9, hBAL, hE, hBE, hcon⟩
  obtain ⟨Z', hZ', hZZ', hEZ', hZ'K⟩ := h.exists_Z' h45 h48
  obtain ⟨R, Y, hR1, hR2, hER, hYp, hY1, hYZ', hZ'Y, hYR, -⟩ :=
    h.exists_R_Y h45 h48 h49 hZ' hZZ' hEZ' hZ'K
  exact h.false_of_R_Y_central h45 h48 h49 hB3 hZ' hZ'K hR1 hR2 hER hYp hY1 hYZ' hZ'Y hYR

theorem rank3II_6_5_central (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : BThreePropertyCentral) : Item6_5 := by
  intro G _ _ hG A hA L hL B hBab hB9 hBAL
  exact ⟨fun E hE hBE => rank3II_6_5_one_central h45 h48 h49 hB3 hG hA hL hBab hB9 hBAL hE hBE,
    fun hno => rank3II_6_5_two h45 h48 hG hA hL hBab hB9 hBAL hno⟩

theorem rank3II_6_6_of_central (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : BThreePropertyCentral) : Item6_6 :=
  rank3II_6_6 (rank3II_6_5_central h45 h48 h49 hB3)

end CFSG.RankThree.PartTwo.Sec6

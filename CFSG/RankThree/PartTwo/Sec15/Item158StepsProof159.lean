module

import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec15.HypS
public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

section Defs

variable {G : Type} [Group G] [Finite G]

structure Ctx159 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop extends Sec15R G A c L where
  irreducible : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L))
  card_inf : Nat.card (A ⊓ L : Subgroup G) = 9
  normalizer_le_inf :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G)
  isElemAbelian_oThree : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A)
  card_oThree : Nat.card (oThreeWStar A) = 9
  wStar_eq : wStar A = oThreeWStar A ⊔
    Sec4.autIn (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
  omegaA_eq : omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c)
  ncard_omegaA : (omegaA A).ncard = 9
  prod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)
  types : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)
  not_three : ¬ (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) ∧ CFSG.Open.pCoreOf 2 L ≠ ⊥)

@[expose] def IsW159 (A L : Subgroup G) (w : G) : Prop :=
  w ∈ Subgroup.normalizer (A : Set G) ∧ (∃ k : ℕ, w ^ 3 ^ k = 1) ∧
    (∀ b ∈ A ⊓ L, w * b = b * w) ∧ w ∉ Subgroup.centralizer (A : Set G)

end Defs

@[expose] noncomputable def Step159Y0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → (scriptY0 A (lB A)).Nonempty

@[expose] noncomputable def Step159W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → ∃ w : G, IsW159 A L w ∧
      ∃ V ∈ scriptY3 A (lB A), w ∈ Subgroup.normalizer (V : Set G)

@[expose] noncomputable def Step159Claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → ∀ w : G, IsW159 A L w → ∀ V ∈ scriptY3 A (lB A),
      w ∈ Subgroup.normalizer (V : Set G) → oPrimeResidualOf 3 V = ⊥

@[expose] noncomputable def Step159S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → ∀ w : G, IsW159 A L w →
      (∀ V ∈ scriptY3 A (lB A), w ∈ Subgroup.normalizer (V : Set G) →
        oPrimeResidualOf 3 V = ⊥) →
      (∃ V ∈ scriptY3 A (lB A), w ∈ Subgroup.normalizer (V : Set G)) →
        ∃ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), w ∈ Subgroup.normalizer (S : Set G)

namespace Proof159

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isW159_conj {A L : Subgroup G}
    (hBW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G))
    {w x : G} (hw : IsW159 A L w) (hx : x ∈ Subgroup.normalizer (A : Set G)) :
    IsW159 A L (x * w * x⁻¹) := by
  obtain ⟨hwA, ⟨k, hk⟩, hwB, hwC⟩ := hw
  refine ⟨mul_mem (mul_mem hx hwA) (inv_mem hx), ⟨k, ?_⟩, fun b hb => ?_, fun hC => ?_⟩
  · rw [conj_pow, hk, mul_one, mul_inv_cancel]
  · have hb' : x⁻¹ * b * x⁻¹⁻¹ ∈ A ⊓ L :=
      (Subgroup.mem_normalizer_iff.mp (hBW (inv_mem hx)) b).mp hb
    have hcomm := hwB _ hb'
    calc x * w * x⁻¹ * b = x * (w * (x⁻¹ * b * x⁻¹⁻¹)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * b * x⁻¹⁻¹) * w) * x⁻¹ := by rw [hcomm]
      _ = b * (x * w * x⁻¹) := by group
  · apply hwC
    rw [Subgroup.mem_centralizer_iff] at hC ⊢
    intro a ha
    have ha' : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hx a).mp ha
    have hcomm := hC _ ha'
    calc a * w = x⁻¹ * (x * a * x⁻¹ * (x * w * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * w * x⁻¹ * (x * a * x⁻¹)) * x := by rw [hcomm]
      _ = w * a := by group

omit [Finite G] in
theorem mem_normalizer_map_conj {S : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (S : Set G)) (x : G) :
    x * w * x⁻¹ ∈
      Subgroup.normalizer ((S.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  have hS : S.map (MulAut.conj w).toMonoidHom = S := Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  change (S.map (MulAut.conj x).toMonoidHom).map (MulAut.conj (x * w * x⁻¹)).toMonoidHom =
    S.map (MulAut.conj x).toMonoidHom
  rw [Late.map_conj_map_conj, show x * w * x⁻¹ * x = x * w by group, ← Late.map_conj_map_conj,
    hS]

theorem delta_mem_scriptY3 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hM1 : CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) =
      {Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G)}) :
    delta A (lB A) (Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G)) ∈
      scriptY3 A (lB A) ∧
    Y ≤ oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hNX, hYX, -, hX2⟩ := facts153 h h149 hY
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hXdef
  set N := Subgroup.normalizer (X : Set G) with hNdef
  set V := delta A (lB A) N with hVdef
  obtain ⟨M₀, hM₀⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  have hM₀N : M₀ = N := by
    have := hM1 ▸ hM₀
    exact this
  have hN2 : N ∈ scriptY2 A := hM₀N ▸ (facts_of_mem_maximalTwoLocalsContaining h hM₀).2.2.1
  have hVN : V ≤ N := delta_le N
  have hVY : V ∈ scriptY A := by
    refine ⟨fun htop => hN2.1.1 (eq_top_iff.mpr (htop ▸ hVN)), ?_⟩
    exact le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hXV : X ≤ V := (oPrimeResidualOf_le_self 3 _).trans (delta_mono hNX)
  have hO2 : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 V :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXV)
      (hVN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X)
  refine ⟨⟨⟨hVY, fun h0 => hX2 (le_bot_iff.mp (h0 ▸ hO2))⟩, (delta_delta N).symm⟩, ?_⟩
  exact le_oPrimeResidualOf_delta hY.prop.1 (hYX.trans Subgroup.le_normalizer)

theorem mem_normalizer_delta {A K : Subgroup G} {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwK : w ∈ Subgroup.normalizer (K : Set G)) :
    w ∈ Subgroup.normalizer ((delta A (lB A) K : Subgroup G) : Set G) := by
  have hK : K.map (MulAut.conj w).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hwK
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  change (delta A (lB A) K).map (MulAut.conj w).toMonoidHom = delta A (lB A) K
  rw [Sec17.HeadProof.map_conj_delta hwA, hK]

end Proof159

section Facts

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IsW159.inf_centralizer_eq [Finite G] {A L : Subgroup G} {w : G} (hw : IsW159 A L w)
    (h27 : Nat.card A = 27) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    A ⊓ Subgroup.centralizer ({w} : Set G) = A ⊓ L := by
  have hBK : A ⊓ L ≤ A ⊓ Subgroup.centralizer ({w} : Set G) := fun b hb =>
    ⟨hb.1, Subgroup.mem_centralizer_singleton_iff.mpr (hw.2.2.1 b hb).symm⟩
  refine (Subgroup.eq_of_le_of_card_ge hBK ?_).symm
  rw [h9]
  have hdvd : Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h9d : 3 ^ 2 ∣ 3 ^ k := by
    rw [← hkc, show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
    exact Subgroup.card_dvd_of_le hBK
  have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h9d
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · rw [hkc, show k = 2 by omega]
    norm_num
  · exfalso
    have hkk : k = 3 := le_antisymm hk hk3
    have hAK : A ⊓ Subgroup.centralizer ({w} : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hkc, hkk]; norm_num)
    apply hw.2.2.2
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haK : a ∈ A ⊓ Subgroup.centralizer ({w} : Set G) := hAK.symm ▸ ha
    exact Subgroup.mem_centralizer_singleton_iff.mp haK.2

theorem Ctx159.not_le_inf {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) {F : Subgroup G}
    (hF : F ∈ omegaA A) : ¬ F ≤ A ⊓ L := by
  have hcL : c ∉ L := ctx.hypS.2.2 c ctx.zpowers_mem_omegaA L ctx.mem_lA
  rw [ctx.omegaA_eq] at hF
  obtain ⟨w, hw, rfl⟩ := hF
  intro hle
  apply hcL
  have h1 : w * c * w⁻¹ ∈ A ⊓ L := hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers c))
  have h2 : w⁻¹ * (w * c * w⁻¹) * w⁻¹⁻¹ ∈ A ⊓ L :=
    (Subgroup.mem_normalizer_iff.mp (ctx.normalizer_le_inf (inv_mem hw)) _).mp h1
  rw [show w⁻¹ * (w * c * w⁻¹) * w⁻¹⁻¹ = c by group] at h2
  exact h2.2

end Facts

end CFSG.RankThree.PartTwo.Sec15

module

public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofE
public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofComm
import CFSG.RankThree.PartTwo.Sec17.Item176ProofTwo
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

namespace Steps165

variable {G : Type} [Group G] [Finite G]

theorem coprime_three_of_isPGroup_two {X : Subgroup G} (hX : IsPGroup 2 X) :
    Nat.Coprime 3 (Nat.card X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  exact Nat.Coprime.pow_right _ (by norm_num)

theorem inf_centralizer_sup_le {N S B : Subgroup G} (hSN : S ≤ Subgroup.normalizer (N : Set G))
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hB3 : IsPGroup 3 B) (hcop : ¬ 3 ∣ Nat.card (S ⊓ N : Subgroup G)) :
    (N ⊔ S) ⊓ Subgroup.centralizer (B : Set G) ≤
      (N ⊓ Subgroup.centralizer (B : Set G)) ⊔ (S ⊓ Subgroup.centralizer (B : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro x ⟨hx, hxB⟩
  have hx' : x ∈ (N : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N S hSN]
    exact hx
  obtain ⟨n, hn, s, hs, rfl⟩ := hx'
  set α : ↥B →* MulAut ↥S := S.normalizerMonoidHom.comp (Subgroup.inclusion hBS) with hα
  have hαap : ∀ (b : ↥B) (y : ↥S), ((α b y : ↥S) : G) = (b : G) * y * (b : G)⁻¹ := fun b y =>
    S.normalizerMonoidHom_apply_apply_coe _ y
  set H := (S ⊓ N).subgroupOf S with hH
  have hHcop : ¬ 3 ∣ Nat.card H := by
    rwa [hH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hmemH : ∀ y : ↥S, y ∈ H ↔ (y : G) ∈ N := fun y =>
    ⟨fun hy => (Subgroup.mem_subgroupOf.mp hy).2,
      fun hy => Subgroup.mem_subgroupOf.mpr ⟨y.2, hy⟩⟩
  have hbs : ∀ b ∈ B, b * s * b⁻¹ * s⁻¹ ∈ N := by
    intro b hb
    have hcomm : b * (n * s) = n * s * b := Subgroup.mem_centralizer_iff.mp hxB b hb
    have hbn : b * n * b⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hBN hb) n).mp hn
    have e : b * s * b⁻¹ * s⁻¹ = (b * n * b⁻¹)⁻¹ * n := by
      have : b * s * b⁻¹ = (b * n * b⁻¹)⁻¹ * (n * s) := by
        calc b * s * b⁻¹ = (b * n * b⁻¹)⁻¹ * (b * (n * s) * b⁻¹) := by group
          _ = (b * n * b⁻¹)⁻¹ * (n * s) := by rw [hcomm]; group
      rw [this]
      group
    rw [e]
    exact N.mul_mem (N.inv_mem hbn) hn
  obtain ⟨s', hs'H, hs'fix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3
    hB3 α H hHcop ⟨s, hs⟩).1 (by
      intro b y hy
      rw [hmemH] at hy ⊢
      have hy' : (y : G) * s⁻¹ ∈ N := by simpa using hy
      have hb : (b : G) * ((y : G) * s⁻¹) * (b : G)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hBN b.2) _).mp hy'
      have e : (((α b y : ↥S) * (⟨s, hs⟩ : ↥S)⁻¹ : ↥S) : G) =
          ((b : G) * ((y : G) * s⁻¹) * (b : G)⁻¹) * ((b : G) * s * (b : G)⁻¹ * s⁻¹) := by
        rw [Subgroup.coe_mul, hαap, Subgroup.coe_inv]
        group
      rw [e]
      exact N.mul_mem hb (hbs b b.2))
  have hs'C : (s' : G) ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := congrArg Subtype.val (hs'fix ⟨b, hb⟩)
    rw [hαap] at h1
    calc b * (s' : G) = b * s' * b⁻¹ * b := by group
      _ = s' * b := by rw [h1]
  have hs'N : (s' : G) * s⁻¹ ∈ N := by
    have := (hmemH _).mp hs'H
    simpa using this
  have hn' : n * s * (s' : G)⁻¹ ∈ N := by
    have : n * s * (s' : G)⁻¹ = n * ((s' : G) * s⁻¹)⁻¹ := by group
    rw [this]
    exact N.mul_mem hn (N.inv_mem hs'N)
  have hn'C : n * s * (s' : G)⁻¹ ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.mul_mem _ hxB (Subgroup.inv_mem _ hs'C)
  have e : n * s = (n * s * (s' : G)⁻¹) * s' := by group
  show n * s ∈ _
  rw [e]
  exact Subgroup.mul_mem_sup ⟨hn', hn'C⟩ ⟨s'.2, hs'C⟩

theorem pCoreOf_mem_scriptQ (hQ : Step171CommQ) {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  set V := CFSG.Open.pCoreOf 2 Y₀ with hV
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := h.le_normalizer_y0.trans hMV
  have key : ∀ K : Subgroup G, K ≤ Subgroup.normalizer (Y₀ : Set G) →
      V ⊓ K ≤ pPrimeCoreOf 3 K := fun K hK =>
    le_pPrimeCoreOf inf_le_right
      (Proof169.le_normalizer_inf (hK.trans hMV) Subgroup.le_normalizer)
      (coprime_three_of_isPGroup_two (hV2.to_le inf_le_left))
  have hAC : ∀ B : Subgroup G, B ≤ A → A ≤ Subgroup.centralizer (B : Set G) := by
    intro B hBA a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.commute (hBA hb) ha
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three V).mpr ?_, hAV,
    fun B hB => ?_⟩
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_three_of_isPGroup_two hV2)
  unfold qBound
  by_cases hcB : c ∈ B
  ·
    have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)).trans
        (HeadProof.centralizer_c_le_M h)
    exact (key _ hCB).trans (le_sup_left.trans le_sup_left)
  have hAcB := Proof169.le_zpowers_sup_of_not_mem hB h.mem_A hcB
  set VB := V ⊓ Subgroup.centralizer (B : Set G) with hVB
  have hVBA : A ≤ Subgroup.normalizer (VB : Set G) :=
    Proof169.le_normalizer_inf hAV ((hAC B hB.1).trans Subgroup.le_normalizer)
  have hVB3 : ¬ 3 ∣ Nat.card VB :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_three_of_isPGroup_two (hV2.to_le inf_le_left))
  rw [Proof176.eq_commutator_sup hA h.mem_A hVB3 hVBA]
  refine sup_le ?_ ?_
  ·
    obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
      have hne : B ≠ ⊥ := by
        intro h0
        have h2 := hB.2
        rw [h0, Subgroup.card_bot, hA.2] at h2
        omega
      obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      exact ⟨b, hb, fun h1 => hb1 (Subtype.ext h1)⟩
    have hbA : b ∈ A := hB.1 hbB
    have hCBb : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)
    have hcomm : ⁅VB, Subgroup.zpowers c⁆ ≤ VB := Proof176.commutator_le_left h.mem_A hVBA
    by_cases hbM : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Y₀ : Set G)
    · have h1 : VB ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) :=
        (inf_le_inf_left V hCBb).trans (key _ hbM)
      have h2 : pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊓
          Subgroup.centralizer (B : Set G) ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
        le_pPrimeCoreOf inf_le_right
          (Proof169.le_normalizer_inf ((hCBb.trans Subgroup.le_normalizer).trans
            (normalizer_le_normalizer_pPrimeCoreOf 3 _)) Subgroup.le_normalizer)
          (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
            (coprime_card_pPrimeCoreOf 3 _))
      exact (hcomm.trans ((le_inf h1 inf_le_right).trans h2)).trans
        (le_sup_left.trans le_sup_left)
    · refine le_trans ?_ (hQ G A c L Y₀ h b hbA hb1 hbM B hB hbB hcB)
      exact le_inf (Subgroup.commutator_mono (inf_le_inf_left V hCBb) le_rfl)
        (hcomm.trans inf_le_right)
  ·
    have hCA : Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ≤
        Subgroup.centralizer (A : Set G) := by
      rintro x ⟨hxB, hxc⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hsub : Subgroup.zpowers c ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
        · intro z hz
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hxB z hz)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsub (hAcB hy))
    have hle : VB ⊓ Subgroup.centralizer ({c} : Set G) ≤ V ⊓ Subgroup.centralizer (A : Set G) :=
      le_inf (inf_le_left.trans inf_le_left)
        ((le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans hCA)
    exact (hle.trans (key _ (HeadProof.centralizer_le_M h))).trans
      (le_sup_right.trans le_sup_left)

end Steps165

theorem q0R165_of (hQ : Step171CommQ) : Q0R165 := by
  intro G _ _ A c L Y₀ h _ S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hVQ := Steps165.pCoreOf_mem_scriptQ hQ h
  set V := CFSG.Open.pCoreOf 2 Y₀ with hV
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hSV : S ≤ Subgroup.normalizer (V : Set G) :=
    (h.qStar_le S hS).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hSQ : S ∈ scriptQ A (lB A) := hS.prop.1.1
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hSQ.1.2.2
  have hVS2 : IsPGroup 2 (V ⊔ S : Subgroup G) := hV2.to_sup_of_normal_left' hS2 hSV
  have hVSQ : V ⊔ S ∈ scriptQ A (lB A) := by
    refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three _).mpr ?_,
      Sec14.le_normalizer_sup hVQ.1.2.2 hAS, fun B hB => ?_⟩
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (Steps165.coprime_three_of_isPGroup_two hVS2)
    have hcop : ¬ 3 ∣ Nat.card (S ⊓ V : Subgroup G) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (Steps165.coprime_three_of_isPGroup_two (hS2.to_le inf_le_left))
    refine (Steps165.inf_centralizer_sup_le hSV (hB.1.trans hAS) (hB.1.trans hVQ.1.2.2)
      (hA.isPGroup.to_le hB.1) hcop).trans ?_
    exact sup_le (hVQ.2 B hB) (hSQ.2 B hB)
  have hmem : V ⊔ S ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hVSQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hVS2⟩
  exact le_sup_left.trans (hS.2 hmem le_sup_right)

theorem step165E_of_commQ (hQ : Step171CommQ) (h153 : Item153MainR) (hU : CentU165)
    (hL : Tor165L) : Step165E :=
  step165E_of (q0R165_of hQ) h153 hU hL

end CFSG.RankThree.PartTwo.Sec16

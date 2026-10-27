module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofLayers
public import CFSG.RankThree.PartTwo.Sec20.Item20Res4ProofThompson
public import CFSG.RankThree.PartTwo.Sec3.Sims321CountDef
import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofComm
import CFSG.RankThree.PartTwo.Sec18.Item182
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped commutatorElement Pointwise

namespace Res4

variable {G : Type} [Group G]

theorem le_normalizer_omegaZOf_of_le_normalizer {X Y : Subgroup G}
    (h : Y ≤ Subgroup.normalizer (X : Set G)) :
    Y ≤ Subgroup.normalizer (Sec3.omegaZOf (CFSG.Open.pCoreOf 2 X) : Set G) := by
  have : (CFSG.omegaOneCenter (⊤ : Subgroup ↥(CFSG.Open.pCoreOf 2 X))).Characteristic :=
    omegaOneCenter_top_characteristic
  exact (h.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

theorem exists_mul_of_mem_sup {T B Q : Subgroup G} (hQT : Q ≤ T)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G))
    (hTBQ : T ≤ Subgroup.normalizer ((B ⊔ Q : Subgroup G) : Set G)) {g : G} (hg : g ∈ T ⊔ B) :
    ∃ t ∈ T, ∃ b ∈ B, g = t * b := by
  have hg' : g ∈ T ⊔ (B ⊔ Q) := (sup_le_sup_left le_sup_left T) hg
  have h1 : g ∈ (T : Set G) * ((B ⊔ Q : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T (B ⊔ Q) hTBQ]
    exact hg'
  obtain ⟨t, ht, x, hx, rfl⟩ := h1
  have h2 : x ∈ (B : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right B Q hBQ]
    exact hx
  obtain ⟨b, hb, q, hq, rfl⟩ := h2
  refine ⟨t * (b * q * b⁻¹),
    T.mul_mem ht (hQT ((Subgroup.mem_normalizer_iff.mp (hBQ hb) q).mp hq)), b, hb, by group⟩

theorem commutator_sup_le {Ω B Q : Subgroup G} (hBQ : B ≤ Subgroup.normalizer (Q : Set G))
    (hQΩ : ∀ q ∈ Q, ∀ ω ∈ Ω, q * ω = ω * q) : ⁅Ω, B ⊔ Q⁆ ≤ ⁅Ω, B⁆ := by
  rw [Subgroup.commutator_le]
  intro ω hω x hx
  have h2 : x ∈ (B : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right B Q hBQ]
    exact hx
  obtain ⟨b, hb, q, hq, rfl⟩ := h2
  rw [Res3.commutatorElement_mul_right]
  have : ⁅ω, q⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (hQΩ q hq ω hω).symm
  rw [this, mul_one, mul_inv_cancel, mul_one]
  exact Subgroup.commutator_mem_commutator hω hb

theorem mem_normalizer_sup_of [Finite G] {P Q : Subgroup G} {g : G}
    (hP : ∀ x ∈ P, g * x * g⁻¹ ∈ P ⊔ Q) (hQ : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hP x hx
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hQ x).mp hx)

end Res4

theorem item206One_core {G : Type} [Group G] [Finite G] (h321 : Sec3.Sims321.Item321Count)
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20 G A M L N c T)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hQ : ∃ Q : Subgroup (MulAut ↥(A ⊓ L)), Q ≤ Sec4.autIn M (A ⊓ L) ∧
      Nonempty (↥Q ≃* QuaternionGroup 2))
    (hBn : M ≤ Subgroup.normalizer (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G))
    (hKC : kTwenty M c ∈ oTwoComponentsIn M)
    (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M})
    (h1 : ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (h3 : KIsL3 M c) :
    ⁅vTwenty M c T, A ⊓ L⁆ = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  change ¬ ⁅⁅zTwenty T, kTwenty M c⁆, A ⊓ L⁆ = ⊥ at hne
  set K := kTwenty M c with hKdef
  set B := A ⊓ L with hBdef
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  set H := T ⊔ B with hHdef
  set S := CFSG.Open.pCoreOf 2 H with hSdef
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hTM : T ≤ M := hT.sylow.le
  have hAM : A ≤ M := le_of_hyp201 hT.toHyp201
  have hBM : B ≤ M := inf_le_left.trans hAM
  have hHM : H ≤ M := sup_le hTM hBM
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowOf hT.sylow
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hSH : S ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHS : H ≤ Subgroup.normalizer (S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hQS : Q ≤ S := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hQT.trans le_sup_left) (hHM.trans hMQ) hQ2
  have hTH : CFSG.ABGLocalTools.IsSylowOf 2 T H := hT.sylow.of_le le_sup_left hHM
  have hST : S ≤ T := pCoreOf_le_of_isSylowOf hTH
  have hSM : S ≤ M := hSH.trans hHM
  have hMR : M ≤ Subgroup.normalizer ((B ⊔ Q : Subgroup G) : Set G) := hBn
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hBM.trans hMQ
  have hAE := hT.mem_partTwoE.1
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAE.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => hAc a ha.1 b hb.1
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := fun b hb => hAE.2 b hb.1
  have hM := hT.mem_scriptM.1
  obtain ⟨P, hP, hP2, hMP⟩ := hM.1
  have hFM : CFSG.generalizedFitting M = CFSG.pCore 2 M :=
    generalizedFitting_eq_of_pCoreOf_le hT.charTwoType ⟨P, hP, hP2, hMP⟩ le_rfl
      (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
  set ΩM := Sec3.omegaZOf Q with hΩMdef
  obtain ⟨hΩMc, hΩM2, hΩMQ, hQΩM⟩ := omegaZOf_props Q
  have hMΩM : M ≤ Subgroup.normalizer (ΩM : Set G) :=
    Res4.le_normalizer_omegaZOf_of_le_normalizer Subgroup.le_normalizer
  have hZΩM : zTwenty T ≤ ΩM := omegaZOf_le_omegaZOf_pCoreOf hFM hT.sylow
  have hVΩM : ⁅zTwenty T, K⁆ ≤ ΩM :=
    Res3.commutator_le_of_le_of_le_normalizer hZΩM (hKM.trans hMΩM)
  set W := ⁅ΩM, B⁆ with hWdef
  have hWΩM : W ≤ ΩM := Res3.commutator_le_of_le_of_le_normalizer le_rfl (hBM.trans hMΩM)
  have hW1 : W ≠ ⊥ := fun h =>
    hne (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hVΩM le_rfl))
  have hQc : ∀ q ∈ Q, ∀ ω ∈ ΩM, q * ω = ω * q := fun q hq ω hω => hQΩM ω hω q hq
  have hWeq : ⁅ΩM, B ⊔ Q⁆ = W :=
    le_antisymm (Res4.commutator_sup_le hBQ hQc) (Subgroup.commutator_mono le_rfl le_sup_left)
  have hMW : M ≤ Subgroup.normalizer (W : Set G) := by
    rw [← hWeq]
    exact Res3.le_normalizer_commutator hMΩM hMR
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Res4.inf_centralizer_ne_bot hS2 ((hWΩM.trans hΩMQ).trans hQS) (hSM.trans hMW) hW1)
  have hcop : Nat.Coprime (Nat.card B) (Nat.card ΩM) := by
    obtain ⟨k, hk⟩ := (hQ2.to_le hΩMQ).exists_card_eq
    rw [h9, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hCWB : W ⊓ Subgroup.centralizer (B : Set G) = ⊥ := by
    have := CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot (B := B) (K := ΩM) hΩMc
      (hBM.trans hMΩM) hcop
    rwa [Subgroup.commutator_comm] at this
  have hvW : v ∈ W := hv.1
  have hvO : v ∈ Sec3.omegaG S :=
    ⟨hQS (hΩMQ (hWΩM hvW)), fun x hx => ((Subgroup.mem_centralizer_iff.mp hv.2) x hx).symm,
      hΩM2 v (hWΩM hvW)⟩
  have hV : ∃ b ∈ B, ∃ v ∈ Sec3.omegaG S, b * v * b⁻¹ ≠ v := by
    by_contra hall
    push Not at hall
    apply hv1
    apply Subtype.ext
    have hvB : v ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := hall b hb v hvO
      calc b * v = b * v * b⁻¹ * b := by group
        _ = v * b := by rw [h1]
    have : v ∈ W ⊓ Subgroup.centralizer (B : Set G) := ⟨hvW, hvB⟩
    rw [hCWB, Subgroup.mem_bot] at this
    exact this
  have hTB : ∀ g ∈ T ⊔ B, ∃ t ∈ T, ∃ b ∈ B, g = t * b := fun g hg =>
    Res4.exists_mul_of_mem_sup hQT hBQ (hTM.trans hMR) hg
  have htr : ∀ d ∈ B, ∀ d' ∈ B, d ≠ 1 → d' ≠ 1 →
      ∃ t ∈ T, t ∈ Subgroup.normalizer (B : Set G) ∧ t * d * t⁻¹ = d' :=
    fun d hd d' hd' hd1 hd'1 => Res3.exists_conj_eq_core hT h9 hQ hBn hd hd' hd1 hd'1
  have hJT : Sec3.jG T 0 ≤ S := sSup_le fun A' hA' =>
    Res4.le_pCoreOf_of_mem_famG hT.sylow.isPGroup h9 hBc hB3 hTB htr hV hA'
  have hKB : ∀ k ∈ K, ∀ b ∈ B, ⁅k, b⁆ ∈ CFSG.Open.pCoreOf 2 K := fun k hk b hb =>
    commutator_mem_pCoreOf_core hT hBn hKC h3 hk hb
  have hOKM : CFSG.Open.pCoreOf 2 K ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKM)
      (hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hTKS : T ⊓ K ≤ S := by
    have hR2 : IsPGroup 2 ((T ⊓ K) ⊔ Q : Subgroup G) :=
      hT.sylow.isPGroup.to_le (sup_le inf_le_left hQT)
    have hRN : H ≤ Subgroup.normalizer (((T ⊓ K) ⊔ Q : Subgroup G) : Set G) := by
      refine sup_le (fun t ht => ?_) (fun b hb => ?_)
      · refine Res4.mem_normalizer_sup_of (fun x hx => Subgroup.mem_sup_left ⟨?_, ?_⟩)
          (hMQ (hTM ht))
        · exact T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht)
        · exact (Subgroup.mem_normalizer_iff.mp (hMK (hTM ht)) x).mp hx.2
      · refine Res4.mem_normalizer_sup_of (fun x hx => ?_) (hBQ hb)
        have e : b * x * b⁻¹ = x * ⁅x⁻¹, b⁆ := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
          (Subgroup.mem_sup_right (hOKM (hKB _ (K.inv_mem hx.2) b hb)))
    exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (sup_le (inf_le_left.trans le_sup_left) (hQT.trans le_sup_left)) hRN hR2)
  set X := K ⊔ S with hXdef
  have hXM : X ≤ M := sup_le hKM hSM
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := hSM.trans hMK
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMK (hTM ht)),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHS (Subgroup.mem_sup_left ht))]
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMK (hBM hb)),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHS (Subgroup.mem_sup_right hb))]
  have hFX : CFSG.generalizedFitting X = CFSG.pCore 2 X :=
    generalizedFitting_eq_of_pCoreOf_le hT.charTwoType ⟨P, hP, hP2, hMP⟩ hXM
      (hQS.trans le_sup_right)
  have hSX : CFSG.ABGLocalTools.IsSylowOf 2 S X := by
    have hTXs : CFSG.ABGLocalTools.IsSylowOf 2 T (T ⊔ X) :=
      hT.sylow.of_le le_sup_left (sup_le hTM hXM)
    have hinf := hTXs.inf_of_le_normalizer le_sup_right (sup_le hTX Subgroup.le_normalizer)
    have hTXeq : T ⊓ X = S := by
      apply le_antisymm
      · rintro x ⟨hxT, hxX⟩
        have hx' : x ∈ (K : Set G) * (S : Set G) := by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left K S hSK]
          exact hxX
        obtain ⟨k, hk, s, hs, rfl⟩ := hx'
        have hkT : k ∈ T := by
          have := T.mul_mem hxT (T.inv_mem (hST hs))
          rwa [mul_inv_cancel_right] at this
        exact S.mul_mem (hTKS ⟨hkT, hk⟩) hs
      · exact le_inf hST le_sup_right
    rwa [hTXeq] at hinf
  have h2 := rank3II_20_5_2_core hT h204 h1
  have hKX : K ∈ oTwoComponentsIn X := by
    obtain ⟨-, ⟨-, hsn, -⟩⟩ := mem_oTwoComponentsIn_iff.mp hKC
    exact Sec18.mem_oTwoComponentsIn_of_le hKC le_sup_left
      (Sec18.isSubnormal_subgroupOf_of_le hsn hXM)
  obtain ⟨n, hn, hiso⟩ := h3
  set Ω := Sec3.omegaZOf (CFSG.Open.pCoreOf 2 X) with hΩdef
  obtain ⟨hΩc, hΩ2, hΩR, hRΩ⟩ := omegaZOf_props (CFSG.Open.pCoreOf 2 X)
  have hKΩ : K ≤ Subgroup.normalizer (Ω : Set G) := le_normalizer_omegaZOf_pCoreOf
  have hBΩ : B ≤ Subgroup.normalizer (Ω : Set G) :=
    Res4.le_normalizer_omegaZOf_of_le_normalizer hBX
  have hOKX : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
        (hSK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hZΩ : zTwenty T ≤ Ω := by
    have hZS : zTwenty T ≤ Sec3.omegaZOf S := by
      rintro _ ⟨z, hz, rfl⟩
      have hzQ : (z : G) ∈ Q := hΩMQ (hZΩM ⟨z, hz, rfl⟩)
      rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff] at hz
      refine ⟨⟨z, hQS hzQ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff]
      refine ⟨Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, Subtype.ext ?_⟩
      · have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz.1 ⟨y, hST y.2⟩)
        exact h1
      · simpa using congrArg Subtype.val hz.2
    exact hZS.trans (omegaZOf_le_omegaZOf_pCoreOf hFX hSX)
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c (mem_of_hyp201 hT.toHyp201)
  have hS3 : ∀ s ∈ {x | ∃ m ∈ M, x = m * c * m⁻¹}, s ^ 3 = 1 := by
    rintro _ ⟨m, -, rfl⟩
    rw [conj_pow, hc3, mul_one, mul_inv_cancel]
  have hBV : B ≤ Subgroup.normalizer ((⁅Ω, K⁆ : Subgroup G) : Set G) :=
    Res3.le_normalizer_commutator hBΩ (hBM.trans hMK)
  have hKBΩ : ∀ k ∈ K, ∀ b ∈ B, ∀ ω ∈ Ω, ⁅k, b⁆ * ω = ω * ⁅k, b⁆ :=
    fun k hk b hb ω hω => hRΩ ω hω _ (hOKX (hKB k hk b hb))
  have htr' : ∀ d ∈ B, ∀ d' ∈ B, d ≠ 1 → d' ≠ 1 → ∃ t : G,
      t ∈ Subgroup.normalizer (K : Set G) ∧ t ∈ Subgroup.normalizer (Ω : Set G) ∧
        t ∈ Subgroup.normalizer (B : Set G) ∧ t * d * t⁻¹ = d' := by
    intro d hd d' hd' hd1 hd'1
    obtain ⟨t, htT, htB, htd⟩ := htr d hd d' hd' hd1 hd'1
    exact ⟨t, hMK (hTM htT), Res4.le_normalizer_omegaZOf_of_le_normalizer hTX htT, htB, htd⟩
  have hne' : ⁅⁅Ω, K⁆, B⁆ ≠ ⊥ := fun h => hne (le_bot_iff.mp
    (h ▸ Subgroup.commutator_mono (Subgroup.commutator_mono hZΩ le_rfl) le_rfl))
  obtain ⟨W₁, W₂, W₃, h0, h12, h23, h3, hW₁, hW₂, hW₃, hp₁, hp₂, hp₃⟩ :=
    Res3.exists_layers (Ω := Ω) (Z := Ω) (K := K) (B := B)
      (S := {x | ∃ m ∈ M, x = m * c * m⁻¹}) rfl hS3 hΩc hΩ2
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hΩR) hKΩ le_rfl hBc hB3 h9 hBV hKBΩ
      htr' hne'
  obtain ⟨r, Vs, hVs, i, j, k, hij, hjk, hi, hj, hk⟩ :=
    Res3.exists_chief_three_noncentral h0 h12 h23 h3 hW₁ hW₂ hW₃ hKΩ hp₁ hp₂ hp₃
  rcases h321 G X K S n hFX hKX (hXM.trans hMK) hSX rfl hn hiso with
      (hJ | hV') | ⟨-, hch⟩
  ·
    have hJeq : Sec3.thompsonOf S = Sec3.thompsonOf T := by
      rw [Sec3.thompsonOf, Sec3.thompsonOf, Sec3.map_higherElemThompson,
        Sec3.map_higherElemThompson]
      exact Res4.jG_zero_eq_of_le hST hJT
    have hT1 : T ≠ ⊥ := by
      intro hbot
      have := pCoreOf_le_of_isSylowOf hT.sylow
      rw [hbot, le_bot_iff] at this
      exact pCoreOf_ne_bot_of_isMaximalTwoLocal hM this
    have : (CFSG.higherElemThompson T 0).Characteristic := higherElemThompson_zero_characteristic
    have hTJ : T ≤ Subgroup.normalizer (Sec3.thompsonOf T : Set G) :=
      Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
    have hKJ : K ≤ Subgroup.normalizer (Sec3.thompsonOf T : Set G) := by
      rw [← hJeq]
      exact le_sup_left.trans hJ
    refine h2 (CFSG.higherElemThompson T 0) this ?_ (sup_le hKJ hTJ)
    intro hbot
    apply thompsonOf_ne_bot hT.sylow.isPGroup hT1
    rw [Sec3.thompsonOf, hbot, Subgroup.map_bot]
  ·
    have hle : W₁ ≤ ⁅Ω, K⁆ :=
      hp₁.trans (Subgroup.commutator_mono (h12.le.trans (h23.le.trans h3)) le_rfl)
    rw [hV', le_bot_iff] at hle
    exact (ne_of_gt h0) hle
  ·
    exact hch r Vs hVs i j k hij hjk hi hj hk

section Main

theorem item206One_of_thompson (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    (h2031 : Item203One1) (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053)
    (h189 : Sec18.Item189) (h321 : Sec3.Sims321.Item321Count) : Item206One := by
  intro G _ _ A M L N c T hT hTN
  have h1 := h2051 G A M L N c T hT
  have h3 := h2053 G A M L N c T hT (rank3II_20_5_2_of h204 hT h1)
  obtain ⟨hKC, -, -⟩ := item189_case_one h189 hT h3
  exact item206One_core h321 hT.toCtx20 (card_inf_of_hyp201One h1812 h184 hT.hyp201One)
    (Res3.exists_quaternion_le_autIn h1812 h184 hT.hyp201One) (h2031 G A M L N c hT.hyp201One)
    hKC (h204 G A M L N c T hT) h1 h3

end Main

end CFSG.RankThree.PartTwo.Sec20

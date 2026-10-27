module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res5ProofDelta
public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofSeven
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofLd
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item64

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof
open scoped commutatorElement

@[expose] noncomputable def Sec17OThreeSolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ b ∈ A, b ≠ 1 →
      Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))

theorem sec17OThreeSolv_of_item174
    (h174 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item174 A (lB A)) : Sec17OThreeSolv := by
  intro G _ _ A c L Y₀ h b hb _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) with hO
  have hOQ : O ∈ scriptQ A (lB A) := Proof172.pPrimeCoreOf_centralizer_mem_scriptQ hA hb
  have hOΔ : O = delta A (lB A) O := le_antisymm (le_delta hOQ le_rfl) (delta_le O)
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  exact h174 G A c L Y₀ h O hOΔ hO3

theorem step177OThreeSolv_of_sec17 (h : Sec17OThreeSolv) : Step177OThreeSolv :=
  fun G _ _ A c L Y₀ hs _ _ _ _ _ _ _ _ _ _ b hb hb1 => h G A c L Y₀ hs b hb.1 hb1

@[expose] noncomputable def Step1712DeltaQ8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Subgroup.zpowers c⁆ = ⊥ → omegaA A = {Subgroup.zpowers c} →
      (∀ R ∈ fourGroups A, R ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) →
        R ≠ ⁅R, Subgroup.zpowers c⁆) →
        (∃ R ∈ fourGroups A, R = ⁅R, Subgroup.zpowers c⁆ ∧ R ∈ scriptQ A (lB A) ∧
          R ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G))) ∨
        ∃ a ∈ A, a ∉ Subgroup.zpowers c ∧
          (CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) ≠ ⊥ ∨
            ∃ Z ∈ fourGroups A, Z ∈ scriptQ A (lB A) ∧
              Z ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ⊓
                Subgroup.centralizer ({a} : Set G) ∧
              ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
                ⁅CFSG.Open.pCoreOf p (delta A (lB A) (Subgroup.centralizer ({a} : Set G))),
                  Z⁆ = ⊥)

namespace Proof17Res11

variable {G : Type} [Group G] [Finite G]

theorem coprime_three_of_isPGroup_two {P : Subgroup G} (hP : IsPGroup 2 P) :
    Nat.Coprime 3 (Nat.card P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem lB_le_of_omega {A L : Subgroup G} {c : G} (hΩ : omegaA A = {Subgroup.zpowers c})
    (hLc : L ∈ lA A c) (D : Subgroup G) : lB A D ≤ L := by
  refine iSup_le fun b => iSup_le fun d => iSup_le fun L' => iSup_le fun hcfg => ?_
  obtain ⟨-, hbΩ, hLb, -⟩ := hcfg
  have hbc : Subgroup.zpowers b = Subgroup.zpowers c := by
    rw [hΩ] at hbΩ
    exact hbΩ
  have hLL' : L = L' := by
    have hL' : L ∈ lA A b := (CFSG.RankThree.PartTwo.Sec14.lA_eq_of_zpowers_eq hbc) ▸ hLc
    rw [hLb] at hL'
    exact hL'
  subst hLL'
  exact (Subgroup.map_subtype_le _).trans inf_le_left

theorem delta_le_of {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (hbal : Step143Balance)
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c}) {b : G} (hbA : b ∈ A)
    (hb1 : b ≠ 1) (hbΩ : Subgroup.zpowers b ∉ omegaA A)
    (hOM : pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G)) :
    delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have hΔ := Proof17Res9.delta_le_sup_of_lB_le hbal h.toSec14Std hbA hb1 hbΩ (X := L)
    fun D _ _ => (lB_le_of_omega hΩ h.toSec13Data.mem_lA D).trans le_sup_right
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hOA : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G) :=
    (pPrimeCoreOf_le 3 _).trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)).trans
      ((centralizer_singleton_le_normalizer_zpowers c).trans h.normalizer_c_le))
  exact hΔ.trans (sup_le (sup_le hOM hOA) (h.le_y0.trans Subgroup.le_normalizer))

theorem mem_scriptQ_of_le_of_commutator_eq_bot {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {V Z : Subgroup G}
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hV2 : IsPGroup 2 V) (hVc : ⁅V, Subgroup.zpowers c⁆ = ⊥) (hZV : Z ≤ V)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) : Z ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hZ2 : IsPGroup 2 Z := hV2.to_le hZV
  have hZ3 : ¬ 3 ∣ Nat.card Z :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_three_of_isPGroup_two hZ2)
  have hVC : V ≤ Subgroup.centralizer ({c} : Set G) := by
    have h1 : V ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVc
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h1
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three Z).mpr hZ3, hAZ,
    fun D hD => ?_⟩
  rw [qBound]
  by_cases hcD : c ∈ D
  · have hCD : Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcD)).trans
        ((centralizer_singleton_le_normalizer_zpowers c).trans h.normalizer_c_le)
    have hle : V ⊓ Subgroup.centralizer (D : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)) :=
      le_pPrimeCoreOf inf_le_right (Late.le_normalizer_inf (hCD.trans hMV) Subgroup.le_normalizer)
        (coprime_three_of_isPGroup_two (hV2.to_le inf_le_left))
    exact (inf_le_inf_right _ hZV).trans (hle.trans (le_sup_left.trans le_sup_left))
  · have hAle := le_sup_zpowers_of_not_mem hA hD hcA hcD
    have hle : Z ⊓ Subgroup.centralizer (D : Set G) ≤ Z ⊓ Subgroup.centralizer (A : Set G) :=
      fun x hx => ⟨hx.1, mem_centralizer_of_le_sup hAle hx.2 (hVC (hZV hx.1))⟩
    exact hle.trans ((inf_centralizer_le_xA h.toSec14Std.maximal_isElemAbelian hZ3).trans
      (le_sup_right.trans le_sup_left))

end Proof17Res11

open Proof17Res11 in
theorem step1712DeltaF_of_q8 (hQ8 : Step1712DeltaQ8) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (hFaith : Step1712Faith) (h176 : Item176R)
    (hbal : Step143Balance) (hsol : Sec17OThreeSolv) : Step1712DeltaF := by
  intro G _ _ A c L Y₀ h V hV hVc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  obtain ⟨hVM, hMV, hVab⟩ := hV.prop
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hc3 : c ^ 3 = 1 := pow_three_of_std h hcA
  have hcord : orderOf c = 3 := h.toSec13Data.orderOf_eq
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
  have hAM : A ≤ M := Subgroup.le_normalizer.trans h.normalizer_le
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hVO : V ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVM hMV hV2
  by_cases hΩ : omegaA A = {Subgroup.zpowers c}
  swap
  ·
    exfalso
    have hT : TransOmegaThree A c := by
      rcases h1514 G A c L Y₀ h Y₀ h.mem_y0Star (hMeets G A c L Y₀ h) with
        ⟨-, -, hΩ', -⟩ | ⟨-, -, hT, -⟩ | ⟨-, -, -, hΩ', -⟩
      · exact absurd hΩ' hΩ
      · exact hT
      · exact absurd hΩ' hΩ
    obtain ⟨F, hF, hFc⟩ : ∃ F ∈ omegaA A, F ≠ Subgroup.zpowers c := by
      by_contra hcon
      push Not at hcon
      have hsub : omegaA A ⊆ {Subgroup.zpowers c} := fun F hF => hcon F hF
      have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
      rw [hT.1, Set.ncard_singleton] at this
      omega
    obtain ⟨w, hw, rfl⟩ := hT.2 F hF
    have hFeq : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom =
        Subgroup.zpowers (w * c * w⁻¹) := by
      rw [MonoidHom.map_zpowers]
      rfl
    have hfA : w * c * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw c).mp hcA
    have hfc : w * c * w⁻¹ ∉ Subgroup.zpowers c := by
      intro hfc
      apply hFc
      rw [hFeq]
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfc) ?_
      rw [← hFeq, Subgroup.card_map_of_injective (MulAut.conj w).injective]
    have hwV : w ∈ Subgroup.normalizer (V : Set G) := hMV (h.normalizer_le hw)
    have hVf : ⁅V, Subgroup.zpowers (w * c * w⁻¹)⁆ = ⊥ := by
      have := congrArg (Subgroup.map (MulAut.conj w).toMonoidHom) hVc
      rwa [Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer hwV, hFeq,
        Subgroup.map_bot] at this
    exact hFaith G A c L Y₀ h V hV hVc _ hfA hfc hVf
  by_cases hR : ∃ R ∈ fourGroups A, R ≤ CFSG.Open.pCoreOf 2 M ∧ R = ⁅R, Subgroup.zpowers c⁆
  swap
  · push Not at hR
    exact hQ8 G A c L Y₀ h V hV hVc hΩ hR
  obtain ⟨R, hR4, hRO2, hRc⟩ := hR
  obtain ⟨hAR, hRab, hRcard⟩ := mem_fourGroups_iff.mp hR4
  have hR2 : IsPGroup 2 R := Sec5.isPGroup_of_isElemAbelian hRab
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hRab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRsq : ∀ u ∈ R, u * u = 1 := fun u hu => by rw [← pow_two]; exact hRab.2 u hu
  have hcR : c ∈ Subgroup.normalizer (R : Set G) := hAR hcA
  have hR1 : R ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hRcard
    omega
  have hRm : R ∈ fourGroupsMinus A := ⟨hR4, le_antisymm
    (hRc.le.trans (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcA)))
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hAR)⟩
  set B' := A ⊓ Subgroup.centralizer (R : Set G) with hB'def
  have hB'9 : Nat.card B' = 9 := Sec6.card_inf_centralizer_of_mem_fourGroupsMinus hA hRm
  have hB' : IsHyperplane A B' := ⟨inf_le_left, by rw [hA.2, hB'9]⟩
  have hcB' : c ∉ B' := by
    intro hcB'
    apply hR1
    rw [hRc, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcB'.2 u hu)
  have hRB' : R ≤ Subgroup.centralizer (B' : Set G) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => (Subgroup.mem_centralizer_iff.mp hx.2 r hr).symm
  by_cases hRO : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B' : Set G))
  ·
    exact Or.inl ⟨R, hR4, hRc, mem_scriptQ_of_le
      (Proof17Res.pPrimeCoreOf_centralizer_hyperplane_mem_scriptQ hA hB') hRO hAR, hRO2⟩
  have hbM : ∀ b ∈ B', b ≠ 1 → delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ M := by
    intro b hb hb1
    have hbΩ : Subgroup.zpowers b ∉ omegaA A := by
      rw [hΩ, Set.mem_singleton_iff]
      intro hbc
      exact hcB' ((Subgroup.zpowers_le.mpr hb) (hbc ▸ Subgroup.mem_zpowers c))
    have hRb : R ≤ Subgroup.centralizer ({b} : Set G) :=
      hRB'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
    have hRb' : ¬ R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
      intro hle
      apply hRO
      intro r hr
      exact (Proof17Res.inf_pPrimeCoreOf_le hb hRB' ⟨hr, hle hr⟩).2
    have hOM := pPrimeCoreOf_centralizer_le_of h (h176 G A c L h.toSec15R) hΩ
      (CFSG.LieType.BorelTits.pCoreOf_le 2 M) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hRO2 hRcomm hRsq hcR
      (fun u hu => mul_conj_mul_conj_eq_one hc3 hR2 hRcomm hcR (hRc.le hu)) hRc hb.1 hb1 hRb hRb'
      (hsol G A c L Y₀ h b hb.1 hb1)
    exact delta_le_of hbal h hΩ hb.1 hb1 hbΩ hOM
  have hB'ab : CFSG.Assembly.IsElemAbelian 3 B' := Sec5.isElemAbelian_of_le hA.1 hB'.1
  obtain ⟨b, hbB', hb1⟩ : ∃ b ∈ B', b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : B' = ⊥ := (Subgroup.eq_bot_iff_forall B').mpr hcon
    rw [hbot, Subgroup.card_bot] at hB'9
    omega
  have hV1 : V ≠ ⊥ := by
    intro hbot
    have hbc : b ∉ Subgroup.zpowers c := by
      intro hbc
      have hle : Subgroup.zpowers b ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hbc
      have heq : Subgroup.zpowers b = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (pow_three_of_std h hbB'.1) hb1,
            hcord])
      exact hcB' ((Subgroup.zpowers_le.mpr hbB') (heq ▸ Subgroup.mem_zpowers c))
    exact hFaith G A c L Y₀ h V hV hVc b hbB'.1 hbc (by rw [hbot, Subgroup.commutator_bot_left])
  obtain ⟨b₀, hb₀, hb₀1, hZ1⟩ : ∃ b₀ ∈ B', b₀ ≠ 1 ∧
      V ⊓ Subgroup.centralizer ({b₀} : Set G) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hV1
    rw [eq_bot_iff]
    exact Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hB'ab (by rw [hB'9]; norm_num)
      (hB'.1.trans hAV) (coprime_three_of_isPGroup_two hV2) fun b hb hb1 => (hcon b hb hb1).le
  set Z := V ⊓ Subgroup.centralizer ({b₀} : Set G) with hZdef
  have hAb₀ : A ≤ Subgroup.centralizer ({b₀} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha hb₀.1)
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_inf hAV (hAb₀.trans Subgroup.le_normalizer)
  have hZQ : Z ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le_of_commutator_eq_bot h hMV hV2 hVc inf_le_left hAZ
  have hZΔ : Z ≤ delta A (lB A) (Subgroup.centralizer ({b₀} : Set G)) := le_delta hZQ inf_le_right
  have hZO : Z ≤ CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b₀} : Set G))) :=
    (le_inf (inf_le_left.trans hVO) hZΔ).trans
      (inf_le_pCoreOf_of_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
        ((hbM b₀ hb₀ hb₀1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)))
  have hb₀c : b₀ ∉ Subgroup.zpowers c := by
    intro hb₀c
    have hle : Subgroup.zpowers b₀ ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hb₀c
    have heq : Subgroup.zpowers b₀ = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (pow_three_of_std h hb₀.1) hb₀1,
          hcord])
    exact hcB' ((Subgroup.zpowers_le.mpr hb₀) (heq ▸ Subgroup.mem_zpowers c))
  refine Or.inr ⟨b₀, hb₀.1, hb₀c, Or.inl fun hbot => hZ1 ?_⟩
  rw [eq_bot_iff, ← hbot]
  exact hZO

end CFSG.RankThree.PartTwo.Sec17

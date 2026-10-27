module

public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofClaims
public import CFSG.RankThree.PartTwo.Sec16.Item163Proof
import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofOdd
import CFSG.RankThree.PartTwo.Sec17.Item17Res12ProofSolv
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec16.Item166ResProofDeltaSz
import CFSG.RankThree.PartTwo.Sec14.Item146General

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

@[expose] noncomputable def Claim174Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ¬ IsL3TwoPow L →
    ∀ X : Subgroup G, X = delta A (lB A) X → ¬ 3 ∣ Nat.card X →
      ∀ K ∈ thetaComponentsIn X,
        (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) →
        ∀ Y ∈ scriptY1Star A (lB A), ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G) →
          ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀)

namespace Proof17Res14

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem mem_normalizer_delta_cQuot (hOD : CFSG.Open.pCoreOf 2 Y₀ ≤ delta A (lB A) (cQuot Y₀))
    {s : G} (hsY : s ∈ Y₀) :
    s ∈ Subgroup.normalizer ((delta A (lB A) (cQuot Y₀) : Subgroup G) : Set G) := by
  set D := delta A (lB A) (cQuot Y₀) with hD
  have hle : D.map (MulAut.conj s).toMonoidHom ≤ D := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun Q hQ q hq => ?_
    rw [Subgroup.mem_comap]
    have hqC : q⁻¹ ∈ (cQuot Y₀ : Set G) := inv_mem (hQ.2 hq)
    rw [coe_cQuot] at hqC
    have hkK := hqC.2 s hsY
    have e : (MulAut.conj s).toMonoidHom q = q * (q⁻¹ * s * q⁻¹⁻¹ * s⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact D.mul_mem (le_sSup hQ hq) (hOD hkK)
  exact Subgroup.mem_normalizer_fintype fun x hx => hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem cQuot_le_normalizer (Y₀ : Subgroup G) :
    cQuot Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) := fun z hz => by
  have hz' : z ∈ (cQuot Y₀ : Set G) := hz
  rw [coe_cQuot] at hz'
  exact hz'.1

omit [Finite G] in
theorem oPrimeResidualOf_eq_bot_of_not_three_dvd {Y : Subgroup G} (hY3 : ¬ 3 ∣ Nat.card Y) :
    oPrimeResidualOf 3 Y = ⊥ := by
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_eq_bot_iff]
  rintro x ⟨hxY, k, hk⟩
  have hdvd : orderOf (⟨x, hxY⟩ : Y) ∣ Nat.gcd (3 ^ k) (Nat.card Y) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk)))
      (orderOf_dvd_natCard _)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3)), Nat.dvd_one,
    orderOf_eq_one_iff] at hdvd
  exact congrArg Subtype.val hdvd

theorem mem_scriptY1_delta_sup (h : Sec17Std G A c L Y₀)
    (hQ0 : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A))
    (hD3 : ¬ 3 ∣ Nat.card (delta A (lB A) (cQuot Y₀))) {S : Subgroup G}
    (hS : S ∈ scriptQPi A (lB A) ⊤ (piOf 2))
    (hSD : S ≤ Subgroup.normalizer ((delta A (lB A) (cQuot Y₀) : Subgroup G) : Set G)) :
    delta A (lB A) (S ⊔ delta A (lB A) (cQuot Y₀)) ∈ scriptY1 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := delta A (lB A) (cQuot Y₀) with hDdef
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set Y' := delta A (lB A) (S ⊔ D) with hY'
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.2
  have hZ3 : ¬ 3 ∣ Nat.card (S ⊔ D : Subgroup G) := by
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans (card_sup_dvd_card_mul hSD)) with
      h1 | h1
    · obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hS2
      rw [hm] at h1
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h1)
      omega
    · exact hD3 h1
  have hY'Z : Y' ≤ S ⊔ D := delta_le _
  have hY'3 : ¬ 3 ∣ Nat.card Y' := fun h3 => hZ3 (h3.trans (Subgroup.card_dvd_of_le hY'Z))
  have hSM : S ≤ M := HeadProof.le_M_of_mem_scriptQPi_two h hS
  have hDM : D ≤ M := (delta_le _).trans (cQuot_le_normalizer Y₀)
  have hY'M : Y' ≤ M := hY'Z.trans (sup_le hSM hDM)
  have hOD : CFSG.Open.pCoreOf 2 Y₀ ≤ D := le_delta hQ0 (Proof1712.pCoreOf_le_cQuot Y₀)
  have hOY' : CFSG.Open.pCoreOf 2 Y₀ ≤ Y' := le_delta hQ0 (hOD.trans le_sup_right)
  have hO2 : CFSG.Open.pCoreOf 2 Y₀ ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOY'
      (hY'M.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀)
  refine ⟨⟨⟨⟨Proof17Res12.ne_top_of_not_three_dvd h hY'3, Sec14.le_normalizer_delta _⟩,
    fun hbot => h.mem_y0Star.prop.2.2 (eq_bot_iff.mpr (hbot ▸ hO2))⟩, (delta_delta _).symm⟩,
    oPrimeResidualOf_eq_bot_of_not_three_dvd hY'3⟩

end Proof17Res14

open Proof17Res14 in
theorem claim174_of_inner
    (h165 : Item165S17)
    (h9 : CardInfNineS17) (hQ0 : Claim17Q0) (h146 : Item146S14) (h166 : Item166S17)
    (hI : Claim174Inner) : Claim174 := by
  intro G _ _ A c L Y₀ h X hXΔ hX3 K hK hSz Y hY hYM S hS
  by_cases hL3 : IsL3TwoPow L
  · exact absurd (h165 G A c L Y₀ h hL3 Y₀ h.mem_y0Star Y hY.prop.1) hYM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := isE27_of_std h
  obtain ⟨n, hn⟩ := hSz
  set D := delta A (lB A) (cQuot Y₀) with hDdef
  have hQ0' := hQ0 G A c L Y₀ h
  have hXtop : X ≠ ⊤ := Proof17Res12.ne_top_of_not_three_dvd h hX3
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
    have := Sec14.le_normalizer_delta (A := A) (LB := lB A) X
    rwa [← hXΔ] at this
  have hXQ : X ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA (h146 G A c L h.toSec14Std)
      ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three X).mpr hX3, hAX⟩
    rwa [← hXΔ] at this
  obtain ⟨hθ, hcen⟩ := (h166 G A c L Y₀ h Y₀ h.mem_y0Star).1 X ⟨hXtop, hAX⟩ hXΔ K hK ⟨n, hn⟩
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha =>
    ProofDeltaSz166.mem_normalizer_of_suzukiModel h.toTheoremFourHyp.localRank_lt hK hn hθ
      (hAX ha) (hA.1.2 a ha)
  have hKQ : K ∈ scriptQ A (lB A) := mem_scriptQ_of_le hXQ (le_of_mem_thetaComponentsIn hK) hAK
  have hKD : K ≤ D := le_delta hKQ fun x hx => by
    rw [← SetLike.mem_coe, coe_cQuot]
    exact hcen hx
  have hSQ : S ∈ scriptQ A (lB A) := hS.prop.1.1
  have hAC : A ≤ Subgroup.normalizer ((cQuot Y₀ : Subgroup G) : Set G) :=
    (Subgroup.le_normalizer.trans h.normalizer_le).trans
      (HeadProof.normalizer_le_normalizer_cQuot Y₀)
  have hSC : S ⊓ cQuot Y₀ ≤ D :=
    le_delta (mem_scriptQ_of_le hSQ inf_le_left (Late.le_normalizer_inf hSQ.1.2.2 hAC))
      inf_le_right
  have hOD : CFSG.Open.pCoreOf 2 Y₀ ≤ D := le_delta hQ0' (Proof1712.pCoreOf_le_cQuot Y₀)
  have hSD : S ≤ Subgroup.normalizer (D : Set G) :=
    (hI G A c L Y₀ h hL3 X hXΔ hX3 K hK ⟨n, hn⟩ Y hY hYM S hS).trans
      (sup_le (fun s hs => mem_normalizer_delta_cQuot hOD hs.2)
        (hSC.trans Subgroup.le_normalizer))
  have hD3 := Proof1712.not_three_dvd_delta_cQuot (claim1716Odd_proof h9) h
  have hS2 : S ∈ scriptQPi A (lB A) ⊤ (piOf 2) := ⟨⟨hSQ, le_top⟩, hS.prop.2⟩
  exact ⟨_, mem_scriptY1_delta_sup h hQ0' hD3 hS2 hSD, le_delta hKQ (hKD.trans le_sup_right),
    le_delta hSQ le_sup_left⟩

end CFSG.RankThree.PartTwo.Sec17

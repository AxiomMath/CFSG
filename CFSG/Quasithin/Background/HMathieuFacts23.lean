
module

public import CFSG.Quasithin.Background.HMathieuFacts23Base

public import CFSG.Quasithin.Background.HMathieuFacts22
public import CFSG.Quasithin.Background.HMathieuSyl23Greedy
public import CFSG.Quasithin.Background.HMathieuSyl23Odd
public import CFSG.Sporadic.Schreier.M23Data
public import CFSG.Sporadic.Schreier.M23PinnedInputs
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Quasithin.Background.HMathieuCentInputs
public import CFSG.Quasithin.Background.HMathieuMask
public import CFSG.Quasithin.Background.HMathieuNormInputs
public import CFSG.Quasithin.Background.HMathieuCent
public import CFSG.Monster.B.TwoA.Base.M22
public import CFSG.Monster.CodeAut.Bridge
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Quasithin.Background.HMathieuSyl23Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Quasithin.Background.HMathieuSyl23

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V]

variable {L M : Subgroup (MulAut V)}

theorem chain23
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rho11 mog23 inf_le_left).range) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hk : k ∈ [1, 2, 3, 4, 5])
    (hcard : Nat.card A = 2 ^ k) :
    ∃ g : ↥mog23, ∃ l : List T23s2.Elem, IndepList l ∧ pred23 k l = true ∧
      IsChainSub (chainAut e rhoM23 phi23 g) l A :=
  exists_chainModel rhoM23 (rho11_injective _ _) phi23 (T23s2.toSub_injective _ _) card_T23s2
    (fun _ h1 h2 => T23s2.mem_invols h1 h2) (greedy23 k hk) e (map_le_range23 hLM he hA) hAe
    hcard

theorem cocode23_card_le
    (hLM : IsOver L M) (h : MathieuCocode23 L ⊤ ⊥) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hcard : Nat.card A = 2 ^ k) : k ≤ 4 := by
  obtain ⟨e, he, -⟩ := cocode23_stdO h
  by_contra hk
  push Not at hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := A) (n := 5)
    (by rw [hcard]; exact Nat.pow_dvd_pow 2 (by omega))
  set B := K.map A.subtype
  have hBA : B ≤ A := Subgroup.map_subtype_le K
  have hB : Nat.card B = 2 ^ 5 := by rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
  have hBe : IsElemAbelian2 B :=
    ⟨fun a ha b hb => hAe.1 a (hBA ha) b (hBA hb), fun a ha => hAe.2 a (hBA ha)⟩
  obtain ⟨g, l, -, hpred, -⟩ := chain23 hLM he (hBA.trans hA) hBe (by simp) hB
  exact absurd (pred23_spec hpred).1 (by norm_num)

theorem cocode23_pRank
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode23 L ⊤ ⊥) :
    CFSG.Open.pRank 2 M ≤ 4 := by
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨E, hEM, hE, hEc⟩ := exists_isElemAbelian_card_pRank M
  exact cocode23_card_le hLM h hEM (isElemAbelian2_iff.2 hE) hEc

theorem cocode23_rk_mem
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode23 L ⊤ ⊥)
    {A : Subgroup (MulAut V)} (hA : A ≤ M) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    Nat.card A = 2 ^ rk A ∧ rk A ∈ [1, 2, 3, 4, 5] := by
  have : Finite (MulAut V) := finite_mulAut V
  have hpg : IsPGroup 2 A := isPGroup_two_of_sq_eq_one fun a => Subtype.ext (hAe.2 a a.2)
  have hc := card_eq_two_pow_of_isPGroup hpg
  have hle := cocode23_card_le hLM h hA hAe hc
  have h1 : rk A ≠ 0 := fun h0 => hA1 ((rk_eq_zero_iff_of_isPGroup hpg).1 h0)
  refine ⟨hc, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem cocode23_rkIdx_eq_four
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode23 L ⊤ ⊥)
    {t : MulAut V} (htM : t ∈ M) (ht : orderOf t = 2) :
    rkIdx (fixV (Subgroup.zpowers t)) = 4 := by
  obtain ⟨e, he, -⟩ := cocode23_stdO h
  have hAe : IsElemAbelian2 (Subgroup.zpowers t) := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht, pow_orderOf_eq_one,
        one_zpow]
  have hcard : Nat.card (Subgroup.zpowers t) = 2 ^ 1 := by rw [Nat.card_zpowers, ht, pow_one]
  have hle : Subgroup.zpowers t ≤ M := (Subgroup.zpowers_le).2 htM
  obtain ⟨g, l, -, hpred, hchain⟩ := chain23 hLM he hle hAe (by simp) hcard
  have hcardX := card_fixV (chainAct23 e g) hchain
  rw [(MaskCoords.ofEquiv (twistEquiv e rhoM23 g)).rkIdx_of_card hcardX]
  exact (pred23_spec hpred).2.2 rfl

theorem cocode23_rk_le_four_off
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode23 L ⊤ ⊥)
    (U : Subgroup V) (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v) {A : Subgroup (MulAut V)}
    (hA : IsFOneOffender M A) (hUA : U ≤ fixV A) : rk U ≤ 4 := by
  obtain ⟨e, he, hO2⟩ := cocode23_stdO h
  obtain ⟨⟨hAM, hA1, hAe⟩, hoff⟩ := hA
  obtain ⟨hcard, hk⟩ := cocode23_rk_mem hLM h hAM hA1 hAe
  obtain ⟨g, l, -, hpred, hchain⟩ := chain23 hLM he hAM hAe hk hcard
  have hact := chainAct23 e g
  have hcardX := card_fixV hact hchain
  have hidx := (MaskCoords.ofEquiv (twistEquiv e rhoM23 g)).rkIdx_of_card hcardX
  refine rk_le_four_of_o2OK (MaskCoords.ofEquiv (twistEquiv e rhoM23 g)) (X := fixV A)
    (fun m hm => fixMasks_spec hact hchain hm) hcardX (o2_twist23 hO2 g) hUA
    (fun v hv hvO => hU v hv hvO) ((pred23_spec hpred).2.1 ?_)
  omega

theorem cocode23_rk_le_four
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode23 L ⊤ ⊥)
    (U : Subgroup V) (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v)
    (hd : (∃ A : Subgroup (MulAut V), IsFOneOffender M A ∧ U ≤ fixV A) ∨
      (∃ y ∈ M, y ≠ 1 ∧ Odd (orderOf y) ∧ U ≤ fixV (Subgroup.zpowers y))) : rk U ≤ 4 := by
  rcases hd with ⟨A, hA, hUA⟩ | ⟨y, hyM, hy1, hyo, hUy⟩
  · exact cocode23_rk_le_four_off hLM h U hU hA hUA
  · exact cocode23_rk_le_four_odd hLM h U hU hyM hy1 hyo hUy

end CFSG.Quasithin.H.Mathieu

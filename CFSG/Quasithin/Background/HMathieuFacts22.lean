
module

public import CFSG.Quasithin.Background.HMathieuFacts22Base

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.HMathieuSyl22Greedy
public import CFSG.Quasithin.Background.HMathieuSyl22Odd
public import CFSG.Quasithin.Background.HMathieuNorm
public import CFSG.Quasithin.Background.HMathieuTransfer
public import CFSG.Quasithin.Background.HMathieuStdO
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public import Certificates.Data.CFSGNative.Mathieu.M24
public import Certificates.Data.CFSGNative.Mathieu.M22
public import CFSG.Monster.B.Mathieu.M22CheckInputs
public import CFSG.Quasithin.Background.HMathieuCentInputs
public import CFSG.Quasithin.Background.HMathieuMask
public import CFSG.Quasithin.Background.HMathieuSyl22Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Quasithin.Background.HMathieuSyl22
public import Certificates.Certificate7068

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V]

variable {L M : Subgroup (MulAut V)}

theorem chain22
    (hLM : IsOver L M) {e : V ≃* W10}
    (he : L.map (congrHom e) = (rho10 mog22 mog22_le_mog22plus).range) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hk : k ∈ [1, 2, 3, 4, 5, 6])
    (hcard : Nat.card A = 2 ^ k) :
    ∃ g : ↥mog22plus, ∃ l : List T22s2.Elem, IndepList l ∧ pred22 k l = true ∧
      IsChainSub (chainAut e psi22 phi22 g) l A :=
  exists_chainModel psi22 rho10_mog22plus_injective phi22 (T22s2.toSub_injective _ _) card_T22s2
    (fun _ h1 h2 => T22s2.mem_invols h1 h2) (greedy22 k hk) e (map_le_range22 hLM he hA) hAe
    hcard

theorem cocode22_card_le
    (hLM : IsOver L M) (h : MathieuCocode22 L ⊤ ⊥) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hcard : Nat.card A = 2 ^ k) : k ≤ 5 := by
  obtain ⟨e, he, -⟩ := cocode22_stdO h
  by_contra hk
  push Not at hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := A) (n := 6)
    (by rw [hcard]; exact Nat.pow_dvd_pow 2 (by omega))
  set B := K.map A.subtype
  have hBA : B ≤ A := Subgroup.map_subtype_le K
  have hB : Nat.card B = 2 ^ 6 := by rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
  have hBe : IsElemAbelian2 B :=
    ⟨fun a ha b hb => hAe.1 a (hBA ha) b (hBA hb), fun a ha => hAe.2 a (hBA ha)⟩
  obtain ⟨g, l, -, hpred, -⟩ := chain22 hLM he (hBA.trans hA) hBe (by simp) hB
  exact absurd (pred22_spec hpred).1 (by norm_num)

theorem cocode22_pRank
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode22 L ⊤ ⊥) :
    CFSG.Open.pRank 2 M ≤ 5 := by
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨E, hEM, hE, hEc⟩ := exists_isElemAbelian_card_pRank M
  exact cocode22_card_le hLM h hEM (isElemAbelian2_iff.2 hE) hEc

theorem cocode22_rk_mem
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode22 L ⊤ ⊥)
    {A : Subgroup (MulAut V)} (hA : A ≤ M) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    Nat.card A = 2 ^ rk A ∧ rk A ∈ [1, 2, 3, 4, 5, 6] := by
  have : Finite (MulAut V) := finite_mulAut V
  have hpg : IsPGroup 2 A := isPGroup_two_of_sq_eq_one fun a => Subtype.ext (hAe.2 a a.2)
  have hc := card_eq_two_pow_of_isPGroup hpg
  have hle := cocode22_card_le hLM h hA hAe hc
  have h1 : rk A ≠ 0 := fun h0 => hA1 ((rk_eq_zero_iff_of_isPGroup hpg).1 h0)
  refine ⟨hc, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem cocode22_rk_le_four_off
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode22 L ⊤ ⊥)
    (U : Subgroup V) (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v) {A : Subgroup (MulAut V)}
    (hA : IsFOneOffender M A) (hUA : U ≤ fixV A) : rk U ≤ 4 := by
  obtain ⟨e, he, hO2⟩ := cocode22_stdO h
  obtain ⟨⟨hAM, hA1, hAe⟩, hoff⟩ := hA
  obtain ⟨hcard, hk⟩ := cocode22_rk_mem hLM h hAM hA1 hAe
  obtain ⟨g, l, -, hpred, hchain⟩ := chain22 hLM he hAM hAe hk hcard
  have hact := chainAct22 e g
  have hcardX := card_fixV hact hchain
  have hidx := (MaskCoords.ofEquiv (twistEquiv e psi22 g)).rkIdx_of_card hcardX
  refine rk_le_four_of_o2OK (MaskCoords.ofEquiv (twistEquiv e psi22 g)) (X := fixV A)
    (fun m hm => fixMasks_spec hact hchain hm) hcardX (o2_twist22 hO2 g) hUA
    (fun v hv hvO => hU v hv hvO) ((pred22_spec hpred).2.1 ?_)
  omega

theorem cocode22_rk_le_four
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode22 L ⊤ ⊥)
    (U : Subgroup V) (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v)
    (hd : (∃ A : Subgroup (MulAut V), IsFOneOffender M A ∧ U ≤ fixV A) ∨
      (∃ y ∈ M, y ≠ 1 ∧ Odd (orderOf y) ∧ U ≤ fixV (Subgroup.zpowers y))) : rk U ≤ 4 := by
  rcases hd with ⟨A, hA, hUA⟩ | ⟨y, hyM, hy1, hyo, hUy⟩
  · exact cocode22_rk_le_four_off hLM h U hU hA hUA
  · exact cocode22_rk_le_four_odd hLM h U hU hyM hy1 hyo hUy

theorem stmtH15M22 :
    StmtH15M22 := by
  intro V _ _ L M hLM hL
  obtain ⟨e, he, -⟩ := cocode22_stdO hL
  refine ⟨fun A hAM hAe hcard => ?_, fun A hAM hAe hcard => ?_⟩
  · obtain ⟨g, l, hind, hpred, hchain⟩ := chain22 hLM he hAM hAe (k := 5) (by simp)
      (by rw [hcard]; norm_num)
    obtain ⟨hxi, hpair⟩ := (pred22_spec hpred).2.2.2.2 rfl
    exact ⟨(MaskCoords.ofEquiv (twistEquiv e psi22 g)).eq_top_of_pow_le
        (pow_le_card_xiV (chainAct22 e g) hchain (chainAut22_injective e g) hxi),
      (MaskCoords.ofEquiv (twistEquiv e psi22 g)).eq_top_of_pow_le
        (pow_le_card_iSup_four (chainAct22 e g) hchain (chainAut22_injective e g) hind hpair)⟩
  · obtain ⟨g, l, -, hpred, hchain⟩ := chain22 hLM he hAM hAe (k := 4) (by simp)
      (by rw [hcard]; norm_num)
    have hxi := (pred22_spec hpred).2.2.2.1 rfl
    exact (MaskCoords.ofEquiv (twistEquiv e psi22 g)).rkIdx_le_one_of_pow_le (by norm_num)
      (pow_le_card_xiV (chainAct22 e g) hchain (chainAut22_injective e g) hxi)

theorem cocode22_three_le_rkIdx
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode22 L ⊤ ⊥)
    {t : MulAut V} (htM : t ∈ M) (ht : orderOf t = 2) :
    3 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  obtain ⟨e, he, -⟩ := cocode22_stdO h
  have hAe : IsElemAbelian2 (Subgroup.zpowers t) := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht, pow_orderOf_eq_one,
        one_zpow]
  have hcard : Nat.card (Subgroup.zpowers t) = 2 ^ 1 := by rw [Nat.card_zpowers, ht, pow_one]
  obtain ⟨g, l, -, hpred, hchain⟩ := chain22 hLM he ((Subgroup.zpowers_le).2 htM) hAe (by simp)
    hcard
  have hcardX := card_fixV (chainAct22 e g) hchain
  rw [(MaskCoords.ofEquiv (twistEquiv e psi22 g)).rkIdx_of_card hcardX]
  exact (pred22_spec hpred).2.2.1 rfl

theorem cocode22_mParam
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode22 L ⊤ ⊥) :
    3 ≤ E3.mParam M := by
  have : Finite (MulAut V) := finite_mulAut V
  unfold E3.mParam
  split_ifs with hev
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 2 (even_iff_two_dvd.1 hev)
    refine le_csInf ⟨_, (t : MulAut V), t.2, by rw [Subgroup.orderOf_coe, ht], rfl⟩ ?_
    rintro _ ⟨s, hs, hso, rfl⟩
    exact cocode22_three_le_rkIdx hLM h hs hso
  · obtain ⟨e, -, -⟩ := cocode22_stdO h
    rw [(MaskCoords.ofEquiv e).rk_eq]
    norm_num

end CFSG.Quasithin.H.Mathieu

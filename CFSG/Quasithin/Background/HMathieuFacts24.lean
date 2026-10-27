
module

public import CFSG.Quasithin.Background.HMathieuFacts24Base

public import CFSG.Quasithin.Background.HMathieuFacts22
public import CFSG.Quasithin.Background.HMathieuSyl24Greedy
public import CFSG.Quasithin.Background.HMathieuSyl24Odd
public meta import CFSG.Quasithin.Background.HMathieuSyl24
public import CFSG.Sporadic.Schreier.M24Data
public meta import CFSG.Sporadic.Schreier.M24Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Monster.B.Mathieu.M24CheckInputs
public import CFSG.Quasithin.Background.HMathieuFacts24Inputs
public import Certificates.Certificate7063
public import CFSG.Quasithin.Background.HMathieuCentInputs
public import CFSG.Quasithin.Background.HMathieuMask
public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuAvoid
public import CFSG.Quasithin.Background.HMathieuEnumAll
public import CFSG.Quasithin.Background.HMathieuSyl24
public import Certificates.Certificate7074

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V]

variable {L M : Subgroup (MulAut V)}

theorem pred24_spec {l : List T24s2.Elem} (hl : IndepList l)
    (h : pred24 l = true) :
    l.length ≤ 6 ∧
      (1 ≤ l.length → 11 - Nat.log 2 (fixMasks 11 act24s2 l).length ≤ l.length + 1 →
        avoidOK 11 3 o2Masks24 (fixMasks 11 act24s2 l) = true) ∧
      (l.length = 1 → 4 ≤ 11 - Nat.log 2 (fixMasks 11 act24s2 l).length) ∧
      (l.length = 6 → xiCheck 11 11 act24s2 l = true ∨
        Nat.log 2 (fixMasks 11 act24s2 l).length = 3) := by
  have hinv : ∀ a ∈ l, a * a = 1 := (isCommInvol_of_indepList hl).1
  rw [pred24, fixMasks24_eq hinv] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hk, h1⟩, h2⟩, h3⟩ := h
  refine ⟨hk, fun hk1 hd => ?_, fun h1' => h2.resolve_left (not_not.2 h1'), fun h6 => ?_⟩
  · rcases h1 with (h | h) | h
    · omega
    · exact absurd hd h
    · exact h
  · rcases h3 with (h | h) | h
    · exact absurd h6 h
    · exact Or.inl h
    · exact Or.inr h

theorem chain24
    (hLM : IsOver L M)
    {e : V ≃* W11}
    (he : L.map (congrHom e) = (rho11 AutPerm le_rfl).range) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hk : k ≤ 7) (hcard : Nat.card A = 2 ^ k) :
    ∃ g : ↥AutPerm, ∃ l : List T24s2.Elem, IndepList l ∧ pred24 l = true ∧
      IsChainSub (chainAut e rhoM24 phi24 g) l A :=
  exists_chainModel rhoM24 (rho11_injective _ _) phi24 (T24s2.toSub_injective _ _) card_T24s2
    (fun _ h1 h2 => T24s2.mem_invols h1 h2) (greedy24 hk) e (map_le_range24 hLM he hA) hAe hcard

theorem cocode24_card_le
    (hLM : IsOver L M) (h : MathieuCocode24 L ⊤ ⊥) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hcard : Nat.card A = 2 ^ k) : k ≤ 6 := by
  obtain ⟨e, he, -⟩ := cocode24_stdO h
  by_contra hk
  push Not at hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := A) (n := 7)
    (by rw [hcard]; exact Nat.pow_dvd_pow 2 (by omega))
  set B := K.map A.subtype
  have hBA : B ≤ A := Subgroup.map_subtype_le K
  have hB : Nat.card B = 2 ^ 7 := by rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
  have hBe : IsElemAbelian2 B :=
    ⟨fun a ha b hb => hAe.1 a (hBA ha) b (hBA hb), fun a ha => hAe.2 a (hBA ha)⟩
  obtain ⟨g, l, hind, hpred, hchain⟩ := chain24 hLM he (hBA.trans hA) hBe le_rfl hB
  have hlen := (pred24_spec hind hpred).1
  have hcl := card_of_chainSub hchain (chainAut24_injective e g) hind
  rw [hB] at hcl
  have := Nat.pow_right_injective (le_refl 2) hcl
  omega

theorem cocode24_pRank
    [Finite V]
    (hLM : IsOver L M) (h : MathieuCocode24 L ⊤ ⊥) :
    CFSG.Open.pRank 2 M ≤ 6 := by
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨E, hEM, hE, hEc⟩ := exists_isElemAbelian_card_pRank M
  exact cocode24_card_le hLM h hEM (isElemAbelian2_iff.2 hE) hEc

theorem chain24'
    [Finite V]
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rho11 AutPerm le_rfl).range) (h : MathieuCocode24 L ⊤ ⊥)
    {A : Subgroup (MulAut V)} (hA : A ≤ M) (hAe : IsElemAbelian2 A) :
    ∃ g : ↥AutPerm, ∃ l : List T24s2.Elem, IndepList l ∧ pred24 l = true ∧
      IsChainSub (chainAut e rhoM24 phi24 g) l A ∧ Nat.card A = 2 ^ l.length := by
  have : Finite (MulAut V) := finite_mulAut V
  have hpg : IsPGroup 2 A := isPGroup_two_of_sq_eq_one fun a => Subtype.ext (hAe.2 a a.2)
  have hc := card_eq_two_pow_of_isPGroup hpg
  have hle := cocode24_card_le hLM h hA hAe hc
  obtain ⟨g, l, hind, hpred, hchain⟩ := chain24 hLM he hA hAe (by omega) hc
  exact ⟨g, l, hind, hpred, hchain, card_of_chainSub hchain (chainAut24_injective e g) hind⟩

theorem cocode24_four_le_rkIdx
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode24 L ⊤ ⊥)
    {t : MulAut V} (htM : t ∈ M) (ht : orderOf t = 2) :
    4 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  obtain ⟨e, he, -⟩ := cocode24_stdO h
  obtain ⟨g, l, hind, hpred, hchain, hcl⟩ :=
    chain24' hLM he h ((Subgroup.zpowers_le).2 htM) (isElemAbelian2_zpowers ht)
  have hlen : l.length = 1 := by
    rw [Nat.card_zpowers, ht] at hcl
    have := Nat.pow_right_injective (le_refl 2) (hcl.symm.trans (pow_one 2).symm)
    exact this
  have hcardX := card_fixV (chainAct24 e g) hchain
  rw [(MaskCoords.ofEquiv (twistEquiv e rhoM24 g)).rkIdx_of_card hcardX]
  exact (pred24_spec hind hpred).2.2.1 hlen

theorem inv24Arr_ok :
    inAutOK inv24Arr = true ∧ (∀ i < 24, inv24Arr[inv24Arr[i]!]! = i) ∧
    inv24Arr[0]! ≠ 0 ∧ ((List.range (2 ^ 11)).filter fun m => act11 inv24Arr m == m).length =
      2 ^ 7 :=
  Certificates.certificate7063

theorem exists_inv_rkIdx_four24
    (h : MathieuCocode24 L ⊤ ⊥) :
    ∃ t ∈ L, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) = 4 := by
  obtain ⟨e, he, -⟩ := cocode24_stdO h
  obtain ⟨hok, hinv, hne, hfix⟩ := inv24Arr_ok
  obtain ⟨t, htL, ht, hX⟩ := exists_inv_of_arr le_rfl hok hinv 0 hne (fun σ hσ _ => hσ) he
  refine ⟨t, htL, ht, ?_⟩
  have hcard := (MaskCoords.ofEquiv e).card_eq (fixV (Subgroup.zpowers t))
    (fun m => act11 inv24Arr m == m) fun m hm => (hX m hm).trans beq_iff_eq.symm
  rw [(MaskCoords.ofEquiv e).rkIdx_of_card hcard, hfix, Nat.log_pow (by norm_num)]

theorem cocode24_mParam
    [Finite V]
    (hLM : IsOver L M) (h : MathieuCocode24 L ⊤ ⊥) :
    E3.mParam M = 4 := by
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨t, htL, ht, h4⟩ := exists_inv_rkIdx_four24 h
  have htM : t ∈ M := hLM.1 htL
  unfold E3.mParam
  have hev : Even (Nat.card M) := by
    rw [even_iff_two_dvd, ← ht, ← Subgroup.orderOf_mk t htM]
    exact orderOf_dvd_natCard _
  rw [ite_eq_left hev]
  refine le_antisymm (Nat.sInf_le ⟨t, htM, ht, h4.symm⟩) (le_csInf ⟨4, t, htM, ht, h4.symm⟩ ?_)
  rintro _ ⟨s, hs, hso, rfl⟩
  exact cocode24_four_le_rkIdx hLM h hs hso

theorem cocode24_rk_le_three_off
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode24 L ⊤ ⊥)
    (U : Subgroup V) (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v) {A : Subgroup (MulAut V)}
    (hA : IsFOneOffender M A) (hUA : U ≤ fixV A) : rk U ≤ 3 := by
  obtain ⟨e, he, hO2⟩ := cocode24_stdO h
  obtain ⟨⟨hAM, hA1, hAe⟩, hoff⟩ := hA
  obtain ⟨g, l, hind, hpred, hchain, hcl⟩ := chain24' hLM he h hAM hAe
  have hact := chainAct24 e g
  have hcardX := card_fixV hact hchain
  have hidx := (MaskCoords.ofEquiv (twistEquiv e rhoM24 g)).rkIdx_of_card hcardX
  have hrkA : rk A = l.length := by
    unfold rk
    rw [hcl, padicValNat.prime_pow]
  have hl1 : 1 ≤ l.length := by
    by_contra h0
    have h0' : l.length = 0 := by omega
    rw [h0', pow_zero] at hcl
    exact hA1 (Subgroup.card_eq_one.1 hcl)
  refine rk_le_of_avoidOK (MaskCoords.ofEquiv (twistEquiv e rhoM24 g)) (X := fixV A)
    (fun m hm hv => mem_fixMasks_of_vm hact hchain hm hv) (o2_twist24 hO2 g) hUA
    (fun w hw hwO => hU w hw hwO) ((pred24_spec hind hpred).2.1 hl1 (by omega))

theorem cocode24_rk_le_three
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode24 L ⊤ ⊥)
    (U : Subgroup V) (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v)
    (hd : (∃ A : Subgroup (MulAut V), IsFOneOffender M A ∧ U ≤ fixV A) ∨
      (∃ y ∈ M, y ≠ 1 ∧ Odd (orderOf y) ∧ U ≤ fixV (Subgroup.zpowers y))) : rk U ≤ 3 := by
  rcases hd with ⟨A, hA, hUA⟩ | ⟨y, hyM, hy1, hyo, hUy⟩
  · exact cocode24_rk_le_three_off hLM h U hU hA hUA
  · exact cocode24_rk_le_three_odd hLM h U hU hyM hy1 hyo hUy

theorem stmtH15M24 :
    StmtH15M24 := by
  intro V _ _ L M hLM hL A hAM hAe hcard
  obtain ⟨e, he, -⟩ := cocode24_stdO hL
  obtain ⟨g, l, hind, hpred, hchain, hcl⟩ := chain24' hLM he hL hAM hAe
  have hlen : l.length = 6 := by
    rw [hcard] at hcl
    exact Nat.pow_right_injective (le_refl 2) (hcl.symm.trans (by norm_num : (64 : ℕ) = 2 ^ 6))
  rcases (pred24_spec hind hpred).2.2.2 hlen with hxi | hd
  · exact Or.inl ((MaskCoords.ofEquiv (twistEquiv e rhoM24 g)).eq_top_of_pow_le
      (pow_le_card_xiV (chainAct24 e g) hchain (chainAut24_injective e g) hxi))
  · right
    rw [(MaskCoords.ofEquiv (twistEquiv e rhoM24 g)).rk_of_card (card_fixV (chainAct24 e g) hchain),
      hd]

end CFSG.Quasithin.H.Mathieu

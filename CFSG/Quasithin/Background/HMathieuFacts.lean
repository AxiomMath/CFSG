
module

public import CFSG.Quasithin.Background.HMathieuFactsBase

public import CFSG.Quasithin.Background.HMathieuFacts23
public import CFSG.Quasithin.Background.HMathieuFacts24
public import CFSG.Quasithin.Background.HMathieuCodeCent
public import CFSG.Quasithin.Background.HMathieuCodeInv
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import CFSG.Sporadic.Schreier.M23Data
public import CFSG.Sporadic.Schreier.M23PinnedInputs
public import CFSG.Sporadic.Schreier.M24Data
public meta import CFSG.Sporadic.Schreier.M24Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public import Certificates.Data.CFSGNative.Mathieu.M24
public import Certificates.Data.CFSGNative.Mathieu.M22
public import CFSG.Monster.B.Mathieu.M24CheckInputs
public import CFSG.Monster.B.Mathieu.M22CheckInputs
public import CFSG.Quasithin.Background.HMathieuCentInputs
public import CFSG.Quasithin.Background.HMathieuMask
public import CFSG.Quasithin.Background.HMathieuCodeCentInputs
public import CFSG.Quasithin.Background.HMathieuCodeMask
public import CFSG.Quasithin.Background.HMathieuNorm
public import CFSG.Quasithin.Background.HMathieuCodeInvInputs
public import CFSG.Quasithin.Background.HMathieuSyl22
public import CFSG.Quasithin.Background.HMathieuSyl23
public import CFSG.Quasithin.Background.HMathieuSyl24
public import CFSG.Quasithin.Background.HMathieuSyl22Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Quasithin.Background.HMathieuSyl23Inputs
public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public import CFSG.Quasithin.Background.HMathieuAvoid
public import CFSG.Quasithin.Background.HMathieuEnumAll
public import CFSG.Quasithin.Background.HMathieuFacts24Inputs
public import CFSG.Quasithin.Background.HMathieuFacts22
public import CFSG.Quasithin.Background.HMathieuSyl24Greedy
public import CFSG.Quasithin.Background.HMathieuSyl24Odd
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
public import Certificates.Certificate7071
public import Certificates.Certificate7074

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem code22_card_le
    (hLM : IsOver L M) (h : MathieuCode22 L ⊤ ⊥) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hcard : Nat.card A = 2 ^ k) : k ≤ 5 := by
  obtain ⟨e, he⟩ := code22_std h
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
  obtain ⟨g, l, -, hpred, -⟩ := exists_chainModel psiC22 rhoC10_mog22plus_injective phi22
    (T22s2.toSub_injective _ _) card_T22s2 (fun _ h1 h2 => T22s2.mem_invols h1 h2)
    (greedy22 6 (by simp)) e
    (map_le_of_normalizer hLM he normalizer_rhoC10_mog22 (hBA.trans hA)) hBe hB
  exact absurd (pred22_spec hpred).1 (by norm_num)

theorem code22_three_le_rkIdx
    [Finite V] (hLM : IsOver L M) (h : MathieuCode22 L ⊤ ⊥)
    {t : MulAut V} (htM : t ∈ M) (ht : orderOf t = 2) :
    3 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  obtain ⟨e, he⟩ := code22_std h
  obtain ⟨s, hs1, hss, hidx⟩ := inv_model psiC22 rhoC10_mog22plus_injective phi22
    (T22s2.toSub_injective _ _) card_T22s2 (fun q m => actM (matsC22[q.idx]!) m)
    (fun s _ hm => psiC22_phi22 s hm)
    (fun s _ hm => by rw [actM_matsC10 T22s2 (mats := matsC22) rfl s hm]; exact actC10_lt _ _) e
    (map_le_of_normalizer hLM he normalizer_rhoC10_mog22 ((Subgroup.zpowers_le).2 htM)
      ⟨t, Subgroup.mem_zpowers t, rfl⟩) ht
  rw [hidx]
  have hle := invC22_ok s hs1 hss
  have hlog : Nat.log 2 (fixMasks 10 (fun q m => actM (matsC22[q.idx]!) m) [s]).length ≤ 7 :=
    (Nat.log_mono_right hle).trans (by rw [Nat.log_pow (by norm_num)])
  omega

theorem code23_card_le
    (hLM : IsOver L M) (h : MathieuCode23 L ⊤ ⊥) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hcard : Nat.card A = 2 ^ k) : k ≤ 4 := by
  obtain ⟨e, he⟩ := code23_std h
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
  obtain ⟨g, l, -, hpred, -⟩ := exists_chainModel psiC23 (rhoC11_injective _ _) phi23
    (T23s2.toSub_injective _ _) card_T23s2 (fun _ h1 h2 => T23s2.mem_invols h1 h2)
    (greedy23 5 (by simp)) e
    (map_le_of_normalizer hLM he normalizer_rhoC11_mog23 (hBA.trans hA)) hBe hB
  exact absurd (pred23_spec hpred).1 (by norm_num)

theorem code23_rkIdx_eq_four
    [Finite V] (hLM : IsOver L M) (h : MathieuCode23 L ⊤ ⊥)
    {t : MulAut V} (htM : t ∈ M) (ht : orderOf t = 2) :
    rkIdx (fixV (Subgroup.zpowers t)) = 4 := by
  obtain ⟨e, he⟩ := code23_std h
  obtain ⟨s, hs1, hss, hidx⟩ := inv_model psiC23 (rhoC11_injective _ _) phi23
    (T23s2.toSub_injective _ _) card_T23s2 (fun q m => actM (matsC23[q.idx]!) m)
    (fun s _ hm => psiC23_phi23 s hm)
    (fun s _ hm => by rw [actM_matsC11 T23s2 (mats := matsC23) rfl s hm]; exact actC11_lt _ _) e
    (map_le_of_normalizer hLM he normalizer_rhoC11_mog23 ((Subgroup.zpowers_le).2 htM)
      ⟨t, Subgroup.mem_zpowers t, rfl⟩) ht
  rw [hidx, invC23_ok s hs1 hss, Nat.log_pow (by norm_num)]

theorem code24_card_le
    (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hcard : Nat.card A = 2 ^ k) : k ≤ 6 := by
  obtain ⟨e, he⟩ := code24_std h
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
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC24 (rhoC11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
    (greedy24 le_rfl) e
    (map_le_of_normalizer hLM he normalizer_rhoC11_autPerm (hBA.trans hA)) hBe hB
  have hlen := (pred24_spec hind hpred).1
  have hcl := card_of_chainSub hchain
    (chainAut_injective (rhoC11_injective _ _) (T24s2.toSub_injective _ _) g) hind
  rw [hB] at hcl
  have := Nat.pow_right_injective (le_refl 2) hcl
  omega

theorem code24_four_le_rkIdx
    [Finite V] (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥)
    {t : MulAut V} (htM : t ∈ M) (ht : orderOf t = 2) :
    4 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  obtain ⟨e, he⟩ := code24_std h
  obtain ⟨s, hs1, hss, hidx⟩ := inv_model psiC24 (rhoC11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun q m => actM (matsC24[q.idx]!) m)
    (fun s _ hm => psiC24_phi24 s hm)
    (fun s _ hm => by rw [actM_matsC11 T24s2 (mats := matsC24) rfl s hm]; exact actC11_lt _ _) e
    (map_le_of_normalizer hLM he normalizer_rhoC11_autPerm ((Subgroup.zpowers_le).2 htM)
      ⟨t, Subgroup.mem_zpowers t, rfl⟩) ht
  rw [hidx]
  have hle := invC24_ok s hs1 hss
  have hlog : Nat.log 2 (fixMasks 11 (fun q m => actM (matsC24[q.idx]!) m) [s]).length ≤ 7 :=
    (Nat.log_mono_right hle).trans (by rw [Nat.log_pow (by norm_num)])
  omega

theorem cocode23_mParam
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode23 L ⊤ ⊥) :
    E3.mParam M = 4 := by
  obtain ⟨e, he, -⟩ := cocode23_stdO h
  obtain ⟨hok, hinv, h0, h1, hfix, -, -⟩ := invArr_ok
  obtain ⟨t, htL, ht, hX⟩ := exists_inv_of_arr_gen (rho11 mog23 inf_le_left) (rho11_injective _ _)
    act11 (fun σ a ha m => rho11_toW mog23 inf_le_left σ ha m) act11_lt hok hinv 1 h1
    (fun σ hσ hσa => mem_mog23_of_arr hσ hσa h0) he
  have h4 : rkIdx (fixV (Subgroup.zpowers t)) = 4 := by
    rw [rkIdx_of_arr (P := fun m => act11 inv23Arr m == m)
      (fun m hm => (hX m hm).trans beq_iff_eq.symm), hfix, Nat.log_pow (by norm_num)]
  exact mParam_eq_of hLM htL ht h4 fun s hs hso => (cocode23_rkIdx_eq_four hLM h hs hso).ge

theorem code23_mParam
    [Finite V] (hLM : IsOver L M) (h : MathieuCode23 L ⊤ ⊥) :
    E3.mParam M = 4 := by
  obtain ⟨e, he⟩ := code23_std h
  obtain ⟨hok, hinv, h0, h1, -, hfix, -⟩ := invArr_ok
  obtain ⟨t, htL, ht, hX⟩ := exists_inv_of_arr_gen (rhoC11 mog23 inf_le_left)
    (rhoC11_injective _ _) actC11 (fun σ a ha m => rhoC11_toW mog23 inf_le_left σ ha m) actC11_lt
    hok hinv 1 h1 (fun σ hσ hσa => mem_mog23_of_arr hσ hσa h0) he
  have h4 : rkIdx (fixV (Subgroup.zpowers t)) = 4 := by
    rw [rkIdx_of_arr (P := fun m => actC11 inv23Arr m == m)
      (fun m hm => (hX m hm).trans beq_iff_eq.symm), hfix, Nat.log_pow (by norm_num)]
  exact mParam_eq_of hLM htL ht h4 fun s hs hso => (code23_rkIdx_eq_four hLM h hs hso).ge

theorem code24_mParam
    [Finite V] (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) :
    E3.mParam M = 4 := by
  obtain ⟨e, he⟩ := code24_std h
  obtain ⟨hok, hinv, hne, -⟩ := inv24Arr_ok
  obtain ⟨-, -, -, -, -, -, hfix⟩ := invArr_ok
  obtain ⟨t, htL, ht, hX⟩ := exists_inv_of_arr_gen (rhoC11 AutPerm le_rfl) (rhoC11_injective _ _)
    actC11 (fun σ a ha m => rhoC11_toW AutPerm le_rfl σ ha m) actC11_lt hok hinv 0 hne
    (fun σ hσ _ => hσ) he
  have h4 : rkIdx (fixV (Subgroup.zpowers t)) = 4 := by
    rw [rkIdx_of_arr (P := fun m => actC11 inv24Arr m == m)
      (fun m hm => (hX m hm).trans beq_iff_eq.symm), hfix, Nat.log_pow (by norm_num)]
  exact mParam_eq_of hLM htL ht h4 fun s hs hso => code24_four_le_rkIdx hLM h hs hso

theorem code22_mParam
    [Finite V] (hLM : IsOver L M) (h : MathieuCode22 L ⊤ ⊥) :
    3 ≤ E3.mParam M := by
  obtain ⟨e, -⟩ := code22_std h
  refine le_mParam_of ?_ fun s hs hso => code22_three_le_rkIdx hLM h hs hso
  rw [(MaskCoords.ofEquiv e).rk_eq]
  norm_num

theorem stmtH14PRank
    : StmtH14PRank := by
  intro V _ _ L M hLM
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases h with h | h
    · exact cocode24_pRank hLM h
    · exact pRank_le_of_card_le fun A hA hAe k hk => code24_card_le hLM h hA hAe hk
  · rcases h with h | h
    · exact cocode23_pRank hLM h
    · exact pRank_le_of_card_le fun A hA hAe k hk => code23_card_le hLM h hA hAe hk
  · rcases h with h | h
    · exact cocode22_pRank hLM h
    · exact pRank_le_of_card_le fun A hA hAe k hk => code22_card_le hLM h hA hAe hk

theorem stmtH14_4
    : StmtH14_4 := by
  intro V _ _ L M hLM
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | h | h | h
    · exact cocode24_mParam hLM h
    · exact code24_mParam hLM h
    · exact cocode23_mParam hLM h
    · exact code23_mParam hLM h
  · rcases h with h | h
    · exact cocode22_mParam hLM h
    · exact code22_mParam hLM h

theorem stmtH15O2
    : StmtH15O2 := by
  intro V _ _ L M hLM U hU hd
  exact ⟨fun h => cocode22_rk_le_four hLM h U hU hd, fun h => cocode23_rk_le_four hLM h U hU hd,
    fun h => cocode24_rk_le_three hLM h U hU hd⟩

end CFSG.Quasithin.H.Mathieu

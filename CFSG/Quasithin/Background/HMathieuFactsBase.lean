
module

public import CFSG.Quasithin.Background.HMathieuFacts23Base
public import CFSG.Quasithin.Background.HMathieuFacts24Base
public import CFSG.Quasithin.Background.HMathieuCodeCent
public import CFSG.Quasithin.Background.HMathieuCodeInvBase
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
public import CFSG.Quasithin.Background.HMathieuFacts22Base
public import CFSG.Quasithin.Background.HMathieuSyl24GreedyBase
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

@[expose] public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem map_le_of_normalizer {W : Type*} [CommGroup W] (hLM : IsOver L M) {e : V ≃* W}
    {R R' : Subgroup (MulAut W)} (he : L.map (congrHom e) = R)
    (hN : Subgroup.normalizer (R : Set (MulAut W)) = R') {A : Subgroup (MulAut V)}
    (hA : A ≤ M) : A.map (congrHom e) ≤ R' := by
  have h1 : A.map (congrHom e) ≤ (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) :=
    Subgroup.map_mono (hA.trans hLM.2)
  have h2 := Subgroup.le_normalizer_map (H := L) (congrHom e)
  have h3 : Subgroup.normalizer ((L.map (congrHom e) : Subgroup (MulAut W)) : Set (MulAut W)) =
      R' :=
    (congrArg (fun H : Subgroup (MulAut W) => Subgroup.normalizer (H : Set (MulAut W))) he).trans hN
  exact h1.trans (h2.trans h3.le)

theorem inv_model {n : ℕ} {K P : Type*} [Group K] [Finite K] [Group P] [Finite P]
    (ψ : K →* MulAut (Wn n)) (hψ : Function.Injective ψ) (φ : P →* K) (hφ : Function.Injective φ)
    (hsyl : Nat.card P = 2 ^ (Nat.card K).factorization 2) (act : P → ℕ → ℕ)
    (hact : ∀ s, ∀ m < 2 ^ n, ψ (φ s) (toW n m) = toW n (act s m))
    (hlt : ∀ s, ∀ m < 2 ^ n, act s m < 2 ^ n) (e : V ≃* Wn n) {t : MulAut V}
    (htR : congrHom e t ∈ ψ.range) (ht : orderOf t = 2) :
    ∃ s : P, s ≠ 1 ∧ s * s = 1 ∧
      rkIdx (fixV (Subgroup.zpowers t)) = n - Nat.log 2 (fixMasks n act [s]).length := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, s, hs1, hgs⟩ := exists_conj_elemModel ψ hψ φ hφ hsyl e htR ht
  set e' := twistEquiv e ψ g with he'
  have hss : s * s = 1 := by
    have h1 : orderOf (ψ (φ s)) = 2 :=
      (congrArg orderOf hgs).symm.trans ((orderOf_injective _ (congrHom_injective e') t).trans ht)
    have h2 : orderOf s = 2 := (orderOf_injective (ψ.comp φ) (hψ.comp hφ) s).symm.trans h1
    rw [← sq, ← h2, pow_orderOf_eq_one]
  have hX : ∀ m < 2 ^ n,
      (MaskCoords.ofEquiv e').vm m ∈ fixV (Subgroup.zpowers t) ↔ act s m = m := by
    intro m hm
    rw [mem_fixV_zpowers_iff, MaskCoords.ofEquiv_vm]
    have h1 : e' (t (e'.symm (toW n m))) = toW n (act s m) := by
      rw [apply_of_congrHom_eq hgs, MulEquiv.apply_symm_apply, hact s m hm]
    have h2 : t (e'.symm (toW n m)) = e'.symm (toW n (act s m)) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    rw [h2]
    constructor
    · intro h3
      exact toW_inj (hlt s m hm) hm (e'.symm.injective h3)
    · intro h3
      rw [h3]
  have hcard : Nat.card (fixV (Subgroup.zpowers t)) = (fixMasks n act [s]).length :=
    (MaskCoords.ofEquiv e').card_eq _ _ fun m hm => (hX m hm).trans (by simp)
  exact ⟨s, hs1, hss, (MaskCoords.ofEquiv e').rkIdx_of_card hcard⟩

theorem exists_inv_of_arr_gen {n : ℕ} {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (ψ : ↥Γ →* MulAut (Wn n)) (hψ : Function.Injective ψ) (act : Array ℕ → ℕ → ℕ)
    (hact : ∀ (σ : ↥Γ) (a : Array ℕ), HasArr (σ : Equiv.Perm (Fin 24)) a → ∀ m,
      ψ σ (toW n m) = toW n (act a m)) (hlt : ∀ a m, act a m < 2 ^ n)
    {a : Array ℕ} (hok : inAutOK a = true) (hinv : ∀ i < 24, a[a[i]!]! = i) (i0 : Fin 24)
    (hne : a[(i0 : ℕ)]! ≠ i0)
    (hmem : ∀ σ : Equiv.Perm (Fin 24), σ ∈ AutPerm → HasArr σ a → σ ∈ Γ)
    {e : V ≃* Wn n} (he : L.map (congrHom e) = ψ.range) :
    ∃ t ∈ L, orderOf t = 2 ∧ ∀ m < 2 ^ n,
      (MaskCoords.ofEquiv e).vm m ∈ fixV (Subgroup.zpowers t) ↔ act a m = m := by
  obtain ⟨σ, hσA, hσa⟩ := exists_of_inAutOK hok
  have hσ := hmem σ hσA hσa
  have hσσ : σ * σ = 1 := Equiv.ext fun i => Fin.ext (by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hσa (σ i), hσa i]
    exact hinv i i.2)
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hne
    have := hσa i0
    rw [h1, Equiv.Perm.one_apply] at this
    exact this.symm
  have hmemR : ψ ⟨σ, hσ⟩ ∈ L.map (congrHom e) := he ▸ ⟨⟨σ, hσ⟩, rfl⟩
  obtain ⟨t, htL, hte⟩ := hmemR
  refine ⟨t, htL, ?_, fun m hm => ?_⟩
  · have h1 : orderOf (⟨σ, hσ⟩ : ↥Γ) = 2 := by
      refine orderOf_eq_prime (Subtype.ext ?_) fun h => hσ1 (congrArg Subtype.val h)
      rw [Subgroup.coe_pow, sq, hσσ]
      rfl
    exact (orderOf_injective _ (congrHom_injective e) t).symm.trans
      ((congrArg orderOf hte).trans ((orderOf_injective _ hψ _).trans h1))
  · rw [mem_fixV_zpowers_iff, MaskCoords.ofEquiv_vm]
    have h1 : e (t (e.symm (toW n m))) = toW n (act a m) := by
      rw [apply_of_congrHom_eq hte, MulEquiv.apply_symm_apply]
      exact hact ⟨σ, hσ⟩ a hσa m
    have h2 : t (e.symm (toW n m)) = e.symm (toW n (act a m)) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    rw [h2]
    constructor
    · intro h3
      exact toW_inj (hlt _ _) hm (e.symm.injective h3)
    · intro h3
      rw [h3]

theorem rkIdx_of_arr {n : ℕ} {t : MulAut V} {e : V ≃* Wn n} {P : ℕ → Bool}
    (hX : ∀ m < 2 ^ n, (MaskCoords.ofEquiv e).vm m ∈ fixV (Subgroup.zpowers t) ↔ P m = true) :
    rkIdx (fixV (Subgroup.zpowers t)) = n - Nat.log 2 ((List.range (2 ^ n)).filter P).length :=
  (MaskCoords.ofEquiv e).rkIdx_of_card ((MaskCoords.ofEquiv e).card_eq _ _ hX)

theorem mParam_eq_of [Finite V] (hLM : IsOver L M) {b : ℕ} {t : MulAut V} (htL : t ∈ L)
    (ht : orderOf t = 2) (hb : rkIdx (fixV (Subgroup.zpowers t)) = b)
    (hall : ∀ s ∈ M, orderOf s = 2 → b ≤ rkIdx (fixV (Subgroup.zpowers s))) :
    E3.mParam M = b := by
  have : Finite (MulAut V) := finite_mulAut V
  have htM : t ∈ M := hLM.1 htL
  unfold E3.mParam
  have hev : Even (Nat.card M) := by
    rw [even_iff_two_dvd, ← ht, ← Subgroup.orderOf_mk t htM]
    exact orderOf_dvd_natCard _
  rw [ite_eq_left hev]
  refine le_antisymm (Nat.sInf_le ⟨t, htM, ht, hb.symm⟩) (le_csInf ⟨b, t, htM, ht, hb.symm⟩ ?_)
  rintro _ ⟨s, hs, hso, rfl⟩
  exact hall s hs hso

theorem le_mParam_of [Finite V] {b : ℕ} (hV : b ≤ rk V)
    (hall : ∀ s ∈ M, orderOf s = 2 → b ≤ rkIdx (fixV (Subgroup.zpowers s))) :
    b ≤ E3.mParam M := by
  have : Finite (MulAut V) := finite_mulAut V
  unfold E3.mParam
  split_ifs with hev
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 2 (even_iff_two_dvd.1 hev)
    refine le_csInf ⟨_, (t : MulAut V), t.2, by rw [Subgroup.orderOf_coe, ht], rfl⟩ ?_
    rintro _ ⟨s, hs, hso, rfl⟩
    exact hall s hs hso
  · exact hV

noncomputable abbrev psiC22 : ↥mog22plus →* MulAut W10 := rhoC10 mog22plus le_rfl

theorem psiC22_phi22 (s : T22s2.Elem) {m : ℕ} (hm : m < 2 ^ 10) :
    psiC22 (phi22 s) (toW 10 m) = toW 10 (actM (matsC22[s.idx]!) m) := by
  rw [actM_matsC10 T22s2 (mats := matsC22) rfl s hm]
  exact rhoC10_toW mog22plus le_rfl _ (T22s2.hasArr_toSub _ _ s) m

theorem code22_card
    (h : MathieuCode22 L ⊤ ⊥) : Nat.card V = 2 ^ 10 :=
  (MaskCoords.ofEquiv (code22_std h).choose).card_eq_pow

noncomputable abbrev psiC23 : ↥mog23 →* MulAut W11 := rhoC11 mog23 inf_le_left

theorem psiC23_phi23 (s : T23s2.Elem) {m : ℕ} (hm : m < 2 ^ 11) :
    psiC23 (phi23 s) (toW 11 m) = toW 11 (actM (matsC23[s.idx]!) m) := by
  rw [actM_matsC11 T23s2 (mats := matsC23) rfl s hm]
  exact rhoC11_toW mog23 inf_le_left _ (T23s2.hasArr_toSub _ _ s) m

theorem code23_card
    (h : MathieuCode23 L ⊤ ⊥) : Nat.card V = 2 ^ 11 :=
  (MaskCoords.ofEquiv (code23_std h).choose).card_eq_pow

noncomputable abbrev psiC24 : ↥AutPerm →* MulAut W11 := rhoC11 AutPerm le_rfl

theorem psiC24_phi24 (s : T24s2.Elem) {m : ℕ} (hm : m < 2 ^ 11) :
    psiC24 (phi24 s) (toW 11 m) = toW 11 (actM (matsC24[s.idx]!) m) := by
  rw [actM_matsC11 T24s2 (mats := matsC24) rfl s hm]
  exact rhoC11_toW AutPerm le_rfl _ (T24s2.hasArr_toSub _ _ s) m

theorem code24_card (h : MathieuCode24 L ⊤ ⊥) : Nat.card V = 2 ^ 11 :=
  (MaskCoords.ofEquiv (code24_std h).choose).card_eq_pow

theorem stmtH13Card : StmtH13Card := by
  intro V _ L
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases h with h | h
    · exact cocode24_card h
    · exact code24_card h
  · rcases h with h | h
    · exact cocode23_card h
    · exact code23_card h
  · rcases h with h | h
    · exact cocode22_card h
    · exact code22_card h

theorem pRank_le_of_card_le [Finite V] {M : Subgroup (MulAut V)} {b : ℕ}
    (h : ∀ A : Subgroup (MulAut V), A ≤ M → IsElemAbelian2 A → ∀ k, Nat.card A = 2 ^ k → k ≤ b) :
    CFSG.Open.pRank 2 M ≤ b := by
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨E, hEM, hE, hEc⟩ := exists_isElemAbelian_card_pRank M
  exact h E hEM (isElemAbelian2_iff.2 hE) _ hEc

end CFSG.Quasithin.H.Mathieu

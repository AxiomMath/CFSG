module

public import CFSG.Quasithin.Background.HFNormal
public import CFSG.Quasithin.Background.HMathieuFacts
public import Certificates.Certificate7243
public import Certificates.Certificate7244

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem hf24All :
    forallGreedyAll pos24s2 inv24s2 predHF24 6 [] = true :=
  Certificates.certificate7243

theorem hf24Greedy {k : ℕ}
    (hk : k ≤ 6) : forallGreedy T24s2.invols predHF24 k [] = true :=
  (forallGreedyP_eq pos24s2_eq predHF24 k []).symm.trans (forallGreedyAll_le 6 [] hf24All k hk)

theorem codeFixTab24_get {a : T24s2.Elem} (ha : a * a = 1) :
    codeFixTab24[a.idx]! = fixMasks 11 codeAct24 [a] := by
  rw [codeFixTab24, getElem!_pos _ a.idx (by simpa using a.lt), Array.getElem_ofFn]
  have : T24s2.elemEquiv.symm ⟨a.idx, a.lt⟩ = a := rfl
  simp only [this, ha, ↓reduceIte]

theorem codeFixMasks24_eq {l : List T24s2.Elem}
    (hl : ∀ a ∈ l, a * a = 1) : codeFixMasks24 l = fixMasks 11 codeAct24 l := by
  cases l with
  | nil => rfl
  | cons a l => rw [codeFixMasks24, codeFixTab24_get (hl a List.mem_cons_self), ← fixMasks_cons]

theorem predHF24_spec {l : List T24s2.Elem} (hl : IndepList l)
    (h : predHF24 l = true) :
    (1 ≤ l.length → 11 - Nat.log 2 (fixMasks 11 codeAct24 l).length ≤ l.length + 1 →
        7 ≤ 11 - Nat.log 2 (fixMasks 11 codeAct24 l).length) ∧
      (l.length = 4 → 7 ≤ 11 - Nat.log 2 (fixMasks 11 codeAct24 l).length) ∧
      (l.length = 6 → Nat.log 2 (fixMasks 11 codeAct24 l).length % 2 = 0 ∧
        normalChainB T24s2 l = true) := by
  have hinv : ∀ a ∈ l, a * a = 1 := (isCommInvol_of_indepList hl).1
  rw [predHF24, codeFixMasks24_eq hinv] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun hk hd => ?_, fun h4 => ?_, fun h6 => ?_⟩
  · rcases h1 with (h | h) | h
    · omega
    · exact absurd hd h
    · exact h
  · rcases h2 with h | h
    · exact absurd h4 h
    · exact h
  · rcases h3 with h | h
    · exact absurd h6 h
    · exact h

theorem conj_mem_E64
    (B : Subgroup T24s2.Elem) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (hcard : Nat.card B = 2 ^ 6) (t : T24s2.Elem) {b : T24s2.Elem}
    (hb : b ∈ B) : t * b * t⁻¹ ∈ B :=
  conj_mem_of_forallGreedy (hf24Greedy le_rfl)
    (fun _ hl hlen hp => ((predHF24_spec hl hp).2.2 hlen).2) B hcomm hsq hcard t hb

theorem chainActC24 (e : V ≃* W11) (g : ↥AutPerm) :
    ChainAct (MaskCoords.ofEquiv (twistEquiv e psiC24 g)) (chainAut e psiC24 phi24 g)
      codeAct24 :=
  chainAct_twist e psiC24 phi24 g (fun s _ hm => psiC24_phi24 s hm)
    (fun s _ hm => by
      rw [codeAct24, actM_matsC11 T24s2 (mats := matsC24) rfl s hm]
      exact actC11_lt _ _)

theorem chainAutC24_injective
    (e : V ≃* W11) (g : ↥AutPerm) :
    Function.Injective (chainAut e psiC24 phi24 g) :=
  chainAut_injective (rhoC11_injective _ _) (T24s2.toSub_injective _ _) g

theorem map_le_rangeC24
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rhoC11 AutPerm le_rfl).range) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) : A.map (congrHom e) ≤ psiC24.range :=
  map_le_of_normalizer hLM he normalizer_rhoC11_autPerm hA

theorem chainHF24
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rhoC11 AutPerm le_rfl).range) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hk : k ≤ 6) (hcard : Nat.card A = 2 ^ k) :
    ∃ g : ↥AutPerm, ∃ l : List T24s2.Elem, IndepList l ∧ predHF24 l = true ∧
      IsChainSub (chainAut e psiC24 phi24 g) l A ∧ l.length = k := by
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC24 (rhoC11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
    (hf24Greedy hk) e (map_le_rangeC24 hLM he hA) hAe hcard
  have hcl := card_of_chainSub hchain (chainAutC24_injective e g) hind
  rw [hcard] at hcl
  exact ⟨g, l, hind, hpred, hchain, (Nat.pow_right_injective (le_refl 2) hcl).symm⟩

theorem rkIdx_fixV_chainC24 {e : V ≃* W11} {g : ↥AutPerm}
    {l : List T24s2.Elem} {A : Subgroup (MulAut V)}
    (hchain : IsChainSub (chainAut e psiC24 phi24 g) l A) :
    rkIdx (fixV A) = 11 - Nat.log 2 (fixMasks 11 codeAct24 l).length :=
  (MaskCoords.ofEquiv (twistEquiv e psiC24 g)).rkIdx_of_card (card_fixV (chainActC24 e g) hchain)

theorem rkIdx_le_rkIdx_of_le [Finite V] {U W : Subgroup V} (h : U ≤ W) : rkIdx W ≤ rkIdx U := by
  unfold rkIdx
  exact padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite (Subgroup.index_dvd_of_le h)

theorem code24_alphaSet
    [Finite V] (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) : ∀ k ∈ alphaSet M, 7 ≤ k := by
  rintro k ⟨hk2, U, -, hUk, hkle⟩
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨e, he⟩ := code24_std h
  obtain ⟨E, hEM, hE, hEc⟩ := exists_isElemAbelian_card_pRank (M ⊓ centSub U)
  have hE2 : IsElemAbelian2 E := isElemAbelian2_iff.2 hE
  have hj6 := code24_card_le hLM h (hEM.trans inf_le_left) hE2 hEc
  obtain ⟨g, l, hind, hpred, hchain, hlen⟩ :=
    chainHF24 hLM he (hEM.trans inf_le_left) hE2 hj6 hEc
  have hr := rkIdx_fixV_chainC24 hchain
  have hUE : U ≤ fixV E := fun u hu x hx => mem_centSub.1 (hEM hx).2 u hu
  have hle := rkIdx_le_rkIdx_of_le hUE
  have h1 := (predHF24_spec hind hpred).1 (by omega) (by omega)
  omega

theorem code24_seven_le_rkIdx_E16
    (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {A : Subgroup (MulAut V)} (hA : A ≤ M)
    (hAe : IsElemAbelian2 A) (hcard : Nat.card A = 2 ^ 4) : 7 ≤ rkIdx (fixV A) := by
  obtain ⟨e, he⟩ := code24_std h
  obtain ⟨g, l, hind, hpred, hchain, hlen⟩ := chainHF24 hLM he hA hAe (by norm_num) hcard
  rw [rkIdx_fixV_chainC24 hchain]
  exact (predHF24_spec hind hpred).2.1 hlen

theorem code24_even_E64
    (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {A : Subgroup (MulAut V)} (hA : A ≤ M)
    (hAe : IsElemAbelian2 A) (hcard : Nat.card A = 2 ^ 6) :
    ∃ d : ℕ, d % 2 = 0 ∧ Nat.card (fixV A) = 2 ^ d := by
  obtain ⟨e, he⟩ := code24_std h
  obtain ⟨g, l, hind, hpred, hchain, hlen⟩ := chainHF24 hLM he hA hAe le_rfl hcard
  have hc := card_fixV (chainActC24 e g) hchain
  obtain ⟨hd, -⟩ := (predHF24_spec hind hpred).2.2 hlen
  refine ⟨Nat.log 2 (fixMasks 11 codeAct24 l).length, hd, ?_⟩
  have hfin : Finite V := (MaskCoords.ofEquiv (twistEquiv e psiC24 g)).finite
  obtain ⟨c, hcV⟩ : ∃ c : ℕ, Nat.card (fixV A) = 2 ^ c := by
    have hdvd : Nat.card (fixV A) ∣ 2 ^ 11 := by
      rw [← (MaskCoords.ofEquiv (twistEquiv e psiC24 g)).card_eq_pow]
      exact Subgroup.card_subgroup_dvd_card _
    exact (Nat.dvd_prime_pow Nat.prime_two).1 hdvd |>.imp fun c hc => hc.2
  rw [hcV, ← hc, hcV, Nat.log_pow (by norm_num)]

theorem oddC24_case
    {T : PT 24} [Fact (T.check = true)] (hT : T.allOK okAut = true) {p : ℕ}
    [Fact p.Prime] (hsyl : Nat.card T.Elem = p ^ (Nat.card ↥AutPerm).factorization p)
    {mats : Array (List ℕ)} (hmats : mats = matsOfC11 T) {b : ℕ}
    (hodd : oddFixOK 11 b T mats) (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rhoC11 AutPerm le_rfl).range)
    {z : MulAut V} (hzM : z ∈ M) (hz : orderOf z = p) :
    11 - b ≤ rkIdx (fixV (Subgroup.zpowers z)) := by
  have hzR : congrHom e z ∈ psiC24.range :=
    map_le_rangeC24 hLM he ((Subgroup.zpowers_le).2 hzM) ⟨z, Subgroup.mem_zpowers z, rfl⟩
  obtain ⟨g, s, hs1, hgs⟩ := exists_conj_elemModel psiC24 (rhoC11_injective _ _)
    (T.toSub AutPerm (T.mem_autPerm (fun _ _ h => h) hT)) (T.toSub_injective _ _) hsyl e hzR hz
  set e' := twistEquiv e psiC24 g with he'
  set act : T.Elem → ℕ → ℕ := fun q m => actM (mats[q.idx]!) m with hactdef
  have hactC : ∀ m < 2 ^ 11, act s m = actC11 (T.arr s) m := fun m hm =>
    actM_matsC11 T hmats s hm
  have hact : ∀ m < 2 ^ 11,
      psiC24 (T.toSub AutPerm (T.mem_autPerm (fun _ _ h => h) hT) s) (toW 11 m) =
        toW 11 (act s m) := by
    intro m hm
    rw [hactC m hm]
    exact rhoC11_toW AutPerm le_rfl _ (T.hasArr_toSub _ _ s) m
  have hX : ∀ m < 2 ^ 11,
      (MaskCoords.ofEquiv e').vm m ∈ fixV (Subgroup.zpowers z) ↔ act s m = m := by
    intro m hm
    rw [mem_fixV_zpowers_iff, MaskCoords.ofEquiv_vm]
    have h1 : e' (z (e'.symm (toW 11 m))) = toW 11 (act s m) := by
      rw [apply_of_congrHom_eq hgs, MulEquiv.apply_symm_apply, hact m hm]
    have h2 : z (e'.symm (toW 11 m)) = e'.symm (toW 11 (act s m)) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    rw [h2]
    constructor
    · intro h3
      exact toW_inj (by rw [hactC m hm]; exact actC11_lt _ _) hm (e'.symm.injective h3)
    · intro h3
      rw [h3]
  have hcard : Nat.card (fixV (Subgroup.zpowers z)) = (fixMasks 11 act [s]).length :=
    (MaskCoords.ofEquiv e').card_eq _ _ fun m hm => (hX m hm).trans (by simp)
  have hle := hodd s hs1
  have := (MaskCoords.ofEquiv e').finite
  have hpos : 0 < (fixMasks 11 act [s]).length := hcard ▸ Nat.card_pos
  have hlog : Nat.log 2 (fixMasks 11 act [s]).length ≤ b :=
    Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hpos.ne' (lt_of_le_of_lt hle
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self b))))
  rw [(MaskCoords.ofEquiv e').rkIdx_of_card hcard]
  omega

theorem code24_odd_le
    (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {z : MulAut V} (hzM : z ∈ M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hz : orderOf z = p) :
    6 ≤ rkIdx (fixV (Subgroup.zpowers z)) ∧ (p ≠ 3 → 7 ≤ rkIdx (fixV (Subgroup.zpowers z))) := by
  obtain ⟨e, he⟩ := code24_std h
  obtain ⟨k0, hk0⟩ : congrHom e z ∈ psiC24.range :=
    map_le_rangeC24 hLM he ((Subgroup.zpowers_le).2 hzM) ⟨z, Subgroup.mem_zpowers z, rfl⟩
  have hk0o : orderOf k0 = p :=
    (orderOf_injective psiC24 (rhoC11_injective _ _) k0).symm.trans ((congrArg orderOf hk0).trans
      ((orderOf_injective _ (congrHom_injective e) z).trans hz))
  have hpK : p ∣ 244823040 := by
    have := hk0o ▸ orderOf_dvd_natCard k0
    rwa [card_AutPerm] at this
  obtain ⟨-, h3, h5, h7, h11, h23⟩ := Certificates.certificate7244
  rcases prime_dvd_m24 hp hpK hp2 with rfl | rfl | rfl | rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have := oddC24_case T24s3_ok.2.2 (card_T24sp (by norm_num) (n := 3) T24s3_ok.2.1
      (by norm_num : (244823040 : ℕ) = 3 ^ 3 * 9067520) (by norm_num)) rfl h3 hLM he hzM hz
    exact ⟨by omega, fun h => absurd rfl h⟩
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have := oddC24_case T24s5_ok.2.2 (card_T24sp (by norm_num) (n := 1) T24s5_ok.2.1
      (by norm_num : (244823040 : ℕ) = 5 ^ 1 * 48964608) (by norm_num)) rfl h5 hLM he hzM hz
    exact ⟨by omega, fun _ => by omega⟩
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have := oddC24_case T24s7_ok.2.2 (card_T24sp (by norm_num) (n := 1) T24s7_ok.2.1
      (by norm_num : (244823040 : ℕ) = 7 ^ 1 * 34974720) (by norm_num)) rfl h7 hLM he hzM hz
    exact ⟨by omega, fun _ => by omega⟩
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    have := oddC24_case T24s11_ok.2.2 (card_T24sp (by norm_num) (n := 1) T24s11_ok.2.1
      (by norm_num : (244823040 : ℕ) = 11 ^ 1 * 22256640) (by norm_num)) rfl h11 hLM he hzM hz
    exact ⟨by omega, fun _ => by omega⟩
  · have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    have := oddC24_case T24s23_ok.2.2 (card_T24sp (by norm_num) (n := 1) T24s23_ok.2.1
      (by norm_num : (244823040 : ℕ) = 23 ^ 1 * 10644480) (by norm_num)) rfl h23 hLM he hzM hz
    exact ⟨by omega, fun _ => by omega⟩

theorem code24_betaH
    [Finite V] (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) : (6 : ℕ∞) ≤ betaH M := by
  have : Finite (MulAut V) := finite_mulAut V
  refine le_betaH_iff_isPGroup.mpr fun U _ hnp => ?_
  obtain ⟨p, hp, hp2, hpdvd⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥(M ⊓ centSub U) := by
    by_contra hno
    push Not at hno
    apply hnp
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
    intro d hd hdd
    by_contra hd2
    exact hno d hd hd2 hdd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ centSub U)) p hpdvd
  have hyo : orderOf (y : MulAut V) = p := by rw [Subgroup.orderOf_coe, hy]
  have hUy : U ≤ fixV (Subgroup.zpowers (y : MulAut V)) := fun u hu =>
    mem_fixV_zpowers_iff.mpr (mem_centSub.mp y.2.2 u hu)
  have h6 := (code24_odd_le hLM h y.2.1 hp hp2 hyo).1
  exact_mod_cast h6.trans (rkIdx_le_rkIdx_of_le hUy)

theorem code24_orderOf_ne_nine
    (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {y : MulAut V} (hyM : y ∈ M) :
    orderOf y ≠ 9 := by
  intro hy9
  obtain ⟨e, he⟩ := code24_std h
  obtain ⟨k0, hk0⟩ : congrHom e y ∈ psiC24.range :=
    map_le_rangeC24 hLM he ((Subgroup.zpowers_le).2 hyM) ⟨y, Subgroup.mem_zpowers y, rfl⟩
  have hk0o : orderOf k0 = 9 :=
    (orderOf_injective psiC24 (rhoC11_injective _ _) k0).symm.trans ((congrArg orderOf hk0).trans
      ((orderOf_injective _ (congrHom_injective e) y).trans hy9))
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hH : IsPGroup 3 (Subgroup.zpowers k0) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hk0o]; norm_num)
  set φ3 := T24s3.toSub AutPerm (T24s3.mem_autPerm (fun _ _ h => h) T24s3_ok.2.2) with hφ3
  obtain ⟨g, hg⟩ := exists_conj_le_range φ3 (T24s3.toSub_injective _ _)
    (card_T24sp (by norm_num) (n := 3) T24s3_ok.2.1
      (by norm_num : (244823040 : ℕ) = 3 ^ 3 * 9067520) (by norm_num)) hH
  obtain ⟨s, hs⟩ := hg k0 (Subgroup.mem_zpowers k0)
  have hso : orderOf s = 9 := by
    rw [← orderOf_injective φ3 (T24s3.toSub_injective _ _) s, hs]
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective k0
    rw [← hk0o, ← this]
    rfl
  have h3 := Certificates.certificate7244.1 s
  have hd : orderOf s ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_three, ← mul_assoc]; exact h3)
  rw [hso] at hd
  omega

theorem code24_odd_fact
    [Finite V] (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {x : MulAut V} (hxM : x ∈ M)
    (hx1 : x ≠ 1) (hxo : Odd (orderOf x)) (hx6 : rkIdx (fixV (Subgroup.zpowers x)) ≤ 6) :
    orderOf x = 3 ∧ rkIdx (fixV (Subgroup.zpowers x)) = 6 := by
  have : Finite (MulAut V) := finite_mulAut V
  have hn0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hn1 : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.1 h1)
  have key : ∀ q : ℕ, q.Prime → q ∣ orderOf x → q = 3 := by
    intro q hq hqn
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hxo) (even_iff_two_dvd.2 hqn)
    have hyo : orderOf (x ^ (orderOf x / q)) = q := orderOf_pow_orderOf_div hn0 hqn
    have hle : rkIdx (fixV (Subgroup.zpowers (x ^ (orderOf x / q)))) ≤
        rkIdx (fixV (Subgroup.zpowers x)) := rkIdx_le_rkIdx_of_le (fixV_zpowers_pow_le x _)
    by_contra hq3
    have := (code24_odd_le hLM h (M.pow_mem hxM _) hq hq2 hyo).2 hq3
    omega
  have h3 : 3 ∣ orderOf x := by
    have := key _ (Nat.minFac_prime hn1) (Nat.minFac_dvd _)
    rw [← this]
    exact Nat.minFac_dvd _
  have hn3 : orderOf x = 3 := by
    by_contra hne
    obtain ⟨m, hm⟩ := h3
    have hm1 : m ≠ 1 := fun h1 => hne (by rw [hm, h1])
    have hmq := key m.minFac (Nat.minFac_prime hm1)
      ((Nat.minFac_dvd m).trans ⟨3, by rw [hm]; ring⟩)
    have h9 : 9 ∣ orderOf x := by
      rw [hm]
      have : 3 ∣ m := hmq ▸ Nat.minFac_dvd m
      exact Nat.mul_dvd_mul_left 3 this
    exact code24_orderOf_ne_nine hLM h (M.pow_mem hxM _) (orderOf_pow_orderOf_div hn0 h9)
  exact ⟨hn3, le_antisymm hx6 (code24_odd_le hLM h hxM (by norm_num) (by norm_num) hn3).1⟩

end CFSG.Quasithin.H.Mathieu

module

public import CFSG.Quasithin.H13.A5M12Cent
public import Certificates.Certificate7113
public import Certificates.Certificate7114

public section

namespace CFSG.Quasithin.H13.A5.M12

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.Vol2.Ch10.SecA.C10P01 CFSG.QuasithinUnique.Setup.X1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem dodecadE_mul_allOnes_ne : dodecadE * G6.allOnes 24 ≠ dodecadE := by
  intro h
  have h1 : G6.allOnes 24 = 1 := mul_eq_left.mp h
  have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
  revert h2
  decide +kernel

theorem relIndex_m24Fix :
    (m24Fix dodecadE).relIndex m24Pair = 2 := by
  obtain ⟨τ, hτ, hτn⟩ := exists_mem_m24Pair_not_mem
  have hτ2 : G6.permAct 24 τ dodecadE = dodecadE * G6.allOnes 24 :=
    hτ.2.resolve_left fun h => hτn ⟨hτ.1, h⟩
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨τ, hτ⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hbτ : G6.permAct 24 ((b : Equiv.Perm (Fin 24)) * τ) dodecadE =
      G6.permAct 24 (b : Equiv.Perm (Fin 24)) dodecadE * G6.allOnes 24 := by
    rw [map_mul, MulAut.mul_apply, hτ2, map_mul, H.Mathieu.permAct_allOnes]
  have hmul : ((b * ⟨τ, hτ⟩ : ↥m24Pair) : Equiv.Perm (Fin 24)) = (b : Equiv.Perm (Fin 24)) * τ :=
    rfl
  rw [hmul]
  rcases b.2.2 with hb | hb
  · refine Or.inr ⟨⟨b.2.1, hb⟩, fun h => ?_⟩
    have h2 := h.2
    rw [hbτ, hb] at h2
    exact dodecadE_mul_allOnes_ne h2
  · refine Or.inl ⟨⟨AutPerm.mul_mem b.2.1 hτ.1, ?_⟩, fun h => ?_⟩
    · rw [hbτ, hb, mul_assoc, H.Mathieu.allOnes_sq, mul_one]
    · have h2 := h.2
      rw [hb] at h2
      exact dodecadE_mul_allOnes_ne h2

theorem card_m24Pair :
    Nat.card ↥m24Pair = 190080 := by
  obtain ⟨-, hcard⟩ := m24Fix_dodecadE_props
  have h3 := Subgroup.relIndex_mul_card (H := m24Fix dodecadE) (K := m24Pair)
  rw [inf_of_le_left m24Fix_le_m24Pair, hcard, relIndex_m24Fix] at h3
  omega

theorem mem_m24Pair_of_allOK (T : PT 24) [Fact (T.check = true)] (h : T.allOK okPair = true)
    (p : T.Elem) : T.perm p ∈ m24Pair := by
  have hok := PT.ok_of_allOK h p
  simp only [okPair, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
  have harr := T.hasArr_perm p
  refine ⟨mem_AutPerm_of_arr (T.invPairOK_arr p) hok.1, ?_⟩
  rcases hok.2 with h0 | h1
  · exact Or.inl (permAct_dodecadE_of_arr harr h0)
  · right
    rw [permAct_dodecadE_of_arr harr h1, bvec_compl]
    rfl

noncomputable abbrev psi12 : ↥m24Pair →* MulAut W10 := rhoC12 m24Pair le_rfl

abbrev phi12 : T12s2.Elem →* ↥m24Pair :=
  T12s2.toSub m24Pair (mem_m24Pair_of_allOK T12s2 T12s2_ok.2.2)

theorem xorLin_actC12 (a : Array ℕ) : XorLin (actC12 a) :=
  ((actM_xor _).comp (actM_xor _)).comp (actM_xor _)

theorem actM_mats12 (T : PT 24) [Fact (T.check = true)] {mats : Array (List ℕ)}
    (hm : mats = matsOf12 T) (p : T.Elem) {m : ℕ} (hm2 : m < 2 ^ 10) :
    actM (mats[p.idx]!) m = actC12 (T.arr p) m := by
  have hlt : p.idx < T.elems.size := by rw [T.size_elems]; exact p.lt
  rw [hm, matsOf12, getElem!_pos _ p.idx (by simpa using hlt), Array.getElem_map, PT.arr,
    getElem!_pos _ p.idx hlt, actM_matOf (xorLin_actC12 _) 10 m hm2]

theorem psi12_phi12 (s : T12s2.Elem) {m : ℕ} (hm : m < 2 ^ 10) :
    psi12 (phi12 s) (toW 10 m) = toW 10 (act12s2 s m) := by
  rw [act12s2, actM_mats12 T12s2 (mats := mats12s2) rfl s hm]
  exact rhoC12_toW m24Pair le_rfl _ (T12s2.hasArr_toSub _ _ s) m

theorem card_T12s2 :
    Nat.card T12s2.Elem = 2 ^ (Nat.card ↥m24Pair).factorization 2 := by
  rw [PT.card_elem, T12s2_ok.2.1, card_m24Pair,
    show (190080 : ℕ) = 2 ^ 7 * 1485 by norm_num, factorization_eq Nat.prime_two (by norm_num)]
  norm_num

theorem card_T12sp
    {T : PT 24} {p n b : ℕ} (hp : p.Prime) (hn : T.n = p ^ n)
    (hb : (190080 : ℕ) = p ^ n * b) (hpb : ¬ p ∣ b) :
    Nat.card T.Elem = p ^ (Nat.card ↥m24Pair).factorization p := by
  rw [PT.card_elem, hn, card_m24Pair, hb, factorization_eq hp hpb]

theorem greedy12 :
    ∀ k ∈ [1, 2, 3, 4, 5], forallGreedy T12s2.invols (pred12 k) k [] = true :=
  fun k hk => (forallGreedyP_eq pos12s2_eq (pred12 k) k []).symm.trans
    (Certificates.certificate7113 k hk)

theorem pred12_spec {k : ℕ} {l : List T12s2.Elem}
    (h : pred12 k l = true) :
    k ≤ 4 ∧ k + 2 ≤ 10 - Nat.log 2 (fixMasks 10 act12s2 l).length ∧
      (k = 4 → (fixMasks 10 act12s2 l).length ≤ 2 ^ 3 ∧ xiCheck 10 8 act12s2 l = true) := by
  simp only [pred12, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨hk, hd⟩, hxi⟩ := h
  exact ⟨hk, hd, fun h4 => hxi.resolve_left (not_not.2 h4)⟩

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem chain12
    (hLM : IsOver L M) {e : V ≃* W10}
    (he : L.map (congrHom e) = (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range)
    {A : Subgroup (MulAut V)} (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ}
    (hk : k ∈ [1, 2, 3, 4, 5]) (hcard : Nat.card A = 2 ^ k) :
    ∃ g : ↥m24Pair, ∃ l : List T12s2.Elem, IndepList l ∧ pred12 k l = true ∧
      IsChainSub (chainAut e psi12 phi12 g) l A :=
  exists_chainModel psi12 rhoC12_m24Pair_injective phi12 (T12s2.toSub_injective _ _) card_T12s2
    (fun _ h1 h2 => T12s2.mem_invols h1 h2) (greedy12 k hk) e
    (map_le_of_normalizer hLM he normalizer_rhoC12 hA) hAe hcard

theorem chainAct12 (e : V ≃* W10) (g : ↥m24Pair) :
    ChainAct (MaskCoords.ofEquiv (twistEquiv e psi12 g)) (chainAut e psi12 phi12 g) act12s2 :=
  chainAct_twist e psi12 phi12 g (fun s _ hm => psi12_phi12 s hm)
    (fun s _ hm => by
      rw [act12s2, actM_mats12 T12s2 (mats := mats12s2) rfl s hm]
      exact actC12_lt _ _)

theorem m12_card
    (h : M12Ten L ⊤ ⊥) : Nat.card V = 2 ^ 10 :=
  (MaskCoords.ofEquiv (m12_std h).choose).card_eq_pow

theorem m12_card_le
    (hLM : IsOver L M) (h : M12Ten L ⊤ ⊥) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hcard : Nat.card A = 2 ^ k) : k ≤ 4 := by
  obtain ⟨e, he⟩ := m12_std h
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
  obtain ⟨g, l, -, hpred, -⟩ := chain12 hLM he (hBA.trans hA) hBe (by simp) hB
  exact absurd (pred12_spec hpred).1 (by norm_num)

theorem m12_E16
    (hLM : IsOver L M) (h : M12Ten L ⊤ ⊥) {A : Subgroup (MulAut V)} (hAM : A ≤ M)
    (hAe : IsElemAbelian2 A) (hcard : Nat.card A = 16) :
    Nat.card ↥(fixV A) ≤ 2 ^ 3 ∧ 2 ^ 8 ≤ Nat.card ↥(xiV A) := by
  obtain ⟨e, he⟩ := m12_std h
  obtain ⟨g, l, -, hpred, hchain⟩ := chain12 hLM he hAM hAe (k := 4) (by simp)
    (by rw [hcard]; norm_num)
  obtain ⟨hF, hxi⟩ := (pred12_spec hpred).2.2 rfl
  exact ⟨(card_fixV (chainAct12 e g) hchain).trans_le hF,
    pow_le_card_xiV (chainAct12 e g) hchain
      (chainAut_injective rhoC12_m24Pair_injective (T12s2.toSub_injective _ _) g) hxi⟩

theorem m12_not_isFOneModule
    [Finite V] (hLM : IsOver L M) (h : M12Ten L ⊤ ⊥) : ¬ IsFOneModule M := by
  rintro ⟨A, ⟨hAM, hA1, hAe⟩, hoff⟩
  obtain ⟨e, he⟩ := m12_std h
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_isElemAbelian (isElemAbelian2_iff.mp hAe)
  have hk4 := m12_card_le hLM h hAM hAe hk
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero] at hk
    exact hA1 (Subgroup.eq_bot_of_card_eq A hk)
  obtain ⟨g, l, -, hpred, hchain⟩ := chain12 hLM he hAM hAe (k := k)
    (by interval_cases k <;> simp) hk
  obtain ⟨-, hd, -⟩ := pred12_spec hpred
  have hr := (MaskCoords.ofEquiv (twistEquiv e psi12 g)).rkIdx_of_card
    (card_fixV (chainAct12 e g) hchain)
  have hrk : rk ↥A = k := by
    unfold rk
    rw [hk, padicValNat.prime_pow]
  omega

theorem m12_alphaH
    [Finite V] (hLM : IsOver L M) (h : M12Ten L ⊤ ⊥) : alphaH M = 1 :=
  alphaH_eq_one_of_not_isFOneModule (m12_not_isFOneModule hLM h)

theorem prime_dvd_m12pair {p : ℕ} (hp : p.Prime) (hdvd : p ∣ 190080) (hp2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 11 := by
  have e : (190080 : ℕ) = 2 ^ 7 * 3 ^ 3 * 5 * 11 := by norm_num
  rw [e] at hdvd
  have hq : ∀ q : ℕ, q.Prime → ∀ k, p ∣ q ^ k → p = q := fun q hq k h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h)
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd (hq 2 Nat.prime_two 7 h) hp2
      · exact Or.inl (hq 3 (by norm_num) 3 h)
    · exact Or.inr (Or.inl (hq 5 (by norm_num) 1 (by simpa using h)))
  · exact Or.inr (Or.inr (hq 11 (by norm_num) 1 (by simpa using h)))

theorem odd12_case
    {T : PT 24} [Fact (T.check = true)] (hT : T.allOK okPair = true) {p : ℕ}
    [Fact p.Prime] (hsyl : Nat.card T.Elem = p ^ (Nat.card ↥m24Pair).factorization p)
    {mats : Array (List ℕ)} (hmats : mats = matsOf12 T) (hodd : odd12OK T mats)
    (hLM : IsOver L M) {e : V ≃* W10}
    (he : L.map (congrHom e) = (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range)
    {z : MulAut V} (hzM : z ∈ M) (hz : orderOf z = p) :
    6 ≤ rkIdx (fixV (Subgroup.zpowers z)) := by
  have hzR : congrHom e z ∈ psi12.range :=
    map_le_of_normalizer hLM he normalizer_rhoC12 ((Subgroup.zpowers_le).2 hzM)
      ⟨z, Subgroup.mem_zpowers z, rfl⟩
  obtain ⟨g, s, hs1, hgs⟩ := exists_conj_elemModel psi12 rhoC12_m24Pair_injective
    (T.toSub m24Pair (mem_m24Pair_of_allOK T hT)) (T.toSub_injective _ _) hsyl e hzR hz
  set e' := twistEquiv e psi12 g with he'
  set act : T.Elem → ℕ → ℕ := fun q m => actM (mats[q.idx]!) m with hactdef
  have hactC : ∀ m < 2 ^ 10, act s m = actC12 (T.arr s) m := fun m hm =>
    actM_mats12 T hmats s hm
  have hact : ∀ m < 2 ^ 10,
      psi12 (T.toSub m24Pair (mem_m24Pair_of_allOK T hT) s) (toW 10 m) = toW 10 (act s m) := by
    intro m hm
    rw [hactC m hm]
    exact rhoC12_toW m24Pair le_rfl _ (T.hasArr_toSub _ _ s) m
  have hX : ∀ m < 2 ^ 10,
      (MaskCoords.ofEquiv e').vm m ∈ fixV (Subgroup.zpowers z) ↔ act s m = m := by
    intro m hm
    rw [mem_fixV_zpowers_iff, MaskCoords.ofEquiv_vm]
    have h1 : e' (z (e'.symm (toW 10 m))) = toW 10 (act s m) := by
      rw [apply_of_congrHom_eq hgs, MulEquiv.apply_symm_apply, hact m hm]
    have h2 : z (e'.symm (toW 10 m)) = e'.symm (toW 10 (act s m)) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    rw [h2]
    constructor
    · intro h3
      exact toW_inj (by rw [hactC m hm]; exact actC12_lt _ _) hm (e'.symm.injective h3)
    · intro h3
      rw [h3]
  have hcard : Nat.card (fixV (Subgroup.zpowers z)) = (fixMasks 10 act [s]).length :=
    (MaskCoords.ofEquiv e').card_eq _ _ fun m hm => (hX m hm).trans (by simp)
  have hle := hodd s hs1
  have := (MaskCoords.ofEquiv e').finite
  have hpos : 0 < (fixMasks 10 act [s]).length := hcard ▸ Nat.card_pos
  have hlog : Nat.log 2 (fixMasks 10 act [s]).length ≤ 4 :=
    Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hpos.ne' (lt_of_le_of_lt hle (by norm_num)))
  rw [(MaskCoords.ofEquiv e').rkIdx_of_card hcard]
  omega

theorem m12_six_le_rkIdx_odd
    (hLM : IsOver L M) (h : M12Ten L ⊤ ⊥) {z : MulAut V} (hzM : z ∈ M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hz : orderOf z = p) :
    6 ≤ rkIdx (fixV (Subgroup.zpowers z)) := by
  obtain ⟨e, he⟩ := m12_std h
  obtain ⟨k0, hk0⟩ : congrHom e z ∈ psi12.range :=
    map_le_of_normalizer hLM he normalizer_rhoC12 ((Subgroup.zpowers_le).2 hzM)
      ⟨z, Subgroup.mem_zpowers z, rfl⟩
  have hk0o : orderOf k0 = p :=
    (orderOf_injective psi12 rhoC12_m24Pair_injective k0).symm.trans
      ((congrArg orderOf hk0).trans ((orderOf_injective _ (congrHom_injective e) z).trans hz))
  have hpK : p ∣ 190080 := by
    have := hk0o ▸ orderOf_dvd_natCard k0
    rwa [card_m24Pair] at this
  obtain ⟨h3, h5, h11⟩ := Certificates.certificate7114
  rcases prime_dvd_m12pair hp hpK hp2 with rfl | rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact odd12_case T12s3_ok.2.2 (card_T12sp (by norm_num) (n := 3) T12s3_ok.2.1
      (by norm_num : (190080 : ℕ) = 3 ^ 3 * 7040) (by norm_num)) rfl h3 hLM he hzM hz
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact odd12_case T12s5_ok.2.2 (card_T12sp (by norm_num) (n := 1) T12s5_ok.2.1
      (by norm_num : (190080 : ℕ) = 5 ^ 1 * 38016) (by norm_num)) rfl h5 hLM he hzM hz
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact odd12_case T12s11_ok.2.2 (card_T12sp (by norm_num) (n := 1) T12s11_ok.2.1
      (by norm_num : (190080 : ℕ) = 11 ^ 1 * 17280) (by norm_num)) rfl h11 hLM he hzM hz

theorem m12_betaH
    [Finite V] (hLM : IsOver L M) (h : M12Ten L ⊤ ⊥) : (6 : ℕ∞) ≤ betaH M := by
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
  have h6 := m12_six_le_rkIdx_odd hLM h y.2.1 hp hp2 hyo
  have hle : rkIdx (fixV (Subgroup.zpowers (y : MulAut V))) ≤ rkIdx U := by
    unfold rkIdx
    exact padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite
      (Subgroup.index_dvd_of_le hUy)
  exact_mod_cast h6.trans hle

end CFSG.Quasithin.H13.A5.M12

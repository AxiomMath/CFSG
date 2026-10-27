module

public import CFSG.Quasithin.Background.HMathieuFacts
public import Certificates.Certificate7110
public import Certificates.Certificate7111

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem greedyC23 :
    ∀ k ∈ [1, 2, 3, 4], forallGreedy T23s2.invols (predC23 k) k [] = true :=
  fun k hk => (forallGreedyP_eq pos23s2_eq (predC23 k) k []).symm.trans
    (Certificates.certificate7110 k hk)

theorem predC23_spec {k : ℕ} {l : List T23s2.Elem}
    (h : predC23 k l = true) :
    k ≤ 4 ∧ k + 2 ≤ 11 - Nat.log 2 (fixMasks 11 actC23s2 l).length ∧
      (k = 4 → xiCheck 11 10 actC23s2 l = true) := by
  simp only [predC23, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨hk, hd⟩, hxi⟩ := h
  exact ⟨hk, hd, fun h4 => hxi.resolve_left (not_not.2 h4)⟩

theorem chainC23
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rhoC11 mog23 inf_le_left).range) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hk : k ∈ [1, 2, 3, 4])
    (hcard : Nat.card A = 2 ^ k) :
    ∃ g : ↥mog23, ∃ l : List T23s2.Elem, IndepList l ∧ predC23 k l = true ∧
      IsChainSub (chainAut e psiC23 phi23 g) l A :=
  exists_chainModel psiC23 (rhoC11_injective _ _) phi23 (T23s2.toSub_injective _ _) card_T23s2
    (fun _ h1 h2 => T23s2.mem_invols h1 h2) (greedyC23 k hk) e
    (map_le_of_normalizer hLM he normalizer_rhoC11_mog23 hA) hAe hcard

theorem chainActC23 (e : V ≃* W11) (g : ↥mog23) :
    ChainAct (MaskCoords.ofEquiv (twistEquiv e psiC23 g)) (chainAut e psiC23 phi23 g)
      actC23s2 :=
  chainAct_twist e psiC23 phi23 g (fun s _ hm => psiC23_phi23 s hm)
    (fun s _ hm => by rw [actC23s2, actM_matsC11 T23s2 (mats := matsC23) rfl s hm]
                      exact actC11_lt _ _)

theorem code23_xi
    (hLM : IsOver L M) (h : MathieuCode23 L ⊤ ⊥) {A : Subgroup (MulAut V)} (hAM : A ≤ M)
    (hAe : IsElemAbelian2 A) (hcard : Nat.card A = 16) : rkIdx (xiV A) ≤ 1 := by
  obtain ⟨e, he⟩ := code23_std h
  obtain ⟨g, l, -, hpred, hchain⟩ := chainC23 hLM he hAM hAe (k := 4) (by simp)
    (by rw [hcard]; norm_num)
  have hxi := (predC23_spec hpred).2.2 rfl
  exact (MaskCoords.ofEquiv (twistEquiv e psiC23 g)).rkIdx_le_one_of_pow_le (by norm_num)
    (pow_le_card_xiV (chainActC23 e g) hchain
      (chainAut_injective (rhoC11_injective _ _) (T23s2.toSub_injective _ _) g) hxi)

theorem code23_not_isFOneModule
    [Finite V] (hLM : IsOver L M) (h : MathieuCode23 L ⊤ ⊥) : ¬ IsFOneModule M := by
  rintro ⟨A, ⟨hAM, hA1, hAe⟩, hoff⟩
  obtain ⟨e, he⟩ := code23_std h
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_isElemAbelian (isElemAbelian2_iff.mp hAe)
  have hk4 := code23_card_le hLM h hAM hAe hk
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero] at hk
    exact hA1 (Subgroup.eq_bot_of_card_eq A hk)
  obtain ⟨g, l, -, hpred, hchain⟩ := chainC23 hLM he hAM hAe (k := k)
    (by interval_cases k <;> simp) hk
  obtain ⟨-, hd, -⟩ := predC23_spec hpred
  have hr := (MaskCoords.ofEquiv (twistEquiv e psiC23 g)).rkIdx_of_card
    (card_fixV (chainActC23 e g) hchain)
  have hrk : rk ↥A = k := by
    unfold rk
    rw [hk, padicValNat.prime_pow]
  omega

theorem code23_alphaH
    [Finite V] (hLM : IsOver L M) (h : MathieuCode23 L ⊤ ⊥) : alphaH M = 1 :=
  alphaH_eq_one_of_not_isFOneModule (code23_not_isFOneModule hLM h)

theorem oddC23_case
    {T : PT 24} [Fact (T.check = true)] (hT : T.allOK okM23 = true) {p : ℕ}
    [Fact p.Prime] (hsyl : Nat.card T.Elem = p ^ (Nat.card ↥mog23).factorization p)
    {mats : Array (List ℕ)} (hmats : mats = matsOfC11 T) (hodd : oddC23OK T mats)
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rhoC11 mog23 inf_le_left).range)
    {z : MulAut V} (hzM : z ∈ M) (hz : orderOf z = p) :
    6 ≤ rkIdx (fixV (Subgroup.zpowers z)) := by
  have hzR : congrHom e z ∈ psiC23.range :=
    map_le_of_normalizer hLM he normalizer_rhoC11_mog23 ((Subgroup.zpowers_le).2 hzM)
      ⟨z, Subgroup.mem_zpowers z, rfl⟩
  obtain ⟨g, s, hs1, hgs⟩ := exists_conj_elemModel psiC23 (rhoC11_injective _ _)
    (T.toSub mog23 (T.mem_mog23 hT)) (T.toSub_injective _ _) hsyl e hzR hz
  set e' := twistEquiv e psiC23 g with he'
  set act : T.Elem → ℕ → ℕ := fun q m => actM (mats[q.idx]!) m with hactdef
  have hactC : ∀ m < 2 ^ 11, act s m = actC11 (T.arr s) m := fun m hm =>
    actM_matsC11 T hmats s hm
  have hact : ∀ m < 2 ^ 11,
      psiC23 (T.toSub mog23 (T.mem_mog23 hT) s) (toW 11 m) = toW 11 (act s m) := by
    intro m hm
    rw [hactC m hm]
    exact rhoC11_toW mog23 inf_le_left _ (T.hasArr_toSub _ _ s) m
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
  have hlog : Nat.log 2 (fixMasks 11 act [s]).length ≤ 5 :=
    Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hpos.ne' (lt_of_le_of_lt hle (by norm_num)))
  rw [(MaskCoords.ofEquiv e').rkIdx_of_card hcard]
  omega

theorem code23_six_le_rkIdx_odd
    (hLM : IsOver L M) (h : MathieuCode23 L ⊤ ⊥) {z : MulAut V} (hzM : z ∈ M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hz : orderOf z = p) :
    6 ≤ rkIdx (fixV (Subgroup.zpowers z)) := by
  obtain ⟨e, he⟩ := code23_std h
  obtain ⟨k0, hk0⟩ : congrHom e z ∈ psiC23.range :=
    map_le_of_normalizer hLM he normalizer_rhoC11_mog23 ((Subgroup.zpowers_le).2 hzM)
      ⟨z, Subgroup.mem_zpowers z, rfl⟩
  have hk0o : orderOf k0 = p :=
    (orderOf_injective psiC23 (rhoC11_injective _ _) k0).symm.trans ((congrArg orderOf hk0).trans
      ((orderOf_injective _ (congrHom_injective e) z).trans hz))
  have hpK : p ∣ 10200960 := by
    have := hk0o ▸ orderOf_dvd_natCard k0
    rwa [card_mog23] at this
  obtain ⟨h3, h5, h7, h11, h23⟩ := Certificates.certificate7111
  rcases prime_dvd_m23 hp hpK hp2 with rfl | rfl | rfl | rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact oddC23_case T23s3_ok.2.2 (card_T23sp (by norm_num) (n := 2) T23s3_ok.2.1
      (by norm_num : (10200960 : ℕ) = 3 ^ 2 * 1133440) (by norm_num)) rfl h3 hLM he hzM hz
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact oddC23_case T23s5_ok.2.2 (card_T23sp (by norm_num) (n := 1) T23s5_ok.2.1
      (by norm_num : (10200960 : ℕ) = 5 ^ 1 * 2040192) (by norm_num)) rfl h5 hLM he hzM hz
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact oddC23_case T23s7_ok.2.2 (card_T23sp (by norm_num) (n := 1) T23s7_ok.2.1
      (by norm_num : (10200960 : ℕ) = 7 ^ 1 * 1457280) (by norm_num)) rfl h7 hLM he hzM hz
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact oddC23_case T23s11_ok.2.2 (card_T23sp (by norm_num) (n := 1) T23s11_ok.2.1
      (by norm_num : (10200960 : ℕ) = 11 ^ 1 * 927360) (by norm_num)) rfl h11 hLM he hzM hz
  · have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact oddC23_case T23s23_ok.2.2 (card_T23sp (by norm_num) (n := 1) T23s23_ok.2.1
      (by norm_num : (10200960 : ℕ) = 23 ^ 1 * 443520) (by norm_num)) rfl h23 hLM he hzM hz

theorem code23_betaH
    [Finite V] (hLM : IsOver L M) (h : MathieuCode23 L ⊤ ⊥) : (6 : ℕ∞) ≤ betaH M := by
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
  have h6 := code23_six_le_rkIdx_odd hLM h y.2.1 hp hp2 hyo
  have hle : rkIdx (fixV (Subgroup.zpowers (y : MulAut V))) ≤ rkIdx U := by
    unfold rkIdx
    exact padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite
      (Subgroup.index_dvd_of_le hUy)
  exact_mod_cast h6.trans hle

end CFSG.Quasithin.H.Mathieu

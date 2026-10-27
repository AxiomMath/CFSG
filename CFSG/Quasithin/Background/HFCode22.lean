module

public import CFSG.Quasithin.Background.HFCode24B
public import Certificates.Certificate7225
public import Certificates.Certificate7238

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem hf22All :
    forallGreedyAll pos22s2 inv22s2 predHF22 5 [] = true :=
  Certificates.certificate7225

theorem hf22Greedy {k : ℕ}
    (hk : k ≤ 5) : forallGreedy T22s2.invols predHF22 k [] = true :=
  (forallGreedyP_eq pos22s2_eq predHF22 k []).symm.trans (forallGreedyAll_le 5 [] hf22All k hk)

theorem codeFixTab22_get {a : T22s2.Elem} (ha : a * a = 1) :
    codeFixTab22[a.idx]! = fixMasks 10 codeAct22 [a] := by
  rw [codeFixTab22, getElem!_pos _ a.idx (by simpa using a.lt), Array.getElem_ofFn]
  have : T22s2.elemEquiv.symm ⟨a.idx, a.lt⟩ = a := rfl
  simp only [this, ha, ↓reduceIte]

theorem codeFixMasks22_eq {l : List T22s2.Elem}
    (hl : ∀ a ∈ l, a * a = 1) : codeFixMasks22 l = fixMasks 10 codeAct22 l := by
  cases l with
  | nil => rfl
  | cons a l => rw [codeFixMasks22, codeFixTab22_get (hl a List.mem_cons_self), ← fixMasks_cons]

theorem predHF22_spec {l : List T22s2.Elem} (hl : IndepList l)
    (h : predHF22 l = true) :
    (1 ≤ l.length → 10 - Nat.log 2 (fixMasks 10 codeAct22 l).length ≤ l.length + 1 →
        6 ≤ 10 - Nat.log 2 (fixMasks 10 codeAct22 l).length) ∧
      (l.length = 5 → normalChainB T22s2 l = true) := by
  have hinv : ∀ a ∈ l, a * a = 1 := (isCommInvol_of_indepList hl).1
  rw [predHF22, codeFixMasks22_eq hinv] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hk hd => ?_, fun h5 => ?_⟩
  · rcases h1 with (h | h) | h
    · omega
    · exact absurd hd h
    · exact h
  · rcases h2 with h | h
    · exact absurd h5 h
    · exact h

theorem conj_mem_E32
    (B : Subgroup T22s2.Elem) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (hcard : Nat.card B = 2 ^ 5) (t : T22s2.Elem) {b : T22s2.Elem}
    (hb : b ∈ B) : t * b * t⁻¹ ∈ B :=
  conj_mem_of_forallGreedy (hf22Greedy le_rfl)
    (fun _ hl hlen hp => (predHF22_spec hl hp).2 hlen) B hcomm hsq hcard t hb

theorem chainActC22 (e : V ≃* W10) (g : ↥mog22plus) :
    ChainAct (MaskCoords.ofEquiv (twistEquiv e psiC22 g)) (chainAut e psiC22 phi22 g)
      codeAct22 :=
  chainAct_twist e psiC22 phi22 g (fun s _ hm => psiC22_phi22 s hm)
    (fun s _ hm => by
      rw [codeAct22, actM_matsC10 T22s2 (mats := matsC22) rfl s hm]
      exact actC10_lt _ _)

theorem chainAutC22_injective
    (e : V ≃* W10) (g : ↥mog22plus) :
    Function.Injective (chainAut e psiC22 phi22 g) :=
  chainAut_injective rhoC10_mog22plus_injective (T22s2.toSub_injective _ _) g

theorem map_le_rangeC22
    (hLM : IsOver L M) {e : V ≃* W10}
    (he : L.map (congrHom e) = (rhoC10 mog22 mog22_le_mog22plus).range)
    {A : Subgroup (MulAut V)} (hA : A ≤ M) : A.map (congrHom e) ≤ psiC22.range :=
  map_le_of_normalizer hLM he normalizer_rhoC10_mog22 hA

theorem chainHF22
    (hLM : IsOver L M) {e : V ≃* W10}
    (he : L.map (congrHom e) = (rhoC10 mog22 mog22_le_mog22plus).range)
    {A : Subgroup (MulAut V)} (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hk : k ≤ 5)
    (hcard : Nat.card A = 2 ^ k) :
    ∃ g : ↥mog22plus, ∃ l : List T22s2.Elem, IndepList l ∧ predHF22 l = true ∧
      IsChainSub (chainAut e psiC22 phi22 g) l A ∧ l.length = k := by
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC22 rhoC10_mog22plus_injective
    phi22 (T22s2.toSub_injective _ _) card_T22s2 (fun _ h1 h2 => T22s2.mem_invols h1 h2)
    (hf22Greedy hk) e (map_le_rangeC22 hLM he hA) hAe hcard
  have hcl := card_of_chainSub hchain (chainAutC22_injective e g) hind
  rw [hcard] at hcl
  exact ⟨g, l, hind, hpred, hchain, (Nat.pow_right_injective (le_refl 2) hcl).symm⟩

theorem rkIdx_fixV_chainC22 {e : V ≃* W10} {g : ↥mog22plus}
    {l : List T22s2.Elem} {A : Subgroup (MulAut V)}
    (hchain : IsChainSub (chainAut e psiC22 phi22 g) l A) :
    rkIdx (fixV A) = 10 - Nat.log 2 (fixMasks 10 codeAct22 l).length :=
  (MaskCoords.ofEquiv (twistEquiv e psiC22 g)).rkIdx_of_card (card_fixV (chainActC22 e g) hchain)

theorem code22_alphaSet
    [Finite V] (hLM : IsOver L M) (h : MathieuCode22 L ⊤ ⊥) : ∀ k ∈ alphaSet M, 6 ≤ k := by
  rintro k ⟨hk2, U, -, hUk, hkle⟩
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨e, he⟩ := code22_std h
  obtain ⟨E, hEM, hE, hEc⟩ := exists_isElemAbelian_card_pRank (M ⊓ centSub U)
  have hE2 : IsElemAbelian2 E := isElemAbelian2_iff.2 hE
  have hj5 := code22_card_le hLM h (hEM.trans inf_le_left) hE2 hEc
  obtain ⟨g, l, hind, hpred, hchain, hlen⟩ :=
    chainHF22 hLM he (hEM.trans inf_le_left) hE2 hj5 hEc
  have hr := rkIdx_fixV_chainC22 hchain
  have hUE : U ≤ fixV E := fun u hu x hx => mem_centSub.1 (hEM hx).2 u hu
  have hle := rkIdx_le_rkIdx_of_le hUE
  have h1 := (predHF22_spec hind hpred).1 (by omega) (by omega)
  omega

theorem oddC22_case
    {T : PT 24} [Fact (T.check = true)] (hT : T.allOK okPlus = true) {p : ℕ}
    [Fact p.Prime] (hsyl : Nat.card T.Elem = p ^ (Nat.card ↥mog22plus).factorization p)
    {mats : Array (List ℕ)} (hmats : mats = matsOfC10 T) {b : ℕ}
    (hodd : oddFixOK 10 b T mats) (hLM : IsOver L M) {e : V ≃* W10}
    (he : L.map (congrHom e) = (rhoC10 mog22 mog22_le_mog22plus).range)
    {z : MulAut V} (hzM : z ∈ M) (hz : orderOf z = p) :
    10 - b ≤ rkIdx (fixV (Subgroup.zpowers z)) := by
  have hzR : congrHom e z ∈ psiC22.range :=
    map_le_rangeC22 hLM he ((Subgroup.zpowers_le).2 hzM) ⟨z, Subgroup.mem_zpowers z, rfl⟩
  obtain ⟨g, s, hs1, hgs⟩ := exists_conj_elemModel psiC22 rhoC10_mog22plus_injective
    (T.toSub mog22plus (T.mem_mog22plus hT)) (T.toSub_injective _ _) hsyl e hzR hz
  set e' := twistEquiv e psiC22 g with he'
  set act : T.Elem → ℕ → ℕ := fun q m => actM (mats[q.idx]!) m with hactdef
  have hactC : ∀ m < 2 ^ 10, act s m = actC10 (T.arr s) m := fun m hm =>
    actM_matsC10 T hmats s hm
  have hact : ∀ m < 2 ^ 10,
      psiC22 (T.toSub mog22plus (T.mem_mog22plus hT) s) (toW 10 m) = toW 10 (act s m) := by
    intro m hm
    rw [hactC m hm]
    exact rhoC10_toW mog22plus le_rfl _ (T.hasArr_toSub _ _ s) m
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
      exact toW_inj (by rw [hactC m hm]; exact actC10_lt _ _) hm (e'.symm.injective h3)
    · intro h3
      rw [h3]
  have hcard : Nat.card (fixV (Subgroup.zpowers z)) = (fixMasks 10 act [s]).length :=
    (MaskCoords.ofEquiv e').card_eq _ _ fun m hm => (hX m hm).trans (by simp)
  have hle := hodd s hs1
  have := (MaskCoords.ofEquiv e').finite
  have hpos : 0 < (fixMasks 10 act [s]).length := hcard ▸ Nat.card_pos
  have hlog : Nat.log 2 (fixMasks 10 act [s]).length ≤ b :=
    Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hpos.ne' (lt_of_le_of_lt hle
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self b))))
  rw [(MaskCoords.ofEquiv e').rkIdx_of_card hcard]
  omega

theorem code22_odd_le
    (hLM : IsOver L M) (h : MathieuCode22 L ⊤ ⊥) {z : MulAut V} (hzM : z ∈ M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hz : orderOf z = p) :
    6 ≤ rkIdx (fixV (Subgroup.zpowers z)) := by
  obtain ⟨e, he⟩ := code22_std h
  obtain ⟨k0, hk0⟩ : congrHom e z ∈ psiC22.range :=
    map_le_rangeC22 hLM he ((Subgroup.zpowers_le).2 hzM) ⟨z, Subgroup.mem_zpowers z, rfl⟩
  have hk0o : orderOf k0 = p :=
    (orderOf_injective psiC22 rhoC10_mog22plus_injective k0).symm.trans
      ((congrArg orderOf hk0).trans ((orderOf_injective _ (congrHom_injective e) z).trans hz))
  have hpK : p ∣ 887040 := by
    have := hk0o ▸ orderOf_dvd_natCard k0
    rwa [card_mog22plus] at this
  obtain ⟨h3, h5, h7, h11⟩ := Certificates.certificate7238.1
  rcases prime_dvd_aut22 hp hpK hp2 with rfl | rfl | rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact oddC22_case T22s3_ok.2.2 (card_T22sp (by norm_num) (n := 2) T22s3_ok.2.1
      (by norm_num : (887040 : ℕ) = 3 ^ 2 * 98560) (by norm_num)) rfl h3 hLM he hzM hz
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact oddC22_case T22s5_ok.2.2 (card_T22sp (by norm_num) (n := 1) T22s5_ok.2.1
      (by norm_num : (887040 : ℕ) = 5 ^ 1 * 177408) (by norm_num)) rfl h5 hLM he hzM hz
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact oddC22_case T22s7_ok.2.2 (card_T22sp (by norm_num) (n := 1) T22s7_ok.2.1
      (by norm_num : (887040 : ℕ) = 7 ^ 1 * 126720) (by norm_num)) rfl h7 hLM he hzM hz
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact oddC22_case T22s11_ok.2.2 (card_T22sp (by norm_num) (n := 1) T22s11_ok.2.1
      (by norm_num : (887040 : ℕ) = 11 ^ 1 * 80640) (by norm_num)) rfl h11 hLM he hzM hz

theorem code22_betaH
    [Finite V] (hLM : IsOver L M) (h : MathieuCode22 L ⊤ ⊥) : (6 : ℕ∞) ≤ betaH M := by
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
  have h6 := code22_odd_le hLM h y.2.1 hp hp2 hyo
  exact_mod_cast h6.trans (rkIdx_le_rkIdx_of_le hUy)

theorem hP22 :
    ∀ B : Subgroup T22s2.Elem, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B = 2 ^ 5 → ∀ t : T22s2.Elem, ∀ b ∈ B, t * b * t⁻¹ ∈ B :=
  fun B hc hs hcard t _ hb => conj_mem_E32 B hc hs hcard t hb

theorem code22_le_normalizer
    (hLM : IsOver L M) (h : MathieuCode22 L ⊤ ⊥) {S A : Subgroup (MulAut V)} (hSM : S ≤ M)
    (hS : IsPGroup 2 S) (hAS : A ≤ S) (hAe : IsElemAbelian2 A) (hcard : Nat.card A = 2 ^ 5) :
    S ≤ Subgroup.normalizer (A : Set (MulAut V)) := by
  obtain ⟨e, he⟩ := code22_std h
  apply le_normalizer_of_map e
  have hAe' := (isElemAbelian2_map_congrHom e).2 hAe
  exact le_normalizer_of_sylow psiC22 rhoC10_mog22plus_injective phi22
    (T22s2.toSub_injective _ _) card_T22s2 hP22 (map_le_rangeC22 hLM he hSM)
    (hS.map (congrHom e)) (Subgroup.map_mono hAS) (fun x hx y hy => hAe'.1 x hx y hy)
    (fun x hx => by rw [← sq]; exact hAe'.2 x hx) ((card_map_congrHom e A).trans hcard)

end CFSG.Quasithin.H.Mathieu


module

public import CFSG.Quasithin.Background.HMathieuFacts22Base
public import CFSG.Quasithin.Background.HMathieuSyl24GreedyBase
public import CFSG.Quasithin.Background.HMathieuSyl24Odd
public meta import CFSG.Quasithin.Background.HMathieuSyl24
public import CFSG.Sporadic.Schreier.M24Data
public meta import CFSG.Sporadic.Schreier.M24Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Monster.B.Mathieu.M24CheckInputs
public import CFSG.Quasithin.Background.HMathieuFacts24Inputs
public import CFSG.Quasithin.Background.HMathieuCentInputs
public import CFSG.Quasithin.Background.HMathieuMask
public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuAvoid
public import CFSG.Quasithin.Background.HMathieuEnumAll
public import CFSG.Quasithin.Background.HMathieuSyl24
public import Certificates.Certificate7074

@[expose] public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V]

noncomputable abbrev rhoM24 : ↥AutPerm →* MulAut W11 := rho11 AutPerm le_rfl

abbrev phi24 : T24s2.Elem →* ↥AutPerm :=
  T24s2.toSub AutPerm (T24s2.mem_autPerm (fun _ _ h => h) T24s2_ok.2.2)

theorem act24s2_spec (s : T24s2.Elem) {m : ℕ} (hm : m < 2 ^ 11) :
    act24s2 s m = act11 (T24s2.arr s) m :=
  actM_mats11 T24s2 rfl s hm

theorem rhoM24_phi24 (s : T24s2.Elem) {m : ℕ} (hm : m < 2 ^ 11) :
    rhoM24 (phi24 s) (toW 11 m) = toW 11 (act24s2 s m) := by
  rw [act24s2_spec s hm]
  exact rho11_toW AutPerm le_rfl _ (T24s2.hasArr_toSub _ _ s) m

theorem card_T24s2 :
    Nat.card T24s2.Elem = 2 ^ (Nat.card ↥AutPerm).factorization 2 := by
  rw [PT.card_elem, T24s2_ok.2.1, card_AutPerm,
    show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
    factorization_eq Nat.prime_two (by norm_num)]
  norm_num

variable {L M : Subgroup (MulAut V)}

theorem map_le_range24
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rho11 AutPerm le_rfl).range) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) : A.map (congrHom e) ≤ rhoM24.range := by
  have h1 : A.map (congrHom e) ≤ (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) :=
    Subgroup.map_mono (hA.trans hLM.2)
  have h2 := Subgroup.le_normalizer_map (H := L) (congrHom e)
  have h3 : Subgroup.normalizer ((L.map (congrHom e) : Subgroup (MulAut W11)) : Set (MulAut W11))
      = rhoM24.range :=
    (congrArg (fun H : Subgroup (MulAut W11) => Subgroup.normalizer (H : Set (MulAut W11))) he).trans
      normalizer_rho11_autPerm
  exact h1.trans (h2.trans h3.le)

theorem chainAct24 (e : V ≃* W11) (g : ↥AutPerm) :
    ChainAct (MaskCoords.ofEquiv (twistEquiv e rhoM24 g)) (chainAut e rhoM24 phi24 g) act24s2 :=
  chainAct_twist e rhoM24 phi24 g (fun s _ hm => rhoM24_phi24 s hm)
    (fun s _ hm => by rw [act24s2_spec s hm]; exact act11_lt _ _)

theorem chainAut24_injective
    (e : V ≃* W11) (g : ↥AutPerm) :
    Function.Injective (chainAut e rhoM24 phi24 g) :=
  chainAut_injective (rho11_injective _ _) (T24s2.toSub_injective _ _) g

theorem rho11_inv_pairVec24 (g : ↥AutPerm) (i j : Fin 24) :
    (rhoM24 g).symm (cocodeCoords.κ (pairVec i j)) =
      cocodeCoords.κ (pairVec (((g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)) i)
        (((g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)) j)) := by
  rw [← rho11_pairVec AutPerm le_rfl g⁻¹ i j, map_inv]
  rfl

theorem o2_twist24 {e : V ≃* W11}
    (hO2 : ∀ (v : V) (i j : Fin 24), i ≠ j → e v = cocodeCoords.κ (pairVec i j) →
      IsCocodeO2 L v) (g : ↥AutPerm) :
    ∀ o ∈ o2Masks24, (MaskCoords.ofEquiv (twistEquiv e rhoM24 g)).vm o ∈
      {v | IsCocodeO2 L v} := by
  intro o ho
  obtain ⟨i, j, hij, hjo⟩ := toW_o2_24 ho
  set σ : Equiv.Perm (Fin 24) := ((g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)) with hσ
  refine hO2 _ (σ i) (σ j) (σ.injective.ne hij) ?_
  rw [MaskCoords.ofEquiv_vm]
  change e (e.symm ((rhoM24 g).symm (toW 11 o))) = _
  rw [MulEquiv.apply_symm_apply, hjo, rho11_inv_pairVec24]

theorem card_of_chainSub {P : Type*} [Group P] [DecidableEq P] {aut : P →* MulAut V}
    {l : List P} {A : Subgroup (MulAut V)} (hA : IsChainSub aut l A)
    (hinj : Function.Injective aut) (hl : IndepList l) : Nat.card A = 2 ^ l.length := by
  have hset : (A : Set (MulAut V)) = aut '' ((subprods l).toFinset : Set P) := by
    ext a
    simp only [SetLike.mem_coe, Set.mem_image, List.coe_toFinset, Set.mem_ofPred_eq]
    rw [hA a]
    exact ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h.symm⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h.symm⟩⟩
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_image_of_injective _ hinj,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_subprods hl), length_subprods]

theorem cocode24_card (h : MathieuCocode24 L ⊤ ⊥) : Nat.card V = 2 ^ 11 :=
  (MaskCoords.ofEquiv (cocode24_stdO h).choose).card_eq_pow

theorem isElemAbelian2_zpowers {t : MulAut V} (ht : orderOf t = 2) :
    IsElemAbelian2 (Subgroup.zpowers t) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht, pow_orderOf_eq_one,
      one_zpow]

theorem exists_inv_of_arr {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (hΓ : Γ ≤ AutPerm)
    {a : Array ℕ} (hok : inAutOK a = true) (hinv : ∀ i < 24, a[a[i]!]! = i) (i0 : Fin 24)
    (hne : a[(i0 : ℕ)]! ≠ i0)
    (hmem : ∀ σ : Equiv.Perm (Fin 24), σ ∈ AutPerm → HasArr σ a → σ ∈ Γ)
    {e : V ≃* W11} (he : L.map (congrHom e) = (rho11 Γ hΓ).range) :
    ∃ t ∈ L, orderOf t = 2 ∧ ∀ m < 2 ^ 11,
      (MaskCoords.ofEquiv e).vm m ∈ fixV (Subgroup.zpowers t) ↔ act11 a m = m := by
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
  have hmemR : rho11 Γ hΓ ⟨σ, hσ⟩ ∈ L.map (congrHom e) := he ▸ ⟨⟨σ, hσ⟩, rfl⟩
  obtain ⟨t, htL, hte⟩ := hmemR
  refine ⟨t, htL, ?_, fun m hm => ?_⟩
  · have h1 : orderOf (⟨σ, hσ⟩ : ↥Γ) = 2 := by
      refine orderOf_eq_prime (Subtype.ext ?_) fun h => hσ1 (congrArg Subtype.val h)
      rw [Subgroup.coe_pow, sq, hσσ]
      rfl
    exact (orderOf_injective _ (congrHom_injective e) t).symm.trans
      ((congrArg orderOf hte).trans ((orderOf_injective _ (rho11_injective Γ hΓ) _).trans h1))
  · rw [mem_fixV_zpowers_iff, MaskCoords.ofEquiv_vm]
    have h1 : e (t (e.symm (toW 11 m))) = toW 11 (act11 a m) := by
      rw [apply_of_congrHom_eq hte, MulEquiv.apply_symm_apply]
      exact rho11_toW Γ hΓ ⟨σ, hσ⟩ hσa m
    have h2 : t (e.symm (toW 11 m)) = e.symm (toW 11 (act11 a m)) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    rw [h2]
    constructor
    · intro h3
      exact toW_inj (act11_lt _ _) hm (e.symm.injective h3)
    · intro h3
      rw [h3]

theorem mem_fixMasks_of_vm {n : ℕ} {P : Type*} [Group P] {c : MaskCoords V n}
    {aut : P →* MulAut V} {act : P → ℕ → ℕ} {l : List P} {A : Subgroup (MulAut V)}
    (hc : ChainAct c aut act) (hA : IsChainSub aut l A) {m : ℕ} (hm : m < 2 ^ n)
    (hv : c.vm m ∈ fixV A) : m ∈ fixMasks n act l := by
  rw [fixMasks, List.mem_filter, List.mem_range]
  exact ⟨hm, (vm_mem_fixV_iff hc hA hm).1 hv⟩

theorem prime_dvd_m24 {p : ℕ} (hp : p.Prime) (hdvd : p ∣ 244823040) (hp2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  have e : (244823040 : ℕ) = 2 ^ 10 * 3 ^ 3 * 5 * 7 * 11 * 23 := by norm_num
  rw [e] at hdvd
  have hq : ∀ q : ℕ, q.Prime → ∀ k, p ∣ q ^ k → p = q := fun q hq k h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h)
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · exact absurd (hq 2 Nat.prime_two 10 h) hp2
          · exact Or.inl (hq 3 (by norm_num) 3 h)
        · exact Or.inr (Or.inl (hq 5 (by norm_num) 1 (by simpa using h)))
      · exact Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) 1 (by simpa using h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 11 (by norm_num) 1 (by simpa using h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hq 23 (by norm_num) 1 (by simpa using h)))))

theorem odd24_case
    {T : PT 24}
    [Fact (T.check = true)] (hT : T.allOK okAut = true) {p : ℕ}
    [Fact p.Prime] (hsyl : Nat.card T.Elem = p ^ (Nat.card ↥AutPerm).factorization p)
    {mats : Array (List ℕ)} (hmats : mats = matsOf11 T) (hodd : odd24OK T mats)
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rho11 AutPerm le_rfl).range)
    (hO2 : ∀ (v : V) (i j : Fin 24), i ≠ j → e v = cocodeCoords.κ (pairVec i j) →
      IsCocodeO2 L v)
    {z : MulAut V} (hzM : z ∈ M) (hz : orderOf z = p) (U : Subgroup V)
    (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v) (hUz : U ≤ fixV (Subgroup.zpowers z)) : rk U ≤ 3 := by
  have hzR : congrHom e z ∈ rhoM24.range :=
    map_le_range24 hLM he ((Subgroup.zpowers_le).2 hzM) ⟨z, Subgroup.mem_zpowers z, rfl⟩
  obtain ⟨g, s, hs1, hgs⟩ := exists_conj_elemModel rhoM24 (rho11_injective _ _)
    (T.toSub AutPerm (T.mem_autPerm (fun _ _ h => h) hT)) (T.toSub_injective _ _) hsyl e hzR hz
  set e' := twistEquiv e rhoM24 g with he'
  set act : T.Elem → ℕ → ℕ := fun q m => actM (mats[q.idx]!) m with hactdef
  have hact11 : ∀ m < 2 ^ 11, act s m = act11 (T.arr s) m := fun m hm =>
    actM_mats11 T hmats s hm
  have hact : ∀ m < 2 ^ 11,
      rhoM24 (T.toSub AutPerm (T.mem_autPerm (fun _ _ h => h) hT) s) (toW 11 m) =
        toW 11 (act s m) := by
    intro m hm
    rw [hact11 m hm]
    exact rho11_toW AutPerm le_rfl _ (T.hasArr_toSub _ _ s) m
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
      exact toW_inj (by rw [hact11 m hm]; exact act11_lt _ _) hm (e'.symm.injective h3)
    · intro h3
      rw [h3]
  refine rk_le_of_avoidOK (MaskCoords.ofEquiv e') (X := fixV (Subgroup.zpowers z))
    (F := fixMasks 11 act [s]) (fun m hm hv => ?_) (o2_twist24 hO2 g) hUz
    (fun w hw hwO => hU w hw hwO) (hodd s hs1)
  rw [fixMasks, List.mem_filter, List.mem_range]
  exact ⟨hm, by simpa using (hX m hm).1 hv⟩

theorem card_T24sp {T : PT 24} {p n b : ℕ} (hp : p.Prime)
    (hn : T.n = p ^ n)
    (hb : (244823040 : ℕ) = p ^ n * b) (hpb : ¬ p ∣ b) :
    Nat.card T.Elem = p ^ (Nat.card ↥AutPerm).factorization p := by
  rw [PT.card_elem, hn, card_AutPerm, hb, factorization_eq hp hpb]

theorem cocode24_rk_le_three_odd
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode24 L ⊤ ⊥)
    (U : Subgroup V) (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v) {y : MulAut V} (hyM : y ∈ M)
    (hy1 : y ≠ 1) (hyo : Odd (orderOf y)) (hUy : U ≤ fixV (Subgroup.zpowers y)) : rk U ≤ 3 := by
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨e, he, hO2⟩ := cocode24_stdO h
  set n := orderOf y with hndef
  have hn0 : n ≠ 0 := (orderOf_pos y).ne'
  have hn1 : n ≠ 1 := fun h1 => hy1 (orderOf_eq_one_iff.1 h1)
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hpn : n.minFac ∣ n := Nat.minFac_dvd n
  have hp2 : n.minFac ≠ 2 := by
    intro h2
    rw [h2] at hpn
    exact (Nat.not_even_iff_odd.2 hyo) (even_iff_two_dvd.2 hpn)
  obtain ⟨k0, hk0⟩ : congrHom e y ∈ rhoM24.range :=
    map_le_range24 hLM he ((Subgroup.zpowers_le).2 hyM) ⟨y, Subgroup.mem_zpowers y, rfl⟩
  have hk0o : orderOf k0 = n :=
    (orderOf_injective rhoM24 (rho11_injective _ _) k0).symm.trans ((congrArg orderOf hk0).trans
      (orderOf_injective _ (congrHom_injective e) y))
  have hpK : n.minFac ∣ 244823040 := by
    have := hpn.trans (hk0o ▸ orderOf_dvd_natCard k0)
    rwa [card_AutPerm] at this
  have hUz := hUy.trans (fixV_zpowers_pow_le y (n / n.minFac))
  have hzM : y ^ (n / n.minFac) ∈ M := M.pow_mem hyM _
  set z := y ^ (n / n.minFac) with hzdef
  have hz : orderOf z = n.minFac := orderOf_pow_orderOf_div hn0 hpn
  rcases prime_dvd_m24 hp hpK hp2 with h3 | h5 | h7 | h11 | h23
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [h3] at hz
    exact odd24_case T24s3_ok.2.2 (card_T24sp (by norm_num) (n := 3) T24s3_ok.2.1
      (by norm_num : (244823040 : ℕ) = 3 ^ 3 * 9067520) (by norm_num)) rfl odd24_ok.1 hLM he hO2
      hzM hz U hU hUz
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [h5] at hz
    exact odd24_case T24s5_ok.2.2 (card_T24sp (by norm_num) (n := 1) T24s5_ok.2.1
      (by norm_num : (244823040 : ℕ) = 5 ^ 1 * 48964608) (by norm_num)) rfl odd24_ok.2.1 hLM he
      hO2 hzM hz U hU hUz
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [h7] at hz
    exact odd24_case T24s7_ok.2.2 (card_T24sp (by norm_num) (n := 1) T24s7_ok.2.1
      (by norm_num : (244823040 : ℕ) = 7 ^ 1 * 34974720) (by norm_num)) rfl odd24_ok.2.2.1 hLM he
      hO2 hzM hz U hU hUz
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    rw [h11] at hz
    exact odd24_case T24s11_ok.2.2 (card_T24sp (by norm_num) (n := 1) T24s11_ok.2.1
      (by norm_num : (244823040 : ℕ) = 11 ^ 1 * 22256640) (by norm_num)) rfl odd24_ok.2.2.2.1 hLM
      he hO2 hzM hz U hU hUz
  · have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    rw [h23] at hz
    exact odd24_case T24s23_ok.2.2 (card_T24sp (by norm_num) (n := 1) T24s23_ok.2.1
      (by norm_num : (244823040 : ℕ) = 23 ^ 1 * 10644480) (by norm_num)) rfl odd24_ok.2.2.2.2 hLM
      he hO2 hzM hz U hU hUz

end CFSG.Quasithin.H.Mathieu

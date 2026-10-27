
module

public import CFSG.Quasithin.Background.HMathieuFacts22Base
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

@[expose] public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V]

noncomputable abbrev rhoM23 : ↥mog23 →* MulAut W11 := rho11 mog23 inf_le_left

abbrev phi23
    : T23s2.Elem →* ↥mog23 := T23s2.toSub mog23 (T23s2.mem_mog23 T23s2_ok.2.2)

theorem act23s2_spec (s : T23s2.Elem) {m : ℕ} (hm : m < 2 ^ 11) :
    act23s2 s m = act11 (T23s2.arr s) m :=
  actM_mats11 T23s2 rfl s hm

theorem rhoM23_phi23 (s : T23s2.Elem) {m : ℕ} (hm : m < 2 ^ 11) :
    rhoM23 (phi23 s) (toW 11 m) = toW 11 (act23s2 s m) := by
  rw [act23s2_spec s hm]
  exact rho11_toW mog23 inf_le_left _ (T23s2.hasArr_toSub _ _ s) m

theorem card_T23s2
    : Nat.card T23s2.Elem = 2 ^ (Nat.card ↥mog23).factorization 2 := by
  rw [PT.card_elem, T23s2_ok.2.1, card_mog23,
    show (10200960 : ℕ) = 2 ^ 7 * 79695 by norm_num, factorization_eq Nat.prime_two (by norm_num)]
  norm_num

variable {L M : Subgroup (MulAut V)}

theorem map_le_range23
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rho11 mog23 inf_le_left).range) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) : A.map (congrHom e) ≤ rhoM23.range := by
  have h1 : A.map (congrHom e) ≤ (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) :=
    Subgroup.map_mono (hA.trans hLM.2)
  have h2 := Subgroup.le_normalizer_map (H := L) (congrHom e)
  have h3 : Subgroup.normalizer ((L.map (congrHom e) : Subgroup (MulAut W11)) : Set (MulAut W11))
      = rhoM23.range :=
    (congrArg (fun H : Subgroup (MulAut W11) => Subgroup.normalizer (H : Set (MulAut W11))) he).trans
      normalizer_rho11_mog23
  exact h1.trans (h2.trans h3.le)

theorem chainAct23 (e : V ≃* W11) (g : ↥mog23) :
    ChainAct (MaskCoords.ofEquiv (twistEquiv e rhoM23 g)) (chainAut e rhoM23 phi23 g) act23s2 :=
  chainAct_twist e rhoM23 phi23 g (fun s _ hm => rhoM23_phi23 s hm)
    (fun s _ hm => by rw [act23s2_spec s hm]; exact act11_lt _ _)

theorem pred23_spec {k : ℕ} {l : List T23s2.Elem} (h : pred23 k l = true) :
    k ≤ 4 ∧
      (11 - Nat.log 2 (fixMasks 11 act23s2 l).length ≤ k + 1 →
        o2OK o2Masks23 (fixMasks 11 act23s2 l) = true) ∧
      (k = 1 → 11 - Nat.log 2 (fixMasks 11 act23s2 l).length = 4) := by
  simp only [pred23, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hk, h1⟩, h2⟩ := h
  exact ⟨hk, fun hd => h1.resolve_left (not_not.2 hd), fun h1' => h2.resolve_left (not_not.2 h1')⟩

theorem rho11_pairVec_zero (σ : ↥mog23) (j : Fin 24) :
    rhoM23 σ (cocodeCoords.κ (pairVec 0 j)) =
      cocodeCoords.κ (pairVec 0 ((σ : Equiv.Perm (Fin 24)) j)) := by
  rw [rho11_pairVec, (mem_stab_iff 0 _).1 σ.2.2]

theorem rho11_inv_pairVec (g : ↥mog23) (j : Fin 24) :
    (rhoM23 g).symm (cocodeCoords.κ (pairVec 0 j)) =
      cocodeCoords.κ (pairVec 0 (((g⁻¹ : ↥mog23) : Equiv.Perm (Fin 24)) j)) := by
  rw [← rho11_pairVec_zero g⁻¹ j, map_inv]
  rfl

theorem o2_twist23 {e : V ≃* W11}
    (hO2 : ∀ (v : V) (j : Fin 24), j ≠ 0 → e v = cocodeCoords.κ (pairVec 0 j) →
      IsCocodeO2 L v) (g : ↥mog23) :
    ∀ o ∈ o2Masks23, (MaskCoords.ofEquiv (twistEquiv e rhoM23 g)).vm o ∈
      {v | IsCocodeO2 L v} := by
  intro o ho
  obtain ⟨j, hj0, hjo⟩ := toW_o2_23 ho
  set σ : Equiv.Perm (Fin 24) := ((g⁻¹ : ↥mog23) : Equiv.Perm (Fin 24)) with hσ
  have hσ0 : σ 0 = 0 := (mem_stab_iff 0 _).1 (g⁻¹ : ↥mog23).2.2
  have hσj : σ j ≠ 0 := fun h => hj0 (σ.injective (h.trans hσ0.symm))
  refine hO2 _ (σ j) hσj ?_
  rw [MaskCoords.ofEquiv_vm]
  change e (e.symm ((rhoM23 g).symm (toW 11 o))) = _
  rw [MulEquiv.apply_symm_apply, hjo, rho11_inv_pairVec]

theorem cocode23_card
    (h : MathieuCocode23 L ⊤ ⊥) : Nat.card V = 2 ^ 11 :=
  (MaskCoords.ofEquiv (cocode23_stdO h).choose).card_eq_pow

theorem prime_dvd_m23 {p : ℕ} (hp : p.Prime) (hdvd : p ∣ 10200960) (hp2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  have e : (10200960 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 * 23 := by norm_num
  rw [e] at hdvd
  have hq : ∀ q : ℕ, q.Prime → ∀ k, p ∣ q ^ k → p = q := fun q hq k h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h)
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · exact absurd (hq 2 Nat.prime_two 7 h) hp2
          · exact Or.inl (hq 3 (by norm_num) 2 h)
        · exact Or.inr (Or.inl (hq 5 (by norm_num) 1 (by simpa using h)))
      · exact Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) 1 (by simpa using h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 11 (by norm_num) 1 (by simpa using h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hq 23 (by norm_num) 1 (by simpa using h)))))

theorem odd23_case
    {T : PT 24} [Fact (T.check = true)] (hT : T.allOK okM23 = true) {p : ℕ}
    [Fact p.Prime] (hsyl : Nat.card T.Elem = p ^ (Nat.card ↥mog23).factorization p)
    {mats : Array (List ℕ)} (hmats : mats = matsOf11 T) (hodd : odd23OK T mats)
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rho11 mog23 inf_le_left).range)
    (hO2 : ∀ (v : V) (j : Fin 24), j ≠ 0 → e v = cocodeCoords.κ (pairVec 0 j) →
      IsCocodeO2 L v)
    {z : MulAut V} (hzM : z ∈ M) (hz : orderOf z = p) (U : Subgroup V)
    (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v) (hUz : U ≤ fixV (Subgroup.zpowers z)) : rk U ≤ 4 := by
  have hzR : congrHom e z ∈ rhoM23.range :=
    map_le_range23 hLM he ((Subgroup.zpowers_le).2 hzM) ⟨z, Subgroup.mem_zpowers z, rfl⟩
  obtain ⟨g, s, hs1, hgs⟩ := exists_conj_elemModel rhoM23 (rho11_injective _ _)
    (T.toSub mog23 (T.mem_mog23 hT)) (T.toSub_injective _ _) hsyl e hzR hz
  set e' := twistEquiv e rhoM23 g with he'
  set act : T.Elem → ℕ → ℕ := fun q m => actM (mats[q.idx]!) m with hactdef
  have hact11 : ∀ m < 2 ^ 11, act s m = act11 (T.arr s) m := fun m hm =>
    actM_mats11 T hmats s hm
  have hact : ∀ m < 2 ^ 11,
      rhoM23 (T.toSub mog23 (T.mem_mog23 hT) s) (toW 11 m) = toW 11 (act s m) := by
    intro m hm
    rw [hact11 m hm]
    exact rho11_toW mog23 inf_le_left _ (T.hasArr_toSub _ _ s) m
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
  have hcard : Nat.card (fixV (Subgroup.zpowers z)) = (fixMasks 11 act [s]).length :=
    (MaskCoords.ofEquiv e').card_eq _ _ fun m hm => (hX m hm).trans (by simp)
  refine rk_le_four_of_o2OK (MaskCoords.ofEquiv e') (X := fixV (Subgroup.zpowers z))
    (F := fixMasks 11 act [s]) (fun m hm => ?_) hcard (o2_twist23 hO2 g) hUz
    (fun w hw hwO => hU w hw hwO) (hodd s hs1)
  rw [fixMasks, List.mem_filter, List.mem_range] at hm
  exact ⟨hm.1, (hX m hm.1).2 (by simpa using hm.2)⟩

theorem card_T23sp
    {T : PT 24} {p n b : ℕ} (hp : p.Prime) (hn : T.n = p ^ n)
    (hb : (10200960 : ℕ) = p ^ n * b) (hpb : ¬ p ∣ b) :
    Nat.card T.Elem = p ^ (Nat.card ↥mog23).factorization p := by
  rw [PT.card_elem, hn, card_mog23, hb, factorization_eq hp hpb]

theorem cocode23_rk_le_four_odd
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode23 L ⊤ ⊥)
    (U : Subgroup V) (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v) {y : MulAut V} (hyM : y ∈ M)
    (hy1 : y ≠ 1) (hyo : Odd (orderOf y)) (hUy : U ≤ fixV (Subgroup.zpowers y)) : rk U ≤ 4 := by
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨e, he, hO2⟩ := cocode23_stdO h
  set n := orderOf y with hndef
  have hn0 : n ≠ 0 := (orderOf_pos y).ne'
  have hn1 : n ≠ 1 := fun h1 => hy1 (orderOf_eq_one_iff.1 h1)
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hpn : n.minFac ∣ n := Nat.minFac_dvd n
  have hp2 : n.minFac ≠ 2 := by
    intro h2
    rw [h2] at hpn
    exact (Nat.not_even_iff_odd.2 hyo) (even_iff_two_dvd.2 hpn)
  obtain ⟨k0, hk0⟩ : congrHom e y ∈ rhoM23.range :=
    map_le_range23 hLM he ((Subgroup.zpowers_le).2 hyM) ⟨y, Subgroup.mem_zpowers y, rfl⟩
  have hk0o : orderOf k0 = n :=
    (orderOf_injective rhoM23 (rho11_injective _ _) k0).symm.trans ((congrArg orderOf hk0).trans
      (orderOf_injective _ (congrHom_injective e) y))
  have hpK : n.minFac ∣ 10200960 := by
    have := hpn.trans (hk0o ▸ orderOf_dvd_natCard k0)
    rwa [card_mog23] at this
  have hUz := hUy.trans (fixV_zpowers_pow_le y (n / n.minFac))
  have hzM : y ^ (n / n.minFac) ∈ M := M.pow_mem hyM _
  set z := y ^ (n / n.minFac) with hzdef
  have hz : orderOf z = n.minFac := orderOf_pow_orderOf_div hn0 hpn
  rcases prime_dvd_m23 hp hpK hp2 with h3 | h5 | h7 | h11 | h23
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [h3] at hz
    exact odd23_case T23s3_ok.2.2 (card_T23sp (by norm_num) (n := 2) T23s3_ok.2.1
      (by norm_num : (10200960 : ℕ) = 3 ^ 2 * 1133440) (by norm_num)) rfl odd23_ok.1 hLM he hO2
      hzM hz U hU hUz
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [h5] at hz
    exact odd23_case T23s5_ok.2.2 (card_T23sp (by norm_num) (n := 1) T23s5_ok.2.1
      (by norm_num : (10200960 : ℕ) = 5 ^ 1 * 2040192) (by norm_num)) rfl odd23_ok.2.1 hLM he
      hO2 hzM hz U hU hUz
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [h7] at hz
    exact odd23_case T23s7_ok.2.2 (card_T23sp (by norm_num) (n := 1) T23s7_ok.2.1
      (by norm_num : (10200960 : ℕ) = 7 ^ 1 * 1457280) (by norm_num)) rfl odd23_ok.2.2.1 hLM he
      hO2 hzM hz U hU hUz
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    rw [h11] at hz
    exact odd23_case T23s11_ok.2.2 (card_T23sp (by norm_num) (n := 1) T23s11_ok.2.1
      (by norm_num : (10200960 : ℕ) = 11 ^ 1 * 927360) (by norm_num)) rfl odd23_ok.2.2.2.1 hLM
      he hO2 hzM hz U hU hUz
  · have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    rw [h23] at hz
    exact odd23_case T23s23_ok.2.2 (card_T23sp (by norm_num) (n := 1) T23s23_ok.2.1
      (by norm_num : (10200960 : ℕ) = 23 ^ 1 * 443520) (by norm_num)) rfl odd23_ok.2.2.2.2 hLM
      he hO2 hzM hz U hU hUz

end CFSG.Quasithin.H.Mathieu

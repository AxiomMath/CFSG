
module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.HMathieuSyl22GreedyBase
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

@[expose] public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

theorem factorization_eq {p a b : ℕ} (hp : p.Prime) (hb : ¬ p ∣ b) :
    (p ^ a * b).factorization p = a := by
  have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero a hp.ne_zero) hb0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hb, smul_eq_mul, mul_one, add_zero]

variable {V : Type*} [CommGroup V]

theorem MaskCoords.card_eq_pow {n : ℕ} (c : MaskCoords V n) : Nat.card V = 2 ^ n := by
  have h1 := c.card_eq (⊤ : Subgroup V) (fun _ => true) fun m _ => by simp
  rw [Subgroup.card_top] at h1
  rw [h1, List.filter_true, List.length_range]

theorem MaskCoords.rk_eq {n : ℕ} (c : MaskCoords V n) : rk V = n := by
  unfold rk
  rw [c.card_eq_pow, padicValNat.prime_pow]

theorem MaskCoords.rk_of_card {n : ℕ} (c : MaskCoords V n) {U : Subgroup V} {F : List ℕ}
    (h : Nat.card U = F.length) : rk U = Nat.log 2 F.length := by
  have := c.finite
  have hc := card_eq_two_pow c.sq_eq_one U
  rw [← h, hc, Nat.log_pow (by norm_num)]

theorem MaskCoords.rkIdx_of_card {n : ℕ} (c : MaskCoords V n) {U : Subgroup V} {F : List ℕ}
    (h : Nat.card U = F.length) : rkIdx U = n - Nat.log 2 F.length := by
  have := c.finite
  have h1 := rk_add_rkIdx U
  rw [c.rk_eq, c.rk_of_card h] at h1
  omega

theorem mem_fixV_zpowers_iff {y : MulAut V} {v : V} : v ∈ fixV (Subgroup.zpowers y) ↔ y v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem apply_of_congrHom_eq {n : ℕ} {e' : V ≃* Wn n} {y : MulAut V} {f : MulAut (Wn n)}
    (h : congrHom e' y = f) (v : V) : e' (y v) = f (e' v) :=
  calc e' (y v) = e' (y (e'.symm (e' v))) := by rw [MulEquiv.symm_apply_apply]
    _ = congrHom e' y (e' v) := rfl
    _ = f (e' v) := DFunLike.congr_fun h (e' v)

theorem fixMasks_spec {n : ℕ} {P : Type*} [Group P] {c : MaskCoords V n} {aut : P →* MulAut V}
    {act : P → ℕ → ℕ} {l : List P} {A : Subgroup (MulAut V)} (hc : ChainAct c aut act)
    (hA : IsChainSub aut l A) {m : ℕ} (hm : m ∈ fixMasks n act l) :
    m < 2 ^ n ∧ c.vm m ∈ fixV A := by
  rw [fixMasks, List.mem_filter, List.mem_range] at hm
  exact ⟨hm.1, (vm_mem_fixV_iff hc hA hm.1).2 hm.2⟩

noncomputable abbrev psi22 : ↥mog22plus →* MulAut W10 := rho10 mog22plus le_rfl

abbrev phi22 : T22s2.Elem →* ↥mog22plus :=
  T22s2.toSub mog22plus (T22s2.mem_mog22plus T22s2_ok.2.2)

theorem act22s2_spec (s : T22s2.Elem) {m : ℕ} (hm : m < 2 ^ 10) :
    act22s2 s m = act10 (T22s2.arr s) m :=
  actM_mats10 T22s2 rfl s hm

theorem psi22_phi22 (s : T22s2.Elem) {m : ℕ} (hm : m < 2 ^ 10) :
    psi22 (phi22 s) (toW 10 m) = toW 10 (act22s2 s m) := by
  rw [act22s2_spec s hm]
  exact rho10_toW mog22plus le_rfl _ (T22s2.hasArr_toSub _ _ s) m

theorem card_T22s2
    : Nat.card T22s2.Elem = 2 ^ (Nat.card ↥mog22plus).factorization 2 := by
  rw [PT.card_elem, T22s2_ok.2.1, card_mog22plus,
    show (887040 : ℕ) = 2 ^ 8 * 3465 by norm_num, factorization_eq Nat.prime_two (by norm_num)]
  norm_num

variable {L M : Subgroup (MulAut V)}

theorem map_le_range22
    (hLM : IsOver L M) {e : V ≃* W10}
    (he : L.map (congrHom e) = (rho10 mog22 mog22_le_mog22plus).range) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) : A.map (congrHom e) ≤ psi22.range := by
  have h1 : A.map (congrHom e) ≤ (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) :=
    Subgroup.map_mono (hA.trans hLM.2)
  have h2 := Subgroup.le_normalizer_map (H := L) (congrHom e)
  have h3 : Subgroup.normalizer ((L.map (congrHom e) : Subgroup (MulAut W10)) : Set (MulAut W10))
      = psi22.range :=
    (congrArg (fun H : Subgroup (MulAut W10) => Subgroup.normalizer (H : Set (MulAut W10))) he).trans
      normalizer_rho10_mog22
  exact h1.trans (h2.trans h3.le)

theorem chainAct22 (e : V ≃* W10) (g : ↥mog22plus) :
    ChainAct (MaskCoords.ofEquiv (twistEquiv e psi22 g)) (chainAut e psi22 phi22 g) act22s2 :=
  chainAct_twist e psi22 phi22 g (fun s _ hm => psi22_phi22 s hm)
    (fun s _ hm => by rw [act22s2_spec s hm]; exact act10_lt _ _)

theorem chainAut22_injective
    (e : V ≃* W10) (g : ↥mog22plus) :
    Function.Injective (chainAut e psi22 phi22 g) :=
  chainAut_injective rho10_mog22plus_injective (T22s2.toSub_injective _ _) g

theorem pred22_spec {k : ℕ} {l : List T22s2.Elem}
    (h : pred22 k l = true) :
    k ≤ 5 ∧
      (10 - Nat.log 2 (fixMasks 10 act22s2 l).length ≤ k + 1 →
        o2OK o2Masks22 (fixMasks 10 act22s2 l) = true) ∧
      (k = 1 → 3 ≤ 10 - Nat.log 2 (fixMasks 10 act22s2 l).length) ∧
      (k = 4 → xiCheck 10 9 act22s2 l = true) ∧
      (k = 5 → xiCheck 10 10 act22s2 l = true ∧ pairCheck 10 10 act22s2 l = true) := by
  simp only [pred22, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hk, h1⟩, h2⟩, h3⟩, h4⟩ := h
  exact ⟨hk, fun hd => h1.resolve_left (not_not.2 hd), fun h1' => h2.resolve_left (not_not.2 h1'),
    fun h4' => h3.resolve_left (not_not.2 h4'), fun h5 => h4.resolve_left (not_not.2 h5)⟩

theorem rho10_inv_pairVec (g : ↥mog22plus) (j : Fin 24) :
    (psi22 g).symm (cocode22Coords.κ (pairVec 0 j)) =
      cocode22Coords.κ (pairVec 0 (((g⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) j)) := by
  rw [← rho10_pairVec g⁻¹ j, map_inv]
  rfl

theorem o2_twist22 {e : V ≃* W10}
    (hO2 : ∀ (v : V) (j : Fin 24), j ≠ 0 → j ≠ 1 → e v = cocode22Coords.κ (pairVec 0 j) →
      IsCocodeO2 L v) (g : ↥mog22plus) :
    ∀ o ∈ o2Masks22, (MaskCoords.ofEquiv (twistEquiv e psi22 g)).vm o ∈
      {v | IsCocodeO2 L v} := by
  intro o ho
  obtain ⟨j, hj0, hj1, hjo⟩ := toW_o2_22 ho
  set σ : Equiv.Perm (Fin 24) := ((g⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) with hσ
  have hg := (g⁻¹ : ↥mog22plus).2.2
  have hσj : σ j ≠ 0 ∧ σ j ≠ 1 := by
    have hinj := σ.injective
    rcases hg with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · exact ⟨fun h => hj0 (hinj (h.trans e0.symm)), fun h => hj1 (hinj (h.trans e1.symm))⟩
    · exact ⟨fun h => hj1 (hinj (h.trans e1.symm)), fun h => hj0 (hinj (h.trans e0.symm))⟩
  refine hO2 _ (σ j) hσj.1 hσj.2 ?_
  rw [MaskCoords.ofEquiv_vm]
  change e (e.symm ((psi22 g).symm (toW 10 o))) = _
  rw [MulEquiv.apply_symm_apply, hjo, rho10_inv_pairVec]

theorem cocode22_card
    (h : MathieuCocode22 L ⊤ ⊥) : Nat.card V = 2 ^ 10 :=
  (MaskCoords.ofEquiv (cocode22_stdO h).choose).card_eq_pow

theorem pow_apply_of_fix {y : MulAut V} {v : V} (h : y v = v) (k : ℕ) : (y ^ k) v = v := by
  induction k with
  | zero => rw [pow_zero, MulAut.one_apply]
  | succ k ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem fixV_zpowers_pow_le (y : MulAut V) (k : ℕ) :
    fixV (Subgroup.zpowers y) ≤ fixV (Subgroup.zpowers (y ^ k)) := fun _ hv =>
  mem_fixV_zpowers_iff.2 (pow_apply_of_fix (mem_fixV_zpowers_iff.1 hv) k)

theorem prime_dvd_aut22 {p : ℕ} (hp : p.Prime) (hdvd : p ∣ 887040) (hp2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  have e : (887040 : ℕ) = 2 ^ 8 * 3 ^ 2 * 5 * 7 * 11 := by norm_num
  rw [e] at hdvd
  have hq : ∀ q : ℕ, q.Prime → ∀ k, p ∣ q ^ k → p = q := fun q hq k h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h)
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact absurd (hq 2 Nat.prime_two 8 h) hp2
        · exact Or.inl (hq 3 (by norm_num) 2 h)
      · exact Or.inr (Or.inl (hq 5 (by norm_num) 1 (by simpa using h)))
    · exact Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) 1 (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (hq 11 (by norm_num) 1 (by simpa using h))))

theorem odd22_case
    {T : PT 24} [Fact (T.check = true)] (hT : T.allOK okPlus = true) {p : ℕ}
    [Fact p.Prime] (hsyl : Nat.card T.Elem = p ^ (Nat.card ↥mog22plus).factorization p)
    {mats : Array (List ℕ)} (hmats : mats = matsOf10 T) (hodd : odd22OK T mats)
    (hLM : IsOver L M) {e : V ≃* W10}
    (he : L.map (congrHom e) = (rho10 mog22 mog22_le_mog22plus).range)
    (hO2 : ∀ (v : V) (j : Fin 24), j ≠ 0 → j ≠ 1 → e v = cocode22Coords.κ (pairVec 0 j) →
      IsCocodeO2 L v)
    {z : MulAut V} (hzM : z ∈ M) (hz : orderOf z = p) (U : Subgroup V)
    (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v) (hUz : U ≤ fixV (Subgroup.zpowers z)) : rk U ≤ 4 := by
  have hzR : congrHom e z ∈ psi22.range :=
    map_le_range22 hLM he ((Subgroup.zpowers_le).2 hzM) ⟨z, Subgroup.mem_zpowers z, rfl⟩
  obtain ⟨g, s, hs1, hgs⟩ := exists_conj_elemModel psi22 rho10_mog22plus_injective
    (T.toSub mog22plus (T.mem_mog22plus hT)) (T.toSub_injective _ _) hsyl e hzR hz
  set e' := twistEquiv e psi22 g with he'
  set act : T.Elem → ℕ → ℕ := fun q m => actM (mats[q.idx]!) m with hactdef
  have hact10 : ∀ m < 2 ^ 10, act s m = act10 (T.arr s) m := fun m hm =>
    actM_mats10 T hmats s hm
  have hact : ∀ m < 2 ^ 10,
      psi22 (T.toSub mog22plus (T.mem_mog22plus hT) s) (toW 10 m) = toW 10 (act s m) := by
    intro m hm
    rw [hact10 m hm]
    exact rho10_toW mog22plus le_rfl _ (T.hasArr_toSub _ _ s) m
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
      exact toW_inj (by rw [hact10 m hm]; exact act10_lt _ _) hm (e'.symm.injective h3)
    · intro h3
      rw [h3]
  have hcard : Nat.card (fixV (Subgroup.zpowers z)) = (fixMasks 10 act [s]).length :=
    (MaskCoords.ofEquiv e').card_eq _ _ fun m hm => (hX m hm).trans (by simp)
  refine rk_le_four_of_o2OK (MaskCoords.ofEquiv e') (X := fixV (Subgroup.zpowers z))
    (F := fixMasks 10 act [s]) (fun m hm => ?_) hcard (o2_twist22 hO2 g) hUz
    (fun w hw hwO => hU w hw hwO) (hodd s hs1)
  rw [fixMasks, List.mem_filter, List.mem_range] at hm
  exact ⟨hm.1, (hX m hm.1).2 (by simpa using hm.2)⟩

theorem card_T22sp
    {T : PT 24} {p n b : ℕ} (hp : p.Prime) (hn : T.n = p ^ n)
    (hb : (887040 : ℕ) = p ^ n * b) (hpb : ¬ p ∣ b) :
    Nat.card T.Elem = p ^ (Nat.card ↥mog22plus).factorization p := by
  rw [PT.card_elem, hn, card_mog22plus, hb, factorization_eq hp hpb]

theorem cocode22_rk_le_four_odd
    [Finite V] (hLM : IsOver L M) (h : MathieuCocode22 L ⊤ ⊥)
    (U : Subgroup V) (hU : ∀ v ∈ U, ¬ IsCocodeO2 L v) {y : MulAut V} (hyM : y ∈ M)
    (hy1 : y ≠ 1) (hyo : Odd (orderOf y)) (hUy : U ≤ fixV (Subgroup.zpowers y)) : rk U ≤ 4 := by
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨e, he, hO2⟩ := cocode22_stdO h
  set n := orderOf y with hndef
  have hn0 : n ≠ 0 := (orderOf_pos y).ne'
  have hn1 : n ≠ 1 := fun h1 => hy1 (orderOf_eq_one_iff.1 h1)
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hpn : n.minFac ∣ n := Nat.minFac_dvd n
  have hp2 : n.minFac ≠ 2 := by
    intro h2
    rw [h2] at hpn
    exact (Nat.not_even_iff_odd.2 hyo) (even_iff_two_dvd.2 hpn)
  obtain ⟨k0, hk0⟩ : congrHom e y ∈ psi22.range :=
    map_le_range22 hLM he ((Subgroup.zpowers_le).2 hyM) ⟨y, Subgroup.mem_zpowers y, rfl⟩
  have hk0o : orderOf k0 = n :=
    (orderOf_injective psi22 rho10_mog22plus_injective k0).symm.trans ((congrArg orderOf hk0).trans
      (orderOf_injective _ (congrHom_injective e) y))
  have hpK : n.minFac ∣ 887040 := by
    have := hpn.trans (hk0o ▸ orderOf_dvd_natCard k0)
    rwa [card_mog22plus] at this
  have hUz := hUy.trans (fixV_zpowers_pow_le y (n / n.minFac))
  have hzM : y ^ (n / n.minFac) ∈ M := M.pow_mem hyM _
  set z := y ^ (n / n.minFac) with hzdef
  have hz : orderOf z = n.minFac := orderOf_pow_orderOf_div hn0 hpn
  rcases prime_dvd_aut22 hp hpK hp2 with h3 | h5 | h7 | h11
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [h3] at hz
    exact odd22_case T22s3_ok.2.2 (card_T22sp (by norm_num) (n := 2) T22s3_ok.2.1
      (by norm_num : (887040 : ℕ) = 3 ^ 2 * 98560) (by norm_num)) rfl odd22_ok.1 hLM he hO2
      hzM hz U hU hUz
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [h5] at hz
    exact odd22_case T22s5_ok.2.2 (card_T22sp (by norm_num) (n := 1) T22s5_ok.2.1
      (by norm_num : (887040 : ℕ) = 5 ^ 1 * 177408) (by norm_num)) rfl odd22_ok.2.1 hLM he hO2
      hzM hz U hU hUz
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [h7] at hz
    exact odd22_case T22s7_ok.2.2 (card_T22sp (by norm_num) (n := 1) T22s7_ok.2.1
      (by norm_num : (887040 : ℕ) = 7 ^ 1 * 126720) (by norm_num)) rfl odd22_ok.2.2.1 hLM he
      hO2 hzM hz U hU hUz
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    rw [h11] at hz
    exact odd22_case T22s11_ok.2.2 (card_T22sp (by norm_num) (n := 1) T22s11_ok.2.1
      (by norm_num : (887040 : ℕ) = 11 ^ 1 * 80640) (by norm_num)) rfl odd22_ok.2.2.2 hLM he
      hO2 hzM hz U hU hUz

end CFSG.Quasithin.H.Mathieu

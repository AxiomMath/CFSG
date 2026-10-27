module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.S12K.OrdRigid

public section

namespace CFSG.RankThree.PartOne

open CFSG.Open

theorem factorization_pow_sub_one {p x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx : 2 ≤ x)
    (hpx : ¬ p ∣ x) :
    (x ^ p - 1).factorization p =
      (x - 1).factorization p + if p ∣ x - 1 then 1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : 1 ≤ x ^ p := Nat.one_le_pow _ _ (by omega)
  by_cases hd : p ∣ x - 1
  · simp only [hd, ↓reduceIte]
    have := padicValNat.pow_sub_pow (p := p) (x := x) (y := 1) (hp.odd_of_ne_two hp2)
      (by omega) (by simpa using hd) hpx (n := p) hp.ne_zero
    simp only [one_pow, padicValNat_self] at this
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    exact this
  · simp only [hd, ↓reduceIte, add_zero]
    have h1 : ¬ p ∣ x ^ p - 1 := by
      intro h
      apply hd
      have h0 : ((x ^ p - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [Nat.cast_sub hx1] at h0
      simp only [Nat.cast_pow, Nat.cast_one, ZMod.pow_card] at h0
      have h2 : ((x - 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub (by omega)]
        simpa using h0
      exact (ZMod.natCast_eq_zero_iff _ _).mp h2
    rw [Nat.factorization_eq_zero_of_not_dvd h1, Nat.factorization_eq_zero_of_not_dvd hd]

theorem factorization_pow_add_one {p x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpx : ¬ p ∣ x) :
    (x ^ p + 1).factorization p =
      (x + 1).factorization p + if p ∣ x + 1 then 1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hd : p ∣ x + 1
  · simp only [hd, ↓reduceIte]
    have := padicValNat.pow_add_pow (p := p) (x := x) (y := 1) (hp.odd_of_ne_two hp2)
      (by simpa using hd) hpx (n := p) (hp.odd_of_ne_two hp2)
    simp only [one_pow, padicValNat_self] at this
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    exact this
  · simp only [hd, ↓reduceIte, add_zero]
    have h1 : ¬ p ∣ x ^ p + 1 := by
      intro h
      apply hd
      have h0 : ((x ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ZMod.pow_card] at h0
      have h2 : ((x + 1 : ℕ) : ZMod p) = 0 := by
        simpa using h0
      exact (ZMod.natCast_eq_zero_iff _ _).mp h2
    rw [Nat.factorization_eq_zero_of_not_dvd h1, Nat.factorization_eq_zero_of_not_dvd hd]

inductive FacKind
  | sub
  | add
  | phi3

@[expose] def fac : FacKind → ℕ → ℕ → ℕ
  | .sub, k, Q => Q ^ k - 1
  | .add, k, Q => Q ^ k + 1
  | .phi3, k, Q => Q ^ (2 * k) + Q ^ k + 1

theorem fac_pos {b : FacKind} {k Q : ℕ} (hQ : 2 ≤ Q) (hk : 1 ≤ k) : 0 < fac b k Q := by
  have h1 : 2 ≤ Q ^ k := by
    calc 2 ≤ Q := hQ
      _ = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ k := Nat.pow_le_pow_right (by omega) hk
  cases b <;> simp only [fac] <;> omega

theorem factorization_phi3_pow {p x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hx : 2 ≤ x)
    (hpx : ¬ p ∣ x) :
    ((x ^ p) ^ 2 + x ^ p + 1).factorization p =
      (x ^ 2 + x + 1).factorization p + if p ∣ x ^ 2 + x + 1 then 1 else 0 := by
  have hx3 : 2 ≤ x ^ 3 := by
    calc 2 ≤ x := hx
      _ = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hxp : 2 ≤ x ^ p := by
    calc 2 ≤ x := hx
      _ = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
  have hpx3 : ¬ p ∣ x ^ 3 := fun h => hpx (hp.dvd_of_dvd_pow h)
  have hid : ∀ z : ℕ, 1 ≤ z → (z ^ 2 + z + 1) * (z - 1) = z ^ 3 - 1 := by
    intro z hz
    obtain ⟨w, rfl⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (w + 1) ^ 3 = (w + 1) ^ 3 - 1 + 1 := by
      have : 1 ≤ (w + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    have h2 : ((w + 1) ^ 2 + (w + 1) + 1) * w + 1 = (w + 1) ^ 3 := by ring
    omega
  have hΦ : ∀ z : ℕ, 2 ≤ z → (z ^ 2 + z + 1).factorization p + (z - 1).factorization p =
      (z ^ 3 - 1).factorization p := by
    intro z hz
    have h1 : z ^ 2 + z + 1 ≠ 0 := by positivity
    have h2 : z - 1 ≠ 0 := by omega
    rw [← hid z (by omega), Nat.factorization_mul h1 h2, Finsupp.add_apply]
  have h1 := hΦ (x ^ p) hxp
  have h2 := hΦ x hx
  have e3 : (x ^ p) ^ 3 = (x ^ 3) ^ p := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e3, factorization_pow_sub_one hp hp2 hx3 hpx3, factorization_pow_sub_one hp hp2 hx hpx] at h1
  have hfac : (x ^ 3 - 1).factorization p = (x ^ 2 + x + 1).factorization p + (x - 1).factorization p := h2.symm
  rw [hfac] at h1
  have hpc : p ∣ x ^ 3 - 1 ↔ p ∣ x - 1 ∨ p ∣ x ^ 2 + x + 1 := by
    rw [← hid x (by omega), hp.dvd_mul]
    exact or_comm
  by_cases h3 : p ∣ x - 1
  · have hnot : ¬ p ∣ x ^ 2 + x + 1 := by
      intro h4
      have h5 : p ∣ 3 := by
        have : x ^ 2 + x + 1 = (x - 1) * (x + 2) + 3 := by
          obtain ⟨w, rfl⟩ : ∃ w, x = w + 1 := ⟨x - 1, by omega⟩
          simp only [Nat.add_sub_cancel]; ring
        rw [this] at h4
        exact (Nat.dvd_add_right (dvd_mul_of_dvd_left h3 _)).mp h4
      have := Nat.le_of_dvd (by norm_num) h5
      have := hp.two_le
      omega
    have h6 : p ∣ x ^ 3 - 1 := hpc.mpr (Or.inl h3)
    simp only [h3, h6, hnot, ↓reduceIte] at h1 ⊢
    omega
  · have : p ∣ x ^ 3 - 1 ↔ p ∣ x ^ 2 + x + 1 := by
      rw [hpc]
      simp [h3]
    by_cases h4 : p ∣ x ^ 2 + x + 1
    · have h6 : p ∣ x ^ 3 - 1 := this.mpr h4
      simp only [h3, h4, h6, ↓reduceIte] at h1 ⊢
      omega
    · have h6 : ¬ p ∣ x ^ 3 - 1 := fun h => h4 (this.mp h)
      simp only [h3, h4, h6, ↓reduceIte] at h1 ⊢
      omega

theorem factorization_fac_pow {p Q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hQ : 2 ≤ Q) (hpQ : ¬ p ∣ Q) {b : FacKind} {k : ℕ} (hk : 1 ≤ k) :
    (fac b k (Q ^ p)).factorization p =
      (fac b k Q).factorization p + if p ∣ fac b k Q then 1 else 0 := by
  have hQk : 2 ≤ Q ^ k := by
    calc 2 ≤ Q := hQ
      _ = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ k := Nat.pow_le_pow_right (by omega) hk
  have hpk : ¬ p ∣ Q ^ k := fun h => hpQ (hp.dvd_of_dvd_pow h)
  have hpow : (Q ^ p) ^ k = (Q ^ k) ^ p := by rw [← pow_mul, ← pow_mul, mul_comm]
  cases b
  · simp only [fac, hpow]
    exact factorization_pow_sub_one hp hp2 hQk hpk
  · simp only [fac, hpow]
    exact factorization_pow_add_one hp hp2 hpk
  · have e : (Q ^ p) ^ (2 * k) + (Q ^ p) ^ k + 1 = ((Q ^ k) ^ p) ^ 2 + (Q ^ k) ^ p + 1 := by ring
    have e2 : Q ^ (2 * k) + Q ^ k + 1 = (Q ^ k) ^ 2 + Q ^ k + 1 := by ring
    simp only [fac, e, e2]
    exact factorization_phi3_pow hp hp2 hp3 hQk hpk


theorem factorization_listprod_fac {p Q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hQ : 2 ≤ Q) (hpQ : ¬ p ∣ Q) (L : List (FacKind × ℕ)) (hk : ∀ x ∈ L, 1 ≤ x.2) :
    ((L.map fun x => fac x.1 x.2 (Q ^ p)).prod).factorization p =
      ((L.map fun x => fac x.1 x.2 Q).prod).factorization p +
        (L.filter fun x => decide (p ∣ fac x.1 x.2 Q)).length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hkx : 1 ≤ x.2 := hk x (List.mem_cons_self)
    have hkL : ∀ y ∈ L, 1 ≤ y.2 := fun y hy => hk y (List.mem_cons_of_mem _ hy)
    have hQp : 2 ≤ Q ^ p := by
      calc 2 ≤ Q := hQ
        _ = Q ^ 1 := (pow_one Q).symm
        _ ≤ Q ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
    have hprod_ne : ∀ R : ℕ, 2 ≤ R → ((L.map fun y => fac y.1 y.2 R).prod) ≠ 0 := by
      intro R hR
      rw [Ne, List.prod_eq_zero_iff]
      simp only [List.mem_map, not_exists, not_and]
      intro y hy
      exact (fac_pos hR (hkL y hy)).ne'
    simp only [List.map_cons, List.prod_cons]
    rw [Nat.factorization_mul (fac_pos hQp hkx).ne' (hprod_ne _ hQp),
      Nat.factorization_mul (fac_pos hQ hkx).ne' (hprod_ne _ hQ)]
    simp only [Finsupp.add_apply]
    rw [factorization_fac_pow hp hp2 hp3 hQ hpQ hkx, ih hkL]
    by_cases hd : p ∣ fac x.1 x.2 Q <;> simp [hd] <;> omega

theorem not_dvd_listprod {p : ℕ} (hp : p.Prime) {l : List ℕ} (h : ∀ x ∈ l, ¬ p ∣ x) :
    ¬ p ∣ l.prod := by
  induction l with
  | nil => simpa using hp.one_lt.ne'
  | cons x l ih =>
    simp only [List.prod_cons]
    rw [hp.dvd_mul]
    push Not
    exact ⟨h x (by simp), ih (fun y hy => h y (by simp [hy]))⟩

theorem listprod_lt {p Q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q)
    (hpQ : ¬ p ∣ Q) (L : List (FacKind × ℕ)) (hk : ∀ x ∈ L, 1 ≤ x.2)
    (hdvd : p ∣ (L.map fun x => fac x.1 x.2 (Q ^ p)).prod) :
    ((L.map fun x => fac x.1 x.2 Q).prod).factorization p <
      ((L.map fun x => fac x.1 x.2 (Q ^ p)).prod).factorization p := by
  have heq := factorization_listprod_fac hp hp2 hp3 hQ hpQ L hk
  have hQp : 2 ≤ Q ^ p := by
    calc 2 ≤ Q := hQ
      _ = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
  have hne : ((L.map fun x => fac x.1 x.2 (Q ^ p)).prod) ≠ 0 := by
    rw [Ne, List.prod_eq_zero_iff]
    simp only [List.mem_map, not_exists, not_and]
    intro y hy
    exact (fac_pos hQp (hk y hy)).ne'
  have hpos : 1 ≤ ((L.map fun x => fac x.1 x.2 (Q ^ p)).prod).factorization p :=
    (hp.factorization_pos_of_dvd hne hdvd)
  by_contra hlt
  have hcard : (L.filter fun x => decide (p ∣ fac x.1 x.2 Q)).length = 0 := by omega
  have hnone : ∀ x ∈ L, ¬ p ∣ fac x.1 x.2 Q := by
    intro x hx hdx
    have : x ∈ L.filter fun x => decide (p ∣ fac x.1 x.2 Q) := by
      simp [List.mem_filter, hx, hdx]
    rw [List.length_eq_zero_iff] at hcard
    rw [hcard] at this
    simp at this
  have h0 : ¬ p ∣ (L.map fun x => fac x.1 x.2 Q).prod :=
    not_dvd_listprod hp (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact hnone x hx)
  have h00 := Nat.factorization_eq_zero_of_not_dvd h0
  omega

theorem finprod_fac_eq_list {ι : Type*} (s : Finset ι) (b : ι → FacKind) (k : ι → ℕ) (R : ℕ) :
    ∏ i ∈ s, fac (b i) (k i) R =
      (((s.toList.map fun i => (b i, k i)).map fun x => fac x.1 x.2 R)).prod := by
  rw [List.map_map, Finset.prod_map_toList]
  rfl

theorem ord_lt_of_prod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {Q e : ℕ}
    (hQ : 2 ≤ Q) (hpQ : ¬ p ∣ Q) (L : List (FacKind × ℕ)) (hk : ∀ x ∈ L, 1 ≤ x.2)
    (ord g : ℕ → ℕ)
    (hord : ∀ R, 2 ≤ R → ord R * g R = R ^ e * (L.map fun x => fac x.1 x.2 R).prod)
    (hg : ∀ R, 2 ≤ R → ¬ p ∣ g R) (hdvd : p ∣ ord (Q ^ p)) :
    (ord Q).factorization p < (ord (Q ^ p)).factorization p := by
  have hQp : 2 ≤ Q ^ p := by
    calc 2 ≤ Q := hQ
      _ = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
  have hpQp : ¬ p ∣ Q ^ p := fun h => hpQ (hp.dvd_of_dvd_pow h)
  have hprod_ne : ∀ R : ℕ, 2 ≤ R → ((L.map fun x => fac x.1 x.2 R).prod) ≠ 0 := by
    intro R hR
    rw [Ne, List.prod_eq_zero_iff]
    simp only [List.mem_map, not_exists, not_and]
    intro y hy
    exact (fac_pos hR (hk y hy)).ne'
  have hF : ∀ R, 2 ≤ R → ¬ p ∣ R →
      (ord R).factorization p = ((L.map fun x => fac x.1 x.2 R).prod).factorization p := by
    intro R hR hpR
    have hg0 : g R ≠ 0 := fun h0 => hg R hR (by rw [h0]; exact dvd_zero p)
    have hRe : R ^ e ≠ 0 := pow_ne_zero _ (by omega)
    have hord0 : ord R ≠ 0 := by
      intro h0
      have := hord R hR
      rw [h0, zero_mul] at this
      exact (mul_ne_zero hRe (hprod_ne R hR)) this.symm
    have h1 : (ord R * g R).factorization p =
        (R ^ e * (L.map fun x => fac x.1 x.2 R).prod).factorization p := by
      rw [hord R hR]
    rw [Nat.factorization_mul hord0 hg0, Nat.factorization_mul hRe (hprod_ne R hR)] at h1
    simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd hpR, Nat.factorization_eq_zero_of_not_dvd (hg R hR),
      smul_zero, zero_add, add_zero] at h1
    exact h1
  rw [hF Q hQ hpQ, hF (Q ^ p) hQp hpQp]
  apply listprod_lt hp hp2 hp3 hQ hpQ L hk
  have h1 : p ∣ ord (Q ^ p) * g (Q ^ p) := dvd_mul_of_dvd_left hdvd _
  rw [hord _ hQp] at h1
  rcases (hp.dvd_mul).mp h1 with h | h
  · exact absurd (hp.dvd_of_dvd_pow h) hpQp
  · exact h

section Exceptional

variable {p Q : ℕ}

theorem not_dvd_gcd_of_le_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {m x : ℕ}
    (hm : m ≤ 3) (hm0 : 0 < m) : ¬ p ∣ Nat.gcd m x := by
  intro h
  have h1 : p ∣ m := h.trans (Nat.gcd_dvd_left m x)
  have := Nat.le_of_dvd hm0 h1
  have := hp.two_le
  omega

theorem ordG2_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q) (hpQ : ¬ p ∣ Q)
    (hdvd : p ∣ ordG2 (Q ^ p)) :
    (ordG2 Q).factorization p < (ordG2 (Q ^ p)).factorization p :=
  ord_lt_of_prod hp hp2 hp3 hQ hpQ [(.sub, 6), (.sub, 2)] (by simp) ordG2 (fun _ => 1) (e := 6)
    (fun R _ => by simp [ordG2, fac]; ring) (fun R _ => hp.not_dvd_one) hdvd

theorem ordF4_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q) (hpQ : ¬ p ∣ Q)
    (hdvd : p ∣ ordF4 (Q ^ p)) :
    (ordF4 Q).factorization p < (ordF4 (Q ^ p)).factorization p :=
  ord_lt_of_prod hp hp2 hp3 hQ hpQ [(.sub, 12), (.sub, 8), (.sub, 6), (.sub, 2)] (by simp) ordF4
    (fun _ => 1) (e := 24) (fun R _ => by simp [ordF4, fac]; ring) (fun R _ => hp.not_dvd_one)
    hdvd

theorem ordE8_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q) (hpQ : ¬ p ∣ Q)
    (hdvd : p ∣ ordE8 (Q ^ p)) :
    (ordE8 Q).factorization p < (ordE8 (Q ^ p)).factorization p :=
  ord_lt_of_prod hp hp2 hp3 hQ hpQ
    [(.sub, 30), (.sub, 24), (.sub, 20), (.sub, 18), (.sub, 14), (.sub, 12), (.sub, 8),
      (.sub, 2)] (by simp) ordE8 (fun _ => 1) (e := 120)
    (fun R _ => by simp [ordE8, fac]; ring) (fun R _ => hp.not_dvd_one) hdvd

theorem ordTrialityD4_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q)
    (hpQ : ¬ p ∣ Q) (hdvd : p ∣ ordTrialityD4 (Q ^ p)) :
    (ordTrialityD4 Q).factorization p < (ordTrialityD4 (Q ^ p)).factorization p :=
  ord_lt_of_prod hp hp2 hp3 hQ hpQ [(.phi3, 4), (.sub, 6), (.sub, 2)] (by simp) ordTrialityD4
    (fun _ => 1) (e := 12) (fun R _ => by simp [ordTrialityD4, fac]; ring)
    (fun R _ => hp.not_dvd_one) hdvd

theorem ordTwistedF4_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q)
    (hpQ : ¬ p ∣ Q) (hdvd : p ∣ ordTwistedF4 (Q ^ p)) :
    (ordTwistedF4 Q).factorization p < (ordTwistedF4 (Q ^ p)).factorization p :=
  ord_lt_of_prod hp hp2 hp3 hQ hpQ [(.add, 6), (.sub, 4), (.add, 3), (.sub, 1)] (by simp)
    ordTwistedF4 (fun _ => 1) (e := 12) (fun R _ => by simp [ordTwistedF4, fac]; ring)
    (fun R _ => hp.not_dvd_one) hdvd

theorem ordSuzuki_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q) (hpQ : ¬ p ∣ Q)
    (hdvd : p ∣ ordSuzuki (Q ^ p)) :
    (ordSuzuki Q).factorization p < (ordSuzuki (Q ^ p)).factorization p :=
  ord_lt_of_prod hp hp2 hp3 hQ hpQ [(.add, 2), (.sub, 1)] (by simp) ordSuzuki (fun _ => 1)
    (e := 2) (fun R _ => by simp [ordSuzuki, fac]; ring) (fun R _ => hp.not_dvd_one) hdvd

theorem ordE6_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q) (hpQ : ¬ p ∣ Q)
    (hdvd : p ∣ ordE6 (Q ^ p)) :
    (ordE6 Q).factorization p < (ordE6 (Q ^ p)).factorization p :=
  ord_lt_of_prod hp hp2 hp3 hQ hpQ
    [(.sub, 12), (.sub, 9), (.sub, 8), (.sub, 6), (.sub, 5), (.sub, 2)] (by simp) ordE6
    (fun R => Nat.gcd 3 (R - 1)) (e := 36)
    (fun R hR => by
      have hdvd' : Nat.gcd 3 (R - 1) ∣ R ^ 36 * (R ^ 12 - 1) * (R ^ 9 - 1) * (R ^ 8 - 1) *
          (R ^ 6 - 1) * (R ^ 5 - 1) * (R ^ 2 - 1) :=
        (Nat.gcd_dvd_right 3 (R - 1)).trans (by
          have := Nat.sub_dvd_pow_sub_pow R 1 2
          simpa using this.mul_left _)
      simp only [ordE6]
      rw [Nat.div_mul_cancel hdvd']
      simp [fac]; ring)
    (fun R _ => not_dvd_gcd_of_le_three hp hp2 hp3 (by norm_num) (by norm_num)) hdvd

theorem ordE7_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q) (hpQ : ¬ p ∣ Q)
    (hdvd : p ∣ ordE7 (Q ^ p)) :
    (ordE7 Q).factorization p < (ordE7 (Q ^ p)).factorization p :=
  ord_lt_of_prod hp hp2 hp3 hQ hpQ
    [(.sub, 18), (.sub, 14), (.sub, 12), (.sub, 10), (.sub, 8), (.sub, 6), (.sub, 2)]
    (by simp) ordE7 (fun R => Nat.gcd 2 (R - 1)) (e := 63)
    (fun R hR => by
      have hdvd' : Nat.gcd 2 (R - 1) ∣ R ^ 63 * (R ^ 18 - 1) * (R ^ 14 - 1) * (R ^ 12 - 1) *
          (R ^ 10 - 1) * (R ^ 8 - 1) * (R ^ 6 - 1) * (R ^ 2 - 1) :=
        (Nat.gcd_dvd_right 2 (R - 1)).trans (by
          have := Nat.sub_dvd_pow_sub_pow R 1 2
          simpa using this.mul_left _)
      simp only [ordE7]
      rw [Nat.div_mul_cancel hdvd']
      simp [fac]; ring)
    (fun R _ => not_dvd_gcd_of_le_three hp hp2 hp3 (by norm_num) (by norm_num)) hdvd

theorem ordTwistedE6_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q)
    (hpQ : ¬ p ∣ Q) (hdvd : p ∣ ordTwistedE6 (Q ^ p)) :
    (ordTwistedE6 Q).factorization p < (ordTwistedE6 (Q ^ p)).factorization p :=
  ord_lt_of_prod hp hp2 hp3 hQ hpQ
    [(.sub, 12), (.add, 9), (.sub, 8), (.sub, 6), (.add, 5), (.sub, 2)] (by simp) ordTwistedE6
    (fun R => Nat.gcd 3 (R + 1)) (e := 36)
    (fun R hR => by
      have hdvd' : Nat.gcd 3 (R + 1) ∣ R ^ 36 * (R ^ 12 - 1) * (R ^ 9 + 1) * (R ^ 8 - 1) *
          (R ^ 6 - 1) * (R ^ 5 + 1) * (R ^ 2 - 1) := by
        have h1 : R + 1 ∣ R ^ 5 + 1 := by
          simpa using Odd.nat_add_dvd_pow_add_pow R 1 (by decide : Odd 5)
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (((Nat.gcd_dvd_right 3 (R + 1)).trans h1)) _) _
      simp only [ordTwistedE6]
      rw [Nat.div_mul_cancel hdvd']
      simp [fac]; ring)
    (fun R _ => not_dvd_gcd_of_le_three hp hp2 hp3 (by norm_num) (by norm_num)) hdvd

theorem not_dvd_gcd_of_le_four {p : ℕ} (h5 : 5 ≤ p) {m x : ℕ} (hm : m ≤ 4) (hm0 : 0 < m) :
    ¬ p ∣ Nat.gcd m x := by
  intro h
  have h1 : p ∣ m := h.trans (Nat.gcd_dvd_left m x)
  have := Nat.le_of_dvd hm0 h1
  omega

theorem ordBC_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h5 : 5 ≤ p) (hQ : 2 ≤ Q)
    (hpQ : ¬ p ∣ Q) {n : ℕ} (hn : 1 ≤ n) (hdvd : p ∣ ordBC n (Q ^ p)) :
    (ordBC n Q).factorization p < (ordBC n (Q ^ p)).factorization p := by
  set L : List (FacKind × ℕ) := (Finset.Icc 1 n).toList.map fun i => (FacKind.sub, 2 * i) with hL
  refine ord_lt_of_prod hp hp2 hp3 hQ hpQ L ?_ (ordBC n) (fun R => Nat.gcd 2 (R - 1))
    (e := n * n) ?_ (fun R _ => not_dvd_gcd_of_le_four h5 (by norm_num) (by norm_num)) hdvd
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := (Finset.mem_Icc.mp (Finset.mem_toList.mp hi)).1
    simp only
    omega
  · intro R hR
    have hprod : ∏ i ∈ Finset.Icc 1 n, (R ^ (2 * i) - 1) =
        (L.map fun x => fac x.1 x.2 R).prod := by
      rw [hL, ← finprod_fac_eq_list (Finset.Icc 1 n) (fun _ => FacKind.sub) (fun i => 2 * i) R]
      simp [fac]
    have hdvd' : Nat.gcd 2 (R - 1) ∣ R ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (R ^ (2 * i) - 1) := by
      refine Dvd.dvd.mul_left ?_ _
      refine (Nat.gcd_dvd_right 2 (R - 1)).trans ?_
      have h2 : R - 1 ∣ R ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow R 1 2
      refine h2.trans ?_
      have h3 := Finset.dvd_prod_of_mem (fun i => R ^ (2 * i) - 1)
        (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
      simpa using h3
    simp only [ordBC]
    rw [Nat.div_mul_cancel hdvd', hprod]

theorem ordD_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h5 : 5 ≤ p) (hQ : 2 ≤ Q)
    (hpQ : ¬ p ∣ Q) {n : ℕ} (hn : 1 ≤ n) (hdvd : p ∣ ordD n (Q ^ p)) :
    (ordD n Q).factorization p < (ordD n (Q ^ p)).factorization p := by
  set L : List (FacKind × ℕ) := (FacKind.sub, n) ::
    (Finset.Icc 1 (n - 1)).toList.map fun i => (FacKind.sub, 2 * i) with hL
  refine ord_lt_of_prod hp hp2 hp3 hQ hpQ L ?_ (ordD n) (fun R => Nat.gcd 4 (R ^ n - 1))
    (e := n * (n - 1)) ?_ (fun R _ => not_dvd_gcd_of_le_four h5 (by norm_num) (by norm_num)) hdvd
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa using hn
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have := (Finset.mem_Icc.mp (Finset.mem_toList.mp hi)).1
      simp only
      omega
  · intro R hR
    have hprod : ∏ i ∈ Finset.Icc 1 (n - 1), (R ^ (2 * i) - 1) =
        ((((Finset.Icc 1 (n - 1)).toList.map fun i => (FacKind.sub, 2 * i)).map
          fun x => fac x.1 x.2 R)).prod := by
      rw [← finprod_fac_eq_list (Finset.Icc 1 (n - 1)) (fun _ => FacKind.sub) (fun i => 2 * i) R]
      simp [fac]
    have hdvd' : Nat.gcd 4 (R ^ n - 1) ∣
        R ^ (n * (n - 1)) * (R ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (R ^ (2 * i) - 1) :=
      ((Nat.gcd_dvd_right 4 (R ^ n - 1)).trans (dvd_mul_left _ _)).mul_right _
    simp only [ordD]
    rw [Nat.div_mul_cancel hdvd', hL, List.map_cons, List.prod_cons, hprod]
    simp [fac, mul_assoc]

theorem ordTwistedD_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h5 : 5 ≤ p) (hQ : 2 ≤ Q)
    (hpQ : ¬ p ∣ Q) {n : ℕ} (hn : 1 ≤ n) (hdvd : p ∣ ordTwistedD n (Q ^ p)) :
    (ordTwistedD n Q).factorization p < (ordTwistedD n (Q ^ p)).factorization p := by
  set L : List (FacKind × ℕ) := (FacKind.add, n) ::
    (Finset.Icc 1 (n - 1)).toList.map fun i => (FacKind.sub, 2 * i) with hL
  refine ord_lt_of_prod hp hp2 hp3 hQ hpQ L ?_ (ordTwistedD n) (fun R => Nat.gcd 4 (R ^ n + 1))
    (e := n * (n - 1)) ?_ (fun R _ => not_dvd_gcd_of_le_four h5 (by norm_num) (by norm_num)) hdvd
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa using hn
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have := (Finset.mem_Icc.mp (Finset.mem_toList.mp hi)).1
      simp only
      omega
  · intro R hR
    have hprod : ∏ i ∈ Finset.Icc 1 (n - 1), (R ^ (2 * i) - 1) =
        ((((Finset.Icc 1 (n - 1)).toList.map fun i => (FacKind.sub, 2 * i)).map
          fun x => fac x.1 x.2 R)).prod := by
      rw [← finprod_fac_eq_list (Finset.Icc 1 (n - 1)) (fun _ => FacKind.sub) (fun i => 2 * i) R]
      simp [fac]
    have hdvd' : Nat.gcd 4 (R ^ n + 1) ∣
        R ^ (n * (n - 1)) * (R ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (R ^ (2 * i) - 1) :=
      ((Nat.gcd_dvd_right 4 (R ^ n + 1)).trans (dvd_mul_left _ _)).mul_right _
    simp only [ordTwistedD]
    rw [Nat.div_mul_cancel hdvd', hL, List.map_cons, List.prod_cons, hprod]
    simp [fac, mul_assoc]

theorem listprod_card_pos {p Q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hQ : 2 ≤ Q)
    (hpQ : ¬ p ∣ Q) (L : List (FacKind × ℕ)) (hk : ∀ x ∈ L, 1 ≤ x.2)
    (hdvd : p ∣ (L.map fun x => fac x.1 x.2 (Q ^ p)).prod) :
    1 ≤ (L.filter fun x => decide (p ∣ fac x.1 x.2 Q)).length := by
  have h1 := listprod_lt hp hp2 hp3 hQ hpQ L hk hdvd
  have h2 := factorization_listprod_fac hp hp2 hp3 hQ hpQ L hk
  omega

theorem ordA_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h5 : 5 ≤ p) (hQ : 2 ≤ Q)
    (hpQ : ¬ p ∣ Q) {m : ℕ} (hm : 1 ≤ m) (hdvd : p ∣ ordA m (Q ^ p)) :
    (ordA m Q).factorization p < (ordA m (Q ^ p)).factorization p := by
  classical
  set L : List (FacKind × ℕ) := (Finset.Icc 2 (m + 1)).toList.map fun i => (FacKind.sub, i)
    with hL
  have hk : ∀ x ∈ L, 1 ≤ x.2 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := (Finset.mem_Icc.mp (Finset.mem_toList.mp hi)).1
    simp only
    omega
  have hQp : 2 ≤ Q ^ p := by
    calc 2 ≤ Q := hQ
      _ = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
  have hpQp : ¬ p ∣ Q ^ p := fun h => hpQ (hp.dvd_of_dvd_pow h)
  have hprod : ∀ R, ∏ i ∈ Finset.Icc 2 (m + 1), (R ^ i - 1) =
      (L.map fun x => fac x.1 x.2 R).prod := by
    intro R
    rw [hL, ← finprod_fac_eq_list (Finset.Icc 2 (m + 1)) (fun _ => FacKind.sub) (fun i => i) R]
    simp [fac]
  have hdvd' : ∀ R, 2 ≤ R → Nat.gcd (m + 1) (R - 1) ∣
      R ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (R ^ i - 1) := by
    intro R hR
    refine Dvd.dvd.mul_left ?_ _
    refine (Nat.gcd_dvd_right (m + 1) (R - 1)).trans ?_
    have h2 : R - 1 ∣ R ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow R 1 2
    refine h2.trans ?_
    exact Finset.dvd_prod_of_mem (fun i => R ^ i - 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hord : ∀ R, 2 ≤ R → ordA m R * Nat.gcd (m + 1) (R - 1) =
      R ^ (m * (m + 1) / 2) * (L.map fun x => fac x.1 x.2 R).prod := by
    intro R hR
    simp only [ordA]
    rw [Nat.div_mul_cancel (hdvd' R hR), hprod R]
  have hP0 : ∀ R, 2 ≤ R → ((L.map fun x => fac x.1 x.2 R).prod) ≠ 0 := by
    intro R hR
    rw [Ne, List.prod_eq_zero_iff]
    simp only [List.mem_map, not_exists, not_and]
    intro y hy
    exact (fac_pos hR (hk y hy)).ne'
  have hFnum : ∀ R, 2 ≤ R → ¬ p ∣ R → (ordA m R).factorization p +
      (Nat.gcd (m + 1) (R - 1)).factorization p =
        ((L.map fun x => fac x.1 x.2 R).prod).factorization p := by
    intro R hR hpR
    have hg0 : Nat.gcd (m + 1) (R - 1) ≠ 0 := by
      have : 0 < Nat.gcd (m + 1) (R - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
      omega
    have hRe : R ^ (m * (m + 1) / 2) ≠ 0 := pow_ne_zero _ (by omega)
    have hord0 : ordA m R ≠ 0 := by
      intro h0
      have := hord R hR
      rw [h0, zero_mul] at this
      exact (mul_ne_zero hRe (hP0 R hR)) this.symm
    have h1 : (ordA m R * Nat.gcd (m + 1) (R - 1)).factorization p =
        (R ^ (m * (m + 1) / 2) * (L.map fun x => fac x.1 x.2 R).prod).factorization p := by
      rw [hord R hR]
    rw [Nat.factorization_mul hord0 hg0, Nat.factorization_mul hRe (hP0 R hR)] at h1
    simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd hpR, smul_zero, zero_add] at h1
    exact h1
  have hgF : ∀ R, 2 ≤ R → (Nat.gcd (m + 1) (R - 1)).factorization p =
      min ((m + 1).factorization p) ((R - 1).factorization p) := by
    intro R hR
    rw [Nat.factorization_gcd (by omega) (by omega)]
    rfl
  have hA := factorization_listprod_fac hp hp2 hp3 hQ hpQ L hk
  have hN1 := hFnum Q hQ hpQ
  have hN2 := hFnum (Q ^ p) hQp hpQp
  have hQ1 := factorization_pow_sub_one hp hp2 hQ hpQ
  have hg1 := hgF Q hQ
  have hg2 := hgF (Q ^ p) hQp
  by_cases h1 : p ∣ Q - 1
  ·
    have hall : (L.filter fun x => decide (p ∣ fac x.1 x.2 Q)).length = m := by
      have : L.filter (fun x => decide (p ∣ fac x.1 x.2 Q)) = L := by
        rw [List.filter_eq_self]
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        simp only [fac]
        exact decide_eq_true (h1.trans (by simpa using Nat.sub_dvd_pow_sub_pow Q 1 i))
      rw [this, hL, List.length_map, Finset.length_toList, Nat.card_Icc]
      omega
    have hm1 : m = 1 → (m + 1).factorization p = 0 := by
      intro h
      subst h
      exact Nat.factorization_eq_zero_of_not_dvd (fun h => by
        have := Nat.le_of_dvd (by norm_num) h
        omega)
    simp only [h1, ↓reduceIte] at hQ1
    rw [hall] at hA
    omega
  · have hc := listprod_card_pos hp hp2 hp3 hQ hpQ L hk (by
      have h1 : p ∣ ordA m (Q ^ p) * Nat.gcd (m + 1) (Q ^ p - 1) := dvd_mul_of_dvd_left hdvd _
      rw [hord _ hQp] at h1
      rcases (hp.dvd_mul).mp h1 with h | h
      · exact absurd (hp.dvd_of_dvd_pow h) hpQp
      · exact h)
    have h0 : (Q - 1).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd h1
    simp only [h1, ↓reduceIte] at hQ1
    omega

@[expose] def kindU (i : ℕ) : FacKind := if i % 2 = 0 then .sub else .add

theorem toNat_sub_neg_one_pow (R i : ℕ) (hR : 1 ≤ R) :
    ((R : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = fac (kindU i) i R := by
  have h1 : 1 ≤ R ^ i := Nat.one_le_pow _ _ (by omega)
  have hc : ((R : ℤ) ^ i) = ((R ^ i : ℕ) : ℤ) := by push_cast; rfl
  rcases Nat.even_or_odd i with he | ho
  · have : i % 2 = 0 := Nat.even_iff.mp he
    simp only [kindU, this, ↓reduceIte, fac, he.neg_one_pow]
    rw [hc]
    omega
  · have : ¬ i % 2 = 0 := by have := Nat.odd_iff.mp ho; omega
    simp only [kindU, this, ↓reduceIte, fac, ho.neg_one_pow]
    rw [hc]
    omega

theorem ordTwistedA_lt (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h5 : 5 ≤ p) (hQ : 2 ≤ Q)
    (hpQ : ¬ p ∣ Q) {m : ℕ} (hm : 1 ≤ m) (hdvd : p ∣ ordTwistedA m (Q ^ p)) :
    (ordTwistedA m Q).factorization p < (ordTwistedA m (Q ^ p)).factorization p := by
  classical
  set L : List (FacKind × ℕ) := (Finset.Icc 2 (m + 1)).toList.map fun i => (kindU i, i) with hL
  have hk : ∀ x ∈ L, 1 ≤ x.2 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := (Finset.mem_Icc.mp (Finset.mem_toList.mp hi)).1
    simp only
    omega
  have hQp : 2 ≤ Q ^ p := by
    calc 2 ≤ Q := hQ
      _ = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
  have hpQp : ¬ p ∣ Q ^ p := fun h => hpQ (hp.dvd_of_dvd_pow h)
  have hprod : ∀ R : ℕ, 2 ≤ R → ∏ i ∈ Finset.Icc 2 (m + 1), ((R : ℤ) ^ i - (-1 : ℤ) ^ i).toNat =
      (L.map fun x => fac x.1 x.2 R).prod := by
    intro R hR
    rw [hL, ← finprod_fac_eq_list (Finset.Icc 2 (m + 1)) kindU (fun i => i) R]
    exact Finset.prod_congr rfl fun i _ => toNat_sub_neg_one_pow R i (by omega)
  have hsq : ∀ R, 1 ≤ R → R + 1 ∣ R ^ 2 - 1 := by
    intro R hR
    obtain ⟨w, rfl⟩ : ∃ w, R = w + 1 := ⟨R - 1, by omega⟩
    refine ⟨w, ?_⟩
    have : (w + 1) ^ 2 = (w + 1 + 1) * w + 1 := by ring
    omega
  have hdvd' : ∀ R, 2 ≤ R → Nat.gcd (m + 1) (R + 1) ∣
      R ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), ((R : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
    intro R hR
    refine Dvd.dvd.mul_left ?_ _
    refine (Nat.gcd_dvd_right (m + 1) (R + 1)).trans ?_
    refine (hsq R (by omega)).trans ?_
    have h2 : ((R : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat ∣
        ∏ i ∈ Finset.Icc 2 (m + 1), ((R : ℤ) ^ i - (-1 : ℤ) ^ i).toNat :=
      Finset.dvd_prod_of_mem (fun i => ((R : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
        (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩ : 2 ∈ Finset.Icc 2 (m + 1))
    have h3 : ((R : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = R ^ 2 - 1 := by
      have := toNat_sub_neg_one_pow R 2 (by omega)
      simpa [fac, kindU] using this
    rw [h3] at h2
    exact h2
  have hord : ∀ R, 2 ≤ R → ordTwistedA m R * Nat.gcd (m + 1) (R + 1) =
      R ^ (m * (m + 1) / 2) * (L.map fun x => fac x.1 x.2 R).prod := by
    intro R hR
    simp only [ordTwistedA]
    rw [Nat.div_mul_cancel (hdvd' R hR), hprod R hR]
  have hP0 : ∀ R, 2 ≤ R → ((L.map fun x => fac x.1 x.2 R).prod) ≠ 0 := by
    intro R hR
    rw [Ne, List.prod_eq_zero_iff]
    simp only [List.mem_map, not_exists, not_and]
    intro y hy
    exact (fac_pos hR (hk y hy)).ne'
  have hFnum : ∀ R, 2 ≤ R → ¬ p ∣ R → (ordTwistedA m R).factorization p +
      (Nat.gcd (m + 1) (R + 1)).factorization p =
        ((L.map fun x => fac x.1 x.2 R).prod).factorization p := by
    intro R hR hpR
    have hg0 : Nat.gcd (m + 1) (R + 1) ≠ 0 := by
      have : 0 < Nat.gcd (m + 1) (R + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
      omega
    have hRe : R ^ (m * (m + 1) / 2) ≠ 0 := pow_ne_zero _ (by omega)
    have hord0 : ordTwistedA m R ≠ 0 := by
      intro h0
      have := hord R hR
      rw [h0, zero_mul] at this
      exact (mul_ne_zero hRe (hP0 R hR)) this.symm
    have h1 : (ordTwistedA m R * Nat.gcd (m + 1) (R + 1)).factorization p =
        (R ^ (m * (m + 1) / 2) * (L.map fun x => fac x.1 x.2 R).prod).factorization p := by
      rw [hord R hR]
    rw [Nat.factorization_mul hord0 hg0, Nat.factorization_mul hRe (hP0 R hR)] at h1
    simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd hpR, smul_zero, zero_add] at h1
    exact h1
  have hgF : ∀ R, 2 ≤ R → (Nat.gcd (m + 1) (R + 1)).factorization p =
      min ((m + 1).factorization p) ((R + 1).factorization p) := by
    intro R hR
    rw [Nat.factorization_gcd (by omega) (by omega)]
    rfl
  have hA := factorization_listprod_fac hp hp2 hp3 hQ hpQ L hk
  have hN1 := hFnum Q hQ hpQ
  have hN2 := hFnum (Q ^ p) hQp hpQp
  have hQ1 := factorization_pow_add_one hp hp2 hpQ
  have hg1 := hgF Q hQ
  have hg2 := hgF (Q ^ p) hQp
  by_cases h1 : p ∣ Q + 1
  · have hall : (L.filter fun x => decide (p ∣ fac x.1 x.2 Q)).length = m := by
      have : L.filter (fun x => decide (p ∣ fac x.1 x.2 Q)) = L := by
        rw [List.filter_eq_self]
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        refine decide_eq_true ?_
        rcases Nat.even_or_odd i with he | ho
        · have hi2 : i % 2 = 0 := Nat.even_iff.mp he
          obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j := ⟨i / 2, by omega⟩
          simp only [kindU, hi2, ↓reduceIte, fac]
          have h2 : Q ^ 2 - 1 ∣ (Q ^ 2) ^ j - 1 := by
            simpa using Nat.sub_dvd_pow_sub_pow (Q ^ 2) 1 j
          rw [pow_mul]
          exact h1.trans ((hsq Q (by omega)).trans h2)
        · have hi2 : ¬ i % 2 = 0 := by have := Nat.odd_iff.mp ho; omega
          simp only [kindU, hi2, ↓reduceIte, fac]
          exact h1.trans (by simpa using Odd.nat_add_dvd_pow_add_pow Q 1 ho)
      rw [this, hL, List.length_map, Finset.length_toList, Nat.card_Icc]
      omega
    have hm1 : m = 1 → (m + 1).factorization p = 0 := by
      intro h
      subst h
      exact Nat.factorization_eq_zero_of_not_dvd (fun h => by
        have := Nat.le_of_dvd (by norm_num) h
        omega)
    simp only [h1, ↓reduceIte] at hQ1
    rw [hall] at hA
    omega
  · have hc := listprod_card_pos hp hp2 hp3 hQ hpQ L hk (by
      have h1 : p ∣ ordTwistedA m (Q ^ p) * Nat.gcd (m + 1) (Q ^ p + 1) :=
        dvd_mul_of_dvd_left hdvd _
      rw [hord _ hQp] at h1
      rcases (hp.dvd_mul).mp h1 with h | h
      · exact absurd (hp.dvd_of_dvd_pow h) hpQp
      · exact h)
    have h0 : (Q + 1).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd h1
    simp only [h1, ↓reduceIte] at hQ1
    omega

end Exceptional

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.RankThree.PartOne.S12K (charTwoOrder)

theorem charTwoOrder_pval_lt {t : StatedLieTag} {n f p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hadm : StatedLieAdmissible t n 2 f) (hadm' : StatedLieAdmissible t n 2 (p * f))
    (hdvd : p ∣ charTwoOrder t n (p * f)) :
    (charTwoOrder t n f).factorization p < (charTwoOrder t n (p * f)).factorization p := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hf : 1 ≤ f := hadm.2.1
  have hQ : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hpQ : ¬ p ∣ 2 ^ f := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow h))
  have hpow : 2 ^ (p * f) = (2 ^ f) ^ p := by rw [mul_comm, pow_mul]
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordA_lt hp hp2 hp3 h5 hQ hpQ (m := n - 1) (by omega) hdvd
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordTwistedA_lt hp hp2 hp3 h5 hQ hpQ (m := n - 1) (by omega) hdvd
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordBC_lt hp hp2 hp3 h5 hQ hpQ (by omega) hdvd
  case POmegaOdd =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordBC_lt hp hp2 hp3 h5 hQ hpQ (by omega) hdvd
  case POmegaPlus =>
    simp only [StatedLieAdmissible] at hadm
    obtain ⟨-, -, hn⟩ := hadm
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordD_lt hp hp2 hp3 h5 hQ hpQ (by omega) hdvd
  case POmegaMinus =>
    simp only [StatedLieAdmissible] at hadm
    obtain ⟨-, -, hn⟩ := hadm
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordTwistedD_lt hp hp2 hp3 h5 hQ hpQ (by omega) hdvd
  case G2 =>
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordG2_lt hp hp2 hp3 hQ hpQ hdvd
  case F4 =>
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordF4_lt hp hp2 hp3 hQ hpQ hdvd
  case E6 =>
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordE6_lt hp hp2 hp3 hQ hpQ hdvd
  case E7 =>
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordE7_lt hp hp2 hp3 hQ hpQ hdvd
  case E8 =>
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordE8_lt hp hp2 hp3 hQ hpQ hdvd
  case twistedE6 =>
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordTwistedE6_lt hp hp2 hp3 hQ hpQ hdvd
  case trialityD4 =>
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordTrialityD4_lt hp hp2 hp3 hQ hpQ hdvd
  case twistedB2 =>
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordSuzuki_lt hp hp2 hp3 hQ hpQ hdvd
  case twistedG2 =>
    exact absurd hadm.2.2.2.1 (by norm_num)
  case twistedF4 =>
    simp only [charTwoOrder, hpow] at hdvd ⊢
    exact ordTwistedF4_lt hp hp2 hp3 hQ hpQ hdvd
  case Tits =>
    have h1 : p * f = 1 := hadm'.2.2.2.2
    have : 1 ≤ f := hf
    have : p ≤ p * f := Nat.le_mul_of_pos_right p hf
    omega

end CFSG.RankThree.PartOne

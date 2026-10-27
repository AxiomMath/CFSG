module

public import CFSG.Quasithin.H13.L32A511Qa

public section

namespace CFSG.Quasithin.H13.Q511

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem map_map_commHom (g r : MulAut V) :
    ((⊤ : Subgroup V).map (commHom r)).map (g : V →* V) =
      (⊤ : Subgroup V).map (commHom (g * r * g⁻¹)) := by
  ext v
  constructor
  · rintro ⟨_, ⟨u, -, rfl⟩, rfl⟩
    refine ⟨g u, Subgroup.mem_top _, ?_⟩
    simp [commHom_apply, MulAut.mul_apply, MulAut.inv_apply]
  · rintro ⟨u, -, rfl⟩
    refine ⟨commHom r (g⁻¹ u), ⟨g⁻¹ u, Subgroup.mem_top _, rfl⟩, ?_⟩
    simp [commHom_apply, MulAut.mul_apply, MulAut.inv_apply]

omit [Finite V] in
theorem mem_fix_conj_iff {g e : MulAut V} {v : V} :
    g v ∈ fixV (Subgroup.zpowers (g * e * g⁻¹)) ↔ v ∈ fixV (Subgroup.zpowers e) := by
  rw [mem_fixV_zpowers_iff, mem_fixV_zpowers_iff]
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  exact g.injective.eq_iff

omit [Finite V] in
theorem rk_map_aut (H : Subgroup V) (g : MulAut V) : rk (H.map (g : V →* V)) = rk H := by
  unfold rk
  rw [← Nat.card_congr (H.equivMapOfInjective _ g.injective).toEquiv]

omit [Finite V] in
theorem eq_one_of_forall {g : MulAut V} (h : ∀ v, g v = v) : g = 1 := MulEquiv.ext h

omit [Finite V] in
theorem map_commHom_ne_bot {r : MulAut V} (hr : r ≠ 1) :
    (⊤ : Subgroup V).map (commHom r) ≠ ⊥ := by
  intro h
  apply hr
  refine eq_one_of_forall fun v => ?_
  have : commHom r v ∈ (⊤ : Subgroup V).map (commHom r) := ⟨v, Subgroup.mem_top _, rfl⟩
  rw [h, Subgroup.mem_bot, commHom_apply, mul_inv_eq_one] at this
  exact this

omit [Finite V] in
theorem mem_map_commHom_of_comm {r g : MulAut V} (hc : g * r = r * g) {u : V}
    (hu : u ∈ (⊤ : Subgroup V).map (commHom r)) : g u ∈ (⊤ : Subgroup V).map (commHom r) := by
  obtain ⟨v, -, rfl⟩ := hu
  refine ⟨g v, Subgroup.mem_top _, ?_⟩
  have : g (r v) = r (g v) := by
    have := congrArg (fun h : MulAut V => h v) hc
    simpa using this
  rw [commHom_apply, commHom_apply, map_mul, map_inv, this]

omit [Finite V] in
theorem mem_map_commHom_of_inv {r g : MulAut V} (hc : g * r * g⁻¹ = r⁻¹) {u : V}
    (hu : u ∈ (⊤ : Subgroup V).map (commHom r)) : g u ∈ (⊤ : Subgroup V).map (commHom r) := by
  obtain ⟨v, -, rfl⟩ := hu
  have h1 : g (r v) = r⁻¹ (g v) := by
    have := congrArg (fun h : MulAut V => h (g v)) hc
    simpa [MulAut.mul_apply] using this
  have h2 : g (commHom r v) = (commHom r (r⁻¹ (g v)))⁻¹ := by
    rw [commHom_apply, commHom_apply, map_mul, map_inv, h1]
    simp only [MulAut.inv_apply, MulEquiv.apply_symm_apply]
    rw [mul_inv, inv_inv, mul_comm]
  rw [h2]
  exact Subgroup.inv_mem _ ⟨r⁻¹ (g v), Subgroup.mem_top _, rfl⟩

omit [Finite V] in
theorem mem_fix_of_comm {r g : MulAut V} (hc : g * r = r * g) {u : V}
    (hu : u ∈ fixV (Subgroup.zpowers r)) : g u ∈ fixV (Subgroup.zpowers r) := by
  rw [mem_fixV_zpowers_iff] at hu ⊢
  have := congrArg (fun h : MulAut V => h u) hc
  simp only [MulAut.mul_apply] at this
  rw [← this, hu]

omit [Finite V] in
theorem fix_inv_iff {r : MulAut V} {u : V} :
    u ∈ fixV (Subgroup.zpowers r⁻¹) ↔ u ∈ fixV (Subgroup.zpowers r) := by
  rw [Subgroup.zpowers_inv]

omit [Finite V] in
theorem inf_fix_le_of_le {U U' : Subgroup V} (h : U ≤ U') (g : MulAut V)
    (h' : U' ⊓ fixV (Subgroup.zpowers g) = ⊥) : U ⊓ fixV (Subgroup.zpowers g) = ⊥ :=
  le_bot_iff.mp (h' ▸ inf_le_inf_right _ h)

omit [Finite V] in
theorem map_commHom_inf_fix_top (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} {n : ℕ} (hn : Odd n)
    (hg : g ^ n = 1) :
    (⊤ : Subgroup V).map (commHom g) ⊓ fixV (Subgroup.zpowers g) = ⊥ :=
  map_commHom_inf_fix_eq_bot hV hn hg ⊤

theorem prime_dvd_of_even {p d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 2 ^ d - 1)
    (hd : d ≤ 6) (hd0 : 0 < d) (hev : Even d) : (p = 5 ∧ d = 4) ∨ (p = 7 ∧ d = 6) := by
  obtain ⟨k, rfl⟩ := hev
  have hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | rfl | rfl
  · exfalso
    have := Nat.le_of_dvd (by norm_num) h
    norm_num at this
    omega
  · left
    refine ⟨?_, rfl⟩
    have h15 : p ∣ 3 * 5 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).mp h15 with h3 | h5
    · exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
    · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
  · right
    refine ⟨?_, rfl⟩
    have h63 : p ∣ 3 ^ 2 * 7 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).mp h63 with h9 | h7
    · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h9)) (by omega)
    · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7

theorem false_of_nonabelian (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {r r₁ w s : MulAut V} (hw : w = r * r₁ * r⁻¹ * r₁⁻¹) (hw1 : w ≠ 1)
    (hwr : w * r = r * w) (hwr₁ : w * r₁ = r₁ * w) (hrp : r ^ p = 1) (hwp : w ^ p = 1)
    (hs2 : s ^ 2 = 1) (hsr : s * r * s⁻¹ = r⁻¹) (hsw : s * w * s⁻¹ = w⁻¹)
    (hs3 : rk ((⊤ : Subgroup V).map (commHom s)) ≤ 3) : False := by
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  set U := (⊤ : Subgroup V).map (commHom w) with hU
  have hUw : ∀ u ∈ U, w u ∈ U := fun u hu => mem_map_commHom_of_comm rfl hu
  have hUr : ∀ u ∈ U, r u ∈ U := fun u hu => mem_map_commHom_of_comm hwr.symm hu
  have hUr₁ : ∀ u ∈ U, r₁ u ∈ U := fun u hu => mem_map_commHom_of_comm hwr₁.symm hu
  have hUs : ∀ u ∈ U, s u ∈ U := fun u hu => mem_map_commHom_of_inv hsw hu
  have hfixU : U ⊓ fixV (Subgroup.zpowers w) = ⊥ := map_commHom_inf_fix_top hV hpodd hwp
  have hD := rk_eq_two_mul_of_inverts hV hUw hUs hfixU hs2 hsw
  have hUs' := rk_map_add_rk_inf U s
  have hle : rk (U.map (commHom s)) ≤ rk ((⊤ : Subgroup V).map (commHom s)) :=
    rk_mono (Subgroup.map_mono le_top)
  have hrkU : rk U ≤ 6 := by omega
  set L : ℕ → Subgroup V := fun i => U ⊓ fixV (Subgroup.zpowers (r * w ^ i)) with hL
  have hgen : ∀ u ∈ U, u ∈ ⨆ i ∈ Finset.range p, L i :=
    fun u hu => mem_iSup_inf_fix hV hp.out hp2 hwp hrp hwr hUw hUr hfixU hu
  have hdisj : L 0 ⊓ L 1 = ⊥ :=
    inf_inf_fix_eq_bot hp.out hwp hwr hfixU (by norm_num) (by omega)
  have hconj : ∀ i : ℕ, r₁ * (r * w ^ (i + 1)) * r₁⁻¹ = r * w ^ i := by
    intro i
    have h1 : r₁ * r * r₁⁻¹ = w⁻¹ * r := by rw [hw]; group
    have hc : Commute w r₁ := hwr₁
    have h2 : r₁ * w ^ (i + 1) * r₁⁻¹ = w ^ (i + 1) := by
      rw [← (hc.pow_left (i + 1)).eq, mul_inv_cancel_right]
    have h3 : w⁻¹ * r = r * w⁻¹ := (Commute.inv_left (hwr : Commute w r)).eq
    calc r₁ * (r * w ^ (i + 1)) * r₁⁻¹ = (r₁ * r * r₁⁻¹) * (r₁ * w ^ (i + 1) * r₁⁻¹) := by group
      _ = w⁻¹ * r * w ^ (i + 1) := by rw [h1, h2]
      _ = r * w ^ i := by rw [h3, mul_assoc, pow_succ', inv_mul_cancel_left]
  have hmapL : ∀ i : ℕ, (L (i + 1)).map (r₁ : V →* V) = L i := by
    intro i
    ext v
    constructor
    · rintro ⟨u, ⟨huU, huf⟩, rfl⟩
      refine ⟨hUr₁ u huU, ?_⟩
      have := (mem_fix_conj_iff (g := r₁) (e := r * w ^ (i + 1))).mpr huf
      rwa [hconj i] at this
    · rintro ⟨hvU, hvf⟩
      refine ⟨r₁⁻¹ v, ⟨inv_mem_of_invariant hUr₁ v hvU, ?_⟩, by simp⟩
      rw [← hconj i] at hvf
      exact (mem_fix_conj_iff (g := r₁) (e := r * w ^ (i + 1))).mp (by simpa using hvf)
  have hrk0 : ∀ i : ℕ, rk (L i) = rk (L 0) := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [← ih, ← hmapL i, rk_map_aut]
  have hUne : U ≠ ⊥ := map_commHom_ne_bot hw1
  have hL0 : L 0 ≠ ⊥ := by
    intro h0
    apply hUne
    have hall : ∀ i, L i = ⊥ := fun i =>
      (rk_eq_zero_iff hV).mp (by rw [hrk0 i, (rk_eq_zero_iff hV).mpr h0])
    rw [eq_bot_iff]
    intro u hu
    have h := hgen u hu
    have hb : (⨆ i ∈ Finset.range p, L i) = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun i _ => ?_)
      rw [hall i]
    rwa [hb] at h
  have hL0eq : L 0 = U ⊓ fixV (Subgroup.zpowers r) := by
    show U ⊓ fixV (Subgroup.zpowers (r * w ^ 0)) = _
    rw [pow_zero, mul_one]
  have hL0w : ∀ u ∈ L 0, w u ∈ L 0 := by
    rw [hL0eq]
    rintro u ⟨huU, huf⟩
    exact ⟨hUw u huU, mem_fix_of_comm hwr huf⟩
  have hL0s : ∀ u ∈ L 0, s u ∈ L 0 := by
    rw [hL0eq]
    intro u hu
    obtain ⟨huU, huf⟩ := mem_inf_fix.mp hu
    refine mem_inf_fix.mpr ⟨hUs u huU, ?_⟩
    have h1 : s (r u) = r⁻¹ (s u) := by
      have := congrArg (fun h : MulAut V => h (s u)) hsr
      simp only [MulAut.mul_apply] at this
      rw [← this]
      simp
    have h2 : r⁻¹ (s u) = s u := by rw [← h1, huf]
    calc r (s u) = r (r⁻¹ (s u)) := by rw [h2]
      _ = s u := by simp
  have hL0fix : L 0 ⊓ fixV (Subgroup.zpowers w) = ⊥ := inf_fix_le_of_le inf_le_left w hfixU
  have hL0D := rk_eq_two_mul_of_inverts hV hL0w hL0s hL0fix hs2 hsw
  have hsum := rk_sup_add_rk_inf (L 0) (L 1)
  rw [hdisj, rk_bot, hrk0 1] at hsum
  have hsup : rk ↥(L 0 ⊔ L 1) ≤ rk U := rk_mono (sup_le inf_le_left inf_le_left)
  have hpos : 0 < rk (L 0) := Nat.pos_of_ne_zero fun h => hL0 ((rk_eq_zero_iff hV).mp h)
  have h2 : rk (L 0) = 2 := by omega
  have hdvd := dvd_two_pow_rk_sub_one hV (p := p) hL0w hwp hL0fix
  rw [h2] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem eq_inf_fix_sup_map (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} {n : ℕ} (hn : Odd n)
    (hg : g ^ n = 1) {A : Subgroup V} (hA : ∀ u ∈ A, g u ∈ A) :
    A = (A ⊓ fixV (Subgroup.zpowers g)) ⊔ A.map (commHom g) := by
  have hle : (A ⊓ fixV (Subgroup.zpowers g)) ⊔ A.map (commHom g) ≤ A :=
    sup_le inf_le_left (map_commHom_le hA)
  refine (eq_of_le_of_rk_le hV hle ?_).symm
  have h1 := rk_map_add_rk_inf A g
  have h2 := rk_sup_add_rk_inf (A ⊓ fixV (Subgroup.zpowers g)) (A.map (commHom g))
  have h3 : (A ⊓ fixV (Subgroup.zpowers g)) ⊓ A.map (commHom g) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have := map_commHom_inf_fix_eq_bot hV hn hg A
    rw [← this]
    exact ⟨hv.2, hv.1.2⟩
  rw [h3, rk_bot] at h2
  omega

omit [Finite V] in
theorem pow_apply_eq_self {g : MulAut V} {u : V} (h : g u = u) (n : ℕ) : (g ^ n) u = u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem rk_of_dvd_five {k : ℕ} (h : 5 ∣ 2 ^ k - 1) (hk : k ≤ 4) : k = 0 ∨ k = 4 := by
  interval_cases k <;> simp_all

theorem rk_of_dvd_seven {k : ℕ} (h : 7 ∣ 2 ^ k - 1) (hk : k ≤ 6) : k = 0 ∨ k = 3 ∨ k = 6 := by
  interval_cases k <;> simp_all

theorem false_of_abelian (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {r r₁ x s : MulAut V} (hrp : r ^ p = 1) (hr₁p : r₁ ^ p = 1) (hr1 : r ≠ 1)
    (hc : r * r₁ = r₁ * r) (hind : ∀ k : ℕ, r₁ ≠ r ^ k)
    (hxr : x * r * x⁻¹ = r₁) (hxr₁ : x * r₁ * x⁻¹ = (r * r₁)⁻¹)
    (hs2 : s ^ 2 = 1) (hsr : s * r * s⁻¹ = r⁻¹)
    (hb : rk ((⊤ : Subgroup V).map (commHom s)) ≤ 2 ∨
      ∃ c : MulAut V, c ^ 2 = 1 ∧ c ≠ 1 ∧ c * s = s * c ∧
        ((c * r * c⁻¹ = r ∧ c * r₁ * c⁻¹ = r₁) ∨ (c * r * c⁻¹ = r⁻¹ ∧ c * r₁ * c⁻¹ = r₁⁻¹)) ∧
        rkIdx (fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers c)) ≤ 3) : False := by
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  set U := (⊤ : Subgroup V).map (commHom r) with hU
  have hUr : ∀ u ∈ U, r u ∈ U := fun u hu => mem_map_commHom_of_comm rfl hu
  have hUr₁ : ∀ u ∈ U, r₁ u ∈ U := fun u hu => mem_map_commHom_of_comm hc.symm hu
  have hUs : ∀ u ∈ U, s u ∈ U := fun u hu => mem_map_commHom_of_inv hsr hu
  have hfixU : U ⊓ fixV (Subgroup.zpowers r) = ⊥ := map_commHom_inf_fix_top hV hpodd hrp
  have hUne : U ≠ ⊥ := map_commHom_ne_bot hr1
  have hrV := rk_map_add_rk_inf (⊤ : Subgroup V) s
  rw [top_inf_eq, rk_top] at hrV
  have hs3 : rk ((⊤ : Subgroup V).map (commHom s)) ≤ 3 := by
    rcases hb with h | ⟨c, -, -, -, -, h⟩
    · omega
    · have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers c))
      have h3 : rk ↥(fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers c)) ≤
          rk (fixV (Subgroup.zpowers s)) := rk_mono inf_le_left
      omega
  have hD := rk_eq_two_mul_of_inverts hV hUr hUs hfixU hs2 hsr
  have hUs' := rk_map_add_rk_inf U s
  have hle : rk (U.map (commHom s)) ≤ rk ((⊤ : Subgroup V).map (commHom s)) :=
    rk_mono (Subgroup.map_mono le_top)
  have hrkU6 : rk U ≤ 6 := by omega
  have hrkU0 : 0 < rk U := Nat.pos_of_ne_zero fun h => hUne ((rk_eq_zero_iff hV).mp h)
  have hdvdU := dvd_two_pow_rk_sub_one hV hUr hrp hfixU
  have hpU := prime_dvd_of_even hp.out hp5 hdvdU hrkU6 hrkU0
    ⟨rk (U ⊓ fixV (Subgroup.zpowers s) : Subgroup V), by omega⟩
  set L : ℕ → Subgroup V := fun i => U ⊓ fixV (Subgroup.zpowers (r₁ * r ^ i)) with hL
  have hgen : ∀ u ∈ U, u ∈ ⨆ i ∈ Finset.range p, L i :=
    fun u hu => mem_iSup_inf_fix hV hp.out hp2 hrp hr₁p hc hUr hUr₁ hfixU hu
  have hLr : ∀ i, ∀ u ∈ L i, r u ∈ L i := by
    intro i u hu
    obtain ⟨huU, huf⟩ := mem_inf_fix.mp hu
    have hcomm : r * (r₁ * r ^ i) = (r₁ * r ^ i) * r :=
      (Commute.mul_right hc (Commute.self_pow r i)).eq
    exact Subgroup.mem_inf.mpr ⟨hUr u huU, mem_fix_of_comm hcomm (mem_fixV_zpowers_iff.mpr huf)⟩
  have hLfix : ∀ i, L i ⊓ fixV (Subgroup.zpowers r) = ⊥ := fun i =>
    inf_fix_le_of_le inf_le_left r hfixU
  have hLdvd : ∀ i, p ∣ 2 ^ rk (L i) - 1 := fun i =>
    dvd_two_pow_rk_sub_one hV (hLr i) hrp (hLfix i)
  have hLrk : ∀ i, rk (L i) ≤ rk U := fun i => rk_mono inf_le_left
  have hLU : ∀ i, rk (L i) = rk U → L i = U := fun i h =>
    eq_of_le_of_rk_le hV inf_le_left h.ge
  obtain ⟨i₀, hi₀p, hi₀⟩ : ∃ i < p, L i ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hUne
    rw [eq_bot_iff]
    intro u hu
    have h := hgen u hu
    have hb : (⨆ i ∈ Finset.range p, L i) = ⊥ :=
      le_bot_iff.mp (iSup₂_le fun i hi => (hcon i (Finset.mem_range.mp hi)).le)
    rwa [hb] at h
  have hpos : ∀ i, L i ≠ ⊥ → 0 < rk (L i) := fun i h =>
    Nat.pos_of_ne_zero fun h0 => h ((rk_eq_zero_iff hV).mp h0)
  have hcases : (∃ i < p, L i = U) ∨
      (p = 7 ∧ ∃ i j, i < j ∧ j < p ∧ rk (L i) = 3 ∧ rk (L j) = 3 ∧ L i ⊔ L j = U) := by
    rcases hpU with ⟨rfl, h4⟩ | ⟨rfl, h6⟩
    · left
      refine ⟨i₀, hi₀p, hLU i₀ ?_⟩
      rcases rk_of_dvd_five (hLdvd i₀) (by rw [← h4]; exact hLrk i₀) with h | h
      · exact absurd h (hpos i₀ hi₀).ne'
      · rw [h, h4]
    · rcases rk_of_dvd_seven (hLdvd i₀) (by rw [← h6]; exact hLrk i₀) with h | h | h
      · exact absurd h (hpos i₀ hi₀).ne'
      ·
        by_cases hj : ∃ j < 7, j ≠ i₀ ∧ L j ≠ ⊥
        · obtain ⟨j, hjp, hji, hjne⟩ := hj
          rcases rk_of_dvd_seven (hLdvd j) (by rw [← h6]; exact hLrk j) with h' | h' | h'
          · exact absurd h' (hpos j hjne).ne'
          · right
            refine ⟨rfl, ?_⟩
            have key : ∀ a b, a < b → b < 7 → rk (L a) = 3 → rk (L b) = 3 →
                L a ⊔ L b = U := by
              intro a b hab hb7 ha hb
              have hdisj := inf_inf_fix_eq_bot hp.out hrp hc hfixU hab hb7 (r₁ := r₁) (U := U)
              have hsum := rk_sup_add_rk_inf (L a) (L b)
              rw [show L a ⊓ L b = ⊥ from hdisj, rk_bot, ha, hb] at hsum
              exact eq_of_le_of_rk_le hV (sup_le inf_le_left inf_le_left) (by omega)
            rcases lt_or_gt_of_ne hji with hlt | hgt
            · exact ⟨j, i₀, hlt, hi₀p, h', h, key j i₀ hlt hi₀p h' h⟩
            · exact ⟨i₀, j, hgt, hjp, h, h', key i₀ j hgt hjp h h'⟩
          · left
            exact ⟨j, hjp, hLU j (by rw [h', h6])⟩
        · exfalso
          push Not at hj
          have hUle : U ≤ L i₀ := by
            intro u hu
            have hmem := hgen u hu
            have hle' : (⨆ i ∈ Finset.range 7, L i) ≤ L i₀ := by
              refine iSup₂_le fun i hi => ?_
              by_cases hii : i = i₀
              · rw [hii]
              · rw [hj i (Finset.mem_range.mp hi) hii]
                exact bot_le
            exact hle' hmem
          have := rk_mono hUle
          omega
      · left
        exact ⟨i₀, hi₀p, hLU i₀ (by rw [h, h6])⟩
  rcases hcases with ⟨i, hip, hi⟩ | ⟨hp7, i, j, hij, hjp, hi3, hj3, hsup⟩
  ·
    have hfixe : ∀ u ∈ U, (r₁ * r ^ i) u = u := by
      intro u hu
      rw [← hi] at hu
      exact (mem_inf_fix.mp hu).2
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    ·
      have hr₁U : ∀ u ∈ U, r₁ u = u := fun u hu => by
        have := hfixe u hu
        rwa [pow_zero, mul_one] at this
      have hr₂U : ∀ u ∈ U, (r * r₁)⁻¹ u = r⁻¹ u := by
        intro u hu
        rw [mul_inv_rev, MulAut.mul_apply]
        have h1 : r⁻¹ u ∈ U := inv_mem_of_invariant hUr u hu
        have h2 : r₁⁻¹ (r⁻¹ u) = r⁻¹ u := by
          conv_lhs => rw [← hr₁U _ h1]
          simp
        exact h2
      have hUr₂ : ∀ u ∈ U, (r * r₁)⁻¹ u ∈ U := fun u hu => by
        rw [hr₂U u hu]; exact inv_mem_of_invariant hUr u hu
      have hfix₂ : U ⊓ fixV (Subgroup.zpowers (r * r₁)⁻¹) = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        obtain ⟨huU, huf⟩ := mem_inf_fix.mp hu
        rw [hr₂U u huU] at huf
        have : r u = u := by
          conv_lhs => rw [← huf]
          simp
        rw [← hfixU]
        exact mem_inf_fix.mpr ⟨huU, this⟩
      have hx2r : (x * x) * r * (x * x)⁻¹ = (r * r₁)⁻¹ := by
        have e1 : (x * x) * r * (x * x)⁻¹ = x * (x * r * x⁻¹) * x⁻¹ := by group
        rw [e1, hxr, hxr₁]
      have hx2r₁ : (x * x) * r₁ * (x * x)⁻¹ = r := by
        have e1 : (x * x) * r₁ * (x * x)⁻¹ = x * (x * r₁ * x⁻¹) * x⁻¹ := by group
        have e2 : x * (r * r₁)⁻¹ * x⁻¹ = ((x * r * x⁻¹) * (x * r₁ * x⁻¹))⁻¹ := by group
        rw [e1, hxr₁, e2, hxr, hxr₁]
        group
      have hU₂ : U.map ((x * x : MulAut V) : V →* V) =
          (⊤ : Subgroup V).map (commHom (r * r₁)⁻¹) := by
        rw [map_map_commHom, hx2r]
      have hUle : U ≤ (⊤ : Subgroup V).map (commHom (r * r₁)⁻¹) := by
        rw [← map_commHom_eq_of_fix_eq_bot hV hUr₂ hfix₂]
        exact Subgroup.map_mono le_top
      have hUeq : U = (⊤ : Subgroup V).map (commHom (r * r₁)⁻¹) :=
        eq_of_le_of_rk_le hV hUle (by rw [← hU₂, rk_map_aut])
      have hrU : ∀ v ∈ U, r v = v := by
        intro v hv
        have hv' : v ∈ U.map ((x * x : MulAut V) : V →* V) := by rw [hU₂, ← hUeq]; exact hv
        obtain ⟨u, hu, rfl⟩ := hv'
        have key : r ((x * x) u) = (x * x) (r₁ u) := by
          rw [← hx2r₁]
          simp [MulAut.mul_apply]
        show r ((x * x) u) = (x * x) u
        rw [key, hr₁U u hu]
      apply hUne
      rw [eq_bot_iff, ← hfixU]
      intro u hu
      exact mem_inf_fix.mpr ⟨hu, hrU u hu⟩
    ·
      have hr₁U : ∀ u ∈ U, r₁ u = (r ^ i)⁻¹ u := by
        intro u hu
        have h1 : (r ^ i)⁻¹ u ∈ U := inv_mem_of_invariant (fun v hv =>
          pow_mem_of_invariant hUr i v hv) u hu
        have := hfixe _ h1
        rw [MulAut.mul_apply] at this
        simpa using this
      have hfix₁ : U ⊓ fixV (Subgroup.zpowers r₁) = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        obtain ⟨huU, huf⟩ := mem_inf_fix.mp hu
        rw [hr₁U u huU] at huf
        have h1 : (r ^ i) u = u := by
          conv_lhs => rw [← huf]
          simp
        have h2 := apply_eq_of_pow_apply_eq hp.out hrp hi0 hip h1
        rw [← hfixU]
        exact mem_inf_fix.mpr ⟨huU, h2⟩
      have hU₁ : U.map (x : V →* V) = (⊤ : Subgroup V).map (commHom r₁) := by
        rw [map_map_commHom, hxr]
      have hUle : U ≤ (⊤ : Subgroup V).map (commHom r₁) := by
        rw [← map_commHom_eq_of_fix_eq_bot hV hUr₁ hfix₁]
        exact Subgroup.map_mono le_top
      have hUeq : (⊤ : Subgroup V).map (commHom r₁) = U :=
        (eq_of_le_of_rk_le hV hUle (by rw [← hU₁, rk_map_aut])).symm
      set A := fixV (Subgroup.zpowers r) with hA
      have hAr₁ : ∀ u ∈ A, r₁ u ∈ A := fun u hu => mem_fix_of_comm hc.symm hu
      have hdecA := eq_inf_fix_sup_map hV hpodd hr₁p hAr₁
      have hdecV := eq_inf_fix_sup_map hV hpodd hrp (A := ⊤) (fun u _ => Subgroup.mem_top _)
      rw [top_inf_eq] at hdecV
      have hmapA : A.map (commHom r₁) ≤ U := by
        rw [← hUeq]; exact Subgroup.map_mono le_top
      have hA' : A ≤ (A ⊓ fixV (Subgroup.zpowers r₁)) ⊔ U := by
        conv_lhs => rw [hdecA]
        exact sup_le_sup_left hmapA _
      have htop : (⊤ : Subgroup V) ≤ (A ⊓ fixV (Subgroup.zpowers r₁)) ⊔ U :=
        hdecV.le.trans (sup_le hA' le_sup_right)
      have hfixV : ∀ v, (r₁ * r ^ i) v = v := by
        intro v
        have hv : v ∈ fixV (Subgroup.zpowers (r₁ * r ^ i)) := by
          refine (sup_le ?_ ?_ : (A ⊓ fixV (Subgroup.zpowers r₁)) ⊔ U ≤ _)
            (htop (Subgroup.mem_top v))
          · intro u hu
            rw [mem_fixV_zpowers_iff, MulAut.mul_apply]
            have h1 : (r ^ i) u = u := pow_apply_eq_self (mem_fixV_zpowers_iff.mp hu.1) i
            rw [h1]
            exact mem_fixV_zpowers_iff.mp hu.2
          · intro u hu
            exact mem_fixV_zpowers_iff.mpr (hfixe u hu)
        exact mem_fixV_zpowers_iff.mp hv
      have he := eq_one_of_forall hfixV
      apply hind (p - i)
      have h1 : r ^ (p - i) * r ^ i = 1 := by rw [← pow_add, Nat.sub_add_cancel hip.le, hrp]
      calc r₁ = r₁ * r ^ i * (r ^ i)⁻¹ := by group
        _ = (r ^ i)⁻¹ := by rw [he, one_mul]
        _ = r ^ (p - i) := (eq_inv_of_mul_eq_one_left h1).symm
  ·
    subst hp7
    have hrkU : rk U = 6 := by
      rcases hpU with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · exact h
    rcases hb with h2 | ⟨c, hc2, hc1, hcs, hcr, hcV⟩
    · omega
    ·
      have hcU : ∀ u ∈ U, c u ∈ U := by
        intro u hu
        rcases hcr with ⟨h1, -⟩ | ⟨h1, -⟩
        · have hcomm1 : c * r = r * c := by
            have := congrArg (· * c) h1
            simpa [mul_assoc] using this
          exact mem_map_commHom_of_comm hcomm1 hu
        · exact mem_map_commHom_of_inv h1 hu
      have hce : ∀ k : ℕ, c * (r₁ * r ^ k) * c⁻¹ = r₁ * r ^ k ∨
          c * (r₁ * r ^ k) * c⁻¹ = (r₁ * r ^ k)⁻¹ := by
        intro k
        have hck : ∀ g : MulAut V, c * g ^ k * c⁻¹ = (c * g * c⁻¹) ^ k := fun g => by
          rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
        have e : c * (r₁ * r ^ k) * c⁻¹ = (c * r₁ * c⁻¹) * (c * r ^ k * c⁻¹) := by group
        rcases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          rw [e, hck, h1, h2]
        · right
          rw [e, hck, h1, h2, inv_pow, mul_inv_rev]
          exact (Commute.inv_inv (Commute.pow_right (Commute.symm hc) k)).eq
      have hcL : ∀ k, ∀ u ∈ L k, c u ∈ L k := by
        intro k u hu
        obtain ⟨huU, huf⟩ := mem_inf_fix.mp hu
        refine Subgroup.mem_inf.mpr ⟨hcU u huU, ?_⟩
        have hfu : u ∈ fixV (Subgroup.zpowers (r₁ * r ^ k)) := mem_fixV_zpowers_iff.mpr huf
        have := (mem_fix_conj_iff (g := c) (e := r₁ * r ^ k)).mpr hfu
        rcases hce k with h | h
        · rwa [h] at this
        · rwa [h, fix_inv_iff] at this
      have hcr' : c * r * c⁻¹ = r := by
        rcases hcr with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact h1
        · exfalso
          have := rk_eq_two_mul_of_inverts hV (hLr i) (hcL i) (hLfix i) hc2 h1
          omega
      have hcrc : c * r = r * c := by
        have := congrArg (· * c) hcr'
        simpa [mul_assoc] using this
      have hcfix : ∀ k, rk (L k) = 3 → ∀ u ∈ L k, c u = u := by
        intro k hk
        have h1 := rk_map_add_rk_inf (L k) c
        have h2 := rk_mono (map_commHom_le_inf_fix hV (hcL k) hc2)
        set F := L k ⊓ fixV (Subgroup.zpowers c) with hF
        have hFr : ∀ u ∈ F, r u ∈ F := by
          intro u hu
          obtain ⟨huL, huc⟩ := mem_inf_fix.mp hu
          exact mem_inf_fix.mpr ⟨hLr k u huL, by
            have := congrArg (fun h : MulAut V => h u) hcrc
            simp only [MulAut.mul_apply] at this
            rw [this, huc]⟩
        have hFfix : F ⊓ fixV (Subgroup.zpowers r) = ⊥ :=
          inf_fix_le_of_le inf_le_left r (hLfix k)
        have hdF := dvd_two_pow_rk_sub_one hV hFr hrp hFfix
        have hFle : rk F ≤ 3 := hk ▸ rk_mono inf_le_left
        have hF3 : rk F = 3 := by
          rcases rk_of_dvd_seven hdF (by omega) with h | h | h <;> omega
        have hFeq : F = L k := eq_of_le_of_rk_le hV inf_le_left (by rw [hF3, hk])
        intro u hu
        rw [← hFeq] at hu
        exact (mem_inf_fix.mp hu).2
      have hcUfix : U ≤ fixV (Subgroup.zpowers c) := by
        rw [← hsup]
        refine sup_le (fun u hu => ?_) (fun u hu => ?_)
        · exact mem_fixV_zpowers_iff.mpr (hcfix i hi3 u hu)
        · exact mem_fixV_zpowers_iff.mpr (hcfix j hj3 u hu)
      have hCs : rk (U ⊓ fixV (Subgroup.zpowers s) : Subgroup V) = 3 := by omega
      have hsV3 : 3 ≤ rk ((⊤ : Subgroup V).map (commHom s)) := by omega
      have hst := rk_add_rkIdx (fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers c))
      have hsc : fixV (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers c) =
          fixV (Subgroup.zpowers s) :=
        eq_of_le_of_rk_le hV inf_le_left (by omega)
      have hsupV := rk_sup_add_rk_inf (fixV (Subgroup.zpowers s)) U
      rw [inf_comm, hCs, hrkU] at hsupV
      have htop : (⊤ : Subgroup V) ≤ fixV (Subgroup.zpowers s) ⊔ U := by
        have := eq_of_le_of_rk_le hV (le_top : fixV (Subgroup.zpowers s) ⊔ U ≤ ⊤)
          (by rw [rk_top]; omega)
        rw [this]
      apply hc1
      refine eq_one_of_forall fun v => ?_
      have hv := htop (Subgroup.mem_top v)
      have hle' : fixV (Subgroup.zpowers s) ⊔ U ≤ fixV (Subgroup.zpowers c) :=
        sup_le (hsc ▸ inf_le_right) hcUfix
      exact mem_fixV_zpowers_iff.mp (hle' hv)

end CFSG.Quasithin.H13.Q511

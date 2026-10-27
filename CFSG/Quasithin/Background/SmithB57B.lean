module

public import CFSG.Quasithin.Background.SmithB57A
public import CFSG.Quasithin.Background.FFC6L
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace SmithB57

open CFSG.Timmesfeld FFC.B59

section Coprime

variable {V : Type} [CommGroup V]

@[expose] def cs (s : MulAut V) : Subgroup V := (commMap s).range

theorem cs_inv (s : MulAut V) : ∀ w ∈ cs s, s w ∈ cs s := by
  rintro _ ⟨v, rfl⟩
  refine ⟨s v, ?_⟩
  rw [commMap_apply, commMap_apply, map_mul, map_inv]

theorem cs_inv_of_comm {s x : MulAut V} (hx : x * s = s * x) : ∀ w ∈ cs s, x w ∈ cs s := by
  rintro _ ⟨v, rfl⟩
  refine ⟨x v, ?_⟩
  have h : x (s v) = s (x v) := by
    rw [← MulAut.mul_apply, hx, MulAut.mul_apply]
  rw [commMap_apply, commMap_apply, map_mul, map_inv, h]

theorem pow_apply_of_fix (s : MulAut V) (v : V) (hw : s (s v * v⁻¹) = s v * v⁻¹) (k : ℕ) :
    (s ^ k) v = v * (s v * v⁻¹) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hw, pow_succ]
    calc s v * (s v * v⁻¹) ^ k = (v * v⁻¹) * (s v * (s v * v⁻¹) ^ k) := by
          rw [mul_inv_cancel, one_mul]
      _ = v * ((s v * v⁻¹) ^ k * (s v * v⁻¹)) := by
          simp only [mul_comm, mul_assoc]

theorem cs_inf_fix (hV : ∀ v : V, v ^ 2 = 1) {s : MulAut V} {r : ℕ} (hs : s ^ r = 1)
    (hr : Odd r) : cs s ⊓ fixV (Subgroup.zpowers s) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨⟨v, rfl⟩, hw⟩
  rw [commMap_apply] at hw ⊢
  have hfix : s (s v * v⁻¹) = s v * v⁻¹ := mem_fixV_zpowers.mp hw
  have h1 := pow_apply_of_fix s v hfix r
  rw [hs, MulAut.one_apply, left_eq_mul] at h1
  obtain ⟨k, hk⟩ := hr
  rw [Subgroup.mem_bot]
  have h2 : (s v * v⁻¹) ^ r = s v * v⁻¹ := by
    rw [hk, pow_succ, pow_mul, hV, one_pow, one_mul]
  rw [← h2]
  exact h1

theorem card_cs_mul (s : MulAut V) :
    Nat.card (cs s) * Nat.card (fixV (Subgroup.zpowers s)) = Nat.card V := by
  rw [mul_comm, ← ker_commMap]
  exact Subgroup.card_ker_mul_card_range (commMap s)

variable [Finite V]

theorem rk_cs_add (s : MulAut V) :
    rk (cs s) + rk (fixV (Subgroup.zpowers s)) = rk V := by
  unfold rk
  rw [← padicValNat.mul (card_subgroup_pos _).ne' (card_subgroup_pos _).ne', card_cs_mul]

omit [Finite V] in
theorem card_map_mul (s : MulAut V) (N : Subgroup V) :
    Nat.card (N.map (commMap s)) * Nat.card ↥(N ⊓ fixV (Subgroup.zpowers s)) = Nat.card N := by
  set φ : ↥N →* V := (commMap s).comp N.subtype with hφ
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hrange : φ.range = N.map (commMap s) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card φ.ker = Nat.card ↥(N ⊓ fixV (Subgroup.zpowers s)) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    · have hx : commMap s (x.1 : V) = 1 := x.2
      rw [← ker_commMap]
      exact hx
    · have hx : (x.1 : V) ∈ (commMap s).ker := by rw [ker_commMap]; exact x.2.2
      exact hx
  rw [hrange, hker, mul_comm] at h1
  exact h1

theorem rk_map_add (s : MulAut V) (N : Subgroup V) :
    rk (N.map (commMap s)) + rk ↥(N ⊓ fixV (Subgroup.zpowers s)) = rk N := by
  unfold rk
  rw [← padicValNat.mul (card_subgroup_pos _).ne' (card_subgroup_pos _).ne', card_map_mul]

theorem mem_map_of_mem_cs (hV : ∀ v : V, v ^ 2 = 1) {s : MulAut V} {r : ℕ} (hs : s ^ r = 1)
    (hr : Odd r) {W : Subgroup V} (hW : ∀ w ∈ W, s w ∈ W) {w : V} (hwW : w ∈ W)
    (hwc : w ∈ cs s) : w ∈ W.map (commMap s) := by
  set R := W.map (commMap s) with hR
  set C := W ⊓ fixV (Subgroup.zpowers s) with hC
  have hRW : R ≤ W := by
    rintro _ ⟨v, hv, rfl⟩
    exact W.mul_mem (hW v hv) (W.inv_mem hv)
  have hRc : R ≤ cs s := by
    rintro _ ⟨v, -, rfl⟩
    exact ⟨v, rfl⟩
  have hRC : R ⊓ C = ⊥ := by
    rw [eq_bot_iff, ← cs_inf_fix hV hs hr]
    exact fun x hx => ⟨hRc hx.1, hx.2.2⟩
  have hsup : R ⊔ C = W := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hRW inf_le_left) ?_
    have h1 := card_sup_mul_card_inf R C
    rw [hRC, Subgroup.card_bot, mul_one, card_map_mul s W] at h1
    rw [h1]
  have hw' : w ∈ R ⊔ C := hsup ▸ hwW
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw'
  have hc1 : c = 1 := by
    have hcc : c ∈ cs s ⊓ fixV (Subgroup.zpowers s) := by
      refine ⟨?_, hc.2⟩
      have : c = a⁻¹ * (a * c) := by group
      rw [this]
      exact (cs s).mul_mem ((cs s).inv_mem (hRc ha)) hwc
    rw [cs_inf_fix hV hs hr, Subgroup.mem_bot] at hcc
    exact hcc
  rw [hc1, mul_one]
  exact ha

theorem three_mul_dvd_rk (hV : ∀ v : V, v ^ 2 = 1) {m r : ℕ} (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) {s : MulAut V} (hs : s ^ r = 1) {N : Subgroup V}
    (hN : ∀ v ∈ N, s v ∈ N) (hNf : N ⊓ fixV (Subgroup.zpowers s) = ⊥) : 3 * m ∣ rk N := by
  have : Fact r.Prime := ⟨hr.prime⟩
  let f : N → N := fun v => ⟨s v, hN v v.2⟩
  have hit : ∀ (n : ℕ) (v : N), ((f^[n] v : N) : V) = (s ^ n) (v : V) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply', pow_succ', MulAut.mul_apply, ← ih]
  have hmod := card_modEq_card_fix (r := r) f (fun v => by
    apply Subtype.ext
    rw [hit, hs, MulAut.one_apply])
  have hone : Nat.card {x : N // f x = x} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, Subtype.ext (by simp [f])⟩, ?_⟩
    rintro ⟨v, hv⟩
    have h1 : s (v : V) = v := congrArg Subtype.val hv
    have h2 : (v : V) ∈ N ⊓ fixV (Subgroup.zpowers s) := ⟨v.2, mem_fixV_zpowers.mpr h1⟩
    rw [hNf, Subgroup.mem_bot] at h2
    apply Subtype.ext
    exact Subtype.ext h2
  rw [hone, card_eq_two_pow hV N] at hmod
  have h1 : r ∣ 2 ^ rk N - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm
  exact (hr.dvd_sub_one_iff (by omega) _).mp h1

theorem three_mul_dvd_rk_of_le_cs (hV : ∀ v : V, v ^ 2 = 1) {m r : ℕ} (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) {s : MulAut V} (hs : s ^ r = 1) {N : Subgroup V}
    (hN : ∀ v ∈ N, s v ∈ N) (hNc : N ≤ cs s) : 3 * m ∣ rk N := by
  have hodd : Odd r := hr.prime.odd_of_ne_two (ppd_ne_two hm hr)
  refine three_mul_dvd_rk hV hm hr hs hN ?_
  rw [eq_bot_iff, ← cs_inf_fix hV hs hodd]
  exact fun x hx => ⟨hNc hx.1, hx.2⟩

end Coprime

section Involution

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem map_le_fix_of_sq (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V} (hx : x * x = 1)
    {N : Subgroup V} (hN : ∀ v ∈ N, x v ∈ N) :
    N.map (commMap x) ≤ N ⊓ fixV (Subgroup.zpowers x) := by
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨N.mul_mem (hN v hv) (N.inv_mem hv), mem_fixV_zpowers.mpr ?_⟩
  have hxx : x (x v) = v := by rw [← MulAut.mul_apply, hx, MulAut.one_apply]
  rw [commMap_apply, map_mul, map_inv, hxx]
  have h1 : (x v)⁻¹ = x v := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hV]
  have h2 : v⁻¹ = v := by rw [inv_eq_iff_mul_eq_one, ← sq, hV]
  rw [h1, h2, mul_comm]

omit [Finite V] in
theorem fix_inv_of_comm {s x : MulAut V} (hsx : x * s = s * x) {N : Subgroup V}
    (hN : ∀ v ∈ N, s v ∈ N) : ∀ v ∈ N ⊓ fixV (Subgroup.zpowers x),
      s v ∈ N ⊓ fixV (Subgroup.zpowers x) := by
  rintro v ⟨hvN, hvx⟩
  refine ⟨hN v hvN, mem_fixV_zpowers.mpr ?_⟩
  have h := mem_fixV_zpowers.mp hvx
  rw [← MulAut.mul_apply, hsx, MulAut.mul_apply, h]

theorem fix_ne_bot (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V} (hx : x * x = 1) {N : Subgroup V}
    (hN : ∀ v ∈ N, x v ∈ N) (hN1 : N ≠ ⊥) : N ⊓ fixV (Subgroup.zpowers x) ≠ ⊥ := by
  intro h
  have hmap : N.map (commMap x) = ⊥ := le_bot_iff.mp (h ▸ map_le_fix_of_sq hV hx hN)
  have h1 := rk_map_add x N
  rw [hmap, h, rk_bot, add_zero] at h1
  exact hN1 ((rk_eq_zero_iff hV).mp h1.symm)

variable {m r : ℕ}

theorem fix_of_comm_square (hV : ∀ v : V, v ^ 2 = 1) (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) {s : MulAut V} (hs : s ^ r = 1)
    (hM : rk (cs s) ≤ 6 * m) {x₁ x₂ x₃ : MulAut V} (hc₁ : x₁ * s = s * x₁)
    (hc₂ : x₂ * s = s * x₂) (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1) (h₃ : x₃ * x₃ = 1)
    (h123 : x₁ * x₂ * x₁ * x₂ = x₃) (h31 : x₃ * x₁ = x₁ * x₃) (h32 : x₃ * x₂ = x₂ * x₃) :
    ∀ v ∈ cs s, x₃ v = v := by
  have hc₃ : x₃ * s = s * x₃ := by
    rw [← h123]
    calc x₁ * x₂ * x₁ * x₂ * s = x₁ * x₂ * x₁ * (x₂ * s) := by group
      _ = x₁ * x₂ * x₁ * (s * x₂) := by rw [hc₂]
      _ = x₁ * x₂ * (x₁ * s) * x₂ := by group
      _ = x₁ * x₂ * (s * x₁) * x₂ := by rw [hc₁]
      _ = x₁ * (x₂ * s) * x₁ * x₂ := by group
      _ = x₁ * (s * x₂) * x₁ * x₂ := by rw [hc₂]
      _ = (x₁ * s) * x₂ * x₁ * x₂ := by group
      _ = (s * x₁) * x₂ * x₁ * x₂ := by rw [hc₁]
      _ = s * (x₁ * x₂ * x₁ * x₂) := by group
  set M := cs s with hMdef
  have hMs : ∀ v ∈ M, s v ∈ M := cs_inv s
  have hdvd : ∀ N : Subgroup V, (∀ v ∈ N, s v ∈ N) → N ≤ M → 3 * m ∣ rk N :=
    fun N hN hNM => three_mul_dvd_rk_of_le_cs hV hm hr hs hN hNM
  have hMx : ∀ {x : MulAut V}, x * s = s * x → ∀ v ∈ M, x v ∈ M :=
    fun hx => cs_inv_of_comm hx
  have hfixrk : ∀ {x : MulAut V}, x * s = s * x → x * x = 1 → ∀ N : Subgroup V,
      (∀ v ∈ N, s v ∈ N) → (∀ v ∈ N, x v ∈ N) → N ≤ M → N ≠ ⊥ → rk N ≤ 3 * m →
      ∀ v ∈ N, x v = v := by
    intro x hx hxx N hNs hNx hNM hN1 hNr v hv
    have hF := fix_ne_bot hV hxx hNx hN1
    have hFd := hdvd _ (fix_inv_of_comm hx hNs) (inf_le_left.trans hNM)
    have hFpos : 0 < rk ↥(N ⊓ fixV (Subgroup.zpowers x)) := by
      rw [Nat.pos_iff_ne_zero, Ne, rk_eq_zero_iff hV]
      exact hF
    have hFN : N ⊓ fixV (Subgroup.zpowers x) = N := by
      refine eq_of_le_of_rk_le hV inf_le_left ?_
      obtain ⟨j, hj⟩ := hFd
      have : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, mul_zero] at hj
          omega
        · exact h0
      calc rk N ≤ 3 * m := hNr
        _ ≤ 3 * m * j := Nat.le_mul_of_pos_right _ this
        _ = _ := hj.symm
    have : v ∈ N ⊓ fixV (Subgroup.zpowers x) := by rw [hFN]; exact hv
    exact mem_fixV_zpowers.mp this.2
  by_cases hMb : M = ⊥
  · intro v hv
    rw [hMb, Subgroup.mem_bot] at hv
    rw [hv, map_one]
  obtain ⟨j, hj⟩ := hdvd M hMs le_rfl
  have hj12 : j = 1 ∨ j = 2 := by
    have hpos : 0 < rk M := by
      rw [Nat.pos_iff_ne_zero, Ne, rk_eq_zero_iff hV]
      exact hMb
    rcases Nat.lt_or_ge j 3 with h | h
    · interval_cases j
      · rw [hj, mul_zero] at hpos; omega
      · left; rfl
      · right; rfl
    · have : 3 * m * 3 ≤ 3 * m * j := Nat.mul_le_mul_left _ h
      omega
  rcases hj12 with rfl | rfl
  ·
    exact hfixrk hc₃ h₃ M hMs (hMx hc₃) le_rfl hMb (by rw [hj, mul_one])
  ·
    have hx₃M := hMx hc₃
    by_cases hx₁ : ∀ v ∈ M, x₁ v = v
    · intro v hv
      rw [← h123]
      simp only [MulAut.mul_apply]
      rw [hx₁ _ (hMx hc₂ v hv), hx₁ _ (hMx hc₂ _ (hMx hc₂ v hv))]
      rw [← MulAut.mul_apply, h₂, MulAut.one_apply]
    by_cases hx₂ : ∀ v ∈ M, x₂ v = v
    · intro v hv
      rw [← h123]
      simp only [MulAut.mul_apply]
      rw [hx₂ v hv, hx₂ _ (hMx hc₁ v hv)]
      rw [← MulAut.mul_apply, h₁, MulAut.one_apply]
    have hH : ∀ {x : MulAut V}, x * s = s * x → x * x = 1 → ¬ (∀ v ∈ M, x v = v) →
        rk ↥(M ⊓ fixV (Subgroup.zpowers x)) = 3 * m ∧
          M.map (commMap x) = M ⊓ fixV (Subgroup.zpowers x) := by
      intro x hx hxx hnt
      have hsum := rk_map_add x M
      have hle := map_le_fix_of_sq hV hxx (hMx hx)
      have hd1 := hdvd _ (fix_inv_of_comm hx hMs) inf_le_left
      have hd2 : 3 * m ∣ rk (M.map (commMap x)) := by
        refine hdvd _ ?_ (hle.trans inf_le_left)
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨s v, hMs v hv, ?_⟩
        have h' : x (s v) = s (x v) := by rw [← MulAut.mul_apply, hx, MulAut.mul_apply]
        rw [commMap_apply, commMap_apply, map_mul, map_inv, h']
      have hne : M ⊓ fixV (Subgroup.zpowers x) ≠ M := by
        intro h
        apply hnt
        intro v hv
        have : v ∈ M ⊓ fixV (Subgroup.zpowers x) := by rw [h]; exact hv
        exact mem_fixV_zpowers.mp this.2
      have hlt : rk ↥(M ⊓ fixV (Subgroup.zpowers x)) < rk M := by
        by_contra hge
        push Not at hge
        exact hne (eq_of_le_of_rk_le hV inf_le_left hge)
      have hrk_le := rk_mono hle
      obtain ⟨a, ha⟩ := hd1
      obtain ⟨b, hb⟩ := hd2
      rw [hj] at hsum hlt
      rw [ha] at hsum hlt hrk_le
      rw [hb] at hsum hrk_le
      have hab : a + b = 2 := by
        have : 3 * m * (b + a) = 3 * m * 2 := by rw [mul_add, hsum]
        have := Nat.eq_of_mul_eq_mul_left (by omega) this
        omega
      have hba : b ≤ a := Nat.le_of_mul_le_mul_left hrk_le (by omega)
      have ha2 : a < 2 := by
        have := Nat.lt_of_mul_lt_mul_left hlt
        exact this
      have ha1 : a = 1 := by omega
      have hb1 : b = 1 := by omega
      refine ⟨by rw [ha, ha1, mul_one], ?_⟩
      exact eq_of_le_of_rk_le hV hle (by rw [ha, hb, ha1, hb1])
    obtain ⟨hr₁, hm₁⟩ := hH hc₁ h₁ hx₁
    obtain ⟨hr₂, hm₂⟩ := hH hc₂ h₂ hx₂
    set H₁ := M ⊓ fixV (Subgroup.zpowers x₁) with hH₁
    set H₂ := M ⊓ fixV (Subgroup.zpowers x₂) with hH₂
    have hHs₁ : ∀ v ∈ H₁, s v ∈ H₁ := fix_inv_of_comm hc₁ hMs
    have hHs₂ : ∀ v ∈ H₂, s v ∈ H₂ := fix_inv_of_comm hc₂ hMs
    have hI := hdvd (H₁ ⊓ H₂) (fun v hv => ⟨hHs₁ v hv.1, hHs₂ v hv.2⟩)
      (inf_le_left.trans inf_le_left)
    have hIle : rk ↥(H₁ ⊓ H₂) ≤ 3 * m := hr₁ ▸ rk_mono inf_le_left
    obtain ⟨i, hi⟩ := hI
    have hi01 : i = 0 ∨ i = 1 := by
      have : 3 * m * i ≤ 3 * m * 1 := by rw [← hi, mul_one]; exact hIle
      have := Nat.le_of_mul_le_mul_left this (by omega)
      omega
    rcases hi01 with rfl | rfl
    ·
      have hIb : H₁ ⊓ H₂ = ⊥ := (rk_eq_zero_iff hV).mp (by rw [hi, mul_zero])
      have hx₃H : ∀ {x : MulAut V}, x * s = s * x → x * x = 1 → x₃ * x = x * x₃ →
          ¬ (∀ v ∈ M, x v = v) → ∀ v ∈ M ⊓ fixV (Subgroup.zpowers x), x₃ v = v := by
        intro x hx hxx h3x hnt
        obtain ⟨hrx, -⟩ := hH hx hxx hnt
        refine hfixrk hc₃ h₃ _ (fix_inv_of_comm hx hMs) ?_ inf_le_left ?_ hrx.le
        · rintro v ⟨hvM, hvx⟩
          refine ⟨hx₃M v hvM, mem_fixV_zpowers.mpr ?_⟩
          have := mem_fixV_zpowers.mp hvx
          rw [← MulAut.mul_apply, ← h3x, MulAut.mul_apply, this]
        · intro h
          have := rk_bot (G := V)
          rw [← h, hrx] at this
          omega
      have hsup : H₁ ⊔ H₂ = M := by
        refine eq_of_le_of_rk_le hV (sup_le inf_le_left inf_le_left) ?_
        have := rk_sup_add_rk_inf H₁ H₂
        rw [hIb, rk_bot, add_zero, hr₁, hr₂] at this
        rw [this, hj]
        ring_nf
        omega
      intro v hv
      rw [← hsup] at hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
      rw [map_mul, hx₃H hc₁ h₁ h31 hx₁ a ha, hx₃H hc₂ h₂ h32 hx₂ b hb]
    ·
      have heq : H₁ = H₂ := by
        have h1 : H₁ ⊓ H₂ = H₁ := eq_of_le_of_rk_le hV inf_le_left (by rw [hr₁, hi, mul_one])
        have h2 : H₁ ⊓ H₂ = H₂ := eq_of_le_of_rk_le hV inf_le_right (by rw [hr₂, hi, mul_one])
        rw [← h1, h2]
      have hq₁ : ∀ v ∈ M, x₁ v * v⁻¹ ∈ H₂ := by
        intro v hv
        rw [← heq, ← hm₁]
        exact ⟨v, hv, rfl⟩
      have hq₂ : ∀ v ∈ M, x₂ v * v⁻¹ ∈ H₂ := by
        intro v hv
        rw [← hm₂]
        exact ⟨v, hv, rfl⟩
      have hf₁ : ∀ h ∈ H₂, x₁ h = h := by
        intro h hh
        rw [← heq] at hh
        exact mem_fixV_zpowers.mp hh.2
      have hf₂ : ∀ h ∈ H₂, x₂ h = h := fun h hh => mem_fixV_zpowers.mp hh.2
      intro v hv
      rw [← h123]
      simp only [MulAut.mul_apply]
      set a₂ := x₂ v * v⁻¹ with ha₂
      have hx₂v : x₂ v = v * a₂ := by rw [ha₂, mul_comm v, inv_mul_cancel_right]
      set a₁ := x₁ v * v⁻¹ with ha₁
      have hx₁v : x₁ v = v * a₁ := by rw [ha₁, mul_comm v, inv_mul_cancel_right]
      have ha₂H := hq₂ v hv
      have ha₁H := hq₁ v hv
      have hsq : ∀ a : V, a * a = 1 := fun a => by rw [← sq, hV]
      have e1 : x₁ (x₂ v) = v * a₁ * a₂ := by rw [hx₂v, map_mul, hx₁v, hf₁ a₂ ha₂H]
      have e2 : x₂ (x₁ (x₂ v)) = v * a₁ := by
        rw [e1, map_mul, map_mul, hx₂v, hf₂ a₁ ha₁H, hf₂ a₂ ha₂H]
        calc v * a₂ * a₁ * a₂ = v * a₁ * (a₂ * a₂) := by
              simp only [mul_comm, mul_left_comm, mul_assoc]
          _ = v * a₁ := by rw [hsq, mul_one]
      rw [e2, map_mul, hx₁v, hf₁ a₁ ha₁H, mul_assoc, hsq, mul_one]

end Involution

section NormalClosure

variable {V : Type} [CommGroup V]

theorem commV_le_of_cs_le {L : Subgroup (MulAut V)} (hLq : CFSG.Open.IsQuasisimple ↥L)
    {s : MulAut V} (hsL : s ∈ L) (hsz : ∃ l ∈ L, l * s ≠ s * l) {Y : Subgroup V}
    (hY : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) (hsY : cs s ≤ Y) : commV L ≤ Y := by
  set L' : Subgroup ↥L := (B19.commLeSub Y).subgroupOf L with hL'
  have hL'n : L'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hL', Subgroup.mem_subgroupOf] at hx ⊢
    intro v
    have h1 : ((g * x * g⁻¹ : ↥L) : MulAut V) v * v⁻¹ =
        (g : MulAut V) ((x : MulAut V) ((g : MulAut V)⁻¹ v) * ((g : MulAut V)⁻¹ v)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, map_mul, map_inv,
        MulAut.apply_inv_self]
    rw [h1]
    exact hY _ g.2 _ (hx _)
  have hsL' : (⟨s, hsL⟩ : ↥L) ∈ L' := by
    rw [hL', Subgroup.mem_subgroupOf]
    intro v
    exact hsY ⟨v, rfl⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hLq L' with h | h
  · exfalso
    obtain ⟨l, hl, hls⟩ := hsz
    have hc := Subgroup.mem_center_iff.mp (h hsL') ⟨l, hl⟩
    exact hls (congrArg Subtype.val hc)
  · rw [B19.commV_le_iff]
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ L' := h ▸ Subgroup.mem_top _
    rw [hL', Subgroup.mem_subgroupOf] at this
    exact this

end NormalClosure

end SmithB57

end CFSG.Quasithin

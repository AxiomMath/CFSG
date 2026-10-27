module

public import CFSG.RankThree.S4Free.StellmacherOffender
public import CFSG.Quasithin.Background.D2Fitting
import CFSG.Quasithin.Background.B1MoreNineA
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

theorem mRel_add_rk (H K : Subgroup V) : mRel H K + rk ↥(H ⊓ K) = rk K := by
  unfold mRel rk
  rw [← padicValNat.mul (relIndex_ne_zero_of_finite H K) Nat.card_pos.ne',
    Subgroup.relIndex_mul_card]

theorem apply_mem_of_mem_stabSub {W : Subgroup V} {y : MulAut V} (hy : y ∈ stabSub W) {w : V}
    (hw : w ∈ W) : y w ∈ W :=
  (hy w).mpr hw

theorem five_le_card {W : Subgroup V} {a b c d e : V} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W)
    (hd : d ∈ W) (he : e ∈ W) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    5 ≤ Nat.card W := by
  classical
  have : Fintype W := Fintype.ofFinite W
  set s : Finset V := {a, b, c, d, e} with hs
  have hcard : s.card = 5 := by
    rw [hs, Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Finset.card_insert_of_notMem (by simp [hcd, hce]),
      Finset.card_insert_of_notMem (by simp [hde]), Finset.card_singleton]
  have hsub : s ⊆ (W : Set V).toFinset := by
    intro x hx
    rw [Set.mem_toFinset, SetLike.mem_coe]
    simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h := Finset.card_le_card hsub
  rw [hcard, Set.toFinset_card] at h
  rw [Nat.card_eq_fintype_card]
  convert h using 1

theorem two_mul_rk_fixV_inf_le (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} {a y : MulAut V}
    (hay : a * y * a⁻¹ = y⁻¹) (hodd : Odd (orderOf y)) (ha : a ∈ stabSub W)
    (hy : y ∈ stabSub W) (hfpf : ∀ w ∈ W, y w = w → w = 1) :
    2 * rk ↥(fixV (Subgroup.zpowers a) ⊓ W) ≤ rk W := by
  obtain ⟨k, hk⟩ := hodd
  set s := y ^ (k + 1) with hsdef
  have hs2 : s * s = y := by
    rw [hsdef, ← pow_add, show k + 1 + (k + 1) = orderOf y + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have has : a * s * a⁻¹ = s⁻¹ := by
    rw [hsdef, ← conj_pow, hay, inv_pow]
  have hkey : s⁻¹ * a * s = y⁻¹ * a := by
    have h1 : a * s = s⁻¹ * a := by
      calc a * s = a * s * a⁻¹ * a := by group
        _ = s⁻¹ * a := by rw [has]
    calc s⁻¹ * a * s = s⁻¹ * (a * s) := by group
      _ = s⁻¹ * (s⁻¹ * a) := by rw [h1]
      _ = (s * s)⁻¹ * a := by group
      _ = y⁻¹ * a := by rw [hs2]
  have hsW : s⁻¹ ∈ stabSub W := (stabSub W).inv_mem ((stabSub W).pow_mem hy (k + 1))
  set C := fixV (Subgroup.zpowers a) ⊓ W with hC
  set C' := C.map (s⁻¹ : MulAut V).toMonoidHom with hC'
  have hCW : C ≤ W := inf_le_right
  have hC'W : C' ≤ W := by
    rintro _ ⟨u, hu, rfl⟩
    exact apply_mem_of_mem_stabSub hsW (hCW hu)
  have hcard' : Nat.card C' = Nat.card C :=
    Subgroup.card_map_of_injective (s⁻¹ : MulAut V).injective
  have hinf : C ⊓ C' = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvC, u, hu, rfl⟩
    rw [Subgroup.mem_bot]
    have hau : a u = u := hu.1 a (Subgroup.mem_zpowers a)
    have hav : a (s⁻¹ u) = s⁻¹ u := hvC.1 a (Subgroup.mem_zpowers a)
    have h1 : (s⁻¹ * a * s) ((s⁻¹ : MulAut V) u) = (s⁻¹ : MulAut V) u := by
      simp only [MulAut.mul_apply]
      rw [show s ((s⁻¹ : MulAut V) u) = u by simp, hau]
    rw [hkey, MulAut.mul_apply, hav] at h1
    have h2 : y ((s⁻¹ : MulAut V) u) = (s⁻¹ : MulAut V) u := by
      have h3 := congrArg y h1
      simpa using h3.symm
    exact hfpf _ (hCW hvC) h2
  have hsup := card_sup_mul_card_inf C C'
  rw [hinf, Subgroup.card_bot, mul_one, hcard'] at hsup
  have hle : Nat.card ↥(C ⊔ C') ≤ Nat.card W := Subgroup.card_le_of_le (sup_le hCW hC'W)
  rw [hsup, card_eq_two_pow hV C, card_eq_two_pow hV W, ← pow_add] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  omega

theorem three_dvd_orderOf_of_card_four (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V}
    (hW : Nat.card W = 4) {y : MulAut V} (hy : y ∈ stabSub W) (hodd : Odd (orderOf y))
    (hfpf : ∀ w ∈ W, y w = w → w = 1) : 3 ∣ orderOf y := by
  have hfpf2 : ∀ w ∈ W, y (y w) = w → w = 1 := by
    intro w hw h2
    apply hfpf w hw
    obtain ⟨k, hk⟩ := hodd
    have hyy : (y ^ 2) w = w := by rw [pow_two, MulAut.mul_apply, h2]
    have hpow : ∀ n : ℕ, (y ^ (2 * n)) w = w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, MulAut.mul_apply, hyy, ih]
    have := hpow (k + 1)
    rwa [show 2 * (k + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
      at this
  have hcube : ∀ u ∈ W, (y ^ 3) u = u := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1, map_one]
    set v := y u with hv
    set w := y v with hw
    have hvW : v ∈ W := apply_mem_of_mem_stabSub hy hu
    have hwW : w ∈ W := apply_mem_of_mem_stabSub hy hvW
    have hv1 : v ≠ 1 := fun h => hu1 (by rw [← map_one y] at h; exact y.injective h)
    have hw1 : w ≠ 1 := fun h => hv1 (by rw [← map_one y] at h; exact y.injective h)
    have huv : u ≠ v := fun h => hu1 (hfpf u hu h.symm)
    have hvw : v ≠ w := fun h => hv1 (hfpf v hvW h.symm)
    have huw : u ≠ w := fun h => hu1 (hfpf2 u hu h.symm)
    have hprod : u * v = w := by
      by_contra hne
      have hmem : u * v ∈ W := W.mul_mem hu hvW
      have h1 : u * v ≠ 1 := by
        intro h
        apply huv
        have : u = v⁻¹ := eq_inv_of_mul_eq_one_left h
        rw [this, inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)]
      have h2 : u * v ≠ u := fun h => hv1 (by simpa using h)
      have h3 : u * v ≠ v := fun h => hu1 (by simpa using h)
      have := five_le_card W.one_mem hu hvW hwW hmem (Ne.symm hu1) (Ne.symm hv1) (Ne.symm hw1)
        (Ne.symm h1) huv huw (Ne.symm h2) hvw (Ne.symm h3) (Ne.symm hne)
      omega
    have h4 : y w = v * w := by
      conv_lhs => rw [← hprod]
      rw [map_mul]
    have hv2 : v * v = 1 := by rw [← pow_two]; exact hV v
    calc (y ^ 3) u = y w := by
          rw [show (3 : ℕ) = 1 + 1 + 1 by rfl, pow_succ, pow_succ, pow_one]
          simp [hv, hw]
      _ = v * w := h4
      _ = v * (u * v) := by rw [hprod]
      _ = u := by rw [mul_comm u v, ← mul_assoc, hv2, one_mul]
  by_contra h3
  have hcop : Nat.Coprime 3 (orderOf y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ W, u ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : W = ⊥ := eq_bot_iff.mpr fun w hw => Subgroup.mem_bot.mpr (hall w hw)
    rw [hbot, Subgroup.card_bot] at hW
    norm_num at hW
  obtain ⟨j, hyj⟩ := exists_pow_eq_self_of_coprime hcop
  have hfix : ∀ n : ℕ, ((y ^ 3) ^ n) u = u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hcube u hu, ih]
  exact hu1 (hfpf u hu (by rw [← hyj]; exact hfix j))

theorem mem_stabSub_commSub {Y : Subgroup V} {Z : Subgroup (MulAut V)} {g : MulAut V}
    (hgY : g ∈ stabSub Y) (hgZ : g ∈ Subgroup.normalizer (Z : Set (MulAut V))) :
    g ∈ stabSub (commSub Y Z) := by
  have key : ∀ h : MulAut V, h ∈ stabSub Y → h ∈ Subgroup.normalizer (Z : Set (MulAut V)) →
      ∀ u ∈ commSub Y Z, h u ∈ commSub Y Z := by
    intro h hhY hhZ u hu
    have hle : commSub Y Z ≤ (commSub Y Z).comap h.toMonoidHom := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      show h (x w * w⁻¹) ∈ commSub Y Z
      have hx' : h * x * h⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hhZ x).mp hx
      have hw' : h w ∈ Y := apply_mem_of_mem_stabSub hhY hw
      have he : h (x w * w⁻¹) = (h * x * h⁻¹) (h w) * (h w)⁻¹ := by
        simp [MulAut.mul_apply]
      rw [he]
      exact Subgroup.subset_closure ⟨_, hx', _, hw', rfl⟩
    exact hle hu
  intro u
  constructor
  · intro hu
    have h1 := key g⁻¹ ((stabSub Y).inv_mem hgY) (inv_mem hgZ) _ hu
    simpa using h1
  · exact key g hgY hgZ u

theorem two_le_mRel_or_three_dvd (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup V} {a y : MulAut V}
    (ha2 : a ^ 2 = 1) (hay : a * y * a⁻¹ = y⁻¹) (hodd : Odd (orderOf y))
    (ha : a ∈ stabSub Y) (hy : y ∈ stabSub Y) (hnt : ¬ Y ≤ fixV (Subgroup.zpowers y)) :
    2 ≤ mRel (fixV (Subgroup.zpowers a)) Y ∨ 3 ∣ orderOf y := by
  set Z := Subgroup.zpowers y with hZ
  have hZodd : Odd (Nat.card Z) := by rw [hZ, Nat.card_zpowers]; exact hodd
  have hZY : ∀ z ∈ Z, ∀ m ∈ Y, z m ∈ Y := fun z hz m hm =>
    apply_mem_of_mem_stabSub ((Subgroup.zpowers_le.mpr hy) hz) hm
  obtain ⟨hsup, hinf⟩ := B1.coprime_decomp hV hZodd hZY
  set Y' := commSub Y Z with hY'
  have hY'Y : Y' ≤ Y := commSub_le_of_invariant hZY
  have hfpf : ∀ w ∈ Y', y w = w → w = 1 := by
    intro w hw hyw
    have hwfix : w ∈ fixV Z := by
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hall : ∀ n : ℕ, (y ^ n) w = w := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hyw, ih]
      rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast]
        exact hall n
      · rw [zpow_neg, zpow_natCast]
        exact (MulEquiv.symm_apply_eq _).mpr (hall n).symm
    have hmem : w ∈ (Y ⊓ fixV Z) ⊓ Y' := ⟨⟨hY'Y hw, hwfix⟩, hw⟩
    rw [hinf] at hmem
    exact hmem
  have hne : Y' ≠ ⊥ := by
    intro hbot
    rw [hbot, sup_bot_eq] at hsup
    exact hnt (hsup ▸ inf_le_right)
  have hyZ : y ∈ Subgroup.normalizer (Z : Set (MulAut V)) :=
    Subgroup.le_normalizer (Subgroup.mem_zpowers y)
  have haZ : a ∈ Subgroup.normalizer (Z : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hZ, MonoidHom.map_zpowers]
    change Subgroup.zpowers (a * y * a⁻¹) = Subgroup.zpowers y
    rw [hay, Subgroup.zpowers_inv]
  have ha' : a ∈ stabSub Y' := mem_stabSub_commSub ha haZ
  have hy' : y ∈ stabSub Y' := mem_stabSub_commSub hy hyZ
  have hdih := two_mul_rk_fixV_inf_le hV hay hodd ha' hy' hfpf
  have ha2grp : IsPGroup 2 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ha2) with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      subst h
      have h1 : y = y⁻¹ := by simpa using hay
      have hy2 : y ^ 2 = 1 := by rw [pow_two]; nth_rw 2 [h1]; exact mul_inv_cancel y
      obtain ⟨k, hk⟩ := hodd
      have hdvd := orderOf_dvd_of_pow_eq_one hy2
      rw [hk] at hdvd
      have : 2 * k + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hk0 : k = 0 := by omega
      rw [hk0] at hk
      have hy1 : y = 1 := orderOf_eq_one_iff.mp hk
      exact hnt fun v _ z hz => by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        rw [hy1, one_zpow]
        rfl
    · exact h
  have hMa : ∀ b ∈ Subgroup.zpowers a, ∀ m ∈ Y', b m ∈ Y' := fun b hb m hm =>
    apply_mem_of_mem_stabSub ((Subgroup.zpowers_le.mpr ha') hb) hm
  obtain ⟨c, hc, hc1, hcfix⟩ := B1.exists_fixed_ne_one hV ha2grp hMa hne
  have hrkC : 1 ≤ rk ↥(fixV (Subgroup.zpowers a) ⊓ Y') := by
    by_contra h0
    have h0' : rk ↥(fixV (Subgroup.zpowers a) ⊓ Y') = 0 := by omega
    rw [rk_eq_zero_iff hV] at h0'
    have : c ∈ fixV (Subgroup.zpowers a) ⊓ Y' := ⟨fun b hb => hcfix b hb, hc⟩
    rw [h0', Subgroup.mem_bot] at this
    exact hc1 this
  have hsplit := mRel_add_rk (fixV (Subgroup.zpowers a)) Y'
  by_cases h2 : rk Y' = 2
  · right
    refine three_dvd_orderOf_of_card_four hV ?_ hy' hodd hfpf
    rw [card_eq_two_pow hV Y', h2]
    norm_num
  · left
    have h3 : 2 ≤ mRel (fixV (Subgroup.zpowers a)) Y' := by omega
    exact h3.trans (mRel_le_of_le_right (isPGroup_subgroup hV Y) hY'Y)

theorem inf_centralizer_fittingOf_le {H : Subgroup (MulAut V)} (hH : Group.IsSolvable H) :
    H ⊓ Subgroup.centralizer (fittingOf H : Set (MulAut V)) ≤ fittingOf H := by
  have hle := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := ↥H) hH
  rintro g ⟨hgH, hg⟩
  have hmem : (⟨g, hgH⟩ : ↥H) ∈
      Subgroup.centralizer (CFSG.fittingSubgroup ↥H : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg (f : MulAut V) ⟨f, hf, rfl⟩)
  exact ⟨_, hle hmem, rfl⟩

theorem two_mul_rk_le_rkIdx_of_isSolvable (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    (hsol : Group.IsSolvable H) (hO2 : CFSG.Open.pCoreOf 2 H = ⊥)
    (hS3 : ∀ a ∈ H, ∀ y ∈ H, a ^ 2 = 1 → y ^ 3 = 1 → a * y * a⁻¹ = y⁻¹ → y = 1)
    {A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : IsElemAbelian2 A) :
    2 * rk A ≤ rkIdx (fixV A) := by
  set F := fittingOf H with hFdef
  have hFH : F ≤ H := fittingOf_le H
  have hFodd : ∀ x ∈ F, Odd (orderOf x) := B19Aux.odd_orderOf_of_mem_fittingOf hO2
  have hFcop : Nat.Coprime 2 (Nat.card F) := by
    rw [Nat.coprime_two_left]
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have h := hFodd (x : MulAut V) x.2
    rw [Subgroup.orderOf_coe, hx] at h
    exact (Nat.not_even_iff_odd.mpr h) even_two
  have hCF := inf_centralizer_fittingOf_le hsol
  induction hn : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  by_cases hA1 : A = ⊥
  · subst hA1
    rw [rk_bot]
    exact Nat.zero_le _
  have hA2 : IsPGroup 2 A := hA.isPGroup
  have hAel : CFSG.Open.IsElemAbelian 2 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hA.1 a a.2 b b.2)⟩⟩, hA.2⟩
  have hcardA : 2 ≤ Nat.card A := by
    have hpos := hA.rk_pos hA1
    rw [B1.card_elemAbelian hA]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ rk A := Nat.pow_le_pow_right (by norm_num) hpos
  have hAF : A ≤ Subgroup.normalizer (F : Set (MulAut V)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf
      exact conj_mem_fittingOf (hAH ha) hf
    · intro hf
      have h1 := conj_mem_fittingOf ((hAH ha) |> H.inv_mem) hf
      simpa [mul_assoc] using h1
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes Nat.prime_two
    hAel hcardA hAF hFcop
  obtain ⟨B, ⟨hBA, hcardB⟩, x, ⟨hxF, hxB⟩, a, haA, hax⟩ :
      ∃ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 A,
        ∃ x ∈ F ⊓ Subgroup.centralizer (B : Set (MulAut V)), ∃ a ∈ A, a * x ≠ x * a := by
    by_contra hall
    push Not at hall
    have hFA : F ≤ Subgroup.centralizer (A : Set (MulAut V)) := by
      rw [← hgen]
      refine iSup₂_le fun B hB x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      exact fun a ha => hall B hB x hx a ha
    have hAle : A ≤ F := by
      intro a ha
      refine hCF ⟨hAH ha, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp (hFA hf) a ha).symm
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have hodd := hFodd a (hAle ha)
    have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (hA.2 a ha)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have haB : a ∉ B := fun h => hax (Subgroup.mem_centralizer_iff.mp hxB a h)
  have ha2 : a ^ 2 = 1 := hA.2 a haA
  have hainv : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ha2]
  have hAeq : B ⊔ Subgroup.zpowers a = A := by
    have hle : B ⊔ Subgroup.zpowers a ≤ A := sup_le hBA (Subgroup.zpowers_le.mpr haA)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : B ≤ B ⊔ Subgroup.zpowers a)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hk, hcardB, mul_comm 2] at hdvd
    have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
    · exfalso
      rw [mul_one] at hk
      have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ Subgroup.zpowers a) hk.le
      exact haB (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    · rw [hk, hcardB, mul_comm]
  set y := x⁻¹ * (a * x * a⁻¹) with hydef
  have hyF : y ∈ F := F.mul_mem (F.inv_mem hxF) (conj_mem_fittingOf (hAH haA) hxF)
  have hyH : y ∈ H := hFH hyF
  have hy1 : y ≠ 1 := by
    intro h
    apply hax
    have h1 : x = a * x * a⁻¹ := inv_mul_eq_one.mp h
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [← h1]
  have hay : a * y * a⁻¹ = y⁻¹ := by
    have h := B19Aux.comm_conj_inv a x⁻¹ ha2
    rw [inv_inv] at h
    have he : x⁻¹ * a * x * a⁻¹ = y := by rw [hydef]; group
    rw [he] at h
    exact h
  have hBc : ∀ b ∈ B, a * b = b * a := fun b hb => hA.1 a haA b (hBA hb)
  have hyB : y ∈ Subgroup.centralizer (B : Set (MulAut V)) := by
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ hxB) ?_
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ hxB) (Subgroup.inv_mem _ ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun b hb => (hBc b hb).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun b hb => (hBc b hb).symm
  have hyodd : Odd (orderOf y) := hFodd y hyF
  have hB2 : IsPGroup 2 B := hA2.to_le hBA
  have hnt : ¬ fixV B ≤ fixV (Subgroup.zpowers y) := by
    intro hle
    have hZodd : Odd (Nat.card (Subgroup.zpowers y)) := by rw [Nat.card_zpowers]; exact hyodd
    have hcomm : ∀ z ∈ Subgroup.zpowers y, ∀ b ∈ B, z * b = b * z := by
      intro z hz b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hyb : y * b = b * y := (Subgroup.mem_centralizer_iff.mp hyB b hb).symm
      exact ((Commute.zpow_left hyb k))
    have htop := B1.axb hV hZodd hB2 hcomm (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
      (fun _ _ _ _ => Subgroup.mem_top _) (fun z hz m hm => hle hm.2 z hz)
    apply hy1
    exact MulEquiv.ext fun v => htop (Subgroup.mem_top v) y (Subgroup.mem_zpowers y)
  have haN : a ∈ Subgroup.normalizer (B : Set (MulAut V)) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hBc b hb).symm)
  have hyN : y ∈ Subgroup.normalizer (B : Set (MulAut V)) :=
    Subgroup.centralizer_le_normalizer _ hyB
  have haS : a ∈ stabSub (fixV B) :=
    FixVLat.le_stabSub_fixV_of_le_normalizer (Subgroup.zpowers_le.mpr haN)
      (Subgroup.mem_zpowers a)
  have hyS : y ∈ stabSub (fixV B) :=
    FixVLat.le_stabSub_fixV_of_le_normalizer (Subgroup.zpowers_le.mpr hyN)
      (Subgroup.mem_zpowers y)
  rcases two_le_mRel_or_three_dvd hV ha2 hay hyodd haS hyS hnt with h4 | h3
  ·
    have hfix : fixV A = fixV (Subgroup.zpowers a) ⊓ fixV B := by
      rw [← hAeq, FixVLat.fixV_sup_eq, inf_comm]
    have hsplit := codimOn_eq_add hBA (⊤ : Subgroup V)
    rw [codimOn_top, codimOn_top, inf_top_eq] at hsplit
    have hrel : mRel (fixV A) (fixV B) = mRel (fixV (Subgroup.zpowers a)) (fixV B) := by
      rw [hfix]
      unfold mRel
      rw [Subgroup.inf_relIndex_right]
    have hIH := ih (Nat.card B) (by rw [← hn, hcardB]; have := Nat.card_pos (α := B); omega)
      (hBA.trans hAH) ⟨fun x hx y hy => hA.1 x (hBA hx) y (hBA hy), fun x hx => hA.2 x (hBA hx)⟩
      rfl
    have hrkA : rk A = rk B + 1 := by
      unfold rk
      rw [hcardB, padicValNat.mul (by norm_num) Nat.card_pos.ne', padicValNat_self]
      ring
    omega
  ·
    exfalso
    set z := y ^ (orderOf y / 3) with hzdef
    have hz3 : orderOf z = 3 := orderOf_pow_orderOf_div (orderOf_pos y).ne' h3
    have hzH : z ∈ H := H.pow_mem hyH _
    have haz : a * z * a⁻¹ = z⁻¹ := by
      rw [hzdef, ← conj_pow, hay, inv_pow]
    have hz1 := hS3 a (hAH haA) z hzH ha2 (by rw [← hz3]; exact pow_orderOf_eq_one z) haz
    rw [hz1, orderOf_one] at hz3
    norm_num at hz3

end CFSG.RankThree.S4Free.Stell

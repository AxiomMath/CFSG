module

public import CFSG.RankThree.S4Free.StellmacherThmA
import CFSG.Quasithin.Background.B1MoreNineA
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

theorem two_mul_rk_le_rkIdx_of_inv (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    (hS3 : ∀ a ∈ H, ∀ y ∈ H, a ^ 2 = 1 → y ^ 3 = 1 → a * y * a⁻¹ = y⁻¹ → y = 1)
    {A B : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : IsElemAbelian2 A) (hBA : B ≤ A)
    (hcardB : Nat.card A = 2 * Nat.card B) {a y : MulAut V} (haA : a ∈ A) (haB : a ∉ B)
    (hyH : y ∈ H) (hy1 : y ≠ 1) (hyodd : Odd (orderOf y))
    (hyB : y ∈ Subgroup.centralizer (B : Set (MulAut V))) (hay : a * y * a⁻¹ = y⁻¹)
    (hIH : 2 * rk B ≤ rkIdx (fixV B)) : 2 * rk A ≤ rkIdx (fixV A) := by
  have ha2 : a ^ 2 = 1 := hA.2 a haA
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
  have hA2 : IsPGroup 2 A := hA.isPGroup
  have hB2 : IsPGroup 2 B := hA2.to_le hBA
  have hnt : ¬ fixV B ≤ fixV (Subgroup.zpowers y) := by
    intro hle
    have hZodd : Odd (Nat.card (Subgroup.zpowers y)) := by rw [Nat.card_zpowers]; exact hyodd
    have hcomm : ∀ z ∈ Subgroup.zpowers y, ∀ b ∈ B, z * b = b * z := by
      intro z hz b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hyb : y * b = b * y := (Subgroup.mem_centralizer_iff.mp hyB b hb).symm
      exact Commute.zpow_left hyb k
    have htop := B1.axb hV hZodd hB2 hcomm (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
      (fun _ _ _ _ => Subgroup.mem_top _) (fun z hz m hm => hle hm.2 z hz)
    apply hy1
    exact MulEquiv.ext fun v => htop (Subgroup.mem_top v) y (Subgroup.mem_zpowers y)
  have hBc : ∀ b ∈ B, a * b = b * a := fun b hb => hA.1 a haA b (hBA hb)
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

theorem two_mul_rk_le_rkIdx_of_odd (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    (hS3 : ∀ a ∈ H, ∀ y ∈ H, a ^ 2 = 1 → y ^ 3 = 1 → a * y * a⁻¹ = y⁻¹ → y = 1)
    {A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : IsElemAbelian2 A) {X : Subgroup (MulAut V)}
    (hXH : X ≤ H) (hXodd : ∀ x ∈ X, Odd (orderOf x))
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hXA : ¬ X ≤ Subgroup.centralizer (A : Set (MulAut V)))
    (hIH : ∀ B : Subgroup (MulAut V), B ≤ A → Nat.card B < Nat.card A →
      2 * rk B ≤ rkIdx (fixV B)) :
    2 * rk A ≤ rkIdx (fixV A) := by
  have hXcop : Nat.Coprime 2 (Nat.card X) := by
    rw [Nat.coprime_two_left]
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have h := hXodd (x : MulAut V) x.2
    rw [Subgroup.orderOf_coe, hx] at h
    exact (Nat.not_even_iff_odd.mpr h) even_two
  have hA1 : A ≠ ⊥ := by
    rintro rfl
    apply hXA
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at ha
    rw [ha, one_mul, mul_one]
  have hAel : CFSG.Open.IsElemAbelian 2 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hA.1 a a.2 b b.2)⟩⟩, hA.2⟩
  have hcardA : 2 ≤ Nat.card A := by
    have hpos := hA.rk_pos hA1
    rw [B1.card_elemAbelian hA]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ rk A := Nat.pow_le_pow_right (by norm_num) hpos
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes Nat.prime_two
    hAel hcardA hAX hXcop
  obtain ⟨B, ⟨hBA, hcardB⟩, x, ⟨hxX, hxB⟩, a, haA, hax⟩ :
      ∃ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 A,
        ∃ x ∈ X ⊓ Subgroup.centralizer (B : Set (MulAut V)), ∃ a ∈ A, a * x ≠ x * a := by
    by_contra hall
    push Not at hall
    apply hXA
    rw [← hgen]
    refine iSup₂_le fun B hB x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    exact fun a ha => hall B hB x hx a ha
  have haB : a ∉ B := fun h => hax (Subgroup.mem_centralizer_iff.mp hxB a h)
  have ha2 : a ^ 2 = 1 := hA.2 a haA
  set y := x⁻¹ * (a * x * a⁻¹) with hydef
  have hxa : a * x * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hAX haA) x).mp hxX
  have hyX : y ∈ X := X.mul_mem (X.inv_mem hxX) hxa
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
  exact two_mul_rk_le_rkIdx_of_inv hV hS3 hAH hA hBA hcardB haA haB (hXH hyX) hy1
    (hXodd y hyX) hyB hay (hIH B hBA (by rw [hcardB]; have := Nat.card_pos (α := B); omega))

theorem two_mul_le_mRel_of_orderOf_two (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V}
    {a y : MulAut V} {ℓ n : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hord : orderOf (2 : ZMod ℓ) = 4 * n) (hy : orderOf y = ℓ) (hay : a * y * a⁻¹ = y⁻¹)
    (ha : a ∈ stabSub W) (hyW : y ∈ stabSub W) (hnt : ¬ W ≤ fixV (Subgroup.zpowers y)) :
    2 * n ≤ mRel (fixV (Subgroup.zpowers a)) W := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hodd : Odd (orderOf y) := hy ▸ hℓ.odd_of_ne_two hℓ2
  set Z := Subgroup.zpowers y with hZ
  have hZcard : Nat.card Z = ℓ := by rw [hZ, Nat.card_zpowers, hy]
  have hZodd : Odd (Nat.card Z) := by rw [hZcard]; exact hℓ.odd_of_ne_two hℓ2
  have hZW : ∀ z ∈ Z, ∀ m ∈ W, z m ∈ W := fun z hz m hm =>
    apply_mem_of_mem_stabSub ((Subgroup.zpowers_le.mpr hyW) hz) hm
  obtain ⟨hsup, hinf⟩ := B1.coprime_decomp hV hZodd hZW
  set Y' := commSub W Z with hY'
  have hY'W : Y' ≤ W := commSub_le_of_invariant hZW
  have hfix : Y' ⊓ fixV Z = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw, hwfix⟩
    have hmem : w ∈ (W ⊓ fixV Z) ⊓ Y' := ⟨⟨hY'W hw, hwfix⟩, hw⟩
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
  have hy' : y ∈ stabSub Y' := mem_stabSub_commSub hyW hyZ
  have hfpf : ∀ w ∈ Y', y w = w → w = 1 := by
    intro w hw hyw
    have hwfix : w ∈ fixV Z := by
      rw [hZ]
      exact mem_fixV_zpowers_iff.mpr hyw
    have hmem : w ∈ Y' ⊓ fixV Z := ⟨hw, hwfix⟩
    rw [hfix] at hmem
    exact hmem
  have hdih := two_mul_rk_fixV_inf_le hV hay hodd ha' hy' hfpf
  have hZY' : ∀ g ∈ Z, ∀ f ∈ Y', g f ∈ Y' := fun g hg f hf =>
    apply_mem_of_mem_stabSub ((Subgroup.zpowers_le.mpr hy') hg) hf
  have hdvd := prime_dvd_card_sub_one hZcard hZY' hfix
  rw [card_eq_two_pow hV Y'] at hdvd
  have h2 : (2 : ZMod ℓ) ^ rk Y' = 1 := by
    have h1 : 1 ≤ 2 ^ rk Y' := Nat.one_le_two_pow
    have h0 := (ZMod.natCast_eq_zero_iff (2 ^ rk Y' - 1) ℓ).mpr hdvd
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, sub_eq_zero] at h0
    exact h0
  have h4 : 4 * n ∣ rk Y' := hord ▸ orderOf_dvd_of_pow_eq_one h2
  have hpos : 0 < rk Y' := by
    by_contra h0
    exact hne ((rk_eq_zero_iff hV).mp (by omega))
  have hle : 4 * n ≤ rk Y' := Nat.le_of_dvd hpos h4
  have hsplit := mRel_add_rk (fixV (Subgroup.zpowers a)) Y'
  have hmono : mRel (fixV (Subgroup.zpowers a)) Y' ≤ mRel (fixV (Subgroup.zpowers a)) W :=
    mRel_le_of_le_right (isPGroup_subgroup hV W) hY'W
  omega

end CFSG.RankThree.S4Free.Stell

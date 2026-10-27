module

public import CFSG.RankThree.PartTwo.Sec13.Item13Plane
public import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.KFacts.K74Bloom

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

section Helpers

theorem mem_sectionCentralizer_of_ne {A L X : Subgroup G} {c x : G}
    (hL : L ∈ thetaComponentsAt 3 c) (hX : X ∈ thetaComponentsAt 3 c) (hne : X ≠ L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hxA : x ∈ A) (hxX : x ∈ X) :
    x ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
  refine ⟨hxA, fun y hy => ?_⟩
  have h1 := Sec10.commutator_mem_theta_of_ne hX hL hne hxX hy
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN hxA) y).mp hy) (L.inv_mem hy)
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL]
    exact ⟨h2, h1⟩
  exact h3

omit [Finite G] in
theorem card_autIn_map_conj {A L : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    Nat.card (Sec4.autIn (L.map (MulAut.conj w).toMonoidHom) A) = Nat.card (Sec4.autIn L A) := by
  set ρ : MulAut A := A.normalizerMonoidHom ⟨w, hw⟩ with hρ
  have heq : Sec4.autIn (L.map (MulAut.conj w).toMonoidHom) A =
      (Sec4.autIn L A).map (MulAut.conj ρ).toMonoidHom := by
    ext σ
    rw [Sec4.mem_autIn_iff]
    constructor
    · rintro ⟨h, hN, ⟨l, hl, rfl⟩, rfl⟩
      have hlN : l ∈ Subgroup.normalizer (A : Set G) := by
        have : w⁻¹ * (w * l * w⁻¹) * w ∈ Subgroup.normalizer (A : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) hN) hw
        simpa [mul_assoc] using this
      refine ⟨A.normalizerMonoidHom ⟨l, hlN⟩, Sec4.mem_autIn_iff.mpr ⟨l, hlN, hl, rfl⟩, ?_⟩
      ext x
      simp [hρ, MulAut.conj_apply, mul_assoc]
    · rintro ⟨τ, hτ, rfl⟩
      obtain ⟨l, hlN, hlL, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
      refine ⟨w * l * w⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hlN) (Subgroup.inv_mem _ hw),
        ⟨l, hlL, rfl⟩, ?_⟩
      ext x
      simp [hρ, MulAut.conj_apply, mul_assoc]
  rw [heq]
  exact Nat.card_congr
    ((Sec4.autIn L A).equivMapOfInjective _ (MulAut.conj ρ).injective).toEquiv.symm

omit [Finite G] in
theorem autIn_normalizer_eq (A : Subgroup G) :
    Sec4.autIn (Subgroup.normalizer (A : Set G)) A = wStar A := by
  ext σ
  rw [wStar, Sec4.mem_autIn_iff, Sec4.mem_autIn_iff]
  exact ⟨fun ⟨h, hN, _, hσ⟩ => ⟨h, hN, Subgroup.mem_top _, hσ⟩,
    fun ⟨h, hN, _, hσ⟩ => ⟨h, hN, hN, hσ⟩⟩

omit [Finite G] in
theorem autIn_mono {K H B : Subgroup G} (hKH : K ≤ H) : Sec4.autIn K B ≤ Sec4.autIn H B := by
  intro σ hσ
  obtain ⟨h, hN, hK, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  exact Sec4.mem_autIn_iff.mpr ⟨h, hN, hKH hK, rfl⟩

theorem ne_bot_of_mulEquiv {M : Type*} [Group M] {H : Subgroup M} {T : Type*} [Group T]
    (e : H ≃* T) (hT : Nat.card T ≠ 1) : H ≠ ⊥ := by
  rintro rfl
  apply hT
  rw [← Nat.card_congr e.toEquiv]
  exact Subgroup.card_bot

theorem card_multiplicative_zmod (n : ℕ) [NeZero n] :
    Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem card_perm_fin_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_quaternion_two : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem card_SL_two_three : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [Matrix.card_SL_field, ZMod.card]
  simp [Fin.prod_univ_two]

theorem autIn_ne_bot_of_not_mem (h131 : Item131) (hspor : SporadicModels131)
    (hSLC : SLTwoCenter) {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) (hcL : c ∉ L) :
    Sec4.autIn L A ≠ ⊥ := by
  rcases cases131 h131 hspor hSLC hD with
    ⟨-, -, -, ⟨-, he | he⟩ | ⟨-, he⟩ | ⟨-, he⟩⟩ | ⟨-, -, -, he⟩ | ⟨-, -, he, -⟩ | ⟨h, -⟩
  · obtain ⟨e⟩ := he
    exact ne_bot_of_mulEquiv e (by rw [card_quaternion_two]; norm_num)
  · obtain ⟨e⟩ := he
    exact ne_bot_of_mulEquiv e (by rw [card_SL_two_three]; norm_num)
  · obtain ⟨e⟩ := he
    exact ne_bot_of_mulEquiv e (by rw [card_multiplicative_zmod]; norm_num)
  · obtain ⟨e⟩ := he
    exact ne_bot_of_mulEquiv e (by rw [card_quaternion_two]; norm_num)
  · obtain ⟨e⟩ := he
    exact ne_bot_of_mulEquiv e (by rw [card_perm_fin_three]; norm_num)
  · obtain ⟨e⟩ := he
    exact ne_bot_of_mulEquiv e (by rw [card_multiplicative_zmod]; norm_num)
  · exact absurd h hcL

theorem not_mem_of_hyp (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (hSLT : NotSLTwoOfHypT) {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hST : HypS A ∨ HypT A)
    (hW : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    c ∉ L := by
  rcases hST with hS | hT
  · exact hS.2.2 c hD.zpowers_mem_omegaA L hD.mem_lA
  · intro hcL
    rcases cases131 h131 hspor hSLC hD with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hSL | ⟨-, hle⟩⟩
    · exact h hcL
    · exact h hcL
    · exact h hcL
    · exact hSLT G A c L hD hT hSL
    · exact hW hle

omit [Finite G] in
theorem inf_normalizer_le_normalizer_inf (A X : Subgroup G) :
    X ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G) := by
  rintro k ⟨hkX, hkA⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxA, hxX⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hkA x).mp hxA,
      X.mul_mem (X.mul_mem hkX hxX) (X.inv_mem hkX)⟩
  · rintro ⟨hxA, hxX⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hkA x).mpr hxA, ?_⟩
    have : k⁻¹ * (k * x * k⁻¹) * k ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hkX) hxX) hkX
    simpa [mul_assoc] using this

theorem card_plane_eq_nine {A B : Subgroup G} {a : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (haB : a ∉ B) : Nat.card B = 9 := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hdvd : Nat.card B ∣ 27 := h27 ▸ Subgroup.card_dvd_of_le hBA
  have hne : Nat.card B ≠ 27 := by
    intro h
    apply haB
    have : B = A := Subgroup.eq_of_le_of_card_ge hBA (by rw [h, h27])
    rw [this]
    exact haA
  have hsurj : Function.Surjective (fun ib : Fin 3 × B =>
      (⟨a ^ (ib.1 : ℕ) * ib.2, A.mul_mem (A.pow_mem haA _) (hBA ib.2.2)⟩ : A)) := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, b, hb, rfl⟩ := exists_pow_mul_of_mem hA haA hAa hx
    exact ⟨(⟨i, hi⟩, ⟨b, hb⟩), rfl⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_fin, h27] at hle
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card B ∣ 3 ^ 3 from hdvd)
  interval_cases k <;> simp_all

end Helpers

section Commutator

omit [Finite G] in
theorem exists_mem_inf_of_autIn_ne_bot {A L : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hne : Sec4.autIn L A ≠ ⊥) :
    ∃ d ∈ A, d ∈ L ∧ d ≠ 1 := by
  obtain ⟨σ, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨l, hlN, hlL, hσl⟩ := Sec4.mem_autIn_iff.mp σ.2
  obtain ⟨y, hy⟩ : ∃ y : A, (σ : MulAut A) y ≠ y := by
    by_contra h
    push Not at h
    apply hσ1
    apply Subtype.ext
    ext y
    rw [h y]
    rfl
  refine ⟨l * y * l⁻¹ * y⁻¹, A.mul_mem ((Subgroup.mem_normalizer_iff.mp hlN y).mp y.2)
    (A.inv_mem y.2), ?_, ?_⟩
  · have h1 : (y : G) * l⁻¹ * (y : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAN y.2) l⁻¹).mp (L.inv_mem hlL)
    have : l * ((y : G) * l⁻¹ * (y : G)⁻¹) ∈ L := L.mul_mem hlL h1
    simpa [mul_assoc] using this
  · intro h1
    apply hy
    rw [← hσl]
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_val]
    have h1' : l * (y : G) * l⁻¹ * (y : G)⁻¹ = 1 := by simpa using h1
    have : l * y * l⁻¹ = (l * y * l⁻¹ * (y : G)⁻¹) * y := by group
    rw [this, h1', one_mul]

end Commutator

section Plane

variable {A : Subgroup G} {a : G} {X : Subgroup G}

theorem not_mem_plane_of_mem_omegaA (h131 : Item131) (hspor : SporadicModels131)
    (hSLC : SLTwoCenter) (hset : Item13SetupAt) (h410 : K410NotInverted)
    (hSLT : NotSLTwoOfHypT) {c : G} {L : Subgroup G} (hD : Sec13Data G A c L)
    (hST : HypS A ∨ HypT A) (haA : a ∈ A) (hX : X ∈ thetaComponentsAt 3 a)
    (hAa : A = Subgroup.zpowers a ⊔ (A ⊓ X)) (haB : a ∉ A ⊓ X)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (X ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ X)))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G))
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G))
    {c' : G} (hc' : Subgroup.zpowers c' ∈ omegaA A) : c' ∉ A ⊓ X := by
  intro hc'B
  set B := A ⊓ X with hBdef
  set K := X ⊓ Subgroup.normalizer (A : Set G) with hKdef
  have hAe := hD.isElemAbelian
  have h27 := hD.card_eq
  have hBA : B ≤ A := inf_le_left
  have hB9 : Nat.card B = 9 := card_plane_eq_nine hAe h27 haA hAa haB
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz => hD.commute hy hz
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x (hBA x.2) y (hBA y.2))⟩⟩, fun x hx => hAe.2 x (hBA hx)⟩
  have hKa : ∀ k ∈ K, k * a = a * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (Sec6.le_centralizer_of_mem_thetaComponentsAt hX hk.1)
  have hKA : K ≤ Subgroup.normalizer (A : Set G) := inf_le_right
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := inf_normalizer_le_normalizer_inf A X
  obtain ⟨L', hL'⟩ := hset G hD.toPartTwoStanding hD.partTwoS_eq A hD.mem_partTwoF
    hD.not_mem_partTwoT c' hc'
  have hD' : Sec13Data G A c' L' :=
    ⟨hD.toPartTwoStanding, hD.partTwoS_eq, hD.mem_partTwoF, hD.not_mem_partTwoT, hc', hL'⟩
  have hc'1 : c' ≠ 1 := hD'.ne_one
  have hc'A : c' ∈ A := hD'.mem_A
  have hc'3 : c' ^ 3 = 1 := hAe.2 c' hc'A
  have hWc' : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c' : Set G) := by
    intro hle
    rcases eq_bot_or_eq_of_isIrreducibleOn hirr (Subgroup.zpowers_le.mpr hc'B)
      (fun k hk => hle (hKA hk)) with h | h
    · exact hc'1 (Subgroup.zpowers_eq_bot.mp h)
    · have := hD'.card_zpowers
      rw [h, hB9] at this
      norm_num at this
  have hc'L' : c' ∉ L' := not_mem_of_hyp h131 hspor hSLC hSLT hD' hST hWc'
  have hAL'B : A ⊓ L' ≤ B := by
    intro x hx
    by_contra hxB
    obtain ⟨i, hi3, b, hb, hxe⟩ := exists_pow_mul_of_mem hAe haA hAa hx.1
    obtain ⟨w, hw, hwT, hwa⟩ :=
      exists_transv_of_irreducible hAe haA hAa hB9 hKa hirr hKA hKB hWB hWa hc'B
    have hwfix : ∀ y ∈ B, w * y * w⁻¹ = y := fun y hy => by
      have h1 := congrArg Subtype.val (hwT.1 ⟨y, hBA hy⟩ hy)
      rwa [normalizerMonoidHom_apply_val] at h1
    have hwH : w ∈ Subgroup.normalizer (Subgroup.zpowers c' : Set G) := by
      refine centralizer_le_normalizer_zpowers c' (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      calc w * c' = (w * c' * w⁻¹) * w := by group
        _ = c' * w := by rw [hwfix c' hc'B]
    have hxc' : x ∉ Subgroup.zpowers c' := fun h => hxB (Subgroup.zpowers_le.mpr hc'B h)
    have hwL' : w ∈ Subgroup.normalizer (L' : Set G) :=
      normalizer_inf_le_of_mem hL'.1 hL'.2.1 hL'.2.2.1 hx.1 hx.2 hxc' ⟨hwH, hw⟩
    have hwx : w * x * w⁻¹ = x * c' ^ i := by
      have e1 : w * x * w⁻¹ = (w * a * w⁻¹) ^ i * (w * b * w⁻¹) := by
        rw [hxe, ← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul, map_pow]
      rw [e1, hwa, hwfix b hb, hxe, Commute.mul_pow (hcomm a haA c' hc'A) i, mul_assoc,
        mul_assoc, hcomm (c' ^ i) (A.pow_mem hc'A i) b (hBA hb)]
    have hc'i : c' ^ i ∈ L' := by
      have h1 : w * x * w⁻¹ ∈ L' := (Subgroup.mem_normalizer_iff.mp hwL' x).mp hx.2
      rw [hwx] at h1
      have h2 := L'.mul_mem (L'.inv_mem hx.2) h1
      rwa [inv_mul_cancel_left] at h2
    interval_cases i
    · apply hxB
      rw [hxe, pow_zero, one_mul]
      exact hb
    · exact hc'L' (by simpa using hc'i)
    · apply hc'L'
      have e : (c' ^ 2) ^ 2 = c' := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc'3, one_mul, pow_one]
      rw [← e]
      exact L'.pow_mem hc'i 2
  have hne9 : Nat.card (A ⊓ L' : Subgroup G) ≠ 9 := fun h9 => by
    have : A ⊓ L' = B := Subgroup.eq_of_le_of_card_ge hAL'B (by rw [h9, hB9])
    have hc'AL' : c' ∈ A ⊓ L' := this ▸ hc'B
    exact hc'L' hc'AL'.2
  rcases cases131 h131 hspor hSLC hD' with ⟨-, h9, -⟩ | ⟨-, h9, -⟩ | ⟨-, hPGL, hstar, hx⟩ |
      ⟨hc'L, -⟩
  · exact hne9 h9
  · exact hne9 h9
  ·
    obtain ⟨ψ⟩ := hstar
    have hne : Sec4.autIn L' A ≠ ⊥ :=
      ne_bot_of_mulEquiv ψ (by rw [card_multiplicative_zmod]; norm_num)
    obtain ⟨d, hdA, hdL', hd1⟩ := exists_mem_inf_of_autIn_ne_bot hL'.2.1 hne
    have hdB : d ∈ B := hAL'B ⟨hdA, hdL'⟩
    have hdc' : d ∉ Subgroup.zpowers c' := by
      intro h
      rcases eq_of_mem_zpowers_of_pow_three hc'3 h with h | h | h
      · exact hd1 h
      · exact hc'L' (h ▸ hdL')
      · apply hc'L'
        have e : d ^ 2 = c' := by
          rw [h, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc'3, one_mul, pow_one]
        rw [← e]
        exact L'.pow_mem hdL' 2
    have hd3 : d ^ 3 = 1 := hAe.2 d hdA
    have hdcard : Nat.card (Subgroup.zpowers d) = 3 := by
      rw [Nat.card_zpowers]
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hd3) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hd1
      · exact h
    have hAL'eq : A ⊓ L' = Subgroup.zpowers d := by
      symm
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hdA, hdL'⟩) ?_
      have hdvd : Nat.card (A ⊓ L' : Subgroup G) ∣ 3 ^ 2 := by
        rw [show 3 ^ 2 = 9 by norm_num, ← hB9]
        exact Subgroup.card_dvd_of_le hAL'B
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      rw [hdcard, hk']
      interval_cases k
      · norm_num
      · norm_num
      · exact absurd hk' hne9
    have hS4 : 4 ∣ Nat.card (Sec4.autIn K B) :=
      KFacts.four_dvd_card_of_isIrreducibleOn hBe hB9 hirr
    obtain ⟨ι, hι, hιinv⟩ := exists_inv_mem_of_four_dvd hBe hB9 hS4
    obtain ⟨t, htN, htK, htι⟩ := Sec4.mem_autIn_iff.mp hι
    have htinv : ∀ y ∈ B, t * y * t⁻¹ = y⁻¹ := fun y hy => by
      have h1 := hιinv ⟨y, hy⟩
      rw [← htι] at h1
      have h2 := congrArg Subtype.val h1
      rwa [normalizerMonoidHom_apply_val] at h2
    have htW : t ∈ Subgroup.normalizer (A : Set G) := htK.2
    have htH : t ∈ Subgroup.normalizer (Subgroup.zpowers c' : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change Subgroup.zpowers (t * c' * t⁻¹) = _
      rw [htinv c' hc'B, Subgroup.zpowers_inv]
    have htL' : t ∈ Subgroup.normalizer (L' : Set G) :=
      normalizer_inf_le_of_mem hL'.1 hL'.2.1 hL'.2.2.1 hdA hdL' hdc' ⟨htH, htW⟩
    have hta : t * a * t⁻¹ = a := by
      rw [hKa t htK, mul_inv_cancel_right]
    have hanot : a ∉ Subgroup.zpowers c' ⊔ Subgroup.zpowers d := fun h =>
      haB ((sup_le (Subgroup.zpowers_le.mpr hc'B) (Subgroup.zpowers_le.mpr hdB)) h)
    exact h410 G A c' L' hL'.1 hAe h27 hc'A hc'1 hL'.2.1 hL'.2.2.1 hPGL hx d a t hAL'eq hd1 haA
      hanot htL' htW hta (htinv d hdB)
  · exact hc'L' hc'L

end Plane

section CaseThree

variable {A : Subgroup G} {a : G} {X : Subgroup G}

theorem case_three_132 (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (hSLT : NotSLTwoOfHypT) {c : G} {L : Subgroup G} (hD : Sec13Data G A c L)
    (hST : HypS A ∨ HypT A) (haA : a ∈ A) (hX : X ∈ thetaComponentsAt 3 a)
    (hAa : A = Subgroup.zpowers a ⊔ (A ⊓ X)) (haB : a ∉ A ⊓ X)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (X ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ X)))
    (hWB : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G))
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    Sec21.IsIrreducibleOn (wStar A) ∧
      Nonempty (Subgroup.closure {σ : MulAut A | σ ∈ wStar A ∧ ∃ k : ℕ, σ ^ 3 ^ k = 1} ≃*
        alternatingGroup (Fin 4)) ∧
      ∃ φ : wStar A →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4), Function.Injective φ := by
  set B := A ⊓ X with hBdef
  set K := X ⊓ Subgroup.normalizer (A : Set G) with hKdef
  have hAe := hD.isElemAbelian
  have h27 := hD.card_eq
  have hBA : B ≤ A := inf_le_left
  have hB9 : Nat.card B = 9 := card_plane_eq_nine hAe h27 haA hAa haB
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz => hD.commute hy hz
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x (hBA x.2) y (hBA y.2))⟩⟩, fun x hx => hAe.2 x (hBA hx)⟩
  have hKa : ∀ k ∈ K, k * a = a * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (Sec6.le_centralizer_of_mem_thetaComponentsAt hX hk.1)
  have hKA : K ≤ Subgroup.normalizer (A : Set G) := inf_le_right
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := inf_normalizer_le_normalizer_inf A X
  have hirrW := isIrreducibleOn_wStar_of hAe h27 haA hAa haB hB9 hKa hirr hKA hKB hWa hWB
  have hWc : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro hle
    have hirr' : Sec21.IsIrreducibleOn (Sec4.autIn (Subgroup.normalizer (A : Set G)) A) := by
      rw [autIn_normalizer_eq]
      exact hirrW
    rcases eq_bot_or_eq_of_isIrreducibleOn hirr' (Subgroup.zpowers_le.mpr hD.mem_A) hle with
      h | h
    · exact hD.ne_one (Subgroup.zpowers_eq_bot.mp h)
    · have := hD.card_zpowers
      rw [h, h27] at this
      norm_num at this
  have hcL : c ∉ L := not_mem_of_hyp h131 hspor hSLC hSLT hD hST hWc
  have hN1 : Sec4.autIn L A ≠ ⊥ := autIn_ne_bot_of_not_mem h131 hspor hSLC hD hcL
  obtain ⟨d, hdA, hdL, hd1⟩ := exists_mem_inf_of_autIn_ne_bot hD.le_normalizer hN1
  have hdc : d ∉ Subgroup.zpowers c := by
    intro h
    have hc3 : c ^ 3 = 1 := hAe.2 c hD.mem_A
    rcases eq_of_mem_zpowers_of_pow_three hc3 h with h | h | h
    · exact hd1 h
    · exact hcL (h ▸ hdL)
    · apply hcL
      have e : d ^ 2 = c := by
        rw [h, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc3, one_mul, pow_one]
      rw [← e]
      exact L.pow_mem hdL 2
  have hHW := normalizer_inf_le_of_mem hD.mem_thetaComponentsAt hD.le_normalizer
    hD.sectionCentralizer_eq hdA hdL hdc
  have h4 : 4 ∣ Nat.card (wStar A) :=
    KFacts.four_dvd_card_of_irreducible_plane hBe hB9 hBA hKA hKB hirr (autIn_mono le_top)
  refine ⟨hirrW, KFacts.rank3II_13_2_bloom hAe h27 hirrW h4 (c := ⟨c, hD.mem_A⟩)
    (B := (A ⊓ L).subgroupOf A) ?_ hN1 ?_ ?_ ?_⟩
  · intro h
    exact hcL (Subgroup.mem_subgroupOf.mp h).2
  · intro n hn
    obtain ⟨l, hlN, hlL, rfl⟩ := Sec4.mem_autIn_iff.mp hn
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_val]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hlL)
    change l * c * l⁻¹ = c
    rw [h1, mul_inv_cancel_right]
  · intro n hn x
    obtain ⟨l, hlN, hlL, rfl⟩ := Sec4.mem_autIn_iff.mp hn
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, normalizerMonoidHom_apply_val]
    refine ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp hlN x).mp x.2) (A.inv_mem x.2), ?_⟩
    have h1 : (x : G) * l⁻¹ * (x : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer x.2) l⁻¹).mp (L.inv_mem hlL)
    have : l * ((x : G) * l⁻¹ * (x : G)⁻¹) ∈ L := L.mul_mem hlL h1
    simpa [mul_assoc] using this
  · intro σ hσ hσc n hn
    obtain ⟨w, hwN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    obtain ⟨l, hlN, hlL, rfl⟩ := Sec4.mem_autIn_iff.mp hn
    have hwc : w * c * w⁻¹ = c := by
      have h1 := congrArg Subtype.val hσc
      rwa [normalizerMonoidHom_apply_val] at h1
    have hwH : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      refine centralizer_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      calc w * c = (w * c * w⁻¹) * w := by group
        _ = c * w := by rw [hwc]
    have hwL : w ∈ Subgroup.normalizer (L : Set G) := hHW ⟨hwH, hwN⟩
    refine Sec4.mem_autIn_iff.mpr ⟨w * l * w⁻¹,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hwN hlN) (Subgroup.inv_mem _ hwN),
      (Subgroup.mem_normalizer_iff.mp hwL l).mp hlL, ?_⟩
    ext x
    simp [MulAut.mul_apply, mul_assoc]

end CaseThree

section CaseOne

variable {A : Subgroup G} {a : G} {X : Subgroup G}

theorem case_one_132 (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (hset : Item13SetupAt) (h410 : K410NotInverted) (hSLT : NotSLTwoOfHypT) {c : G}
    {L : Subgroup G} (hD : Sec13Data G A c L) (hST : HypS A ∨ HypT A) (haA : a ∈ A)
    (hX : X ∈ thetaComponentsAt 3 a) (hAa : A = Subgroup.zpowers a ⊔ (A ⊓ X)) (haB : a ∉ A ⊓ X)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (X ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ X)))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G))
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G) ∧
      CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) ∧ Nat.card (oThreeWStar A) = 9 ∧
      wStar A = oThreeWStar A ⊔
        Sec4.autIn (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A ∧
      omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) ∧
      omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers a) ∧
      (omegaA A).ncard = 9 ∧
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      (IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22)) := by
  set B := A ⊓ X with hBdef
  set K := X ⊓ Subgroup.normalizer (A : Set G) with hKdef
  have hAe := hD.isElemAbelian
  have h27 := hD.card_eq
  have hBA : B ≤ A := inf_le_left
  have hB9 : Nat.card B = 9 := card_plane_eq_nine hAe h27 haA hAa haB
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz => hD.commute hy hz
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x (hBA x.2) y (hBA y.2))⟩⟩, fun x hx => hAe.2 x (hBA hx)⟩
  have hKa : ∀ k ∈ K, k * a = a * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (Sec6.le_centralizer_of_mem_thetaComponentsAt hX hk.1)
  have hKA : K ≤ Subgroup.normalizer (A : Set G) := inf_le_right
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := inf_normalizer_le_normalizer_inf A X
  have hsub : omegaA A ⊆ pointsOff A B := by
    rintro F ⟨hFA, hF3, c', rfl, hstar⟩
    refine ⟨hFA, hF3, fun h => ?_⟩
    exact not_mem_plane_of_mem_omegaA h131 hspor hSLC hset h410 hSLT hD hST haA hX hAa haB hirr
      hWB hWa ⟨hFA, hF3, c', rfl, hstar⟩ (h (Subgroup.mem_zpowers c'))
  have hcP : Subgroup.zpowers c ∈ pointsOff A B := hsub hD.zpowers_mem_omegaA
  have hcB : c ∉ B := fun h => hcP.2.2 (Subgroup.zpowers_le.mpr h)
  have haP : Subgroup.zpowers a ∈ pointsOff A B :=
    (mem_pointsOff_iff hAe haA hAa haB).mpr ⟨1, B.one_mem, by rw [mul_one]⟩
  have horbit : ∀ F ∈ pointsOff A B, orbitIn (Subgroup.normalizer (A : Set G)) F =
      pointsOff A B := by
    intro F hF
    ext F'
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact map_conj_mem_pointsOff hw (hWB hw) hF
    · intro hF'
      obtain ⟨b, hb, rfl⟩ := (mem_pointsOff_iff hAe haA hAa haB).mp hF
      obtain ⟨b', hb', rfl⟩ := (mem_pointsOff_iff hAe haA hAa haB).mp hF'
      obtain ⟨w, hw, -, hwF⟩ :=
        exists_conj_pointsOff hAe haA hAa hB9 hKa hirr hKA hKB hWB hWa hb hb'
      exact ⟨w, hw, hwF.symm⟩
  have hΩ : omegaA A = pointsOff A B := by
    refine Set.Subset.antisymm hsub fun F hF => ?_
    rw [← horbit _ hcP] at hF
    obtain ⟨w, hw, rfl⟩ := hF
    exact (map_conj_mem_omegaA_iff hw).mpr hD.zpowers_mem_omegaA
  have hO3 := oThreeWStar_eq_transvAxis hAe haA hAa haB hB9 hKa hirr hKA hKB hWB hWa
  obtain ⟨-, hT9⟩ := transvAxis_le_wStar_and_card hAe haA hAa hB9 hKa hirr hKA hKB hWB hWa
  have hTinj : Function.Injective (transvValue (B := B) hAe haA) := by
    intro σ τ hστ
    have h1 : σ.1 ⟨a, haA⟩ = τ.1 ⟨a, haA⟩ := by
      have := congrArg (fun z : A => z * ⟨a, haA⟩) hστ
      simpa [transvValue] using this
    exact Subtype.ext (transvAxis_ext hAe haA hAa σ.2 τ.2 h1)
  have hTe : CFSG.Assembly.IsElemAbelian 3 (transvAxis A B) := by
    refine ⟨⟨⟨fun σ τ => hTinj ?_⟩⟩, fun σ hσ => transvAxis_pow_three hAe hσ⟩
    rw [map_mul, map_mul]
    exact hAe.1.is_comm.comm _ _
  obtain ⟨b₀, hb₀, hcb₀⟩ := (mem_pointsOff_iff hAe haA hAa haB).mp hcP
  obtain ⟨w, hw, -, hwc⟩ :=
    exists_conj_pointsOff hAe haA hAa hB9 hKa hirr hKA hKB hWB hWa hb₀ B.one_mem
  have hwca : Subgroup.zpowers (w * c * w⁻¹) = Subgroup.zpowers a := by
    have h1 : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers a := by
      rw [hcb₀, hwc, mul_one]
    rw [MonoidHom.map_zpowers] at h1
    exact h1
  set L' := L.map (MulAut.conj w).toMonoidHom with hL'def
  have hL'a : L' ∈ lA A a := by
    have h1 := (map_conj_mem_lA_iff hw).mpr hD.mem_lA
    rwa [lA_congr hwca] at h1
  have hXL' : X = L' := by
    by_contra hne
    have hBsub : B ≤ Subgroup.zpowers a := fun y hy => by
      have h1 := mem_sectionCentralizer_of_ne hL'a.1 hX hne hL'a.2.1 hy.1 hy.2
      rw [hL'a.2.2.1] at h1
      exact h1
    have h1 := Subgroup.card_le_of_le hBsub
    rw [hB9, haP.2.1] at h1
    omega
  have hcL : c ∉ L := by
    intro hcL
    apply haB
    have h1 : w * c * w⁻¹ ∈ X := by
      rw [hXL']
      exact ⟨c, hcL, rfl⟩
    have h2 : w * c * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw c).mp hD.mem_A
    have h3 : a ∈ Subgroup.zpowers (w * c * w⁻¹) := hwca ▸ Subgroup.mem_zpowers a
    exact (Subgroup.zpowers_le.mpr ⟨h2, h1⟩ : Subgroup.zpowers (w * c * w⁻¹) ≤ B) h3
  have h4 : 4 ∣ Nat.card (Sec4.autIn L A) := by
    have h4X : 4 ∣ Nat.card (Sec4.autIn X A) :=
      KFacts.four_dvd_card_of_irreducible_plane hBe hB9 hBA hKA hKB hirr (autIn_mono inf_le_left)
    rwa [hXL', card_autIn_map_conj hw] at h4X
  have hcases : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      (IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22)) := by
    rcases cases131 h131 hspor hSLC hD with ⟨-, -, hprod, hL3 | hA7 | hM22⟩ |
        ⟨-, -, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩, -⟩ | ⟨h, -⟩
    · exact ⟨hprod, Or.inl hL3.1⟩
    · exact ⟨hprod, Or.inr (Or.inl hA7.1)⟩
    · exact ⟨hprod, Or.inr (Or.inr hM22.1)⟩
    · rw [Nat.card_congr e.toEquiv, card_perm_fin_three] at h4
      norm_num at h4
    · rw [Nat.card_congr e.toEquiv, card_multiplicative_zmod] at h4
      norm_num at h4
    · exact absurd h hcL
  refine ⟨hWB, by rw [hO3]; exact hTe, by rw [hO3, hT9],
    wStar_eq_sup hAe haA hAa haB hB9 hKa hirr hKA hKB hWB hWa hD.mem_A hcB hD.ne_one,
    by rw [hΩ, horbit _ hcP], by rw [hΩ, horbit _ haP],
    by rw [hΩ, ncard_pointsOff hAe haA hAa haB hB9], hcases.1, hcases.2⟩

end CaseOne

theorem rank3II_13_2_of_inputs (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (hset : Item13SetupAt) (h410 : K410NotInverted) (hSLT : NotSLTwoOfHypT) : Item132 := by
  intro G _ _ A c L hD hST a haA _ X hX hAa haB hirr
  by_cases hWa : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)
  · exact Or.inr (Or.inl hWa)
  by_cases hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G)
  · exact Or.inl (case_one_132 h131 hspor hSLC hset h410 hSLT hD hST haA hX hAa haB hirr hWB hWa)
  · exact Or.inr (Or.inr (case_three_132 h131 hspor hSLC hSLT hD hST haA hX hAa haB hirr hWB hWa))

end CFSG.RankThree.PartTwo.Sec13

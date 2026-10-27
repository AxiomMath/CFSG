module

public import CFSG.RankThree.PartTwo.Sec3.TwoOfThreeNormal
public import CFSG.RankThree.PartTwo.Sec18.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec3
open Subgroup

namespace Item181ThreeProof

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def pAt (S Q : Subgroup G) (i : ℕ) : Subgroup G :=
  sSup {B | B ∈ famG S i ∧ B ≤ Q}

omit [Finite G] in
theorem pAt_le (S Q : Subgroup G) (i : ℕ) : pAt S Q i ≤ Q := sSup_le fun _ h => h.2

omit [Finite G] in
theorem pAt_le_jG (S Q : Subgroup G) (i : ℕ) : pAt S Q i ≤ jG S i :=
  sSup_le fun _ h => le_jG h.1

omit [Finite G] in
theorem le_pAt {S Q B : Subgroup G} {i : ℕ} (h : B ∈ famG S i) (hQ : B ≤ Q) :
    B ≤ pAt S Q i :=
  le_sSup ⟨h, hQ⟩

omit [Finite G] in
theorem conj_mem_pAt {S Q : Subgroup G} (hQS : Q ≤ S) {i : ℕ} {g : G}
    (hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) {x : G} (hx : x ∈ pAt S Q i) :
    g * x * g⁻¹ ∈ pAt S Q i := by
  have hle : (pAt S Q i).map (MulAut.conj g).toMonoidHom ≤ pAt S Q i := by
    rw [pAt, (Subgroup.gc_map_comap (MulAut.conj g).toMonoidHom).l_sSup]
    refine iSup₂_le fun B hB => le_sSup ⟨map_conj_mem_famG hB.1 g
      (fun b hb => hQS (hgQ b (hB.2 hb))), ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hgQ b (hB.2 hb)
  exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem isPGroup_of_isElemTwo {B : Subgroup G} (hB : IsElemTwo B) : IsPGroup 2 B := fun b =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one]; exact hB.2 b b.2)⟩

theorem le_pAt_of_card {S Q B : Subgroup G} {i : ℕ} (hQS : Q ≤ S) (hBQ : B ≤ Q)
    (hB : IsElemTwo B) (hi : 1 ≤ CFSG.pRank 2 S - i)
    (hcard : 2 ^ (CFSG.pRank 2 S - i) ≤ Nat.card B) : B ≤ pAt S Q i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro b hb
  obtain ⟨r, hr⟩ := (isPGroup_of_isElemTwo hB).exists_card_eq
  have hdvd1 : Nat.card (Subgroup.zpowers b) ∣ 2 ^ (CFSG.pRank 2 S - i) := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hB.2 b hb)).trans
      (dvd_pow_self 2 (by omega))
  have hdvd2 : 2 ^ (CFSG.pRank 2 S - i) ∣ Nat.card B := by
    rw [hr]
    apply Nat.pow_dvd_pow
    rw [hr] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  obtain ⟨K, hK, hbK, hKB⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hdvd1
    hdvd2 (Subgroup.zpowers_le.mpr hb)
  have hKfam : K ∈ famG S i :=
    ⟨hKB.trans (hBQ.trans hQS), ⟨fun x hx y hy => hB.1 x (hKB hx) y (hKB hy),
      fun x hx => hB.2 x (hKB hx)⟩, hK⟩
  exact le_pAt hKfam (hKB.trans hBQ) (hbK (Subgroup.mem_zpowers b))

omit [Finite G] in
theorem jG_eq_bot_of_pRank_sub_eq_zero {S : Subgroup G} {i : ℕ}
    (h : CFSG.pRank 2 S - i = 0) : jG S i = ⊥ := by
  rw [eq_bot_iff, jG]
  refine sSup_le fun A hA => ?_
  have hcard := hA.2.2
  rw [h, pow_zero] at hcard
  rw [Subgroup.card_eq_one.mp hcard]

theorem normalizer_le_normalizer_omegaG (J : Subgroup G) :
    normalizer (J : Set G) ≤ normalizer (omegaG J : Set G) := by
  intro g hg
  refine Sec3.mem_normalizer_of_conj_mem fun z hz => conj_mem_omegaG (fun x hx => ?_)
    (fun x hx => ?_) hz
  · exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    rwa [inv_inv] at this

theorem normalizer_le_normalizer_jG (S : Subgroup G) (i : ℕ) :
    normalizer (S : Set G) ≤ normalizer (jG S i : Set G) := by
  intro g hg
  refine Sec3.mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : (jG S i).map (MulAut.conj g).toMonoidHom ≤ jG S i := by
    rw [jG, (Subgroup.gc_map_comap (MulAut.conj g).toMonoidHom).l_sSup]
    exact iSup₂_le fun A hA => le_sSup (map_conj_mem_famG hA g
      (fun a ha => (Subgroup.mem_normalizer_iff.mp hg a).mp (hA.1 ha)))
  exact hle ⟨x, hx, rfl⟩

theorem le_normalizer_jG_of_le {H S Q : Subgroup G} {i : ℕ} (hQS : Q ≤ S)
    (hHQ : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) (hle : ∀ B ∈ famG S i, B ≤ Q) :
    H ≤ normalizer (jG S i : Set G) := by
  intro h hh
  refine Sec3.mem_normalizer_of_conj_mem fun x hx => ?_
  have hle' : (jG S i).map (MulAut.conj h).toMonoidHom ≤ jG S i := by
    rw [jG, (Subgroup.gc_map_comap (MulAut.conj h).toMonoidHom).l_sSup]
    exact iSup₂_le fun A hA => le_sSup (map_conj_mem_famG hA h
      (fun a ha => hQS (hHQ h hh a (hle A hA ha))))
  exact hle' ⟨x, hx, rfl⟩

theorem mem_normalizer_of_forall_conj_eq {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ = x) : g ∈ normalizer (X : Set G) :=
  Sec3.mem_normalizer_of_conj_mem fun x hx => by rw [h x hx]; exact hx

omit [Finite G] in
theorem fourChar_zero (S : Subgroup G) : fourChar S 0 = omegaG S := by
  change (CFSG.omegaOneCenter (⊤ : Subgroup S)).map S.subtype = _
  rw [map_omegaOneCenter, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem fourChar_one (S : Subgroup G) : fourChar S 1 = jG S 0 :=
  map_higherElemThompson S 0

theorem fourChar_two (S : Subgroup G) : fourChar S 2 = omegaG (jG S 1) := by
  change (CFSG.omegaOneCenter (CFSG.higherElemThompson S 1)).map S.subtype = _
  rw [map_omegaOneCenter, map_higherElemThompson]

theorem fourChar_three (S : Subgroup G) : fourChar S 3 = omegaG (jG S 2) := by
  change (CFSG.omegaOneCenter (CFSG.higherElemThompson S 2)).map S.subtype = _
  rw [map_omegaOneCenter, map_higherElemThompson]

omit [Finite G] in
theorem threeOfFourNormal_of_ne {H : Subgroup G} {T : Fin 4 → Subgroup G} (k : Fin 4)
    (h : ∀ i, i ≠ k → H ≤ normalizer (T i : Set G)) : ThreeOfFourNormal H T := by
  intro i j hij
  by_cases hik : i = k
  · subst hik
    exact Or.inr (h j (Ne.symm hij))
  · exact Or.inl (h i hik)

omit [Finite G] in
theorem mem_omegaOneCenter_top_iff {S : Type*} [Group S] (z : S) :
    z ∈ CFSG.omegaOneCenter (⊤ : Subgroup S) ↔ z ∈ Subgroup.center S ∧ z ^ 2 = 1 := by
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    refine ⟨Subgroup.mem_center_iff.mpr fun y => ?_, hz⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, Subgroup.mem_top y⟩)
  · rintro ⟨hz, hz2⟩
    refine ⟨⟨⟨z, Subgroup.mem_top z⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩,
      hz2⟩
    exact Subgroup.mem_center_iff.mp hz y

omit [Finite G] in
theorem omegaOneCenter_top_characteristic {S : Type*} [Group S] :
    (CFSG.omegaOneCenter (⊤ : Subgroup S)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  rintro φ _ ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff] at hz
  rw [mem_omegaOneCenter_top_iff]
  refine ⟨Subgroup.mem_center_iff.mpr fun y => ?_, by
    change φ z ^ 2 = 1
    rw [← map_pow, hz.2, map_one]⟩
  obtain ⟨y, rfl⟩ := φ.surjective y
  change φ y * φ z = φ z * φ y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz.1 y]

omit [Finite G] in
theorem higherElemThompson_characteristic {S : Type*} [Group S] [Finite S] (j : ℕ) :
    (CFSG.higherElemThompson S j).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro ϕ
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun A hA => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ?_
  rw [CFSG.mem_higherElemThompsonFamily_iff] at hA ⊢
  obtain ⟨hAe, hAc⟩ := hA
  have := hAe
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨IsElementaryAbelian.map ϕ.toMonoidHom,
    by rw [Subgroup.card_map_of_injective ϕ.injective, hAc]⟩

theorem omegaG_ne_bot {S : Subgroup G} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) : omegaG S ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
  have hZ := hS2.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    obtain ⟨k, hk⟩ := (IsPGroup.of_equiv (hS2.to_subgroup (Subgroup.center S))
      (MulEquiv.refl _)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center S) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    exact dvd_pow_self 2 (by rintro rfl; simp at h1)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  intro hbot
  have hmem : (((z : S) : G)) ∈ omegaG S := by
    refine ⟨(z : S).2, fun x hx => ?_, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩).symm
    · have h2 : z ^ 2 = 1 := by
        rw [← hz]
        exact pow_orderOf_eq_one z
      have h3 := congrArg (fun x : Subgroup.center S => ((x : S) : G)) h2
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
      rwa [pow_two] at h3
  rw [hbot, Subgroup.mem_bot] at hmem
  have : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem exists_mem_famG_zero (S : Subgroup G) : ∃ A, A ∈ famG S 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := {r : ℕ | ∃ B : Subgroup S, CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 2 ^ r}
    with hX
  have hbot : IsElemTwo (⊥ : Subgroup G) :=
    ⟨fun a ha b hb => by rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb],
      fun a ha => by rw [Subgroup.mem_bot.mp ha, one_mul]⟩
  have hne : X.Nonempty := ⟨0, (⊥ : Subgroup G).subgroupOf S,
    isElementaryAbelian_of_isElemTwo hbot, by
      rw [pow_zero, Subgroup.card_eq_one, Subgroup.bot_subgroupOf]⟩
  have hbdd : BddAbove X := by
    refine ⟨Nat.card S, fun r ⟨B, _, hB⟩ => ?_⟩
    have h1 : 2 ^ r ≤ Nat.card S := hB ▸ Subgroup.card_le_card_group B
    exact (Nat.lt_two_pow_self).le.trans h1
  obtain ⟨B, hB, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨B.map S.subtype, Subgroup.map_subtype_le B, isElemTwo_map_of_isElementaryAbelian hB, ?_⟩
  rw [Subgroup.card_map_of_injective S.subtype_injective, hcard, Nat.sub_zero]
  rfl

theorem jG_zero_ne_bot {S : Subgroup G} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) : jG S 0 ≠ ⊥ := by
  obtain ⟨A, hA⟩ := exists_mem_famG_zero S
  have hZ := omegaG_ne_bot hS2 hS1
  have : Nontrivial (omegaG S) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ
  have h2 : 1 < Nat.card (omegaG S) := Finite.one_lt_card_iff_nontrivial.mpr this
  have hle := card_le_two_pow_pRank (omegaG_le S) (isElemTwo_omegaG S)
  intro hbot
  have hAle : A ≤ ⊥ := hbot ▸ le_jG hA
  have hAc := hA.2.2
  rw [le_bot_iff.mp hAle, Subgroup.card_bot, Nat.sub_zero] at hAc
  omega

omit [Finite G] in
theorem inv_mul_mem_of_relIndex_eq_two {Q S : Subgroup G} (hrel : Q.relIndex S = 2) {x y : G}
    (hx : x ∈ S) (hy : y ∈ S) (hxQ : x ∉ Q) (hyQ : y ∉ Q) : x⁻¹ * y ∈ Q := by
  have hidx : (Q.subgroupOf S).index = 2 := hrel
  have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x⁻¹, S.inv_mem hx⟩)
    (b := ⟨y, hy⟩)).mpr ⟨fun h => absurd (by simpa using Q.inv_mem (Subgroup.mem_subgroupOf.mp h))
      hxQ, fun h => absurd (Subgroup.mem_subgroupOf.mp h) hyQ⟩
  exact Subgroup.mem_subgroupOf.mp h

omit [Finite G] in
theorem card_le_two_mul_card_inf {Q S A : Subgroup G} (hrel : Q.relIndex S = 2) (hAS : A ≤ S) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Q) := by
  have h1 := Subgroup.relIndex_mul_card Q A
  have h2 : Q.relIndex A ≤ 2 := by
    rw [← hrel]
    exact Subgroup.relIndex_le_of_le_right hAS (by rw [hrel]; norm_num)
  rw [inf_comm] at h1
  calc Nat.card A = Q.relIndex A * Nat.card ↥(A ⊓ Q) := h1.symm
    _ ≤ 2 * Nat.card ↥(A ⊓ Q) := Nat.mul_le_mul_right _ h2

theorem relIndex_centralizer_mul_card_le {S W D : Subgroup G} (hWS : W ≤ S) (hDS : D ≤ S)
    (hW : IsElemTwo W) (hD : IsElemTwo D) (hWD : ∀ d ∈ D, ∀ w ∈ W, d * w = w * d) {a : G}
    (haD : ∀ d ∈ D, a * d = d * a) :
    (centralizer ({a} : Set G)).relIndex W * Nat.card D ≤ 2 ^ CFSG.pRank 2 S := by
  have hDC : D ≤ centralizer ({a} : Set G) := fun d hd => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (haD d hd).symm
  have h1 : (centralizer ({a} : Set G)).relIndex W ≤ D.relIndex W :=
    Subgroup.relIndex_le_of_le_left hDC (relIndex_ne_zero_of_finite _ _)
  have h2 := Subgroup.relIndex_mul_card D W
  have h3 := card_sup_mul_card_inf_of_commute hWD
  have h4 := card_le_two_pow_pRank (sup_le hDS hWS) (isElemTwo_sup hD hW hWD)
  have hpos : 0 < Nat.card ↥(D ⊓ W) := Nat.card_pos
  have key : D.relIndex W * Nat.card D * Nat.card ↥(D ⊓ W) ≤
      2 ^ CFSG.pRank 2 S * Nat.card ↥(D ⊓ W) := by
    calc D.relIndex W * Nat.card D * Nat.card ↥(D ⊓ W)
        = (D.relIndex W * Nat.card ↥(D ⊓ W)) * Nat.card D := by ring
      _ = Nat.card W * Nat.card D := by rw [h2]
      _ = Nat.card ↥(D ⊔ W) * Nat.card ↥(D ⊓ W) := by rw [h3, mul_comm]
      _ ≤ 2 ^ CFSG.pRank 2 S * Nat.card ↥(D ⊓ W) := Nat.mul_le_mul_right _ h4
  calc _ ≤ D.relIndex W * Nat.card D := Nat.mul_le_mul_right _ h1
    _ ≤ _ := Nat.le_of_mul_le_mul_right key hpos

theorem le_two_pow_of_mul_le {r d m i : ℕ} (h : r * d ≤ 2 ^ m) (hd : 2 ^ (m - i) ≤ d)
    (hi : i ≤ m) : r ≤ 2 ^ i := by
  have hm : 2 ^ m = 2 ^ i * 2 ^ (m - i) := by rw [← pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (m - i) := by positivity
  have : r * 2 ^ (m - i) ≤ 2 ^ i * 2 ^ (m - i) :=
    (Nat.mul_le_mul_left r hd).trans (h.trans hm.le)
  exact Nat.le_of_mul_le_mul_right this hpos

structure Setting (H Q S L : Subgroup G) : Prop where
  le_S : Q ≤ S
  S_le : S ≤ H
  isPGroup_S : IsPGroup 2 S
  relIndex_eq : Q.relIndex S = 2
  conj_mem : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q
  mem_of_commute : ∀ x ∈ H, (∀ q ∈ Q, x * q = q * x) → x ∈ Q
  le_of_normal : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) →
    IsPGroup 2 K → K ≤ Q
  L_le : L ≤ H
  gen : ∀ X : Subgroup G, L ≤ normalizer (X : Set G) →
    normalizer (S : Set G) ≤ normalizer (X : Set G) → H ≤ normalizer (X : Set G)

@[expose] def ModuleBound (H Q S L : Subgroup G) (k : ℕ) : Prop :=
  ∀ W : Subgroup G, W ≤ Q → (∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W) → IsElemTwo W →
    (∃ l ∈ L, ∃ w ∈ W, l * w * l⁻¹ ≠ w) → ∀ a ∈ S, a ∉ Q →
      k ≤ (centralizer ({a} : Set G)).relIndex W

variable {H Q S L : Subgroup G}

omit [Finite G] in
theorem Setting.isPGroup_Q (hs : Setting H Q S L) : IsPGroup 2 Q :=
  hs.isPGroup_S.to_le hs.le_S

omit [Finite G] in
theorem Setting.not_le_normalizer (hs : Setting H Q S L) : ¬ L ≤ normalizer (S : Set G) := by
  intro hLS
  have hHS := hs.gen S hLS le_rfl
  have hSQ : S ≤ Q := hs.le_of_normal S hs.S_le
    (fun h hh x hx => (Subgroup.mem_normalizer_iff.mp (hHS hh) x).mp hx) hs.isPGroup_S
  have h1 : Q.relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSQ
  rw [hs.relIndex_eq] at h1
  exact absurd h1 (by norm_num)

omit [Finite G] in
theorem Setting.omegaG_le_omegaG (hs : Setting H Q S L) : omegaG S ≤ omegaG Q := by
  rintro z ⟨hzS, hzc, hz2⟩
  have hzQ : z ∈ Q := hs.mem_of_commute z (hs.S_le hzS) fun q hq => hzc q (hs.le_S hq)
  exact ⟨hzQ, fun x hx => hzc x (hs.le_S hx), hz2⟩

omit [Finite G] in
theorem Setting.conj_mem_omegaG_Q (hs : Setting H Q S L) {h : G} (hh : h ∈ H) {w : G}
    (hw : w ∈ omegaG Q) : h * w * h⁻¹ ∈ omegaG Q :=
  conj_mem_omegaG (fun x hx => hs.conj_mem h hh x hx)
    (fun x hx => by
      have := hs.conj_mem h⁻¹ (H.inv_mem hh) x hx
      rwa [inv_inv] at this) hw

omit [Finite G] in
theorem Setting.conj_mem_omegaG_pAt (hs : Setting H Q S L) {i : ℕ} {h : G} (hh : h ∈ H) {w : G}
    (hw : w ∈ omegaG (pAt S Q i)) : h * w * h⁻¹ ∈ omegaG (pAt S Q i) :=
  conj_mem_omegaG (fun x hx => conj_mem_pAt hs.le_S (hs.conj_mem h hh) hx)
    (fun x hx => by
      have := conj_mem_pAt hs.le_S (g := h⁻¹) (hs.conj_mem h⁻¹ (H.inv_mem hh)) hx
      rwa [inv_inv] at this) hw

theorem Setting.le_normalizer_omegaG_S (hs : Setting H Q S L)
    (hL : ∀ l ∈ L, ∀ v ∈ omegaG Q, l * v * l⁻¹ = v) : H ≤ normalizer (omegaG S : Set G) :=
  hs.gen _ (fun l hl => mem_normalizer_of_forall_conj_eq fun z hz =>
    hL l hl z (hs.omegaG_le_omegaG hz)) (normalizer_le_normalizer_omegaG S)

theorem Setting.le_of_mem_famG_of_bound (hs : Setting H Q S L) {i k : ℕ} (hk : 2 ^ (i + 1) < k)
    (hV : ∀ a ∈ S, a ∉ Q → k ≤ (centralizer ({a} : Set G)).relIndex (omegaG Q))
    {A : Subgroup G} (hA : A ∈ famG S i) : A ≤ Q := by
  by_contra hAQ
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  have hk' := hV a (hA.1 haA) haQ
  have hDel : IsElemTwo (A ⊓ Q) :=
    ⟨fun x hx y hy => hA.2.1.1 x hx.1 y hy.1, fun x hx => hA.2.1.2 x hx.1⟩
  have hb := relIndex_centralizer_mul_card_le (S := S) ((omegaG_le Q).trans hs.le_S)
    (inf_le_left.trans hA.1) (isElemTwo_omegaG Q) hDel
    (fun d hd w hw => (hw.2.1 d hd.2).symm) (a := a) (fun d hd => hA.2.1.1 a haA d hd.1)
  have hcard := card_le_two_mul_card_inf hs.relIndex_eq hA.1
  rw [hA.2.2] at hcard
  have hi : 1 ≤ CFSG.pRank 2 S - i := by
    by_contra hi
    push Not at hi
    have h0 : CFSG.pRank 2 S - i = 0 := by omega
    have hA1 := hA.2.2
    rw [h0, pow_zero, Subgroup.card_eq_one] at hA1
    exact haQ (by rw [hA1, Subgroup.mem_bot] at haA; rw [haA]; exact Q.one_mem)
  have hd : 2 ^ (CFSG.pRank 2 S - (i + 1)) ≤ Nat.card ↥(A ⊓ Q) := by
    have he : 2 ^ (CFSG.pRank 2 S - i) = 2 * 2 ^ (CFSG.pRank 2 S - (i + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hle := le_two_pow_of_mul_le hb hd (by omega)
  omega

theorem Setting.centralizes_omegaG_pAt (hs : Setting H Q S L) {i k : ℕ} (hk : 2 ^ i < k)
    (hMB : ModuleBound H Q S L k) (hi : 1 ≤ CFSG.pRank 2 S - i) {A : Subgroup G} (hAS : A ≤ S)
    (hA : IsElemTwo A) (hAQ : ¬ A ≤ Q)
    (hcard : 2 ^ (CFSG.pRank 2 S - i) ≤ Nat.card ↥(A ⊓ Q)) :
    ∀ l ∈ L, ∀ w ∈ omegaG (pAt S Q i), l * w * l⁻¹ = w := by
  by_contra hnc
  push Not at hnc
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  have hWQ : omegaG (pAt S Q i) ≤ Q := (omegaG_le _).trans (pAt_le S Q i)
  have hk' := hMB _ hWQ (fun h hh w hw => hs.conj_mem_omegaG_pAt hh hw) (isElemTwo_omegaG _)
    hnc a (hAS haA) haQ
  have hDel : IsElemTwo (A ⊓ Q) :=
    ⟨fun x hx y hy => hA.1 x hx.1 y hy.1, fun x hx => hA.2 x hx.1⟩
  have hDP : A ⊓ Q ≤ pAt S Q i := le_pAt_of_card hs.le_S inf_le_right hDel hi hcard
  have hb := relIndex_centralizer_mul_card_le (S := S) (hWQ.trans hs.le_S)
    (inf_le_left.trans hAS) (isElemTwo_omegaG _) hDel
    (fun d hd w hw => (hw.2.1 d (hDP hd)).symm) (a := a) (fun d hd => hA.1 a haA d hd.1)
  have hle := le_two_pow_of_mul_le hb hcard (by omega)
  omega

theorem mem_of_stabilizes_rel {H Q W : Subgroup G} (hQ2 : IsPGroup 2 Q) (hWQ : W ≤ Q)
    (hCQ : ∀ x ∈ H, (∀ q ∈ Q, x * q = q * x) → x ∈ Q)
    (hHQ : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) (hHW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hO2 : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsPGroup 2 K →
      K ≤ Q)
    {k : G} (hkH : k ∈ H) (hkW : ∀ w ∈ W, k * w * k⁻¹ = w)
    (hkQ : ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ W) : k ∈ Q := by
  let K : Subgroup G :=
    { carrier := {h | h ∈ H ∧ (∀ w ∈ W, h * w * h⁻¹ = w) ∧ ∀ q ∈ Q, h * q * h⁻¹ * q⁻¹ ∈ W}
      one_mem' := ⟨H.one_mem, fun w _ => by group, fun q _ => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact W.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haH, haW, haQ⟩ ⟨hbH, hbW, hbQ⟩
        refine ⟨H.mul_mem haH hbH, fun w hw => ?_, fun q hq => ?_⟩
        · calc a * b * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
            _ = w := by rw [hbW w hw, haW w hw]
        · have h1 := hbQ q hq
          have h2 := haQ q hq
          have h3 : a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ = b * q * b⁻¹ * q⁻¹ := haW _ h1
          rw [show a * b * q * (a * b)⁻¹ * q⁻¹ =
              a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ * (a * q * a⁻¹ * q⁻¹) by group, h3]
          exact W.mul_mem h1 h2
      inv_mem' := by
        rintro a ⟨haH, haW, haQ⟩
        refine ⟨H.inv_mem haH, fun w hw => ?_, fun q hq => ?_⟩
        · have hw' : a⁻¹ * w * a ∈ W := by
            have := hHW a⁻¹ (H.inv_mem haH) w hw
            rwa [inv_inv] at this
          have := haW _ hw'
          calc a⁻¹ * w * a⁻¹⁻¹ = a⁻¹ * w * a := by group
            _ = a * (a⁻¹ * w * a) * a⁻¹ := this.symm
            _ = w := by group
        · have hq' : a⁻¹ * q * a ∈ Q := by
            have := hHQ a⁻¹ (H.inv_mem haH) q hq
            rwa [inv_inv] at this
          have h1 := haQ _ hq'
          have : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = (a * (a⁻¹ * q * a) * a⁻¹ * (a⁻¹ * q * a)⁻¹)⁻¹ := by
            group
          rw [this]
          exact W.inv_mem h1 }
  have hKH : K ≤ H := fun h hh => hh.1
  have hKn : ∀ h ∈ H, ∀ x ∈ K, h * x * h⁻¹ ∈ K := by
    rintro g hg x ⟨hxH, hxW, hxQ⟩
    refine ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), fun w hw => ?_, fun q hq => ?_⟩
    · have hw' : g⁻¹ * w * g ∈ W := by
        have := hHW g⁻¹ (H.inv_mem hg) w hw
        rwa [inv_inv] at this
      calc g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ = g * (x * (g⁻¹ * w * g) * x⁻¹) * g⁻¹ := by group
        _ = w := by rw [hxW _ hw']; group
    · have hq' : g⁻¹ * q * g ∈ Q := by
        have := hHQ g⁻¹ (H.inv_mem hg) q hq
        rwa [inv_inv] at this
      have h1 := hHW g hg _ (hxQ _ hq')
      have : g * x * g⁻¹ * q * (g * x * g⁻¹)⁻¹ * q⁻¹ =
          g * (x * (g⁻¹ * q * g) * x⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ := by group
      rw [this]
      exact h1
  have hK2 : IsPGroup 2 K := by
    intro x
    have hne : orderOf (x : G) ≠ 0 := (orderOf_pos (x : G)).ne'
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd hne
    set y : G := (x : G) ^ (2 ^ a) with hydef
    have hyK : y ∈ K := K.pow_mem x.2 _
    have hyord : orderOf y = m := by
      rw [hydef, orderOf_pow' _ (by positivity), hord, Nat.gcd_mul_right_left]
      rw [Nat.mul_div_cancel_left _ (by positivity)]
    have hycent : ∀ q ∈ Q, y * q * y⁻¹ = q := fun q hq =>
      commute_of_odd_of_stabilizes hQ2 hWQ (by rw [hyord]; exact hm) hyK.2.2 hyK.2.1 hq
    have hyQ : y ∈ Q := by
      refine hCQ y hyK.1 fun q hq => ?_
      have := hycent q hq
      calc y * q = y * q * y⁻¹ * y := by group
        _ = q * y := by rw [this]
    obtain ⟨j, hj⟩ := hQ2 ⟨y, hyQ⟩
    have hyj : y ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have hdvd : m ∣ 2 ^ j := hyord ▸ orderOf_dvd_of_pow_eq_one hyj
    have hm1 : m = 1 := by
      have hcop : Nat.Coprime m (2 ^ j) :=
        Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hm)
      exact Nat.Coprime.eq_one_of_dvd hcop hdvd
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hydef]
    rw [← orderOf_eq_one_iff, hyord, hm1]
  exact hO2 K hKH hKn hK2 ⟨hkH, hkW, hkQ⟩

theorem Setting.le_normalizer_omegaG_jG (hs : Setting H Q S L) {i : ℕ}
    (hi : 1 ≤ CFSG.pRank 2 S - i) {B : Subgroup G} (hB : B ∈ famG S i) (hBQ : B ≤ Q)
    (hLW : ∀ l ∈ L, ∀ w ∈ omegaG (pAt S Q i), l * w * l⁻¹ = w) :
    H ≤ normalizer (omegaG (jG S i) : Set G) := by
  set E := omegaG (jG S i) with hEdef
  set W := omegaG (pAt S Q i) with hWdef
  have hES : E ≤ S := (omegaG_le _).trans (jG_le S i)
  have hWQ : W ≤ Q := (omegaG_le _).trans (pAt_le S Q i)
  have hEW : ∀ e ∈ E, e ∈ Q → e ∈ W := by
    intro e he heQ
    refine ⟨?_, fun x hx => he.2.1 x (pAt_le_jG S Q i hx), he.2.2⟩
    have hcomm : ∀ x ∈ Subgroup.zpowers e, ∀ b ∈ B, x * b = b * x := by
      intro x hx b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((Commute.zpow_left (he.2.1 b (le_jG hB hb)) n)).eq
    have he2 : IsElemTwo (Subgroup.zpowers e) := by
      refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
      · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← zpow_add, ← zpow_add, add_comm]
      · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← zpow_add, ← two_mul, zpow_mul, show e ^ (2 : ℤ) = 1 by
          rw [zpow_two]; exact he.2.2, one_zpow]
    have hD : IsElemTwo (Subgroup.zpowers e ⊔ B) := isElemTwo_sup he2 hB.2.1 hcomm
    have hDQ : Subgroup.zpowers e ⊔ B ≤ Q := sup_le (Subgroup.zpowers_le.mpr heQ) hBQ
    have hDcard : 2 ^ (CFSG.pRank 2 S - i) ≤ Nat.card ↥(Subgroup.zpowers e ⊔ B) := by
      rw [← hB.2.2]
      exact Subgroup.card_le_of_le le_sup_right
    exact le_pAt_of_card hs.le_S hDQ hD hi hDcard
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers e))
  have hEc : ∀ e ∈ E, e ∈ centralizer (W : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => (he.2.1 w (pAt_le_jG S Q i (omegaG_le _ hw))).symm
  have hEQW : ∀ e ∈ E, ∀ q ∈ Q, e * q * e⁻¹ * q⁻¹ ∈ W := by
    intro e he q hq
    have h1 : q * e⁻¹ * q⁻¹ ∈ E := conj_mem_omegaG_jG (hs.le_S hq) (E.inv_mem he)
    have h2 : e * q * e⁻¹ * q⁻¹ ∈ E := by
      rw [show e * q * e⁻¹ * q⁻¹ = e * (q * e⁻¹ * q⁻¹) by group]
      exact E.mul_mem he h1
    have h3 : e * q * e⁻¹ * q⁻¹ ∈ Q :=
      Q.mul_mem (hs.conj_mem e (hs.S_le (hES he)) q hq) (Q.inv_mem hq)
    exact hEW _ h2 h3
  have hLc : ∀ l ∈ L, l ∈ centralizer (W : Set G) := fun l hl =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      have := hLW l hl w hw
      calc w * l = l * w * l⁻¹ * l := by rw [this]
        _ = l * w := by group
  have hLE : ∀ l ∈ L, ∀ e ∈ E, l * e * l⁻¹ * e⁻¹ ∈ Q := by
    intro l hl e he
    have hlH := hs.L_le hl
    have heH := hs.S_le (hES he)
    have hxc : l * e * l⁻¹ * e⁻¹ ∈ centralizer (W : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLc l hl) (hEc e he))
        (Subgroup.inv_mem _ (hLc l hl))) (Subgroup.inv_mem _ (hEc e he))
    refine mem_of_stabilizes_rel hs.isPGroup_Q hWQ hs.mem_of_commute hs.conj_mem
      (fun h hh w hw => hs.conj_mem_omegaG_pAt hh hw) hs.le_of_normal
      (H.mul_mem (H.mul_mem (H.mul_mem hlH heH) (H.inv_mem hlH)) (H.inv_mem heH))
      (fun w hw => ?_) (fun q hq => ?_)
    · have := Subgroup.mem_centralizer_iff.mp hxc w hw
      calc l * e * l⁻¹ * e⁻¹ * w * (l * e * l⁻¹ * e⁻¹)⁻¹
          = w * (l * e * l⁻¹ * e⁻¹) * (l * e * l⁻¹ * e⁻¹)⁻¹ := by rw [this]
        _ = w := by group
    ·
      have hq' : l⁻¹ * q * l ∈ Q := by
        have := hs.conj_mem l⁻¹ (H.inv_mem hlH) q hq
        rwa [inv_inv] at this
      have hy : l * e * l⁻¹ * q * (l * e * l⁻¹)⁻¹ * q⁻¹ ∈ W := by
        have h1 := hEQW e he _ hq'
        have h2 : l * (e * (l⁻¹ * q * l) * e⁻¹ * (l⁻¹ * q * l)⁻¹) * l⁻¹ ∈ W :=
          hs.conj_mem_omegaG_pAt hlH h1
        rw [show l * e * l⁻¹ * q * (l * e * l⁻¹)⁻¹ * q⁻¹ =
          l * (e * (l⁻¹ * q * l) * e⁻¹ * (l⁻¹ * q * l)⁻¹) * l⁻¹ by group]
        exact h2
      have hz : e⁻¹ * q * e⁻¹⁻¹ * q⁻¹ ∈ W := hEQW e⁻¹ (E.inv_mem he) q hq
      have hyW : l * e * l⁻¹ * (e⁻¹ * q * e⁻¹⁻¹ * q⁻¹) * (l * e * l⁻¹)⁻¹ ∈ W :=
        hs.conj_mem_omegaG_pAt (H.mul_mem (H.mul_mem hlH heH) (H.inv_mem hlH)) hz
      rw [show l * e * l⁻¹ * e⁻¹ * q * (l * e * l⁻¹ * e⁻¹)⁻¹ * q⁻¹ =
        (l * e * l⁻¹ * (e⁻¹ * q * e⁻¹⁻¹ * q⁻¹) * (l * e * l⁻¹)⁻¹) *
          (l * e * l⁻¹ * q * (l * e * l⁻¹)⁻¹ * q⁻¹) by group]
      exact W.mul_mem hyW hy
  have hEQ : E ≤ Q := by
    by_contra hEQ
    obtain ⟨e₀, he₀, he₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp hEQ
    apply hs.not_le_normalizer
    intro l hl
    refine Sec3.mem_normalizer_of_conj_mem fun x hx => ?_
    by_cases hxQ : x ∈ Q
    · exact hs.le_S (hs.conj_mem l (hs.L_le hl) x hxQ)
    · have h1 := inv_mul_mem_of_relIndex_eq_two hs.relIndex_eq (hES he₀) hx he₀Q hxQ
      have h2 := hLE l hl e₀ he₀
      rw [show l * x * l⁻¹ = (l * e₀ * l⁻¹ * e₀⁻¹) * e₀ * (l * (e₀⁻¹ * x) * l⁻¹) by group]
      exact S.mul_mem (S.mul_mem (hs.le_S h2) (hES he₀))
        (hs.le_S (hs.conj_mem l (hs.L_le hl) _ h1))
  exact hs.gen E (fun l hl => mem_normalizer_of_forall_conj_eq fun e he =>
    hLW l hl e (hEW e he (hEQ he)))
    ((normalizer_le_normalizer_jG S i).trans (normalizer_le_normalizer_omegaG _))

omit [Finite G] in
theorem Setting.pow_le_card_inf (hs : Setting H Q S L) {i j : ℕ} (hji : j < i) {A : Subgroup G}
    (hA : A ∈ famG S j) (hAQ : ¬ A ≤ Q) :
    2 ^ (CFSG.pRank 2 S - i) ≤ Nat.card ↥(A ⊓ Q) := by
  have hcard := card_le_two_mul_card_inf hs.relIndex_eq hA.1
  rw [hA.2.2] at hcard
  have hj : 1 ≤ CFSG.pRank 2 S - j := by
    by_contra hj
    push Not at hj
    have h0 : CFSG.pRank 2 S - j = 0 := by omega
    have hA1 := hA.2.2
    rw [h0, pow_zero, Subgroup.card_eq_one] at hA1
    exact hAQ (by rw [hA1]; exact bot_le)
  have he : 2 ^ (CFSG.pRank 2 S - j) = 2 * 2 ^ (CFSG.pRank 2 S - j - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hle : 2 ^ (CFSG.pRank 2 S - i) ≤ 2 ^ (CFSG.pRank 2 S - j - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem Setting.le_normalizer_omegaG_jG_of_not_le (hs : Setting H Q S L) {i j k : ℕ}
    (hk : 2 ^ i < k) (hMB : ModuleBound H Q S L k) (hji : j < i) {A : Subgroup G}
    (hA : A ∈ famG S j) (hAQ : ¬ A ≤ Q) : H ≤ normalizer (omegaG (jG S i) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hm : CFSG.pRank 2 S - i = 0
  · have hbot : omegaG (jG S i) = ⊥ := by
      rw [jG_eq_bot_of_pRank_sub_eq_zero hm]
      exact le_bot_iff.mp (omegaG_le ⊥)
    rw [hbot, Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]
    exact le_top
  have hi : 1 ≤ CFSG.pRank 2 S - i := Nat.one_le_iff_ne_zero.mpr hm
  have hcard := hs.pow_le_card_inf hji hA hAQ
  have hDel : IsElemTwo (A ⊓ Q) :=
    ⟨fun x hx y hy => hA.2.1.1 x hx.1 y hy.1, fun x hx => hA.2.1.2 x hx.1⟩
  have hLW := hs.centralizes_omegaG_pAt hk hMB hi hA.1 hA.2.1 hAQ hcard
  obtain ⟨r, hr⟩ := (isPGroup_of_isElemTwo hDel).exists_card_eq
  have hdvd : 2 ^ (CFSG.pRank 2 S - i) ∣ Nat.card ↥(A ⊓ Q) := by
    rw [hr]
    apply Nat.pow_dvd_pow
    rw [hr] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  obtain ⟨B, hB, -, hBD⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := ⊥) (by rw [Subgroup.card_bot]; exact one_dvd _) hdvd bot_le
  have hBfam : B ∈ famG S i :=
    ⟨hBD.trans (inf_le_left.trans hA.1), ⟨fun x hx y hy => hDel.1 x (hBD hx) y (hBD hy),
      fun x hx => hDel.2 x (hBD hx)⟩, hB⟩
  exact hs.le_normalizer_omegaG_jG hi hBfam (hBD.trans inf_le_right) hLW

theorem Setting.part_one (hs : Setting H Q S L) (hMB : ModuleBound H Q S L 4) :
    ∃ C : Subgroup S, C.Characteristic ∧ C ≠ ⊥ ∧
      H ≤ normalizer ((C.map S.subtype : Subgroup G) : Set G) := by
  have hS1 : S ≠ ⊥ := by
    intro hbot
    have h1 : Q.relIndex S = 1 := Subgroup.relIndex_eq_one.mpr (by rw [hbot]; exact bot_le)
    rw [hs.relIndex_eq] at h1
    exact absurd h1 (by norm_num)
  by_cases hL : ∀ l ∈ L, ∀ v ∈ omegaG Q, l * v * l⁻¹ = v
  · refine ⟨CFSG.omegaOneCenter (⊤ : Subgroup S), omegaOneCenter_top_characteristic, ?_, ?_⟩
    · intro hbot
      apply omegaG_ne_bot hs.isPGroup_S hS1
      rw [← fourChar_zero]
      change (CFSG.omegaOneCenter (⊤ : Subgroup S)).map S.subtype = ⊥
      rw [hbot, Subgroup.map_bot]
    · have h0 : (CFSG.omegaOneCenter (⊤ : Subgroup S)).map S.subtype = omegaG S :=
        fourChar_zero S
      rw [h0]
      exact hs.le_normalizer_omegaG_S hL
  · push Not at hL
    have hV : ∀ a ∈ S, a ∉ Q → 4 ≤ (centralizer ({a} : Set G)).relIndex (omegaG Q) :=
      hMB _ (omegaG_le Q) (fun h hh w hw => hs.conj_mem_omegaG_Q hh hw) (isElemTwo_omegaG Q) hL
    have hle : ∀ A ∈ famG S 0, A ≤ Q := fun A hA =>
      hs.le_of_mem_famG_of_bound (by norm_num) hV hA
    refine ⟨CFSG.higherElemThompson S 0, higherElemThompson_characteristic 0, ?_, ?_⟩
    · intro hbot
      apply jG_zero_ne_bot hs.isPGroup_S hS1
      rw [← map_higherElemThompson, hbot, Subgroup.map_bot]
    · rw [map_higherElemThompson]
      exact le_normalizer_jG_of_le hs.le_S hs.conj_mem hle

theorem Setting.part_two (hs : Setting H Q S L) (hMB : ModuleBound H Q S L 16) :
    ThreeOfFourNormal H (fourChar S) := by
  have hnorm : ∀ i, (∀ A ∈ famG S i, A ≤ Q) → H ≤ normalizer (omegaG (jG S i) : Set G) :=
    fun i hle => (le_normalizer_jG_of_le hs.le_S hs.conj_mem hle).trans
      (normalizer_le_normalizer_omegaG _)
  by_cases hL : ∀ l ∈ L, ∀ v ∈ omegaG Q, l * v * l⁻¹ = v
  · have h0 : H ≤ normalizer (fourChar S 0 : Set G) := by
      rw [fourChar_zero]
      exact hs.le_normalizer_omegaG_S hL
    by_cases h𝓐 : ∀ A ∈ famG S 0, A ≤ Q
    · have h1 : H ≤ normalizer (fourChar S 1 : Set G) := by
        rw [fourChar_one]
        exact le_normalizer_jG_of_le hs.le_S hs.conj_mem h𝓐
      by_cases h𝓐₁ : ∀ A ∈ famG S 1, A ≤ Q
      · have h2 : H ≤ normalizer (fourChar S 2 : Set G) := by
          rw [fourChar_two]
          exact hnorm 1 h𝓐₁
        refine threeOfFourNormal_of_ne 3 fun i hi => ?_
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact absurd rfl hi
      · push Not at h𝓐₁
        obtain ⟨A, hA, hAQ⟩ := h𝓐₁
        have h3 : H ≤ normalizer (fourChar S 3 : Set G) := by
          rw [fourChar_three]
          exact hs.le_normalizer_omegaG_jG_of_not_le (by norm_num) hMB (by norm_num : 1 < 2)
            hA hAQ
        refine threeOfFourNormal_of_ne 2 fun i hi => ?_
        fin_cases i
        · exact h0
        · exact h1
        · exact absurd rfl hi
        · exact h3
    · push Not at h𝓐
      obtain ⟨A, hA, hAQ⟩ := h𝓐
      have h2 : H ≤ normalizer (fourChar S 2 : Set G) := by
        rw [fourChar_two]
        exact hs.le_normalizer_omegaG_jG_of_not_le (by norm_num) hMB (by norm_num : 0 < 1)
          hA hAQ
      have h3 : H ≤ normalizer (fourChar S 3 : Set G) := by
        rw [fourChar_three]
        exact hs.le_normalizer_omegaG_jG_of_not_le (by norm_num) hMB (by norm_num : 0 < 2)
          hA hAQ
      refine threeOfFourNormal_of_ne 1 fun i hi => ?_
      fin_cases i
      · exact h0
      · exact absurd rfl hi
      · exact h2
      · exact h3
  · push Not at hL
    have hV : ∀ a ∈ S, a ∉ Q → 16 ≤ (centralizer ({a} : Set G)).relIndex (omegaG Q) :=
      hMB _ (omegaG_le Q) (fun h hh w hw => hs.conj_mem_omegaG_Q hh hw) (isElemTwo_omegaG Q) hL
    have hle : ∀ i ≤ 2, ∀ A ∈ famG S i, A ≤ Q := fun i hi A hA =>
      hs.le_of_mem_famG_of_bound (by
        calc 2 ^ (i + 1) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ < 16 := by norm_num) hV hA
    have h1 : H ≤ normalizer (fourChar S 1 : Set G) := by
      rw [fourChar_one]
      exact le_normalizer_jG_of_le hs.le_S hs.conj_mem (hle 0 (by norm_num))
    have h2 : H ≤ normalizer (fourChar S 2 : Set G) := by
      rw [fourChar_two]
      exact hnorm 1 (hle 1 (by norm_num))
    have h3 : H ≤ normalizer (fourChar S 3 : Set G) := by
      rw [fourChar_three]
      exact hnorm 2 (hle 2 le_rfl)
    refine threeOfFourNormal_of_ne 0 fun i hi => ?_
    fin_cases i
    · exact absurd rfl hi
    · exact h1
    · exact h2
    · exact h3

end Item181ThreeProof

end CFSG.RankThree.PartTwo.Sec18

module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WPoint
import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofPGL
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1411W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

namespace YFrame

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

@[expose] noncomputable def pbY (U : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)) (Z : Subgroup G) :
    Subgroup G :=
  (U.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype ⊓ Z

theorem mem_pbY {U : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} {Z : Subgroup G} {g : G} :
    g ∈ pbY U Z ↔
      ∃ hg : g ∈ Y ⊔ A, QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ ∈ U ∧ g ∈ Z := by
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hZ⟩
    exact ⟨k.2, hk, hZ⟩
  · rintro ⟨hg, hU, hZ⟩
    exact ⟨⟨⟨g, hg⟩, hU, rfl⟩, hZ⟩

theorem mk_mem_img_A {a : G} (ha : a ∈ A) :
    QuotientGroup.mk' (ker148 A Y) ⟨a, (le_sup_right : A ≤ Y ⊔ A) ha⟩ ∈ img148 A Y A :=
  ⟨⟨a, (le_sup_right : A ≤ Y ⊔ A) ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

theorem le_normalizer_pbY {U : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} {Z : Subgroup G}
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hAU : img148 A Y A ≤ Subgroup.normalizer (U : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    A ≤ Subgroup.normalizer (pbY U Z : Set G) := by
  intro a ha
  refine Subgroup.mem_normalizer_fintype fun g hg => ?_
  obtain ⟨hgK, hgU, hgZ⟩ := mem_pbY.mp hg
  have haKA : a ∈ Y ⊔ A := (le_sup_right : A ≤ Y ⊔ A) ha
  refine mem_pbY.mpr ⟨mul_mem (mul_mem haKA hgK) (inv_mem haKA), ?_,
    (Subgroup.mem_normalizer_iff.mp (hAZ ha) g).mp hgZ⟩
  have h := (Subgroup.mem_normalizer_iff.mp (hAU (mk_mem_img_A ha)) _).mp hgU
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact h

theorem le_pbY_img {X Z : Subgroup G} (hXK : X ≤ Y ⊔ A) (hXZ : X ≤ Z) :
    X ≤ pbY (img148 A Y X) Z := fun x hx =>
  mem_pbY.mpr ⟨hXK hx, ⟨⟨x, hXK hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, hXZ hx⟩

theorem img_map_conj {X : Subgroup G} (hX : X ≤ Y ⊔ A) {n : G} (hn : n ∈ Y ⊔ A) :
    img148 A Y (X.map (MulAut.conj n).toMonoidHom) =
      (img148 A Y X).map
        (MulAut.conj (QuotientGroup.mk' (ker148 A Y) ⟨n, hn⟩)).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_subgroupOf.mp hk
    refine ⟨QuotientGroup.mk' (ker148 A Y) ⟨x, hX hx⟩,
      ⟨⟨x, hX hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa using hxk
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨⟨n, hn⟩ * k * ⟨n, hn⟩⁻¹, Subgroup.mem_subgroupOf.mpr
      ⟨(k : G), Subgroup.mem_subgroupOf.mp hk, by simp⟩, ?_⟩
    simp [map_mul, map_inv]

theorem img_le_normalizer_img {U V : Subgroup G} (hUV : U ≤ Subgroup.normalizer (V : Set G)) :
    img148 A Y U ≤ Subgroup.normalizer (img148 A Y V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  have h1 : U.subgroupOf (Y ⊔ A) ≤
      Subgroup.normalizer (V.subgroupOf (Y ⊔ A) : Set ↥(Y ⊔ A)) := by
    intro u hu
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hv ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hUV (Subgroup.mem_subgroupOf.mp hu)) v).mp hv
  exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)

theorem isPGroup_img {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) :
    IsPGroup p (img148 A Y X) :=
  hX.comap_subtype.map _

theorem img_sup {S T : Subgroup G} (hS : S ≤ Y ⊔ A) (hT : T ≤ Y ⊔ A) :
    img148 A Y (S ⊔ T) = img148 A Y S ⊔ img148 A Y T := by
  rw [img148, img148, img148, Subgroup.subgroupOf_sup hS hT, Subgroup.map_sup]

theorem eq_one_of_mem_ker {k : ↥(Y ⊔ A)} (hk : k ∈ ker148 A Y) {m : ℕ} (hkm : k ^ 3 ^ m = 1) :
    (k : G) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkO : (k : G) ∈ pPrimeCoreOf 3 Y := Subgroup.mem_subgroupOf.mp hk
  have hkm' : (k : G) ^ 3 ^ m = 1 := by
    have := congrArg Subtype.val hkm
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have h1 : orderOf (k : G) ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hkm'
  have h2 : orderOf (k : G) ∣ Nat.card (pPrimeCoreOf 3 Y) := Subgroup.orderOf_dvd_natCard _ hkO
  have hcop : Nat.Coprime (3 ^ m) (Nat.card (pPrimeCoreOf 3 Y)) :=
    Nat.Coprime.pow_left m (coprime_card_pPrimeCoreOf 3 Y)
  have h3 : orderOf (k : G) ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem not_three_dvd_card_pbY {U : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hU : IsPGroup 2 U)
    {Z : Subgroup G} (hZY : Z ≤ Y) : ¬ 3 ∣ Nat.card (pbY U Z) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := pbY U Z) 3 h3
  have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  obtain ⟨hxK, hxU, hxZ⟩ := mem_pbY.mp x.2
  set k : ↥(Y ⊔ A) := ⟨(x : G), hxK⟩ with hk
  have hk3 : k ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxG, pow_orderOf_eq_one]
  have hq1 : QuotientGroup.mk' (ker148 A Y) k = 1 := by
    obtain ⟨j, hj⟩ := hU ⟨_, hxU⟩
    have hj' : (QuotientGroup.mk' (ker148 A Y) k) ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h3' : (QuotientGroup.mk' (ker148 A Y) k) ^ 3 = 1 := by rw [← map_pow, hk3, map_one]
    have hg : Nat.gcd 3 (2 ^ j) = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 3 2))
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3') (orderOf_dvd_of_pow_eq_one hj')
    rw [hg] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hkN : k ∈ ker148 A Y := (QuotientGroup.eq_one_iff k).mp hq1
  have h1 : (x : G) = 1 := eq_one_of_mem_ker hkN (m := 1) (by rw [pow_one]; exact hk3)
  rw [h1, orderOf_one] at hxG
  exact absurd hxG (by norm_num)

theorem maximal_img (hA3 : IsPGroup 3 A) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hQY : ∀ Z : Subgroup G, Z ≤ Y → A ≤ Subgroup.normalizer (Z : Set G) → ¬ 3 ∣ Nat.card Z →
      Z ∈ scriptQ A (lB A))
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    Maximal (InvTwo (img148 A Y A) (img148 A Y Y)) (img148 A Y S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := ker148 A Y with hN
  set q := QuotientGroup.mk' N with hq
  have hYKA : Y ≤ Y ⊔ A := le_sup_left
  have hSY : S ≤ Y := hS.prop.1.2
  have hSq : S ∈ scriptQ A (lB A) := hS.prop.1.1
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hSq.1.2.2
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
  refine ⟨⟨Subgroup.map_mono (Subgroup.comap_mono hSY), img_le_normalizer_img hAS,
    isPGroup_img hS2⟩, fun U hU hSU => ?_⟩
  obtain ⟨hUY, hAU, hU2⟩ := hU
  set Uh := pbY U Y with hUh
  have hUh3 : ¬ 3 ∣ Nat.card Uh := not_three_dvd_card_pbY hU2 le_rfl
  have hAUh : A ≤ Subgroup.normalizer (Uh : Set G) := le_normalizer_pbY hAY hAU
  have hSUh : S ≤ Uh := fun s hs =>
    mem_pbY.mpr ⟨hYKA (hSY hs), hSU ⟨⟨s, hYKA (hSY hs)⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩,
      hSY hs⟩
  obtain ⟨S', hS'syl, hSS', hAS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 hUh3 hAUh hSUh hS2 hAS
  have hS'Y : S' ≤ Y := hS'syl.1.trans inf_le_right
  have hS'3 : ¬ 3 ∣ Nat.card S' := not_three_dvd_card_of_isPGroup hS'syl.2.1
  have hS'q : S' ∈ scriptQ A (lB A) := hQY S' hS'Y hAS' hS'3
  have hS'S : S' = S := le_antisymm (hS.2 ⟨⟨hS'q, hS'Y⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two S').mpr hS'syl.2.1⟩ hSS') hSS'
  have hUhKA : Uh ≤ Y ⊔ A := inf_le_left.trans (Subgroup.map_subtype_le _)
  set f : ↥Uh →* ↥(Y ⊔ A) ⧸ N := q.comp (Subgroup.inclusion hUhKA) with hf
  have hfr : f.range = U := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨hxK, hxU, -⟩ := mem_pbY.mp x.2
      exact hxU
    · intro u hu
      obtain ⟨k, hk, rfl⟩ := hUY hu
      have hkY : (k : G) ∈ Y := Subgroup.mem_subgroupOf.mp hk
      exact ⟨⟨k, mem_pbY.mpr ⟨k.2, hu, hkY⟩⟩, rfl⟩
  have hmax : ∀ R : Subgroup G, S ≤ R → R ≤ Uh → IsPGroup 2 R → R = S := by
    intro R hSR hRU hR2
    rw [← hS'S]
    exact hS'syl.2.2 R hRU hR2 (hS'S ▸ hSR)
  have hSUh' : S ≤ Uh := hS'S ▸ hS'syl.1
  let P : Sylow 2 Uh :=
    { toSubgroup := S.subgroupOf Uh
      isPGroup' := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSUh').symm
      is_maximal' := fun {Q'} hQ' hle => by
        have h1 := hmax (Q'.map Uh.subtype)
          (fun x hx => ⟨⟨x, hSUh' hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩)
          (Subgroup.map_subtype_le Q') (hQ'.map Uh.subtype)
        ext y
        constructor
        · intro hy
          rw [Subgroup.mem_subgroupOf, ← h1]
          exact ⟨y, hy, rfl⟩
        · intro hy
          exact hle hy }
  have himg := map_sylow_eq_range_of_isPGroup f (hfr ▸ hU2) P
  rw [hfr] at himg
  rw [← himg]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨Subgroup.inclusion hUhKA x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx),
    rfl⟩

theorem exists_lift (hA3 : IsPGroup 3 A) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {ñ : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hñ : ñ ∈ img148 A Y Y ⊓ Subgroup.normalizer
      (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    ∃ n ∈ Subgroup.normalizer (A : Set G) ⊓ Y, ∃ hn : n ∈ Y ⊔ A,
      ∃ a₁ ∈ img148 A Y A, ∃ a₂ ∈ img148 A Y A,
        QuotientGroup.mk' (ker148 A Y) ⟨n, hn⟩ = a₁ * ñ * a₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set KA := Y ⊔ A with hKA
  set N := ker148 A Y with hN
  set q := QuotientGroup.mk' N with hq
  have hAKA : A ≤ KA := le_sup_right
  obtain ⟨⟨k, hk, rfl⟩, hñA⟩ := hñ
  have hyY : (k : G) ∈ Y := Subgroup.mem_subgroupOf.mp hk
  set P := pbY (img148 A Y A) (Y ⊔ A) with hP
  have hAP : A ≤ P := le_pbY_img hAKA le_sup_right
  set Ay := A.map (MulAut.conj (k : G)).toMonoidHom with hAy
  have hAyP : Ay ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp hñA (q ⟨a, hAKA ha⟩)).mp (mk_mem_img_A ha)
    rw [← map_inv, ← map_mul, ← map_mul] at hconj
    refine mem_pbY.mpr ⟨mul_mem (mul_mem k.2 (hAKA ha)) (inv_mem k.2), hconj, ?_⟩
    exact mul_mem (mul_mem (le_sup_left (a := Y) hyY) (le_sup_right (b := A) ha))
      (inv_mem (le_sup_left (a := Y) hyY))
  have hker3 : ∀ {R : Subgroup G}, IsPGroup 3 R → ∀ r ∈ R, ∀ e ∈ R, ∀ (hr : r ∈ KA)
      (he : e ∈ KA), q ⟨r, hr⟩ = q ⟨e, he⟩ → r = e := by
    intro R hR r hr e he hrK heK hre
    have hmem : (⟨r, hrK⟩ : KA) * (⟨e, heK⟩ : KA)⁻¹ ∈ N := by
      have h1 : q ((⟨r, hrK⟩ : KA) * (⟨e, heK⟩ : KA)⁻¹) = 1 := by
        rw [map_mul, map_inv, hre, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨m, hm⟩ := hR ⟨r * e⁻¹, mul_mem hr (inv_mem he)⟩
    have h1 := eq_one_of_mem_ker hmem (m := m)
      (Subtype.ext (by simpa using congrArg Subtype.val hm))
    have h2 : r * e⁻¹ = 1 := by simpa using h1
    exact mul_inv_eq_one.mp h2
  have hmaxA : ∀ R : Subgroup G, A ≤ R → R ≤ P → IsPGroup 3 R → R = A := by
    intro R hAR hRP hR3
    refine le_antisymm (fun r hr => ?_) hAR
    obtain ⟨hrK, hrA, -⟩ := mem_pbY.mp (hRP hr)
    obtain ⟨⟨e, heK⟩, he, hre⟩ := hrA
    have heA : e ∈ A := Subgroup.mem_subgroupOf.mp he
    have := hker3 hR3 r hr e (hAR heA) hrK heK hre.symm
    rw [this]
    exact heA
  have himgAy : img148 A Y Ay = img148 A Y A := by
    rw [hAy, img_map_conj hAKA k.2]
    exact Sec13.map_conj_eq_of_mem_normalizer hñA
  have hmaxAy : ∀ R : Subgroup G, Ay ≤ R → R ≤ P → IsPGroup 3 R → R = Ay := by
    intro R hAR hRP hR3
    refine le_antisymm (fun r hr => ?_) hAR
    obtain ⟨hrK, hrA, -⟩ := mem_pbY.mp (hRP hr)
    rw [← himgAy] at hrA
    obtain ⟨⟨e, heK⟩, he, hre⟩ := hrA
    have heA : e ∈ Ay := Subgroup.mem_subgroupOf.mp he
    have := hker3 hR3 r hr e (hAR heA) hrK heK hre.symm
    rw [this]
    exact heA
  obtain ⟨p, hpP, hpA⟩ := exists_mem_map_conj_eq_of_maximal_pGroup hAP hA3 hmaxA hAyP
    (hA3.map _) hmaxAy
  have hpyN : p * k ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have h1 : p * k * a * (p * k)⁻¹ ∈ A.map (MulAut.conj (p * (k : G))).toMonoidHom :=
      ⟨a, ha, by simp [MulAut.conj_apply, mul_assoc]⟩
    rwa [← Late.map_conj_map_conj, ← hAy, hpA] at h1
  obtain ⟨hpK, hpα, hpYA⟩ := mem_pbY.mp hpP
  have hpYA' : p ∈ (Y : Set G) * (A : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y A hAY]
    exact hpYA
  obtain ⟨y₁, hy₁, a₁, ha₁, hpya⟩ := hpYA'
  change y₁ * a₁ = p at hpya
  have hnY : p * k * a₁⁻¹ ∈ Y := by
    have h1 : p * k * a₁⁻¹ = y₁ * (a₁ * k * a₁⁻¹) := by rw [← hpya]; group
    rw [h1]
    exact mul_mem hy₁ ((Subgroup.mem_normalizer_iff.mp (hAY ha₁) _).mp hyY)
  have hnK : p * k * a₁⁻¹ ∈ KA := mul_mem (mul_mem hpK k.2) (inv_mem (hAKA ha₁))
  refine ⟨p * k * a₁⁻¹, Subgroup.mem_inf.mpr ⟨mul_mem hpyN
    (inv_mem ((Subgroup.le_normalizer : A ≤ Subgroup.normalizer (A : Set G)) ha₁)), hnY⟩,
    hnK, q ⟨p, hpK⟩, hpα, (q ⟨a₁, hAKA ha₁⟩)⁻¹, inv_mem (mk_mem_img_A ha₁), ?_⟩
  rw [show (⟨p * k * a₁⁻¹, hnK⟩ : KA) = ⟨p, hpK⟩ * k * (⟨a₁, hAKA ha₁⟩ : KA)⁻¹ from
    Subtype.ext rfl, map_mul, map_mul, map_inv]

theorem isConjIn_of_img_conj (hA : Late.IsE27 A) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hQY : ∀ Z : Subgroup G, Z ≤ Y → A ≤ Subgroup.normalizer (Z : Set G) → ¬ 3 ∣ Nat.card Z →
      Z ∈ scriptQ A (lB A))
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2))
    {ñ : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hñ : ñ ∈ img148 A Y Y ⊓ Subgroup.normalizer
      (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hñT : img148 A Y T = (img148 A Y S).map (MulAut.conj ñ).toMonoidHom) :
    Late.IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 x x.2)⟩
  have hYKA : Y ≤ Y ⊔ A := le_sup_left
  have hSY : S ≤ Y := hS.prop.1.2
  have hTY : T ≤ Y := hT.prop.1.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hT.prop.1.1.1.2.2
  obtain ⟨n, hn, hnK, a₁, ha₁, a₂, ha₂, hna⟩ := exists_lift hA3 hAY hñ
  set Sn := S.map (MulAut.conj n).toMonoidHom with hSn
  have himg : img148 A Y Sn = img148 A Y T := by
    rw [hSn, img_map_conj (hSY.trans hYKA) hnK, hna, ← Late.map_conj_map_conj,
      ← Late.map_conj_map_conj,
      Sec13.map_conj_eq_of_mem_normalizer (img_le_normalizer_img hAS ha₂), ← hñT,
      Sec13.map_conj_eq_of_mem_normalizer (img_le_normalizer_img hAT ha₁)]
  have hnY : n ∈ Y := (Subgroup.mem_inf.mp hn).2
  have hSnY : Sn ≤ Y := by
    rintro _ ⟨s, hs, rfl⟩
    exact mul_mem (mul_mem hnY (hSY hs)) (inv_mem hnY)
  have hSnStar : Sn ∈ scriptQPiStar A (lB A) Y (piOf 2) := by
    refine Late.maximal_map_conj (W := Subgroup.normalizer (A : Set G) ⊓ Y) (fun R hR w hw => ?_)
      hS hn
    refine ⟨⟨rank3II_14_4_5_lB (Subgroup.mem_inf.mp hw).1 hR.1.1, ?_⟩, fun p hp => hR.2 p ?_⟩
    · rintro _ ⟨r, hr, rfl⟩
      have hwY := (Subgroup.mem_inf.mp hw).2
      exact mul_mem (mul_mem hwY (hR.1.2 hr)) (inv_mem hwY)
    · rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective] at hp
  set Z := pbY (img148 A Y T) Y with hZ
  have hT2 : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT.prop.2
  have hZY : Z ≤ Y := inf_le_right
  have hZQ : Z ∈ scriptQ A (lB A) :=
    hQY Z hZY (le_normalizer_pbY hAY (img_le_normalizer_img hAT))
      (not_three_dvd_card_pbY (isPGroup_img hT2) le_rfl)
  have hTZ : T ≤ Z := le_pbY_img (hTY.trans hYKA) hTY
  have hSnZ : Sn ≤ Z := by
    have h1 := le_pbY_img (hSnY.trans hYKA) hSnY
    rwa [himg] at h1
  obtain ⟨x, hx, hxT⟩ := Proof1413Res5.isConjIn_of_le_mem_scriptQ hA hbot hZQ hZY
    hSnStar hT hSnZ hTZ
  have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)) (Subgroup.mem_inf.mp hx).1
  refine ⟨x * n, mul_mem (Subgroup.mem_inf.mpr ⟨hxN, (Subgroup.mem_inf.mp hx).2⟩) hn, ?_⟩
  rw [hxT, hSn, Late.map_conj_map_conj]

end YFrame

end CFSG.RankThree.PartTwo.Sec14.Wales1411W

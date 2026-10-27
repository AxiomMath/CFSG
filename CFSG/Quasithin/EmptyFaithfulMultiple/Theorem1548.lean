module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
import CFSG.Quasithin.Background.A4Aut
import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

section Bar

variable {G : Type*} [Group G]

private abbrev Bar (K : Subgroup G) : Type _ := ↥K ⧸ CFSG.Open.pCore 2 ↥K

private abbrev bar (K : Subgroup G) : ↥K →* Bar K := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)

private def img (K X : Subgroup G) : Subgroup (Bar K) := (X.subgroupOf K).map (bar K)

private def pre (K : Subgroup G) (L : Subgroup (Bar K)) : Subgroup G :=
  (L.comap (bar K)).map K.subtype

private theorem bar_surjective (K : Subgroup G) : Function.Surjective (bar K) :=
  QuotientGroup.mk'_surjective _

private theorem bar_eq_one_iff {K : Subgroup G} {g : G} (hg : g ∈ K) :
    bar K ⟨g, hg⟩ = 1 ↔ g ∈ pCoreOf 2 K := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

private theorem mem_pre {K : Subgroup G} {L : Subgroup (Bar K)} {g : G} :
    g ∈ pre K L ↔ ∃ hg : g ∈ K, bar K ⟨g, hg⟩ ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hL⟩
    exact ⟨⟨g, hg⟩, hL, rfl⟩

private theorem mem_img {K X : Subgroup G} {q : Bar K} :
    q ∈ img K X ↔ ∃ x : ↥K, (x : G) ∈ X ∧ bar K x = q := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

private theorem pre_le (K : Subgroup G) (L : Subgroup (Bar K)) : pre K L ≤ K :=
  Subgroup.map_subtype_le _

private theorem pre_mono (K : Subgroup G) {L L' : Subgroup (Bar K)} (h : L ≤ L') :
    pre K L ≤ pre K L' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

private theorem img_mono (K : Subgroup G) {X Y : Subgroup G} (h : X ≤ Y) : img K X ≤ img K Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

private theorem img_pre (K : Subgroup G) (L : Subgroup (Bar K)) : img K (pre K L) = L := by
  unfold img pre
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  exact Subgroup.map_comap_eq_self_of_surjective (bar_surjective K) L

private theorem pre_img {K X : Subgroup G} (hX : X ≤ K) : pre K (img K X) = X ⊔ pCoreOf 2 K := by
  unfold img pre
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hX]
  rfl

private theorem img_sup {K X Y : Subgroup G} (hX : X ≤ K) (hY : Y ≤ K) :
    img K (X ⊔ Y) = img K X ⊔ img K Y := by
  unfold img
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

private theorem img_top (K : Subgroup G) : img K K = ⊤ := by
  unfold img
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (bar_surjective K)

private theorem mem_normalizer_pre {K : Subgroup G} {L : Subgroup (Bar K)} {g : G} (hg : g ∈ K)
    (hL : bar K ⟨g, hg⟩ ∈ Subgroup.normalizer (L : Set (Bar K))) :
    g ∈ Subgroup.normalizer (pre K L : Set G) := by
  have h1 : (⟨g, hg⟩ : ↥K) ∈ Subgroup.normalizer ((L.comap (bar K) : Subgroup ↥K) : Set ↥K) :=
    Subgroup.le_normalizer_comap (bar K) hL
  exact Subgroup.le_normalizer_map K.subtype ⟨⟨g, hg⟩, h1, rfl⟩

private theorem le_normalizer_pre {K : Subgroup G} {L : Subgroup (Bar K)} (hL : L.Normal) :
    K ≤ Subgroup.normalizer (pre K L : Set G) := by
  intro g hg
  refine mem_normalizer_pre hg ?_
  rw [Subgroup.normalizer_eq_top_iff.mpr hL]
  exact Subgroup.mem_top _

private theorem img_le_normalizer_img {K T Y : Subgroup G} (hYK : Y ≤ K)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) :
    img K T ≤ Subgroup.normalizer (img K Y : Set (Bar K)) := by
  refine le_trans ?_ (Subgroup.le_normalizer_map (bar K))
  refine Subgroup.map_mono ?_
  rw [← Subgroup.subgroupOf_normalizer_eq hYK]
  intro t ht
  exact hTY ht

private theorem img_normal {K Y : Subgroup G} (hYK : Y ≤ K)
    (hKY : K ≤ Subgroup.normalizer (Y : Set G)) : (img K Y).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← img_top K]
  exact img_le_normalizer_img hYK hKY

private theorem card_img {K X : Subgroup G} (hX : X ≤ K) :
    Nat.card (img K X) = (pCoreOf 2 K).relIndex X := by
  unfold img
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  have : CFSG.Open.pCore 2 ↥K = (pCoreOf 2 K).subgroupOf K := by
    unfold pCoreOf
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  rw [this, Subgroup.relIndex_subgroupOf hX]

private theorem img_oTwoUpper [Finite G] {K Y : Subgroup G} (hY : Y ≤ K) :
    img K (oTwoUpper Y) = oTwoUpper (img K Y) := by
  unfold img
  rw [oTwoUpper_map, A4.oTwoUpper_subgroupOf hY]

private theorem le_pCoreOf_of_img_eq_bot {K Y : Subgroup G} (hY : Y ≤ K) (h : img K Y = ⊥) :
    Y ≤ pCoreOf 2 K := by
  have h1 := card_img hY
  rw [h, Subgroup.card_bot] at h1
  exact Subgroup.relIndex_eq_one.mp h1.symm

private theorem eq_of_img_eq {K X Y : Subgroup G} (hXK : X ≤ K) (hYX : Y ≤ X)
    (hXY : X ⊓ pCoreOf 2 K ≤ Y) (h : img K Y = img K X) : Y = X := by
  refine le_antisymm hYX fun x hx => ?_
  have hx' : bar K ⟨x, hXK hx⟩ ∈ img K Y := by
    rw [h]
    exact mem_img.mpr ⟨⟨x, hXK hx⟩, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := mem_img.mp hx'
  have hr : (y : G)⁻¹ * x ∈ pCoreOf 2 K := by
    have : bar K (y⁻¹ * ⟨x, hXK hx⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    exact (bar_eq_one_iff (K.mul_mem (K.inv_mem y.2) (hXK hx))).mp this
  have hrX : (y : G)⁻¹ * x ∈ X := X.mul_mem (X.inv_mem (hYX hy)) hx
  have := Y.mul_mem hy (hXY ⟨hrX, hr⟩)
  simpa using this

private theorem pow_mem_of_mem_pre {K : Subgroup G} {L : Subgroup (Bar K)} {p : ℕ}
    (hL : ∀ q ∈ L, q ^ p = 1) {x : G} (hx : x ∈ pre K L) : x ^ p ∈ pCoreOf 2 K := by
  obtain ⟨hxK, hxL⟩ := mem_pre.mp hx
  have h1 : bar K (⟨x, hxK⟩ ^ p) = 1 := by rw [map_pow]; exact hL _ hxL
  exact (bar_eq_one_iff (K.pow_mem hxK p)).mp h1

private theorem commutator_mem_of_mem_pre {K : Subgroup G} {L : Subgroup (Bar K)}
    (hL : IsMulCommutative L) {x y : G} (hx : x ∈ pre K L) (hy : y ∈ pre K L) :
    ⁅x, y⁆ ∈ pCoreOf 2 K := by
  obtain ⟨hxK, hxL⟩ := mem_pre.mp hx
  obtain ⟨hyK, hyL⟩ := mem_pre.mp hy
  have hc : bar K ⟨x, hxK⟩ * bar K ⟨y, hyK⟩ = bar K ⟨y, hyK⟩ * bar K ⟨x, hxK⟩ :=
    congrArg Subtype.val (mul_comm' (⟨_, hxL⟩ : L) ⟨_, hyL⟩)
  have h1 : bar K ⁅(⟨x, hxK⟩ : ↥K), ⟨y, hyK⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_def, hc]
    group
  have hmem : ⁅x, y⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hxK hyK) (K.inv_mem hxK)) (K.inv_mem hyK)
  exact (bar_eq_one_iff hmem).mp h1

private theorem index_img_dvd (K T : Subgroup G) :
    (img K T).index ∣ (T.subgroupOf K).index :=
  Subgroup.index_map_dvd _ (bar_surjective K)

end Bar

section General

variable {G : Type*} [Group G]

private theorem oTwoUpper_oTwoUpper' (X : Subgroup G) :
    oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun x hx => ?_)
  exact mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2

private theorem sup_eq_oTwoUpper {X Y : Subgroup G} (hX : X = oTwoUpper X)
    (hY : Y = oTwoUpper Y) : X ⊔ Y = oTwoUpper (X ⊔ Y) :=
  le_antisymm (sup_le (hX.le.trans (oTwoUpper_mono le_sup_left))
    (hY.le.trans (oTwoUpper_mono le_sup_right))) (oTwoUpper_le _)

private theorem oTwoUpper_eq_self_of_odd [Finite G] {L : Subgroup G} (hL : Odd (Nat.card L)) :
    oTwoUpper L = L :=
  le_antisymm (oTwoUpper_le L) fun _ hx =>
    mem_oTwoUpper_of_odd hx (hL.of_dvd_nat (Subgroup.orderOf_dvd_natCard L hx))

private theorem oTwoUpper_sup_eq {X R : Subgroup G} (hX : X = oTwoUpper X) (hR : IsPGroup 2 R)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) : oTwoUpper (X ⊔ R) = X := by
  refine (eq_oTwoUpper_of_pow_mem le_sup_left (fun y hy => ?_) hX).symm
  have hy' : y ∈ ((X ⊔ R : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X R hRX] at hy'
  obtain ⟨x, hx, r, hr, rfl⟩ := hy'
  exact A4.exists_pow_mem_of_mul (sup_le Subgroup.le_normalizer hRX) hR hy hx hr rfl le_sup_left

private theorem pCoreOf_eq_inf {X R : Subgroup G} (hXR : pCoreOf 2 X ≤ R)
    (hRn : X ≤ Subgroup.normalizer (R : Set G)) (hR : IsPGroup 2 R) :
    pCoreOf 2 X = X ⊓ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_inf (pCoreOf_le 2 X) hXR) ?_
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg => ?_) (hR.to_le inf_le_right)
  exact A4.mem_normalizer_inf (Subgroup.le_normalizer hg) (hRn hg)

variable [Finite G]

private theorem pCoreOf_le_pCoreOf {X K : Subgroup G} (hXK : X ≤ K)
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) : pCoreOf 2 X ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 X).trans hXK)
    (hKX.trans (normalizer_le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)

private theorem pCoreOf_ne_bot_of_charTwo {M N : Subgroup G}
    (hM : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M) (hNM : N ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) : pCoreOf 2 N ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  set R := pCoreOf 2 M
  have hle : N ⊓ R ≤ pCoreOf 2 N :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => A4.mem_normalizer_inf (Subgroup.le_normalizer hg)
        (le_normalizer_pCoreOf 2 M (hNM hg))) ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
  rw [h] at hle
  have hNC : N ≤ M ⊓ Subgroup.centralizer (R : Set G) := by
    intro n hn
    refine ⟨hNM hn, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    have h1 : n * r * n⁻¹ * r⁻¹ ∈ N := by
      have : r * n⁻¹ * r⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hMN (pCoreOf_le 2 M hr)) n⁻¹).mp (N.inv_mem hn)
      have h2 := N.mul_mem hn this
      simpa [mul_assoc] using h2
    have h2 : n * r * n⁻¹ * r⁻¹ ∈ R := by
      have : n * r * n⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M (hNM hn)) r).mp hr
      exact R.mul_mem this (R.inv_mem hr)
    have h3 : n * r * n⁻¹ * r⁻¹ = 1 := Subgroup.mem_bot.mp (hle ⟨h1, h2⟩)
    calc r * n = (n * r * n⁻¹ * r⁻¹)⁻¹ * (n * r) := by group
      _ = n * r := by rw [h3, inv_one, one_mul]
  have hNR : N ≤ N ⊓ R := le_inf le_rfl (hNC.trans hM)
  exact hN (eq_bot_iff.mpr (hNR.trans hle))

end General

section Lines

variable {Q : Type*} [Group Q]

private def lineJoin (p : ℕ) (B : Subgroup Q) : Subgroup Q :=
  Subgroup.closure {x | ∃ A : Subgroup Q, A ≤ B ∧ B ≤ Subgroup.normalizer (A : Set Q) ∧
    Nat.card A = p ∧ x ∈ A}

private theorem le_lineJoin {p : ℕ} {A B : Subgroup Q} (hAB : A ≤ B)
    (hBA : B ≤ Subgroup.normalizer (A : Set Q)) (hA : Nat.card A = p) : A ≤ lineJoin p B :=
  fun _ hx => Subgroup.subset_closure ⟨A, hAB, hBA, hA, hx⟩

private theorem lineJoin_le (p : ℕ) (B : Subgroup Q) : lineJoin p B ≤ B :=
  (Subgroup.closure_le B).mpr fun _ ⟨_, hAB, _, _, hx⟩ => hAB hx

private theorem normalizer_le_normalizer_lineJoin (p : ℕ) (B : Subgroup Q) :
    Subgroup.normalizer (B : Set Q) ≤ Subgroup.normalizer (lineJoin p B : Set Q) := by
  rw [lineJoin, Subgroup.le_normalizer_closure_iff]
  rintro g hg x ⟨A, hAB, hBA, hA, hx⟩
  refine Subgroup.subset_closure ⟨A.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, x, hx, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg a).mp (hAB ha)
  · rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨a, ha, rfl⟩
    have hb' : g⁻¹ * b * g ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) b).mp hb
      simpa using this
    have h1 := (Subgroup.le_normalizer_iff.mp hBA) _ hb' a ha
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA]

variable [Finite Q]

private theorem exists_card_eq_three_pow {E : Subgroup Q} (hE : IsElemAbelian 3 E) :
    ∃ k : ℕ, Nat.card E = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine IsPGroup.iff_card.mp fun x => ⟨1, ?_⟩
  apply Subtype.ext
  simpa using hE.2 x x.2

private theorem card_eq_of_isElemAbelian
    (hrk : ∀ E : Subgroup Q, IsElemAbelian 3 E → Nat.card E ≤ 9) {E : Subgroup Q}
    (hE : IsElemAbelian 3 E) : Nat.card E = 1 ∨ Nat.card E = 3 ∨ Nat.card E = 9 := by
  obtain ⟨k, hk⟩ := exists_card_eq_three_pow hE
  have h := hrk E hE
  rw [hk] at h ⊢
  have hk2 : k ≤ 2 := by
    by_contra hk2
    have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp

private theorem commute_of_card_prime {p : ℕ} (hp : p.Prime) {A₁ A₂ B : Subgroup Q}
    (h₁ : A₁ ≤ B) (h₂ : A₂ ≤ B) (hn₁ : B ≤ Subgroup.normalizer (A₁ : Set Q))
    (hn₂ : B ≤ Subgroup.normalizer (A₂ : Set Q)) (hc₁ : Nat.card A₁ = p)
    (hc₂ : Nat.card A₂ = p) {a b : Q} (ha : a ∈ A₁) (hb : b ∈ A₂) : Commute a b := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases h : A₁ = A₂
  · subst h
    have : IsCyclic A₁ := isCyclic_of_prime_card hc₁
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A₁) ⟨b, hb⟩)
  · have hinf : A₁ ⊓ A₂ = ⊥ := by
      have hdvd : Nat.card (A₁ ⊓ A₂ : Subgroup Q) ∣ p := hc₁ ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have e1 : A₁ ⊓ A₂ = A₁ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc₁, h1])
        have e2 : A₁ ⊓ A₂ = A₂ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hc₂, h1])
        exact h (e1.symm.trans e2)
    have hc : a * b * a⁻¹ * b⁻¹ ∈ A₁ ⊓ A₂ := by
      refine ⟨?_, ?_⟩
      · have : b * a⁻¹ * b⁻¹ ∈ A₁ :=
          (Subgroup.mem_normalizer_iff.mp (hn₁ (h₂ hb)) a⁻¹).mp (A₁.inv_mem ha)
        have h2 := A₁.mul_mem ha this
        simpa [mul_assoc] using h2
      · have : a * b * a⁻¹ ∈ A₂ := (Subgroup.mem_normalizer_iff.mp (hn₂ (h₁ ha)) b).mp hb
        exact A₂.mul_mem this (A₂.inv_mem hb)
    rw [hinf, Subgroup.mem_bot] at hc
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [hc, one_mul]

private theorem isElemAbelian_lineJoin {p : ℕ} (hp : p.Prime) (B : Subgroup Q) :
    IsElemAbelian p (lineJoin p B) := by
  have hcomm : IsMulCommutative (lineJoin p B) := by
    apply Subgroup.isMulCommutative_closure
    rintro x ⟨A₁, h₁, hn₁, hc₁, hx⟩ y ⟨A₂, h₂, hn₂, hc₂, hy⟩ -
    exact commute_of_card_prime hp h₁ h₂ hn₁ hn₂ hc₁ hc₂ hx hy
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨A, -, -, hA, hxA⟩ := hx
    exact orderOf_dvd_iff_pow_eq_one.mp (hA ▸ Subgroup.orderOf_dvd_natCard A hxA)
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : lineJoin p B) ⟨y, hy⟩)
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

private theorem sup_eq_of_ne {A B W : Subgroup Q} (hW : IsElemAbelian 3 W)
    (hW9 : Nat.card W ≤ 9) (hA : A ≤ W) (hB : B ≤ W) (hA3 : Nat.card A = 3)
    (hB3 : Nat.card B = 3) (hAB : A ≠ B) : A ⊔ B = W ∧ Nat.card W = 9 := by
  have hsup : A ⊔ B ≤ W := sup_le hA hB
  obtain ⟨k, hk⟩ := exists_card_eq_three_pow hW
  obtain ⟨j, -, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hk ▸ Subgroup.card_dvd_of_le hsup)
  have h3 : 3 ∣ Nat.card (A ⊔ B : Subgroup Q) := hA3 ▸ Subgroup.card_dvd_of_le le_sup_left
  have hle : Nat.card (A ⊔ B : Subgroup Q) ≤ Nat.card W := Subgroup.card_le_of_le hsup
  have hj : j = 2 := by
    rw [hjc] at h3 hle
    have hj2 : j ≤ 2 := by
      by_contra hj2
      have : 3 ^ 3 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases j
    · norm_num at h3
    · exfalso
      have e1 : A = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hjc, hA3]; norm_num)
      have e2 : B = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hjc, hB3]; norm_num)
      exact hAB (e1.trans e2.symm)
    · rfl
  subst hj
  have hW9' : Nat.card W = 9 := le_antisymm hW9 (by rw [hjc] at hle; simpa using hle)
  exact ⟨Subgroup.eq_of_le_of_card_ge hsup (by rw [hW9', hjc]; norm_num), hW9'⟩

omit [Finite Q] in
private theorem card_filter_mem_not_mem [Fintype Q] [DecidableEq Q] {K L : Subgroup Q}
    [DecidablePred (· ∈ K)] [DecidablePred (· ∈ L)] (hKL : K ≤ L) :
    ((Finset.univ : Finset Q).filter fun x => x ∈ L ∧ x ∉ K).card =
      Nat.card L - Nat.card K := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Q).filter fun x => x ∈ L) (fun x => x ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have hK : ((Finset.univ : Finset Q).filter fun x => x ∈ L ∧ x ∈ K).card = Nat.card K := by
    rw [Finset.filter_congr fun x _ =>
      (show x ∈ L ∧ x ∈ K ↔ x ∈ K from ⟨fun h => h.2, fun h => ⟨hKL h, h⟩⟩),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hL : ((Finset.univ : Finset Q).filter fun x => x ∈ L).card = Nat.card L := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  omega

private theorem ncard_lines {V : Subgroup Q} (hV9 : Nat.card V = 9)
    (hV3 : ∀ v ∈ V, v ^ 3 = 1) : {L : Subgroup Q | L ≤ V ∧ Nat.card L = 3}.ncard = 4 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype Q := Fintype.ofFinite Q
  have : Fintype (Subgroup Q) := Fintype.ofFinite (Subgroup Q)
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  set s := (Finset.univ : Finset (Subgroup Q)).filter fun L => L ≤ V ∧ Nat.card L = 3
  set X := (Finset.univ : Finset Q).filter fun x => x ∈ V ∧ x ∉ (⊥ : Subgroup Q)
  have hX : X.card = 8 := by rw [card_filter_mem_not_mem bot_le, hV9, Subgroup.card_bot]
  have hA : ∀ x ∈ V, x ∉ (⊥ : Subgroup Q) → Nat.card (Subgroup.zpowers x) = 3 := by
    intro x hx h1
    rw [Nat.card_zpowers, orderOf_eq_prime (hV3 x hx) (fun h => h1 (h ▸ Subgroup.one_mem _))]
  have hmaps : Set.MapsTo (fun x : Q => Subgroup.zpowers x) (X : Set Q)
      (s : Set (Subgroup Q)) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, Subgroup.zpowers_le.mpr hx.2.1, hA x hx.2.1 hx.2.2⟩
  have hfiber : ∀ L ∈ s, (X.filter fun x => Subgroup.zpowers x = L).card = 2 := by
    intro L hL
    rw [Finset.mem_filter] at hL
    obtain ⟨-, hLV, hL3⟩ := hL
    have : (X.filter fun x => Subgroup.zpowers x = L) =
        (Finset.univ : Finset Q).filter fun x => x ∈ L ∧ x ∉ (⊥ : Subgroup Q) := by
      ext x
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨-, hx1⟩, hxL⟩
        exact ⟨hxL ▸ Subgroup.mem_zpowers x, hx1⟩
      · rintro ⟨hxL, hx1⟩
        refine ⟨⟨hLV hxL, hx1⟩, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxL) ?_⟩
        rw [hL3, hA x (hLV hxL) hx1]
    rw [this, card_filter_mem_not_mem bot_le, hL3, Subgroup.card_bot]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, hX] at hsum
  omega

omit [Finite Q] in
private theorem smul_mem_lines {V : Subgroup Q} (hV : V.Normal) (c : ConjAct Q) {L : Subgroup Q}
    (hL : L ∈ {L : Subgroup Q | L ≤ V ∧ Nat.card L = 3}) :
    c • L ∈ {L : Subgroup Q | L ≤ V ∧ Nat.card L = 3} := by
  obtain ⟨hLV, hL3⟩ := hL
  have hinj : Function.Injective (MulDistribMulAction.toMonoidEnd (ConjAct Q) Q c) :=
    MulAction.injective c
  refine ⟨?_, ?_⟩
  · rw [← hV.conjAct c, Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hLV
  · rw [Subgroup.pointwise_smul_def, Subgroup.card_map_of_injective hinj, hL3]

private theorem exists_normal_line {V T L₀ : Subgroup Q} (hV : V.Normal) (hV9 : Nat.card V = 9)
    (hV3 : ∀ v ∈ V, v ^ 3 = 1) (hT : ¬ 2 ∣ T.index) (hL₀V : L₀ ≤ V) (hL₀ : Nat.card L₀ = 3)
    (hTL₀ : T ≤ Subgroup.normalizer (L₀ : Set Q)) :
    ∃ L : Subgroup Q, L ≤ V ∧ Nat.card L = 3 ∧ L.Normal := by
  classical
  set Ω : Set (Subgroup Q) := {L : Subgroup Q | L ≤ V ∧ Nat.card L = 3}
  have hΩ4 : Ω.ncard = 4 := ncard_lines hV9 hV3
  set O := MulAction.orbit (ConjAct Q) L₀
  have hOΩ : O ⊆ Ω := by
    rintro _ ⟨c, rfl⟩
    exact smul_mem_lines hV c ⟨hL₀V, hL₀⟩
  have hOle : O.ncard ≤ 4 := hΩ4 ▸ Set.ncard_le_ncard hOΩ (Set.toFinite Ω)
  have hOpos : 0 < O.ncard :=
    Set.ncard_pos (Set.toFinite O) |>.mpr ⟨L₀, MulAction.mem_orbit_self L₀⟩
  have hOodd : ¬ 2 ∣ O.ncard := by
    rw [← MulAction.index_stabilizer]
    have hcomap := Subgroup.index_comap_of_surjective (MulAction.stabilizer (ConjAct Q) L₀)
      (f := (ConjAct.toConjAct : Q ≃* ConjAct Q).toMonoidHom) ConjAct.toConjAct.surjective
    have hTle : T ≤ (MulAction.stabilizer (ConjAct Q) L₀).comap
        (ConjAct.toConjAct : Q ≃* ConjAct Q).toMonoidHom := by
      intro t ht
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      exact Subgroup.conjAct_pointwise_smul_iff.mpr (hTL₀ ht)
    rw [← hcomap]
    exact fun h => hT (h.trans (Subgroup.index_dvd_of_le hTle))
  have hnormal : ∀ L : Subgroup Q, (∀ c : ConjAct Q, c • L = L) → L.Normal := fun L h =>
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun g _ =>
      Subgroup.conjAct_pointwise_smul_iff.mp (h _))
  have hO13 : O.ncard = 1 ∨ O.ncard = 3 := by omega
  rcases hO13 with h1 | h3
  · refine ⟨L₀, hL₀V, hL₀, hnormal L₀ fun c => ?_⟩
    obtain ⟨L, hL⟩ := Set.ncard_eq_one.mp h1
    have e1 : c • L₀ ∈ O := MulAction.mem_orbit L₀ c
    have e2 : L₀ ∈ O := MulAction.mem_orbit_self L₀
    rw [hL, Set.mem_singleton_iff] at e1 e2
    exact e1.trans e2.symm
  · have hdiff : (Ω \ O).ncard = 1 := by
      rw [Set.ncard_sdiff hOΩ (Set.toFinite O), hΩ4, h3]
    obtain ⟨L₁, hL₁⟩ := Set.ncard_eq_one.mp hdiff
    have hL₁mem : L₁ ∈ Ω \ O := hL₁ ▸ Set.mem_singleton L₁
    refine ⟨L₁, hL₁mem.1.1, hL₁mem.1.2, hnormal L₁ fun c => ?_⟩
    have hc : c • L₁ ∈ Ω \ O := by
      refine ⟨smul_mem_lines hV c hL₁mem.1, fun hcO => hL₁mem.2 ?_⟩
      have h1 : MulAction.orbit (ConjAct Q) (c • L₁) = O := MulAction.orbit_eq_iff.mpr hcO
      rw [MulAction.orbit_smul] at h1
      exact h1 ▸ MulAction.mem_orbit_self L₁
    rw [hL₁, Set.mem_singleton_iff] at hc
    exact hc

private theorem exists_normal_isElemAbelian_three [Group.IsSolvable Q] [Nontrivial Q]
    (hO2 : CFSG.Open.pCore 2 Q = ⊥)
    (h23 : ∀ q : ℕ, q.Prime → q ∣ Nat.card Q → q = 2 ∨ q = 3) :
    ∃ V : Subgroup Q, V.Normal ∧ V ≠ ⊥ ∧ IsElemAbelian 3 V := by
  obtain ⟨M, hMn, -, hMne, hMmin⟩ := CFSG.exists_minimal_normal_le (⊤ : Subgroup Q)
    inferInstance (by simp)
  have : M.Normal := hMn
  have : CFSG.IsMinimalNormal M := ⟨fun K _ hK => by
    by_cases hK' : K = ⊥
    · exact Or.inl hK'
    · exact Or.inr (hMmin K inferInstance hK hK')⟩
  obtain ⟨p, hp, hpM⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian M
  have : Fact p.Prime := ⟨hp⟩
  have hMp : IsPGroup p M := CFSG.IsElementaryAbelian.isPGroup p M
  have hdvd : p ∣ Nat.card M := by
    have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
    obtain ⟨n, hn0, hn⟩ := hMp.nontrivial_iff_card.mp this
    rw [hn]
    exact dvd_pow_self p hn0.ne'
  rcases h23 p hp (hdvd.trans (Subgroup.card_subgroup_dvd_card M)) with h2 | h3
  · subst h2
    exact absurd (eq_bot_iff.mpr (hO2 ▸ CFSG.LieType.BorelTits.le_pCore 2 hMn hMp)) hMne
  · subst h3
    exact ⟨M, hMn, hMne, hpM.toIsMulCommutative,
      fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩

end Lines

section Setting

variable {G : Type*} [Group G]

private theorem omegaOneCenter_le (T : Subgroup G) : quasithinOmegaOneCenter T ≤ T :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1.1

private theorem le_centralizer_omegaOneCenter (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  exact (Subgroup.closure_le _).mpr fun _ hz => hz.1.2

private theorem centralizer_VZ_le (T M : Subgroup G) :
    M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  inf_le_right.trans (Subgroup.centralizer_le (le_conjClosure _ M))

private theorem le_normalizer_centralizer_VZ (T M : Subgroup G) :
    M ≤ Subgroup.normalizer (M ⊓ Subgroup.centralizer (VZ T M : Set G) : Set G) := fun _ hg =>
  A4.mem_normalizer_inf (Subgroup.le_normalizer hg)
    (A4.mem_normalizer_centralizer (le_normalizer_conjClosure _ M hg))

private theorem not_two_dvd_index_subgroupOf {T K : Subgroup G} (hT : ¬ 2 ∣ T.index)
    (hTK : T ≤ K) : ¬ 2 ∣ (T.subgroupOf K).index :=
  fun h => hT (h.trans (Subgroup.relIndex_dvd_index_of_le hTK))

variable [Finite G]

private theorem pCoreOf_sup_ne_bot {T X : Subgroup G} (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hXC : X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    pCoreOf 2 (X ⊔ T) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  apply quasithinOmegaOneCenter_ne_bot hT2 hTne
  rw [eq_bot_iff, ← hbot]
  exact le_pCoreOf_of_le_normalizer 2 ((omegaOneCenter_le T).trans le_sup_right)
    ((sup_le hXC (le_centralizer_omegaOneCenter T)).trans (Subgroup.centralizer_le_normalizer _))
    (hT2.to_le (omegaOneCenter_le T))

private theorem isSmallXi_of {T X : Subgroup G} (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hX : X = oTwoUpper X) (hXC : X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (h3 : (pCoreOf 2 X).relIndex X = 3) :
    IsSmallXi T X :=
  ⟨hX, hTX, ⟨le_sup_right, pCoreOf_sup_ne_bot hT2 hTne hXC⟩, 3, Nat.prime_three,
    by norm_num, h3⟩

omit [Finite G] in
private theorem isSylowTwoOf_of_le {T M : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTM : T ≤ M) : IsSylowTwoOf T M :=
  ⟨hTM, hT.1, not_two_dvd_index_subgroupOf hT.2 hTM⟩

private theorem pRank_le_two {G : Type} [Group G] [Finite G]
    (hK : CFSG.QuasithinUnique.quasithinIsQTKECat G)
    {H : Subgroup G} (hH : IsTwoLocal H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p H ≤ 2 :=
  pRank_le_two_of_isTwoLocal_cat hK hH hp hp2

private theorem card_le_nine {G : Type} [Group G] [Finite G]
    (hK : CFSG.QuasithinUnique.quasithinIsQTKECat G)
    {K L : Subgroup G} (hL : IsTwoLocal L) (hKL : K ≤ L) {E : Subgroup (Bar K)}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := exists_card_eq_three_pow hE
  have h1 : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar K)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk
  have h3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K) 2)
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  rw [CFSG.SectionRank.pRank_quotient_eq _ h3, pRank_top_subtype] at h1
  have h2 := (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hKL).trans
    (pRank_le_two hK hL Nat.prime_three (by norm_num))
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (h1.trans h2)
    _ = 9 := by norm_num

private theorem ne_bot_of_hyp {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) : T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M₁, -, -, hM₁, -, -, -⟩ := hyp.two_centralizer_maximal
  obtain ⟨P, hP, hP2, -⟩ := hM₁.1
  have h2P : 2 ∣ Nat.card P := by
    have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
    obtain ⟨n, hn0, hn⟩ := hP2.nontrivial_iff_card.mp this
    rw [hn]
    exact dvd_pow_self 2 hn0.ne'
  intro hT
  apply hyp.sylow.2
  rw [hT, Subgroup.index_bot]
  exact h2P.trans (Subgroup.card_subgroup_dvd_card P)

private theorem relIndex_eq_three {G : Type} [Group G] [Finite G] {T X : Subgroup G}
    (h5 : Stmt1545 G T) (hX : IsSmallXi T X)
    (hXC : X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    (pCoreOf 2 X).relIndex X = 3 := by
  obtain ⟨p, hp, hp2, hrel⟩ := hX.2.2.2
  have hdvd : p ∣ Nat.card (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
    hrel ▸ (Subgroup.index_dvd_card _).trans (Subgroup.card_dvd_of_le hXC)
  rcases h5 p hp hdvd with h | h
  · exact absurd h hp2
  · rw [hrel, h]

private theorem eq_of_le_normalizer {G : Type} [Group G] [Finite G]
    (hev : quasithinEvenCharacteristic G) {T M₁ M₂ N : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hM₁ : quasithinIsMaxTwoLocal M₁) (hM₂ : quasithinIsMaxTwoLocal M₂) (hTM₁ : T ≤ M₁)
    (hN : N ≠ ⊥) (hNM₁ : N ≤ M₁) (h₁ : M₁ ≤ Subgroup.normalizer (N : Set G))
    (h₂ : M₂ ≤ Subgroup.normalizer (N : Set G)) : M₁ = M₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hc := hev M₁ hM₁.1 ⟨S, hS ▸ hTM₁⟩
  have hP := pCoreOf_ne_bot_of_charTwo hc hNM₁ h₁ hN
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 N : Set G)) :=
    ⟨pCoreOf 2 N, hP, pCoreOf_isPGroup 2 N, rfl⟩
  have e₁ := hM₁.2 _ hloc (h₁.trans (normalizer_le_normalizer_pCoreOf 2 N))
  have e₂ := hM₂.2 _ hloc (h₂.trans (normalizer_le_normalizer_pCoreOf 2 N))
  exact e₁.symm.trans e₂

private theorem oTwoUpper_pre_img {M X : Subgroup G} (hXM : X ≤ M)
    (hX : X = oTwoUpper X) (hRX : pCoreOf 2 M ≤ Subgroup.normalizer (X : Set G)) :
    oTwoUpper (pre M (img M X)) = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pre_img hXM, oTwoUpper_sup_eq hX (pCoreOf_isPGroup 2 M) hRX]

private theorem le_normalizer_of_img_normal {M X : Subgroup G} (hXM : X ≤ M)
    (hX : X = oTwoUpper X) (hRX : pCoreOf 2 M ≤ Subgroup.normalizer (X : Set G))
    (h : (img M X).Normal) : M ≤ Subgroup.normalizer (X : Set G) := by
  have h1 := (le_normalizer_pre h).trans (normalizer_le_normalizer_oTwoUpper _)
  rwa [oTwoUpper_pre_img hXM hX hRX] at h1

private theorem eq_of_img_eq_of_oTwoUpper {M X Y : Subgroup G} (hXM : X ≤ M) (hYM : Y ≤ M)
    (hX : X = oTwoUpper X) (hY : Y = oTwoUpper Y)
    (hRX : pCoreOf 2 M ≤ Subgroup.normalizer (X : Set G))
    (hRY : pCoreOf 2 M ≤ Subgroup.normalizer (Y : Set G)) (h : img M X = img M Y) : X = Y := by
  rw [← oTwoUpper_pre_img hXM hX hRX, h, oTwoUpper_pre_img hYM hY hRY]

private theorem card_img_of_normal {M H Y : Subgroup G} (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hHM : H ≤ M)
    (hMH : M ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card (img M Y) = (pCoreOf 2 Y).relIndex Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 Y ≤ pCoreOf 2 M :=
    (pCoreOf_le_pCoreOf hYH hHY).trans (pCoreOf_le_pCoreOf hHM hMH)
  rw [card_img (hYH.trans hHM), pCoreOf_eq_inf h1
    ((hYH.trans hHM).trans (le_normalizer_pCoreOf 2 M)) (pCoreOf_isPGroup 2 M),
    Subgroup.inf_relIndex_left]

private theorem oTwoUpper_pre_spec {K : Subgroup G} {L : Subgroup (Bar K)} (hLn : L.Normal)
    (hLo : Odd (Nat.card L)) :
    oTwoUpper (pre K L) ≤ K ∧ K ≤ Subgroup.normalizer (oTwoUpper (pre K L) : Set G) ∧
      img K (oTwoUpper (pre K L)) = L ∧
      pCoreOf 2 (oTwoUpper (pre K L)) = oTwoUpper (pre K L) ⊓ pCoreOf 2 K ∧
      (pCoreOf 2 (oTwoUpper (pre K L))).relIndex (oTwoUpper (pre K L)) = Nat.card L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXK : oTwoUpper (pre K L) ≤ K := (oTwoUpper_le _).trans (pre_le K L)
  have hKX : K ≤ Subgroup.normalizer (oTwoUpper (pre K L) : Set G) :=
    (le_normalizer_pre hLn).trans (normalizer_le_normalizer_oTwoUpper _)
  have himg : img K (oTwoUpper (pre K L)) = L := by
    rw [img_oTwoUpper (pre_le K L), img_pre, oTwoUpper_eq_self_of_odd hLo]
  have hO2 : pCoreOf 2 (oTwoUpper (pre K L)) = oTwoUpper (pre K L) ⊓ pCoreOf 2 K :=
    pCoreOf_eq_inf (pCoreOf_le_pCoreOf hXK hKX) (hXK.trans (le_normalizer_pCoreOf 2 K))
      (pCoreOf_isPGroup 2 K)
  refine ⟨hXK, hKX, himg, hO2, ?_⟩
  rw [hO2, Subgroup.inf_relIndex_left, ← card_img hXK, himg]

end Setting

theorem stmt1549_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T) (h3 : Stmt1542Three G T)
    (h5 : Stmt1545 G T) : Stmt1549 G T := by
  intro hCT
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := quasithinOmegaOneCenter T
  set C := Subgroup.centralizer (Z : Set G)
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hTne : T ≠ ⊥ := ne_bot_of_hyp hyp
  have hTC : T ≤ C := le_centralizer_omegaOneCenter T
  obtain ⟨M₁, -, -, hM₁, -, hCM₁, -⟩ := hyp.two_centralizer_maximal
  have hsolv : Group.IsSolvable C := by
    have := h2 M₁ ⟨hM₁, hTC.trans hCM₁⟩
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCM₁)
  have hQ23 : ∀ q : ℕ, q.Prime → q ∣ Nat.card (Bar C) → q = 2 ∨ q = 3 := fun q hq hdvd =>
    h5 q hq (hdvd.trans (Subgroup.card_quotient_dvd_card _))
  have hQO2 : CFSG.Open.pCore 2 (Bar C) = ⊥ := B6.pCore_quotient_pCore
  have hQnt : Nontrivial (Bar C) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hCle : C ≤ pCoreOf 2 C := fun c hc => (bar_eq_one_iff hc).mp (Subsingleton.elim _ _)
    have hC2 : IsPGroup 2 C := (pCoreOf_isPGroup 2 C).to_le hCle
    obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
    have := S.is_maximal' hC2 (hS ▸ hTC)
    exact hCT (this.trans hS)
  have hrk : ∀ E : Subgroup (Bar C), IsElemAbelian 3 E → Nat.card E ≤ 9 := fun E hE =>
    card_le_nine hyp.qtke (isTwoLocal_normalizer_omegaOneCenter hT2 hTne)
      (Subgroup.centralizer_le_normalizer _) hE
  have hTodd : ¬ 2 ∣ (img C T).index := fun h =>
    not_two_dvd_index_subgroupOf hyp.sylow.2 hTC (h.trans (index_img_dvd C T))
  obtain ⟨V, hVn, hVne, hVea⟩ := exists_normal_isElemAbelian_three hQO2 hQ23
  obtain ⟨L, hLn, hL3⟩ : ∃ L : Subgroup (Bar C), L.Normal ∧ Nat.card L = 3 := by
    rcases card_eq_of_isElemAbelian hrk hVea with h1 | h3' | h9
    · exact absurd (Subgroup.card_eq_one.mp h1) hVne
    · exact ⟨V, hVn, h3'⟩
    by_cases hred : ∃ L₀ : Subgroup (Bar C), L₀ ≤ V ∧ Nat.card L₀ = 3 ∧
        img C T ≤ Subgroup.normalizer (L₀ : Set (Bar C))
    · obtain ⟨L₀, hL₀V, hL₀, hTL₀⟩ := hred
      obtain ⟨L, -, hL, hLn⟩ := exists_normal_line hVn h9 hVea.2 hTodd hL₀V hL₀ hTL₀
      exact ⟨L, hLn, hL⟩
    exfalso
    push Not at hred
    obtain ⟨hXK, hKX, himg, hO2, hrel⟩ := oTwoUpper_pre_spec hVn (by rw [h9]; decide)
    set X := oTwoUpper (pre C V)
    have hXi : IsXi T X := by
      refine ⟨(oTwoUpper_oTwoUpper' _).symm, hTC.trans hKX, pCoreOf_sup_ne_bot hT2 hTne hXK,
        3, Nat.prime_three, by norm_num, fun x hx => ?_, Or.inl (by rw [hrel, h9]; norm_num),
        fun Y hY1 hY2 hTY => ?_⟩
      · rw [hO2]
        exact ⟨X.pow_mem hx 3, pow_mem_of_mem_pre hVea.2 (oTwoUpper_le _ hx)⟩
      · have hcomm : ⁅X, X⁆ ≤ pCoreOf 2 X := by
          rw [hO2]
          refine Subgroup.commutator_le.mpr fun a ha b hb => ⟨?_, ?_⟩
          · rw [commutatorElement_def]
            exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
          · exact commutator_mem_of_mem_pre hVea.1 (oTwoUpper_le _ ha) (oTwoUpper_le _ hb)
        rw [sup_eq_right.mpr hcomm] at hY1 ⊢
        have hYC : Y ≤ C := hY2.trans hXK
        have hYV : img C Y ≤ V := himg ▸ img_mono C hY2
        obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
          (show Nat.card (img C Y) ∣ 3 ^ 2 by
            rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
            exact Subgroup.card_dvd_of_le hYV)
        interval_cases j
        · left
          refine le_antisymm ?_ hY1
          rw [hO2]
          exact le_inf hY2 (le_pCoreOf_of_img_eq_bot hYC
            (Subgroup.card_eq_one.mp (by simpa using hjc)))
        · exact absurd (img_le_normalizer_img hYC hTY) (hred _ hYV (by simpa using hjc))
        · right
          refine eq_of_img_eq hXK hY2 (hO2 ▸ hY1) ?_
          rw [himg]
          exact Subgroup.eq_of_le_of_card_ge hYV (by rw [hjc, h9]; norm_num)
    apply (h3 X hXi).1
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact hXK
  obtain ⟨hXK, hKX, -, -, hrel⟩ := oTwoUpper_pre_spec hLn (by rw [hL3]; decide)
  exact ⟨oTwoUpper (pre C L), isSmallXi_of hT2 hTne (oTwoUpper_oTwoUpper' _).symm hXK
    (hTC.trans hKX) (hrel.trans hL3), hXK, hKX⟩

private theorem false_of_not_le_normalizer {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h5 : Stmt1545 G T) (h10 : Stmt15410 G T)
    {X M₁ M₂ : Subgroup G} (hX : IsXFamily1548 G T X) (hne : M₁ ≠ M₂)
    (hM₁ : quasithinIsMaxTwoLocal M₁) (hM₂ : quasithinIsMaxTwoLocal M₂)
    (hCM₁ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁)
    (hCM₂ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₂)
    (hX1 : ¬ M₁ ≤ Subgroup.normalizer (X : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := quasithinOmegaOneCenter T
  set C := Subgroup.centralizer (Z : Set G)
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hTne : T ≠ ⊥ := ne_bot_of_hyp hyp
  have hTC : T ≤ C := le_centralizer_omegaOneCenter T
  have hTM₁ : T ≤ M₁ := hTC.trans hCM₁
  have hTM₂ : T ≤ M₂ := hTC.trans hCM₂
  obtain ⟨hXxi, hXC, hCX⟩ := hX
  have hX3 : (pCoreOf 2 X).relIndex X = 3 := relIndex_eq_three h5 hXxi hXC
  have hXO : X = oTwoUpper X := hXxi.1
  have hXM₁ : X ≤ M₁ := hXC.trans hCM₁
  have hXM₂ : X ≤ M₂ := hXC.trans hCM₂
  set H₁ := M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G)
  set H₂ := M₂ ⊓ Subgroup.centralizer (VZ T M₂ : Set G)
  have hH₁C : H₁ ≤ C := centralizer_VZ_le T M₁
  have hH₂C : H₂ ≤ C := centralizer_VZ_le T M₂
  have hM₁H₁ : M₁ ≤ Subgroup.normalizer (H₁ : Set G) := le_normalizer_centralizer_VZ T M₁
  have hM₂H₂ : M₂ ≤ Subgroup.normalizer (H₂ : Set G) := le_normalizer_centralizer_VZ T M₂
  have hXH₁ : X ≤ H₁ := h10 X ⟨hXxi, hXC, hCX⟩ M₁ ⟨hM₁, sup_le hXM₁ hTM₁⟩
  have hXH₂ : X ≤ H₂ := h10 X ⟨hXxi, hXC, hCX⟩ M₂ ⟨hM₂, sup_le hXM₂ hTM₂⟩
  have hR₁C : pCoreOf 2 M₁ ≤ C :=
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hyp.sylow hTM₁)).trans hTC
  have hR₂C : pCoreOf 2 M₂ ≤ C :=
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hyp.sylow hTM₂)).trans hTC
  have hrk₁ : ∀ E : Subgroup (Bar M₁), IsElemAbelian 3 E → Nat.card E ≤ 9 := fun E hE =>
    card_le_nine hyp.qtke hM₁.1 le_rfl hE
  have hrk₂ : ∀ E : Subgroup (Bar M₂), IsElemAbelian 3 E → Nat.card E ≤ 9 := fun E hE =>
    card_le_nine hyp.qtke hM₂.1 le_rfl hE
  have hXbar : Nat.card (img M₁ X) = 3 :=
    (card_img_of_normal hXH₁ (hH₁C.trans hCX) inf_le_left hM₁H₁).trans hX3
  have hXbarn : ¬ (img M₁ X).Normal := fun h =>
    hX1 (le_normalizer_of_img_normal hXM₁ hXO (hR₁C.trans hCX) h)
  set V₁ := lineJoin 3 (img M₁ H₁)
  have hV₁n : V₁.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    rw [← Subgroup.normalizer_eq_top_iff.mpr (img_normal inf_le_left hM₁H₁)]
    exact normalizer_le_normalizer_lineJoin 3 _
  have hV₁ea : IsElemAbelian 3 V₁ := isElemAbelian_lineJoin Nat.prime_three _
  have hXV₁ : img M₁ X ≤ V₁ :=
    le_lineJoin (img_mono M₁ hXH₁) (img_le_normalizer_img hXM₁ (hH₁C.trans hCX)) hXbar
  have hV₁9 : Nat.card V₁ = 9 := by
    rcases card_eq_of_isElemAbelian hrk₁ hV₁ea with h | h | h
    · have := Subgroup.card_dvd_of_le hXV₁
      rw [hXbar, h] at this
      norm_num at this
    · exfalso
      apply hXbarn
      rw [Subgroup.eq_of_le_of_card_ge hXV₁ (by rw [h, hXbar])]
      exact hV₁n
    · exact h
  have hTodd : ¬ 2 ∣ (img M₁ T).index := fun h =>
    not_two_dvd_index_subgroupOf hyp.sylow.2 hTM₁ (h.trans (index_img_dvd M₁ T))
  obtain ⟨L, hLV, hL3, hLn⟩ := exists_normal_line hV₁n hV₁9 hV₁ea.2 hTodd hXV₁ hXbar
    (img_le_normalizer_img hXM₁ (hTC.trans hCX))
  obtain ⟨hX₁M₁, hM₁X₁, himgX₁, -, hrelX₁⟩ := oTwoUpper_pre_spec hLn (by rw [hL3]; decide)
  set X₁ := oTwoUpper (pre M₁ L)
  have hX₁O : X₁ = oTwoUpper X₁ := (oTwoUpper_oTwoUpper' _).symm
  have hX₁C : X₁ ≤ C :=
    calc X₁ ≤ pre M₁ L := oTwoUpper_le _
      _ ≤ pre M₁ (img M₁ H₁) := pre_mono M₁ (hLV.trans (lineJoin_le 3 _))
      _ = H₁ ⊔ pCoreOf 2 M₁ := pre_img inf_le_left
      _ ≤ C := sup_le hH₁C hR₁C
  have hCX₁ : C ≤ Subgroup.normalizer (X₁ : Set G) := hCM₁.trans hM₁X₁
  have hX₁ : IsXFamily1548 G T X₁ :=
    ⟨isSmallXi_of hT2 hTne hX₁O hX₁C (hTC.trans hCX₁) (hrelX₁.trans hL3), hX₁C, hCX₁⟩
  have hX₁M₂ : X₁ ≤ M₂ := hX₁C.trans hCM₂
  have hX₁H₂ : X₁ ≤ H₂ := h10 X₁ hX₁ M₂ ⟨hM₂, sup_le hX₁M₂ hTM₂⟩
  have hXX₁ : X ≠ X₁ := fun h => hX1 (h ▸ hM₁X₁)
  have hXX₁O : X ⊔ X₁ = oTwoUpper (X ⊔ X₁) := sup_eq_oTwoUpper hXO hX₁O
  have hCXX₁ : C ≤ Subgroup.normalizer ((X ⊔ X₁ : Subgroup G) : Set G) :=
    (le_inf hCX hCX₁).trans (Subgroup.inf_normalizer_le_normalizer_sup X X₁)
  have hN₁ : M₁ ≤ Subgroup.normalizer ((X ⊔ X₁ : Subgroup G) : Set G) := by
    have hXL : img M₁ X ≠ L := fun h => hXbarn (h ▸ hLn)
    have hsup := (sup_eq_of_ne hV₁ea (hrk₁ V₁ hV₁ea) hXV₁ hLV hXbar hL3 hXL).1
    refine le_normalizer_of_img_normal (sup_le hXM₁ hX₁M₁) hXX₁O (hR₁C.trans hCXX₁) ?_
    rw [img_sup hXM₁ hX₁M₁, himgX₁, hsup]
    exact hV₁n
  have hXbar₂ : Nat.card (img M₂ X) = 3 :=
    (card_img_of_normal hXH₂ (hH₂C.trans hCX) inf_le_left hM₂H₂).trans hX3
  have hX₁bar₂ : Nat.card (img M₂ X₁) = 3 :=
    (card_img_of_normal hX₁H₂ (hH₂C.trans hCX₁) inf_le_left hM₂H₂).trans (hrelX₁.trans hL3)
  set W := lineJoin 3 (img M₂ H₂)
  have hWn : W.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    rw [← Subgroup.normalizer_eq_top_iff.mpr (img_normal inf_le_left hM₂H₂)]
    exact normalizer_le_normalizer_lineJoin 3 _
  have hWea : IsElemAbelian 3 W := isElemAbelian_lineJoin Nat.prime_three _
  have hXW : img M₂ X ≤ W :=
    le_lineJoin (img_mono M₂ hXH₂) (img_le_normalizer_img hXM₂ (hH₂C.trans hCX)) hXbar₂
  have hX₁W : img M₂ X₁ ≤ W :=
    le_lineJoin (img_mono M₂ hX₁H₂) (img_le_normalizer_img hX₁M₂ (hH₂C.trans hCX₁)) hX₁bar₂
  have hne₂ : img M₂ X ≠ img M₂ X₁ := fun h =>
    hXX₁ (eq_of_img_eq_of_oTwoUpper hXM₂ hX₁M₂ hXO hX₁O (hR₂C.trans hCX) (hR₂C.trans hCX₁) h)
  have hN₂ : M₂ ≤ Subgroup.normalizer ((X ⊔ X₁ : Subgroup G) : Set G) := by
    have hsup := (sup_eq_of_ne hWea (hrk₂ W hWea) hXW hX₁W hXbar₂ hX₁bar₂ hne₂).1
    refine le_normalizer_of_img_normal (sup_le hXM₂ hX₁M₂) hXX₁O (hR₂C.trans hCXX₁) ?_
    rw [img_sup hXM₂ hX₁M₂, hsup]
    exact hWn
  have hXne : X ⊔ X₁ ≠ ⊥ := by
    intro h
    have hXbot : X = ⊥ := eq_bot_iff.mpr (h ▸ le_sup_left)
    rw [hXbot] at hX3
    simp at hX3
  exact hne (eq_of_le_normalizer hyp.qtke.2.1 hyp.sylow hM₁ hM₂ hTM₁ hXne
    (sup_le hXM₁ hX₁M₁) hN₁ hN₂)

theorem stmt1548_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h5 : Stmt1545 G T)
    (h9 : Stmt1549 G T) (h10 : Stmt15410 G T) : Stmt1548 G T := by
  by_contra hCT
  obtain ⟨X, hX⟩ := h9 hCT
  obtain ⟨M₁, M₂, hne, hM₁, hM₂, hCM₁, hCM₂⟩ := hyp.two_centralizer_maximal
  by_cases hX1 : M₁ ≤ Subgroup.normalizer (X : Set G)
  · by_cases hX2 : M₂ ≤ Subgroup.normalizer (X : Set G)
    · have hXne : X ≠ ⊥ := by
        intro h
        have h3 := relIndex_eq_three h5 hX.1 hX.2.1
        rw [h] at h3
        simp at h3
      exact hne (eq_of_le_normalizer hyp.qtke.2.1 hyp.sylow hM₁ hM₂
        ((le_centralizer_omegaOneCenter T).trans hCM₁) hXne (hX.2.1.trans hCM₁) hX1 hX2)
    · exact false_of_not_le_normalizer hyp h5 h10 hX hne.symm hM₂ hM₁ hCM₂ hCM₁ hX2
  · exact false_of_not_le_normalizer hyp h5 h10 hX hne hM₁ hM₂ hCM₁ hCM₂ hX1

end CFSG.Quasithin.EmptyFaithfulMultiple

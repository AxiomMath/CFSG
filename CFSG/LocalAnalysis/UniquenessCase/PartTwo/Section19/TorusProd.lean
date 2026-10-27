module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem tcpr_exists_sl2 {Y : Type} [Group Y] {n : ℕ} (h : IsL2 Y n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK,
    ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_two_equiv K)⟩⟩

theorem centralizer_of_pow_eq_one_of_isL2 {Y : Type} [Group Y] {n : ℕ} (hY : IsL2 Y n) {a : Y}
    (ha1 : a ≠ 1) (ha : a ^ (2 ^ n - 1) = 1) :
    IsMulCommutative (centralizer ({a} : Set Y)) ∧
      Nat.card (centralizer ({a} : Set Y)) = 2 ^ n - 1 := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := tcpr_exists_sl2 hY
  have ha' : a ^ (Nat.card F - 1) = 1 := by rw [hF]; exact ha
  rw [← CFSG.LocalAnalysis.EvenBN.Common.centralizer_zpowers]
  exact ⟨CFSG.LocalAnalysis.EvenBN.Common.isMulCommutative_centralizer_zpowers e ha1 ha',
    by rw [CFSG.LocalAnalysis.EvenBN.Common.card_centralizer_zpowers e ha1 ha', hF]⟩

private theorem tcpr_odd (n : ℕ) (hn : n ≠ 0) : Odd (2 ^ n - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' hn).2 even_two) odd_one

private theorem tcpr_exists_prime_pow {Y : Type} [Group Y] {m : ℕ} (hm : Odd m) {a : Y}
    (ha1 : a ≠ 1) (ha : a ^ m = 1) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ m ∧ ∃ b ∈ zpowers a, orderOf b = r := by
  have hdvd : orderOf a ∣ m := orderOf_dvd_of_pow_eq_one ha
  have ho0 : orderOf a ≠ 0 := fun h => by
    rw [h, zero_dvd_iff] at hdvd
    rw [hdvd] at hm
    exact absurd hm (by decide)
  have ho1 : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.1 h)
  have hr := Nat.minFac_prime ho1
  have hrm : (orderOf a).minFac ∣ m := (Nat.minFac_dvd _).trans hdvd
  refine ⟨_, hr, fun h2 => ?_, hrm, _, npow_mem_zpowers a (orderOf a / (orderOf a).minFac),
    orderOf_pow_orderOf_div ho0 (Nat.minFac_dvd _)⟩
  rw [h2] at hrm
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hrm)

private theorem tcpr_centralizer_eq {Y : Type} [Group Y] {a b : Y} (hb : b ∈ zpowers a)
    (hcomm : ∀ y ∈ centralizer ({b} : Set Y), ∀ z ∈ centralizer ({b} : Set Y), y * z = z * y) :
    centralizer ({a} : Set Y) = centralizer {b} := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  have ha : a ∈ centralizer ({a ^ k} : Set Y) :=
    mem_centralizer_singleton_iff.2 (Commute.self_zpow a k).eq
  apply le_antisymm
  · intro y hy
    exact mem_centralizer_singleton_iff.2 (Commute.zpow_right
      (mem_centralizer_singleton_iff.1 hy) k).eq
  · intro y hy
    exact mem_centralizer_singleton_iff.2 (hcomm y hy a ha)

private theorem tcpr_sz_prime {Y : Type} [Group Y] {n : ℕ}
    (hY : IsSz Y n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1) {b : Y}
    (hb : orderOf b = r) :
    (∀ y ∈ centralizer ({b} : Set Y), ∀ z ∈ centralizer ({b} : Set Y), y * z = z * y) ∧
      Nat.card (centralizer ({b} : Set Y)) = 2 ^ n - 1 := by
  obtain ⟨-, -, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel hY
  have hbo : orderOf (e b) = r := by rw [MulEquiv.orderOf_eq, hb]
  obtain ⟨⟨g, hg⟩, hcomm⟩ :=
    (CFSG.LieType.Ree.suzuki_split_torus_odd_prime_centralizers hK).2 r hr hr2 hrn (e b) hbo
  have hmap : (centralizer ({b} : Set Y)).map e.toMonoidHom = centralizer {e b} := by
    rw [CFSG.LocalAnalysis.EvenBN.Common.map_equiv_centralizer, Set.image_singleton]
  have hmem : ∀ y ∈ centralizer ({b} : Set Y), e y ∈ centralizer ({e b} : Set _) :=
    fun y hy => hmap ▸ mem_map_of_mem e.toMonoidHom hy
  refine ⟨fun y hy z hz => e.injective ?_, ?_⟩
  · rw [map_mul, map_mul]
    exact hcomm _ (hmem y hy) _ (hmem z hz)
  · rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, hmap, hg,
      card_map_of_injective (MulAut.conj g).injective]
    exact (CFSG.LieType.Ree.suzuki_borel_structure hK).2.2.1

theorem centralizer_of_pow_eq_one_of_isSz {Y : Type} [Group Y]
    {n : ℕ} (hY : IsSz Y n) {a : Y} (ha1 : a ≠ 1) (ha : a ^ (2 ^ n - 1) = 1) :
    IsMulCommutative (centralizer ({a} : Set Y)) ∧
      Nat.card (centralizer ({a} : Set Y)) = 2 ^ n - 1 := by
  obtain ⟨-, -, k, -, K, _, _, hn, -⟩ := CFSG.Blueprint.LieModel.suzukiModel hY
  obtain ⟨r, hr, hr2, hrn, b, hb, hbo⟩ :=
    tcpr_exists_prime_pow (tcpr_odd n (by omega)) ha1 ha
  obtain ⟨hcomm, hcard⟩ := tcpr_sz_prime hY hr hr2 hrn hbo
  rw [tcpr_centralizer_eq hb hcomm]
  exact ⟨isMulCommutative_iff.2 fun y z => Subtype.ext (hcomm _ y.2 _ z.2), hcard⟩

theorem centralizer_of_pow_eq_one_of_isL2_or_isSz {Y : Type}
    [Group Y] {n : ℕ} (hY : IsL2 Y n ∨ IsSz Y n) {a : Y} (ha1 : a ≠ 1)
    (ha : a ^ (2 ^ n - 1) = 1) :
    IsMulCommutative (centralizer ({a} : Set Y)) ∧
      Nat.card (centralizer ({a} : Set Y)) = 2 ^ n - 1 :=
  hY.elim (fun h => centralizer_of_pow_eq_one_of_isL2 h ha1 ha)
    (fun h => centralizer_of_pow_eq_one_of_isSz h ha1 ha)

section Product

variable {X : Type} [Group X]

private theorem tcpr_pow_eq_one {T : Subgroup X} {n : ℕ} (hT : IsZModSq T n) {t : X}
    (ht : t ∈ T) : t ^ (2 ^ n - 1) = 1 := by
  obtain ⟨e⟩ := hT
  have hx : ∀ {m : ℕ} (z : Multiplicative (ZMod m × ZMod m)), z ^ m = 1 := fun z => by
    rw [← toAdd_eq_zero, toAdd_pow]
    ext <;> simp
  have h1 : (⟨t, ht⟩ : T) ^ (2 ^ n - 1) = 1 :=
    e.injective (by rw [map_pow, hx (e ⟨t, ht⟩), map_one])
  simpa using congrArg Subtype.val h1

private theorem tcpr_map_centralizer {S : Subgroup X} {a : X} (ha : a ∈ S) :
    (centralizer ({(⟨a, ha⟩ : S)} : Set S)).map S.subtype = centralizer ({a} : Set X) ⊓ S := by
  ext z
  simp only [mem_map, mem_centralizer_singleton_iff, mem_inf, Subgroup.coe_subtype]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨congrArg Subtype.val hw, w.2⟩
  · rintro ⟨hz, hzS⟩
    exact ⟨⟨z, hzS⟩, Subtype.ext hz, rfl⟩

private theorem tcpr_factor {S : Subgroup X} {n : ℕ}
    (hS : IsL2 S n ∨ IsSz S n) {a : X} (haS : a ∈ S) (ha1 : a ≠ 1) (ha : a ^ (2 ^ n - 1) = 1) :
    (∀ y ∈ centralizer ({a} : Set X) ⊓ S, ∀ z ∈ centralizer ({a} : Set X) ⊓ S, y * z = z * y) ∧
      Nat.card (centralizer ({a} : Set X) ⊓ S : Subgroup X) = 2 ^ n - 1 := by
  have ha1' : (⟨a, haS⟩ : S) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have ha' : (⟨a, haS⟩ : S) ^ (2 ^ n - 1) = 1 := Subtype.ext (by simpa using ha)
  obtain ⟨hcomm, hcard⟩ := centralizer_of_pow_eq_one_of_isL2_or_isSz hS ha1' ha'
  rw [← tcpr_map_centralizer haS]
  refine ⟨?_, by rw [card_map_of_injective S.subtype_injective, hcard]⟩
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  exact congrArg (fun w : centralizer ({(⟨a, haS⟩ : S)} : Set S) => ((w : S) : X))
    (mul_comm' (⟨y, hy⟩ : centralizer ({(⟨a, haS⟩ : S)} : Set S)) ⟨z, hz⟩)

variable {S₁ S₂ : Subgroup X}

private theorem tcpr_comm (h₁ : S₁.Normal) (h₂ : S₂.Normal) (hinf : S₁ ⊓ S₂ = ⊥) {a b : X}
    (ha : a ∈ S₁) (hb : b ∈ S₂) : a * b = b * a :=
  Subgroup.commute_of_normal_of_disjoint S₁ S₂ h₁ h₂ (disjoint_iff.2 hinf) a b ha hb

private theorem tcpr_decomp (h₁ : S₁.Normal) (hsup : S₁ ⊔ S₂ = ⊤) (x : X) :
    ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, x = x₁ * x₂ := by
  have hx : x ∈ ((S₁ ⊔ S₂ : Subgroup X) : Set X) := by
    rw [hsup]
    exact mem_top x
  rw [Subgroup.normal_mul] at hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Set.mem_mul.1 hx
  exact ⟨x₁, hx₁, x₂, hx₂, rfl⟩

private theorem tcpr_unique (hinf : S₁ ⊓ S₂ = ⊥) {a b c d : X} (ha : a ∈ S₁) (hb : b ∈ S₂)
    (hc : c ∈ S₁) (hd : d ∈ S₂) (h : a * b = c * d) : a = c ∧ b = d := by
  have h1 : c⁻¹ * a = d * b⁻¹ := by
    calc c⁻¹ * a = c⁻¹ * (a * b) * b⁻¹ := by group
      _ = c⁻¹ * (c * d) * b⁻¹ := by rw [h]
      _ = d * b⁻¹ := by group
  have h2 : c⁻¹ * a ∈ S₁ ⊓ S₂ :=
    ⟨S₁.mul_mem (S₁.inv_mem hc) ha, h1 ▸ S₂.mul_mem hd (S₂.inv_mem hb)⟩
  rw [hinf, mem_bot, inv_mul_eq_one] at h2
  subst h2
  exact ⟨rfl, mul_left_cancel h⟩

private theorem tcpr_split (h₁ : S₁.Normal) (h₂ : S₂.Normal) (hinf : S₁ ⊓ S₂ = ⊥)
    {x₁ x₂ y₁ y₂ : X} (hx₁ : x₁ ∈ S₁) (hx₂ : x₂ ∈ S₂) (hy₁ : y₁ ∈ S₁) (hy₂ : y₂ ∈ S₂)
    (h : y₁ * y₂ * (x₁ * x₂) = x₁ * x₂ * (y₁ * y₂)) :
    y₁ * x₁ = x₁ * y₁ ∧ y₂ * x₂ = x₂ * y₂ := by
  have e1 : y₁ * y₂ * (x₁ * x₂) = y₁ * x₁ * (y₂ * x₂) := by
    calc y₁ * y₂ * (x₁ * x₂) = y₁ * (y₂ * x₁) * x₂ := by group
      _ = y₁ * (x₁ * y₂) * x₂ := by rw [tcpr_comm h₁ h₂ hinf hx₁ hy₂]
      _ = y₁ * x₁ * (y₂ * x₂) := by group
  have e2 : x₁ * x₂ * (y₁ * y₂) = x₁ * y₁ * (x₂ * y₂) := by
    calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by group
      _ = x₁ * (y₁ * x₂) * y₂ := by rw [tcpr_comm h₁ h₂ hinf hy₁ hx₂]
      _ = x₁ * y₁ * (x₂ * y₂) := by group
  rw [e1, e2] at h
  exact tcpr_unique hinf (S₁.mul_mem hy₁ hx₁) (S₂.mul_mem hy₂ hx₂) (S₁.mul_mem hx₁ hy₁)
    (S₂.mul_mem hx₂ hy₂) h

private theorem tcpr_cent_inf (h₁ : S₁.Normal) (h₂ : S₂.Normal) (hinf : S₁ ⊓ S₂ = ⊥)
    {x₁ x₂ : X} (hx₁ : x₁ ∈ S₁) (hx₂ : x₂ ∈ S₂) :
    centralizer ({x₁ * x₂} : Set X) ⊓ S₁ = centralizer ({x₁} : Set X) ⊓ S₁ := by
  ext y
  simp only [mem_inf, mem_centralizer_singleton_iff]
  refine and_congr_left fun hy => ⟨fun h => ?_, fun h => ?_⟩
  · refine (tcpr_split h₁ h₂ hinf hx₁ hx₂ hy (one_mem S₂) ?_).1
    simpa only [mul_one] using h
  · calc y * (x₁ * x₂) = x₁ * (y * x₂) := by rw [← mul_assoc, h, mul_assoc]
      _ = x₁ * x₂ * y := by rw [tcpr_comm h₁ h₂ hinf hy hx₂, mul_assoc]

private theorem tcpr_cent_inf₂ (h₁ : S₁.Normal) (h₂ : S₂.Normal) (hinf : S₁ ⊓ S₂ = ⊥)
    {x₁ x₂ : X} (hx₁ : x₁ ∈ S₁) (hx₂ : x₂ ∈ S₂) :
    centralizer ({x₁ * x₂} : Set X) ⊓ S₂ = centralizer ({x₂} : Set X) ⊓ S₂ := by
  rw [tcpr_comm h₁ h₂ hinf hx₁ hx₂]
  exact tcpr_cent_inf h₂ h₁ (by rw [inf_comm, hinf]) hx₂ hx₁

private theorem tcpr_card_cent_le [Finite X] (h₁ : S₁.Normal) (h₂ : S₂.Normal)
    (hinf : S₁ ⊓ S₂ = ⊥) (hsup : S₁ ⊔ S₂ = ⊤) {x₁ x₂ : X} (hx₁ : x₁ ∈ S₁) (hx₂ : x₂ ∈ S₂) :
    Nat.card (centralizer ({x₁ * x₂} : Set X)) ≤
      Nat.card (centralizer ({x₁} : Set X) ⊓ S₁ : Subgroup X) *
        Nat.card (centralizer ({x₂} : Set X) ⊓ S₂ : Subgroup X) := by
  have hm₁ : ∀ y ∈ centralizer ({x₁} : Set X) ⊓ S₁, y ∈ centralizer ({x₁ * x₂} : Set X) :=
    fun y hy => (show y ∈ centralizer ({x₁ * x₂} : Set X) ⊓ S₁ by
      rw [tcpr_cent_inf h₁ h₂ hinf hx₁ hx₂]; exact hy).1
  have hm₂ : ∀ y ∈ centralizer ({x₂} : Set X) ⊓ S₂, y ∈ centralizer ({x₁ * x₂} : Set X) :=
    fun y hy => (show y ∈ centralizer ({x₁ * x₂} : Set X) ⊓ S₂ by
      rw [tcpr_cent_inf₂ h₁ h₂ hinf hx₁ hx₂]; exact hy).1
  let f : ↥(centralizer ({x₁} : Set X) ⊓ S₁) × ↥(centralizer ({x₂} : Set X) ⊓ S₂) →
      ↥(centralizer ({x₁ * x₂} : Set X)) := fun p =>
    ⟨p.1 * p.2, mul_mem (hm₁ _ p.1.2) (hm₂ _ p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := tcpr_decomp h₁ hsup y
    obtain ⟨e₁, e₂⟩ := tcpr_split h₁ h₂ hinf hx₁ hx₂ hy₁ hy₂
      (mem_centralizer_singleton_iff.1 hy)
    exact ⟨(⟨y₁, mem_centralizer_singleton_iff.2 e₁, hy₁⟩,
      ⟨y₂, mem_centralizer_singleton_iff.2 e₂, hy₂⟩), rfl⟩
  calc Nat.card (centralizer ({x₁ * x₂} : Set X)) ≤ Nat.card
        (↥(centralizer ({x₁} : Set X) ⊓ S₁) × ↥(centralizer ({x₂} : Set X) ⊓ S₂)) :=
        Nat.card_le_card_of_surjective f hf
    _ = _ := Nat.card_prod _ _

private theorem tcpr_T_comm {T : Subgroup X} {n : ℕ} (hT : IsZModSq T n) {s t : X} (hs : s ∈ T)
    (ht : t ∈ T) : s * t = t * s :=
  congrArg Subtype.val (@mul_comm' T _ (isMulCommutative_of_isZModSq hT) ⟨s, hs⟩ ⟨t, ht⟩)

private theorem tcpr_parts {n : ℕ} {T : Subgroup X} (hT : IsZModSq T n) (h₁ : S₁.Normal)
    (h₂ : S₂.Normal) (hinf : S₁ ⊓ S₂ = ⊥) {x₁ x₂ : X} (hx₁S : x₁ ∈ S₁) (hx₂S : x₂ ∈ S₂)
    (hxT : x₁ * x₂ ∈ T) (hx₁ : x₁ * x₂ ∉ S₁) (hx₂ : x₁ * x₂ ∉ S₂) :
    x₁ ≠ 1 ∧ x₂ ≠ 1 ∧ x₁ ^ (2 ^ n - 1) = 1 ∧ x₂ ^ (2 ^ n - 1) = 1 := by
  have hpow : x₁ ^ (2 ^ n - 1) * x₂ ^ (2 ^ n - 1) = 1 * 1 := by
    rw [← (Commute.mul_pow (tcpr_comm h₁ h₂ hinf hx₁S hx₂S)), mul_one]
    exact tcpr_pow_eq_one hT hxT
  refine ⟨?_, ?_, tcpr_unique hinf (pow_mem hx₁S _) (pow_mem hx₂S _) (one_mem _) (one_mem _) hpow⟩
  · rintro rfl
    rw [one_mul] at hx₂
    exact hx₂ hx₂S
  · rintro rfl
    rw [mul_one] at hx₁
    exact hx₁ hx₁S

private theorem tcpr_cent_eq [Finite X] {n : ℕ} {T : Subgroup X}
    (hT : IsZModSq T n) (h₁ : S₁.Normal) (h₂ : S₂.Normal) (hinf : S₁ ⊓ S₂ = ⊥)
    (hsup : S₁ ⊔ S₂ = ⊤) (hS₁ : IsL2 S₁ n ∨ IsSz S₁ n) (hS₂ : IsL2 S₂ n ∨ IsSz S₂ n) {x : X}
    (hxT : x ∈ T) (hx₁ : x ∉ S₁) (hx₂ : x ∉ S₂) : centralizer ({x} : Set X) = T := by
  obtain ⟨x₁, hx₁S, x₂, hx₂S, rfl⟩ := tcpr_decomp h₁ hsup x
  obtain ⟨hne₁, hne₂, hp₁, hp₂⟩ := tcpr_parts hT h₁ h₂ hinf hx₁S hx₂S hxT hx₁ hx₂
  have hc := tcpr_card_cent_le h₁ h₂ hinf hsup hx₁S hx₂S
  rw [(tcpr_factor hS₁ hx₁S hne₁ hp₁).2, (tcpr_factor hS₂ hx₂S hne₂ hp₂).2] at hc
  refine (eq_of_le_of_card_ge (fun t ht => mem_centralizer_singleton_iff.2
    (tcpr_T_comm hT ht hxT)) ?_).symm
  rw [card_eq_of_isZModSq hT]
  exact hc

private theorem tcpr_card_inf_le [Finite X] {T S : Subgroup X}
    {n : ℕ} (hn : n ≠ 0) (hT : IsZModSq T n) (hS : IsL2 S n ∨ IsSz S n) :
    Nat.card (T ⊓ S : Subgroup X) ≤ 2 ^ n - 1 := by
  rcases (T ⊓ S).bot_or_exists_ne_one with h | ⟨a, ha, ha1⟩
  · rw [h, card_bot]
    exact (tcpr_odd n hn).pos
  · have hle : T ⊓ S ≤ centralizer ({a} : Set X) ⊓ S := fun y hy =>
      ⟨mem_centralizer_singleton_iff.2 (tcpr_T_comm hT hy.1 ha.1), hy.2⟩
    exact (card_le_of_le hle).trans (tcpr_factor hS ha.2 ha1 (tcpr_pow_eq_one hT ha.1)).2.le

private theorem tcpr_not_le [Finite X] {T S : Subgroup X} {n : ℕ}
    (hn : 2 ≤ n) (hT : IsZModSq T n) (hS : IsL2 S n ∨ IsSz S n) : ¬ T ≤ S := by
  intro hle
  have h1 := tcpr_card_inf_le (by omega) hT hS
  rw [inf_of_le_left hle, card_eq_of_isZModSq hT] at h1
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3 : 3 ≤ 2 ^ n - 1 := by omega
  nlinarith

private theorem tcpr_exists_not_mem {T : Subgroup X} (h1 : ¬ T ≤ S₁) (h2 : ¬ T ≤ S₂) :
    ∃ x ∈ T, x ∉ S₁ ∧ x ∉ S₂ := by
  obtain ⟨a, haT, ha1⟩ := SetLike.not_le_iff_exists.1 h1
  obtain ⟨b, hbT, hb2⟩ := SetLike.not_le_iff_exists.1 h2
  by_cases ha2 : a ∈ S₂
  · by_cases hb1 : b ∈ S₁
    · refine ⟨a * b, T.mul_mem haT hbT, fun h => ha1 ?_, fun h => hb2 ?_⟩
      · simpa using S₁.mul_mem h (S₁.inv_mem hb1)
      · simpa using S₂.mul_mem (S₂.inv_mem ha2) h
    · exact ⟨b, hbT, hb1, hb2⟩
  · exact ⟨a, haT, ha1, ha2⟩

private theorem tcpr_factors {n : ℕ} (hS : (IsL2 S₁ n ∧ IsL2 S₂ n) ∨ (IsSz S₁ n ∧ IsSz S₂ n)) :
    (IsL2 S₁ n ∨ IsSz S₁ n) ∧ (IsL2 S₂ n ∨ IsSz S₂ n) :=
  hS.elim (fun h => ⟨Or.inl h.1, Or.inl h.2⟩) (fun h => ⟨Or.inr h.1, Or.inr h.2⟩)

private theorem tcpr_inf_eq [Finite X] {T S : Subgroup X} {n : ℕ}
    (hT : IsZModSq T n) (hS : IsL2 S n ∨ IsSz S n)
    (hcard : Nat.card (T ⊓ S : Subgroup X) = 2 ^ n - 1) {a : X} (ha : a ∈ T ⊓ S) (ha1 : a ≠ 1) :
    T ⊓ S = centralizer ({a} : Set X) ⊓ S := by
  refine eq_of_le_of_card_ge (fun y hy => ⟨mem_centralizer_singleton_iff.2
    (tcpr_T_comm hT hy.1 ha.1), hy.2⟩) ?_
  rw [hcard, (tcpr_factor hS ha.2 ha1 (tcpr_pow_eq_one hT ha.1)).2]

end Product

theorem torus_eq_sup_inf_of_prod {X : Type} [Group X] [Finite X]
    {n : ℕ} (hn : 2 ≤ n) {T : Subgroup X} (hT : IsZModSq T n) (S₁ S₂ : Subgroup X)
    (h₁ : S₁.Normal) (h₂ : S₂.Normal) (hinf : S₁ ⊓ S₂ = ⊥) (hsup : S₁ ⊔ S₂ = ⊤)
    (hS : (IsL2 S₁ n ∧ IsL2 S₂ n) ∨ (IsSz S₁ n ∧ IsSz S₂ n)) :
    Nat.card (T ⊓ S₁ : Subgroup X) = 2 ^ n - 1 ∧ Nat.card (T ⊓ S₂ : Subgroup X) = 2 ^ n - 1 ∧
      T = (T ⊓ S₁) ⊔ (T ⊓ S₂) := by
  obtain ⟨hS₁, hS₂⟩ := tcpr_factors hS
  obtain ⟨x, hxT, hx₁, hx₂⟩ :=
    tcpr_exists_not_mem (tcpr_not_le hn hT hS₁) (tcpr_not_le hn hT hS₂)
  have hC := tcpr_cent_eq hT h₁ h₂ hinf hsup hS₁ hS₂ hxT hx₁ hx₂
  obtain ⟨x₁, hx₁S, x₂, hx₂S, rfl⟩ := tcpr_decomp h₁ hsup x
  obtain ⟨hne₁, hne₂, hp₁, hp₂⟩ := tcpr_parts hT h₁ h₂ hinf hx₁S hx₂S hxT hx₁ hx₂
  have hc₁ : T ⊓ S₁ = centralizer ({x₁} : Set X) ⊓ S₁ := by
    rw [← hC, tcpr_cent_inf h₁ h₂ hinf hx₁S hx₂S]
  have hc₂ : T ⊓ S₂ = centralizer ({x₂} : Set X) ⊓ S₂ := by
    rw [← hC, tcpr_cent_inf₂ h₁ h₂ hinf hx₁S hx₂S]
  refine ⟨hc₁ ▸ (tcpr_factor hS₁ hx₁S hne₁ hp₁).2, hc₂ ▸ (tcpr_factor hS₂ hx₂S hne₂ hp₂).2,
    le_antisymm (fun t ht => ?_) (sup_le inf_le_left inf_le_left)⟩
  obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := tcpr_decomp h₁ hsup t
  rw [← hC] at ht
  obtain ⟨e₁, e₂⟩ := tcpr_split h₁ h₂ hinf hx₁S hx₂S ht₁ ht₂ (mem_centralizer_singleton_iff.1 ht)
  rw [hc₁, hc₂]
  exact mul_mem_sup ⟨mem_centralizer_singleton_iff.2 e₁, ht₁⟩
    ⟨mem_centralizer_singleton_iff.2 e₂, ht₂⟩

theorem inf_eq_centralizer_inf_of_prod {X : Type} [Group X]
    [Finite X] {n : ℕ} (hn : 2 ≤ n) {T : Subgroup X} (hT : IsZModSq T n) (S₁ S₂ : Subgroup X)
    (h₁ : S₁.Normal) (h₂ : S₂.Normal) (hinf : S₁ ⊓ S₂ = ⊥) (hsup : S₁ ⊔ S₂ = ⊤)
    (hS : (IsL2 S₁ n ∧ IsL2 S₂ n) ∨ (IsSz S₁ n ∧ IsSz S₂ n)) :
    (∀ a ∈ T ⊓ S₁, a ≠ 1 → T ⊓ S₁ = centralizer ({a} : Set X) ⊓ S₁) ∧
      ∀ a ∈ T ⊓ S₂, a ≠ 1 → T ⊓ S₂ = centralizer ({a} : Set X) ⊓ S₂ := by
  obtain ⟨hS₁, hS₂⟩ := tcpr_factors hS
  obtain ⟨hc₁, hc₂, -⟩ := torus_eq_sup_inf_of_prod hn hT S₁ S₂ h₁ h₂ hinf hsup hS
  exact ⟨fun a ha ha1 => tcpr_inf_eq hT hS₁ hc₁ ha ha1,
    fun a ha ha1 => tcpr_inf_eq hT hS₂ hc₂ ha ha1⟩

theorem k_19_25_torusCent_prod
    {X : Type} [Group X] [Finite X] {n : ℕ} {T : Subgroup X} (hT : IsZModSq T n) {x : X}
    (hxT : x ∈ T) (S₁ S₂ : Subgroup X) (h₁ : S₁.Normal) (h₂ : S₂.Normal) (hinf : S₁ ⊓ S₂ = ⊥)
    (hsup : S₁ ⊔ S₂ = ⊤)
    (hS : (IsL2 S₁ n ∧ IsL2 S₂ n) ∨ (IsSz S₁ n ∧ IsSz S₂ n)) :
    x ∈ S₁ ∨ x ∈ S₂ ∨ centralizer ({x} : Set X) = T := by
  obtain ⟨hS₁, hS₂⟩ := tcpr_factors hS
  by_cases hx₁ : x ∈ S₁
  · exact Or.inl hx₁
  by_cases hx₂ : x ∈ S₂
  · exact Or.inr (Or.inl hx₂)
  exact Or.inr (Or.inr (tcpr_cent_eq hT h₁ h₂ hinf hsup hS₁ hS₂ hxT hx₁ hx₂))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

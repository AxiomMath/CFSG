module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.Delta
public import Mathlib.GroupTheory.Commutator.Basic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentralProduct
import CFSG.ClassicalInvolution.SL2Facts
import CFSG.HardMathSupport.Foote.Proving.SLFiveCard
import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup
open CFSG.HardMathSupport.Foote.Proving (card_SL_two_five)

variable {G : Type} [Group G] {t : G} {L₁ L₂ : Subgroup G}

theorem WongHyp.symm (h : WongHyp t L₁ L₂) : WongHyp t L₂ L₁ where
  orderOf_t := h.orderOf_t
  equiv₁ := h.equiv₂
  equiv₂ := h.equiv₁
  commute a ha b hb := (h.commute b hb a ha).symm
  inf_eq := by rw [inf_comm, h.inf_eq]
  relIndex_eq := by rw [sup_comm, h.relIndex_eq]
  sup_oddCore_ne_top := h.sup_oddCore_ne_top

theorem WongHyp.exists_embedding_left (h : WongHyp t L₁ L₂) :
    ∃ i : SL5 →* G, Function.Injective i ∧ i.range = L₁ := by
  obtain ⟨e⟩ := h.equiv₁
  refine ⟨L₁.subtype.comp e.symm.toMonoidHom,
    fun x y hxy => e.symm.injective (Subtype.ext hxy), ?_⟩
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact (e.symm x).2
  · intro hg
    exact ⟨e ⟨g, hg⟩, by simp⟩

theorem WongHyp.exists_mem_centralizer_notMem (h : WongHyp t L₁ L₂) :
    ∃ n ∈ centralizer ({t} : Set G), n ∉ L₁ ⊔ L₂ := by
  refine SetLike.not_le_iff_exists.mp fun hle => ?_
  have h1 := relIndex_eq_one.mpr hle
  rw [h.relIndex_eq] at h1
  exact absurd h1 (by norm_num)

theorem conj_mem_of_commute (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) {k : G}
    (hk : k ∈ L₁ ⊔ L₂) {a : G} (ha : a ∈ L₁) : k * a * k⁻¹ ∈ L₁ := by
  have hle : L₁ ⊔ L₂ ≤ normalizer (L₁ : Set G) := sup_le le_normalizer fun b hb =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun a ha => (hcomm a ha b hb).eq)
  exact (mem_normalizer_iff.mp (hle hk) a).mp ha

theorem exists_mul_eq_of_commute (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) {g : G}
    (hg : g ∈ L₁ ⊔ L₂) : ∃ a ∈ L₁, ∃ b ∈ L₂, a * b = g := by
  have hle : L₁ ≤ normalizer (L₂ : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => (hcomm a ha b hb).eq.symm)
  have hg' : g ∈ ((L₁ ⊔ L₂ : Subgroup G) : Set G) := hg
  rwa [coe_mul_of_left_le_normalizer_right L₁ L₂ hle, Set.mem_mul] at hg'

theorem conj_inv_mem_of_map_eq {H H' : Subgroup G} {n : G}
    (hmap : H.map (MulAut.conj n⁻¹).toMonoidHom = H') {a : G} (ha : a ∈ H) :
    n⁻¹ * a * n ∈ H' := by
  rw [← hmap]
  exact ⟨a, ha, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩

theorem le_or_inf_le_of_conj_mem {i : SL5 →* G} {R : Subgroup G}
    (hR : ∀ x : SL5, ∀ r ∈ R, i x * r * (i x)⁻¹ ∈ R) :
    i.range ≤ R ∨ R ⊓ i.range ≤ zpowers (i (-1)) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hN : (R.comap i).Normal := ⟨fun x hx g => by
    simpa only [mem_comap, map_mul, map_inv] using hR g _ hx⟩
  rcases CFSG.ClassicalInvolution.sl2_normal_cases (by rw [Nat.card_zmod]; norm_num) _ hN with
    hb | hc | ht
  · refine Or.inr fun g hg => ?_
    obtain ⟨hr, x, rfl⟩ := mem_inf.mp hg
    have hx : x ∈ R.comap i := hr
    rw [hb, mem_bot] at hx
    rw [hx, map_one]
    exact one_mem _
  · refine Or.inr fun g hg => ?_
    obtain ⟨hr, x, rfl⟩ := mem_inf.mp hg
    have hx : x ∈ R.comap i := hr
    rw [hc] at hx
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff x).mp hx with rfl | rfl
    · rw [map_one]
      exact one_mem _
    · exact mem_zpowers _
  · refine Or.inl ?_
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ R.comap i := by rw [ht]; exact mem_top x
    exact hx

theorem commutator_le_of_inf_le {M Z : Subgroup G} (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b)
    (hM : ∀ k ∈ L₁ ⊔ L₂, ∀ m ∈ M, k * m * k⁻¹ ∈ M) (hMK : M ≤ L₁ ⊔ L₂) (hZ₁ : M ⊓ L₁ ≤ Z)
    (hZ₂ : M ⊓ L₂ ≤ Z) (hZ : Z ≤ centralizer (L₁ : Set G)) : ⁅M, M⁆ ≤ Z := by
  have hcomm' : ∀ b ∈ L₂, ∀ a ∈ L₁, Commute b a := fun b hb a ha => (hcomm a ha b hb).symm
  have hc : ∀ m ∈ M, ∀ L : Subgroup G, M ⊓ L ≤ Z → (∀ k ∈ M, ∀ a ∈ L, k * a * k⁻¹ ∈ L) →
      L ≤ L₁ ⊔ L₂ → ∀ a ∈ L, m * a * m⁻¹ * a⁻¹ ∈ Z := by
    intro m hm L hZL hL hLK a ha
    refine hZL ⟨?_, L.mul_mem (hL m hm a ha) (L.inv_mem ha)⟩
    rw [show m * a * m⁻¹ * a⁻¹ = m * (a * m⁻¹ * a⁻¹) by group]
    exact M.mul_mem hm (hM a (hLK ha) _ (M.inv_mem hm))
  rw [commutator_le]
  intro m hm m' hm'
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_commute hcomm (hMK hm')
  have h₁ := hc m hm L₁ hZ₁ (fun k hk a ha => conj_mem_of_commute hcomm (hMK hk) ha)
    le_sup_left a ha
  have h₂ := hc m hm L₂ hZ₂
    (fun k hk b hb => conj_mem_of_commute hcomm' (by rw [sup_comm]; exact hMK hk) hb)
    le_sup_right b hb
  have e : a * (m * b * m⁻¹ * b⁻¹) * a⁻¹ = m * b * m⁻¹ * b⁻¹ := by
    rw [mem_centralizer_iff.mp (hZ h₂) a ha, mul_inv_cancel_right]
  rw [commutatorElement_def, show m * (a * b) * m⁻¹ * (a * b)⁻¹ =
    (m * a * m⁻¹ * a⁻¹) * (a * (m * b * m⁻¹ * b⁻¹) * a⁻¹) by group, e]
  exact Z.mul_mem h₁ h₂

theorem WongHyp.eq_or_eq_of_normal [Finite G] (h : WongHyp t L₁ L₂) {M : Subgroup G}
    (hMK : M ≤ L₁ ⊔ L₂) (hM : ∀ k ∈ L₁ ⊔ L₂, ∀ m ∈ M, k * m * k⁻¹ ∈ M) (hperf : ⁅M, M⁆ = M)
    (hcard : Nat.card M = 120) : M = L₁ ∨ M = L₂ := by
  obtain ⟨j₁, hj₁, hr₁⟩ := h.exists_embedding_left
  obtain ⟨j₂, hj₂, hr₂⟩ := h.symm.exists_embedding_left
  have hc₁ : Nat.card L₁ = 120 := by
    obtain ⟨e⟩ := h.equiv₁
    rw [Nat.card_congr e.toEquiv, card_SL_two_five]
  have hc₂ : Nat.card L₂ = 120 := by
    obtain ⟨e⟩ := h.equiv₂
    rw [Nat.card_congr e.toEquiv, card_SL_two_five]
  have htt : t ∈ L₁ ⊓ L₂ := by rw [h.inf_eq]; exact mem_zpowers t
  have ht₁ : t ∈ j₁.range := by rw [hr₁]; exact htt.1
  have ht₂ : t ∈ j₂.range := by rw [hr₂]; exact htt.2
  rcases le_or_inf_le_of_conj_mem (i := j₁) (R := M) fun x m hm =>
      hM _ (mem_sup_left (by rw [← hr₁]; exact ⟨x, rfl⟩)) m hm with h₁ | h₁
  · rw [hr₁] at h₁
    exact Or.inl (eq_of_le_of_card_ge h₁ (hcard.trans hc₁.symm).le).symm
  rcases le_or_inf_le_of_conj_mem (i := j₂) (R := M) fun x m hm =>
      hM _ (mem_sup_right (by rw [← hr₂]; exact ⟨x, rfl⟩)) m hm with h₂ | h₂
  · rw [hr₂] at h₂
    exact Or.inr (eq_of_le_of_card_ge h₂ (hcard.trans hc₂.symm).le).symm
  rw [hr₁, ← eq_apply_neg_one hj₁ h.orderOf_t ht₁] at h₁
  rw [hr₂, ← eq_apply_neg_one hj₂ h.orderOf_t ht₂] at h₂
  have hZ : zpowers t ≤ centralizer (L₁ : Set G) :=
    zpowers_le.mpr (mem_centralizer_iff.mpr fun a ha => (h.commute a ha t htt.2).eq)
  have hle := commutator_le_of_inf_le h.commute hM hMK h₁ h₂ hZ
  rw [hperf] at hle
  have := card_le_of_le hle
  rw [hcard, Nat.card_zpowers, h.orderOf_t] at this
  omega

theorem WongHyp.map_conj_eq_or_eq [Finite G] (h : WongHyp t L₁ L₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) :
    L₁.map (MulAut.conj n).toMonoidHom = L₁ ∨ L₁.map (MulAut.conj n).toMonoidHom = L₂ := by
  obtain ⟨e₁⟩ := h.equiv₁
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Group.IsPerfect L₁ :=
    CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 (by rw [Nat.card_zmod]; norm_num) e₁
  have hK : ∀ k, k ∈ L₁ ⊔ L₂ ↔ n * k * n⁻¹ ∈ L₁ ⊔ L₂ :=
    mem_normalizer_iff.mp (h.centralizer_le_normalizer_sup hn)
  refine h.eq_or_eq_of_normal ?_ ?_ (by rw [← map_commutator, commutator_eq_self]) ?_
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (hK a).mp (mem_sup_left ha)
  · rintro k hk _ ⟨a, ha, rfl⟩
    have hk' : n⁻¹ * k * n ∈ L₁ ⊔ L₂ := by
      rw [hK, show n * (n⁻¹ * k * n) * n⁻¹ = k by group]
      exact hk
    refine ⟨n⁻¹ * k * n * a * (n⁻¹ * k * n)⁻¹, conj_mem_of_commute h.commute hk' ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [card_map_of_injective (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective,
      Nat.card_congr e₁.toEquiv, card_SL_two_five]

theorem WongHyp.map_conj_inv_eq [Finite G] (h : WongHyp t L₁ L₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) :
    (L₁.map (MulAut.conj n⁻¹).toMonoidHom = L₁ ∧ L₂.map (MulAut.conj n⁻¹).toMonoidHom = L₂) ∨
      (L₁.map (MulAut.conj n⁻¹).toMonoidHom = L₂ ∧
        L₂.map (MulAut.conj n⁻¹).toMonoidHom = L₁) := by
  have hne : L₁ ≠ L₂ := by
    intro he
    have h2 := congrArg (fun H : Subgroup G => Nat.card H) h.inf_eq
    obtain ⟨e⟩ := h.equiv₂
    simp only [he, inf_idem, Nat.card_zpowers, h.orderOf_t] at h2
    rw [Nat.card_congr e.toEquiv, card_SL_two_five] at h2
    omega
  have hinj := map_injective (f := (MulAut.conj n⁻¹).toMonoidHom) (MulAut.conj n⁻¹).injective
  rcases h.map_conj_eq_or_eq (inv_mem hn) with h₁ | h₁ <;>
    rcases h.symm.map_conj_eq_or_eq (inv_mem hn) with h₂ | h₂
  · exact Or.inl ⟨h₁, h₂⟩
  · exact absurd (hinj (h₁.trans h₂.symm)) hne
  · exact absurd (hinj (h₁.trans h₂.symm)) hne
  · exact Or.inr ⟨h₁, h₂⟩

theorem exists_conj_eq_or {i : SL5 →* G} (hi : Function.Injective i) {n : G}
    (hn : ∀ x, n⁻¹ * i x * n ∈ i.range) :
    ∃ g : SL5, (∀ x, n⁻¹ * i x * n = i (g * x * g⁻¹)) ∨
      ∀ x, n⁻¹ * i x * n = i (g * deltaAut x * g⁻¹) := by
  choose f hf using fun x => MonoidHom.mem_range.mp (hn x)
  have hmul : ∀ x y, f (x * y) = f x * f y := fun x y => hi (by
    rw [map_mul i (f x), hf, hf, hf, map_mul]
    group)
  have hinj : Function.Injective f := fun x y hxy => hi (by
    have h' := congrArg i hxy
    rw [hf, hf] at h'
    exact mul_left_cancel (mul_right_cancel h'))
  obtain ⟨g, hg | hg⟩ := exists_eq_conj_or_conj_deltaAut
    (MulEquiv.ofBijective (MonoidHom.mk' f hmul) ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩)
  · exact ⟨g, Or.inl fun x => by rw [← hf, ← hg x]; rfl⟩
  · exact ⟨g, Or.inr fun x => by rw [← hf, ← hg x]; rfl⟩

theorem conj_mul_mul_eq {i₁ i₂ : SL5 →* G} (hcomm : ∀ x y, Commute (i₁ x) (i₂ y)) {n : G}
    {g₁ g₂ : SL5} {f₁ f₂ : SL5 → SL5} (h₁ : ∀ x, n⁻¹ * i₁ x * n = i₁ (g₁ * f₁ x * g₁⁻¹))
    (h₂ : ∀ x, n⁻¹ * i₂ x * n = i₂ (g₂ * f₂ x * g₂⁻¹)) (x : SL5) :
    (n * i₁ g₁ * i₂ g₂)⁻¹ * i₁ x * (n * i₁ g₁ * i₂ g₂) = i₁ (f₁ x) ∧
      (n * i₁ g₁ * i₂ g₂)⁻¹ * i₂ x * (n * i₁ g₁ * i₂ g₂) = i₂ (f₂ x) := by
  have e : ∀ y, (n * i₁ g₁ * i₂ g₂)⁻¹ * y * (n * i₁ g₁ * i₂ g₂) =
      (i₂ g₂)⁻¹ * ((i₁ g₁)⁻¹ * (n⁻¹ * y * n) * i₁ g₁) * i₂ g₂ := fun y => by group
  have c : ∀ {a b : G}, a * b = b * a → a⁻¹ * b * a = b := fun hab => by
    rw [mul_assoc, ← hab, inv_mul_cancel_left]
  constructor
  · rw [e, h₁, map_mul, map_mul, map_inv,
      show (i₁ g₁)⁻¹ * (i₁ g₁ * i₁ (f₁ x) * (i₁ g₁)⁻¹) * i₁ g₁ = i₁ (f₁ x) by group]
    exact c (hcomm _ _).symm.eq
  · rw [e, h₂, c (hcomm g₁ _).eq, map_mul, map_mul, map_inv]
    group

theorem WongHyp.sq_eq_one_or_eq_of_conj [Finite G] (h : WongHyp t L₁ L₂) {i₁ i₂ : SL5 →* G}
    (hr₁ : i₁.range = L₁) (hr₂ : i₂.range = L₂) {n : G} (hn : n ∈ centralizer ({t} : Set G))
    {f₁ f₂ : SL5 → SL5} (hf₁ : ∀ x, f₁ (f₁ x) = x) (hf₂ : ∀ x, f₂ (f₂ x) = x)
    (h₁ : ∀ x, n⁻¹ * i₁ x * n = i₁ (f₁ x)) (h₂ : ∀ x, n⁻¹ * i₂ x * n = i₂ (f₂ x)) :
    n ^ 2 = 1 ∨ n ^ 2 = t := by
  have hc : ∀ (i : SL5 →* G) (f : SL5 → SL5), (∀ x, f (f x) = x) →
      (∀ x, n⁻¹ * i x * n = i (f x)) → i.range ≤ centralizer ({n ^ 2} : Set G) := by
    rintro i f hf hi _ ⟨x, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have e : (n ^ 2)⁻¹ * i x * n ^ 2 = i x := by
      rw [pow_two, show (n * n)⁻¹ * i x * (n * n) = n⁻¹ * (n⁻¹ * i x * n) * n by group, hi, hi,
        hf]
    calc i x * n ^ 2 = n ^ 2 * ((n ^ 2)⁻¹ * i x * n ^ 2) := by group
      _ = n ^ 2 * i x := by rw [e]
  have hle : L₁ ⊔ L₂ ≤ centralizer ({n ^ 2} : Set G) := by
    rw [← hr₁, ← hr₂]
    exact sup_le (hc i₁ f₁ hf₁ h₁) (hc i₂ f₂ hf₂ h₂)
  have hmem : n ^ 2 ∈ (L₁ ⊔ L₂) ⊓ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) :=
    ⟨h.sq_mem_sup hn, mem_centralizer_iff.mpr fun k hk => mem_centralizer_singleton_iff.mp (hle hk)⟩
  rw [h.sup_inf_centralizer] at hmem
  exact (mem_zpowers_of_orderOf_eq_two h.orderOf_t).mp hmem

theorem WongHyp.sq_mul_inv_eq (h : WongHyp t L₁ L₂) {n₀ a b : G} (ha : a ∈ L₁) (hb : b ∈ L₂)
    (hab : a * b = n₀ ^ 2) (hc₁ : ∀ x ∈ L₁, n₀⁻¹ * x * n₀ ∈ L₂)
    (hc₂ : ∀ y ∈ L₂, n₀⁻¹ * y * n₀ ∈ L₁) : (n₀ * a⁻¹) ^ 2 = 1 ∨ (n₀ * a⁻¹) ^ 2 = t := by
  have hb' := hc₁ _ (inv_mem ha)
  have h₂ : (n₀ * a⁻¹) ^ 2 ∈ L₂ := by
    have e : (n₀ * a⁻¹) ^ 2 = a * (b * (n₀⁻¹ * a⁻¹ * n₀)) * a⁻¹ := by
      rw [← mul_assoc a b, hab]
      simp only [pow_two]
      group
    rw [e, (h.commute a ha _ (mul_mem hb hb')).eq, mul_inv_cancel_right]
    exact mul_mem hb hb'
  have h₁ : (n₀ * a⁻¹) ^ 2 ∈ L₁ := by
    have e : (n₀ * a⁻¹) ^ 2 = a * (n₀⁻¹ * (n₀ * a⁻¹) ^ 2 * n₀) * a⁻¹ := by
      simp only [pow_two]
      group
    rw [e]
    exact mul_mem (mul_mem ha (hc₂ _ h₂)) (inv_mem ha)
  have hmem : (n₀ * a⁻¹) ^ 2 ∈ L₁ ⊓ L₂ := ⟨h₁, h₂⟩
  rw [h.inf_eq] at hmem
  exact (mem_zpowers_of_orderOf_eq_two h.orderOf_t).mp hmem

private abbrev NormalFormConcl (s : G) (M₁ M₂ : Subgroup G) : Prop :=
  ∃ (i₁ i₂ : SL5 →* G) (n : G), Function.Injective i₁ ∧ Function.Injective i₂ ∧
    ((i₁.range = M₁ ∧ i₂.range = M₂) ∨ (i₁.range = M₂ ∧ i₂.range = M₁)) ∧
    n ∈ centralizer ({s} : Set G) ∧ n ∉ M₁ ⊔ M₂ ∧
    M₁ ⊔ M₂ ⊔ zpowers n = centralizer ({s} : Set G) ∧ (n ^ 2 = 1 ∨ n ^ 2 = s) ∧
    ((∀ x, n⁻¹ * i₁ x * n = i₁ x ∧ n⁻¹ * i₂ x * n = i₂ x) ∨
      (∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ x) ∨
      (∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ (deltaAut x)) ∨
      (∀ x, n⁻¹ * i₁ x * n = i₂ x ∧ n⁻¹ * i₂ x * n = i₁ x))

private theorem WongHyp.exists_normalForm_of_map_eq [Finite G] (h : WongHyp t L₁ L₂)
    {j₁ j₂ : SL5 →* G} (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂)
    (hr₁ : j₁.range = L₁) (hr₂ : j₂.range = L₂) {n₀ : G}
    (hn₀ : n₀ ∈ centralizer ({t} : Set G)) (hn₀K : n₀ ∉ L₁ ⊔ L₂)
    (hm₁ : L₁.map (MulAut.conj n₀⁻¹).toMonoidHom = L₁)
    (hm₂ : L₂.map (MulAut.conj n₀⁻¹).toMonoidHom = L₂) : NormalFormConcl t L₁ L₂ := by
  have hmem₁ : ∀ x, j₁ x ∈ L₁ := fun x => by rw [← hr₁]; exact ⟨x, rfl⟩
  have hmem₂ : ∀ x, j₂ x ∈ L₂ := fun x => by rw [← hr₂]; exact ⟨x, rfl⟩
  have hcomm : ∀ x y, Commute (j₁ x) (j₂ y) := fun x y => h.commute _ (hmem₁ x) _ (hmem₂ y)
  obtain ⟨g₁, hg₁⟩ := exists_conj_eq_or hj₁ fun x => by
    rw [hr₁]; exact conj_inv_mem_of_map_eq hm₁ (hmem₁ x)
  obtain ⟨g₂, hg₂⟩ := exists_conj_eq_or hj₂ fun x => by
    rw [hr₂]; exact conj_inv_mem_of_map_eq hm₂ (hmem₂ x)
  have hgK : j₁ g₁ * j₂ g₂ ∈ L₁ ⊔ L₂ :=
    mul_mem (mem_sup_left (hmem₁ g₁)) (mem_sup_right (hmem₂ g₂))
  have hn : n₀ * j₁ g₁ * j₂ g₂ ∈ centralizer ({t} : Set G) := by
    rw [mul_assoc]
    exact mul_mem hn₀ (h.sup_le_centralizer hgK)
  have hnK : n₀ * j₁ g₁ * j₂ g₂ ∉ L₁ ⊔ L₂ := fun hK => hn₀K (by
    have e : n₀ * j₁ g₁ * j₂ g₂ * (j₁ g₁ * j₂ g₂)⁻¹ = n₀ := by group
    rw [← e]
    exact mul_mem hK (inv_mem hgK))
  have hsup := h.sup_zpowers_eq_centralizer hn hnK
  rcases hg₁ with hg₁ | hg₁ <;> rcases hg₂ with hg₂ | hg₂
  · have hc := conj_mul_mul_eq hcomm (f₁ := fun x => x) (f₂ := fun x => x) hg₁ hg₂
    exact ⟨j₁, j₂, n₀ * j₁ g₁ * j₂ g₂, hj₁, hj₂, Or.inl ⟨hr₁, hr₂⟩, hn, hnK, hsup,
      h.sq_eq_one_or_eq_of_conj hr₁ hr₂ hn (f₁ := fun x => x) (f₂ := fun x => x)
        (fun _ => rfl) (fun _ => rfl) (fun x => (hc x).1) (fun x => (hc x).2), Or.inl hc⟩
  · have hc := conj_mul_mul_eq hcomm (f₁ := fun x => x) (f₂ := deltaAut) hg₁ hg₂
    exact ⟨j₂, j₁, n₀ * j₁ g₁ * j₂ g₂, hj₂, hj₁, Or.inr ⟨hr₂, hr₁⟩, hn, hnK, hsup,
      h.sq_eq_one_or_eq_of_conj hr₁ hr₂ hn (f₁ := fun x => x) (f₂ := deltaAut)
        (fun _ => rfl) deltaAut_deltaAut (fun x => (hc x).1) (fun x => (hc x).2),
      Or.inr (Or.inl fun x => ⟨(hc x).2, (hc x).1⟩)⟩
  · have hc := conj_mul_mul_eq hcomm (f₁ := deltaAut) (f₂ := fun x => x) hg₁ hg₂
    exact ⟨j₁, j₂, n₀ * j₁ g₁ * j₂ g₂, hj₁, hj₂, Or.inl ⟨hr₁, hr₂⟩, hn, hnK, hsup,
      h.sq_eq_one_or_eq_of_conj hr₁ hr₂ hn (f₁ := deltaAut) (f₂ := fun x => x)
        deltaAut_deltaAut (fun _ => rfl) (fun x => (hc x).1) (fun x => (hc x).2),
      Or.inr (Or.inl hc)⟩
  · have hc := conj_mul_mul_eq hcomm (f₁ := deltaAut) (f₂ := deltaAut) hg₁ hg₂
    exact ⟨j₁, j₂, n₀ * j₁ g₁ * j₂ g₂, hj₁, hj₂, Or.inl ⟨hr₁, hr₂⟩, hn, hnK, hsup,
      h.sq_eq_one_or_eq_of_conj hr₁ hr₂ hn (f₁ := deltaAut) (f₂ := deltaAut)
        deltaAut_deltaAut deltaAut_deltaAut (fun x => (hc x).1) (fun x => (hc x).2),
      Or.inr (Or.inr (Or.inl hc))⟩

private theorem WongHyp.exists_normalForm_of_swap [Finite G] (h : WongHyp t L₁ L₂)
    {j₁ : SL5 →* G} (hj₁ : Function.Injective j₁) (hr₁ : j₁.range = L₁) {n₀ : G}
    (hn₀ : n₀ ∈ centralizer ({t} : Set G)) (hn₀K : n₀ ∉ L₁ ⊔ L₂)
    (hm₁ : L₁.map (MulAut.conj n₀⁻¹).toMonoidHom = L₂)
    (hm₂ : L₂.map (MulAut.conj n₀⁻¹).toMonoidHom = L₁) : NormalFormConcl t L₁ L₂ := by
  have hmem : ∀ x, j₁ x ∈ L₁ := fun x => by rw [← hr₁]; exact ⟨x, rfl⟩
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_eq_of_commute h.commute (h.sq_mem_sup hn₀)
  have hn : n₀ * a⁻¹ ∈ centralizer ({t} : Set G) :=
    mul_mem hn₀ (inv_mem (h.sup_le_centralizer (mem_sup_left ha)))
  have hnK : n₀ * a⁻¹ ∉ L₁ ⊔ L₂ := fun hK => hn₀K (by
    have := mul_mem hK (mem_sup_left ha : a ∈ L₁ ⊔ L₂)
    rwa [inv_mul_cancel_right] at this)
  have hsq := h.sq_mul_inv_eq ha hb hab (fun _ => conj_inv_mem_of_map_eq hm₁)
    (fun _ => conj_inv_mem_of_map_eq hm₂)
  have ht₂ : t ∈ L₂ := by
    have : t ∈ L₁ ⊓ L₂ := by rw [h.inf_eq]; exact mem_zpowers t
    exact this.2
  obtain ⟨i₂, hi₂⟩ : ∃ i₂ : SL5 →* G, i₂ = (MulAut.conj n₀⁻¹).toMonoidHom.comp j₁ := ⟨_, rfl⟩
  have hi₂x : ∀ x, i₂ x = n₀⁻¹ * j₁ x * n₀ := fun x => by
    rw [hi₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hact₁ : ∀ x, (n₀ * a⁻¹)⁻¹ * j₁ x * (n₀ * a⁻¹) = i₂ x := fun x => by
    rw [hi₂x, show (n₀ * a⁻¹)⁻¹ * j₁ x * (n₀ * a⁻¹) = a * (n₀⁻¹ * j₁ x * n₀) * a⁻¹ by group,
      (h.commute a ha _ (conj_inv_mem_of_map_eq hm₁ (hmem x))).eq, mul_inv_cancel_right]
  have hact₂ : ∀ x, (n₀ * a⁻¹)⁻¹ * i₂ x * (n₀ * a⁻¹) = j₁ x := fun x => by
    have hz : Commute ((n₀ * a⁻¹) ^ 2) (j₁ x) := by
      rcases hsq with h1 | h1 <;> rw [h1]
      · exact Commute.one_left _
      · exact (h.commute _ (hmem x) t ht₂).symm
    rw [← hact₁, show ∀ m y : G, m⁻¹ * (m⁻¹ * y * m) * m = (m ^ 2)⁻¹ * (y * m ^ 2) from
      fun m y => by simp only [pow_two]; group, ← hz.eq, inv_mul_cancel_left]
  refine ⟨j₁, i₂, n₀ * a⁻¹, hj₁, ?_, Or.inl ⟨hr₁, ?_⟩, hn, hnK,
    h.sup_zpowers_eq_centralizer hn hnK, hsq,
    Or.inr (Or.inr (Or.inr fun x => ⟨hact₁ x, hact₂ x⟩))⟩
  · rw [hi₂]
    exact fun x y hxy => hj₁ ((MulAut.conj n₀⁻¹).injective hxy)
  · rw [hi₂, MonoidHom.range_comp, hr₁, hm₁]

theorem WongHyp.exists_normalForm [Finite G] (h : WongHyp t L₁ L₂) :
    ∃ (i₁ i₂ : SL5 →* G) (n : G), Function.Injective i₁ ∧ Function.Injective i₂ ∧
      ((i₁.range = L₁ ∧ i₂.range = L₂) ∨ (i₁.range = L₂ ∧ i₂.range = L₁)) ∧
      n ∈ centralizer ({t} : Set G) ∧ n ∉ L₁ ⊔ L₂ ∧
      L₁ ⊔ L₂ ⊔ zpowers n = centralizer ({t} : Set G) ∧ (n ^ 2 = 1 ∨ n ^ 2 = t) ∧
      ((∀ x, n⁻¹ * i₁ x * n = i₁ x ∧ n⁻¹ * i₂ x * n = i₂ x) ∨
        (∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ x) ∨
        (∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ (deltaAut x)) ∨
        (∀ x, n⁻¹ * i₁ x * n = i₂ x ∧ n⁻¹ * i₂ x * n = i₁ x)) := by
  obtain ⟨j₁, hj₁, hr₁⟩ := h.exists_embedding_left
  obtain ⟨j₂, hj₂, hr₂⟩ := h.symm.exists_embedding_left
  obtain ⟨n₀, hn₀, hn₀K⟩ := h.exists_mem_centralizer_notMem
  rcases h.map_conj_inv_eq hn₀ with ⟨hm₁, hm₂⟩ | ⟨hm₁, hm₂⟩
  · exact WongHyp.exists_normalForm_of_map_eq h hj₁ hj₂ hr₁ hr₂ hn₀ hn₀K hm₁ hm₂
  · exact WongHyp.exists_normalForm_of_swap h hj₁ hr₁ hn₀ hn₀K hm₁ hm₂

end CFSG.OddTranspositions.PartThree.Wong

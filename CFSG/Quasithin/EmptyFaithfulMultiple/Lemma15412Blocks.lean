module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Group
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.E2SolvTwo

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

section OrderSix

variable {K : Type*} [Group K] {L : Subgroup K}

theorem index_zpowers_eq_two (hL : Nat.card L = 6) {f : K} (hf : f ∈ L) (h3 : orderOf f = 3) :
    ((Subgroup.zpowers f).subgroupOf L).index = 2 := by
  have h := Subgroup.relIndex_mul_card (Subgroup.zpowers f) L
  rw [inf_eq_left.2 (Subgroup.zpowers_le.mpr hf), Nat.card_zpowers, h3, hL] at h
  show (Subgroup.zpowers f).relIndex L = 2
  omega

theorem mul_self_mem_zpowers (hL : Nat.card L = 6) {f : K} (hf : f ∈ L) (h3 : orderOf f = 3)
    {l : K} (hl : l ∈ L) : l * l ∈ Subgroup.zpowers f := by
  have hsq := Subgroup.mul_self_mem_of_index_two (index_zpowers_eq_two hL hf h3) ⟨l, hl⟩
  rw [Subgroup.mem_subgroupOf] at hsq
  simpa using hsq

theorem eq_inv_mul_self {x : K} (hx : x ^ 3 = 1) : x = (x * x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← hx, pow_three]

theorem zpowers_eq_of_card_six [Finite K] (hL : Nat.card L = 6) {f f' : K} (hf : f ∈ L)
    (hf' : f' ∈ L) (h3 : orderOf f = 3) (h3' : orderOf f' = 3) :
    Subgroup.zpowers f' = Subgroup.zpowers f := by
  have h3'' : f' ^ 3 = 1 := by rw [← h3']; exact pow_orderOf_eq_one f'
  have hmem : f' ∈ Subgroup.zpowers f := by
    rw [eq_inv_mul_self h3'']
    exact (Subgroup.zpowers f).inv_mem (mul_self_mem_zpowers hL hf h3 hf')
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, h3, h3']

theorem mem_zpowers_three {f x : K} (hf3 : orderOf f = 3) (hx : x ∈ Subgroup.zpowers f) :
    x = 1 ∨ x = f ∨ x = f ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hf3]
  have hr : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hr with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero f)
  · exact Or.inr (Or.inl (zpow_one f))
  · exact Or.inr (Or.inr (zpow_ofNat f 2))

theorem conj_eq_inv (hL : Nat.card L = 6) {f t : K} (hf : f ∈ L) (ht : t ∈ L)
    (h3 : orderOf f = 3) (hnc : t * f ≠ f * t) : t * f * t⁻¹ = f⁻¹ := by
  have hf3 : f ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one f
  have hmem : t * f * t⁻¹ ∈ Subgroup.zpowers f := by
    have hn := Subgroup.normal_of_index_eq_two (index_zpowers_eq_two hL hf h3)
    have := hn.conj_mem ⟨f, hf⟩ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers f)) ⟨t, ht⟩
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hf1 : f ≠ 1 := fun h => by rw [h, orderOf_one] at h3; norm_num at h3
  rcases mem_zpowers_three h3 hmem with h | h | h
  · exfalso
    apply hf1
    have : f = t⁻¹ * (t * f * t⁻¹) * t := by group
    rw [this, h]
    group
  · exfalso
    apply hnc
    calc t * f = t * f * t⁻¹ * t := by group
      _ = f * t := by rw [h]
  · rw [h, eq_inv_iff_mul_eq_one, ← pow_succ, hf3]

theorem conj_eq_inv_of_mem_zpowers {f t : K} (htf : t * f * t⁻¹ = f⁻¹) {a : K}
    (ha : a ∈ Subgroup.zpowers f) : t * a * t⁻¹ = a⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have h : (MulAut.conj t) (f ^ k) = ((MulAut.conj t) f) ^ k := map_zpow _ f k
  simp only [MulAut.conj_apply] at h
  rw [h, htf, inv_zpow]

theorem mem_zpowers_of_odd (hL : Nat.card L = 6) {f : K} (hf : f ∈ L) (h3 : orderOf f = 3)
    {x : K} (hx : x ∈ L) (hodd : Odd (orderOf x)) : x ∈ Subgroup.zpowers f := by
  have hcop : Nat.Coprime 2 (orderOf x) := Nat.coprime_two_left.mpr hodd
  have h1 : x ∈ Subgroup.zpowers (x ^ 2) := A4.mem_zpowers_pow_of_coprime hcop
  have h2 : x ^ 2 ∈ Subgroup.zpowers f := by
    rw [pow_two]
    exact mul_self_mem_zpowers hL hf h3 hx
  exact (Subgroup.zpowers_le.mpr h2) h1

theorem eq_bot_or_eq_of_le_zpowers [Finite K] {f : K} (h3 : orderOf f = 3) {X : Subgroup K}
    (hX : X ≤ Subgroup.zpowers f) : X = ⊥ ∨ X = Subgroup.zpowers f := by
  have hdvd : Nat.card X ∣ 3 := by
    have := Subgroup.card_dvd_of_le hX
    rwa [Nat.card_zpowers, h3] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact Or.inl (Subgroup.eq_bot_of_card_eq X h)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hX (by rw [Nat.card_zpowers, h3, h]))

end OrderSix

section ElemThree

variable {K : Type*} [Group K]

theorem isElemAbelian_sup {p : ℕ} {A B : Subgroup K} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian p (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB h

theorem isElemAbelian_zpowers {p : ℕ} {f : K} (hf : f ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers f) := CFSG.Open.isElemAbelian_zpowers hf

end ElemThree

section BlockSystem

variable {W : Type*} [CommGroup W] {J : Subgroup (MulAut W)}
  {𝓗 : Finset (Subgroup (MulAut W))}

theorem conjAut_mul (a b : MulAut W) (L : Subgroup (MulAut W)) :
    B1.conjAut (a * b) L = B1.conjAut a (B1.conjAut b L) := by
  rw [conjAut_eq_map, conjAut_eq_map, conjAut_eq_map, Subgroup.map_map]
  congr 1

theorem conjAut_injective (g : MulAut W) : Function.Injective (B1.conjAut g) := by
  intro A B h
  rw [conjAut_eq_map, conjAut_eq_map] at h
  exact Subgroup.map_injective (MulAut.conj g).injective h

theorem mem_normalizer_iff_conjAut {g : MulAut W} {L : Subgroup (MulAut W)} :
    g ∈ Subgroup.normalizer (L : Set (MulAut W)) ↔ B1.conjAut g L = L := by
  rw [conjAut_eq_map]
  exact Subgroup.mem_normalizer_iff_map_conj_eq

theorem inf_eq_bot_of_ne (hb : IsTransvectionBlocks J 𝓗) {L₁ L₂ : Subgroup (MulAut W)}
    (h₁ : L₁ ∈ 𝓗) (h₂ : L₂ ∈ 𝓗) (hne : L₁ ≠ L₂) : L₁ ⊓ L₂ = ⊥ := by
  refine le_bot_iff.1 ((inf_le_inf_left L₁ ?_).trans (hb.inf_biSup_ne_eq_bot h₁).le)
  exact le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut W)) (_ : H' ∈ 𝓗) => ⨆ (_ : H' ≠ L₁), H')
    L₂ h₂ (le_iSup_of_le (Ne.symm hne) le_rfl)

theorem commSub_inf_eq_bot_of_ne [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hb : IsTransvectionBlocks J 𝓗) {L₁ L₂ : Subgroup (MulAut W)} (h₁ : L₁ ∈ 𝓗) (h₂ : L₂ ∈ 𝓗)
    (hne : L₁ ≠ L₂) : commSub ⊤ L₁ ⊓ commSub ⊤ L₂ = ⊥ := by
  refine le_bot_iff.1 ((inf_le_inf_left _ ?_).trans (hb.commSub_inf_biSup_ne_eq_bot hW h₁).le)
  exact le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut W)) (_ : H' ∈ 𝓗) =>
    ⨆ (_ : H' ≠ L₁), commSub (⊤ : Subgroup W) H') L₂ h₂ (le_iSup_of_le (Ne.symm hne) le_rfl)

theorem le_normalizer_of_ne (hb : IsTransvectionBlocks J 𝓗) {L₁ L₂ : Subgroup (MulAut W)}
    (h₁ : L₁ ∈ 𝓗) (h₂ : L₂ ∈ 𝓗) (hne : L₁ ≠ L₂) :
    L₂ ≤ Subgroup.normalizer (L₁ : Set (MulAut W)) :=
  E2.le_normalizer_of_commute fun b hb' a ha => (hb.comm L₁ h₁ L₂ h₂ hne a ha b hb').symm

theorem mem_sup_zpowers_of_odd (hb : IsTransvectionBlocks J 𝓗) {L₁ L₂ : Subgroup (MulAut W)}
    (h₁ : L₁ ∈ 𝓗) (h₂ : L₂ ∈ 𝓗) (hne : L₁ ≠ L₂) {f₁ f₂ : MulAut W} (hf₁ : f₁ ∈ L₁)
    (hf₂ : f₂ ∈ L₂) (h3₁ : orderOf f₁ = 3) (h3₂ : orderOf f₂ = 3) {x : MulAut W}
    (hx : x ∈ L₁ ⊔ L₂) (hodd : Odd (orderOf x)) :
    x ∈ Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ := by
  obtain ⟨a, ha, b, hb', rfl⟩ := (mem_sup_iff_exists_mul (le_normalizer_of_ne hb h₁ h₂ hne)).mp hx
  have hab : a * b = b * a := hb.comm L₁ h₁ L₂ h₂ hne a ha b hb'
  set m := orderOf (a * b)
  have hm : (a * b) ^ m = 1 := pow_orderOf_eq_one _
  rw [Commute.mul_pow hab m] at hm
  have ham : a ^ m ∈ L₁ ⊓ L₂ := by
    refine ⟨L₁.pow_mem ha m, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hm]
    exact L₂.inv_mem (L₂.pow_mem hb' m)
  rw [inf_eq_bot_of_ne hb h₁ h₂ hne, Subgroup.mem_bot] at ham
  have hbm : b ^ m = 1 := by rwa [ham, one_mul] at hm
  have hao : Odd (orderOf a) := hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ham)
  have hbo : Odd (orderOf b) := hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hbm)
  exact Subgroup.mul_mem_sup (mem_zpowers_of_odd (hb.card_eq L₁ h₁) hf₁ h3₁ ha hao)
    (mem_zpowers_of_odd (hb.card_eq L₂ h₂) hf₂ h3₂ hb' hbo)

theorem mem_of_mul_mem (hb : IsTransvectionBlocks J 𝓗) {L₁ L₂ : Subgroup (MulAut W)}
    (h₁ : L₁ ∈ 𝓗) (h₂ : L₂ ∈ 𝓗) (hne : L₁ ≠ L₂) {f₁ f₂ t₁ t₂ : MulAut W} (hf₁ : f₁ ∈ L₁)
    (hf₂ : f₂ ∈ L₂) (h3₁ : orderOf f₁ = 3) (h3₂ : orderOf f₂ = 3) (ht₁ : t₁ ∈ L₁)
    (ht₂ : t₂ ∈ L₂) (hi₁ : t₁ * f₁ * t₁⁻¹ = f₁⁻¹) (hi₂ : t₂ * f₂ * t₂⁻¹ = f₂⁻¹)
    {D : Subgroup (MulAut W)} (ht₁D : t₁ ∈ Subgroup.normalizer (D : Set (MulAut W)))
    (ht₂D : t₂ ∈ Subgroup.normalizer (D : Set (MulAut W))) {a b : MulAut W}
    (ha : a ∈ Subgroup.zpowers f₁) (hb' : b ∈ Subgroup.zpowers f₂) (hab : a * b ∈ D) :
    a ∈ D ∧ b ∈ D := by
  have haL : a ∈ L₁ := Subgroup.zpowers_le.mpr hf₁ ha
  have hbL : b ∈ L₂ := Subgroup.zpowers_le.mpr hf₂ hb'
  have ha3 : a ^ 3 = 1 :=
    (isElemAbelian_zpowers (by rw [← h3₁]; exact pow_orderOf_eq_one f₁)).2 a ha
  have hb3 : b ^ 3 = 1 :=
    (isElemAbelian_zpowers (by rw [← h3₂]; exact pow_orderOf_eq_one f₂)).2 b hb'
  have hc₁ : t₁ * b * t₁⁻¹ = b := by
    rw [hb.comm L₁ h₁ L₂ h₂ hne t₁ ht₁ b hbL, mul_inv_cancel_right]
  have hc₂ : t₂ * a * t₂⁻¹ = a := by
    rw [← hb.comm L₁ h₁ L₂ h₂ hne a haL t₂ ht₂, mul_inv_cancel_right]
  have e₁ : t₁ * (a * b) * t₁⁻¹ = a⁻¹ * b := by
    calc t₁ * (a * b) * t₁⁻¹ = (t₁ * a * t₁⁻¹) * (t₁ * b * t₁⁻¹) := by group
      _ = a⁻¹ * b := by rw [conj_eq_inv_of_mem_zpowers hi₁ ha, hc₁]
  have e₂ : t₂ * (a * b) * t₂⁻¹ = a * b⁻¹ := by
    calc t₂ * (a * b) * t₂⁻¹ = (t₂ * a * t₂⁻¹) * (t₂ * b * t₂⁻¹) := by group
      _ = a * b⁻¹ := by rw [conj_eq_inv_of_mem_zpowers hi₂ hb', hc₂]
  have hD₁ : a⁻¹ * b ∈ D := e₁ ▸ (Subgroup.mem_normalizer_iff.mp ht₁D _).mp hab
  have hD₂ : a * b⁻¹ ∈ D := e₂ ▸ (Subgroup.mem_normalizer_iff.mp ht₂D _).mp hab
  have haa : a * a ∈ D := by
    have := D.mul_mem hab (D.inv_mem hD₁)
    have e : a * b * (a⁻¹ * b)⁻¹ = a * a := by
      have hcomm : a * b = b * a := hb.comm L₁ h₁ L₂ h₂ hne a haL b hbL
      calc a * b * (a⁻¹ * b)⁻¹ = a * b * (b⁻¹ * a) := by group
        _ = a * a := by group
    rwa [e] at this
  have hbb : b * b ∈ D := by
    have := D.mul_mem hab (D.inv_mem hD₂)
    have hcomm : Commute a b := hb.comm L₁ h₁ L₂ h₂ hne a haL b hbL
    have hc2 : Commute a (b * b) := hcomm.mul_right hcomm
    have e : a * b * (a * b⁻¹)⁻¹ = b * b := by
      calc a * b * (a * b⁻¹)⁻¹ = a * (b * b) * a⁻¹ := by group
        _ = b * b := by rw [hc2.eq, mul_inv_cancel_right]
    rwa [e] at this
  constructor
  · rw [eq_inv_mul_self ha3]
    exact D.inv_mem haa
  · rw [eq_inv_mul_self hb3]
    exact D.inv_mem hbb

theorem eq_of_le_sup_zpowers [Finite W] (hb : IsTransvectionBlocks J 𝓗)
    {L₁ L₂ : Subgroup (MulAut W)} (h₁ : L₁ ∈ 𝓗) (h₂ : L₂ ∈ 𝓗) (hne : L₁ ≠ L₂)
    {f₁ f₂ t₁ t₂ : MulAut W} (hf₁ : f₁ ∈ L₁) (hf₂ : f₂ ∈ L₂) (h3₁ : orderOf f₁ = 3)
    (h3₂ : orderOf f₂ = 3) (ht₁ : t₁ ∈ L₁) (ht₂ : t₂ ∈ L₂) (hi₁ : t₁ * f₁ * t₁⁻¹ = f₁⁻¹)
    (hi₂ : t₂ * f₂ * t₂⁻¹ = f₂⁻¹) {D : Subgroup (MulAut W)}
    (ht₁D : t₁ ∈ Subgroup.normalizer (D : Set (MulAut W)))
    (ht₂D : t₂ ∈ Subgroup.normalizer (D : Set (MulAut W)))
    (hD : D ≤ Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂) :
    D = ⊥ ∨ D = Subgroup.zpowers f₁ ∨ D = Subgroup.zpowers f₂ ∨
      D = Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ := by
  have hN : Subgroup.zpowers f₂ ≤ Subgroup.normalizer ((Subgroup.zpowers f₁ : Subgroup _) :
      Set (MulAut W)) :=
    E2.le_normalizer_of_commute fun b hb' a ha =>
      (hb.comm L₁ h₁ L₂ h₂ hne a (Subgroup.zpowers_le.mpr hf₁ ha) b
        (Subgroup.zpowers_le.mpr hf₂ hb')).symm
  have hsplit : D = (D ⊓ Subgroup.zpowers f₁) ⊔ (D ⊓ Subgroup.zpowers f₂) := by
    refine le_antisymm (fun d hd => ?_) (sup_le inf_le_left inf_le_left)
    obtain ⟨a, ha, b, hb', rfl⟩ := (mem_sup_iff_exists_mul hN).mp (hD hd)
    obtain ⟨haD, hbD⟩ := mem_of_mul_mem hb h₁ h₂ hne hf₁ hf₂ h3₁ h3₂ ht₁ ht₂ hi₁ hi₂ ht₁D ht₂D
      ha hb' hd
    exact Subgroup.mul_mem_sup ⟨haD, ha⟩ ⟨hbD, hb'⟩
  rcases eq_bot_or_eq_of_le_zpowers h3₁ (inf_le_right : D ⊓ Subgroup.zpowers f₁ ≤ _) with
    e₁ | e₁ <;>
  rcases eq_bot_or_eq_of_le_zpowers h3₂ (inf_le_right : D ⊓ Subgroup.zpowers f₂ ≤ _) with
    e₂ | e₂
  · rw [e₁, e₂, bot_sup_eq] at hsplit
    exact Or.inl hsplit
  · rw [e₁, e₂, bot_sup_eq] at hsplit
    exact Or.inr (Or.inr (Or.inl hsplit))
  · rw [e₁, e₂, sup_bot_eq] at hsplit
    exact Or.inr (Or.inl hsplit)
  · rw [e₁, e₂] at hsplit
    exact Or.inr (Or.inr (Or.inr hsplit))

theorem conjAut_zpowers_eq [Finite W] (hb : IsTransvectionBlocks J 𝓗) {g : MulAut W}
    {L L' : Subgroup (MulAut W)} (hL' : L' ∈ 𝓗) (hgL : B1.conjAut g L = L') {f f' : MulAut W}
    (hf : f ∈ L) (hf' : f' ∈ L') (h3 : orderOf f = 3) (h3' : orderOf f' = 3) :
    B1.conjAut g (Subgroup.zpowers f) = Subgroup.zpowers f' := by
  rw [conjAut_eq_map, MonoidHom.map_zpowers]
  have hmem : (MulAut.conj g).toMonoidHom f ∈ L' := by
    rw [← hgL, conjAut_eq_map]
    exact ⟨f, hf, rfl⟩
  have hord : orderOf ((MulAut.conj g).toMonoidHom f) = 3 := by
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, h3]
  exact zpowers_eq_of_card_six (hb.card_eq L' hL') hf' hmem h3' hord

theorem conjAut_eq_of_isSylowTwoOf {A P : Subgroup (MulAut W)} (hsyl : IsSylowTwoOf P A)
    {I : Finset (Subgroup (MulAut W))} {L₁ L₂ : Subgroup (MulAut W)} (h₁ : L₁ ∈ I)
    (hne : L₁ ≠ L₂) (hI : ∀ L ∈ I, L = L₁ ∨ L = L₂)
    (hperm : ∀ g ∈ A, ∀ L ∈ I, B1.conjAut g L ∈ I) (h₂ : L₂ ∈ I)
    (hP : ∀ t ∈ P, B1.conjAut t L₁ = L₁) : ∀ g ∈ A, B1.conjAut g L₁ = L₁ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g₀, hg₀, hg₀L⟩ := hcon
  have hg₀L₂ : B1.conjAut g₀ L₁ = L₂ := (hI _ (hperm g₀ hg₀ L₁ h₁)).resolve_left hg₀L
  have hswap : ∀ b ∈ A, B1.conjAut b L₁ ≠ L₁ → B1.conjAut b L₂ = L₁ := by
    intro b hb hb1
    have hb2 : B1.conjAut b L₁ = L₂ := (hI _ (hperm b hb L₁ h₁)).resolve_left hb1
    refine (hI _ (hperm b hb L₂ h₂)).resolve_right fun h => hne ?_
    exact conjAut_injective b (hb2.trans h.symm)
  set K : Subgroup A := (Subgroup.normalizer (L₁ : Set (MulAut W))).subgroupOf A with hK
  have hmemK : ∀ b : A, b ∈ K ↔ B1.conjAut (b : MulAut W) L₁ = L₁ := fun b => by
    rw [hK, Subgroup.mem_subgroupOf, mem_normalizer_iff_conjAut]
  have hK2 : K.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨g₀, hg₀⟩, fun b => ?_⟩
    rw [hmemK, hmemK]
    simp only [Subgroup.coe_mul]
    rw [conjAut_mul, hg₀L₂]
    by_cases hb : B1.conjAut (b : MulAut W) L₁ = L₁
    · refine Or.inr ⟨hb, fun h => hne ?_⟩
      exact conjAut_injective (b : MulAut W) (hb.trans h.symm)
    · exact Or.inl ⟨hswap b b.2 hb, hb⟩
  have hPK : P.subgroupOf A ≤ K := fun x hx => by
    rw [hmemK]
    exact hP x (Subgroup.mem_subgroupOf.mp hx)
  exact hsyl.2.2 (hK2 ▸ Subgroup.index_dvd_of_le hPK)

end BlockSystem

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple

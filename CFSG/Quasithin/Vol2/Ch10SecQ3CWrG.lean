module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrF
public import CFSG.Quasithin.EmptyFaithful.S153D51
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrC
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {P : Type} [Group P] [Finite P] {T₀ K₁ X₀ S : Subgroup P} {τ : P}

namespace WrCore

theorem le_normalizer_Y (c : WrCore T₀ K₁ X₀ S τ) :
    T₀ ≤ Subgroup.normalizer ((K₁ ⊔ cjSub τ K₁ : Subgroup P) : Set P) := by
  intro s hs
  have hle : ∀ r ∈ T₀, cjSub r K₁ ≤ K₁ ⊔ cjSub τ K₁ := fun r hr => by
    rcases c.orbit r hr with h | h <;> rw [h]
    · exact le_sup_left
    · exact le_sup_right
  have key : ∀ r ∈ T₀, cjSub r (K₁ ⊔ cjSub τ K₁) ≤ K₁ ⊔ cjSub τ K₁ := fun r hr => by
    rw [cjSub, Subgroup.map_sup]
    refine sup_le (hle r hr) ?_
    have := hle (r * τ) (T₀.mul_mem hr c.hτ)
    rwa [B2F.cjSub_mul] at this
  exact B2F.le_normalizer_of_cjSub_le (key s hs) (key s⁻¹ (T₀.inv_mem hs))

theorem normal_Y (c : WrCore T₀ K₁ X₀ S τ) : (K₁ ⊔ cjSub τ K₁ : Subgroup P).Normal := by
  refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
  rw [← c.hgen]
  exact sup_le (le_sup_left.trans Subgroup.le_normalizer) c.le_normalizer_Y

theorem two_quot (c : WrCore T₀ K₁ X₀ S τ) :
    ∀ x : P, ∃ k : ℕ, x ^ 2 ^ k ∈ (K₁ ⊔ cjSub τ K₁ : Subgroup P) := by
  intro x
  have := c.normal_Y
  refine B6.isTwoQuotient_of_sup_eq c.hT.2.1 (D := ⊤)
    (Subgroup.normalizer_eq_top_iff.mpr this).ge ?_ x (Subgroup.mem_top x)
  rw [eq_top_iff, ← c.hgen]
  exact sup_le (le_sup_left.trans le_sup_right) le_sup_left

theorem card_Y (c : WrCore T₀ K₁ X₀ S τ) : Nat.card (K₁ ⊔ cjSub τ K₁ : Subgroup P) = 3600 := by
  obtain ⟨e₁⟩ := c.hA5
  obtain ⟨e₂⟩ := nonempty_cjSub_equiv c.hA5 τ
  have h60 : ∀ (K : Subgroup P), (↥K ≃* AFive) → Nat.card K = 60 := fun K e => by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  rw [card_sup_of_commute c.commute₁₂ (inf_eq_bot_of_commute e₁ c.commute₁₂), h60 _ e₁,
    h60 _ e₂]

theorem center_Y (c : WrCore T₀ K₁ X₀ S τ) : ∀ y ∈ (K₁ ⊔ cjSub τ K₁ : Subgroup P),
    (∀ z ∈ (K₁ ⊔ cjSub τ K₁ : Subgroup P), y * z = z * y) → y = 1 := by
  intro y hy hz
  obtain ⟨e₁⟩ := c.hA5
  obtain ⟨e₂⟩ := nonempty_cjSub_equiv c.hA5 τ
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K₁ (cjSub τ K₁)
    c.commute₁₂).2
  have hy' : y ∈ ((K₁ : Set P) * (cjSub τ K₁ : Set P)) := by rw [← hset]; exact hy
  obtain ⟨k₁, hk₁, k₂, hk₂, hkk⟩ := hy'
  have hkk' : k₁ * k₂ = y := hkk
  subst hkk'
  have h1 : k₁ = 1 := eq_one_of_commute_of_equiv e₁ hk₁ fun a ha => by
    have := hz a (Subgroup.mem_sup_left ha)
    have hc := c.commute₁₂ a ha k₂ hk₂
    calc k₁ * a = k₁ * a * k₂ * k₂⁻¹ := by group
      _ = k₁ * (k₂ * a) * k₂⁻¹ := by rw [mul_assoc k₁, ← hc]
      _ = a * (k₁ * k₂) * k₂⁻¹ := by rw [← mul_assoc, this]
      _ = a * k₁ := by group
  subst h1
  rw [one_mul] at hz ⊢
  exact eq_one_of_commute_of_equiv e₂ hk₂ fun a ha => hz a (Subgroup.mem_sup_right ha)

theorem centralizer_Y (c : WrCore T₀ K₁ X₀ S τ) :
    Subgroup.centralizer ((K₁ ⊔ cjSub τ K₁ : Subgroup P) : Set P) = ⊥ := by
  have := c.normal_Y
  exact centralizer_eq_bot_of c.center_Y c.two_quot c.hO

theorem card_le_of_isPGroup_dvd {U : Subgroup P} (hU : IsPGroup 2 U) {n c : ℕ}
    (hdvd : Nat.card U ∣ n) (hn : ¬ 2 ^ (c + 1) ∣ n) : Nat.card U ≤ 2 ^ c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hU
  rw [hj] at hdvd ⊢
  refine Nat.pow_le_pow_right (by norm_num) ?_
  by_contra h
  exact hn ((Nat.pow_dvd_pow 2 (by omega)).trans hdvd)

omit [Finite P] in
theorem cjSub_one' (K : Subgroup P) : cjSub 1 K = K := by
  ext x
  simp [mem_cjSub]

theorem card_K₁ (c : WrCore T₀ K₁ X₀ S τ) (g : P) : Nat.card (cjSub g K₁) = 60 := by
  obtain ⟨e⟩ := nonempty_cjSub_equiv c.hA5 g
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem card_S (c : WrCore T₀ K₁ X₀ S τ) {g : P} (hg : g ∈ T₀) :
    IsSylowTwoOf (T₀ ⊓ cjSub g K₁) (cjSub g K₁) ∧ Nat.card (T₀ ⊓ cjSub g K₁ : Subgroup P) = 4 := by
  have h := S153D.isSylowTwoOf_inf_of_isSubnormal (c.hsub g hg) c.hT
  exact ⟨h, card_eq_four_of_isSylowTwoOf h (c.card_K₁ g)⟩

theorem inf_Y_eq (c : WrCore T₀ K₁ X₀ S τ) :
    T₀ ⊓ (K₁ ⊔ cjSub τ K₁) = (T₀ ⊓ K₁) ⊔ (T₀ ⊓ cjSub τ K₁) := by
  obtain ⟨e₁⟩ := c.hA5
  have hc : ∀ x ∈ T₀ ⊓ K₁, ∀ y ∈ T₀ ⊓ cjSub τ K₁, x * y = y * x := fun x hx y hy =>
    c.commute₁₂ x hx.2 y hy.2
  have hinf : (T₀ ⊓ K₁) ⊓ (T₀ ⊓ cjSub τ K₁) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf inf_le_right inf_le_right).trans
      (inf_eq_bot_of_commute e₁ c.commute₁₂).le)
  have h1 := (c.card_S (g := 1) T₀.one_mem).2
  rw [cjSub_one'] at h1
  have h16 : Nat.card ((T₀ ⊓ K₁) ⊔ (T₀ ⊓ cjSub τ K₁) : Subgroup P) = 16 := by
    rw [card_sup_of_commute hc hinf, h1, (c.card_S c.hτ).2]
  symm
  refine Subgroup.eq_of_le_of_card_ge (sup_le (inf_le_inf_left _ le_sup_left)
    (inf_le_inf_left _ le_sup_right)) ?_
  rw [h16]
  refine card_le_of_isPGroup_dvd (n := 3600) (c := 4) (c.hT.2.1.to_le inf_le_left) ?_
    (by norm_num)
  rw [← c.card_Y]
  exact Subgroup.card_dvd_of_le inf_le_right

theorem S_eq (c : WrCore T₀ K₁ X₀ S τ) : S = T₀ ⊓ K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (c.card_S (g := 1) T₀.one_mem).2
  rw [cjSub_one'] at h1
  have hS4 : Nat.card S = 4 := card_eq_four_of_isSylowTwoOf c.hS (by
    simpa [cjSub_one'] using c.card_K₁ 1)
  have hN : T₀ ⊓ K₁ ≤ Subgroup.normalizer (S : Set P) := c.hTK.trans inf_le_right
  have h2 : IsPGroup 2 ↥((T₀ ⊓ K₁) ⊔ S) :=
    (c.hT.2.1.to_le inf_le_left).to_sup_of_normal_right' c.hS.2.1 hN
  have h3 : (T₀ ⊓ K₁) ⊔ S ≤ K₁ := sup_le inf_le_right c.hS.1
  have h4 : Nat.card ((T₀ ⊓ K₁) ⊔ S : Subgroup P) ≤ 4 := by
    refine card_le_of_isPGroup_dvd (n := 60) (c := 2) h2 ?_ (by norm_num)
    rw [← (show Nat.card K₁ = 60 by simpa [cjSub_one'] using c.card_K₁ 1)]
    exact Subgroup.card_dvd_of_le h3
  have h5 : (T₀ ⊓ K₁) ⊔ S = S :=
    (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hS4]; exact h4)).symm
  exact (Subgroup.eq_of_le_of_card_ge (h5 ▸ le_sup_left : T₀ ⊓ K₁ ≤ S)
    (by rw [hS4, h1])).symm

omit [Finite P] in
theorem mem_normalizer_sup {A B : Subgroup P} {g : P}
    (hA : g ∈ Subgroup.normalizer (A : Set P)) (hB : g ∈ Subgroup.normalizer (B : Set P)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup P) : Set P) := by
  rw [B2F.mem_normalizer_iff_cjSub_eq] at hA hB ⊢
  rw [cjSub, Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) hA hB

omit [Finite P] in
theorem mem_normalizer_of_commute {B : Subgroup P} {g : P} (hg : ∀ b ∈ B, g * b = b * g) :
    g ∈ Subgroup.normalizer (B : Set P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [hg b hb, mul_inv_cancel_right]
    exact hb
  · intro hb
    have h := hg _ hb
    have h2 : g * (g * b * g⁻¹) = g * b := by rw [h]; group
    have h3 : g * b * g⁻¹ = b := mul_left_cancel h2
    exact h3 ▸ hb

theorem cjSub_S₁ (c : WrCore T₀ K₁ X₀ S τ) : cjSub τ (T₀ ⊓ K₁) = T₀ ⊓ cjSub τ K₁ := by
  rw [B2F.cjSub_inf, B2F.cjSub_eq_of_mem_normalizer (Subgroup.le_normalizer c.hτ)]

theorem le_normalizer_R (c : WrCore T₀ K₁ X₀ S τ) :
    X₀ ≤ Subgroup.normalizer ((T₀ ⊓ (K₁ ⊔ cjSub τ K₁) : Subgroup P) : Set P) := by
  have hSe := c.S_eq
  refine c.hX₀.trans (sup_le (sup_le ?_ ?_) ?_)
  · intro m hm
    rw [c.inf_Y_eq]
    refine mem_normalizer_sup (hSe ▸ hm.2) (mem_normalizer_of_commute fun b hb => ?_)
    exact c.commute₁₂ m hm.1 b hb.2
  · intro m hm
    rw [c.inf_Y_eq]
    have hm' := mem_cjSub.mp hm
    have hmK : m ∈ cjSub τ K₁ := by
      rw [mem_cjSub]
      exact hm'.1
    refine mem_normalizer_sup (mem_normalizer_of_commute fun b hb => ?_) ?_
    · exact (c.commute₁₂ b hb.2 m hmK).symm
    · have hx : cjSub (τ⁻¹ * m * τ) (T₀ ⊓ K₁) = T₀ ⊓ K₁ :=
        B2F.cjSub_eq_of_mem_normalizer (hSe ▸ hm'.2)
      rw [B2F.mem_normalizer_iff_cjSub_eq, ← c.cjSub_S₁, ← B2F.cjSub_mul,
        show m * τ = τ * (τ⁻¹ * m * τ) by group, B2F.cjSub_mul τ (τ⁻¹ * m * τ), hx]
  · intro t ht
    rw [B2F.mem_normalizer_iff_cjSub_eq, B2F.cjSub_inf,
      B2F.cjSub_eq_of_mem_normalizer (Subgroup.le_normalizer ht),
      B2F.cjSub_eq_of_mem_normalizer (c.le_normalizer_Y ht)]

theorem nonempty_equiv (c : WrCore T₀ K₁ X₀ S τ) (h8 : 8 ≤ (K₁ ⊔ cjSub τ K₁).index) :
    Nonempty (P ≃* SymFiveWrTwo) := by
  obtain ⟨e₁⟩ := c.hA5
  obtain ⟨e₂⟩ := nonempty_cjSub_equiv c.hA5 τ
  have := c.normal_Y
  refine nonempty_mulEquiv_symFiveWrTwo e₁ e₂ c.commute₁₂
    (inf_eq_bot_of_commute e₁ c.commute₁₂) c.centralizer_Y ?_
  rw [← (K₁ ⊔ cjSub τ K₁).card_mul_index, c.card_Y]
  omega

end WrCore

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB

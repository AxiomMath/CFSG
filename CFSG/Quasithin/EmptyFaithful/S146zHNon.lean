module

public import CFSG.Quasithin.EmptyFaithful.S146zHTrans
public import CFSG.Quasithin.EmptyFaithful.S146zHFaith
public import CFSG.Quasithin.EmptyFaithful.S146D5
public import CFSG.Quasithin.EmptyFaithful.S146F10
public import CFSG.Quasithin.EmptyFaithful.S146F13
public import CFSG.Quasithin.EmptyFaithful.S146F15
public import CFSG.Quasithin.EmptyFaithful.S146F16
public import CFSG.Quasithin.EmptyFaithful.S146F17
public import CFSG.Quasithin.EmptyFaithful.S146F20
public import CFSG.Quasithin.EmptyFaithful.S146zHDih

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Non

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.exists_decomp (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {k : G} (hk : k ∈ uK T M H) :
    ∃ a ∈ uHi T M H H₁, ∃ b ∈ uHi T M H H₂, k = a * b := by
  have hH : IsHTM T M H := hred.isHTM
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  have hN12 : uHi T M H H₁ ≤ Subgroup.normalizer (uHi T M H H₂ : Set G) :=
    le_normalizer_of_forall_commute fun x hx y hy => isElemAbelian_comm hUab (hi₁ hx) (hi₂ hy)
  have hmul : (↑(uHi T M H H₁ ⊔ uHi T M H H₂) : Set G) = ↑(uHi T M H H₁) * ↑(uHi T M H H₂) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN12
  have hk' : k ∈ (↑(uHi T M H H₁ ⊔ uHi T M H H₂) : Set G) := by
    have : k ∈ uHi T M H H₁ ⊔ uHi T M H H₂ := by
      rw [h.dir_sup]
      exact Subgroup.mem_sup_left hk
    exact this
  rw [hmul] at hk'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hk'
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem IsDecP.exists_nontrivial (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {g : G} (tv : TvData T M H g) :
    (∃ x ∈ conjSub g⁻¹ (conjClosure (VZ T M) H), ∃ u ∈ uHi T M H H₁,
        x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T) ∨
      (∃ x ∈ conjSub g⁻¹ (conjClosure (VZ T M) H), ∃ u ∈ uHi T M H H₂,
        x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T) := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  obtain ⟨x, hx, u, hu, hxu⟩ : ∃ x ∈ conjSub g⁻¹ (conjClosure (VZ T M) H), ∃ u ∈ conjClosure (VZ T M) H,
      x * u * x⁻¹ * u⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : ⁅conjSub g⁻¹ (conjClosure (VZ T M) H), conjClosure (VZ T M) H⁆ ≤ ⊥ :=
      Subgroup.commutator_le.mpr fun x hx u hu => by
        rw [Subgroup.mem_bot, commutatorElement_def]
        exact hall x hx u hu
    rw [tv.comm] at h1
    have h2 : Nat.card (conjSub g⁻¹ (quasithinOmegaOneCenter T)) = 1 := by
      rw [le_bot_iff.mp h1]
      exact Subgroup.card_bot
    rw [tv.card] at h2
    omega
  have hxH : x ∈ H := tv.le_H hx
  have hcZg : x * u * x⁻¹ * u⁻¹ ∈ conjSub g⁻¹ (quasithinOmegaOneCenter T) := by
    rw [← tv.comm]
    exact Subgroup.commutator_mem_commutator hx hu
  have hcZ : x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T := by
    intro hc
    have : x * u * x⁻¹ * u⁻¹ ∈ conjSub g⁻¹ (quasithinOmegaOneCenter T) ⊓ quasithinOmegaOneCenter T :=
      ⟨hcZg, hc⟩
    rw [tv.inf, Subgroup.mem_bot] at this
    exact hxu this
  have h4 : centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) = pCoreOf 2 H :=
    S.lemma_14_5_15_four hH
  have hxQ : x ∉ pCoreOf 2 H := by
    intro hQ
    rw [← h4] at hQ
    exact hcZ (hQ.2.2 u hu)
  rw [← S.centralizerMod_uK_eq hH] at hxQ
  obtain ⟨k, hk, hkZ⟩ : ∃ k ∈ uK T M H, x * k * x⁻¹ * k⁻¹ ∉ quasithinOmegaOneCenter T := by
    by_contra hall
    push Not at hall
    exact hxQ ⟨hxH, hHN hxH, hall⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_decomp S hred hk
  have haN := hUZ (hi₁ ha)
  by_cases hxa : x * a * x⁻¹ * a⁻¹ ∈ quasithinOmegaOneCenter T
  · right
    refine ⟨x, hx, b, hb, fun hxb => hkZ ?_⟩
    have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    refine (quasithinOmegaOneCenter T).mul_mem hxa ?_
    have := (Subgroup.mem_normalizer_iff.mp haN (x * b * x⁻¹ * b⁻¹)).mp hxb
    simpa using this
  · left
    exact ⟨x, hx, a, ha, hxa⟩

theorem IsDecP.normalizer_or_swap (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {x : G} (hx : x ∈ H) :
    (x ∈ Subgroup.normalizer (H₁ : Set G) ∧ conjSub x (uHi T M H H₁) = uHi T M H H₁ ∧
        conjSub x (uHi T M H H₂) = uHi T M H H₂) ∨
      (conjSub x (uHi T M H H₁) = uHi T M H H₂ ∧ conjSub x (uHi T M H H₂) = uHi T M H H₁) := by
  have hTH : T ≤ H := hred.isHTM.1.1
  have hTN : T ≤ Subgroup.normalizer (H₀ : Set G) := hTH.trans h.normal
  have hmul : (↑(H₀ ⊔ T) : Set G) = ↑H₀ * ↑T :=
    Subgroup.coe_mul_of_right_le_normalizer_left H₀ T hTN
  have hx' : x ∈ (↑(H₀ ⊔ T) : Set G) := by rw [← h.eq]; exact hx
  rw [hmul] at hx'
  obtain ⟨y, hy, τ, hτ, rfl⟩ := hx'
  have h₁ := conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred hy)
  have h₂ := conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₂ S hred hy)
  by_cases hτN : τ ∈ Subgroup.normalizer (H₁ : Set G)
  · left
    have hτ₁ : τ ∈ Subgroup.normalizer (uHi T M H H₁ : Set G) :=
      inf_normalizer_le_normalizer_uHi hTH H₁ ⟨hτ, hτN⟩
    have hτ₂ : τ ∈ Subgroup.normalizer (uHi T M H H₂ : Set G) := by
      have : τ ∈ T ⊓ Subgroup.normalizer (H₂ : Set G) := by
        rw [h.inf_normalizer_swap_eq]; exact ⟨hτ, hτN⟩
      exact inf_normalizer_le_normalizer_uHi hTH H₂ this
    refine ⟨(Subgroup.normalizer (H₁ : Set G)).mul_mem (h.H₀_le_normalizer_H₁ hy) hτN, ?_, ?_⟩
    · rw [conjSub_mul, conjSub_eq_of_mem_normalizer hτ₁, h₁]
    · rw [conjSub_mul, conjSub_eq_of_mem_normalizer hτ₂, h₂]
  · right
    have hτN₂ : τ ∉ Subgroup.normalizer (H₂ : Set G) := by
      intro hh
      have : τ ∈ T ⊓ Subgroup.normalizer (H₁ : Set G) := by
        rw [← h.inf_normalizer_swap_eq]; exact ⟨hτ, hh⟩
      exact hτN this.2
    refine ⟨?_, ?_⟩
    · rw [conjSub_mul, h.conjSub_uHi_of_not_mem hred hτ hτN, h₂]
    · rw [conjSub_mul, h.swap.conjSub_uHi_of_not_mem hred hτ hτN₂, h₁]

end Non

end CFSG.Quasithin

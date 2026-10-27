module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrBase
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

namespace X1512

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_of_forall {E A : Subgroup G}
    (h : ∀ e ∈ E, ∀ x ∈ A, e * x * e⁻¹ ∈ A) {y : G} (hy : y ∈ E ⊔ A) :
    ∃ e ∈ E, ∃ x ∈ A, y = e * x := by
  have h1 : ((E ⊔ A : Subgroup G) : Set G) = (E : Set G) * (A : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right E A (le_normalizer_of_forall h)
  have h2 : y ∈ (E : Set G) * (A : Set G) := h1 ▸ hy
  obtain ⟨e, he, x, hx, rfl⟩ := Set.mem_mul.mp h2
  exact ⟨e, he, x, hx, rfl⟩

namespace WrStep

variable {H U L N K F₁ F₂ X₁ X₂ : Subgroup G} (P : WrStep H U L N K F₁ F₂ X₁ X₂)

include P

theorem mul_inv_mem_K {a b : G} (ha : a ∈ H) (hb : b ∈ H) (haK : a ∉ K) (hbK : b ∉ K) :
    a * b⁻¹ ∈ K := by
  obtain ⟨c, hcH, hcK, hc⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp P.K_idx
  have h1 : a * c ∈ K := (hc a ha).resolve_right haK
  have h2 : b * c ∈ K := (hc b hb).resolve_right hbK
  have h3 := K.mul_mem h1 (K.inv_mem h2)
  have e : a * c * (b * c)⁻¹ = a * b⁻¹ := by group
  rwa [e] at h3

theorem mem_K_or_mul_mem {t : G} (ht : t ∈ H) (htK : t ∉ K) :
    ∀ h ∈ H, h ∈ K ∨ h * t⁻¹ ∈ K := fun h hh => by
  by_cases hhK : h ∈ K
  · exact Or.inl hhK
  · exact Or.inr (P.mul_inv_mem_K hh ht hhK htK)

theorem exists_mul_of_mem_N {y : G} (hy : y ∈ N) : ∃ u₁ ∈ X₁, ∃ u₂ ∈ X₂, y = u₁ * u₂ :=
  exists_mul_of_mem_sup_of_forall (fun k hk m hm => by
    rw [P.N_abelian k (P.X₁_le hk) m (P.X₂_le hm), mul_inv_cancel_right]
    exact hm) (by rw [P.sup_eq]; exact hy)

theorem stab {σ : G} (hσH : σ ∈ H) (hσ : ∀ x ∈ X₁, σ * x * σ⁻¹ ∈ X₁) : σ ∈ K := by
  by_contra hσK
  have hall : ∀ h ∈ H, ∀ x ∈ X₁, h * x * h⁻¹ ∈ X₁ := by
    intro h hh x hx
    by_cases hhK : h ∈ K
    · exact P.K_norm₁ h hhK x hx
    · have e : h * x * h⁻¹ = (h * σ⁻¹) * (σ * x * σ⁻¹) * (h * σ⁻¹)⁻¹ := by group
      rw [e]
      exact P.K_norm₁ _ (P.mul_inv_mem_K hh hσH hhK hσK) _ (hσ x hx)
  have hIN : IsNormalIn H U X₁ := ⟨P.X₁_le.trans P.step.1.1, hall⟩
  rcases P.step.2.2.2 X₁ hIN P.L_le₁ P.X₁_le with h | h
  · exact P.L_ne₁ h.symm
  · have h2 : X₂ ≤ X₁ := h ▸ P.X₂_le
    have h5 := P.inf_eq
    rw [inf_eq_right.mpr h2] at h5
    exact P.L_ne₂ h5.symm

theorem false_of_inf_eq [Finite G] {Y : Subgroup G} (hLY : L ≤ Y) (hYN : Y ≤ N)
    (hYK : ∀ b ∈ K, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) (hcardY : Nat.card Y = Nat.card X₁)
    (hA₁ : Y ⊓ X₁ = L) (hA₂ : Y ⊓ X₂ = L) : False := by
  have hYX₁comm : ∀ k ∈ Y, ∀ m ∈ X₁, k * m * k⁻¹ ∈ X₁ := fun k hk m hm => by
    rw [P.N_abelian k (hYN hk) m (P.X₁_le hm), mul_inv_cancel_right]
    exact hm
  have hZ : ∀ f ∈ F₂, ∀ z ∈ Y ⊔ X₁, f * z * f⁻¹ ∈ Y ⊔ X₁ := by
    intro f hf z hz
    obtain ⟨y, hy, x, hx, rfl⟩ := exists_mul_of_mem_sup_of_forall hYX₁comm hz
    have e : f * (y * x) * f⁻¹ = (f * y * f⁻¹) * (f * x * f⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hYK f (P.F₂_le_K hf) y hy))
      (Subgroup.mem_sup_right (P.F₂_norm₁ f hf x hx))
  have hA₃ : (Y ⊔ X₁) ⊓ X₂ = L ∨ (Y ⊔ X₁) ⊓ X₂ = X₂ := by
    refine P.irr₂ ((Y ⊔ X₁) ⊓ X₂) (le_inf (hLY.trans le_sup_left) P.L_le₂) inf_le_right ?_
    intro f hf w hw
    exact ⟨hZ f hf w hw.1, P.F₂_norm f hf w hw.2⟩
  have hX₂Z : X₂ ≤ Y ⊔ X₁ := by
    rcases hA₃ with hA₃ | hA₃
    · exfalso
      have hYX₁ : Y ≤ X₁ := by
        intro y hy
        obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := P.exists_mul_of_mem_N (hYN hy)
        have hu₂Z : u₂ ∈ (Y ⊔ X₁) ⊓ X₂ := by
          refine ⟨?_, hu₂⟩
          have h3 := Subgroup.mul_mem _ (Subgroup.mem_sup_right (X₁.inv_mem hu₁))
            (Subgroup.mem_sup_left hy : u₁ * u₂ ∈ Y ⊔ X₁)
          simpa using h3
        rw [hA₃] at hu₂Z
        exact X₁.mul_mem hu₁ (P.L_le₁ hu₂Z)
      have hYL : Y = L := by
        rw [← hA₁]
        exact (inf_eq_left.mpr hYX₁).symm
      rw [hYL] at hcardY
      exact P.L_ne₁ (Subgroup.eq_of_le_of_card_ge P.L_le₁ hcardY.symm.le)
    · intro x hx
      have h3 : x ∈ (Y ⊔ X₁) ⊓ X₂ := by rw [hA₃]; exact hx
      exact h3.1
  have htriv : ∀ f ∈ F₂, ∀ x ∈ X₂, f * x * f⁻¹ * x⁻¹ ∈ L := by
    intro f hf x hx
    obtain ⟨y, hy, x₁, hx₁, rfl⟩ := exists_mul_of_mem_sup_of_forall hYX₁comm (hX₂Z hx)
    have hfH : f ∈ H := P.F₂_le hf
    rw [P.conj_comm_mul hfH (hYN hy) (P.X₁_le hx₁)]
    refine L.mul_mem ?_ (P.F₂_triv f hf x₁ hx₁)
    have hfy : f * y * f⁻¹ * y⁻¹ ∈ Y ⊓ X₂ := by
      refine ⟨Y.mul_mem (hYK f (P.F₂_le_K hf) y hy) (Y.inv_mem hy), ?_⟩
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := P.exists_mul_of_mem_N (hYN hy)
      rw [P.conj_comm_mul hfH (P.X₁_le hu₁) (P.X₂_le hu₂)]
      exact X₂.mul_mem (P.L_le₂ (P.F₂_triv f hf u₁ hu₁))
        (X₂.mul_mem (P.F₂_norm f hf u₂ hu₂) (X₂.inv_mem hu₂))
    rw [hA₂] at hfy
    exact hfy
  obtain ⟨f, hf, x, hx, hnot⟩ := P.nontriv₂
  exact hnot (htriv f hf x hx)

theorem eq_or_eq_of_card [Finite G] {Y : Subgroup G} (hLY : L ≤ Y) (hYN : Y ≤ N)
    (hYK : ∀ b ∈ K, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) (hcardY : Nat.card Y = Nat.card X₁) :
    Y = X₁ ∨ Y = X₂ := by
  have hA₁ : Y ⊓ X₁ = L ∨ Y ⊓ X₁ = X₁ := by
    refine P.irr₁ (Y ⊓ X₁) (le_inf hLY P.L_le₁) inf_le_right ?_
    intro f hf y hy
    exact ⟨hYK f (P.F₁_le_K hf) y hy.1, P.F₁_norm f hf y hy.2⟩
  have hA₂ : Y ⊓ X₂ = L ∨ Y ⊓ X₂ = X₂ := by
    refine P.irr₂ (Y ⊓ X₂) (le_inf hLY P.L_le₂) inf_le_right ?_
    intro f hf y hy
    exact ⟨hYK f (P.F₂_le_K hf) y hy.1, P.F₂_norm f hf y hy.2⟩
  rcases hA₁ with hA₁ | hA₁
  · rcases hA₂ with hA₂ | hA₂
    · exact (P.false_of_inf_eq hLY hYN hYK hcardY hA₁ hA₂).elim
    · right
      have hle : X₂ ≤ Y := fun x hx => by
        have h3 : x ∈ Y ⊓ X₂ := by rw [hA₂]; exact hx
        exact h3.1
      have hcard : Nat.card Y ≤ Nat.card X₂ := by rw [hcardY, P.card_eq]
      exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  · left
    have hle : X₁ ≤ Y := fun x hx => by
      have h3 : x ∈ Y ⊓ X₁ := by rw [hA₁]; exact hx
      exact h3.1
    exact (Subgroup.eq_of_le_of_card_ge hle hcardY.le).symm

theorem conj_dichotomy [Finite G] {t : G} (ht : t ∈ H) :
    conjSub t X₁ = X₁ ∨ conjSub t X₁ = X₂ := by
  have hLY : L ≤ conjSub t X₁ := fun l hl => mem_conjSub.mpr (P.L_le₁ (by
    simpa using P.H_norm_L t⁻¹ (H.inv_mem ht) l hl))
  have hYN : conjSub t X₁ ≤ N := fun y hy => by
    have h1 : t⁻¹ * y * t ∈ X₁ := mem_conjSub.mp hy
    have h2 := P.H_norm_N t ht _ (P.X₁_le h1)
    have e : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
    rwa [e] at h2
  have hYK : ∀ b ∈ K, ∀ y ∈ conjSub t X₁, b * y * b⁻¹ ∈ conjSub t X₁ := by
    intro b hb y hy
    refine mem_conjSub.mpr ?_
    have hb' : t⁻¹ * b * t ∈ K := by simpa using P.K_normal t⁻¹ (H.inv_mem ht) b hb
    have h1 := P.K_norm₁ _ hb' _ (mem_conjSub.mp hy)
    have e : t⁻¹ * (b * y * b⁻¹) * t = (t⁻¹ * b * t) * (t⁻¹ * y * t) * (t⁻¹ * b * t)⁻¹ := by group
    rw [e]
    exact h1
  have hcardY : Nat.card (conjSub t X₁) = Nat.card X₁ :=
    Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj t))
  exact P.eq_or_eq_of_card hLY hYN hYK hcardY

theorem conjSub_eq_of_not_mem [Finite G] {t : G} (ht : t ∈ H) (htK : t ∉ K) :
    conjSub t X₁ = X₂ := by
  rcases P.conj_dichotomy ht with h | h
  · exfalso
    exact htK (P.stab ht fun x hx => by
      have h3 := mul_mem_conjSub (g := t) hx
      rwa [h] at h3)
  · exact h

theorem conjSub_eq_of_not_mem' [Finite G] {t : G} (ht : t ∈ H) (htK : t ∉ K) :
    conjSub t X₂ = X₁ :=
  P.symm.conjSub_eq_of_not_mem ht htK

theorem conj_centralizes [Finite G] {t k : G} (ht : t ∈ H) (htK : t ∉ K) (_hk : k ∈ K)
    (hk2 : ∀ x ∈ X₂, k * x * k⁻¹ * x⁻¹ ∈ L) :
    ∀ x ∈ X₁, (t * k * t⁻¹) * x * (t * k * t⁻¹)⁻¹ * x⁻¹ ∈ L := by
  intro x hx
  have hx' : x ∈ conjSub t X₂ := by rw [P.conjSub_eq_of_not_mem' ht htK]; exact hx
  have h3 := P.H_norm_L t ht _ (hk2 _ (mem_conjSub.mp hx'))
  have e : t * (k * (t⁻¹ * x * t) * k⁻¹ * (t⁻¹ * x * t)⁻¹) * t⁻¹ =
      (t * k * t⁻¹) * x * (t * k * t⁻¹)⁻¹ * x⁻¹ := by group
  rwa [e] at h3

theorem conj_centralizes' [Finite G] {t k : G} (ht : t ∈ H) (htK : t ∉ K) (_hk : k ∈ K)
    (hk1 : ∀ x ∈ X₁, k * x * k⁻¹ * x⁻¹ ∈ L) :
    ∀ x ∈ X₂, (t * k * t⁻¹) * x * (t * k * t⁻¹)⁻¹ * x⁻¹ ∈ L :=
  P.symm.conj_centralizes ht htK _hk hk1

end WrStep

end X1512

end CFSG.Quasithin

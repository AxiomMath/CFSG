module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrDefs

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32

variable {Γ : Type*} [Group Γ]

theorem mul_comm_of_inf_eq_bot {S K : Subgroup Γ} (hS : S ≤ Subgroup.normalizer (K : Set Γ))
    (hK : K ≤ Subgroup.normalizer (S : Set Γ)) (h : S ⊓ K = ⊥) {s k : Γ} (hs : s ∈ S)
    (hk : k ∈ K) : s * k = k * s := by
  have h1 : s * k * s⁻¹ * k⁻¹ ∈ S ⊓ K := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h2 := (Subgroup.mem_normalizer_iff.mp (hK hk) s⁻¹).mp (inv_mem hs)
      have h3 := mul_mem hs h2
      simpa [mul_assoc] using h3
    · have h2 := (Subgroup.mem_normalizer_iff.mp (hS hs) k).mp hk
      exact mul_mem h2 (inv_mem hk)
  rw [h, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem le_centralizer_of_inf_eq_bot {S K : Subgroup Γ} (hS : S ≤ Subgroup.normalizer (K : Set Γ))
    (hK : K ≤ Subgroup.normalizer (S : Set Γ)) (h : S ⊓ K = ⊥) :
    S ≤ Subgroup.centralizer (K : Set Γ) := fun _ hs =>
  Subgroup.mem_centralizer_iff.mpr fun _ hk => (mul_comm_of_inf_eq_bot hS hK h hs hk).symm

theorem le_normalizer_inf {Q H K : Subgroup Γ} (hH : Q ≤ Subgroup.normalizer (H : Set Γ))
    (hK : Q ≤ Subgroup.normalizer (K : Set Γ)) :
    Q ≤ Subgroup.normalizer ((H ⊓ K : Subgroup Γ) : Set Γ) :=
  (le_inf hH hK).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem le_normalizer_sup {Q H K : Subgroup Γ} (hH : Q ≤ Subgroup.normalizer (H : Set Γ))
    (hK : Q ≤ Subgroup.normalizer (K : Set Γ)) :
    Q ≤ Subgroup.normalizer ((H ⊔ K : Subgroup Γ) : Set Γ) :=
  (le_inf hH hK).trans (Subgroup.inf_normalizer_le_normalizer_sup H K)

theorem le_normalizer_centralizer {Q H : Subgroup Γ} (h : Q ≤ Subgroup.normalizer (H : Set Γ)) :
    Q ≤ Subgroup.normalizer ((Subgroup.centralizer (H : Set Γ) : Subgroup Γ) : Set Γ) :=
  h.trans (Thm211.normalizer_le_normalizer_centralizer H)

theorem mem_sup_iff_mul {H K : Subgroup Γ} (hK : K ≤ Subgroup.normalizer (H : Set Γ)) {g : Γ} :
    g ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left H K hK
  constructor
  · intro hg
    have hg' : g ∈ ((H ⊔ K : Subgroup Γ) : Set Γ) := hg
    rw [hset] at hg'
    obtain ⟨h, hh, k, hk, rfl⟩ := hg'
    exact ⟨h, hh, k, hk, rfl⟩
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup hh hk

theorem mem_sup_iff_mul' {H K : Subgroup Γ} (hH : H ≤ Subgroup.normalizer (K : Set Γ)) {g : Γ} :
    g ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right H K hH
  constructor
  · intro hg
    have hg' : g ∈ ((H ⊔ K : Subgroup Γ) : Set Γ) := hg
    rw [hset] at hg'
    obtain ⟨h, hh, k, hk, rfl⟩ := hg'
    exact ⟨h, hh, k, hk, rfl⟩
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup hh hk

theorem le_of_le_sup_of_inf_le {L Z R : Subgroup Γ} (hLZ : L ≤ Z)
    (hLR : L ≤ Subgroup.normalizer (R : Set Γ)) (hZR : Z ⊓ R ≤ L) (hZ : Z ≤ L ⊔ R) : Z ≤ L := by
  intro z hz
  obtain ⟨l, hl, r, hr, rfl⟩ := (mem_sup_iff_mul' hLR).mp (hZ hz)
  have hrZ : r ∈ Z ⊓ R := ⟨by
    have := mul_mem (inv_mem (hLZ hl)) hz
    simpa using this, hr⟩
  exact mul_mem hl (hZR hrZ)

theorem not_isSolvable_of_chief_bot {H K : Subgroup Γ} (hK : IsChiefFactorOf H K ⊥)
    (hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) : ¬ Group.IsSolvable ↥K := by
  intro hs
  have hK0 : K ≠ ⊥ := hK.2.2.1.ne'
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK0
  have hlt : ⁅K, K⁆ < K := CFSG.commutator_lt_self_of_isSolvable K
  have hle1 : (⁅K, K⁆ : Subgroup Γ) ≤ K := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.map_subtype_le _
  have hnor : H ≤ Subgroup.normalizer ((⁅K, K⁆ : Subgroup Γ) : Set Γ) := by
    have h1 := Thm211.normalizer_le_normalizer_map_subtype (commutator ↥K)
    rw [Subgroup.map_subtype_commutator] at h1
    exact hK.2.1.2.trans h1
  rcases hK.2.2.2 ⁅K, K⁆ ⟨hle1.trans hK.2.1.1, hnor⟩ bot_le hle1 with h | h
  · obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    apply hxy
    have h1 : ⁅x, y⁆ ∈ (⁅K, K⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · exact hlt.ne h

section Pairs

variable {A X Y X₁ X₂ : Subgroup Γ}

theorem isDAIn_left_of_mem_iPairsY (hP : (X₁, X₂) ∈ iPairsY A X Y) : IsDAIn A X X₁ := hP.1.1

theorem isDAIn_right_of_mem_iPairsY (hP : (X₁, X₂) ∈ iPairsY A X Y) : IsDAIn A X X₂ := hP.1.2.1

theorem chief_of_mem_iPairsY (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    IsChiefFactorOf (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) X₁ X₂ := hP.1.2.2.1

theorem secCen_of_mem_iPairsY (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    secCenIn (X₁ ⊔ cenIn X (A : Set Γ)) X₁ X₂ = X₂ := hP.1.2.2.2

theorem inf_eq_of_mem_iPairsY (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    X₂ ⊓ cenIn X (A : Set Γ) = Y := hP.2

theorem le_of_mem_iPairsY (hP : (X₁, X₂) ∈ iPairsY A X Y) : X₂ ≤ X₁ :=
  (chief_of_mem_iPairsY hP).2.2.1.le

theorem mem_iPairsY_of {Z₁ Z₂ : Subgroup Γ} (h1 : IsDAIn A X Z₁) (h2 : IsDAIn A X Z₂)
    (h3 : IsChiefFactorOf (Z₁ ⊔ cenIn X (A : Set Γ) ⊔ A) Z₁ Z₂)
    (h4 : secCenIn (Z₁ ⊔ cenIn X (A : Set Γ)) Z₁ Z₂ = Z₂) (h5 : Z₂ ⊓ cenIn X (A : Set Γ) = Y) :
    (Z₁, Z₂) ∈ iPairsY A X Y :=
  ⟨⟨h1, h2, h3, h4⟩, h5⟩

end Pairs

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32

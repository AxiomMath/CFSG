module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsLoc
public import CFSG.Quasithin.Background.F1AmalgamRestrict
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsAm

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F1

structure TransFacts {P : Type} [Group P] (N₁ N₂ : Subgroup P) : Prop where
  solv : Group.IsSolvable ↥(N₁ ⊓ N₂)
  trans₁ : ∀ a ∈ centerOf (perfectCore N₁), ∀ a' ∈ centerOf (perfectCore N₁), a ≠ 1 → a' ≠ 1 →
    ∃ m ∈ N₁, m * a * m⁻¹ = a'
  trans₂ : ∀ a ∈ centerOf (perfectCore N₂), ∀ a' ∈ centerOf (perfectCore N₂), a ≠ 1 → a' ≠ 1 →
    ∃ m ∈ N₂, m * a * m⁻¹ = a'

structure SplitFacts {P : Type} [Group P] (N₁ N₂ : Subgroup P) : Prop where
  le₁ : centerOf (perfectCore N₁) ≤ pCoreOf 2 (N₁ ⊓ N₂)
  le₂ : centerOf (perfectCore N₂) ≤ pCoreOf 2 (N₁ ⊓ N₂)
  ne₁ : ∃ x ∈ centerOf (perfectCore N₁), x ≠ 1
  ne₂ : ∃ x ∈ centerOf (perfectCore N₂), x ≠ 1
  inf : ∀ x ∈ centerOf (perfectCore N₁), x ∈ centerOf (perfectCore N₂) → x = 1
  third : ∀ a ∈ centerOf (pCoreOf 2 (N₁ ⊓ N₂)), ∀ a' ∈ centerOf (pCoreOf 2 (N₁ ⊓ N₂)),
    a ∉ centerOf (perfectCore N₁) → a ∉ centerOf (perfectCore N₂) →
    a' ∉ centerOf (perfectCore N₁) → a' ∉ centerOf (perfectCore N₂) →
    ∃ m ∈ N₁ ⊓ N₂, m * a * m⁻¹ = a'

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}
  {P : Type} [Group P] [Finite P] {N₁ N₂ : Subgroup P}
  (Φ : (RankTwoAmalgam.ofSubgroups (fG1 M L H B) (fG2 M L H D)).Iso
    (RankTwoAmalgam.ofSubgroups N₁ N₂))

theorem sec53S_le_K (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    sec53S T L ≤ oTwoUpper H := by
  obtain ⟨-, ⟨-, -, -, hST, hSK, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [show sec53S T L = T ⊓ L from rfl, ← hST, hSK]
  exact inf_le_right

theorem mem_L_iff (hpc : perfectCore (fG1 M L H B) = L) (x : ↥(fG1 M L H B)) :
    (x : G) ∈ L ↔ ((isoφ1 Φ x : ↥N₁) : P) ∈ perfectCore N₁ := by
  rw [← mem_perfectCore_iff_of_equiv (isoφ1 Φ) x, hpc]

theorem mem_K_iff (hpc : perfectCore (fG2 M L H D) = oTwoUpper H) (x : ↥(fG2 M L H D)) :
    (x : G) ∈ oTwoUpper H ↔ ((isoφ2 Φ x : ↥N₂) : P) ∈ perfectCore N₂ := by
  rw [← mem_perfectCore_iff_of_equiv (isoφ2 Φ) x, hpc]

omit [Finite P] in
theorem mem_S_iff (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (x : ↥(fG1 M L H B ⊓ fG2 M L H D)) :
    (x : G) ∈ sec53S T L ↔ ((isoφ12 Φ x : ↥(N₁ ⊓ N₂)) : P) ∈ pCoreOf 2 (N₁ ⊓ N₂) := by
  rw [← pCoreOf_fG12 h527 hyp, mem_pCoreOf_iff_of_equiv (isoφ12 Φ) x]

omit [Finite G] [Finite P] in
theorem mem_fG2_of_mem (x : ↥(fG1 M L H B)) (hx : ((isoφ1 Φ x : ↥N₁) : P) ∈ N₂) :
    (x : G) ∈ fG2 M L H D := by
  set y : ↥(N₁ ⊓ N₂) := ⟨_, Subgroup.mem_inf.mpr ⟨(isoφ1 Φ x).2, hx⟩⟩ with hy
  set x' := (isoφ12 Φ).symm y with hx'
  have h1 := coe_isoφ12_eq_φ1 Φ x'
  rw [hx', MulEquiv.apply_symm_apply, hy] at h1
  have h2 : (⟨(x' : G), (Subgroup.mem_inf.mp x'.2).1⟩ : ↥(fG1 M L H B)) = x :=
    (isoφ1 Φ).injective (Subtype.ext h1.symm)
  rw [← h2]
  exact (Subgroup.mem_inf.mp x'.2).2

omit [Finite G] [Finite P] in
theorem mem_fG1_of_mem (x : ↥(fG2 M L H D)) (hx : ((isoφ2 Φ x : ↥N₂) : P) ∈ N₁) :
    (x : G) ∈ fG1 M L H B := by
  set y : ↥(N₁ ⊓ N₂) := ⟨_, Subgroup.mem_inf.mpr ⟨hx, (isoφ2 Φ x).2⟩⟩ with hy
  set x' := (isoφ12 Φ).symm y with hx'
  have h1 := coe_isoφ12_eq_φ2 Φ x'
  rw [hx', MulEquiv.apply_symm_apply, hy] at h1
  have h2 : (⟨(x' : G), (Subgroup.mem_inf.mp x'.2).2⟩ : ↥(fG2 M L H D)) = x :=
    (isoφ2 Φ).injective (Subtype.ext h1.symm)
  rw [← h2]
  exact (Subgroup.mem_inf.mp x'.2).1

end CFSG.Quasithin.H13.Sec53F

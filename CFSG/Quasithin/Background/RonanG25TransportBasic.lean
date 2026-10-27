module

public import CFSG.Quasithin.Background.RonanG25Defs
public import CFSG.Quasithin.Background.RonanG25Mod

public section

namespace CFSG.Quasithin.RonanG25

section Transport

variable {G : Type} [Group G] {F : Type} [Field F] {X : Subgroup G} {E : Type} [AddCommGroup E]

@[expose] def pre (B : Subgroup G) (φ : ↥B →* Multiplicative E) (M : AddSubgroup E) : Subgroup G :=
  ((AddSubgroup.toSubgroup M).comap φ).map B.subtype

structure Equivariant (X B : Subgroup G) (φ : ↥B →* Multiplicative E)
    (act : ↥X → E →+ E) : Prop where
  normalizes : ∀ x ∈ X, ∀ y ∈ B, x * y * x⁻¹ ∈ B
  equiv : ∀ (x : ↥X) (y y' : ↥B), (x : G) * (y : G) * (x : G)⁻¹ = (y' : G) →
    φ y' = Multiplicative.ofAdd (act x (Multiplicative.toAdd (φ y)))

variable {B : Subgroup G} {φ : ↥B →* Multiplicative E} {act : ↥X → E →+ E}

theorem mem_pre {M : AddSubgroup E} {y : G} :
    y ∈ pre B φ M ↔ ∃ hy : y ∈ B, Multiplicative.toAdd (φ ⟨y, hy⟩) ∈ M := by
  unfold pre
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hy, hM⟩
    exact ⟨⟨y, hy⟩, hM, rfl⟩

theorem pre_le (M : AddSubgroup E) : pre B φ M ≤ B := by
  intro y hy
  exact (mem_pre.mp hy).1

theorem pre_mono {M₁ M₂ : AddSubgroup E} (h : M₁ ≤ M₂) : pre B φ M₁ ≤ pre B φ M₂ := by
  intro y hy
  obtain ⟨hyB, hM⟩ := mem_pre.mp hy
  exact mem_pre.mpr ⟨hyB, h hM⟩

theorem pre_inj {N M₁ M₂ : AddSubgroup E}
    (hN : ∀ e, e ∈ N ↔ ∃ y, φ y = Multiplicative.ofAdd e) (h₁ : M₁ ≤ N) (h₂ : M₂ ≤ N)
    (h : pre B φ M₁ = pre B φ M₂) : M₁ = M₂ := by
  have key : ∀ {P Q : AddSubgroup E}, P ≤ N → pre B φ P = pre B φ Q → P ≤ Q := by
    intro P Q hP hPQ e he
    obtain ⟨y, hy⟩ := (hN e).mp (hP he)
    have hmem : (y : G) ∈ pre B φ P := by
      refine mem_pre.mpr ⟨y.2, ?_⟩
      show Multiplicative.toAdd (φ y) ∈ P
      rw [hy]
      exact he
    rw [hPQ] at hmem
    obtain ⟨_, hQ⟩ := mem_pre.mp hmem
    have hQ' : Multiplicative.toAdd (φ y) ∈ Q := hQ
    rw [hy] at hQ'
    exact hQ'
  exact le_antisymm (key h₁ h) (key h₂ h.symm)

theorem inv_pre (hE : Equivariant X B φ act) {M : AddSubgroup E} (hM : AInv act M) :
    Inv X (pre B φ M) := by
  intro x hx y hy
  obtain ⟨hyB, hyM⟩ := mem_pre.mp hy
  have hxyB : x * y * x⁻¹ ∈ B := hE.normalizes x hx y hyB
  refine mem_pre.mpr ⟨hxyB, ?_⟩
  have key := hE.equiv ⟨x, hx⟩ ⟨y, hyB⟩ ⟨x * y * x⁻¹, hxyB⟩ rfl
  rw [key]
  exact hM ⟨x, hx⟩ _ hyM

theorem card_comap_eq_card_ker_mul_of_le_range {H K : Type} [Group H] [Group K] (f : H →* K)
    (S : Subgroup K) (hS : S ≤ f.range) :
    Nat.card (S.comap f) = Nat.card f.ker * Nat.card S := by
  have hker : f.ker ≤ S.comap f := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap, hx]
    exact S.one_mem
  have h1 := Subgroup.relIndex_mul_card f.ker (S.comap f)
  rw [inf_eq_left.mpr hker, Subgroup.relIndex_ker, Subgroup.map_comap_eq,
    inf_eq_right.mpr hS] at h1
  rw [← h1, Nat.mul_comm]

theorem card_pre [Finite G] {N : AddSubgroup E}
    (hN : ∀ e, e ∈ N ↔ ∃ y, φ y = Multiplicative.ofAdd e) {M : AddSubgroup E} (hM : M ≤ N) :
    Nat.card (pre B φ M) = Nat.card (pre B φ ⊥) * Nat.card M := by
  have hle : AddSubgroup.toSubgroup M ≤ φ.range := by
    intro x hx
    have hx' : Multiplicative.toAdd x ∈ M := hx
    obtain ⟨y, hy⟩ := (hN _).mp (hM hx')
    exact MonoidHom.mem_range.mpr ⟨y, by simp [hy]⟩
  have hbot : AddSubgroup.toSubgroup (⊥ : AddSubgroup E) = ⊥ := by
    ext x
    simp
  have hM' : Nat.card (AddSubgroup.toSubgroup M) = Nat.card M := by
    symm
    exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun a => by simp))
  have h1 : Nat.card (pre B φ M) = Nat.card ((AddSubgroup.toSubgroup M).comap φ) := by
    unfold pre
    exact Subgroup.card_subtype B _
  have h2 : Nat.card (pre B φ ⊥) = Nat.card φ.ker := by
    unfold pre
    rw [hbot]
    exact Subgroup.card_subtype B _
  rw [h1, h2, card_comap_eq_card_ker_mul_of_le_range φ _ hle, hM']

end Transport

end CFSG.Quasithin.RonanG25

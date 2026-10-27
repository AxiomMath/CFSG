module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Timmesfeld.ARS.BasicRankOne

public section

namespace CFSG.Timmesfeld.Transvection.ModelRank

open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem not_commuting_of_opposite {A B : Subgroup G} (h : Opposite A B) : ¬ Commuting A B := by
  intro hc
  obtain ⟨hne, h1, h2⟩ := h
  have hA : ∀ b ∈ B, conjSub A b = A := fun b hb =>
    conjSub_of_forall_commute fun a ha => (hc a ha b hb).symm
  have hB : ∀ a ∈ A, conjSub B a = B := fun a ha =>
    conjSub_of_forall_commute fun b hb => hc a ha b hb
  by_cases hAB : A ≤ B
  · have hBA : ¬ B ≤ A := fun hBA => hne (le_antisymm hAB hBA)
    obtain ⟨b, hb, hbA⟩ := IsConcreteLE.not_le_iff_exists.1 hBA
    have hb1 : b ≠ 1 := fun e => hbA (e ▸ A.one_mem)
    obtain ⟨a, ha, -, e⟩ := h2 b hb hb1
    rw [hB a ha, hA b hb] at e
    exact hne e.symm
  · obtain ⟨a, ha, haB⟩ := IsConcreteLE.not_le_iff_exists.1 hAB
    have ha1 : a ≠ 1 := fun e => haB (e ▸ B.one_mem)
    obtain ⟨b, hb, -, e⟩ := h1 a ha ha1
    rw [hA b hb, hB a ha] at e
    exact hne e

theorem commuting_sup {A B C : Subgroup G} (hB : Commuting A B) (hC : Commuting A C) :
    Commuting A (B ⊔ C) := by
  have hle : B ⊔ C ≤ Subgroup.centralizer (A : Set G) :=
    sup_le (fun b hb => Subgroup.mem_centralizer_iff.2 fun a ha => (hB a ha b hb).eq)
      (fun c hc => Subgroup.mem_centralizer_iff.2 fun a ha => (hC a ha c hc).eq)
  exact fun a ha x hx => Subgroup.mem_centralizer_iff.1 (hle hx) a ha

theorem commuting_mono {A B A' B' : Subgroup G} (h : Commuting A B) (hA : A' ≤ A) (hB : B' ≤ B) :
    Commuting A' B' :=
  fun a ha b hb => h a (hA ha) b (hB hb)

theorem commuting_symm {A B : Subgroup G} (h : Commuting A B) : Commuting B A :=
  fun b hb a ha => (h a ha b hb).symm

variable {K : Type*} [Group K]

theorem commuting_map (Φ : K →* G) {X Y : Subgroup K} (h : Commuting X Y) :
    Commuting (X.map Φ) (Y.map Φ) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (h x hx y hy).map Φ

theorem commutator_mem_center {Φ : K →* G} (hker : Φ.ker ≤ Subgroup.center K) {X Y : Subgroup K}
    (h : Commuting (X.map Φ) (Y.map Φ)) : ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ Subgroup.center K :=
  fun x hx y hy => hker (by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)

theorem conjSub_map (Φ : K →* G) (A : Subgroup K) (g : K) :
    conjSub (A.map Φ) (Φ g) = (conjSub A g).map Φ := by
  rw [conjSub, conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem linearIndependent_of_forms {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] {x : ι → V} (L : ι → V →ₗ[k] k) (h0 : ∀ s t, s ≠ t → L t (x s) = 0)
    (h1 : ∀ t, L t (x t) ≠ 0) : LinearIndependent k x := by
  rw [Fintype.linearIndependent_iff]
  intro g hg t
  have h := congrArg (L t) hg
  rw [map_sum, map_zero, Finset.sum_eq_single t] at h
  · rw [map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_right (h1 t)
  · intro s _ hst
    rw [map_smul, h0 s t hst, smul_zero]
  · simp

end CFSG.Timmesfeld.Transvection.ModelRank

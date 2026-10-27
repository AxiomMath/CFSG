module

public import CFSG.Quasithin.EmptyFaithful.S146E3

public section

namespace CFSG.Quasithin.L3Stab

open CFSG.Quasithin.L3 CFSG.SectionRank.Ccomm

theorem card_fix_two_le : ∀ v w : Vec, v ≠ 0 → w ≠ 0 → v ≠ w →
    (Finset.univ.filter fun g : Γ => act g v = v ∧ act g w = w).card ≤ 4 := by
  decide +kernel

theorem false_of_fix_two {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1) (hcard : Nat.card W = 8)
    (D : Subgroup (MulAut W)) (hD : Nat.card D = 8) {w₁ w₂ : W} (h1 : w₁ ≠ 1) (h2 : w₂ ≠ 1)
    (h12 : w₁ ≠ w₂) (hfix : ∀ σ ∈ D, σ w₁ = w₁ ∧ σ w₂ = w₂) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq (n := 3)
    (by rw [hcard]; norm_num)
  let Φ : MulAut W ≃* Γ :=
    (elemAutEquivGL e).trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).symm
  have hΦ : ∀ (σ : MulAut W) (x : W),
      act (Φ σ) (Multiplicative.toAdd (e x)) = Multiplicative.toAdd (e (σ x)) := by
    intro σ x
    have h := elemAutEquivGL_mulVec e σ x
    have h2 : CFSG.QuasithinUnique.Setup.Family.slEquivGL 3 (Φ σ) = elemAutEquivGL e σ :=
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).apply_symm_apply _
    rw [← h, ← h2, slEquivGL_coe]
    rfl
  set v₁ : Vec := Multiplicative.toAdd (e w₁) with hv₁
  set v₂ : Vec := Multiplicative.toAdd (e w₂) with hv₂
  have hv₁0 : v₁ ≠ 0 := fun h => h1 (e.injective (by rw [map_one]; exact toAdd_eq_zero.mp h))
  have hv₂0 : v₂ ≠ 0 := fun h => h2 (e.injective (by rw [map_one]; exact toAdd_eq_zero.mp h))
  have hv12 : v₁ ≠ v₂ := fun h => h12 (e.injective (Multiplicative.toAdd.injective h))
  set D' : Subgroup Γ := D.map Φ.toMonoidHom with hD'
  have hD'card : Nat.card D' = 8 := by
    rw [hD', Subgroup.card_map_of_injective Φ.injective, hD]
  let f : ↥D' → {g : Γ // act g v₁ = v₁ ∧ act g v₂ = v₂} := fun g => ⟨g.1, by
    obtain ⟨σ, hσ, hσg⟩ := Subgroup.mem_map.mp g.2
    have hg : (g : Γ) = Φ σ := hσg.symm
    obtain ⟨hf1, hf2⟩ := hfix σ hσ
    rw [hg]
    refine ⟨?_, ?_⟩
    · rw [hv₁, hΦ, hf1]
    · rw [hv₂, hΦ, hf2]⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (congrArg (fun x : {g : Γ // act g v₁ = v₁ ∧ act g v₂ = v₂} => (x : Γ)) hab)
  have h8 : Nat.card D' ≤ Nat.card {g : Γ // act g v₁ = v₁ ∧ act g v₂ = v₂} :=
    Nat.card_le_card_of_injective f hf
  have h4 : Nat.card {g : Γ // act g v₁ = v₁ ∧ act g v₂ = v₂} ≤ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_fix_two_le v₁ v₂ hv₁0 hv₂0 hv12
  omega

end CFSG.Quasithin.L3Stab

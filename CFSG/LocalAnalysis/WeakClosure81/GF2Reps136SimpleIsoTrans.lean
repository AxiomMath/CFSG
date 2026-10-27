module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIsoOrbitSizes
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIsoMixed

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

variable {Q : Type} [CommGroup Q]

noncomputable def w1369_ta_suppFun {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (S : Subgroup Q) : Fin k → Bool := fun i => by
  classical
  exact if i ∈ w1369_ta_supp P S then true else false

lemma w1369_ta_transitive_on_simple [Finite Q] {Λ N : Subgroup (MulAut Q)}
    (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ)
    {k : ℕ} (hpart : ∀ i : Fin k, ∃ j : Fin k, j ≠ i)
    {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i)) (hIsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    {Ncard m : ℕ} (hcard : Nat.card {f : Fin k → Bool // f ≠ (0 : Fin k → Bool)} ≤ Ncard)
    (hbound : Ncard < 2 * m)
    (hm : ∀ S : Subgroup Q, w1369_ta_IsSimple Λ S → m ≤ (w1369_ta_orb N S).ncard) :
    ∀ S₁ S₂ : Subgroup Q, w1369_ta_IsSimple Λ S₁ → w1369_ta_IsSimple Λ S₂ →
      ∃ n ∈ N, S₂ = S₁.map n.toMonoidHom := by
  classical
  let α := {S : Subgroup Q // w1369_ta_IsSimple Λ S}
  let β := {f : Fin k → Bool // f ≠ (0 : Fin k → Bool)}
  haveI : Finite (Subgroup Q) :=
    Finite.of_injective (fun H : Subgroup Q => (H : Set Q)) SetLike.coe_injective
  haveI : Finite α := Finite.of_injective (fun a : α => a.1) Subtype.val_injective
  haveI : Finite β := Finite.of_injective (fun f : β => (f : Fin k → Bool)) Subtype.val_injective
  letI : MulAction N α :=
    { smul := fun n S => ⟨S.1.map (n : MulAut Q).toMonoidHom, w1369_simple_map hnorm S.2 n.2⟩
      one_smul := fun S => by
        apply Subtype.ext
        show S.1.map (((1 : N) : MulAut Q)).toMonoidHom = S.1
        rw [Subgroup.coe_one]
        exact Subgroup.map_id S.1
      mul_smul := fun m n S => by
        apply Subtype.ext
        show S.1.map (((m * n : N) : MulAut Q)).toMonoidHom =
          (S.1.map (n : MulAut Q).toMonoidHom).map (m : MulAut Q).toMonoidHom
        rw [Subgroup.map_map]
        rfl }
  have horb : ∀ a : α, (MulAction.orbit N a).ncard = (w1369_ta_orb N a.1).ncard := by
    intro a
    have himg : ((Subtype.val : α → Subgroup Q) '' (MulAction.orbit N a)) =
        w1369_ta_orb N a.1 := by
      ext T
      constructor
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨g, rfl⟩ := hb
        exact w1369_ta_mem_orb_iff.mpr ⟨g, rfl⟩
      · intro hT
        obtain ⟨g, hg⟩ := w1369_ta_mem_orb_iff.mp hT
        exact ⟨g • a, ⟨g, rfl⟩, hg.symm⟩
    rw [← Set.ncard_image_of_injective (MulAction.orbit N a) Subtype.val_injective, himg]
  let wfun : α → β := fun a => ⟨w1369_ta_suppFun P a.1, by
    obtain ⟨i, hi⟩ := w1369_ta_supp_nonempty P a.2.1
    intro hzero
    have h1 : w1369_ta_suppFun P a.1 i = false :=
      congrArg (fun f : Fin k → Bool => f i) hzero
    simp [w1369_ta_suppFun, hi] at h1⟩
  have hw : Function.Injective wfun := by
    intro a b hab
    apply Subtype.ext
    apply w1369_ta_eq_of_supp_eq P hstab hIsimple hend hisoAll hpart a.2 b.2
    ext i
    have h1 : w1369_ta_suppFun P a.1 i = w1369_ta_suppFun P b.1 i :=
      congrArg (fun f : β => (f : Fin k → Bool) i) hab
    by_cases ha : i ∈ w1369_ta_supp P a.1 <;>
      by_cases hb : i ∈ w1369_ta_supp P b.1 <;>
      simp [w1369_ta_suppFun, ha, hb] at h1 ⊢
  have hm' : ∀ a : α, m ≤ (MulAction.orbit N a).ncard := by
    intro a
    rw [horb a]
    exact hm a.1 a.2
  have htrans := w1369_ta_transitive_of_orbit_bound (G := N) wfun hw hcard hm' hbound
  intro S₁ S₂ hS₁ hS₂
  obtain ⟨g, hg⟩ := htrans ⟨S₁, hS₁⟩ ⟨S₂, hS₂⟩
  exact ⟨g, g.2, (congrArg (fun a : α => a.1) hg).symm⟩

lemma w1369_ta_hisoAll_three {Λ N : Subgroup (MulAut Q)}
    (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ)
    {I : Fin 3 → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i)) (hIsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), I j) = ⊥)
    (hirr : ∀ M : Subgroup Q, StableUnder N M → M = ⊥ ∨ M = ⊤)
    {a b : Fin 3} (hab : a ≠ b) (hsecab : SecIsoOn Λ (I a) ⊥ (I b) ⊥) :
    ∀ i j : Fin 3, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ := by
  obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
    fin_cases a <;> fin_cases b <;> first
      | exact absurd rfl hab
      | decide
  have hac : a ≠ c := hca.symm
  have hbc : b ≠ c := hcb.symm
  have hcover : ∀ l : Fin 3, l = a ∨ l = b ∨ l = c := by
    intro l
    fin_cases l <;> fin_cases a <;> fin_cases b <;> fin_cases c
    all_goals first | decide | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl hbc
  have hsecac : SecIsoOn Λ (I a) ⊥ (I c) ⊥ := by
    by_contra hnac
    exact w1369_ta_mixed_contra hnorm P hstab hIsimple hind hab hac hbc hcover hsecab hnac hirr
  have hsecbc : SecIsoOn Λ (I b) ⊥ (I c) ⊥ :=
    secIsoOn_trans (w1369_ta_SecIsoOn_symm hsecab) hsecac
  intro i j hij
  rcases hcover i with hi | hi | hi <;> subst i <;>
    rcases hcover j with hj | hj | hj <;> subst j
  all_goals first
    | exact absurd rfl hij
    | exact hsecab
    | exact hsecac
    | exact hsecbc
    | exact w1369_ta_SecIsoOn_symm hsecab
    | exact w1369_ta_SecIsoOn_symm hsecac
    | exact w1369_ta_SecIsoOn_symm hsecbc

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

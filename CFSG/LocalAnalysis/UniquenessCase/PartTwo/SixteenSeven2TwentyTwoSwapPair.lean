module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_twenty_two_preTil_inf (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (S T : Subgroup (Vtil V₀ V hV)) :
    preTil V₀ V hV (S ⊓ T) = preTil V₀ V hV S ⊓ preTil V₀ V hV T := by
  unfold preTil
  rw [Subgroup.comap_inf, Subgroup.map_inf _ _ (valHom V hV) IntMod.val_injective]

theorem s16c167_twenty_two_preTil_sup (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (S T : Subgroup (Vtil V₀ V hV)) :
    preTil V₀ V hV (S ⊔ T) = preTil V₀ V hV S ⊔ preTil V₀ V hV T := by
  unfold preTil
  rw [← Subgroup.comap_sup_eq (mkTil V₀ V hV) S T (mkTil_surjective V₀ V hV), Subgroup.map_sup]

theorem s16c167_twenty_two_imgTil_bot (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    imgTil V₀ V hV ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, hx, rfl⟩ := (mem_imgTil V₀ V hV ⊥ q).1 hq
  have h1 : x = 1 := IntMod.val_injective (by rw [IntMod.val_one]; exact mem_bot.1 hx)
  rw [h1, map_one]
  exact one_mem _

theorem s16c167_twenty_two_delta {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {Δ : Set (Subgroup G)} (hn : Δ.ncard = 2) (hle : ∀ I ∈ Δ, I ≤ V) (hi : sSupIndep Δ)
    (hs : sSup Δ = V) {F : Fin 3 → Subgroup (Vtil ⊥ V hV)}
    (hF : ∀ I ∈ Δ, ∃ i, imgTil ⊥ V hV I = F i) :
    (∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ F j₁ ⊓ F j₂ = ⊥ ∧ F j₁ ⊔ F j₂ = ⊤) ∧
      ∀ I ∈ Δ, ∃ i, I = preTil ⊥ V hV (F i) := by
  have hpre : ∀ I : Subgroup G, I ≤ V → preTil ⊥ V hV (imgTil ⊥ V hV I) = I := by
    intro I hI
    refine le_antisymm ?_ fun g hg => le_preTil_imgTil ⊥ V hV I ⟨hg, hI hg⟩
    intro g hg
    obtain ⟨x, rfl, hx⟩ := (mem_preTil ⊥ V hV _).1 hg
    obtain ⟨y, hyI, hyx⟩ := (mem_imgTil ⊥ V hV I _).1 hx
    have := (mkTil_eq_iff ⊥ V hV y x).1 hyx
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    rwa [← this]
  have hVtop : imgTil ⊥ V hV V = ⊤ := by
    have := imgTil_preTil ⊥ V hV ⊤
    rwa [preTil_top] at this
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.1 hn
  have ha : a ∈ ({a, b} : Set (Subgroup G)) := Set.mem_insert _ _
  have hb : b ∈ ({a, b} : Set (Subgroup G)) := Set.mem_insert_of_mem _ rfl
  have hle_a := hle a ha
  have hle_b := hle b hb
  have hdisj : a ⊓ b = ⊥ := disjoint_iff.1 ((sSupIndep_pair hab).1 hi)
  have hsup : a ⊔ b = V := by rwa [sSup_pair] at hs
  obtain ⟨j₁, hj₁⟩ := hF a ha
  obtain ⟨j₂, hj₂⟩ := hF b hb
  refine ⟨⟨j₁, j₂, ?_, ?_, ?_⟩, ?_⟩
  · intro h
    apply hab
    rw [← hpre a hle_a, ← hpre b hle_b, hj₁, hj₂, h]
  · rw [← hj₁, ← hj₂, ← imgTil_preTil ⊥ V hV (imgTil ⊥ V hV a ⊓ imgTil ⊥ V hV b),
      s16c167_twenty_two_preTil_inf, hpre a hle_a, hpre b hle_b, hdisj,
      s16c167_twenty_two_imgTil_bot ⊥ V hV]
  · rw [← hj₁, ← hj₂, ← imgTil_preTil ⊥ V hV (imgTil ⊥ V hV a ⊔ imgTil ⊥ V hV b),
      s16c167_twenty_two_preTil_sup, hpre a hle_a, hpre b hle_b, hsup, hVtop]
  · intro I hI
    obtain ⟨i, hi'⟩ := hF I hI
    exact ⟨i, by rw [← hi', hpre I (hle I hI)]⟩

theorem s16c167_twenty_two_pairs {W : Type*} [Group W] {X : Subgroup (MulAut W)}
    {F : Fin 3 → Subgroup W} {π : ↥X →* Equiv.Perm (Fin 3)}
    (hact : ∀ (x : ↥X) (i : Fin 3), (F i).map (x : MulAut W).toMonoidHom = F (π x i))
    (htrans : ∀ i j : Fin 3, ∃ y : ↥X, π y i = j) {j₁ j₂ : Fin 3} (hj : j₁ ≠ j₂)
    (hinf : F j₁ ⊓ F j₂ = ⊥) (hsup : F j₁ ⊔ F j₂ = ⊤) :
    ∀ i j : Fin 3, i ≠ j → F i ⊓ F j = ⊥ ∧ F i ⊔ F j = ⊤ := by
  have key : ∀ j₁ j₂ i j : Fin 3, j₁ ≠ j₂ → i ≠ j → ∃ j₃ k : Fin 3,
      ∀ τ : Equiv.Perm (Fin 3), τ j₃ = k → (τ j₁ = i ∧ τ j₂ = j) ∨ (τ j₁ = j ∧ τ j₂ = i) := by
    decide
  intro i j hij
  obtain ⟨j₃, k, hk⟩ := key j₁ j₂ i j hj hij
  obtain ⟨y, hy⟩ := htrans j₃ k
  have hinf' : (F j₁).map (y : MulAut W).toMonoidHom ⊓ (F j₂).map (y : MulAut W).toMonoidHom =
      ⊥ := by
    rw [← Subgroup.map_inf _ _ _ (y : MulAut W).injective, hinf, Subgroup.map_bot]
  have hsup' : (F j₁).map (y : MulAut W).toMonoidHom ⊔ (F j₂).map (y : MulAut W).toMonoidHom =
      ⊤ := by
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 (y : MulAut W).surjective
  rw [hact y j₁, hact y j₂] at hinf' hsup'
  rcases hk (π y) hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hinf' hsup'
    exact ⟨hinf', hsup'⟩
  · rw [h1, h2] at hinf' hsup'
    exact ⟨by rwa [inf_comm], by rwa [sup_comm]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

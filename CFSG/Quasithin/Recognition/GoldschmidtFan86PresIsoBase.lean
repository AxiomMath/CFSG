module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Amalgam

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin

section Presented

theorem toGroup_bijective {α : Type*} {rels : Set (FreeGroup α)} {N : ℕ} {B : Type*} [Group B]
    {g : α → B} (hr : ∀ r ∈ rels, FreeGroup.lift g r = 1)
    (hg : Subgroup.closure (Set.range g) = ⊤) (hfin : Finite (PresentedGroup rels))
    (hle : Nat.card (PresentedGroup rels) ≤ N) (hB : Nat.card B = N) :
    Function.Bijective (PresentedGroup.toGroup hr) := by
  have hsurj : Function.Surjective (PresentedGroup.toGroup hr) := by
    intro b
    have hb : b ∈ (FreeGroup.lift g).range := by
      rw [FreeGroup.range_lift_eq_closure, hg]; trivial
    obtain ⟨u, rfl⟩ := hb
    exact ⟨PresentedGroup.mk _ u, rfl⟩
  exact hsurj.bijective_of_nat_card_le (hB ▸ hle)

theorem exists_mulEquiv_presented {α : Type*} {rels : Set (FreeGroup α)} {N : ℕ} {B : Type*}
    [Group B] {g : α → B} (hr : ∀ r ∈ rels, FreeGroup.lift g r = 1)
    (hg : Subgroup.closure (Set.range g) = ⊤) (hfin : Finite (PresentedGroup rels))
    (hle : Nat.card (PresentedGroup rels) ≤ N) (hB : Nat.card B = N) :
    ∃ φ : PresentedGroup rels ≃* B, ∀ i, φ (PresentedGroup.of i) = g i :=
  ⟨MulEquiv.ofBijective _ (toGroup_bijective hr hg hfin hle hB),
    fun _ => PresentedGroup.toGroup.of hr⟩

end Presented

section Links

variable {A C B A' C' B' : Type*} [Group A] [Group C] [Group B] [Group A'] [Group C'] [Group B']

@[expose] def amalgamDiag (X : GoldAmalgam A C B) : Subgroup (A × B) :=
  (X.toA.prod X.toB).range

theorem amalgamDiag_eq_closure (X : GoldAmalgam A C B) {ι : Type*} (a : ι → A) (b : ι → B)
    (hl : ∀ i, AmalgamLink X (a i) (b i)) (hb : Subgroup.closure (Set.range b) = X.edgeB) :
    amalgamDiag X = Subgroup.closure (Set.range fun i => (a i, b i)) := by
  choose c hc using hl
  have hC : Subgroup.closure (Set.range c) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : X.toB x ∈ Subgroup.closure (Set.range b) := by
      rw [hb]; exact ⟨x, rfl⟩
    have hbc : Set.range b = X.toB '' Set.range c := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i => (hc i).2.symm)
    rw [hbc, ← MonoidHom.map_closure] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← X.toB_injective hyx]
    exact hy
  have hd : amalgamDiag X = (Subgroup.closure (Set.range c)).map (X.toA.prod X.toB) := by
    rw [hC, Subgroup.map_top]; rfl
  rw [hd, MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext i
  exact Prod.ext (hc i).1 (hc i).2

theorem isIso_of_map_diag {X : GoldAmalgam A C B} {X' : GoldAmalgam A' C' B'} (fA : A ≃* A')
    (fB : B ≃* B')
    (h : (amalgamDiag X).map (fA.prodCongr fB).toMonoidHom = amalgamDiag X') : X.IsIso X' := by
  have hinj : Function.Injective (X.toA.prod X.toB) := fun c d hcd =>
    X.toA_injective (congrArg Prod.fst hcd)
  have hinj' : Function.Injective (X'.toA.prod X'.toB) := fun c d hcd =>
    X'.toA_injective (congrArg Prod.fst hcd)
  let ψ : C ≃* amalgamDiag X := MonoidHom.ofInjective hinj
  let ψ' : C' ≃* amalgamDiag X' := MonoidHom.ofInjective hinj'
  let θ : amalgamDiag X ≃* amalgamDiag X' :=
    (MulEquiv.subgroupMap (fA.prodCongr fB) _).trans (MulEquiv.subgroupCongr h)
  let eC : C ≃* C' := ψ.trans (θ.trans ψ'.symm)
  have key : ∀ c, (X'.toA (eC c), X'.toB (eC c)) = (fA (X.toA c), fB (X.toB c)) := by
    intro c
    have h1 : ψ' (eC c) = θ (ψ c) := by simp [eC]
    exact congrArg Subtype.val h1
  exact ⟨⟨fA, eC, fB, fun c => (congrArg Prod.fst (key c)).symm,
    fun c => (congrArg Prod.snd (key c)).symm⟩⟩

theorem isIso_of_links {X : GoldAmalgam A C B} {X' : GoldAmalgam A' C' B'} (fA : A ≃* A')
    (fB : B ≃* B') {ι : Type*} (a : ι → A) (b : ι → B) (a' : ι → A') (b' : ι → B')
    (hl : ∀ i, AmalgamLink X (a i) (b i)) (hl' : ∀ i, AmalgamLink X' (a' i) (b' i))
    (hb : Subgroup.closure (Set.range b) = X.edgeB)
    (hb' : Subgroup.closure (Set.range b') = X'.edgeB)
    (hfa : ∀ i, fA (a i) = a' i) (hfb : ∀ i, fB (b i) = b' i) : X.IsIso X' := by
  refine isIso_of_map_diag fA fB ?_
  rw [amalgamDiag_eq_closure X a b hl hb, amalgamDiag_eq_closure X' a' b' hl' hb',
    MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext i
  exact Prod.ext (hfa i) (hfb i)

theorem closure_range_eq_edgeB {X : GoldAmalgam A C B} {ι : Type*} (b : ι → B)
    (hl : ∀ i, ∃ a, AmalgamLink X a (b i)) {S : Set B} (hS : Subgroup.closure S = X.edgeB)
    (hSb : S ⊆ Set.range b) : Subgroup.closure (Set.range b) = X.edgeB := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) (hS ▸ Subgroup.closure_mono hSb)
  rintro _ ⟨i, rfl⟩
  obtain ⟨a, c, -, hc⟩ := hl i
  exact ⟨c, hc⟩

theorem card_vertexA (X : GoldAmalgam A C B) : Nat.card A = Nat.card C * X.edgeA.index := by
  rw [← Subgroup.card_mul_index X.edgeA]
  congr 1
  exact (Nat.card_congr (MonoidHom.ofInjective X.toA_injective).toEquiv).symm

theorem card_vertexB (X : GoldAmalgam A C B) : Nat.card B = Nat.card C * X.edgeB.index := by
  rw [← Subgroup.card_mul_index X.edgeB]
  congr 1
  exact (Nat.card_congr (MonoidHom.ofInjective X.toB_injective).toEquiv).symm

end Links

end CFSG.Quasithin.Fan86

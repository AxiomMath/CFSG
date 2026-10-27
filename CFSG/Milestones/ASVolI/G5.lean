module

public import CFSG.Quasithin.Background.RonanG52Main
public import CFSG.Quasithin.Background.RonanG51F4
public import CFSG.Quasithin.Background.ShultG53Final

public section

namespace CFSG.ASVolI.ChG

open CFSG.QuasithinUnique

structure FMod (X : Type) [Group X] where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [module : Module (ZMod 2) carrier]
  [finite : Finite carrier]
  ρ : Representation (ZMod 2) X carrier

attribute [instance] FMod.addCommGroup FMod.module FMod.finite

namespace FMod

variable {X : Type} [Group X]

@[expose] def IsInv (M : FMod X) (S : AddSubgroup M.carrier) : Prop :=
  ∀ g : X, ∀ m ∈ S, M.ρ g m ∈ S

@[expose] def IsIrred (M : FMod X) : Prop :=
  Nontrivial M.carrier ∧ ∀ S : AddSubgroup M.carrier, M.IsInv S → S = ⊥ ∨ S = ⊤

@[expose] def Iso (M N : FMod X) : Prop :=
  ∃ f : M.carrier ≃+ N.carrier, ∀ (g : X) (m : M.carrier), f (M.ρ g m) = N.ρ g (f m)

@[expose] def restrict (M : FMod X) (H : Subgroup X) : FMod ↥H where
  carrier := M.carrier
  ρ := M.ρ.comp H.subtype

@[expose] def FixesPoint (M : FMod X) (S : Set X) : Prop :=
  ∃ v : M.carrier, v ≠ 0 ∧ ∀ g ∈ S, M.ρ g v = v

@[expose] def FixesLine (M : FMod X) (S : Set X) : Prop :=
  ∃ L : AddSubgroup M.carrier, Nat.card L = 4 ∧ ∀ g ∈ S, ∀ l ∈ L, M.ρ g l ∈ L

@[expose] def IsTrivial (M : FMod X) : Prop := ∀ g m, M.ρ g m = m

@[expose] def IsPerfect (M : FMod X) : Prop :=
  AddSubgroup.closure {z : M.carrier | ∃ (g : X) (m : M.carrier), z = M.ρ g m - m} = ⊤

@[expose] def IsCovering (W V : FMod X) : Prop :=
  W.IsPerfect ∧ ∃ (W₀ : AddSubgroup W.carrier) (f : W.carrier →+ V.carrier),
    (∀ w ∈ W₀, ∀ g, W.ρ g w = w) ∧ Function.Surjective f ∧
    (∀ w, f w = 0 ↔ w ∈ W₀) ∧ ∀ g w, f (W.ρ g w) = V.ρ g (f w)

@[expose] def IsUniversalCovering (U V : FMod X) : Prop :=
  U.IsCovering V ∧ ∀ W : FMod X, W.IsCovering V →
    ∃ π : U.carrier →+ W.carrier, Function.Surjective π ∧ ∀ g u, π (U.ρ g u) = W.ρ g (π u)

@[expose] def IsFiveDimCover (U V : FMod X) : Prop :=
  U.IsUniversalCovering V ∧ Nat.card U.carrier = 2 ^ 5

end FMod

@[expose] def IsSteinbergModule (M : FMod (Equiv.Perm (Fin 6))) : Prop :=
  M.IsIrred ∧ Nat.card M.carrier = 2 ^ 16 ∧
    Module.Projective (MonoidAlgebra (ZMod 2) (Equiv.Perm (Fin 6))) M.ρ.asModule

structure HypG5 (T G₁ G₂ : Subgroup (Equiv.Perm (Fin 6))) : Prop where
  sylow : IsSylowTwoOf T (alternatingGroup (Fin 6))
  le₁ : G₁ ≤ alternatingGroup (Fin 6)
  le₂ : G₂ ≤ alternatingGroup (Fin 6)
  T_le₁ : T ≤ G₁
  T_le₂ : T ≤ G₂
  index₁ : G₁.relIndex (alternatingGroup (Fin 6)) = 15
  index₂ : G₂.relIndex (alternatingGroup (Fin 6)) = 15
  ne : G₁ ≠ G₂
  only : ∀ H : Subgroup (Equiv.Perm (Fin 6)), H ≤ alternatingGroup (Fin 6) → T ≤ H →
    H.relIndex (alternatingGroup (Fin 6)) = 15 → H = G₁ ∨ H = G₂

@[expose] def inG (H : Subgroup (Equiv.Perm (Fin 6))) : Set ↥(alternatingGroup (Fin 6)) :=
  {g | (g : Equiv.Perm (Fin 6)) ∈ H}


section Perm

open Classical

variable {X : Type} [Group X]

@[expose] def permAct (V : FMod X) (g : X) (u : V.carrier → ZMod 2) : V.carrier → ZMod 2 :=
  fun w => u (V.ρ g⁻¹ w)

@[expose] def evalZero (V : FMod X) : (V.carrier → ZMod 2) →+ ZMod 2 :=
  Pi.evalAddMonoidHom (fun _ : V.carrier => ZMod 2) 0

@[expose] noncomputable def weightHom (V : FMod X) : (V.carrier → ZMod 2) →+ ZMod 2 where
  toFun u := ∑ᶠ w, u w
  map_zero' := by simp
  map_add' := fun a b => by
    simpa using finsum_add_distrib (f := fun w => a w) (g := fun w => b w)
      (Set.toFinite _) (Set.toFinite _)

@[expose] def permSpace (V : FMod X) : AddSubgroup (V.carrier → ZMod 2) := (evalZero V).ker

@[expose] noncomputable def permCore (V : FMod X) : AddSubgroup (V.carrier → ZMod 2) :=
  (evalZero V).ker ⊓ (weightHom V).ker

@[expose] noncomputable def permOnes (V : FMod X) : AddSubgroup (V.carrier → ZMod 2) :=
  AddSubgroup.closure {fun w => if w = 0 then 0 else 1}

@[expose] noncomputable def lineCompl (V : FMod X) (l : AddSubgroup V.carrier) : V.carrier → ZMod 2 :=
  fun w => if w = 0 ∨ w ∈ l then 0 else 1

@[expose] noncomputable def perpCompl (V : FMod X) (B : LinearMap.BilinForm (ZMod 2) V.carrier) (x : V.carrier) :
    V.carrier → ZMod 2 :=
  fun w => if w ≠ 0 ∧ B w x ≠ 0 then 1 else 0

@[expose] def singLines (V : FMod X) (B : LinearMap.BilinForm (ZMod 2) V.carrier) :
    Set (AddSubgroup V.carrier) :=
  {S | Nat.card S = 4 ∧ ∀ x ∈ S, ∀ y ∈ S, B x y = 0}

end Perm

section Rad

variable {X A : Type} [AddCommGroup A] (act : X → A → A)

@[expose] def InvSub (S : AddSubgroup A) : Prop := ∀ g : X, ∀ a ∈ S, act g a ∈ S

@[expose] def IsMaxInvSub (N K : AddSubgroup A) : Prop :=
  K < N ∧ InvSub act K ∧ ∀ K' : AddSubgroup A, InvSub act K' → K ≤ K' → K' ≤ N → K' = K ∨ K' = N

@[expose] noncomputable def jrad (N : AddSubgroup A) : AddSubgroup A :=
  N ⊓ ⨅ (K : AddSubgroup A) (_ : IsMaxInvSub act N K), K

@[expose] noncomputable def jradPow (n : ℕ) (N : AddSubgroup A) : AddSubgroup A :=
  (jrad act)^[n] N

end Rad

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.ASVolI.ChG CFSG.ASVolI.ChG.FMod CFSG.QuasithinUnique

@[expose] def G_5_1 : Prop :=
  ∀ T G₁ G₂ : Subgroup (Equiv.Perm (Fin 6)), HypG5 T G₁ G₂ →
    ∃ M₁ M₄₁ M₄₂ M₁₆ : FMod ↥(alternatingGroup (Fin 6)),
      (M₁.IsIrred ∧ M₁.IsTrivial ∧ Nat.card M₁.carrier = 2) ∧
      (M₄₁.IsIrred ∧ Nat.card M₄₁.carrier = 2 ^ 4) ∧
      (M₄₂.IsIrred ∧ Nat.card M₄₂.carrier = 2 ^ 4) ∧
      (M₁₆.IsIrred ∧ Nat.card M₁₆.carrier = 2 ^ 16) ∧
      ¬ M₁.Iso M₄₁ ∧ ¬ M₁.Iso M₄₂ ∧ ¬ M₁.Iso M₁₆ ∧ ¬ M₄₁.Iso M₄₂ ∧ ¬ M₄₁.Iso M₁₆ ∧
        ¬ M₄₂.Iso M₁₆ ∧
      (∀ N : FMod ↥(alternatingGroup (Fin 6)), N.IsIrred →
        N.Iso M₁ ∨ N.Iso M₄₁ ∨ N.Iso M₄₂ ∨ N.Iso M₁₆) ∧
      (M₄₁.FixesPoint (inG G₁) ∧ M₄₁.FixesLine (inG G₂)) ∧
      (M₄₂.FixesPoint (inG G₂) ∧ M₄₂.FixesLine (inG G₁)) ∧
      ∃ St : FMod (Equiv.Perm (Fin 6)), IsSteinbergModule St ∧
        M₁₆.Iso (St.restrict (alternatingGroup (Fin 6))) ∧
        ∃ U₁ U₂ : Submodule (GaloisField 2 2) (TensorProduct (ZMod 2) (GaloisField 2 2) St.carrier),
          (∀ g : ↥(alternatingGroup (Fin 6)), ∀ x ∈ U₁,
            LinearMap.lTensor (GaloisField 2 2) (St.ρ (g : Equiv.Perm (Fin 6))) x ∈ U₁) ∧
          (∀ g : ↥(alternatingGroup (Fin 6)), ∀ x ∈ U₂,
            LinearMap.lTensor (GaloisField 2 2) (St.ρ (g : Equiv.Perm (Fin 6))) x ∈ U₂) ∧
          IsCompl U₁ U₂ ∧ Module.finrank (GaloisField 2 2) U₁ = 8 ∧
          (∀ t : Equiv.Perm (Fin 6), t ∉ alternatingGroup (Fin 6) →
            (U₂ : Set (TensorProduct (ZMod 2) (GaloisField 2 2) St.carrier)) =
              (LinearMap.lTensor (GaloisField 2 2) (St.ρ t)) '' (U₁ : Set _)) ∧
          (U₂ : Set (TensorProduct (ZMod 2) (GaloisField 2 2) St.carrier)) =
            (LinearMap.rTensor St.carrier
              (AddMonoidHom.toZModLinearMap 2 (frobeniusEquiv (GaloisField 2 2) 2).toAddEquiv.toAddMonoidHom)) ''
              (U₁ : Set _)

section G51Cert

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Quasithin.H13.A6 (g5G1 cA6)

private noncomputable def a6Mod (i : Fin 4) : FMod ↥(alternatingGroup (Fin 6)) where
  carrier := Fin (![1, 4, 4, 16] i) → ZMod 2
  ρ := CFSG.CharacterTheory.SteinbergBY.a6BinaryRep i

private noncomputable def stMod : FMod (Equiv.Perm (Fin 6)) where
  carrier := Fin 16 → ZMod 2
  ρ := CFSG.Quasithin.H13.A6.G52.Mrep 3

private theorem a6Mod_isIrred (i : Fin 4) : (a6Mod i).IsIrred :=
  CFSG.Quasithin.RonanG51.a6_irred i

private theorem a6Mod_card (i : Fin 4) :
    Nat.card (a6Mod i).carrier = 2 ^ (![1, 4, 4, 16] i) :=
  CFSG.Quasithin.RonanG51.card_D i

private theorem a6Mod_not_iso {i j : Fin 4} (h : i ≠ j) : ¬ (a6Mod i).Iso (a6Mod j) :=
  CFSG.Quasithin.RonanG51.a6_not_iso i j h

private theorem a6Mod_complete (N : FMod ↥(alternatingGroup (Fin 6))) (hN : N.IsIrred) :
    ∃ i, N.Iso (a6Mod i) := by
  obtain ⟨hnt, hS⟩ := hN
  haveI := hnt
  exact CFSG.Quasithin.RonanG51.a6_complete N.ρ hS

private theorem stMod_isSteinberg : IsSteinbergModule stMod :=
  ⟨CFSG.Quasithin.RonanG51.mrep_irred 3, (CFSG.Quasithin.RonanG51.card_D 3).trans (by decide),
    CFSG.Quasithin.RonanG52.projective_of_equiv_St
      (τ := stMod.ρ) (Representation.Equiv.refl CFSG.Quasithin.H13.A6.G52.St)⟩

theorem as_G_5_1 : G_5_1 := by
  intro T G₁ G₂ hyp
  obtain ⟨sylow, -, -, -, -, index₁, index₂, -, only⟩ := hyp
  obtain ⟨c, hcA, hc⟩ := CFSG.Quasithin.RonanG52.exists_conj_g5G1_cA6_iff sylow index₁ index₂ only
  set c' : ↥(alternatingGroup (Fin 6)) := ⟨c, hcA⟩ with hc'
  have hcoe : ∀ g : ↥(alternatingGroup (Fin 6)),
      ((c' * g * c'⁻¹ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) =
        c * (g : Equiv.Perm (Fin 6)) * c⁻¹ := fun g => rfl
  have hpt : ∀ (G : Subgroup (Equiv.Perm (Fin 6))) (X : Subgroup (Equiv.Perm (Fin 6))),
      (∀ g, g ∈ G ↔ c * g * c⁻¹ ∈ X) → ∀ i : Fin 4,
      (∃ v : (a6Mod i).carrier, v ≠ 0 ∧ ∀ g : ↥(alternatingGroup (Fin 6)),
        (g : Equiv.Perm (Fin 6)) ∈ X → (a6Mod i).ρ g v = v) →
      (a6Mod i).FixesPoint (inG G) := by
    intro G X hG i ⟨v, hv, hfix⟩
    exact CFSG.Quasithin.RonanG51.fixesPoint_conj (a6Mod i).ρ c' (inG G)
      {g | (g : Equiv.Perm (Fin 6)) ∈ X} (fun g => by
        show (g : Equiv.Perm (Fin 6)) ∈ G ↔ ((c' * g * c'⁻¹ : ↥(alternatingGroup (Fin 6))) :
          Equiv.Perm (Fin 6)) ∈ X
        rw [hcoe]
        exact hG _) v hv fun g hg => hfix g hg
  have hln : ∀ (G : Subgroup (Equiv.Perm (Fin 6))) (X : Subgroup (Equiv.Perm (Fin 6))),
      (∀ g, g ∈ G ↔ c * g * c⁻¹ ∈ X) → ∀ i : Fin 4,
      (∃ L : AddSubgroup (a6Mod i).carrier, Nat.card L = 4 ∧ ∀ g : ↥(alternatingGroup (Fin 6)),
        (g : Equiv.Perm (Fin 6)) ∈ X → ∀ l ∈ L, (a6Mod i).ρ g l ∈ L) →
      (a6Mod i).FixesLine (inG G) := by
    intro G X hG i ⟨L, hL, hst⟩
    exact CFSG.Quasithin.RonanG51.fixesLine_conj (a6Mod i).ρ c' (inG G)
      {g | (g : Equiv.Perm (Fin 6)) ∈ X} (fun g => by
        show (g : Equiv.Perm (Fin 6)) ∈ G ↔ ((c' * g * c'⁻¹ : ↥(alternatingGroup (Fin 6))) :
          Equiv.Perm (Fin 6)) ∈ X
        rw [hcoe]
        exact hG _) L hL fun g hg => hst g hg
  obtain ⟨i, j, hij, hpi, hli, hpj, hlj⟩ : ∃ i j : Fin 4, (i = 1 ∧ j = 2 ∨ i = 2 ∧ j = 1) ∧
      (a6Mod i).FixesPoint (inG G₁) ∧ (a6Mod i).FixesLine (inG G₂) ∧
      (a6Mod j).FixesPoint (inG G₂) ∧ (a6Mod j).FixesLine (inG G₁) := by
    rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨1, 2, Or.inl ⟨rfl, rfl⟩,
        hpt G₁ g5G1 h₁ 1 CFSG.Quasithin.RonanG51.a6_4a_fixesPoint,
        hln G₂ cA6 h₂ 1 CFSG.Quasithin.RonanG51.a6_4a_fixesLine,
        hpt G₂ cA6 h₂ 2 CFSG.Quasithin.RonanG51.a6_4b_fixesPoint,
        hln G₁ g5G1 h₁ 2 CFSG.Quasithin.RonanG51.a6_4b_fixesLine⟩
    · exact ⟨2, 1, Or.inr ⟨rfl, rfl⟩,
        hpt G₁ cA6 h₂ 2 CFSG.Quasithin.RonanG51.a6_4b_fixesPoint,
        hln G₂ g5G1 h₁ 2 CFSG.Quasithin.RonanG51.a6_4b_fixesLine,
        hpt G₂ g5G1 h₁ 1 CFSG.Quasithin.RonanG51.a6_4a_fixesPoint,
        hln G₁ cA6 h₂ 1 CFSG.Quasithin.RonanG51.a6_4a_fixesLine⟩
  have hdim : ![1, 4, 4, 16] i = 4 ∧ ![1, 4, 4, 16] j = 4 := by
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩
  have hi0 : (0 : Fin 4) ≠ i := by rcases hij with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hj0 : (0 : Fin 4) ≠ j := by rcases hij with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hi3 : i ≠ (3 : Fin 4) := by rcases hij with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hj3 : j ≠ (3 : Fin 4) := by rcases hij with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hij' : i ≠ j := by rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  refine ⟨a6Mod 0, a6Mod i, a6Mod j, a6Mod 3, ⟨a6Mod_isIrred 0,
    CFSG.Quasithin.RonanG51.a6_trivial, by simpa using a6Mod_card 0⟩,
    ⟨a6Mod_isIrred i, by rw [a6Mod_card, hdim.1]⟩, ⟨a6Mod_isIrred j, by rw [a6Mod_card, hdim.2]⟩,
    ⟨a6Mod_isIrred 3, by simpa using a6Mod_card 3⟩, a6Mod_not_iso hi0, a6Mod_not_iso hj0,
    a6Mod_not_iso (by decide), a6Mod_not_iso hij', a6Mod_not_iso hi3, a6Mod_not_iso hj3,
    fun N hN => ?_, ⟨hpi, hli⟩, ⟨hpj, hlj⟩, ?_⟩
  · obtain ⟨k, hk⟩ := a6Mod_complete N hN
    have hall : ∀ k : Fin 4, k = 0 ∨ k = i ∨ k = j ∨ k = 3 := by
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rcases hall k with h | h | h | h <;> rw [h] at hk
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
    · exact Or.inr (Or.inr (Or.inl hk))
    · exact Or.inr (Or.inr (Or.inr hk))
  · refine ⟨stMod, stMod_isSteinberg, ?_, ?_⟩
    · obtain ⟨f, hf⟩ := CFSG.Quasithin.RonanG51.a6_three_iso_mrep
      exact ⟨f, hf⟩
    · exact CFSG.Quasithin.RonanG51.f4_decomposition (V := stMod.carrier)
        (LinearEquiv.refl (ZMod 2) _) stMod.ρ (fun g v => rfl)

end G51Cert

@[expose] def G_5_2 : Prop :=
  ∀ T G₁ G₂ : Subgroup (Equiv.Perm (Fin 6)), HypG5 T G₁ G₂ →
    ∀ V : FMod (Equiv.Perm (Fin 6)), V.IsIrred →
      (V.restrict (alternatingGroup (Fin 6))).FixesLine (inG G₁) →
      (V.restrict (alternatingGroup (Fin 6))).FixesLine (inG G₂) →
      IsSteinbergModule V

section G52Cert

theorem as_G_5_2 : G_5_2 := by
  intro T G₁ G₂ hyp V hV hL₁ hL₂
  obtain ⟨hnt, hS⟩ := hV
  obtain ⟨L₁, h₁, hL₁⟩ := hL₁
  obtain ⟨L₂, h₂, hL₂⟩ := hL₂
  obtain ⟨sylow, le₁, le₂, T_le₁, T_le₂, index₁, index₂, ne, only⟩ := hyp
  have hτ : Representation.IsIrreducible V.ρ :=
    CFSG.Quasithin.RonanG51.isIrreducible_of_addSubgroup_bot_or_top V.ρ hS
  obtain ⟨hcard, hproj⟩ := CFSG.Quasithin.RonanG52.steinberg_of_fixesLines V.ρ hτ sylow le₁ le₂
    T_le₁ T_le₂ index₁ index₂ ne only L₁ L₂ h₁ h₂
    (fun g hg l hl => hL₁ ⟨g, le₁ hg⟩ hg l hl) (fun g hg l hl => hL₂ ⟨g, le₂ hg⟩ hg l hl)
  exact ⟨⟨hnt, hS⟩, hcard, hproj⟩

end G52Cert

@[expose] def G_5_3 : Prop :=
  ∀ T G₁ G₂ : Subgroup (Equiv.Perm (Fin 6)), HypG5 T G₁ G₂ →
    ∀ V₁ V₂ : FMod ↥(alternatingGroup (Fin 6)),
      (V₁.IsIrred ∧ Nat.card V₁.carrier = 2 ^ 4 ∧ V₁.FixesPoint (inG G₁) ∧
        V₁.FixesLine (inG G₂)) →
      (V₂.IsIrred ∧ Nat.card V₂.carrier = 2 ^ 4 ∧ V₂.FixesPoint (inG G₂) ∧
        V₂.FixesLine (inG G₁)) →
      ∀ B : LinearMap.BilinForm (ZMod 2) V₁.carrier,
        (∀ x, B x x = 0) → (∀ x, (∀ y, B x y = 0) → x = 0) →
        (∀ g x y, B (V₁.ρ g x) (V₁.ρ g y) = B x y) →
        (InvSub (permAct V₁) (permCore V₁) ∧ InvSub (permAct V₁) (permOnes V₁) ∧
          permCore V₁ ⊓ permOnes V₁ = ⊥ ∧ permCore V₁ ⊔ permOnes V₁ = permSpace V₁) ∧
        (jradPow (permAct V₁) 5 (permCore V₁) = ⊥ ∧
          ∀ n < 5, IsMaxInvSub (permAct V₁) (jradPow (permAct V₁) n (permCore V₁))
            (jradPow (permAct V₁) (n + 1) (permCore V₁))) ∧
        (jradPow (permAct V₁) 2 (permCore V₁) =
            AddSubgroup.closure {u | ∃ l ∈ singLines V₁ B, u = lineCompl V₁ l} ∧
          ∃ (C : FMod ↥(alternatingGroup (Fin 6)))
            (π : ↥(jradPow (permAct V₁) 0 (permCore V₁)) →+ C.carrier),
            Function.Surjective π ∧
            (∀ u, π u = 0 ↔ (u : V₁.carrier → ZMod 2) ∈ jradPow (permAct V₁) 2 (permCore V₁)) ∧
            (∀ (g : ↥(alternatingGroup (Fin 6))) (u u' : ↥(jradPow (permAct V₁) 0 (permCore V₁))),
              permAct V₁ g (u : V₁.carrier → ZMod 2) = (u' : V₁.carrier → ZMod 2) →
                π u' = C.ρ g (π u)) ∧
            C.IsFiveDimCover V₁) ∧
        ((jradPow (permAct V₁) 4 (permCore V₁) : Set (V₁.carrier → ZMod 2)) =
            {u | ∃ x : V₁.carrier, x ≠ 0 ∧ u = perpCompl V₁ B x} ∪ {0} ∧
          ∃ f : ↥(jradPow (permAct V₁) 4 (permCore V₁)) ≃+ V₁.carrier,
            ∀ (g : ↥(alternatingGroup (Fin 6))) (u u' : ↥(jradPow (permAct V₁) 4 (permCore V₁))),
              permAct V₁ g (u : V₁.carrier → ZMod 2) = (u' : V₁.carrier → ZMod 2) →
                f u' = V₁.ρ g (f u)) ∧
        (∃ (C : FMod ↥(alternatingGroup (Fin 6)))
            (π : ↥(jradPow (permAct V₁) 2 (permCore V₁)) →+ C.carrier),
            Function.Surjective π ∧
            (∀ u, π u = 0 ↔ (u : V₁.carrier → ZMod 2) ∈ jradPow (permAct V₁) 4 (permCore V₁)) ∧
            (∀ (g : ↥(alternatingGroup (Fin 6))) (u u' : ↥(jradPow (permAct V₁) 2 (permCore V₁))),
              permAct V₁ g (u : V₁.carrier → ZMod 2) = (u' : V₁.carrier → ZMod 2) →
                π u' = C.ρ g (π u)) ∧
            C.IsFiveDimCover V₂) ∧
        ∀ W : FMod ↥(alternatingGroup (Fin 6)),
          (∃ w : W.carrier, w ≠ 0 ∧ (∀ g ∈ inG G₁, W.ρ g w = w) ∧
            AddSubgroup.closure (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g w) = ⊤ ∧
            Nat.card ↥(AddSubgroup.closure
              (Set.range fun g : ↥(inG G₂) => W.ρ (g : ↥(alternatingGroup (Fin 6))) w)) = 4) →
          W.Iso V₁ ∨ W.IsFiveDimCover V₁

section G53Cert

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem as_G_5_3 : G_5_3 := by
  intro T G₁ G₂ hyp V₁ V₂ h₁ h₂ B hB1 hB2 hB3
  obtain ⟨sylow, -, -, -, -, index₁, index₂, -, only⟩ := hyp
  obtain ⟨c, hcA, hc⟩ := CFSG.Quasithin.RonanG52.exists_conj_g5G1_cA6_iff sylow index₁ index₂ only
  let toMd : ∀ {X : Type} [Group X], FMod X → CFSG.Quasithin.ShultG53.Md X :=
    fun V => ⟨V.carrier, V.ρ⟩
  let ofMd : ∀ {X : Type} [Group X], CFSG.Quasithin.ShultG53.Md X → FMod X :=
    fun V => ⟨V.carrier, V.ρ⟩
  have bridge : ∀ (U V : CFSG.Quasithin.ShultG53.Md ↥(alternatingGroup (Fin 6))),
      U.IsFiveDimCover V → (ofMd U).IsFiveDimCover (ofMd V) := by
    intro U V h
    obtain ⟨⟨hcov, huniv⟩, hcard⟩ := h
    refine ⟨⟨hcov, fun W hW => ?_⟩, hcard⟩
    obtain ⟨π, hπ⟩ := huniv (toMd W) hW
    exact ⟨π, hπ⟩
  have hm := CFSG.Quasithin.ShultG53.g53_main G₁ G₂ c hcA hc (toMd V₁) (toMd V₂) h₁ h₂ B hB1 hB2
    hB3
  obtain ⟨p1, p2, ⟨p31, C3, π3, hs3, hk3, he3, hc3⟩, p4, ⟨C5, π5, hs5, hk5, he5, hc5⟩, p6⟩ := hm
  refine ⟨p1, p2, ⟨p31, ofMd C3, π3, hs3, hk3, he3, bridge _ _ hc3⟩, p4,
    ⟨ofMd C5, π5, hs5, hk5, he5, bridge _ _ hc5⟩, ?_⟩
  intro W hW
  rcases p6 (toMd W) hW with h | h
  · exact Or.inl h
  · exact Or.inr (bridge _ _ h)

end G53Cert

end CFSG.ASVolI

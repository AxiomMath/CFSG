module

public import CFSG.Quasithin.Background.G10Basic
import CFSG.Quasithin.Background.G10Fourteen
import CFSG.Quasithin.Background.G105Core
import CFSG.Quasithin.Background.RonanG1016Final
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G10Stmts
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsSemisimpleFor (K : Subgroup (GLV V)) : Prop :=
  ∀ U : Submodule (ZMod 2) V, Invariant K U → ∃ U' : Submodule (ZMod 2) V, Invariant K U' ∧ IsCompl U U'

@[expose] def InducesIsometries (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V)
    (f : LinearMap.BilinForm (ZMod 2) I) : Prop :=
  (∀ k ∈ K, ∀ x y x' y' : I, k (x : V) = (x' : V) → k (y : V) = (y' : V) → f x' y' = f x y) ∧
    ∀ g : I ≃ₗ[ZMod 2] I, (∀ x y, f (g x) (g y) = f x y) → ∃ k ∈ K, ∀ i : I, k (i : V) = ((g i : I) : V)

@[expose] def InducesSp (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∃ f : LinearMap.BilinForm (ZMod 2) I, (∀ x, f x x = 0) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
    InducesIsometries K I f

@[expose] def InducesOrth (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∃ q : I → ZMod 2, (∀ (c : ZMod 2) x, q (c • x) = c * c * q x) ∧
    (∃ B' : LinearMap.BilinForm (ZMod 2) I, (∀ x y, q (x + y) = q x + q y + B' x y) ∧
      (∀ x, (∀ y, B' x y = 0) → x = 0)) ∧
    (∀ k ∈ K, ∀ x x' : I, k (x : V) = (x' : V) → q x' = q x) ∧
    ∀ g : I ≃ₗ[ZMod 2] I, (∀ x, q (g x) = q x) → ∃ k ∈ K, ∀ i : I, k (i : V) = ((g i : I) : V)

@[expose] def IsSymNaturalSub (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (n : ℕ) : Prop :=
  ∃ (φ : ↥K ≃* Equiv.Perm (Fin n)) (β : ↥(permCore n) →ₗ[ZMod 2] ↥I),
    Function.Surjective β ∧
    (∀ u : ↥(permCore n), β u = 0 ↔ (u = 0 ∨ (Even n ∧ ∀ i, (u : Fin n → ZMod 2) i = 1))) ∧
    ∀ (γ : ↥K) (u u' : ↥(permCore n)),
      (u' : Fin n → ZMod 2) = permAct (φ γ) (u : Fin n → ZMod 2) →
        ((β u' : I) : V) = (γ : GLV V) ((β u : I) : V)

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG
open scoped commutatorElement

@[expose] def G_10_2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G101Hyp B Γ v₁ W X X₀ →
      Module.finrank (ZMod 2) V ≤ 2 * (Nat.log 2 (X₀.relIndex X) + 1) ∧
        2 * (Nat.log 2 (X₀.relIndex X) + 1) ≤ 2 * (CFSG.Open.pRank 2 Γ + 1)

theorem as_G_10_2 : G_10_2 := by
  intro V _ _ _ B Γ v₁ W X X₀ h
  exact ⟨h.dim_le_two_mul, Nat.mul_le_mul_left 2 (Nat.succ_le_succ h.log_relIndex_le_pRank)⟩

@[expose] def G_10_3 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G101Hyp B Γ v₁ W X X₀ →
      (∀ U : Submodule (ZMod 2) V, U ≠ ⊥ → Invariant Γ U → TwoReducedOn Γ U) ∧ pCoreOf 2 Γ = ⊥

theorem as_G_10_3 : G_10_3 := CFSG.Quasithin.G11.g10_3

@[expose] def G_10_4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G101Hyp B Γ v₁ W X X₀ →
      ∀ H : Subgroup (GLV V), H ≤ Γ → (∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) → H ≠ ⊥ →
      ∀ U : Submodule (ZMod 2) V, U ≠ ⊥ → U ≠ ⊤ → IsIrr (H ⊔ X) U →
        (H = Γ ∨ (v₁ ∉ U ∧ commSpace X U ≠ ⊥)) →
          Module.finrank (ZMod 2) V = 4 ∧ Module.finrank (ZMod 2) U = 2 ∧ Group.IsSolvable ↥Γ

theorem as_G_10_4 : G_10_4 :=
  CFSG.Quasithin.g10_4 CFSG.Quasithin.G11.g10_3 CFSG.Quasithin.G11.SzG11S.b49

@[expose] def G_10_5 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G101Hyp B Γ v₁ W X X₀ →
      IsIrr Γ ⊤ ∨
        (Module.finrank (ZMod 2) V = 4 ∧
          ((Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
              Γ = Subgroup.closure {g | g ∈ Γ ∧ ∃ c : V, InducesTransvection g ⊤ c}) ∨
            (IsElemAbelian 3 (pCoreOf 3 Γ) ∧ Nat.card ↥(pCoreOf 3 Γ) = 9 ∧
              ∃ t ∈ Γ, t * t = 1 ∧ t ≠ 1 ∧ Γ = pCoreOf 3 Γ ⊔ Subgroup.zpowers t ∧
                ∀ x ∈ pCoreOf 3 Γ, t * x * t⁻¹ = x⁻¹)))

theorem as_G_10_5 : G_10_5 := by
  intro V _ _ _ B Γ v₁ W X X₀ hG
  by_cases hirr : IsIrr Γ ⊤
  · exact Or.inl hirr
  right
  obtain ⟨U, hUirr, hUtop⟩ := CFSG.Quasithin.G105.exists_irr_of_not_isIrr hG hirr
  have hU0 : U ≠ ⊥ := hUirr.ne_bot
  have hΓ0 : Γ ≠ ⊥ := CFSG.Quasithin.G105.ne_bot_of_proper hG hU0 hUtop
  have hH : Γ ⊔ X = Γ := sup_eq_left.2 hG.X_le
  obtain ⟨hV4, hU2, -⟩ := as_G_10_4 V B Γ v₁ W X X₀ hG Γ le_rfl
    (fun γ hγ h hh => Γ.mul_mem (Γ.mul_mem hγ hh) (Γ.inv_mem hγ)) hΓ0 U hU0 hUtop
    (by rw [hH]; exact hUirr) (Or.inl rfl)
  exact ⟨hV4, CFSG.Quasithin.G105.g105_core hG hUirr hU2 hV4
    (as_G_10_3 V B Γ v₁ W X X₀ hG).2⟩

@[expose] def G_10_7 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    IsIrr Γ ⊤ → IsComponentOf L Γ → (∃ x ∈ X, ∃ l ∈ L, x * l ≠ l * x) →
    G101Hyp B Γ v₁ W X X₀ →
      fixedSpace (normalClosure Γ L) = ⊥ ∧ commSpace (normalClosure Γ L) ⊤ = ⊤ ∧
      ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I →
        (IsIrr (normalClosure Γ L) I ∧
          (∀ γ ∈ Γ, conjSub γ I = I ∨ conjSub γ I ⊓ I = ⊥) ∧ IsSemisimpleFor (normalClosure Γ L)) ∧
        (Isotropic B I ∨ NondegOn B I) ∧
        (∃ (k : ℕ) (Is : Fin k → Submodule (ZMod 2) V), (∃ h : 0 < k, Is ⟨0, h⟩ = I) ∧
          (∀ i, IrrPlus (normalClosure Γ L) (Is i)) ∧ iSupIndep Is ∧ (⨆ i, Is i) = ⊤ ∧
          ((NondegOn B I ∧ B.orthogonal I = ⨆ i : {i : Fin k // 0 < i.val}, Is i) ∨
            (Isotropic B I ∧ ∃ h : 1 < k, IsDualOf (normalClosure Γ L) I (Is ⟨1, h⟩) ∧
              NondegOn B (I ⊔ Is ⟨1, h⟩) ∧
              B.orthogonal (I ⊔ Is ⟨1, h⟩) = ⨆ i : {i : Fin k // 2 ≤ i.val}, Is i))) ∧
        2 < Module.finrank (ZMod 2) I

section G107

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem g107_fixed {Γ L : Subgroup (GLV V)} (hirr : IsIrr Γ ⊤)
    (hl : ∃ l ∈ L, l ≠ 1) : fixedSpace (normalClosure Γ L) = ⊥ := by
  have hinv : Invariant Γ (fixedSpace (normalClosure Γ L)) :=
    invariant_fixedSpace (normalClosure_normal Γ L)
  rcases hirr.eq_bot_or_eq hinv le_top with h | h
  · exact h
  · exfalso
    obtain ⟨l, hlL, hl1⟩ := hl
    exact hl1 (fixedSpace_eq_top_iff.1 h l (le_normalClosure Γ L hlL))

private theorem g107_comm {Γ L : Subgroup (GLV V)} (hirr : IsIrr Γ ⊤)
    (hfix : fixedSpace (normalClosure Γ L) = ⊥) : commSpace (normalClosure Γ L) ⊤ = ⊤ := by
  have hinv : Invariant Γ (commSpace (normalClosure Γ L) ⊤) :=
    invariant_commSpace (normalClosure_normal Γ L) (invariant_top Γ)
  rcases hirr.eq_bot_or_eq hinv le_top with h | h
  · exfalso
    have hfix' : fixedSpace (normalClosure Γ L) = ⊤ := by
      rw [eq_top_iff]
      intro v _ k hk
      exact (commSpace_eq_bot_iff.1 h) k hk v Submodule.mem_top
    exact hirr.ne_bot (hfix'.symm.trans hfix)
  · exact h

private theorem g107_sSup {Γ L : Subgroup (GLV V)} (hirr : IsIrr Γ ⊤) :
    sSup {J : Submodule (ZMod 2) V | IsIrr (normalClosure Γ L) J} = ⊤ := by
  obtain ⟨J, -, hJ⟩ := exists_isIrr_le (invariant_top (normalClosure Γ L)) hirr.ne_bot
  rw [eq_top_iff, ← iSup_conjSub_eq_top hirr hJ.ne_bot]
  refine iSup_le fun γ => le_sSup ?_
  exact hJ.conj_of_normal (normalClosure_normal Γ L) γ.2

private theorem g107_isotropic_or_nondeg {B : LinearMap.BilinForm (ZMod 2) V}
    {H : Subgroup (GLV V)} (hHiso : ∀ k ∈ H, ∀ v w, B (k v) (k w) = B v w)
    (hrefl : B.IsRefl) {I : Submodule (ZMod 2) V} (hI : IsIrr H I) :
    Isotropic B I ∨ NondegOn B I := by
  have hinv : Invariant H (I ⊓ B.orthogonal I) := hI.1.inf (hI.1.orthogonal hHiso)
  rcases hI.eq_bot_or_eq hinv (inf_le_left : I ⊓ B.orthogonal I ≤ I) with h | h
  · right
    intro u hu hw
    have hu' : u ∈ I ⊓ B.orthogonal I := by
      refine Submodule.mem_inf.2 ⟨hu, ?_⟩
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      exact hrefl _ _ (hw n hn)
    rw [h] at hu'
    exact (Submodule.mem_bot _).1 hu'
  · left
    intro u hu u' hu'
    have : u' ∈ I ⊓ B.orthogonal I := by
      rw [h]
      exact hu'
    exact (LinearMap.BilinForm.mem_orthogonal_iff.1 (Submodule.mem_inf.1 this).2) u hu

private theorem g107_compl_orthogonal {B : LinearMap.BilinForm (ZMod 2) V}
    (hrefl : B.IsRefl) {I : Submodule (ZMod 2) V} (hI : NondegOn B I) :
    IsCompl I (B.orthogonal I) := by
  refine LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl ?_
  have h1 : ∀ x : I, (∀ y : I, (B.restrict I) x y = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    exact hI x x.2 fun w hw => hx ⟨w, hw⟩
  refine ⟨fun x hx => h1 x hx, fun x hx => h1 x fun y => ?_⟩
  have := hx y
  exact hrefl _ _ this

private theorem g107_disjoint_of_iso {B : LinearMap.BilinForm (ZMod 2) V}
    {H : Subgroup (GLV V)} {I I₂ : Submodule (ZMod 2) V} (hI : IsIrr H I) (hI₂ : IsIrr H I₂)
    (hiso : Isotropic B I) (hnd : NondegOn B (I ⊔ I₂)) : Disjoint I I₂ := by
  rw [disjoint_iff]
  rcases hI.eq_bot_or_eq (hI.1.inf hI₂.1) inf_le_left with h | h
  · exact h
  · exfalso
    have hle : I ≤ I₂ := inf_eq_left.1 h
    have heq : I = I₂ := by
      rcases hI₂.eq_bot_or_eq hI.1 hle with h0 | h0
      · exact absurd h0 hI.ne_bot
      · exact h0
    have hSI : I ⊔ I₂ = I := sup_eq_left.2 (le_of_eq heq.symm)
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI.ne_bot
    apply hu0
    apply hnd u (Submodule.mem_sup_left hu)
    intro w hw
    rw [hSI] at hw
    exact hiso u hu w hw

private theorem g107_disjoint_sup_left {x A R S : Submodule (ZMod 2) V}
    (hA : Disjoint A S) (hx : x ≤ S) (hR : R ≤ S) (hxR : Disjoint x R) :
    Disjoint x (A ⊔ R) := by
  rw [Submodule.disjoint_def]
  intro z hzx hzAR
  obtain ⟨a, ha, r, hr, hsum⟩ := Submodule.mem_sup.1 hzAR
  have haS : a ∈ S := by
    have h2 : a = z - r := by
      rw [← hsum]
      abel
    rw [h2]
    exact S.sub_mem (hx hzx) (hR hr)
  have ha0 : a = 0 := (Submodule.disjoint_def.1 hA) a ha haS
  have hz : z = r := by
    rw [← hsum, ha0, zero_add]
  have hrx : r ∈ x := hz ▸ hzx
  have hr0 : r = 0 := (Submodule.disjoint_def.1 hxR) r hrx hr
  rw [hz, hr0]

private theorem g107_disjoint_sup_right {x A R S : Submodule (ZMod 2) V}
    (hS : Disjoint S R) (hx : x ≤ S) (hA : A ≤ S) (hxA : Disjoint x A) :
    Disjoint x (A ⊔ R) := by
  rw [Submodule.disjoint_def]
  intro z hzx hzAR
  obtain ⟨a, ha, r, hr, hsum⟩ := Submodule.mem_sup.1 hzAR
  have hrS : r ∈ S := by
    have h2 : r = z - a := by
      rw [← hsum]
      abel
    rw [h2]
    exact S.sub_mem (hx hzx) (hA ha)
  have hr0 : r = 0 := (Submodule.disjoint_def.1 hS) r hrS hr
  have hza : z = a := by
    rw [← hsum, hr0, add_zero]
  have hax : a ∈ x := hza ▸ hzx
  have ha0 : a = 0 := (Submodule.disjoint_def.1 hxA) a hax ha
  rw [hza, ha0]

private theorem g107_iSupIndep_cons {m : ℕ} {A : Submodule (ZMod 2) V}
    {F : Fin m → Submodule (ZMod 2) V} (hF : iSupIndep F) (hA : Disjoint A (⨆ i, F i)) :
    iSupIndep (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) := by
  rw [iSupIndep_def]
  intro i
  induction i using Fin.cases with
  | zero =>
    rw [Fin.cons_zero]
    refine Disjoint.mono_right ?_ hA
    refine iSup_le fun j => iSup_le fun hj => ?_
    induction j using Fin.cases with
    | zero => exact absurd rfl hj
    | succ l =>
      rw [Fin.cons_succ]
      exact le_iSup F l
  | succ k =>
    rw [Fin.cons_succ]
    have hsub : (⨆ j, ⨆ (_ : j ≠ k.succ), (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) j)
        ≤ A ⊔ ⨆ l, ⨆ (_ : l ≠ k), F l := by
      refine iSup_le fun j => iSup_le fun hj => ?_
      induction j using Fin.cases with
      | zero =>
        rw [Fin.cons_zero]
        exact le_sup_left
      | succ l =>
        rw [Fin.cons_succ]
        have hlk : l ≠ k := fun h => hj (by rw [h])
        exact le_sup_of_le_right (le_iSup₂ (f := fun (l' : Fin m) (_ : l' ≠ k) => F l') l hlk)
    have hR : (⨆ l, ⨆ (_ : l ≠ k), F l) ≤ ⨆ i, F i := iSup₂_le fun l _ => le_iSup F l
    exact Disjoint.mono_right hsub
      (g107_disjoint_sup_left hA (le_iSup F k) hR (iSupIndep_def.1 hF k))

private theorem g107_iSup_cons {m : ℕ} (A : Submodule (ZMod 2) V)
    (F : Fin m → Submodule (ZMod 2) V) :
    (⨆ i, (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) i) = A ⊔ ⨆ i, F i := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    induction i using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      exact le_sup_left
    | succ k =>
      rw [Fin.cons_succ]
      exact le_sup_of_le_right (le_iSup F k)
  · refine sup_le ?_ ?_
    · have h0 : (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) 0 ≤
          ⨆ i, (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) i := le_iSup _ 0
      rw [Fin.cons_zero] at h0
      exact h0
    · refine iSup_le fun k => ?_
      have hk : (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) k.succ ≤
          ⨆ i, (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) i := le_iSup _ k.succ
      rw [Fin.cons_succ] at hk
      exact hk

private theorem g107_subtype_one {m : ℕ} (A : Submodule (ZMod 2) V)
    (F : Fin m → Submodule (ZMod 2) V) :
    (⨆ i : {i : Fin (m + 1) // 0 < i.val},
        (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) i) = ⨆ j, F j := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rcases i with ⟨i, hi⟩
    dsimp only
    induction i using Fin.cases with
    | zero => simp at hi
    | succ k =>
      rw [Fin.cons_succ]
      exact le_iSup F k
  · refine iSup_le fun j => ?_
    have hj : (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) j.succ ≤
        ⨆ i : {i : Fin (m + 1) // 0 < i.val},
          (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) i :=
      le_iSup (fun i : {i : Fin (m + 1) // 0 < i.val} =>
        (Fin.cons A F : Fin (m + 1) → Submodule (ZMod 2) V) i) ⟨j.succ, by simp⟩
    rw [Fin.cons_succ] at hj
    exact hj

private theorem g107_subtype_two {m : ℕ} (A B' : Submodule (ZMod 2) V)
    (F : Fin m → Submodule (ZMod 2) V) :
    (⨆ i : {i : Fin (m + 2) // 2 ≤ i.val},
        (Fin.cons A (Fin.cons B' F : Fin (m + 1) → Submodule (ZMod 2) V) :
          Fin (m + 2) → Submodule (ZMod 2) V) i) = ⨆ j, F j := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rcases i with ⟨i, hi⟩
    dsimp only
    induction i using Fin.cases with
    | zero => simp at hi
    | succ k =>
      induction k using Fin.cases with
      | zero => simp at hi
      | succ l =>
        rw [Fin.cons_succ, Fin.cons_succ]
        exact le_iSup F l
  · refine iSup_le fun j => ?_
    have hj : (Fin.cons A (Fin.cons B' F : Fin (m + 1) → Submodule (ZMod 2) V) :
        Fin (m + 2) → Submodule (ZMod 2) V) j.succ.succ ≤
        ⨆ i : {i : Fin (m + 2) // 2 ≤ i.val},
          (Fin.cons A (Fin.cons B' F : Fin (m + 1) → Submodule (ZMod 2) V) :
            Fin (m + 2) → Submodule (ZMod 2) V) i :=
      le_iSup (fun i : {i : Fin (m + 2) // 2 ≤ i.val} =>
        (Fin.cons A (Fin.cons B' F : Fin (m + 1) → Submodule (ZMod 2) V) :
          Fin (m + 2) → Submodule (ZMod 2) V) i) ⟨j.succ.succ, by simp⟩
    rw [Fin.cons_succ, Fin.cons_succ] at hj
    exact hj

private theorem g107_decomp {H : Subgroup (GLV V)}
    (hsup : sSup {J : Submodule (ZMod 2) V | IsIrr H J} = ⊤) :
    ∀ (n : ℕ) (P : Submodule (ZMod 2) V), Module.finrank (ZMod 2) P ≤ n → Invariant H P →
      ∃ (m : ℕ) (J : Fin m → Submodule (ZMod 2) V), (∀ j, IsIrr H (J j)) ∧ iSupIndep J ∧
        ⨆ j, J j = P := by
  intro n
  induction n with
  | zero =>
    intro P hP _
    have hP0 : P = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hP)
    exact ⟨0, fun j => j.elim0, fun j => j.elim0, iSupIndep_subsingleton _, by simp [hP0]⟩
  | succ n ih =>
    intro P hP hPinv
    by_cases hP0 : P = ⊥
    · exact ⟨0, fun j => j.elim0, fun j => j.elim0, iSupIndep_subsingleton _, by simp [hP0]⟩
    obtain ⟨J₀, hJ₀P, hJ₀⟩ := exists_isIrr_le hPinv hP0
    obtain ⟨C, hCinv, hCcompl⟩ := exists_invariant_compl hsup hJ₀.1
    have hsum : J₀ ⊔ (P ⊓ C) = P := by
      have h := sup_inf_assoc_of_le C hJ₀P
      rw [hCcompl.sup_eq_top, top_inf_eq] at h
      rw [inf_comm]
      exact h.symm
    have hJC : J₀ ⊓ (P ⊓ C) = ⊥ :=
      disjoint_iff.1 (Disjoint.mono_right inf_le_right hCcompl.disjoint)
    have hlt : P ⊓ C < P := by
      refine lt_of_le_of_ne inf_le_left (fun h => ?_)
      rw [h, inf_eq_left.2 hJ₀P] at hJC
      exact hJ₀.ne_bot hJC
    have hfin := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨m, K, hKirr, hKind, hKsup⟩ := ih (P ⊓ C) (by omega) (hPinv.inf hCinv)
    refine ⟨m + 1, (Fin.cons J₀ K : Fin (m + 1) → Submodule (ZMod 2) V), ?_, ?_, ?_⟩
    · intro j
      induction j using Fin.cases with
      | zero =>
        rw [Fin.cons_zero]
        exact hJ₀
      | succ l =>
        rw [Fin.cons_succ]
        exact hKirr l
    · apply g107_iSupIndep_cons hKind
      rw [hKsup]
      exact disjoint_iff.2 hJC
    · rw [g107_iSup_cons, hKsup, hsum]

private theorem g107_part3_nondeg {H : Subgroup (GLV V)} {B : LinearMap.BilinForm (ZMod 2) V}
    {I : Submodule (ZMod 2) V} (hfix : fixedSpace H = ⊥) (hI : IrrPlus H I)
    (hsup : sSup {J : Submodule (ZMod 2) V | IsIrr H J} = ⊤)
    (hcompl : IsCompl I (B.orthogonal I)) (hQinv : Invariant H (B.orthogonal I)) :
    ∃ (k : ℕ) (Is : Fin k → Submodule (ZMod 2) V), (∃ h : 0 < k, Is ⟨0, h⟩ = I) ∧
      (∀ i, IrrPlus H (Is i)) ∧ iSupIndep Is ∧ (⨆ i, Is i) = ⊤ ∧
      B.orthogonal I = ⨆ i : {i : Fin k // 0 < i.val}, Is i := by
  obtain ⟨m, J, hJirr, hJind, hJsup⟩ := g107_decomp hsup _ (B.orthogonal I) le_rfl hQinv
  have hirrAll : ∀ i, IrrPlus H ((Fin.cons I J : Fin (m + 1) → Submodule (ZMod 2) V) i) := by
    intro i
    induction i using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      exact hI
    | succ j =>
      rw [Fin.cons_succ]
      exact (hJirr j).irrPlus hfix
  refine ⟨m + 1, (Fin.cons I J : Fin (m + 1) → Submodule (ZMod 2) V), ⟨Nat.succ_pos _, rfl⟩,
    hirrAll, ?_, ?_, ?_⟩
  · apply g107_iSupIndep_cons hJind
    rw [hJsup]
    exact hcompl.disjoint
  · rw [g107_iSup_cons, hJsup]
    exact hcompl.sup_eq_top
  · rw [g107_subtype_one, hJsup]

private theorem g107_part3_iso {H : Subgroup (GLV V)} {B : LinearMap.BilinForm (ZMod 2) V}
    {I I₂ : Submodule (ZMod 2) V} (hfix : fixedSpace H = ⊥) (hI : IrrPlus H I)
    (hI₂ : IrrPlus H I₂) (hsup : sSup {J : Submodule (ZMod 2) V | IsIrr H J} = ⊤)
    (hdisj : Disjoint I I₂) (hcompl : IsCompl (I ⊔ I₂) (B.orthogonal (I ⊔ I₂)))
    (hQinv : Invariant H (B.orthogonal (I ⊔ I₂))) :
    ∃ (k : ℕ) (Is : Fin k → Submodule (ZMod 2) V), (∃ h : 0 < k, Is ⟨0, h⟩ = I) ∧
      (∀ i, IrrPlus H (Is i)) ∧ iSupIndep Is ∧ (⨆ i, Is i) = ⊤ ∧
      ∃ h : 1 < k, Is ⟨1, h⟩ = I₂ ∧
        B.orthogonal (I ⊔ I₂) = ⨆ i : {i : Fin k // 2 ≤ i.val}, Is i := by
  obtain ⟨m, J, hJirr, hJind, hJsup⟩ := g107_decomp hsup _ (B.orthogonal (I ⊔ I₂)) le_rfl hQinv
  have hF : iSupIndep (Fin.cons I₂ J : Fin (m + 1) → Submodule (ZMod 2) V) := by
    apply g107_iSupIndep_cons hJind
    rw [hJsup]
    exact Disjoint.mono_left le_sup_right hcompl.disjoint
  have hirrAll : ∀ i, IrrPlus H
      ((Fin.cons I (Fin.cons I₂ J : Fin (m + 1) → Submodule (ZMod 2) V) :
        Fin (m + 2) → Submodule (ZMod 2) V) i) := by
    intro i
    induction i using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      exact hI
    | succ j =>
      rw [Fin.cons_succ]
      induction j using Fin.cases with
      | zero =>
        rw [Fin.cons_zero]
        exact hI₂
      | succ l =>
        rw [Fin.cons_succ]
        exact (hJirr l).irrPlus hfix
  refine ⟨m + 2, (Fin.cons I (Fin.cons I₂ J : Fin (m + 1) → Submodule (ZMod 2) V) :
    Fin (m + 2) → Submodule (ZMod 2) V), ⟨Nat.succ_pos _, rfl⟩, hirrAll, ?_, ?_,
    ⟨by omega, rfl, ?_⟩⟩
  · apply g107_iSupIndep_cons hF
    rw [g107_iSup_cons, hJsup]
    exact g107_disjoint_sup_right hcompl.disjoint le_sup_left le_sup_right hdisj
  · rw [g107_iSup_cons, g107_iSup_cons, hJsup, ← sup_assoc]
    exact hcompl.sup_eq_top
  · rw [g107_subtype_two, hJsup]

private theorem g107_exists_dual {B : LinearMap.BilinForm (ZMod 2) V}
    {Γ L : Subgroup (GLV V)} {v₁ : V} {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}
    (hG : G101Hyp B Γ v₁ W X X₀)
    (hHiso : ∀ k ∈ normalClosure Γ L, ∀ v w, B (k v) (k w) = B v w)
    (hsup : sSup {J : Submodule (ZMod 2) V | IsIrr (normalClosure Γ L) J} = ⊤)
    (hfix : fixedSpace (normalClosure Γ L) = ⊥)
    {I : Submodule (ZMod 2) V} (hI : IsIrr (normalClosure Γ L) I) (hiso : Isotropic B I) :
    ∃ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J ∧
      IsDualOf (normalClosure Γ L) I J ∧ NondegOn B (I ⊔ J) := by
  set H := normalClosure Γ L with hH
  have hrefl : B.IsRefl := hG.isRefl
  have hnd : B.Nondegenerate := hG.nondegenerate'
  have hPinv : Invariant H (B.orthogonal I) := hI.1.orthogonal hHiso
  have hPP : B.orthogonal (B.orthogonal I) = I :=
    LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl I
  obtain ⟨J, hJinv, hcompl⟩ := exists_invariant_compl hsup hPinv
  have hdim1 : Module.finrank (ZMod 2) ↥(B.orthogonal I) =
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) ↥I :=
    LinearMap.BilinForm.finrank_orthogonal hnd I
  have hdim2 := Submodule.finrank_add_eq_of_isCompl hcompl
  have hdimI : Module.finrank (ZMod 2) ↥I ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le I
  have hdimJ : Module.finrank (ZMod 2) ↥J = Module.finrank (ZMod 2) ↥I := by omega
  have hJirr : IsIrr H J := by
    refine ⟨hJinv, bot_lt_iff_ne_bot.2 ?_, fun J' hJ' _ hJ'J => ?_⟩
    · intro hJ0
      apply hI.ne_bot
      rw [hJ0] at hdimJ
      simpa using hdimJ.symm
    · have hR : Invariant H (I ⊓ B.orthogonal J') := hI.1.inf (hJ'.orthogonal hHiso)
      rcases hI.eq_bot_or_eq hR inf_le_left with hR0 | hRI
      · right
        have hQ : B.orthogonal (B.orthogonal I ⊔ J') = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
          have hxP : x ∈ B.orthogonal (B.orthogonal I) := by
            rw [LinearMap.BilinForm.mem_orthogonal_iff]
            exact fun n hn => hx n (Submodule.mem_sup_left hn)
          have hxJ' : x ∈ B.orthogonal J' := by
            rw [LinearMap.BilinForm.mem_orthogonal_iff]
            exact fun n hn => hx n (Submodule.mem_sup_right hn)
          rw [hPP] at hxP
          have : x ∈ I ⊓ B.orthogonal J' := ⟨hxP, hxJ'⟩
          rw [hR0] at this
          exact this
        have hQtop : B.orthogonal I ⊔ J' = ⊤ := by
          apply Submodule.eq_top_of_finrank_eq
          have h1 := LinearMap.BilinForm.finrank_orthogonal hnd (B.orthogonal I ⊔ J')
          rw [hQ, finrank_bot] at h1
          have h2 : Module.finrank (ZMod 2) ↥(B.orthogonal I ⊔ J') ≤
              Module.finrank (ZMod 2) V :=
            Submodule.finrank_le _
          omega
        apply le_antisymm hJ'J
        intro x hx
        have hx' : x ∈ B.orthogonal I ⊔ J' := by
          rw [hQtop]
          exact Submodule.mem_top
        obtain ⟨p, hp, j', hj', rfl⟩ := Submodule.mem_sup.1 hx'
        have hp' : p ∈ B.orthogonal I ⊓ J := ⟨hp, by
          have : p = (p + j') - j' := by abel
          rw [this]
          exact J.sub_mem hx (hJ'J hj')⟩
        have := hcompl.disjoint.le_bot hp'
        rw [Submodule.mem_bot] at this
        rw [this, zero_add]
        exact hj'
      · left
        have hI' : I ≤ B.orthogonal J' := by
          rw [← hRI]
          exact inf_le_right
        rw [eq_bot_iff]
        intro j hj
        have hjP : j ∈ B.orthogonal I := by
          rw [LinearMap.BilinForm.mem_orthogonal_iff]
          intro n hn
          have := (LinearMap.BilinForm.mem_orthogonal_iff.1 (hI' hn)) j hj
          exact hrefl _ _ this
        have := hcompl.disjoint.le_bot ⟨hjP, hJ'J hj⟩
        exact this
  refine ⟨J, hJirr.irrPlus hfix, ?_, ?_⟩
  ·
    refine ⟨LinearMap.domRestrict₁₂ B J I, fun j hj => ?_, fun i hi => ?_, ?_⟩
    · have hjP : (j : V) ∈ B.orthogonal I := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro n hn
        exact hrefl _ _ (hj ⟨n, hn⟩)
      have := hcompl.disjoint.le_bot ⟨hjP, j.2⟩
      exact Subtype.ext this
    · apply Subtype.ext
      apply hG.nondegenerate
      intro v
      have hv : v ∈ B.orthogonal I ⊔ J := by
        rw [codisjoint_iff.1 hcompl.codisjoint]
        exact Submodule.mem_top
      obtain ⟨p, hp, j₀, hj₀, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      have h1 : B (i : V) p = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hp) i i.2
      have h2 : B (i : V) j₀ = 0 := hrefl _ _ (hi ⟨j₀, hj₀⟩)
      rw [h1, h2, add_zero]
    · intro k hk j j' i i' hj hi
      have : B (j' : V) (i' : V) = B (j : V) (i : V) := by
        rw [← hj, ← hi]
        exact hHiso k hk _ _
      exact this
  ·
    intro x hx hx0
    obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hx
    have hjP : j ∈ B.orthogonal I := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have h1 := hx0 n (Submodule.mem_sup_left hn)
      rw [map_add, LinearMap.add_apply, hiso i hi n hn, zero_add] at h1
      exact hrefl _ _ h1
    have hj0 : j = 0 := by
      have := hcompl.disjoint.le_bot ⟨hjP, hj⟩
      simpa using this
    subst hj0
    rw [add_zero]
    apply hG.nondegenerate
    intro v
    have hv : v ∈ B.orthogonal I ⊔ J := by
      rw [codisjoint_iff.1 hcompl.codisjoint]
      exact Submodule.mem_top
    obtain ⟨p, hp, j₀, hj₀, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    have h1 : B i p = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hp) i hi
    have h2 : B i j₀ = 0 := by
      have := hx0 j₀ (Submodule.mem_sup_right hj₀)
      simpa using this
    rw [h1, h2, add_zero]

private theorem g107_two_lt_finrank {Γ L : Subgroup (GLV V)} (hirr : IsIrr Γ ⊤)
    (hL : IsComponentOf L Γ) (hl : ∃ l ∈ L, l ≠ 1) {I : Submodule (ZMod 2) V}
    (hI : IsIrr (normalClosure Γ L) I) : 2 < Module.finrank (ZMod 2) I := by
  by_contra hle
  have hle' : Module.finrank (ZMod 2) I ≤ 2 := not_lt.1 hle
  have hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hL' : ∀ γ ∈ Γ, ∀ l ∈ L, ∀ u ∈ conjSub γ I, l u = u := by
    intro γ hγ
    have hJ : IsIrr (normalClosure Γ L) (conjSub γ I) :=
      hI.conj_of_normal (normalClosure_normal Γ L) hγ
    have hfin : Module.finrank (ZMod 2) ↥(conjSub γ I) ≤ 2 := by
      rw [finrank_conjSub]
      exact hle'
    have hLinv : Invariant L (conjSub γ I) := hJ.1.mono (le_normalClosure Γ L)
    have hsolv := isSolvable_linearEquiv_of_finrank_le_two (conjSub γ I) hfin
    let φ := restrictHom L (conjSub γ I) hLinv
    have hsub : Subsingleton φ.range := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
      exact Group.IsPerfect.not_isSolvable (G := φ.range) inferInstance
    intro l hl u hu
    have h1 : φ ⟨l, hl⟩ = 1 := by
      have := Subsingleton.elim (⟨φ ⟨l, hl⟩, ⟨_, rfl⟩⟩ : φ.range) ⟨1, φ.range.one_mem⟩
      exact congrArg Subtype.val this
    exact (restrictHom_eq_one_iff.1 h1) u hu
  have hfix : fixedSpace L = ⊤ := by
    rw [eq_top_iff, ← iSup_conjSub_eq_top hirr hI.ne_bot]
    refine iSup_le fun γ u hu l hl => hL' γ γ.2 l hl u hu
  obtain ⟨l, hlL, hl1⟩ := hl
  exact hl1 (fixedSpace_eq_top_iff.1 hfix l hlL)

end G107

theorem as_G_10_7 : G_10_7 := by
  intro V _ _ _ B Γ v₁ W X X₀ L hirr hcomp hnc hG
  have hl : ∃ l ∈ L, l ≠ 1 := by
    obtain ⟨x, -, l, hlL, h⟩ := hnc
    exact ⟨l, hlL, fun h1 => h (by rw [h1, mul_one, one_mul])⟩
  have hHΓ : normalClosure Γ L ≤ Γ := normalClosure_le hcomp.1
  have hHiso : ∀ k ∈ normalClosure Γ L, ∀ v w, B (k v) (k w) = B v w :=
    fun k hk => hG.isometry k (hHΓ hk)
  have hfix := g107_fixed hirr hl
  have hsup := g107_sSup (L := L) hirr
  refine ⟨hfix, g107_comm hirr hfix, fun I hI => ?_⟩
  have hIirr : IsIrr (normalClosure Γ L) I := IrrPlus.isIrr hfix hI
  have hdich := g107_isotropic_or_nondeg hHiso hG.isRefl hIirr
  refine ⟨⟨hIirr, fun γ hγ => hIirr.conj_eq_or_inf_eq_bot (normalClosure_normal Γ L) hγ, ?_⟩,
    hdich, ?_, g107_two_lt_finrank hirr hcomp hl hIirr⟩
  · intro U hU
    exact exists_invariant_compl hsup hU
  · rcases hdich with hiso | hnd
    · obtain ⟨I₂, hI₂, hdual, hnd2⟩ := g107_exists_dual hG hHiso hsup hfix hIirr hiso
      have hI₂irr : IsIrr (normalClosure Γ L) I₂ := IrrPlus.isIrr hfix hI₂
      have hdisj := g107_disjoint_of_iso hIirr hI₂irr hiso hnd2
      have hcompl := g107_compl_orthogonal hG.isRefl hnd2
      have hQinv : Invariant (normalClosure Γ L) (B.orthogonal (I ⊔ I₂)) :=
        Invariant.orthogonal hHiso (Invariant.sup hIirr.1 hI₂irr.1)
      obtain ⟨k, Is, h0, hirrs, hind, htop, h1, heq, hsubs⟩ :=
        g107_part3_iso hfix hI hI₂ hsup hdisj hcompl hQinv
      exact ⟨k, Is, h0, hirrs, hind, htop, Or.inr ⟨hiso, h1, by rw [heq]; exact hdual,
        by rw [heq]; exact hnd2, by rw [heq]; exact hsubs⟩⟩
    · have hcompl := g107_compl_orthogonal hG.isRefl hnd
      have hQinv : Invariant (normalClosure Γ L) (B.orthogonal I) :=
        Invariant.orthogonal hHiso hIirr.1
      obtain ⟨k, Is, h0, hirrs, hind, htop, hsubs⟩ :=
        g107_part3_nondeg hfix hI hsup hcompl hQinv
      exact ⟨k, Is, h0, hirrs, hind, htop, Or.inl ⟨hnd, hsubs⟩⟩

@[expose] def G_10_9 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G108Hyp B Γ v₁ W X X₀ L →
      ∀ T : Subgroup (GLV V),
        IsSylowTwoOf T (Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁) →
        X ≤ T → T ≤ Subgroup.normalizer (X : Set (GLV V)) →
          IsSylowTwoOf T Γ ∧ ⁅X, T ⊓ normalClosure Γ L⁆ ≤ X ⊓ normalClosure Γ L ∧
            IsElemAbelian 2 ⁅X, T ⊓ normalClosure Γ L⁆

private theorem as_G10_normalClosure_conj_mem {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Γ L : Subgroup (GLV V)) (γ : GLV V) (hγ : γ ∈ Γ) (k : GLV V) (hk : k ∈ normalClosure Γ L) :
    γ * k * γ⁻¹ ∈ normalClosure Γ L := by
  have hle : normalClosure Γ L ≤ (normalClosure Γ L).comap (MulAut.conj γ).toMonoidHom := by
    unfold normalClosure
    rw [Subgroup.closure_le]
    rintro x ⟨γ', hγ', l, hl, rfl⟩
    show γ * (γ' * l * γ'⁻¹) * γ⁻¹ ∈ Subgroup.closure _
    apply Subgroup.subset_closure
    simp only [Set.mem_setOf_eq]
    exact ⟨γ * γ', Γ.mul_mem hγ hγ', l, hl, by group⟩
  exact hle hk

theorem as_G_10_9 : G_10_9 := by
  intro V _ _ _ B Γ v₁ W X X₀ L h T hT hXT hTn
  obtain ⟨hTΓ, hgen⟩ := h.toG101Hyp.g10_9 (H := normalClosure Γ L) hT ⟨hXT, hTn⟩
    (fun γ hγ k hk => as_G10_normalClosure_conj_mem Γ L γ hγ k hk)
  have hcomm : ⁅X, T ⊓ normalClosure Γ L⁆ ≤ X ⊓ normalClosure Γ L := by
    rw [Subgroup.commutator_le]
    intro x hx t ht
    exact hgen x hx t ht
  exact ⟨hTΓ, hcomm,
    CFSG.Open.IsElemAbelian.mono h.toG101Hyp.X_isElemAbelian (hcomm.trans inf_le_left)⟩

@[expose] def G_10_10 : Prop := G1010Stmt

theorem as_G_10_10 : G_10_10 :=
  CFSG.Quasithin.G11.g10_10_of_g10_4 as_G_10_4

@[expose] def G_10_11 : Prop := G1011Stmt

theorem as_G_10_11 : G_10_11 := CFSG.Quasithin.G11.g10_11 as_G_10_10

@[expose] def G_10_12 : Prop := G1012Stmt

theorem as_G_10_12 : G_10_12 := CFSG.Quasithin.G11.g10_12 as_G_10_11

@[expose] def G_10_13 : Prop := G1013Stmt

theorem as_G_10_13 : G_10_13 :=
  CFSG.Quasithin.G11.g10_13 as_G_10_10 as_G_10_11

@[expose] def G_10_14 : Prop := G1014Stmt

theorem as_G_10_14 : G_10_14 := CFSG.Quasithin.G11.g10_14 as_G_10_12

@[expose] def G_10_15 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G108Hyp B Γ v₁ W X X₀ L →
      G1015Concl B Γ v₁ W X L

theorem as_G_10_15 : G_10_15 := by
  exact CFSG.Quasithin.RonanG1015.g10_15_final

@[expose] def G_10_16 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G108Hyp B Γ v₁ W X X₀ L →
      ∀ a ∈ X, a ≠ 1 → Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2 →
        (∃ h ∈ normalClosure Γ L, a * h ≠ h * a) ∧
        (∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I → conjSub a I = I) ∧
        (normalClosure Γ L ≤ normalClosure Γ (Subgroup.zpowers a) ∧
          ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I ↔
            IrrPlus (normalClosure Γ (Subgroup.zpowers a)) I) ∧
        (IsIrr (normalClosure Γ L) ⊤ ∨
          ∃ I₁ I₂ : Submodule (ZMod 2) V, IsCompl I₁ I₂ ∧
            Invariant (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ ∧
            Invariant (normalClosure Γ L ⊔ Subgroup.zpowers a) I₂ ∧
            (HIso (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ I₂ ∨
              (Module.finrank (ZMod 2) I₁ = 4 ∧ AutAll (normalClosure Γ L) I₁)) ∧
            (∃ c₁ : V, InducesTransvection a I₁ c₁) ∧ (∃ c₂ : V, InducesTransvection a I₂ c₂) ∧
            (InducesSp (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ ∨
              InducesOrth (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ ∨
              (∃ n : ℕ, IsSymNaturalSub (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ n) ∨
              (Module.finrank (ZMod 2) I₁ = 4 ∧ AutAll (normalClosure Γ L) I₁)))

theorem as_G_10_16 : G_10_16 := by
  exact CFSG.Quasithin.RonanG1016.g10_16_final

end CFSG.ASVolI

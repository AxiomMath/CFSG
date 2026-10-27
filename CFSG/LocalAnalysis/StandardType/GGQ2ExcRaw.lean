module

public import Certificates.Data.CFSGNative.ExcCensus.Tables
public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG.Assembly Module
open CFSG.StandardType (GGLabelIso)

noncomputable section

namespace ExcRaw

abbrev V (m : Fin 6) : Type := Fin (dim m) → ZMod 3

abbrev Root (m : Fin 6) : Type := Fin (nroots m)

@[expose] def F (m : Fin 6) (i : Root m) (k : Fin (dim m)) : ℤ :=
  ((tabF m).getD i []).getD k 0

@[expose] def H (m : Fin 6) (i : Root m) (k : Fin (dim m)) : ℤ :=
  ((tabH m).getD i []).getD k 0

@[expose] def root (m : Fin 6) (i : Root m) : Module.Dual (ZMod 3) (V m) where
  toFun v := ∑ k, (F m i k : ZMod 3) * v k
  map_add' v w := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem root_apply (m : Fin 6) (i : Root m) (v : V m) :
    root m i v = ∑ k, (F m i k : ZMod 3) * v k :=
  rfl

@[expose] def coroot (m : Fin 6) (i : Root m) : V m := fun k => (H m i k : ZMod 3)

@[expose] def pairing (m : Fin 6) (i j : Root m) : ℤ :=
  if m.val = 3 then
    ∑ k : Fin 6, ((tabF 2).getD i []).getD k 0 * ((tabH 2).getD j []).getD k 0
  else ∑ k, F m i k * H m j k

theorem pairing_eq (m : Fin 6) (i j : Root m) :
    root m i (coroot m j) = (pairing m i j : ZMod 3) := by
  by_cases hm : m.val = 3
  · have h3 : m = 3 := Fin.ext hm
    subst h3
    revert i j
    decide +kernel
  · rw [pairing, if_neg hm, root_apply]
    push_cast
    rfl

theorem pairing_self (m : Fin 6) (i : Root m) : pairing m i i = 2 := by
  revert i
  fin_cases m <;> decide +kernel

theorem root_coroot (m : Fin 6) (i : Root m) : root m i (coroot m i) = 2 := by
  rw [pairing_eq, pairing_self]
  norm_num

@[expose] def reflection (m : Fin 6) (i : Root m) : V m ≃ₗ[ZMod 3] V m :=
  Module.reflection (root_coroot m i)

theorem reflection_apply (m : Fin 6) (i : Root m) (v : V m) :
    reflection m i v = v - root m i v • coroot m i :=
  rfl

@[expose] def Adj (m : Fin 6) (i j : Root m) : Prop :=
  pairing m i j ≠ 0 ∨ pairing m j i ≠ 0

@[expose] def IsComp (m : Fin 6) (S : Root m → Prop) (c : Finset (Root m)) : Prop :=
  c.Nonempty ∧ (∀ i ∈ c, S i) ∧ (∀ i ∈ c, ∀ j, S j → Adj m i j → j ∈ c) ∧
    ∀ T ⊆ c, T.Nonempty → (∀ i ∈ T, ∀ j ∈ c, Adj m i j → j ∈ T) → T = c

@[expose] def Vanish (m : Fin 6) (U : Submodule (ZMod 3) (V m)) (i : Root m) : Prop :=
  ∀ u ∈ U, root m i u = 0

@[expose] def occurs (m : Fin 6) (U : Submodule (ZMod 3) (V m)) (c : Finset (Root m)) : Prop :=
  IsComp m (Vanish m U) c

@[expose] def cent (m : Fin 6) (c : Finset (Root m)) : Submodule (ZMod 3) (V m) :=
  ⨅ i ∈ c, LinearMap.ker (root m i)

@[expose] def inside (m : Fin 6) (c : Finset (Root m)) : Submodule (ZMod 3) (V m) :=
  Submodule.span (ZMod 3) (coroot m '' (c : Set (Root m)))

@[expose] def weyl (m : Fin 6) (c : Finset (Root m)) : Subgroup (V m ≃ₗ[ZMod 3] V m) :=
  Subgroup.closure (reflection m '' (c : Set (Root m)))

@[expose] def normalizerGroup (m : Fin 6) (c : Finset (Root m)) :
    Subgroup (V m ≃ₗ[ZMod 3] V m) :=
  if m.val = 0 ∧ c.card = 4 then
    weyl m c ⊓ (LinearEquiv.det : (V m ≃ₗ[ZMod 3] V m) →* (ZMod 3)ˣ).ker
  else weyl m c

@[expose] def ambientNormalizer (m : Fin 6) : Subgroup (V m ≃ₗ[ZMod 3] V m) :=
  Subgroup.closure (Set.range (reflection m))

@[expose] def orthCount (m : Fin 6) (c : Finset (Root m)) : ℕ :=
  ((c ×ˢ c).filter fun p => pairing m p.1 p.2 = 0).card

@[expose] def longCount (m : Fin 6) (c : Finset (Root m)) : ℕ :=
  (c.filter fun i => tabFix1.getD i.val false = true).card

@[expose] def labelF4 : ℕ → LargeEvenLabel
  | 1 => ⟨.A, 1, 1⟩
  | 3 => ⟨.twA, 2, 1⟩
  | 4 => ⟨.B2der, 0, 1⟩
  | 6 => ⟨.twA, 3, 1⟩
  | 9 => ⟨.C, 3, 1⟩
  | 12 => ⟨.D, 4, 1⟩
  | 16 => ⟨.C, 4, 1⟩
  | 24 => ⟨.F4, 0, 1⟩
  | _ => ⟨.A, 0, 0⟩

@[expose] def labelE6Rel : ℕ → ℕ → LargeEvenLabel
  | 1, 0 => ⟨.A, 1, 2⟩
  | 3, 0 => ⟨.A, 2, 2⟩
  | 1, 1 => ⟨.A, 1, 1⟩
  | 3, 3 => ⟨.twA, 2, 1⟩
  | 6, 6 => ⟨.twA, 3, 1⟩
  | 12, 12 => ⟨.D, 4, 1⟩
  | 4, 2 => ⟨.A, 3, 1⟩
  | 9, 3 => ⟨.A, 5, 1⟩
  | 9, 6 => ⟨.twD, 4, 1⟩
  | 16, 12 => ⟨.D, 5, 1⟩
  | 24, 12 => ⟨.E6, 0, 1⟩
  | _, _ => ⟨.A, 0, 0⟩

@[expose] def labelSL (n o : ℕ) : LargeEvenLabel :=
  match n with
  | 1 => ⟨.A, 1, 1⟩
  | 3 => ⟨.twA, 2, 1⟩
  | 6 => ⟨.twA, 3, 1⟩
  | 10 => ⟨.twA, 4, 1⟩
  | 15 => ⟨.twA, 5, 1⟩
  | 21 => ⟨.twA, 6, 1⟩
  | 28 => ⟨.twA, 7, 1⟩
  | 36 => if o = 756 then ⟨.twA, 8, 1⟩ else ⟨.twE6, 0, 1⟩
  | 12 => ⟨.D, 4, 1⟩
  | 20 => ⟨.twD, 5, 1⟩
  | 30 => ⟨.D, 6, 1⟩
  | 42 => ⟨.twD, 7, 1⟩
  | 56 => ⟨.D, 8, 1⟩
  | 63 => ⟨.E7, 0, 1⟩
  | 120 => ⟨.E8, 0, 1⟩
  | _ => ⟨.A, 0, 0⟩

@[expose] def label (m : Fin 6) (c : Finset (Root m)) : LargeEvenLabel :=
  match m.val with
  | 0 => labelF4 c.card
  | 1 => labelE6Rel c.card (longCount m c)
  | _ => labelSL c.card (orthCount m c)

@[expose] def admissible (m : Fin 6) (c : Finset (Root m)) : Prop :=
  (∃ U : Submodule (ZMod 3) (V m), occurs m U c) ∧ LargeEvenInLambda2 (label m c)

@[expose] def equivLabels (m : Fin 6) (c : Finset (Root m)) : Set LargeEvenLabel :=
  {lab | GGLabelIso (label m c) lab}

@[expose] def ambientLabel (m : Fin 6) : LargeEvenLabel :=
  match m.val with
  | 0 => ⟨.F4, 0, 1⟩
  | 1 => ⟨.E6, 0, 1⟩
  | 2 => ⟨.twE6, 0, 1⟩
  | 3 => ⟨.twE6, 0, 1⟩
  | 4 => ⟨.E7, 0, 1⟩
  | _ => ⟨.E8, 0, 1⟩

@[expose] def rootMap (m : Fin 6) (c : Finset (Root m)) : V m →ₗ[ZMod 3] (Root m → ZMod 3) :=
  LinearMap.pi fun i => if i ∈ c then root m i else 0

end ExcRaw

open ExcRaw in
@[expose] def excRaw (m : Fin 6) : RawFrameData where
  V := V m
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instFiniteDimensional := inferInstance
  Code := Finset (Root m)
  instFintype := inferInstance
  kind := .exceptional m
  ambientLabel := ambientLabel m
  admissible := admissible m
  occurs := occurs m
  label := label m
  cent := cent m
  inside := inside m
  normalizerGroup := normalizerGroup m
  ambientNormalizer := ambientNormalizer m
  absRank := fun _ => nroots m
  rootMap := rootMap m
  equivLabels := equivLabels m
  Root := Root m
  instRootFintype := inferInstance
  root := root m
  coroot := coroot m
  pairing := pairing m
  pairing_eq := pairing_eq m
  pairing_self := pairing_self m
  reflection := reflection m
  reflection_apply := reflection_apply m

end

end CFSG.StandardType.GGQ2Frame

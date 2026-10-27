module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusDefs
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenLine
public import TauCeti.LinearAlgebra.Matrix.Diagonal

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  Multiplicative

variable {F : Type} [Field F] {f m ε p : ℕ} {h : UnitaryFieldData 2 f F}

@[expose] def splitWeight (a : HypIndex m ε) (t : Fin m → ZMod p) : ZMod p :=
  match a with
  | .inl i => t i
  | .inr (.inl _) => 0
  | .inr (.inr i) => -t i

@[simp] theorem splitWeight_inl (i : Fin m) (t : Fin m → ZMod p) :
    splitWeight (.inl i : HypIndex m ε) t = t i := rfl

@[simp] theorem splitWeight_z (k : Fin ε) (t : Fin m → ZMod p) :
    splitWeight (.inr (.inl k) : HypIndex m ε) t = 0 := rfl

@[simp] theorem splitWeight_inr (i : Fin m) (t : Fin m → ZMod p) :
    splitWeight (.inr (.inr i) : HypIndex m ε) t = -t i := rfl

theorem splitEntries_eq_pow_val (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (t : Fin m → ZMod p) (a : HypIndex m ε) :
    splitEntries ζ t a = ζ ^ (splitWeight a t).val := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  rcases a with i | k | i
  · rfl
  · simp [splitEntries, splitWeight]
  · by_cases hi : t i = 0
    · simp [splitEntries, splitWeight, hi]
    · have hval : (-t i : ZMod p).val = p - (t i).val := by
        rw [ZMod.neg_val, if_neg hi]
      rw [splitEntries, splitWeight, hval]
      have hvpos : 0 < (t i).val := ZMod.val_pos.mpr hi
      have hvlt : (t i).val < p := ZMod.val_lt _
      have hmul : ζ ^ (p - (t i).val) * ζ ^ (t i).val = 1 := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt hvlt), hζ.pow_eq_one]
      exact inv_eq_of_mul_eq_one_left hmul

theorem splitEntries_eq_iff_splitWeight_eq (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (t : Fin m → ZMod p) (a b : HypIndex m ε) :
    splitEntries ζ t a = splitEntries ζ t b ↔ splitWeight a t = splitWeight b t := by
  have : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro h
    rw [splitEntries_eq_pow_val hp hζ, splitEntries_eq_pow_val hp hζ] at h
    exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h)
  · intro h
    rw [splitEntries_eq_pow_val hp hζ, splitEntries_eq_pow_val hp hζ, h]

theorem mem_centralizer_apply_eq_zero_of_splitWeight_ne
    (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E : Set (Multiplicative (Fin m → ZMod p))} {c : hypSU h m ε}
    (hc : c ∈ Subgroup.centralizer (τ '' E)) {a b : HypIndex m ε}
    (hab : ∃ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E ∧
      splitWeight a t ≠ splitWeight b t) :
    (((c : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) a b = 0 := by
  obtain ⟨t, ht, hne⟩ := hab
  have hxmem : τ (Multiplicative.ofAdd t) ∈ τ '' E := ⟨_, ht, rfl⟩
  have hcomm := (Subgroup.mem_centralizer_iff.mp hc) _ hxmem
  have hcD : (((c : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) * diagonal (splitEntries ζ t) =
      diagonal (splitEntries ζ t) *
        (((c : hypSU h m ε) : GL (HypIndex m ε) F) :
          Matrix (HypIndex m ε) (HypIndex m ε) F) := by
    have hmat := congrArg (fun y : hypSU h m ε =>
      (((y : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F))) hcomm
    simpa only [Subgroup.coe_mul, Units.val_mul, hτ t] using hmat.symm
  have hDne : splitEntries ζ t a ≠ splitEntries ζ t b := fun hEq =>
    hne ((splitEntries_eq_iff_splitWeight_eq hp hζ t a b).mp hEq)
  exact TauCeti.apply_eq_zero_of_commute_diagonal hcD.symm hDne

@[expose] def weightClass (E : Set (Multiplicative (Fin m → ZMod p))) (a : HypIndex m ε) :
    Set (HypIndex m ε) :=
  {b | ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → splitWeight b t = splitWeight a t}

@[expose] def weightClassPartner (E : Set (Multiplicative (Fin m → ZMod p))) (a : HypIndex m ε) :
    Set (HypIndex m ε) :=
  {b | ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E →
    splitWeight b t = -splitWeight a t}

@[expose] def IsWeightClassUnion (E : Set (Multiplicative (Fin m → ZMod p))) (T : Set (HypIndex m ε)) :
    Prop :=
  ∀ a b : HypIndex m ε, (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E →
    splitWeight a t = splitWeight b t) → (a ∈ T ↔ b ∈ T)

theorem isWeightClassUnion_weightClass_union_partner
    (E : Set (Multiplicative (Fin m → ZMod p))) (a : HypIndex m ε) :
    IsWeightClassUnion E (weightClass E a ∪ weightClassPartner E a) := by
  intro c d hcd
  have h1 : c ∈ weightClass E a ↔ d ∈ weightClass E a := by
    constructor
    · intro hc t ht
      rw [← hcd t ht]
      exact hc t ht
    · intro hd t ht
      rw [hcd t ht]
      exact hd t ht
  have h2 : c ∈ weightClassPartner E a ↔ d ∈ weightClassPartner E a := by
    constructor
    · intro hc t ht
      rw [← hcd t ht]
      exact hc t ht
    · intro hd t ht
      rw [hcd t ht]
      exact hd t ht
  rw [Set.mem_union, Set.mem_union, h1, h2]

theorem exists_splitWeight_ne_of_isWeightClassUnion
    (E : Set (Multiplicative (Fin m → ZMod p))) {T : Set (HypIndex m ε)}
    (hT : IsWeightClassUnion E T) {a b : HypIndex m ε} (ha : a ∈ T) (hb : b ∉ T) :
    ∃ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E ∧ splitWeight a t ≠ splitWeight b t := by
  by_contra h
  exact hb ((hT a b (fun t ht => by
    by_contra hne
    exact h ⟨t, ht, hne⟩)).mp ha)

theorem conj_mem_hypBlock_of_mem_centralizer
    (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E : Set (Multiplicative (Fin m → ZMod p))} {T : Set (HypIndex m ε)}
    (hT : IsWeightClassUnion E T) {c : hypSU h m ε}
    (hc : c ∈ Subgroup.centralizer (τ '' E)) {g : hypSU h m ε}
    (hg : g ∈ hypBlock h T) : c * g * c⁻¹ ∈ hypBlock h T := by
  have hzero : ∀ (d : hypSU h m ε), d ∈ Subgroup.centralizer (τ '' E) → ∀ a b : HypIndex m ε,
      (a ∈ T ∧ b ∉ T) ∨ (a ∉ T ∧ b ∈ T) →
      (((d : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) a b = 0 := by
    intro d hd a b hab
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact mem_centralizer_apply_eq_zero_of_splitWeight_ne hp hζ hτ hd
        (exists_splitWeight_ne_of_isWeightClassUnion E hT ha hb)
    · obtain ⟨t, ht, hne⟩ := exists_splitWeight_ne_of_isWeightClassUnion E hT hb ha
      exact mem_centralizer_apply_eq_zero_of_splitWeight_ne hp hζ hτ hd ⟨t, ht, hne.symm⟩
  let M : Matrix (HypIndex m ε) (HypIndex m ε) F :=
    (((c : hypSU h m ε) : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F)
  let N : Matrix (HypIndex m ε) (HypIndex m ε) F :=
    (((c⁻¹ : hypSU h m ε) : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F)
  let G : Matrix (HypIndex m ε) (HypIndex m ε) F :=
    (((g : hypSU h m ε) : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F)
  have hMN : M * N = 1 := by
    have hmul : c * c⁻¹ = 1 := mul_inv_cancel c
    have hmat := congrArg (fun y : hypSU h m ε =>
      (((y : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F))) hmul
    simpa only [M, N, Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one] using hmat
  have hres : IsHypBlockOn T (M * G * N) :=
    isHypBlockOn_conj (mem_hypBlock.mp hg) (hzero c hc) (hzero c⁻¹ (Subgroup.inv_mem _ hc)) hMN
  rw [mem_hypBlock]
  have hmat : ((((c * g * c⁻¹) : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) = M * G * N := by
    simp only [M, N, G, Subgroup.coe_mul, Units.val_mul]
  rw [hmat]
  exact hres

theorem normal_hypBlock_inf_centralizer
    (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E : Set (Multiplicative (Fin m → ZMod p))} {T : Set (HypIndex m ε)}
    (hT : IsWeightClassUnion E T) :
    (((Subgroup.centralizer (τ '' E)) ⊓ hypBlock (h := h) T).subgroupOf
      (Subgroup.centralizer (τ '' E))).Normal := by
  let C := Subgroup.centralizer (τ '' E)
  have hle : C ⊓ hypBlock (h := h) T ≤ C := inf_le_left
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  have hconj : ∀ (d : hypSU h m ε), d ∈ C → ∀ x ∈ C ⊓ hypBlock (h := h) T,
      d * x * d⁻¹ ∈ C ⊓ hypBlock (h := h) T := by
    intro d hd x hx
    exact ⟨C.mul_mem (C.mul_mem hd hx.1) (Subgroup.inv_mem C hd),
      conj_mem_hypBlock_of_mem_centralizer hp hζ hτ hT hd hx.2⟩
  intro x
  constructor
  · exact hconj c hc x
  · intro hx
    have h := hconj c⁻¹ (Subgroup.inv_mem C hc) (c * x * c⁻¹) hx
    convert h using 1
    group

end CFSG.StandardType.SuSplitRootGen

end

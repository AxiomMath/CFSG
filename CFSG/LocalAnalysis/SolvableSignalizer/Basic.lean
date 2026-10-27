module

public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.SolvableSignalizer

section FixedSubgroups

variable {A G : Type*} [Group A] [Group G]

@[expose]
def fixedSubgroup (α : A →* MulAut G) (a : A) : Subgroup G :=
  (α a).toMonoidHom.eqLocus (MonoidHom.id G)

def fixedBySubgroup (α : A →* MulAut G) (B : Subgroup A) : Subgroup G :=
  ⨅ b : B, fixedSubgroup α (b : A)

@[expose]
def fixedIn (α : A →* MulAut G) (H : Subgroup G) (a : A) : Subgroup G :=
  H ⊓ fixedSubgroup α a

@[expose]
def fixedInBySubgroup (α : A →* MulAut G) (H : Subgroup G)
    (B : Subgroup A) : Subgroup G :=
  H ⊓ fixedBySubgroup α B

@[expose]
def IsInvariant (α : A →* MulAut G) (H : Subgroup G) : Prop :=
  ∀ a : A, H.map (α a).toMonoidHom = H

@[simp]
theorem mem_fixedSubgroup (α : A →* MulAut G) (a : A) (g : G) :
    g ∈ fixedSubgroup α a ↔ α a g = g :=
  Iff.rfl

@[simp]
theorem mem_fixedBySubgroup (α : A →* MulAut G) (B : Subgroup A) (g : G) :
    g ∈ fixedBySubgroup α B ↔ ∀ b ∈ B, α b g = g := by
  simp [fixedBySubgroup]

@[simp]
theorem mem_fixedIn (α : A →* MulAut G) (H : Subgroup G) (a : A) (g : G) :
    g ∈ fixedIn α H a ↔ g ∈ H ∧ α a g = g :=
  Iff.rfl

@[simp]
theorem mem_fixedInBySubgroup (α : A →* MulAut G) (H : Subgroup G)
    (B : Subgroup A) (g : G) :
    g ∈ fixedInBySubgroup α H B ↔ g ∈ H ∧ ∀ b ∈ B, α b g = g := by
  simp [fixedInBySubgroup]

namespace IsInvariant

variable {α : A →* MulAut G} {H K : Subgroup G}

theorem inf (hH : IsInvariant α H) (hK : IsInvariant α K) : IsInvariant α (H ⊓ K) := fun a => by
  rw [Subgroup.map_inf _ _ _ (α a).injective, hH a, hK a]

theorem iSup {ι : Sort*} {H : ι → Subgroup G} (h : ∀ i, IsInvariant α (H i)) :
    IsInvariant α (⨆ i, H i) := fun a => by
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i => h i a

theorem normalizer (hH : IsInvariant α H) : IsInvariant α (Subgroup.normalizer (H : Set G)) :=
  fun a => by rw [Subgroup.map_equiv_normalizer_eq H (α a), hH a]

theorem map_conj {g : G} (hg : ∀ a : A, α a g = g) (hH : IsInvariant α H) :
    IsInvariant α (H.map (MulAut.conj g).toMonoidHom) := fun a => by
  have hcomm : (α a).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (α a).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, hg a]
  rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, hH a]

end IsInvariant

end FixedSubgroups

structure Datum (p : ℕ) {A G : Type*} [CommGroup A] [Finite A]
    [Group G] [Finite G] (α : A →* MulAut G) (θ : A → Subgroup G) : Prop where
  prime : p.Prime
  exponent : ∀ a : A, a ^ p = 1
  rank_two : p ^ 2 ≤ Nat.card A
  invariant : ∀ a : A, a ≠ 1 → IsInvariant α (θ a)
  solvable : ∀ a : A, a ≠ 1 → Group.IsSolvable (θ a)
  coprime : ∀ a : A, a ≠ 1 → Nat.Coprime p (Nat.card (θ a))
  central : ∀ a : A, a ≠ 1 → θ a ≤ fixedSubgroup α a
  balance : ∀ a b : A, a ≠ 1 → b ≠ 1 → fixedIn α (θ a) b ≤ θ b

section Assignments

variable {A G : Type*} [Group A] [Group G]

@[expose]
def Compatible (p : ℕ) (α : A →* MulAut G) (θ : A → Subgroup G)
    (H : Subgroup G) : Prop :=
  IsInvariant α H ∧ Group.IsSolvable H ∧ Nat.Coprime p (Nat.card H) ∧
    ∀ a : A, a ≠ 1 → fixedIn α H a ≤ θ a

@[expose]
def CompatibleAt (p : ℕ) (α : A →* MulAut G) (θ : A → Subgroup G)
    (π : Set ℕ) (H : Subgroup G) : Prop :=
  Compatible p α θ H ∧ primeSupported π (Nat.card H)

@[expose]
def MaxCompatible (p : ℕ) (α : A →* MulAut G) (θ : A → Subgroup G)
    (π : Set ℕ) (H : Subgroup G) : Prop :=
  CompatibleAt p α θ π H ∧
    ∀ K : Subgroup G, CompatibleAt p α θ π K → H ≤ K → K ≤ H

@[expose]
def MaxCompatibleWhole (p : ℕ) (α : A →* MulAut G) (θ : A → Subgroup G)
    (H : Subgroup G) : Prop :=
  Compatible p α θ H ∧
    ∀ K : Subgroup G, Compatible p α θ K → H ≤ K → K ≤ H

@[expose]
def completion (θ : A → Subgroup G) : Subgroup G :=
  ⨆ (a : A) (_ : a ≠ 1), θ a

@[expose]
def completionIn (θ : A → Subgroup G) (H : Subgroup G) : Subgroup G :=
  ⨆ (a : A) (_ : a ≠ 1), θ a ⊓ H

@[expose]
def IsComplete (p : ℕ) (α : A →* MulAut G) (θ : A → Subgroup G) : Prop :=
  Compatible p α θ (completion θ)

@[expose]
def commonSignalizer (θ : A → Subgroup G) (B : Subgroup A) : Subgroup G :=
  ⨅ (b : A) (_ : b ∈ B) (_ : b ≠ 1), θ b

@[expose]
def commonSignalizerWhole (θ : A → Subgroup G) : Subgroup G :=
  commonSignalizer θ ⊤

@[expose]
def spectrum (θ : A → Subgroup G) : Set ℕ :=
  {q | q.Prime ∧ ∃ a : A, a ≠ 1 ∧ q ∣ Nat.card (θ a)}

@[expose]
def primeSubfunctor (α : A →* MulAut G) (θ : A → Subgroup G)
    (π : Set ℕ) (a : A) : Subgroup G :=
  ⨆ (U : Subgroup G) (_ : U ≤ θ a) (_ : IsInvariant α U)
    (_ : primeSupported π (Nat.card U))
    (_ : commonSignalizerWhole θ ≤ Subgroup.normalizer (U : Set G)), U

@[expose]
def LocallyComplete (p : ℕ) (α : A →* MulAut G) (θ : A → Subgroup G) : Prop :=
  (∀ U : Subgroup G, Compatible p α θ U → U ≠ ⊥ →
    Compatible p α θ (completionIn θ (Subgroup.normalizer (U : Set G)))) ∧
  ∀ q ∈ spectrum θ, IsComplete p α (primeSubfunctor α θ (spectrum θ \ {q}))

theorem finite_spectrum [Finite G] (θ : A → Subgroup G) : (spectrum θ).Finite := by
  refine (Set.finite_Iic (Nat.card G)).subset ?_
  rintro q ⟨-, a, -, hqa⟩
  exact Nat.le_of_dvd (Nat.card_pos (α := G)) (hqa.trans (Subgroup.card_subgroup_dvd_card (θ a)))

theorem mem_commonSignalizerWhole {θ : A → Subgroup G} {g : G} :
    g ∈ commonSignalizerWhole θ ↔ ∀ a : A, a ≠ 1 → g ∈ θ a := by
  simp [commonSignalizerWhole, commonSignalizer]

theorem commonSignalizerWhole_le (θ : A → Subgroup G) {a : A} (ha : a ≠ 1) :
    commonSignalizerWhole θ ≤ θ a :=
  fun _ hg => mem_commonSignalizerWhole.mp hg a ha

theorem completionIn_le (θ : A → Subgroup G) (H : Subgroup G) : completionIn θ H ≤ H :=
  iSup₂_le fun _ _ => inf_le_right

theorem completionIn_mono (θ : A → Subgroup G) {H K : Subgroup G} (h : H ≤ K) :
    completionIn θ H ≤ completionIn θ K :=
  iSup₂_mono fun _ _ => inf_le_inf_left _ h

theorem le_primeSubfunctor {α : A →* MulAut G} {θ : A → Subgroup G} {π : Set ℕ} {a : A}
    {U : Subgroup G} (hU : U ≤ θ a) (hi : IsInvariant α U) (hp : primeSupported π (Nat.card U))
    (hn : commonSignalizerWhole θ ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ primeSubfunctor α θ π a :=
  le_iSup_of_le U <| le_iSup_of_le hU <| le_iSup_of_le hi <| le_iSup_of_le hp <|
    le_iSup_of_le hn le_rfl

end Assignments

namespace Datum

variable {p : ℕ} {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]
  {α : A →* MulAut G} {θ : A → Subgroup G}

theorem isElementaryAbelian (d : Datum p α θ) :
    CFSG.IsElementaryAbelian p A where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr d.exponent

theorem notMem_spectrum (d : Datum p α θ) : p ∉ spectrum θ := by
  rintro ⟨_, a, ha, hpa⟩
  exact (d.prime.coprime_iff_not_dvd.mp (d.coprime a ha)) hpa

end Datum

section Restriction

variable {A G : Type*} [Group A] [Group G]

@[expose]
def restrictAction (α : A →* MulAut G) (H : Subgroup G) (hH : IsInvariant α H) :
    A →* MulAut H where
  toFun a := ((α a).subgroupMap H).trans (MulEquiv.subgroupCongr (hH a))
  map_one' := by
    ext x
    change α 1 (x : G) = (x : G)
    simp
  map_mul' a b := by
    ext x
    change α (a * b) (x : G) = α a (α b (x : G))
    simp

@[simp]
theorem restrictAction_apply (α : A →* MulAut G) (H : Subgroup G)
    (hH : IsInvariant α H) (a : A) (x : H) :
    ((restrictAction α H hH a x : H) : G) = α a (x : G) :=
  rfl

theorem isInvariant_restrictAction_iff {α : A →* MulAut G} {H : Subgroup G}
    (hH : IsInvariant α H) (U : Subgroup H) :
    IsInvariant (restrictAction α H hH) U ↔ IsInvariant α (U.map H.subtype) := by
  have key (a : A) : (U.map (restrictAction α H hH a).toMonoidHom).map H.subtype =
      (U.map H.subtype).map (α a).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  refine ⟨fun h a => by rw [← key a, h a], fun h a => ?_⟩
  apply Subgroup.map_injective H.subtype_injective
  rw [key a, h a]

theorem IsInvariant.map_subtype_of_characteristic {α : A →* MulAut G} {H : Subgroup G}
    (hH : IsInvariant α H) {K : Subgroup H} (hK : K.Characteristic) :
    IsInvariant α (K.map H.subtype) :=
  (isInvariant_restrictAction_iff hH K).mp fun a =>
    Subgroup.characteristic_iff_map_eq.mp hK (restrictAction α H hH a)

theorem fixedSubgroup_restrictAction_map_subtype (α : A →* MulAut G) (H : Subgroup G)
    (hH : IsInvariant α H) (a : A) :
    (fixedSubgroup (restrictAction α H hH) a).map H.subtype = fixedIn α H a := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, congrArg Subtype.val hy⟩
  · rintro ⟨hxH, hx⟩
    exact ⟨⟨x, hxH⟩, Subtype.ext hx, rfl⟩

theorem fixedBySubgroup_restrictAction_map_subtype (α : A →* MulAut G) (H : Subgroup G)
    (hH : IsInvariant α H) (B : Subgroup A) :
    (fixedBySubgroup (restrictAction α H hH) B).map H.subtype = fixedInBySubgroup α H B := by
  ext x
  simp only [Subgroup.mem_map, mem_fixedBySubgroup, mem_fixedInBySubgroup]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, fun b hb => by simpa using congrArg Subtype.val (hy b hb)⟩
  · rintro ⟨hxH, hx⟩
    exact ⟨⟨x, hxH⟩, fun b hb => Subtype.ext (by rw [restrictAction_apply]; exact hx b hb), rfl⟩

@[expose]
def restrictTheta (θ : A → Subgroup G) (H : Subgroup G) : A → Subgroup H :=
  fun a => (θ a).subgroupOf H

omit [Group A] in
@[simp]
theorem mem_restrictTheta (θ : A → Subgroup G) (H : Subgroup G) (a : A) (x : H) :
    x ∈ restrictTheta θ H a ↔ (x : G) ∈ θ a :=
  Iff.rfl

omit [Group A] in
theorem restrictTheta_map_subtype (θ : A → Subgroup G) (H : Subgroup G) (a : A) :
    (restrictTheta θ H a).map H.subtype = θ a ⊓ H :=
  Subgroup.subgroupOf_map_subtype (θ a) H

omit [Group A] in
theorem card_restrictTheta (θ : A → Subgroup G) (H : Subgroup G) (a : A) :
    Nat.card (restrictTheta θ H a) = Nat.card ↥(θ a ⊓ H) := by
  rw [← restrictTheta_map_subtype, Subgroup.card_map_of_injective H.subtype_injective]

theorem spectrum_restrictTheta_subset (θ : A → Subgroup G) (H : Subgroup G) :
    spectrum (restrictTheta θ H) ⊆ spectrum θ := by
  rintro q ⟨hq, a, ha, hqa⟩
  refine ⟨hq, a, ha, hqa.trans ?_⟩
  rw [card_restrictTheta]
  exact Subgroup.card_dvd_of_le inf_le_left

@[expose]
def quotientAction (α : A →* MulAut G) (N : Subgroup G) [N.Normal]
    (hN : IsInvariant α N) : A →* MulAut (G ⧸ N) where
  toFun a := QuotientGroup.congr N N (α a) (hN a)
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x fun g => ?_
    change QuotientGroup.mk' N (α 1 g) = QuotientGroup.mk' N g
    simp
  map_mul' a b := by
    ext x
    refine QuotientGroup.induction_on x fun g => ?_
    change QuotientGroup.mk' N (α (a * b) g) = QuotientGroup.mk' N (α a (α b g))
    simp

@[simp]
theorem quotientAction_apply_mk (α : A →* MulAut G) (N : Subgroup G) [N.Normal]
    (hN : IsInvariant α N) (a : A) (g : G) :
    quotientAction α N hN a (QuotientGroup.mk' N g) = QuotientGroup.mk' N (α a g) :=
  rfl

@[expose]
def quotientTheta (θ : A → Subgroup G) (N : Subgroup G) [N.Normal] :
    A → Subgroup (G ⧸ N) :=
  fun a => (θ a).map (QuotientGroup.mk' N)

end Restriction

end CFSG.SolvableSignalizer

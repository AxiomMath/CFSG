module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankGroups
public import CFSG.RankThree.GroupTheory.SteinbergCEExtraspecialMinusModule
public import CFSG.RankThree.GroupTheory.SteinbergCESmallBinaryOrbitCounts
public import Mathlib.RepresentationTheory.Maschke

public section

namespace CFSG.RankThree.PartOne.FixedRank36

open CFSG CFSG.RankThree.GroupTheory

section Generic

variable {K : Type*} [Field K] {L : Type*} [Monoid L] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def IsInv (ρ : Representation K L V) (W : Submodule K V) : Prop :=
  ∀ g : L, ∀ w ∈ W, ρ g w ∈ W

@[expose] def IsMinInv (ρ : Representation K L V) (W : Submodule K V) : Prop :=
  IsInv ρ W ∧ W ≠ ⊥ ∧ ∀ W' : Submodule K V, W' ≤ W → IsInv ρ W' → W' = ⊥ ∨ W' = W

variable {ρ : Representation K L V}

theorem isInv_top : IsInv ρ ⊤ := fun _ _ _ => Submodule.mem_top

theorem isInv_bot : IsInv ρ ⊥ := fun g w hw => by
  rw [Submodule.mem_bot] at hw ⊢
  rw [hw, map_zero]

theorem IsInv.inf {W W' : Submodule K V} (h : IsInv ρ W) (h' : IsInv ρ W') : IsInv ρ (W ⊓ W') :=
  fun g w hw => ⟨h g w hw.1, h' g w hw.2⟩

theorem IsInv.sup {W W' : Submodule K V} (h : IsInv ρ W) (h' : IsInv ρ W') : IsInv ρ (W ⊔ W') := by
  intro g w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add]
  exact Submodule.add_mem_sup (h g a ha) (h' g b hb)

theorem exists_isMinInv_le [FiniteDimensional K V] {U : Submodule K V} (hU : IsInv ρ U)
    (hU0 : U ≠ ⊥) : ∃ Y ≤ U, IsMinInv ρ Y := by
  classical
  have hex : ∃ n, ∃ Y : Submodule K V, Y ≤ U ∧ IsInv ρ Y ∧ Y ≠ ⊥ ∧ Module.finrank K Y = n :=
    ⟨_, U, le_rfl, hU, hU0, rfl⟩
  obtain ⟨Y, hYU, hYinv, hY0, hYn⟩ := Nat.find_spec hex
  refine ⟨Y, hYU, hYinv, hY0, fun W' hW'Y hW'inv => ?_⟩
  by_cases hW'0 : W' = ⊥
  · exact Or.inl hW'0
  right
  have hle : Module.finrank K W' ≤ Module.finrank K Y := Submodule.finrank_mono hW'Y
  have hge : Nat.find hex ≤ Module.finrank K W' :=
    Nat.find_min' hex ⟨W', hW'Y.trans hYU, hW'inv, hW'0, rfl⟩
  exact Submodule.eq_of_le_of_finrank_le hW'Y (by omega)

end Generic

section Restrict

variable {K : Type*} [Field K] {L : Type*} [Monoid L] {V : Type*} [AddCommGroup V] [Module K V]
  {ρ : Representation K L V}

@[expose] def restrictRep (ρ : Representation K L V) (Y : Submodule K V) (hY : IsInv ρ Y) :
    Representation K L Y :=
  (⟨Y, hY⟩ : Subrepresentation ρ).toRepresentation

theorem restrictRep_apply (Y : Submodule K V) (hY : IsInv ρ Y) (g : L) (v : Y) :
    ((restrictRep ρ Y hY g v : Y) : V) = ρ g v := rfl

theorem finrank_eigenspace_restrict (Y : Submodule K V) (hY : IsInv ρ Y) (g : L) :
    Module.finrank K (Module.End.eigenspace (restrictRep ρ Y hY g) 1) =
      Module.finrank K ↥(Module.End.eigenspace (ρ g) 1 ⊓ Y) := by
  have hmap : (Module.End.eigenspace (restrictRep ρ Y hY g) 1).map Y.subtype =
      Module.End.eigenspace (ρ g) 1 ⊓ Y := by
    ext v
    simp only [Submodule.mem_map, Module.End.mem_eigenspace_iff, one_smul, Submodule.mem_inf,
      Submodule.subtype_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨congrArg Subtype.val hw, w.2⟩
    · rintro ⟨hv, hvY⟩
      exact ⟨⟨v, hvY⟩, Subtype.ext hv, rfl⟩
  rw [← hmap]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Y.subtype Y.injective_subtype _))

theorem isIrreducible_restrictRep {Y : Submodule K V} (hY : IsMinInv ρ Y) :
    (restrictRep ρ Y hY.1).IsIrreducible := by
  obtain ⟨hinv, hY0, hmin⟩ := hY
  obtain ⟨y, hyY, hy0⟩ := (Submodule.ne_bot_iff Y).1 hY0
  refine
    { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩
      eq_bot_or_eq_top := fun a => ?_ }
  · have h1 : (⟨y, hyY⟩ : Y) ∈ (⊤ : Subrepresentation (restrictRep ρ Y hinv)) := trivial
    rw [← h] at h1
    exact hy0 (congrArg Subtype.val (Submodule.mem_bot K |>.1 h1))
  · set W' : Submodule K V := a.toSubmodule.map Y.subtype with hW'
    have hW'Y : W' ≤ Y := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hW'inv : IsInv ρ W' := by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨restrictRep ρ Y hinv g w, a.apply_mem_toSubmodule g hw, rfl⟩
    rcases hmin W' hW'Y hW'inv with h | h
    · left
      apply Subrepresentation.ext
      show a.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro w hw
      have : (w : V) ∈ W' := ⟨w, hw, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact (Submodule.mem_bot K).2 (Subtype.ext this)
    · right
      apply Subrepresentation.ext
      show a.toSubmodule = ⊤
      rw [eq_top_iff]
      intro w _
      have : (w : V) ∈ W' := by rw [h]; exact w.2
      obtain ⟨w', hw', hww'⟩ := this
      rwa [show w = w' from (Subtype.ext hww'.symm)]

theorem eq_or_neg_of_isMinInv {Y : Submodule K V} (hY : IsMinInv ρ Y) {T : V →ₗ[K] V}
    (hTsq : ∀ v, T (T v) = v) (hTc : ∀ g v, T (ρ g v) = ρ g (T v)) (hTY : ∀ y ∈ Y, T y ∈ Y) :
    (∀ y ∈ Y, T y = y) ∨ (∀ y ∈ Y, T y = -y) := by
  have hinv : IsInv ρ (Module.End.eigenspace T 1 ⊓ Y) := by
    intro g w hw
    refine Submodule.mem_inf.2 ⟨?_, hY.1 g w (Submodule.mem_inf.1 hw).2⟩
    rw [Module.End.mem_eigenspace_iff, one_smul, hTc, show T w = w from by
      simpa [Module.End.mem_eigenspace_iff] using (Submodule.mem_inf.1 hw).1]
  rcases hY.2.2 _ inf_le_right hinv with h | h
  · right
    intro y hy
    have hu : y + T y ∈ Module.End.eigenspace T 1 ⊓ Y := by
      refine Submodule.mem_inf.2 ⟨?_, Y.add_mem hy (hTY y hy)⟩
      rw [Module.End.mem_eigenspace_iff, one_smul, map_add, hTsq, add_comm]
    rw [h, Submodule.mem_bot] at hu
    exact eq_neg_of_add_eq_zero_right hu
  · left
    intro y hy
    have : y ∈ Module.End.eigenspace T 1 ⊓ Y := by rw [h]; exact hy
    simpa [Module.End.mem_eigenspace_iff] using (Submodule.mem_inf.1 this).1

theorem finrank_add_le_of_inf_eq_bot [FiniteDimensional K V] {A B C : Submodule K V} (hAC : A ≤ C)
    (hBC : B ≤ C) (hd : A ⊓ B = ⊥) :
    Module.finrank K A + Module.finrank K B ≤ Module.finrank K C := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hd, finrank_bot] at h
  have := Submodule.finrank_mono (sup_le hAC hBC)
  omega

end Restrict

section Maschke

variable {K : Type*} [Field K] {L : Type*} [Group L] {V : Type*} [AddCommGroup V] [Module K V]
  {ρ : Representation K L V}

theorem exists_isInv_isCompl [Finite L] [NeZero (Nat.card L : K)] {W : Submodule K V}
    (hW : IsInv ρ W) : ∃ W' : Submodule K V, IsInv ρ W' ∧ IsCompl W W' := by
  obtain ⟨b, hb⟩ := exists_isCompl (⟨W, hW⟩ : Subrepresentation ρ)
  refine ⟨b.toSubmodule, b.apply_mem_toSubmodule, ?_⟩
  have hd : (⟨W, hW⟩ : Subrepresentation ρ) ⊓ b = ⊥ := disjoint_iff.1 hb.1
  have hc : (⟨W, hW⟩ : Subrepresentation ρ) ⊔ b = ⊤ := codisjoint_iff.1 hb.2
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  exact ⟨congrArg Subrepresentation.toSubmodule hd, congrArg Subrepresentation.toSubmodule hc⟩

end Maschke


section Irreducible

variable {K : Type*} [Field K] {L : Type*} [Monoid L] {V : Type*} [AddCommGroup V] [Module K V]
  {ρ : Representation K L V}

theorem isIrreducible_of_forall [Nontrivial V]
    (h : ∀ W : Submodule K V, IsInv ρ W → W = ⊥ ∨ W = ⊤) : ρ.IsIrreducible := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine
    { exists_pair_ne := ⟨⊥, ⊤, fun h' => ?_⟩
      eq_bot_or_eq_top := fun a => ?_ }
  · have h1 : v ∈ (⊤ : Subrepresentation ρ) := trivial
    rw [← h'] at h1
    exact hv ((Submodule.mem_bot K).1 h1)
  · rcases h a.toSubmodule a.apply_mem_toSubmodule with h' | h'
    · exact Or.inl (Subrepresentation.ext h')
    · exact Or.inr (Subrepresentation.ext h')

theorem nontrivial_of_isIrreducible' (hρ : ρ.IsIrreducible) : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton (Submodule K V) := (Submodule.subsingleton_iff K).mpr h
  exact (bot_ne_top (α := Subrepresentation ρ))
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem eq_bot_or_eq_top_of_isIrreducible' (hρ : ρ.IsIrreducible) (W : Submodule K V)
    (hW : IsInv ρ W) : W = ⊥ ∨ W = ⊤ := by
  rcases hρ.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

end Irreducible

section SA

open SemidirectProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {S : Type*} [Group S] {A : Type*} [Group A] {φ : A →* MulAut S} {z : S} {a₀ : A}

structure SAData (S A : Type*) [Group S] [Group A] (φ : A →* MulAut S) (z : S) (a₀ : A) : Prop where
  ext : IsExtraspecialPGroup 2 S
  card : Nat.card S = 32
  center_eq : Subgroup.center S = Subgroup.zpowers z
  ne_one : z ≠ 1
  sq : z * z = 1
  pgroup : IsPGroup 5 A
  comm : ∀ a b : A, a * b = b * a
  fpf : ∀ s : S, s ∉ Subgroup.center S → (φ a₀ s)⁻¹ * s ∉ Subgroup.center S

theorem SAData.inl_central [Finite S] (hD : SAData S A φ z a₀) (x : S ⋊[φ] A) :
    inl z * x = x * inl z := by
  have h1 : (inl z : S ⋊[φ] A) * inl x.left = inl x.left * inl z := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.1 (hD.center_eq ▸ Subgroup.mem_zpowers z) x.left).symm
  have h2 : (inl z : S ⋊[φ] A) * inr x.right = inr x.right * inl z := by
    have := inl_aut (φ := φ) x.right z
    rw [center_fixed φ hD.ext hD.center_eq x.right] at this
    conv_lhs => rw [this]
    rw [mul_assoc, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  calc inl z * x = inl z * (inl x.left * inr x.right) := by rw [inl_left_mul_inr_right]
    _ = (inl z * inl x.left) * inr x.right := by rw [mul_assoc]
    _ = (inl x.left * inl z) * inr x.right := by rw [h1]
    _ = inl x.left * (inl z * inr x.right) := by rw [mul_assoc]
    _ = inl x.left * (inr x.right * inl z) := by rw [h2]
    _ = (inl x.left * inr x.right) * inl z := by rw [mul_assoc]
    _ = x * inl z := by rw [inl_left_mul_inr_right]

end SA

section Plus

open SemidirectProduct

theorem small_binary_consequence {S : Type*} [CommGroup S] [Finite S]
    [Module (ZMod 2) (Additive S)] (hS : Nat.card S = 2 ^ 4) {A : Type*} [Group A]
    {φ : A →* MulAut S} (hφ : Nat.card φ.range = 5)
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    {K : Type*} [Field K] (hK : (2 : K) ≠ 0) {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : Representation K (S ⋊[φ] A) W) (hρ : ρ.IsIrreducible)
    (hinj : Function.Injective (ρ.comp SemidirectProduct.inl)) :
    ∃ s : S, s ≠ 1 ∧
      3 ≤ Module.finrank K (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) := by
  obtain ⟨-, -, e, he, -, -, -, h5, -⟩ := small_binary_prime_orbit_fixed_space_counts
    (p := 5) (d := 4) (Or.inr ⟨rfl, rfl⟩) hS hφ hirr hK ρ hρ hinj
  have h10 := (h5 rfl).1
  obtain ⟨s, hs1, hs2⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h10]; norm_num)
  exact ⟨s, hs1, by omega⟩

variable {K : Type*} [Field K] {S : Type*} [Group S] [Finite S] {A : Type*} [Group A]
  {φ : A →* MulAut S} {z : S} {a₀ : A}

theorem exists_fixed_three [Finite A] (h2 : (2 : K) ≠ 0) (hD : SAData S A φ z a₀)
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (S ⋊[φ] A) W) (hρ : ρ.IsIrreducible)
    (hcen : ∀ c ∈ Subgroup.center S, ρ (inl c) = 1) (hnt : ∃ s : S, ρ (inl s) ≠ 1) :
    ∃ s : S, s ∉ Subgroup.center S ∧
      3 ≤ Module.finrank K (Module.End.eigenspace (ρ (inl s)) 1) := by
  classical
  have hnW : Nontrivial W := nontrivial_of_isIrreducible' hρ
  let : Module (ZMod 2) (Additive (Abelianization S)) :=
    AddCommGroup.zmodModule fun x => by
      change Additive.ofMul (Additive.toMul x ^ 2) = Additive.ofMul 1
      rw [abelianization_sq hD.ext]
  have hcompat : ∀ a : A, (Abelianization.of : S →* Abelianization S).comp (φ a).toMonoidHom =
      ((abAut φ (MonoidHom.id A a)).toMonoidHom).comp Abelianization.of := by
    intro a
    ext s
    rfl
  let π : S ⋊[φ] A →* Abelianization S ⋊[abAut φ] A :=
    SemidirectProduct.map Abelianization.of (MonoidHom.id A) hcompat
  have hπ : Function.Surjective π := by
    rintro ⟨n, a⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective n
    exact ⟨⟨s, a⟩, rfl⟩
  let ρu : S ⋊[φ] A →* (Module.End K W)ˣ := ρ.toHomUnits
  have hker : π.ker ≤ ρu.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : (π x).left = 1 := by rw [hx]; rfl
    have h2' : (π x).right = 1 := by rw [hx]; rfl
    have hxr : x.right = 1 := h2'
    have hxl : Abelianization.of x.left = 1 := h1
    have hxinl : x = inl x.left := by
      apply SemidirectProduct.ext
      · rfl
      · rw [hxr]; rfl
    apply Units.ext
    change ρ x = 1
    rw [hxinl]
    exact hcen _ ((of_eq_one_iff hD.ext _).1 hxl)
  let ρbaru : Abelianization S ⋊[abAut φ] A →* (Module.End K W)ˣ :=
    (π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)) ⟨ρu, hker⟩
  let ρbar : Representation K (Abelianization S ⋊[abAut φ] A) W := (Units.coeHom _).comp ρbaru
  have hρbar : ∀ x, ρbar (π x) = ρ x := by
    intro x
    change ((ρbaru (π x) : (Module.End K W)ˣ) : Module.End K W) = ρ x
    rw [show ρbaru (π x) = ρu x from π.liftOfRightInverse_comp_apply _ _ ⟨ρu, hker⟩ x]
    rfl
  have hρbar_inl : ∀ s : S, ρbar (inl (Abelianization.of s)) = ρ (inl s) := by
    intro s
    rw [← hρbar]
    rfl
  have hirrbar : ρbar.IsIrreducible := by
    refine isIrreducible_of_forall fun W' hW' => ?_
    refine eq_bot_or_eq_top_of_isIrreducible' hρ W' fun g w hw => ?_
    rw [← hρbar g]
    exact hW' _ w hw
  have hinjbar : Function.Injective (ρbar.comp inl) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    let U : Subgroup (Abelianization S) := (ρbar.comp inl).ker
    have hUinv : ∀ a : A, ∀ n ∈ U, abAut φ a n ∈ U := by
      intro a n hn
      have hn' : ρbar (inl n) = 1 := hn
      show ρbar (inl (abAut φ a n)) = 1
      rw [inl_aut, map_mul, map_mul, hn', mul_one, ← map_mul, ← map_mul, mul_inv_cancel, map_one,
        map_one]
    rcases abAut_irreducible φ hD.ext hD.card hD.pgroup a₀ hD.fpf U hUinv with h | h
    · exact h
    · exfalso
      obtain ⟨s, hs⟩ := hnt
      apply hs
      rw [← hρbar_inl]
      have : Abelianization.of s ∈ U := h ▸ Subgroup.mem_top _
      exact this
  obtain ⟨t, ht1, ht3⟩ := small_binary_consequence
    (by rw [card_abelianization hD.ext hD.card]; norm_num)
    (abAut_range_card φ hD.ext hD.card hD.pgroup hD.comm a₀ hD.fpf)
    (abAut_irreducible φ hD.ext hD.card hD.pgroup a₀ hD.fpf) h2 ρbar hirrbar hinjbar
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective t
  refine ⟨s, fun hs => ht1 ((of_eq_one_iff hD.ext s).2 hs), ?_⟩
  rw [← hρbar_inl]
  exact ht3

end Plus

section LemmaY

open SemidirectProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {S : Type*} [Group S] {A : Type*} [Group A] {φ : A →* MulAut S} {z : S} {a₀ : A}

theorem SAData.apply_inl_inl (hD : SAData S A φ z a₀)
    (ρ : Representation K (S ⋊[φ] A) V) (v : V) : ρ (inl z) (ρ (inl z) v) = v := by
  have h : (inl z : S ⋊[φ] A) * inl z = 1 := by rw [← map_mul, hD.sq, map_one]
  calc ρ (inl z) (ρ (inl z) v) = ρ (inl z * inl z) v := by rw [map_mul]; rfl
    _ = v := by rw [h, map_one]; rfl

theorem SAData.apply_comm [Finite S] (hD : SAData S A φ z a₀)
    (ρ : Representation K (S ⋊[φ] A) V) (g : S ⋊[φ] A) (v : V) :
    ρ (inl z) (ρ g v) = ρ g (ρ (inl z) v) := by
  calc ρ (inl z) (ρ g v) = ρ (inl z * g) v := by rw [map_mul]; rfl
    _ = ρ (g * inl z) v := by rw [hD.inl_central g]
    _ = ρ g (ρ (inl z) v) := by rw [map_mul]; rfl

theorem lemmaY_sign [Finite S] (hD : SAData S A φ z a₀) (ρ : Representation K (S ⋊[φ] A) V)
    {Y : Submodule K V} (hY : IsMinInv ρ Y) :
    (∀ y ∈ Y, ρ (inl z) y = y) ∨ (∀ y ∈ Y, ρ (inl z) y = -y) :=
  eq_or_neg_of_isMinInv hY (T := ρ (inl z)) (hD.apply_inl_inl ρ) (hD.apply_comm ρ)
    (fun y hy => hY.1 _ y hy)

theorem lemmaY_minus [Finite S] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (hD : SAData S A φ z a₀)
    (ρ : Representation K (S ⋊[φ] A) V) {Y : Submodule K V} (hY : IsMinInv ρ Y)
    (hzY : ∀ y ∈ Y, ρ (inl z) y = -y) :
    4 ≤ Module.finrank K Y ∧ ∀ s : S, s ∉ Subgroup.center S → orderOf s = 2 →
      2 * Module.finrank K ↥(Module.End.eigenspace (ρ (inl s)) 1 ⊓ Y) = Module.finrank K Y := by
  have hnt : Nontrivial Y := Submodule.nontrivial_iff_ne_bot.2 hY.2.1
  have hρz : ((restrictRep ρ Y hY.1).comp inl) z = -1 := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    show ρ (inl z) y = -(y : V)
    exact hzY y y.2
  obtain ⟨h4, hs⟩ := extraspecial_two_minus_module_bound (n := 2) hD.ext
    (by rw [hD.card]; norm_num) hD.center_eq h2 ((restrictRep ρ Y hY.1).comp inl) hρz
  refine ⟨by simpa using h4, fun s hs1 hs2 => ?_⟩
  have := (hs s hs1 hs2).1
  rwa [MonoidHom.comp_apply, finrank_eigenspace_restrict] at this

theorem lemmaY_plus [Finite S] [Finite A] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hD : SAData S A φ z a₀) (ρ : Representation K (S ⋊[φ] A) V) {Y : Submodule K V}
    (hY : IsMinInv ρ Y) (hzY : ∀ y ∈ Y, ρ (inl z) y = y) :
    (∀ s : S, ∀ y ∈ Y, ρ (inl s) y = y) ∨
      ∃ s : S, s ∉ Subgroup.center S ∧
        3 ≤ Module.finrank K ↥(Module.End.eigenspace (ρ (inl s)) 1 ⊓ Y) := by
  by_cases hall : ∀ s : S, ∀ y ∈ Y, ρ (inl s) y = y
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨s₀, y₀, hy₀, hne⟩ := hall
  have hnt : Nontrivial Y := Submodule.nontrivial_iff_ne_bot.2 hY.2.1
  have hirr := isIrreducible_restrictRep hY
  have hcen : ∀ c ∈ Subgroup.center S, (restrictRep ρ Y hY.1) (inl c) = 1 := by
    intro c hc
    rcases eq_one_or_eq_of_mem_center hD.center_eq hD.ne_one hD.sq hc with rfl | rfl
    · rw [map_one, map_one]
    · refine LinearMap.ext fun y => Subtype.ext ?_
      exact hzY y y.2
  have hnt' : ∃ s : S, (restrictRep ρ Y hY.1) (inl s) ≠ 1 := by
    refine ⟨s₀, fun h => hne ?_⟩
    have := congrArg (fun f : Module.End K Y => ((f ⟨y₀, hy₀⟩ : Y) : V)) h
    exact this
  obtain ⟨s, hs, h3⟩ := exists_fixed_three h2 hD (restrictRep ρ Y hY.1) hirr hcen hnt'
  exact ⟨s, hs, by rwa [finrank_eigenspace_restrict] at h3⟩

end LemmaY

section Core

open SemidirectProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {S : Type*} [Group S] [Finite S] {A : Type*} [Group A] [Finite A] {φ : A →* MulAut S} {z : S}
  {a₀ : A}

theorem module_core [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (hD : SAData S A φ z a₀) (ρ : Representation K (S ⋊[φ] A) V) (hz1 : ρ (inl z) ≠ 1)
    (hfix : ∀ s : S, s ≠ 1 → Module.finrank K (Module.End.eigenspace (ρ (inl s)) 1) ≤ 2) :
    IsMinInv ρ ⊤ ∧ ρ (inl z) = -1 ∧ Module.finrank K V = 4 ∧
      ∀ s : S, s ∉ Subgroup.center S → orderOf s = 2 →
        Module.finrank K (Module.End.eigenspace (ρ (inl s)) 1) = 2 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite (S ⋊[φ] A) := Finite.of_equiv (S × A) SemidirectProduct.equivProd.symm
  have hNZ : NeZero (Nat.card (S ⋊[φ] A) : K) := by
    refine ⟨?_⟩
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, hD.card]
    obtain ⟨m, hm⟩ := hD.pgroup.exists_card_eq
    rw [hm]
    push_cast
    have h32 : (32 : K) = 2 ^ 5 := by norm_num
    rw [h32]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h5)
  set T := ρ (inl z) with hT
  have hVinv : IsInv ρ (Module.End.eigenspace T (-1)) := by
    intro g w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    rw [hD.apply_comm ρ g w, hw, map_smul]
  have hV0 : Module.End.eigenspace T (-1) ≠ ⊥ := by
    obtain ⟨v, hv⟩ : ∃ v, T v ≠ v := by
      by_contra h
      push Not at h
      exact hz1 (LinearMap.ext h)
    have hmem : v - T v ∈ Module.End.eigenspace T (-1) := by
      rw [Module.End.mem_eigenspace_iff, map_sub, hD.apply_inl_inl ρ]
      rw [neg_one_smul, neg_sub]
    intro h
    rw [h, Submodule.mem_bot] at hmem
    exact hv (sub_eq_zero.1 hmem).symm
  obtain ⟨W, hWle, hW⟩ := exists_isMinInv_le hVinv hV0
  have hzW : ∀ y ∈ W, T y = -y := by
    intro y hy
    have := hWle hy
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at this
    exact this
  obtain ⟨s₀, hs₀c, hs₀o⟩ := exists_noncentral_involution hD.ext hD.card
  have hs₀1 : s₀ ≠ 1 := fun h => hs₀c (h ▸ Subgroup.one_mem _)
  obtain ⟨h4, hs⟩ := lemmaY_minus h2 hD ρ hW hzW
  have hW2 := hs s₀ hs₀c hs₀o
  have hle : Module.finrank K ↥(Module.End.eigenspace (ρ (inl s₀)) 1 ⊓ W) ≤ 2 :=
    (Submodule.finrank_mono inf_le_left).trans (hfix s₀ hs₀1)
  have hdimW : Module.finrank K W = 4 := by omega
  have hWsub2 : Module.finrank K ↥(Module.End.eigenspace (ρ (inl s₀)) 1 ⊓ W) = 2 := by omega
  have hWtop : W = ⊤ := by
    by_contra hne
    obtain ⟨W', hW'inv, hW'compl⟩ := exists_isInv_isCompl hW.1
    have hW'0 : W' ≠ ⊥ := by
      intro h
      have := codisjoint_iff.1 hW'compl.2
      rw [h, sup_bot_eq] at this
      exact hne this
    obtain ⟨Y, hYle, hY⟩ := exists_isMinInv_le hW'inv hW'0
    have hdisj : W ⊓ Y = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_left W hYle).trans (disjoint_iff.1 hW'compl.1).le)
    have hdisj' : (Module.End.eigenspace (ρ (inl s₀)) 1 ⊓ W) ⊓
        (Module.End.eigenspace (ρ (inl s₀)) 1 ⊓ Y) = ⊥ :=
      le_bot_iff.1 (le_trans (inf_le_inf inf_le_right inf_le_right) hdisj.le)
    have hfix0 := hfix s₀ hs₀1
    rcases lemmaY_sign hD ρ hY with hzY | hzY
    ·
      rcases lemmaY_plus h2 hD ρ hY hzY with hall | ⟨s', hs', h3⟩
      · have hYC : Y ≤ Module.End.eigenspace (ρ (inl s₀)) 1 := fun y hy => by
          rw [Module.End.mem_eigenspace_iff, one_smul]
          exact hall s₀ y hy
        have hdisj'' : (Module.End.eigenspace (ρ (inl s₀)) 1 ⊓ W) ⊓ Y = ⊥ :=
          le_bot_iff.1 (le_trans (inf_le_inf inf_le_right le_rfl) hdisj.le)
        have := finrank_add_le_of_inf_eq_bot (inf_le_left : _ ≤ Module.End.eigenspace
          (ρ (inl s₀)) 1) hYC hdisj''
        have hpos : 0 < Module.finrank K Y := by
          have : Nontrivial Y := Submodule.nontrivial_iff_ne_bot.2 hY.2.1
          exact Module.finrank_pos
        omega
      · have hs'1 : s' ≠ 1 := fun h => hs' (h ▸ Subgroup.one_mem _)
        have := (Submodule.finrank_mono (inf_le_left : Module.End.eigenspace (ρ (inl s')) 1 ⊓ Y ≤
          Module.End.eigenspace (ρ (inl s')) 1)).trans (hfix s' hs'1)
        omega
    ·
      obtain ⟨hY4, hYs⟩ := lemmaY_minus h2 hD ρ hY hzY
      have hY2 := hYs s₀ hs₀c hs₀o
      have := finrank_add_le_of_inf_eq_bot (inf_le_left : Module.End.eigenspace (ρ (inl s₀)) 1 ⊓ W
        ≤ Module.End.eigenspace (ρ (inl s₀)) 1) (inf_le_left : Module.End.eigenspace (ρ (inl s₀)) 1
        ⊓ Y ≤ Module.End.eigenspace (ρ (inl s₀)) 1) hdisj'
      omega
  subst hWtop
  refine ⟨hW, LinearMap.ext fun v => ?_, ?_, fun s hs1 hs2 => ?_⟩
  · have := hzW v Submodule.mem_top
    rw [this]
    rfl
  · rw [← finrank_top K V]
    exact hdimW
  · have := hs s hs1 hs2
    rw [inf_top_eq, finrank_top] at this
    have h4' := hdimW
    rw [finrank_top] at h4'
    omega

end Core

end CFSG.RankThree.PartOne.FixedRank36

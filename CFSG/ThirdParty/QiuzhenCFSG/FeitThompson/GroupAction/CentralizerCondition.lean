module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

public instance CFSG.center_isInvariant {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] :
    IsInvariant A G (Subgroup.center G) where
  invariant a g := by
    have hcenter := Subgroup.centerCharacteristic.fixed (MulDistribMulAction.toMulAut A G a)
    have mem_comap : g ∈ (Subgroup.center G).comap (MulDistribMulAction.toMulAut A G a).toMonoidHom ↔
        (MulDistribMulAction.toMulAut A G a) g ∈ Subgroup.center G := Subgroup.mem_comap
    have mem_iff : g ∈ Subgroup.center G ↔ (MulDistribMulAction.toMulAut A G a) g ∈ Subgroup.center G := by
      rw [← mem_comap, hcenter]
    have toMulAut_eq : (MulDistribMulAction.toMulAut A G a) g = a • g := by
      simp
    rw [toMulAut_eq] at mem_iff
    exact mem_iff

public instance CFSG.quotientAction_of_invariant {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (H : Subgroup G) [IsInvariant A G H] : MulAction.QuotientAction A H := by
  constructor
  intro b a a' h
  have h_inv : a⁻¹ * a' ∈ H := h
  have h_smul : b • (a⁻¹ * a') ∈ H := (IsInvariant.invariant (A := A) (G := G) (H := H) b (a⁻¹ * a')).1 h_inv
  have eq : b • (a⁻¹ * a') = (b • a)⁻¹ * b • a' := by
    simp [smul_inv']
  rw [eq] at h_smul
  exact h_smul

public instance CFSG.quotient_mulDistribMulAction {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (H : Subgroup G) [H.Normal] [IsInvariant A G H] : MulDistribMulAction A (G ⧸ H) :=
  { MulAction.quotient A H with
    smul_mul := by
      intro a
      refine Quotient.ind₂ ?_
      intro x y
      calc
        a • ((x : G ⧸ H) * (y : G ⧸ H)) = a • (QuotientGroup.mk (x * y)) := by rw [QuotientGroup.mk_mul]
        _ = QuotientGroup.mk (a • (x * y)) := by rw [MulAction.Quotient.smul_mk]
        _ = QuotientGroup.mk (a • x * a • y) := by rw [MulDistribMulAction.smul_mul]
        _ = QuotientGroup.mk (a • x) * QuotientGroup.mk (a • y) := by rw [QuotientGroup.mk_mul]
        _ = ((a • x : G) : G ⧸ H) * ((a • y : G) : G ⧸ H) := by rfl
    smul_one := by
      intro a
      calc
        a • (1 : G ⧸ H) = a • (QuotientGroup.mk (1 : G)) := by rfl
        _ = QuotientGroup.mk (a • (1 : G)) := by rw [MulAction.Quotient.smul_mk]
        _ = QuotientGroup.mk (1 : G) := by rw [MulDistribMulAction.smul_one]
        _ = (1 : G ⧸ H) := by rfl
        }


/-**
**[Subgoal 1: Abelian case]**
If `G` is abelian, then the centralizer of any subgroup is the whole group. Hence under the
hypothesis `hC` we have `fixedPointSubgroup A G = ⊤`, i.e. `∀ a g, a • g = g`.

**Status**: Pending
-/

/-**
**[Subgoal 2: Centre is characteristic]**
The centre `Z(G)` is a characteristic subgroup of `G`. Consequently, any group action on `G`
restricts to an action on `Z(G)`.

**Status**: Pending
**Integration**: Use to obtain an action on the centre and on the quotient `G/Z(G)`.
-/

/-**
**[Subgoal 3: Centralizer condition for the centre]**
Assume the hypotheses of Proposition 1.10. Let `Z = Z(G)` and let `F = G ^* A`.
If `z ∈ Z` centralizes `F ∩ Z`, then `z ∈ F ∩ Z`. In other words,
`Z.centralizer (F ∩ Z) ≤ F ∩ Z`.

**Status**: Pending
**Integration**: Needed to apply the base case to the action on `Z`.
-/
lemma CFSG.centralizer_inf_center_le_fixedPoint_inf_center {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (_ : Group.IsNilpotent G)
    (_ : Nat.Coprime (Nat.card A) (Nat.card G))
    (hC : Subgroup.centralizer (fixedPointSubgroup A G : Set G) ≤ fixedPointSubgroup A G) :
    Subgroup.centralizer ((fixedPointSubgroup A G ⊓ Subgroup.center G) : Set G) ⊓ Subgroup.center G ≤
      (fixedPointSubgroup A G ⊓ Subgroup.center G) := by
  intro z hz
  rcases hz with ⟨hz_centralizer, hz_center⟩
  have hz_centralizer_F : z ∈ Subgroup.centralizer (fixedPointSubgroup A G : Set G) := by
    apply Subgroup.center_le_centralizer (fixedPointSubgroup A G : Set G) hz_center
  have hz_F : z ∈ fixedPointSubgroup A G := hC hz_centralizer_F
  exact ⟨hz_F, hz_center⟩

/-**
**[Subgoal 4: Cocycle lifting]**
Let `G` be a group with a `MulDistribMulAction` of a finite group `A` and let `F = G ^* A`.
Suppose that for a given `x : G` we have `∀ a : A, x⁻¹ * (a • x) ∈ F`. Then there exists `f ∈ F`
such that `x f⁻¹ ∈ F`, i.e. `x ∈ F`.

This is a cohomological vanishing statement: the 1‑cocycle `a ↦ x⁻¹ * (a • x)` is a coboundary.

**Status**: Pending
**Integration**: Used to lift the centralizer condition from `G/Z` to `G`.
-/
lemma CFSG.mem_fixedPointSubgroup_of_cocycle_condition {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (x : G) (hx : ∀ a : A, x⁻¹ * (a • x) ∈ fixedPointSubgroup A G) :
    x ∈ fixedPointSubgroup A G := by
  let F := fixedPointSubgroup A G
  have hFcard : Nat.card F ∣ Nat.card G := Subgroup.card_subgroup_dvd_card F
  have hcoprimeF : Nat.Coprime (Nat.card A) (Nat.card F) :=
    hcoprime.of_dvd_right hFcard
  have hF_fixed (f : F) (a : A) : a • (f : G) = (f : G) := by
    have hmem := (FixedPoints.mem_subgroup (M := A) (a := (f : G))).mp f.2
    exact hmem a
  -- define ψ : A → F
  let ψ : A → F := fun a => ⟨x⁻¹ * (a • x), hx a⟩
  have ψ_one : ψ 1 = 1 := by
    ext
    simp [ψ]
  have ψ_mul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    ext
    dsimp [ψ]
    have h := hF_fixed ⟨x⁻¹ * (b • x), hx b⟩ a
    calc
      x⁻¹ * ((a * b) • x) = x⁻¹ * (a • (b • x)) := by rw [mul_smul]
      _ = x⁻¹ * (a • x) * (a • x)⁻¹ * (a • (b • x)) := by group
      _ = (x⁻¹ * (a • x)) * ((a • x)⁻¹ * (a • (b • x))) := by group
      _ = (x⁻¹ * (a • x)) * (a • (x⁻¹ * (b • x))) := by
        simp [smul_mul', smul_inv']
      _ = (x⁻¹ * (a • x)) * (x⁻¹ * (b • x)) := by rw [h]
      _ = (x⁻¹ * (a • x)) * (x⁻¹ * (b • x)) := rfl
  -- ψ is a monoid homomorphism
  let ψ_hom : A →* F :=
    { toFun := ψ
      map_one' := ψ_one
      map_mul' := ψ_mul }
  have horder : ∀ a, orderOf (ψ a) ∣ Nat.card A := by
    intro a
    have h1 : orderOf (ψ_hom a) ∣ orderOf a := orderOf_map_dvd ψ_hom a
    have h2 : orderOf a ∣ Nat.card A := orderOf_dvd_natCard a
    exact dvd_trans h1 h2
  have horder' : ∀ a, orderOf (ψ a) ∣ Nat.card F := by
    intro a
    exact orderOf_dvd_natCard (ψ a)
  have horder_coprime : ∀ a, orderOf (ψ a) = 1 := by
    intro a
    have hdvd : orderOf (ψ a) ∣ Nat.gcd (Nat.card A) (Nat.card F) :=
      Nat.dvd_gcd (horder a) (horder' a)
    have hgcd : Nat.gcd (Nat.card A) (Nat.card F) = 1 :=
      Nat.Coprime.gcd_eq_one hcoprimeF
    rw [hgcd] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  have hψ_triv : ∀ a, ψ a = 1 := by
    intro a
    have horder1 : orderOf (ψ a) = 1 := horder_coprime a
    exact orderOf_eq_one_iff.mp horder1
  intro a
  have h := hψ_triv a
  dsimp [ψ] at h
  have h' : (ψ a : G) = 1 := congr_arg Subtype.val h
  dsimp [ψ] at h'
  -- h' : x⁻¹ * (a • x) = 1
  calc
    a • x = x := by
      calc
        a • x = x * (x⁻¹ * a • x) := by group
        _ = x * 1 := by rw [h']
        _ = x := by simp


/-**
**[Trivial action on centre]**
Assuming the hypotheses of Proposition 1.10, the action of `A` on the centre `Z(G)` is trivial.

**Status**: Pending
**Integration**: Used to apply the base case to the centre.
-/
lemma CFSG.actsTrivially_center_of_nilpotent_coprime_centralizer_condition {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hnil : Group.IsNilpotent G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (hC : Subgroup.centralizer (fixedPointSubgroup A G : Set G) ≤ fixedPointSubgroup A G) :
    ActsTrivially (A := A) (G := Subgroup.center G) := by
  have hZ_centralizer : Subgroup.center G ≤ Subgroup.centralizer ((fixedPointSubgroup A G ⊓ Subgroup.center G) : Set G) := by
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    rcases hx with ⟨hxF, hxZ⟩
    exact (eq_comm.mpr (Subgroup.mem_center_iff.mp hxZ z))
  have hZ_le_F : Subgroup.center G ≤ fixedPointSubgroup A G := by
    intro z hz
    have hz' : z ∈ Subgroup.centralizer ((fixedPointSubgroup A G ⊓ Subgroup.center G) : Set G) ⊓ Subgroup.center G := by
      exact ⟨hZ_centralizer hz, hz⟩
    have hz'' := centralizer_inf_center_le_fixedPoint_inf_center hnil hcoprime hC hz'
    exact hz''.1
  intro a z
  have hzF : (z : G) ∈ fixedPointSubgroup A G := hZ_le_F z.2
  have hfix := (FixedPoints.mem_subgroup (M := A) (a := (z : G))).mp hzF a
  exact Subtype.ext hfix


/-**
**[Trivial action from trivial actions on centre and quotient]**
If `A` acts trivially on `Z(G)` and on `G/Z(G)`, and `|A|` is coprime to `|G|`, then `A` acts trivially on `G`.

**Status**: Pending
**Integration**: Used in the induction step.
-/
lemma CFSG.actsTrivially_of_center_and_quotient {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hZtriv : ActsTrivially (A := A) (G := Subgroup.center G))
    (hQtriv : ActsTrivially (A := A) (G := G ⧸ Subgroup.center G))
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    ActsTrivially (A := A) (G := G) := by
  have hZ_le_F : Subgroup.center G ≤ fixedPointSubgroup A G := by
    intro z hz
    exact (FixedPoints.mem_subgroup (M := A) (a := (z : G))).mpr fun a' => by
      have h := hZtriv a' ⟨z, hz⟩
      have h' := congr_arg Subtype.val h
      have hcoe : ((a' • ⟨z, hz⟩ : Subgroup.center G) : G) = a' • z := rfl
      rwa [hcoe] at h'
  have h_mem_center : ∀ (a : A) (g : G), (a • g) * g⁻¹ ∈ Subgroup.center G := by
    intro a g
    have h := hQtriv a (QuotientGroup.mk g)
    have h' : QuotientGroup.mk ((a • g) * g⁻¹) = (1 : G ⧸ Subgroup.center G) := by
      calc
        QuotientGroup.mk ((a • g) * g⁻¹) = QuotientGroup.mk (a • g) * (QuotientGroup.mk g)⁻¹ := by simp
        _ = (a • QuotientGroup.mk g) * (QuotientGroup.mk g)⁻¹ := by simp
        _ = (QuotientGroup.mk g) * (QuotientGroup.mk g)⁻¹ := by rw [h]
        _ = (1 : G ⧸ Subgroup.center G) := by simp
    rwa [QuotientGroup.eq_one_iff] at h'
  intro a g
  have hz' := h_mem_center a g
  have h_cond : ∀ a' : A, g⁻¹ * (a' • g) ∈ fixedPointSubgroup A G := by
    intro a'
    have hz'' := h_mem_center a' g
    have h_comm : ((a' • g) * g⁻¹) * g = g * ((a' • g) * g⁻¹) :=
      (Subgroup.mem_center_iff.mp hz'' g).symm
    have h_eq1 : a' • g = ((a' • g) * g⁻¹) * g := by group
    have h_comm' : g⁻¹ * ((a' • g) * g⁻¹) = ((a' • g) * g⁻¹) * g⁻¹ :=
      Subgroup.mem_center_iff.mp hz'' g⁻¹
    have eq : g⁻¹ * (a' • g) = (a' • g) * g⁻¹ := by
      calc
        g⁻¹ * (a' • g) = g⁻¹ * (((a' • g) * g⁻¹) * g) := by
          conv_lhs => arg 2; rw [h_eq1]
        _ = (g⁻¹ * ((a' • g) * g⁻¹)) * g := by group
        _ = (((a' • g) * g⁻¹) * g⁻¹) * g := by rw [h_comm']
        _ = ((a' • g) * g⁻¹) * (g⁻¹ * g) := by group
        _ = ((a' • g) * g⁻¹) * 1 := by simp
        _ = (a' • g) * g⁻¹ := by simp
    rw [eq]
    exact hZ_le_F hz''
  have hg : g ∈ fixedPointSubgroup A G :=
    mem_fixedPointSubgroup_of_cocycle_condition hcoprime g h_cond
  exact (FixedPoints.mem_subgroup (M := A) (a := g)).mp hg a

section CommutatorLemmas

variable {G : Type*} [Group G]

/-- The identity `⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆`. -/
public lemma CFSG.commutator_mul_left (a b c : G) : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  group

/-- `⁅x⁻¹, f⁆ = x⁻¹ * ⁅x, f⁆⁻¹ * x`. -/
public lemma CFSG.commutator_inv_eq_conjugate (x f : G) : ⁅x⁻¹, f⁆ = x⁻¹ * ⁅x, f⁆⁻¹ * x := by
  group

/-- The identity `⁅a, b * c⁆ = ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹`. -/
public lemma CFSG.commutator_mul_right (a b c : G) : ⁅a, b * c⁆ = ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ := by
  group

/-- The identity `⁅a, b⁻¹⁆ = b⁻¹ * ⁅a, b⁆⁻¹ * b`. -/
public lemma CFSG.commutator_inv_right (a b : G) : ⁅a, b⁻¹⁆ = b⁻¹ * ⁅a, b⁆⁻¹ * b := by
  group

/-- If `⁅a • x, f⁆ = ⁅x, f⁆`, then `⁅x⁻¹ * (a • x), f⁆ = 1`. -/
lemma CFSG.commutator_inv_mul_of_central_special (x f a : G)
    (heq : ⁅a • x, f⁆ = ⁅x, f⁆) : ⁅x⁻¹ * (a • x), f⁆ = 1 := by
  calc
    ⁅x⁻¹ * (a • x), f⁆ = x⁻¹ * ⁅a • x, f⁆ * (x⁻¹)⁻¹ * ⁅x⁻¹, f⁆ := by rw [commutator_mul_left]
    _ = x⁻¹ * ⁅a • x, f⁆ * x * ⁅x⁻¹, f⁆ := by simp
    _ = x⁻¹ * ⁅x, f⁆ * x * ⁅x⁻¹, f⁆ := by rw [heq]
    _ = x⁻¹ * ⁅x, f⁆ * x * (x⁻¹ * ⁅x, f⁆⁻¹ * x) := by rw [commutator_inv_eq_conjugate]
    _ = (x⁻¹ * ⁅x, f⁆ * x) * (x⁻¹ * ⁅x, f⁆⁻¹ * x) := by group
    _ = x⁻¹ * ⁅x, f⁆ * (x * x⁻¹) * ⁅x, f⁆⁻¹ * x := by group
    _ = x⁻¹ * ⁅x, f⁆ * 1 * ⁅x, f⁆⁻¹ * x := by simp
    _ = x⁻¹ * ⁅x, f⁆ * ⁅x, f⁆⁻¹ * x := by simp
    _ = x⁻¹ * (⁅x, f⁆ * ⁅x, f⁆⁻¹) * x := by group
    _ = x⁻¹ * 1 * x := by rw [mul_inv_cancel]
    _ = 1 := by simp

end CommutatorLemmas

/-- **[Centralizer condition on quotient]**
Assuming the hypotheses of Proposition 1.10, the centralizer condition also holds for the induced
action of `A` on `G ⧸ Z(G)`. -/
lemma CFSG.centralizer_condition_on_center_quotient {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hnil : Group.IsNilpotent G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (hC : Subgroup.centralizer (fixedPointSubgroup A G : Set G) ≤ fixedPointSubgroup A G) :
    Subgroup.centralizer (fixedPointSubgroup A (G ⧸ Subgroup.center G) : Set (G ⧸ Subgroup.center G)) ≤
      fixedPointSubgroup A (G ⧸ Subgroup.center G) := by
  intro xbar hxbar
  have hZtriv : ActsTrivially (A := A) (G := Subgroup.center G) :=
    actsTrivially_center_of_nilpotent_coprime_centralizer_condition hnil hcoprime hC
  let π : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  have hπ_surj : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨x, hx⟩ := hπ_surj xbar
  have hxbar_centralizer : π x ∈ Subgroup.centralizer (fixedPointSubgroup A (G ⧸ Subgroup.center G) : Set (G ⧸ Subgroup.center G)) := by
    rw [hx]
    exact hxbar
  have hF : fixedPointSubgroup A G ≤ Subgroup.comap π (fixedPointSubgroup A (G ⧸ Subgroup.center G)) := by
    intro f hf
    have hf' : ∀ a, a • (f : G) = f := (FixedPoints.mem_subgroup (M := A) (a := f)).mp hf
    apply (FixedPoints.mem_subgroup (M := A) (a := π f)).mpr
    intro a
    simp [π, hf' a]
  have h_comm' : ∀ f ∈ fixedPointSubgroup A G, ⁅x, f⁆ ∈ Subgroup.center G := by
    intro f hf
    have hfxbar : π f ∈ fixedPointSubgroup A (G ⧸ Subgroup.center G) :=
      (Subgroup.mem_comap (f := π)).mp (hF hf)
    have hcomm := Subgroup.mem_centralizer_iff.mp hxbar_centralizer (π f) hfxbar
    rw [← QuotientGroup.eq_one_iff]
    calc
      π ⁅x, f⁆ = π (x * f * x⁻¹ * f⁻¹) := rfl
      _ = π x * π f * (π x)⁻¹ * (π f)⁻¹ := by simp [π, map_mul, map_inv]
      _ = (π x * π f) * (π x)⁻¹ * (π f)⁻¹ := by group
      _ = (π f * π x) * (π x)⁻¹ * (π f)⁻¹ := by rw [hcomm]
      _ = π f * (π x * (π x)⁻¹) * (π f)⁻¹ := by group
      _ = π f * 1 * (π f)⁻¹ := by simp
      _ = π f * (π f)⁻¹ := by simp
      _ = 1 := by simp
  have h_eq : ∀ a : A, ∀ f ∈ fixedPointSubgroup A G, ⁅a • x, f⁆ = ⁅x, f⁆ := by
    intro a f hf
    have hz := h_comm' f hf
    have hZtriv' := hZtriv a ⟨⁅x, f⁆, hz⟩
    have hZtriv'' : a • (⁅x, f⁆) = ⁅x, f⁆ := by
      have hcoe : ((a • ⟨⁅x, f⁆, hz⟩ : Subgroup.center G) : G) = a • ⁅x, f⁆ := rfl
      have hZtriv_val := congr_arg Subtype.val hZtriv'
      rwa [hcoe] at hZtriv_val
    calc
      ⁅a • x, f⁆ = a • ⁅x, f⁆ := by
        have haf : a • f = f := (FixedPoints.mem_subgroup (M := A) (a := f)).mp hf a
        calc
          ⁅a • x, f⁆ = ⁅a • x, a • f⁆ := by simp [haf]
          _ = a • ⁅x, f⁆ := by simp [commutatorElement_def]
      _ = ⁅x, f⁆ := hZtriv''
  have h_cocycle : ∀ a : A, x⁻¹ * (a • x) ∈ fixedPointSubgroup A G := by
    intro a
    have h' : x⁻¹ * (a • x) ∈ Subgroup.centralizer (fixedPointSubgroup A G : Set G) := by
      refine Subgroup.mem_centralizer_iff_commutator_eq_one.mpr fun f hf => ?_
      let a' : G := (a • x) * x⁻¹
      have ha'_smul : a' • x = a • x := by
        simp [a']
      have h_eq' : ⁅a' • x, f⁆ = ⁅x, f⁆ := by
        rw [ha'_smul, h_eq a f hf]
      have h1 := commutator_inv_mul_of_central_special x f a' h_eq'
      have h1' : ⁅x⁻¹ * (a • x), f⁆ = 1 := by
        rwa [ha'_smul] at h1
      calc
        f * (x⁻¹ * a • x) * f⁻¹ * (x⁻¹ * a • x)⁻¹ = ⁅f, x⁻¹ * a • x⁆ := by rw [commutatorElement_def]
        _ = (⁅x⁻¹ * a • x, f⁆)⁻¹ := by rw [commutatorElement_inv]
        _ = 1⁻¹ := by rw [h1']
        _ = 1 := by simp
    exact hC h'
  have hx_F : x ∈ fixedPointSubgroup A G :=
    mem_fixedPointSubgroup_of_cocycle_condition hcoprime x h_cocycle
  have hxbar_F : π x ∈ fixedPointSubgroup A (G ⧸ Subgroup.center G) :=
    (Subgroup.mem_comap (f := π)).mp (hF hx_F)
  rw [← hx]
  exact hxbar_F


/-
**Kind**: Theorem
**Note**: Proposition 1.10
**Stmt**:
Let $G$ be a finite nilpotent group.
Let $A$ be an operator group on $G$ with $gcd(|A|, |G|) = 1$.
Let $C = C_G(A)$.
If $C_G(C) \subset C$, then $A$ acts trivially on $G$.
-/

public theorem CFSG.actsTrivially_of_nilpotent_coprime_and_centralizer_fixedPointSubgroup {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hnil : Group.IsNilpotent G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (hC : Subgroup.centralizer (fixedPointSubgroup A G : Set G) ≤ fixedPointSubgroup A G) :
    ActsTrivially (A := A) (G := G) := by
  let P : ∀ (G' : Type _) [Group G'] [Group.IsNilpotent G'], Prop :=
    fun G' _ _ => ∀ [MulDistribMulAction A G'] [Finite G'], Nat.Coprime (Nat.card A) (Nat.card G') →
      (Subgroup.centralizer (fixedPointSubgroup A G' : Set G') ≤ fixedPointSubgroup A G') →
      ActsTrivially (A := A) (G := G')
  refine (Group.nilpotent_center_quotient_ind (P := P) G ?_ ?_) hcoprime hC
  · intro G' _ hsub
    haveI : Subsingleton G' := hsub
    intro hact hfin hcoprime' hC' a g
    have : g = (1 : G') := Subsingleton.elim g 1
    subst this
    simp
  · intro G' _ hnil hquot hact hfin hcoprime' hC'
    -- hact and hfin are the implicit instances for MulDistribMulAction and Finite
    haveI : (Subgroup.center G').Normal := inferInstance
    have hZtriv : ActsTrivially (A := A) (G := Subgroup.center G') :=
      actsTrivially_center_of_nilpotent_coprime_centralizer_condition (G := G') hnil hcoprime' hC'
    have hcoprime_quot : Nat.Coprime (Nat.card A) (Nat.card (G' ⧸ Subgroup.center G')) :=
      hcoprime'.of_dvd_right (Subgroup.card_quotient_dvd_card (Subgroup.center G'))
    haveI : Finite (G' ⧸ Subgroup.center G') := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
    have hCquot : Subgroup.centralizer (fixedPointSubgroup A (G' ⧸ Subgroup.center G') : Set (G' ⧸ Subgroup.center G')) ≤
        fixedPointSubgroup A (G' ⧸ Subgroup.center G') :=
      centralizer_condition_on_center_quotient hnil hcoprime' hC'
    haveI : Group.IsNilpotent (G' ⧸ Subgroup.center G') := inferInstance
    have hQtriv : ActsTrivially (A := A) (G := G' ⧸ Subgroup.center G') :=
      hquot hcoprime_quot hCquot
    exact actsTrivially_of_center_and_quotient (G := G') hZtriv hQtriv hcoprime'

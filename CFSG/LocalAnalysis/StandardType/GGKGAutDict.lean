module

public import CFSG.LocalAnalysis.StandardType.GGKGAdjDefs
public import CFSG.LocalAnalysis.StandardType.GGKGWeylRootFacts
public import CFSG.LocalAnalysis.StandardType.GGKGWeylReflCore

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure KGAutFrame {L' : Type} [Group L'] (A : Subgroup (MulAut L'))
    (κ : A →* Multiplicative (Fin 6 → ZMod 3)) : Prop where
  card_eq : Nat.card A = 3 ^ 5
  injective : Function.Injective κ
  range_iff : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ hypE6
  weyl : ∀ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) →
    ∃ u : WeylGroup Tag.E6, ∀ a b : A,
      (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
        Multiplicative.toAdd (κ b) = adAct Tag.E6 3 u (Multiplicative.toAdd (κ a))
  simple : ∀ i : Fin 6, ∃ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
    ∀ a b : A, (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
      Multiplicative.toAdd (κ b) = adRefl Tag.E6 3 i (Multiplicative.toAdd (κ a))

namespace KGAutFrame

variable {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
  {κ : A →* Multiplicative (Fin 6 → ZMod 3)}

private noncomputable def coord (κ : A →* Multiplicative (Fin 6 → ZMod 3)) (a : A) :
    Fin Tag.E6.rank → ZMod 3 :=
  Multiplicative.toAdd (κ a)

private lemma kappa_eq_of_coord_eq {x y : A} (h : coord κ x = coord κ y) : κ x = κ y := by
  rw [← ofAdd_toAdd (κ x), ← ofAdd_toAdd (κ y)]
  exact congrArg Multiplicative.ofAdd h

private lemma zmod3_ne_zero (t : ZMod 3) (ht : t ≠ 0) : t = 1 ∨ t = -1 := by
  have h : ∀ s : ZMod 3, s ≠ 0 → s = 1 ∨ s = -1 := by decide
  exact h t ht

theorem toAdd_mem_hypE6 (hF : KGAutFrame A κ) (a : A) :
    Multiplicative.toAdd (κ a) ∈ hypE6 := by
  exact (hF.range_iff _).1 (by rw [ofAdd_toAdd]; exact ⟨a, rfl⟩)

theorem exists_of_mem_hypE6 (hF : KGAutFrame A κ) {x : Fin 6 → ZMod 3} (hx : x ∈ hypE6) :
    ∃ a : A, Multiplicative.toAdd (κ a) = x := by
  obtain ⟨a, ha⟩ := (hF.range_iff x).2 hx
  exact ⟨a, by rw [ha]; exact toAdd_ofAdd x⟩

private theorem coord_mem (hF : KGAutFrame A κ) (a : A) : coord κ a ∈ hypE6 :=
  toAdd_mem_hypE6 hF a

private theorem coord_exists (hF : KGAutFrame A κ) {x : Fin Tag.E6.rank → ZMod 3}
    (hx : x ∈ hypE6) : ∃ a : A, coord κ a = x := by
  obtain ⟨a, ha⟩ := exists_of_mem_hypE6 hF hx
  exact ⟨a, ha⟩

theorem exists_weyl_of_mem (hF : KGAutFrame A κ) {φ : MulAut ↥A} (hφ : φ ∈ ggTorusAut A) :
    ∃ u : WeylGroup Tag.E6, ∀ a : A,
      Multiplicative.toAdd (κ (φ a)) = adAct Tag.E6 3 u (Multiplicative.toAdd (κ a)) := by
  obtain ⟨g, hgH, hgN, hg⟩ := (mem_ggAutomizer_iff.1 hφ :
    ∃ g ∈ (MulAut.conj : L' →* MulAut L').range,
      g ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
        ∀ b : A, ((φ b : A) : MulAut L') = g * b * g⁻¹)
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 hgH
  have hgN' : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [hm]; exact hgN
  obtain ⟨u, hu⟩ := hF.weyl m hgN'
  refine ⟨u, fun a => hu a (φ a) ?_⟩
  rw [hg a, hm]

private theorem coord_weyl (hF : KGAutFrame A κ) {φ : MulAut ↥A} (hφ : φ ∈ ggTorusAut A) :
    ∃ u : WeylGroup Tag.E6, ∀ a : A, coord κ (φ a) = adAct Tag.E6 3 u (coord κ a) :=
  exists_weyl_of_mem hF hφ

private theorem coord_mul (x y : A) : coord κ (x * y) = coord κ x + coord κ y :=
  (congrArg Multiplicative.toAdd (map_mul κ x y)).trans (toAdd_mul (κ x) (κ y))

private theorem coord_inv (x : A) : coord κ x⁻¹ = -coord κ x :=
  (congrArg Multiplicative.toAdd (map_inv κ x)).trans (toAdd_inv (κ x))

private theorem coord_zpow (x : A) (n : ℤ) : coord κ (x ^ n) = n • coord κ x :=
  (congrArg Multiplicative.toAdd (map_zpow κ x n)).trans (toAdd_zpow (κ x) n)

theorem exists_mem_of_weyl (hF : KGAutFrame A κ) (u : WeylGroup Tag.E6) :
    ∃ φ ∈ ggTorusAut A, ∀ a : A,
      Multiplicative.toAdd (κ (φ a)) = adAct Tag.E6 3 u (Multiplicative.toAdd (κ a)) := by
  change ∃ φ ∈ ggTorusAut A, ∀ a : A, coord κ (φ a) = adAct Tag.E6 3 u (coord κ a)
  induction u using (coxeterSystem Tag.E6).simple_induction_left with
  | one =>
    refine ⟨1, Subgroup.one_mem _, fun a => ?_⟩
    rw [MulAut.one_apply, adAct_one]
  | mul_simple_left w i ih =>
    obtain ⟨φ, hφ, hih⟩ := ih
    obtain ⟨m, hmN, hm⟩ := hF.simple i
    have hψmem : ggConjAut A hmN ∈ ggTorusAut A :=
      ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range) (Bs := A)
        (MonoidHom.mem_range.2 ⟨m, rfl⟩) hmN
    have hψa : ∀ a : A, coord κ (ggConjAut A hmN a) = adRefl Tag.E6 3 i (coord κ a) :=
      fun a => hm a (ggConjAut A hmN a) (ggConjAut_apply A hmN a)
    refine ⟨ggConjAut A hmN * φ, Subgroup.mul_mem _ hψmem hφ, fun a => ?_⟩
    rw [MulAut.mul_apply, adAct_mul, ← hih a, hψa (φ a), adAct_simple]

private theorem coord_of_weyl (hF : KGAutFrame A κ) (u : WeylGroup Tag.E6) :
    ∃ φ ∈ ggTorusAut A, ∀ a : A, coord κ (φ a) = adAct Tag.E6 3 u (coord κ a) :=
  exists_mem_of_weyl hF u


private theorem reflection_data (hF : KGAutFrame A κ) {φ : MulAut ↥A}
    (hφ : φ ∈ ggTorusAut A) (hrefl : GGIsReflection 3 φ) {c : A} (hc : GGReflCentre φ c) :
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧
      (∀ a : A, coord κ (φ a) = rootRefl γ (coord κ a)) ∧
      (coord κ c = kgExpVec γ ∨ coord κ c = kgExpVec (-γ)) := by
  obtain ⟨u, hu⟩ := coord_weyl hF hφ
  have hsq : ∀ x ∈ hypE6, adAct Tag.E6 3 u (adAct Tag.E6 3 u x) = x := by
    intro x hx
    obtain ⟨a, ha⟩ := coord_exists hF hx
    have h2 : φ (φ a) = a := by
      have := congrArg (fun e : MulAut ↥A => e a) hrefl.1
      simpa [pow_two, MulAut.mul_apply, MulAut.one_apply] using this
    calc adAct Tag.E6 3 u (adAct Tag.E6 3 u x)
        = adAct Tag.E6 3 u (adAct Tag.E6 3 u (coord κ a)) := by rw [← ha]
      _ = adAct Tag.E6 3 u (coord κ (φ a)) := by rw [hu a]
      _ = coord κ (φ (φ a)) := by rw [← hu (φ a)]
      _ = coord κ a := by rw [h2]
      _ = x := ha
  have hcard : Nat.card {b : A // φ b = b} =
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ adAct Tag.E6 3 u x = x} := by
    let f : {b : A // φ b = b} →
        {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ adAct Tag.E6 3 u x = x} :=
      fun b => ⟨coord κ b.1, coord_mem hF b.1, by
        have h := congrArg (fun z : A => coord κ z) b.2
        rw [← hu b.1]
        exact h⟩
    apply Nat.card_eq_of_bijective f
    constructor
    · intro b1 b2 h
      apply Subtype.ext
      apply hF.injective
      apply kappa_eq_of_coord_eq
      change coord κ b1.1 = coord κ b2.1
      exact congrArg Subtype.val h
    · intro x
      obtain ⟨a, ha⟩ := coord_exists hF x.2.1
      have hφa : φ a = a := by
        apply hF.injective
        apply kappa_eq_of_coord_eq
        calc coord κ (φ a) = adAct Tag.E6 3 u (coord κ a) := hu a
          _ = adAct Tag.E6 3 u x.1 := by rw [ha]
          _ = x.1 := x.2.2
          _ = coord κ a := ha.symm
      refine ⟨⟨a, hφa⟩, ?_⟩
      apply Subtype.ext
      change coord κ a = x.1
      exact ha
  have hfix : Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ adAct Tag.E6 3 u x = x} * 3 =
      3 ^ 5 := by
    rw [← hcard, hrefl.2, hF.card_eq]
  obtain ⟨γ, hγ, hγact⟩ := exists_root_of_isRefl u hsq hfix
  have hroot : ∀ a : A, coord κ (φ a) = rootRefl γ (coord κ a) := by
    intro a
    rw [hu a, hγact (coord κ a) (coord_mem hF a)]
  refine ⟨γ, hγ, hroot, ?_⟩
  obtain ⟨x, hx, hpx⟩ := exists_rootPair_ne_zero hγ
  obtain ⟨b, hb⟩ := coord_exists hF hx
  have hpne : rootPair γ (coord κ b) ≠ 0 := by rw [hb]; exact hpx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hc b)
  have hL : coord κ (φ b * b⁻¹) = (-rootPair γ (coord κ b)) • kgExpVec γ := by
    rw [coord_mul, coord_inv, hroot b, rootRefl, neg_smul]
    abel
  have hg : coord κ (c ^ n) = n • coord κ c := coord_zpow c n
  have heq : (-rootPair γ (coord κ b)) • kgExpVec γ = n • coord κ c := by
    rw [← hL, ← hn]
    exact hg
  have heqZ : (-rootPair γ (coord κ b)) • kgExpVec γ = (n : ZMod 3) • coord κ c := by
    rw [Int.cast_smul_eq_zsmul]
    exact heq
  have hLne : (-rootPair γ (coord κ b)) • kgExpVec γ ≠ 0 :=
    smul_ne_zero (neg_ne_zero.mpr hpne) (kgExpVec_ne_zero hγ)
  have hbWne : (n : ZMod 3) • coord κ c ≠ 0 := by rw [← heqZ]; exact hLne
  have hbne : (n : ZMod 3) ≠ 0 := left_ne_zero_of_smul hbWne
  have hWne : coord κ c ≠ 0 := right_ne_zero_of_smul hbWne
  have hbW : (n : ZMod 3)⁻¹ • ((n : ZMod 3) • coord κ c) = coord κ c := by
    rw [← mul_smul, inv_mul_cancel₀ hbne, one_smul]
  have hWt : coord κ c = ((n : ZMod 3)⁻¹ * (-rootPair γ (coord κ b))) • kgExpVec γ := by
    calc coord κ c = (n : ZMod 3)⁻¹ • ((n : ZMod 3) • coord κ c) := hbW.symm
      _ = (n : ZMod 3)⁻¹ • ((-rootPair γ (coord κ b)) • kgExpVec γ) := by rw [← heqZ]
      _ = ((n : ZMod 3)⁻¹ * (-rootPair γ (coord κ b))) • kgExpVec γ := by rw [← mul_smul]
  have ht : ((n : ZMod 3)⁻¹ * (-rootPair γ (coord κ b))) = 1 ∨
      ((n : ZMod 3)⁻¹ * (-rootPair γ (coord κ b))) = -1 := by
    apply zmod3_ne_zero
    intro h0
    exact hWne (by rw [hWt, h0, zero_smul])
  rcases ht with ht | ht
  · left
    rw [hWt, ht, one_smul]
  · right
    rw [hWt, ht, neg_one_smul (ZMod 3) (kgExpVec γ), kgExpVec_neg]

private theorem reflection_root_data (hF : KGAutFrame A κ) {φ : MulAut ↥A}
    (hφ : φ ∈ ggTorusAut A) (hrefl : GGIsReflection 3 φ) {c : A} (hc : GGReflCentre φ c) :
    ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ coord κ c = kgExpVec α ∧
      (∀ a : A, coord κ (φ a) = rootRefl α (coord κ a)) := by
  obtain ⟨γ, hγ, hact, hcen⟩ := reflection_data hF hφ hrefl hc
  rcases hcen with h | h
  · exact ⟨γ, hγ, h, hact⟩
  · refine ⟨-γ, IsRoot.neg hγ, h, fun a => ?_⟩
    rw [hact a, rootRefl_neg]

theorem exists_reflection (hF : KGAutFrame A κ) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ∃ φ ∈ ggTorusAut A, GGIsReflection 3 φ ∧
      (∀ a : A, Multiplicative.toAdd (κ (φ a)) = rootRefl γ (Multiplicative.toAdd (κ a))) ∧
      ∀ c : A, Multiplicative.toAdd (κ c) = kgExpVec γ → GGReflCentre φ c := by
  change ∃ φ ∈ ggTorusAut A, GGIsReflection 3 φ ∧
      (∀ a : A, coord κ (φ a) = rootRefl γ (coord κ a)) ∧
      ∀ c : A, coord κ c = kgExpVec γ → GGReflCentre φ c
  obtain ⟨φ, hφ, hact⟩ := coord_of_weyl hF (rootReflection γ)
  have hroot : ∀ a : A, coord κ (φ a) = rootRefl γ (coord κ a) := by
    intro a
    rw [hact a, adAct_rootReflection_eq_rootRefl hγ]
  have hsq : φ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro a
    apply hF.injective
    apply kappa_eq_of_coord_eq
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    change coord κ (φ (φ a)) = coord κ a
    calc coord κ (φ (φ a)) = rootRefl γ (coord κ (φ a)) := hroot (φ a)
      _ = rootRefl γ (rootRefl γ (coord κ a)) := by rw [hroot a]
      _ = coord κ a := rootRefl_rootRefl hγ _
  refine ⟨φ, hφ, ⟨hsq, ?_⟩, hroot, ?_⟩
  · let f : {b : A // φ b = b} →
        {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ rootRefl γ x = x} :=
      fun b => ⟨coord κ b.1, coord_mem hF b.1, by
        have h := congrArg (fun z : A => coord κ z) b.2
        rw [← hroot b.1]
        exact h⟩
    have hcard : Nat.card {b : A // φ b = b} =
        Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ rootRefl γ x = x} := by
      apply Nat.card_eq_of_bijective f
      constructor
      · intro b1 b2 h
        apply Subtype.ext
        apply hF.injective
        apply kappa_eq_of_coord_eq
        change coord κ b1.1 = coord κ b2.1
        exact congrArg Subtype.val h
      · intro x
        obtain ⟨a, ha⟩ := coord_exists hF x.2.1
        have hφa : φ a = a := by
          apply hF.injective
          apply kappa_eq_of_coord_eq
          calc coord κ (φ a) = rootRefl γ (coord κ a) := hroot a
            _ = rootRefl γ x.1 := by rw [ha]
            _ = x.1 := x.2.2
            _ = coord κ a := ha.symm
        refine ⟨⟨a, hφa⟩, ?_⟩
        apply Subtype.ext
        change coord κ a = x.1
        exact ha
    rw [hcard, card_fix_rootRefl hγ, hF.card_eq]
    norm_num
  · intro c hc b
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(((-rootPair γ (coord κ b)).val : ℕ) : ℤ), ?_⟩
    have hk : coord κ (c ^ (((-rootPair γ (coord κ b)).val : ℕ) : ℤ)) =
        (-rootPair γ (coord κ b)) • kgExpVec γ := by
      rw [coord_zpow, hc, ← Int.cast_smul_eq_zsmul (ZMod 3)]
      congr 1
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hL : coord κ (φ b * b⁻¹) = (-rootPair γ (coord κ b)) • kgExpVec γ := by
      rw [coord_mul, coord_inv, hroot b, rootRefl, neg_smul]
      abel
    apply hF.injective
    apply kappa_eq_of_coord_eq
    change coord κ (c ^ (((-rootPair γ (coord κ b)).val : ℕ) : ℤ)) = coord κ (φ b * b⁻¹)
    exact hk.trans hL.symm

theorem corootPt (hF : KGAutFrame A κ) {c : A} (hc : GGCorootPt 3 (ggTorusAut A) c) :
    ∃ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β ∧ Multiplicative.toAdd (κ c) = kgExpVec β := by
  obtain ⟨-, φ, hφ, hrefl, hcc⟩ := hc
  obtain ⟨α, hα, hαc, -⟩ := reflection_root_data hF hφ hrefl hcc
  exact ⟨α, hα, hαc⟩

theorem corootOrth (hF : KGAutFrame A κ) {a b : A} (h : GGCorootOrth 3 (ggTorusAut A) a b) :
    ∃ α β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ IsRoot Tag.E6 β ∧ iform α β = 0 ∧
      Multiplicative.toAdd (κ a) = kgExpVec α ∧ Multiplicative.toAdd (κ b) = kgExpVec β := by
  obtain ⟨hne, φ, hφ, ψ, hψ, hr1, hc1, hr2, hc2, hcomm⟩ := h
  obtain ⟨α, hα, haα, hactα⟩ := reflection_root_data hF hφ hr1 hc1
  obtain ⟨β, hβ, hbβ, hactβ⟩ := reflection_root_data hF hψ hr2 hc2
  refine ⟨α, β, hα, hβ, ?_, haα, hbβ⟩
  refine iform_eq_zero_of_commute hα hβ ?_ ?_ ?_
  · intro h1
    exact hne (by
      have hab : a = b := hF.injective (kappa_eq_of_coord_eq (by rw [haα, hbβ, h1]))
      rw [hab])
  · intro h2
    exact hne (by
      have hab : a = b⁻¹ := hF.injective (kappa_eq_of_coord_eq (by
        rw [haα, coord_inv, hbβ, h2]))
      rw [hab, Subgroup.zpowers_inv])
  · intro x hx
    obtain ⟨a₀, ha₀⟩ := coord_exists hF hx
    have hφψ : φ (ψ a₀) = ψ (φ a₀) := by
      have := congrArg (fun e : MulAut ↥A => e a₀) hcomm
      simpa [MulAut.mul_apply] using this
    rw [← ha₀, ← hactβ a₀, ← hactα (ψ a₀), ← hactα a₀, ← hactβ (φ a₀), hφψ]

theorem fixedByCentres (hF : KGAutFrame A κ) {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (hαβ : iform α β = 0) {a b : A}
    (ha : Multiplicative.toAdd (κ a) = kgExpVec α) (hb : Multiplicative.toAdd (κ b) = kgExpVec β)
    {u : A} (hu : u ∈ ggFixedByCentres 3 (ggTorusAut A) {a, b}) :
    Multiplicative.toAdd (κ u) ∈ AddSubgroup.closure {y : Fin Tag.E6.rank → ZMod 3 |
      ∃ γ, IsRoot Tag.E6 γ ∧ iform γ α = 0 ∧ iform γ β = 0 ∧ y = kgExpVec γ} := by
  obtain ⟨φα, hφα, hreflα, hactα, hcenα⟩ := exists_reflection hF hα
  have hca : GGReflCentre φα a := hcenα a ha
  have hfixα : φα u = u := hu φα hφα hreflα ⟨a, by simp, hca⟩
  have h1 : rootPair α (coord κ u) = 0 := by
    apply rootPair_eq_zero_of_rootRefl_eq hα
    calc rootRefl α (coord κ u) = coord κ (φα u) := (hactα u).symm
      _ = coord κ u := by rw [hfixα]
  obtain ⟨φβ, hφβ, hreflβ, hactβ, hcenβ⟩ := exists_reflection hF hβ
  have hcb : GGReflCentre φβ b := hcenβ b hb
  have hfixβ : φβ u = u := hu φβ hφβ hreflβ ⟨b, by simp, hcb⟩
  have h2 : rootPair β (coord κ u) = 0 := by
    apply rootPair_eq_zero_of_rootRefl_eq hβ
    calc rootRefl β (coord κ u) = coord κ (φβ u) := (hactβ u).symm
      _ = coord κ u := by rw [hfixβ]
  have hmem : coord κ u ∈ AddSubgroup.closure {y : Fin Tag.E6.rank → ZMod 3 |
      ∃ γ, IsRoot Tag.E6 γ ∧ iform γ α = 0 ∧ iform γ β = 0 ∧ y = kgExpVec γ} :=
    mem_closure_of_rootPair_eq_zero hα hβ hαβ (coord_mem hF u) h1 h2
  exact hmem

end KGAutFrame

end CFSG.StandardType.KGL

end

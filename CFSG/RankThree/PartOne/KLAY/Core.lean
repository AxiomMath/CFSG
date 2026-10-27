module

public import CFSG.RankThree.PartOne.KLAY.SL2
public import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.LocalCores CFSG.RankThree.PartOne.KFU CFSG.LieType.Chevalley
open scoped Pointwise

section Levi

variable {G₀ : Type} [Group G₀] [Finite G₀]

theorem inSubgroup_perfectResidual_centralizer_eq (M₀ : Subgroup G₀) (b : ↥M₀)
    (T Q' : Subgroup G₀) (hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hTn : T ≤ Subgroup.normalizer (Q' : Set G₀))
    (hQ'b : Q' ≤ Subgroup.centralizer ({(b : G₀)} : Set G₀))
    (hY : ∀ y : ↥M₀, y ∈ Subgroup.centralizer ({b} : Set ↥M₀) →
      (y : G₀) ∈ (T : Set G₀) * (Q' : Set G₀))
    (Q : Subgroup ↥M₀) (hQ : Q.map M₀.subtype = M₀ ⊓ Q') (hQperf : Group.IsPerfect ↥Q) :
    inSubgroup perfectResidual (Subgroup.centralizer ({b} : Set ↥M₀)) = Q := by
  classical
  set C : Subgroup ↥M₀ := Subgroup.centralizer ({b} : Set ↥M₀) with hC
  set S : Subgroup G₀ := T ⊔ Q' with hS
  have hSn : S ≤ Subgroup.normalizer (Q' : Set G₀) := sup_le hTn Subgroup.le_normalizer
  have hN : (Q'.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hSn
  have hSprod : (S : Set G₀) = (T : Set G₀) * (Q' : Set G₀) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTn
  have hQmem : ∀ y : ↥M₀, y ∈ Q ↔ (y : G₀) ∈ Q' := by
    intro y
    constructor
    · intro hy
      have : (y : G₀) ∈ Q.map M₀.subtype := ⟨y, hy, rfl⟩
      rw [hQ] at this
      exact this.2
    · intro hy
      have : (y : G₀) ∈ M₀ ⊓ Q' := ⟨y.2, hy⟩
      rw [← hQ] at this
      obtain ⟨q, hq, hqy⟩ := this
      have : q = y := Subtype.ext hqy
      rwa [← this]
  have hQC : Q ≤ C := by
    intro q hq
    have hq' : (q : G₀) ∈ Q' := (hQmem q).1 hq
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hQ'b hq')
  have hyS : ∀ y : ↥C, (y.1 : G₀) ∈ S := by
    intro y
    have h := hY y.1 y.2
    rw [← hSprod] at h
    exact h
  have hSQ : ∀ x : ↥S, ∃ t ∈ T, ∃ ht : t ∈ S, (⟨t, ht⟩ : ↥S)⁻¹ * x ∈ Q'.subgroupOf S := by
    intro x
    have hx : (x : G₀) ∈ (T : Set G₀) * (Q' : Set G₀) := by
      rw [← hSprod]; exact x.2
    obtain ⟨t, ht, q, hq, hxy⟩ := hx
    refine ⟨t, ht, (show T ≤ S from le_sup_left) ht, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hxy]
    simpa using hq
  have hcomm : ∀ a b : ↥S ⧸ Q'.subgroupOf S, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    obtain ⟨t₁, ht₁, ht₁S, h₁⟩ := hSQ x
    obtain ⟨t₂, ht₂, ht₂S, h₂⟩ := hSQ y
    have e₁ : (QuotientGroup.mk x : ↥S ⧸ Q'.subgroupOf S) = QuotientGroup.mk ⟨t₁, ht₁S⟩ := by
      rw [eq_comm, QuotientGroup.eq]
      exact h₁
    have e₂ : (QuotientGroup.mk y : ↥S ⧸ Q'.subgroupOf S) = QuotientGroup.mk ⟨t₂, ht₂S⟩ := by
      rw [eq_comm, QuotientGroup.eq]
      exact h₂
    rw [e₁, e₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hTcomm t₁ ht₁ t₂ ht₂)
  have : Group.IsSolvable (↥S ⧸ Q'.subgroupOf S) := Group.isSolvable_of_comm hcomm
  let Φ : ↥C →* ↥S ⧸ Q'.subgroupOf S :=
    { toFun := fun y => QuotientGroup.mk ⟨(y.1 : G₀), hyS y⟩
      map_one' := by
        change QuotientGroup.mk (⟨((1 : ↥C).1 : G₀), hyS 1⟩ : ↥S) = 1
        rw [QuotientGroup.eq_one_iff]
        exact Q'.one_mem
      map_mul' := fun y z => by
        rw [← QuotientGroup.mk_mul]
        rfl }
  refine inSubgroup_perfectResidual_eq_of_ker hQC hQperf Φ ?_
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change (QuotientGroup.mk ⟨(y.1 : G₀), hyS y⟩ : ↥S ⧸ Q'.subgroupOf S) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hQmem]

end Levi


section MSide

variable {M : Type} [Group M]

abbrev layerD (bM : M) : Subgroup M :=
  inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))

structure MSide (p g : ℕ) (T₀ : Subgroup M) (bM : M) : Prop where
  quasi : IsQuasisimple ↥(layerD bM)
  center : ¬ p ∣ Nat.card (Subgroup.center ↥(layerD bM))
  card : Nat.card ↥(T₀ ⊓ layerD bM) = p
  upper : ∃ U : Subgroup M, U ≤ layerD bM ∧ IsPGroup 2 ↥U ∧
    T₀ ≤ Subgroup.normalizer (U : Set M) ∧ ∃ u ∈ U, ∃ t ∈ T₀, u * t ≠ t * u
  model : ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ g ∧
    Nonempty (↥(layerD bM) ⧸ Subgroup.center ↥(layerD bM) ≃* SL2 k ⧸ Subgroup.center (SL2 k))

end MSide

section CenterSL2

variable {k : Type} [Field k] [CharP k 2]

theorem card_center_SL_two : Nat.card (Subgroup.center (SL2 k)) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
  have hbot : ∀ z : ↥(Subgroup.center (SL2 k)), z = 1 := by
    intro z
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 z.2
    rw [Fintype.card_fin] at hr
    have hr1 : r = 1 := by
      have h2 : (r - 1) ^ 2 = 0 := by
        have : (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
        rw [this, hr, CharTwo.two_eq_zero, zero_mul, sub_zero]
        exact CharTwo.add_self_eq_zero 1
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
    apply Subtype.ext
    apply Subtype.ext
    rw [← hrz, hr1]
    simp
  exact (hbot a).trans (hbot b).symm

theorem eq_one_of_forall_commute_SL2 {C : SL2 k} (h : ∀ X : SL2 k, X * C = C * X) : C = 1 := by
  have hmem : C ∈ Subgroup.center (SL2 k) := Subgroup.mem_center_iff.2 h
  have h1 := Nat.card_eq_one_iff_unique.1 (card_center_SL_two (k := k))
  exact congrArg Subtype.val (h1.1.elim ⟨C, hmem⟩ ⟨1, Subgroup.one_mem _⟩)

theorem eq_of_mul_eq_mul_of_commute {G H : Type*} [Group G] [Group H] {f : SL2 k →* G}
    {g : H →* G} (hf : Function.Injective f) (hg : Function.Injective g)
    (hc : ∀ A B, Commute (f A) (g B)) {A A' : SL2 k} {B B' : H}
    (h : f A * g B = f A' * g B') : A = A' ∧ B = B' := by
  have h1 : f (A'⁻¹ * A) = g (B' * B⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv]
    calc (f A')⁻¹ * f A = (f A')⁻¹ * (f A * g B) * (g B)⁻¹ := by group
      _ = (f A')⁻¹ * (f A' * g B') * (g B)⁻¹ := by rw [h]
      _ = g B' * (g B)⁻¹ := by group
  have hC : ∀ X : SL2 k, X * (A'⁻¹ * A) = (A'⁻¹ * A) * X := by
    intro X
    apply hf
    have e1 : f (X * (A'⁻¹ * A)) = f X * g (B' * B⁻¹) := by rw [map_mul, h1]
    have e2 : f ((A'⁻¹ * A) * X) = g (B' * B⁻¹) * f X := by rw [map_mul, h1]
    rw [e1, e2]
    exact (hc X (B' * B⁻¹)).eq
  have hA : A'⁻¹ * A = 1 := eq_one_of_forall_commute_SL2 hC
  have hAA : A = A' := by
    rw [inv_mul_eq_one] at hA
    exact hA.symm
  subst hAA
  refine ⟨rfl, hg ?_⟩
  simpa using h

end CenterSL2

section OfTorus

variable {M : Type} [Group M] {k : Type} [Field k] [Finite k] [CharP k 2]


theorem isSimpleGroup_SL_two (h4 : 4 ≤ Nat.card k) : IsSimpleGroup (SL2 k) := by
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := k) le_rfl h4
  have hc : Subgroup.center (SL2 k) = ⊥ := Subgroup.eq_bot_of_card_eq _ card_center_SL_two
  have e : SL2 k ⧸ Subgroup.center (SL2 k) ≃* SL2 k :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have := hq.2.1
  exact e.symm.isSimpleGroup

theorem SL2Torus.isSimpleGroup_range {p : ℕ} {φ : SL2 k →* M} {T₀ : Subgroup M}
    (h : SL2Torus p φ T₀) (h4 : 4 ≤ Nat.card k) : IsSimpleGroup ↥φ.range := by
  have := isSimpleGroup_SL_two (k := k) h4
  exact (MonoidHom.ofInjective h.inj).symm.isSimpleGroup

omit [CharP k 2] in
theorem SL2Torus.card_range {p : ℕ} {φ : SL2 k →* M} {T₀ : Subgroup M}
    (h : SL2Torus p φ T₀) : Nat.card ↥φ.range = Nat.card k * (Nat.card k ^ 2 - 1) := by
  rw [← CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two k]
  exact (Nat.card_congr (MonoidHom.ofInjective h.inj).toEquiv).symm

omit [CharP k 2] in
theorem SL2Torus.isQuasisimple_range {p : ℕ} {φ : SL2 k →* M} {T₀ : Subgroup M}
    (h : SL2Torus p φ T₀) (h4 : 4 ≤ Nat.card k) : IsQuasisimple ↥φ.range :=
  isQuasisimple_of_mulEquiv (MonoidHom.ofInjective h.inj)
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le le_rfl h4)

theorem MSide.of_SL2Torus {p g : ℕ} {φ : SL2 k →* M} {T₀ : Subgroup M} (h : SL2Torus p φ T₀)
    (hp : p.Prime) (hζ : ∃ ζ : kˣ, IsPrimitiveRoot ζ p) (hk : Nat.card k = 2 ^ g)
    (h4 : 4 ≤ Nat.card k) {bM : M} (hD : layerD bM = φ.range) : MSide p g T₀ bM where
  quasi := by
    rw [hD]
    exact h.isQuasisimple_range h4
  center := by
    rw [hD, ← card_center_mulEquiv (MonoidHom.ofInjective h.inj), card_center_SL_two]
    exact hp.not_dvd_one
  card := by
    rw [hD]
    exact h.card_inf hp.pos hζ
  upper := by
    rw [hD]
    exact h.exists_upper
  model := ⟨k, inferInstance, inferInstance, hk, by
    rw [hD]
    exact exists_centerQuotient_mulEquiv (MonoidHom.ofInjective h.inj).symm⟩

end OfTorus

end CFSG.RankThree.PartOne.KLAY

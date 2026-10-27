module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityModel
import CFSG.RankThree.PartOne.KD4L.TriDescent
import CFSG.GroupTheory.ElementaryAbelianTransport
public import Certificates.Data.ExceptionalSL3

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

section ElemAb

variable {G : Type*} [Group G]

theorem elemAb_comm {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 3 E) :
    ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
  haveI := hE
  have := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  simpa using this

theorem elemAb_cube {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 3 E) :
    ∀ x ∈ E, x ^ 3 = 1 := fun x hx => by
  haveI := hE
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) (p := 3) x hx

theorem isElementaryAbelian_three_of {E : Subgroup G}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcube : ∀ x ∈ E, x ^ 3 = 1) :
    CFSG.IsElementaryAbelian 3 E :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hcube⟩

theorem isElementaryAbelian_map_three {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 3 E)
    (φ : MulAut G) : CFSG.IsElementaryAbelian 3 (E.map φ.toMonoidHom) := by
  refine isElementaryAbelian_three_of ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul, elemAb_comm hE x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    show φ x ^ 3 = 1
    rw [← map_pow, elemAb_cube hE x hx, map_one]

theorem card_zpowers_of_cube_one {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    Nat.card (Subgroup.zpowers a) = 3 := by
  have : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  rw [Nat.card_zpowers, this]

end ElemAb

section AutConj

variable {G : Type*} [Group G]

theorem aut_conj_conj (φ : MulAut G) (x : G) : φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  refine MulEquiv.ext fun y => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem congr_apply_eq (φ m : MulAut G) : (MulAut.congr φ) m = φ * m * φ⁻¹ := by
  refine MulEquiv.ext fun y => ?_
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.mul_apply]
  rfl

theorem congr_mul_toMonoidHom (a b : MulAut G) :
    (MulAut.congr (a * b)).toMonoidHom =
      (MulAut.congr a).toMonoidHom.comp (MulAut.congr b).toMonoidHom := by
  ext m : 1
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, congr_apply_eq, mul_inv_rev]
  group

theorem closure_pair_eq_of_mul_pow (c β t : G) (i : ℕ)
    (h : β * c ^ i = t ∨ β * c ^ i = t⁻¹) :
    Subgroup.closure ({c, β} : Set G) = Subgroup.closure ({c, t} : Set G) := by
  have hc1 : c ∈ Subgroup.closure ({c, β} : Set G) := Subgroup.subset_closure (by simp)
  have hb1 : β ∈ Subgroup.closure ({c, β} : Set G) := Subgroup.subset_closure (by simp)
  have hc2 : c ∈ Subgroup.closure ({c, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht2 : t ∈ Subgroup.closure ({c, t} : Set G) := Subgroup.subset_closure (by simp)
  have hcp1 : c ^ i ∈ Subgroup.closure ({c, β} : Set G) := pow_mem hc1 i
  have hcp2 : c ^ i ∈ Subgroup.closure ({c, t} : Set G) := pow_mem hc2 i
  have hβ2 : β = (β * c ^ i) * (c ^ i)⁻¹ := by group
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hc2
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rcases h with h | h
      · rw [hβ2, h]; exact mul_mem ht2 (inv_mem hcp2)
      · rw [hβ2, h]; exact mul_mem (inv_mem ht2) (inv_mem hcp2)
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hc1
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rcases h with h | h
      · rw [← h]; exact mul_mem hb1 hcp1
      · have : y = (β * c ^ i)⁻¹ := by rw [h]; group
        rw [this]; exact inv_mem (mul_mem hb1 hcp1)

end AutConj


section Field

theorem sigma_pow_apply {X : Type} [Field X] (σ : X ≃+* X) (q : ℕ) (hq : ∀ c : X, σ c = c ^ q)
    (k : ℕ) (c : X) : (σ ^ k) c = c ^ (q ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show σ ^ (k + 1) = σ * σ ^ k from pow_succ' σ k]
    show σ ((σ ^ k) c) = c ^ (q ^ (k + 1))
    rw [ih, map_pow, hq, ← pow_mul, pow_succ, mul_comm (q ^ k) q]

theorem sigma_pow_three {X : Type} [Field X] [Finite X] (σ : X ≃+* X) (n : ℕ)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) : σ ^ 3 = 1 := by
  classical
  haveI := Fintype.ofFinite X
  refine RingEquiv.ext fun c => ?_
  show (σ ^ 3) c = c
  rw [sigma_pow_apply σ (2 ^ n) hσ 3 c, ← hX, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

theorem four_le_card_of_cube {X : Type} (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3) :
    4 ≤ Nat.card X := by
  rw [hX]
  have h2 : 2 ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (show 2 > 0 by norm_num) hn
  calc 4 ≤ 2 ^ 3 := by norm_num
    _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h2 3

end Field

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

structure TrialityABFacts : Prop where
  inf_bot : Asub σ ⊓ Bsub σ = ⊥
  max : ∀ N : Subgroup (C0 σ), Asub σ ⊔ Bsub σ ≤ N → N = Asub σ ⊔ Bsub σ ∨ N = ⊤
  tau3 : tauAut σ ^ 3 = 1
  tau_A : ∀ a ∈ Asub σ, tauAut σ a ∈ Asub σ
  tau_B : ∀ b ∈ Bsub σ, tauAut σ b = b
  sl2A : ∃ e : Asub σ ≃* Matrix.SpecialLinearGroup (Fin 2) X,
    ∀ (a : C0 σ) (ha : a ∈ Asub σ),
      e ⟨tauAut σ a, tau_A a ha⟩ = Matrix.SpecialLinearGroup.map (σ : X →+* X) (e ⟨a, ha⟩)
  sl2B : Nonempty (Bsub σ ≃* Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ))

@[expose] def HasGLine (x g : C0 σ) (e : ℕ) : Prop :=
  ∃ (φ : MulAut (C0 σ)) (i : ℕ),
    φ * (MulAut.conj g * tauAut σ ^ e * MulAut.conj x ^ i) * φ⁻¹ = tauAut σ ∨
      φ * (MulAut.conj g * tauAut σ ^ e * MulAut.conj x ^ i) * φ⁻¹ = (tauAut σ)⁻¹

structure TrialityR1Facts : Prop where
  Eb : 4 ≤ Nat.card (fixSubfield σ) → ∀ {a b : C0 σ}, a ∈ Asub σ → b ∈ Bsub σ → a ^ 3 = 1 →
    b ^ 3 = 1 → a ≠ 1 → b ≠ 1 →
      PlaneGen (Subgroup.closure ({MulAut.conj a, MulAut.conj b} : Set (MulAut (C0 σ))))
  N4 : 4 ≤ Nat.card (fixSubfield σ) → ∀ {b : C0 σ}, b ∈ Bsub σ → b ^ 3 = 1 → b ≠ 1 →
      PlaneGen (Subgroup.closure ({MulAut.conj b, tauAut σ} : Set (MulAut (C0 σ))))
  N3 : 4 ≤ Nat.card (fixSubfield σ) → ∀ {a : C0 σ}, a ∈ A0sub σ → a ^ 3 = 1 → a ≠ 1 →
      PlaneGen (Subgroup.closure ({MulAut.conj a, tauAut σ} : Set (MulAut (C0 σ))))
  Nreg : 4 ≤ Nat.card (fixSubfield σ) → ∀ {a b : C0 σ}, a ∈ A0sub σ → b ∈ Bsub σ → a ^ 3 = 1 →
    b ^ 3 = 1 → a ≠ 1 → b ≠ 1 →
      PlaneGen (Subgroup.closure
        ({MulAut.conj a, MulAut.conj b * tauAut σ} : Set (MulAut (C0 σ))))

theorem isSimple_and_noncomm_C0 (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) :
    IsSimpleGroup (C0 σ) ∧ ∃ x y : C0 σ, x * y ≠ y * x := by
  exact CFSG.RankThree.PartOne.KD4L.isSimple_graphFixedRootGroup_triality (ℓ := 2) (d := n)
    Nat.prime_two hn hX 1 (Or.inl rfl) σ.toRingHom (fun c => by simpa using hσ c)

theorem isSimpleGroup_C0 (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) : IsSimpleGroup (C0 σ) :=
  (isSimple_and_noncomm_C0 σ n hn hX hσ).1

theorem conj_injective_C0 (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) :
    Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) := by
  obtain ⟨hs, x, y, hxy⟩ := isSimple_and_noncomm_C0 σ n hn hX hσ
  haveI := hs
  have hcenter : Subgroup.center (C0 σ) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (C0 σ)) with h | h
    · exact h
    · exfalso
      apply hxy
      have hx : x ∈ Subgroup.center (C0 σ) := by rw [h]; exact Subgroup.mem_top x
      exact ((Subgroup.mem_center_iff.mp hx) y).symm
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : g ∈ Subgroup.center (C0 σ) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun φ : MulAut (C0 σ) => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [hcenter] at hg'
  exact (Subgroup.mem_bot.mp hg')

end Model

end CFSG.RankThree.PartTwo.Sec19

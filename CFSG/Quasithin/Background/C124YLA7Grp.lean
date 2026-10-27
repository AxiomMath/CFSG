module

public import CFSG.Quasithin.Background.C124YLA6Grp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A7

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.L246.C123
open scoped MatrixGroups

@[expose] def ι57 : Fin 5 ↪ Fin 7 := Fin.castLEEmb (by norm_num)

@[expose] noncomputable def altLift5 : ↥(alternatingGroup (Fin 5)) →* A7 :=
  ((Equiv.Perm.viaEmbeddingHom ι57).comp
      (alternatingGroup (Fin 5)).subtype).codRestrict (alternatingGroup (Fin 7)) fun σ => by
    have h := σ.2
    rw [Equiv.Perm.mem_alternatingGroup] at h ⊢
    have key : Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom ι57 (σ : Equiv.Perm (Fin 5))) =
        Equiv.Perm.sign (σ : Equiv.Perm (Fin 5)) := by
      classical
      rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
      convert Equiv.Perm.sign_extendDomain (σ : Equiv.Perm (Fin 5))
        (Equiv.ofInjective ι57.1 ι57.2)
    exact key.trans h

theorem altLift5_injective : Function.Injective altLift5 := fun _ _ h =>
  Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective _ (congrArg Subtype.val h))

theorem viaEmbedding_eq_of_forall {σ : Perm (Fin 5)} {q : Perm (Fin 7)}
    (h : ∀ i : Fin 5, q (ι57 i) = ι57 (σ i)) (h5 : q 5 = 5) (h6 : q 6 = 6) :
    Equiv.Perm.viaEmbedding σ ι57 = q := by
  refine Equiv.ext fun j => ?_
  by_cases hj : j.val < 5
  · have e : j = ι57 ⟨j.val, hj⟩ := Fin.ext rfl
    rw [e, Equiv.Perm.viaEmbedding_apply]
    exact (h _).symm
  · have hrange : j ∉ Set.range ι57 := by
      rintro ⟨i, rfl⟩
      exact hj i.2
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hrange]
    have : j.val = 5 ∨ j.val = 6 := by omega
    rcases this with h | h
    · have : j = 5 := Fin.ext h
      rw [this, h5]
    · have : j = 6 := Fin.ext h
      rw [this, h6]

theorem altLift5_eq_of {σ : ↥(alternatingGroup (Fin 5))} {q : A7}
    (h : ∀ i : Fin 5, (q : Perm (Fin 7)) (ι57 i) = ι57 ((σ : Perm (Fin 5)) i))
    (h5 : (q : Perm (Fin 7)) 5 = 5) (h6 : (q : Perm (Fin 7)) 6 = 6) : altLift5 σ = q :=
  Subtype.ext (viaEmbedding_eq_of_forall h h5 h6)

@[expose] noncomputable def Yst : Subgroup A7 := altLift5.range

noncomputable def YstEquiv : ↥Yst ≃* ↥(alternatingGroup (Fin 5)) :=
  (MonoidHom.ofInjective altLift5_injective).symm

theorem card_Yst : Nat.card Yst = 60 := by
  rw [Nat.card_congr YstEquiv.toEquiv]
  exact Bridge.card_alt_five

theorem sl2_Yst : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (↥Yst ≃* SL(2, F)) := by
  have hF : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e2⟩ := A6.sl2_equiv_alt_five (F := GaloisField 2 2) hF
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, hF, ⟨YstEquiv.trans e2.symm⟩⟩

theorem mem_Yst_of {σ : ↥(alternatingGroup (Fin 5))} {q : A7} (h : altLift5 σ = q) : q ∈ Yst :=
  ⟨σ, h⟩

theorem sign_two_swaps {n : ℕ} (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    (swap a b * swap c d : Perm (Fin n)) ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  decide

theorem sign_four_swaps {n : ℕ} (a b c d e f g h : Fin n) (hab : a ≠ b) (hcd : c ≠ d)
    (hef : e ≠ f) (hgh : g ≠ h) :
    (swap a b * swap c d * swap e f * swap g h : Perm (Fin n)) ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd,
    Equiv.Perm.sign_swap hef, Equiv.Perm.sign_swap hgh]
  decide

theorem x7_lift : ∀ i : Fin 5, x7 (ι57 i) = ι57 ((swap 0 1 * swap 2 3 : Perm (Fin 5)) i) := by
  decide

theorem y7_lift : ∀ i : Fin 5, y7 (ι57 i) = ι57 ((swap 0 2 * swap 1 3 : Perm (Fin 5)) i) := by
  decide

theorem xy7_lift : ∀ i : Fin 5, (x7 * y7) (ι57 i) =
    ι57 ((swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3) : Perm (Fin 5)) i) := by
  decide

theorem x7_fix : x7 5 = 5 ∧ x7 6 = 6 := by decide

theorem y7_fix : y7 5 = 5 ∧ y7 6 = 6 := by decide

theorem xy7_fix : (x7 * y7) 5 = 5 ∧ (x7 * y7) 6 = 6 := by decide

section Klein

theorem kleinA_le_Yst : kleinA ≤ Yst := by
  intro k hk
  have hk' := mem_kleinA.1 hk
  simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton] at hk'
  have hx : (swap 0 1 * swap 2 3 : Perm (Fin 5)) ∈ alternatingGroup (Fin 5) :=
    sign_two_swaps 0 1 2 3 (by decide) (by decide)
  have hy : (swap 0 2 * swap 1 3 : Perm (Fin 5)) ∈ alternatingGroup (Fin 5) :=
    sign_two_swaps 0 2 1 3 (by decide) (by decide)
  rcases hk' with h | h | h | h
  · have : k = 1 := Subtype.ext h
    rw [this]
    exact Yst.one_mem
  · exact mem_Yst_of (σ := ⟨_, hx⟩) (altLift5_eq_of (by rw [h]; exact x7_lift)
      (by rw [h]; exact x7_fix.1) (by rw [h]; exact x7_fix.2))
  · exact mem_Yst_of (σ := ⟨_, hy⟩) (altLift5_eq_of (by rw [h]; exact y7_lift)
      (by rw [h]; exact y7_fix.1) (by rw [h]; exact y7_fix.2))
  · exact mem_Yst_of (σ := ⟨_, (alternatingGroup (Fin 5)).mul_mem hx hy⟩)
      (altLift5_eq_of (by rw [h]; exact xy7_lift) (by rw [h]; exact xy7_fix.1)
        (by rw [h]; exact xy7_fix.2))

end Klein

@[expose] def cyc5 : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def cyc3 : Perm (Fin 7) := swap 4 5 * swap 5 6

theorem cyc5_mem : cyc5 ∈ alternatingGroup (Fin 7) :=
  sign_four_swaps 0 1 1 2 2 3 3 4 (by decide) (by decide) (by decide) (by decide)

theorem cyc3_mem : cyc3 ∈ alternatingGroup (Fin 7) :=
  sign_two_swaps 4 5 5 6 (by decide) (by decide)

theorem cyc5_lift : ∀ i : Fin 5, cyc5 (ι57 i) =
    ι57 ((swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 : Perm (Fin 5)) i) := by decide

theorem cyc5_fix : cyc5 5 = 5 ∧ cyc5 6 = 6 := by decide

theorem seven_cycle : (cyc5 * cyc3) ^ 7 = 1 := by decide +kernel

theorem seven_cycle_ne : cyc5 * cyc3 ≠ 1 := by decide

theorem cyc3_x7 : cyc3 * x7 * cyc3⁻¹ ∈ kleinSet := by decide +kernel

theorem cyc3_y7 : cyc3 * y7 * cyc3⁻¹ ∈ kleinSet := by decide +kernel

theorem gen_A7 :
    Yst ⊔ Subgroup.normalizer (kleinA : Set A7) = ⊤ := by
  have hσ : (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 : Perm (Fin 5)) ∈ alternatingGroup (Fin 5) :=
    sign_four_swaps 0 1 1 2 2 3 3 4 (by decide) (by decide) (by decide) (by decide)
  set a : A7 := ⟨cyc5, cyc5_mem⟩ with ha_def
  set b : A7 := ⟨cyc3, cyc3_mem⟩ with hb_def
  have ha : a ∈ Yst := mem_Yst_of (σ := ⟨_, hσ⟩) (altLift5_eq_of cyc5_lift cyc5_fix.1 cyc5_fix.2)
  have hb : b ∈ Subgroup.normalizer (kleinA : Set A7) :=
    (mem_normalizer_kleinA_iff b).2 ⟨cyc3_x7, cyc3_y7⟩
  have hg : a * b ∈ Yst ⊔ Subgroup.normalizer (kleinA : Set A7) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  apply eq_top_of_dvd
  · have hord : orderOf (a * b) = 7 := by
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        rw [Subgroup.coe_pow]
        exact seven_cycle
      · intro h
        exact seven_cycle_ne (congrArg Subtype.val h)
    have := orderOf_dvd_natCard (⟨a * b, hg⟩ : ↥(Yst ⊔ Subgroup.normalizer (kleinA : Set A7)))
    rwa [Subgroup.orderOf_mk, hord] at this
  · have := Subgroup.card_dvd_of_le
      (le_sup_right : Subgroup.normalizer (kleinA : Set A7) ≤
        Yst ⊔ Subgroup.normalizer (kleinA : Set A7))
    rwa [card_normalizer_kleinA] at this

end CFSG.Quasithin.C124.YL.A7

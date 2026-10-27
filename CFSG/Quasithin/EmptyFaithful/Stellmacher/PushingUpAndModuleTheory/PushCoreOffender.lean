module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreBasic
public import CFSG.Quasithin.Background.Equivariance
public import CFSG.Quasithin.Background.B2Thompson

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def centMod (Z V : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (Z : Set G) ∧ ∀ v ∈ V, ⁅v, x⁆ ∈ Z}
  one_mem' := ⟨Subgroup.one_mem _, fun v _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨Subgroup.mul_mem _ hxN hyN, fun v hv => ?_⟩
    have h1 : ⁅v, x * y⁆ = ⁅v, x⁆ * (x * ⁅v, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact Z.mul_mem (hx v hv) ((Subgroup.mem_normalizer_iff.mp hxN _).mp (hy v hv))
  inv_mem' := by
    rintro x ⟨hxN, hx⟩
    refine ⟨Subgroup.inv_mem _ hxN, fun v hv => ?_⟩
    have h1 : ⁅v, x⁻¹⁆ = x⁻¹ * ⁅v, x⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [h1]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp (Z.inv_mem (hx v hv))
    simpa using this

theorem conj_mem_centMod {Z V : Subgroup G} {g x : G} (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ centMod Z V) :
    g * x * g⁻¹ ∈ centMod Z V := by
  obtain ⟨hxN, hx⟩ := hx
  refine ⟨?_, fun v hv => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgZ hxN) (Subgroup.inv_mem _ hgZ)
  · have hv' : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgV) v).mp hv
      simpa using this
    have h1 : ⁅v, g * x * g⁻¹⁆ = g * ⁅g⁻¹ * v * g, x⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp hgZ _).mp (hx _ hv')

section Offender

variable {X S Z : Subgroup G}

theorem PushHyp.inf_centralizer_of_le [Finite G] (h : PushHyp X S Z) {A : Subgroup G} (hA : A ≤ S) :
    A ⊓ Subgroup.centralizer (Z : Set G) = A ⊓ pCoreOf 2 X := by
  rw [← h.inf_centralizer_eq, ← inf_assoc, inf_of_le_left hA]

theorem relIndex_mul_card_centralizer (Z A : Subgroup G) :
    (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z *
      Nat.card (Z ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) = Nat.card Z := by
  have h := Subgroup.relIndex_mul_card (Z ⊓ Subgroup.centralizer (A : Set G)) Z
  rwa [inf_of_le_left inf_le_left] at h

theorem offender_count [Finite G] (h : PushHyp X S Z) {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z ≤ (A ⊓ pCoreOf 2 X).relIndex A := by
  have h1 := card_le_relIndex_mul_card h.elemAbelian h.Z_le hA
  rw [h.inf_centralizer_of_le hA.1, ← relIndex_mul_card_centralizer Z A] at h1
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

theorem card_eq_of_offender_eq [Finite G] (h : PushHyp X S Z) {A : Subgroup G}
    (heq : (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A)
    (hA : A ≤ S) :
    Nat.card Z = (A ⊓ Subgroup.centralizer (Z : Set G)).relIndex A *
      Nat.card (Z ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  rw [h.inf_centralizer_of_le hA, ← heq, ← relIndex_mul_card_centralizer Z A]

theorem thompsonJ_le_self (S : Subgroup G) : thompsonJ S ≤ S := iSup₂_le fun _ hA => hA.1

theorem omegaOneCenter_le_of_isMax [Finite G] {R A : Subgroup G} (hA : IsMaxElemAbelian R A) :
    omegaOneCenterOf (thompsonJ R) ≤ A :=
  ((omegaOne_centralizer_thompsonJ R).2).le.trans (iInf₂_le A hA)

theorem isMaxElemAbelian_of_le {R S A : Subgroup G} (hA : IsMaxElemAbelian S A) (hAR : A ≤ R)
    (hRS : R ≤ S) : IsMaxElemAbelian R A :=
  ⟨hAR, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans hRS) hBe⟩

theorem le_normalizer_omegaOneCenter_core (X : Subgroup G) :
    X ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ (pCoreOf 2 X)) : Set G) := by
  refine le_trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) ?_
  refine normalizer_le_normalizer_of_map_mulEquiv
    (F := fun R => omegaOneCenterOf (thompsonJ R)) (fun φ Y => ?_) _
  rw [omegaOneCenterOf_map_mulEquiv, thompsonJ_map_mulEquiv]

theorem le_normalizer_thompsonJ_core (X : Subgroup G) :
    X ≤ Subgroup.normalizer (thompsonJ (pCoreOf 2 X) : Set G) :=
  (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X).trans
    (normalizer_le_normalizer_thompsonJ _)

theorem offender_equality [Finite G] (h : PushHyp X S Z) {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (heq : (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A) :
    IsMaxElemAbelian S ((A ⊓ pCoreOf 2 X) ⊔ Z) ∧
      IsMaxElemAbelian (pCoreOf 2 X) ((A ⊓ pCoreOf 2 X) ⊔ Z) ∧
      Z ≤ omegaOneCenterOf (thompsonJ (pCoreOf 2 X)) ∧
      omegaOneCenterOf (thompsonJ S) ≤ omegaOneCenterOf (thompsonJ (pCoreOf 2 X)) := by
  obtain ⟨h1, -, -, h4, h5⟩ := B24_three h.elemAbelian h.Z_le hA
    (card_eq_of_offender_eq h heq hA.1)
  rw [h.inf_centralizer_of_le hA.1] at h1
  rw [h.inf_centralizer_eq] at h4 h5
  refine ⟨h1, isMaxElemAbelian_of_le h1 (sup_le inf_le_right h.le_core) h.core_le, h4, h5⟩

end Offender

section Commutator

variable {X S Z : Subgroup G}

theorem commutator_le_of_equality [Finite G] (h : PushHyp X S Z)
    (hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A) :
    thompsonJ S ≤ centMod Z (omegaOneCenterOf (thompsonJ (pCoreOf 2 X))) := by
  refine iSup₂_le fun A hA a ha => ?_
  refine ⟨(h.normal) (h.le_self (hA.1 ha)), fun w hw => ?_⟩
  by_cases hAQ : A ≤ pCoreOf 2 X
  · have hmax : IsMaxElemAbelian (pCoreOf 2 X) A := isMaxElemAbelian_of_le hA hAQ h.core_le
    have hwA : w ∈ A := omegaOneCenter_le_of_isMax hmax hw
    have : ⁅w, a⁆ = 1 := by
      have := hA.2.1.1.is_comm.comm ⟨w, hwA⟩ ⟨a, ha⟩
      have h2 : w * a = a * w := congrArg Subtype.val this
      simp [commutatorElement_def, h2]
    rw [this]; exact Z.one_mem
  · obtain ⟨-, hmaxQ, -, -⟩ := offender_equality h hA (hall A hA hAQ)
    have hwA : w ∈ (A ⊓ pCoreOf 2 X) ⊔ Z := omegaOneCenter_le_of_isMax hmaxQ hw
    have hle : (A ⊓ pCoreOf 2 X) ⊔ Z ≤ centMod Z A := by
      refine sup_le (fun y hy => ⟨h.normal (CFSG.LieType.BorelTits.pCoreOf_le 2 X hy.2), fun v hv => ?_⟩)
        (fun y hy => ⟨Subgroup.le_normalizer hy, fun v hv => ?_⟩)
      · have := hA.2.1.1.is_comm.comm ⟨v, hv⟩ ⟨y, hy.1⟩
        have h2 : v * y = y * v := congrArg Subtype.val this
        simp [commutatorElement_def, h2]
      · have hvX : v ∈ X := h.le_self (hA.1 hv)
        have h3 : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := by simp [commutatorElement_def]
        rw [h3]
        exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (h.normal hvX) y).mp hy) (Z.inv_mem hy)
    have h4 := (hle hwA).2 a ha
    have h5 : ⁅w, a⁆ = ⁅a, w⁆⁻¹ := (commutatorElement_inv a w).symm
    rw [h5]
    exact Z.inv_mem h4

end Commutator

end CFSG.Quasithin.F53Push

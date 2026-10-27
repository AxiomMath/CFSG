module

public import CFSG.Quasithin.Background.B5NonB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeSecHom
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
public import CFSG.Quasithin.Background.D2Offenders

public section

namespace CFSG.Quasithin.Z391

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped commutatorElement

variable {W : Type} [CommGroup W]

theorem le_stabSub_iff {G : Subgroup (MulAut W)} {Y : Subgroup W} :
    G ≤ stabSub Y ↔ ∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y :=
  ⟨fun h _ hg y hy => (h hg y).2 hy, B1.le_stabSub_of_invariant⟩

theorem inf_centSec_eq_bot {G L A : Subgroup (MulAut W)} {Y Z : Subgroup W}
    (hq : CFSG.IsQuasisimple ↥L) (hLG : L ≤ G) (hAG : A ≤ G)
    (hN : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hGY : G ≤ stabSub Y) (hGZ : G ≤ stabSub Z)
    (hnt : ¬ L ≤ centSec Y Z)
    (hf : ∀ a ∈ A, (∀ x ∈ L, a * x = x * a) → a = 1) :
    A ⊓ centSec Y Z = ⊥ := by
  have hperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hq.1
    exact Subgroup.commutator_eq_self
  have hKn : ((centSec Y Z).subgroupOf L).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    simpa using conj_mem_centSec (hGY (hLG g.2)) (hGZ (hLG g.2)) hk
  have hKc : (centSec Y Z).subgroupOf L ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hKn with h | h
    · exfalso
      apply hnt
      intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ (centSec Y Z).subgroupOf L := by rw [h]; trivial
      exact this
    · exact h
  have hcentral : ∀ z ∈ L ⊓ centSec Y Z, ∀ l ∈ L, z * l = l * z := by
    intro z hz l hl
    have hz' : (⟨z, hz.1⟩ : ↥L) ∈ (centSec Y Z).subgroupOf L := hz.2
    have := Subgroup.mem_center_iff.mp (hKc hz') ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  refine hf a ha.1 ?_
  refine B5.commute_of_comm_central hperf (fun l hl => hN a (hAG ha.1) l hl) hcentral ?_
  intro l hl
  refine ⟨?_, ?_⟩
  · have h1 := hN a (hAG ha.1) l hl
    have h2 : a * l * a⁻¹ * l⁻¹ = (a * l * a⁻¹) * l⁻¹ := rfl
    show a * l * a⁻¹ * l⁻¹ ∈ L
    exact L.mul_mem h1 (L.inv_mem hl)
  · have h1 : l * a⁻¹ * l⁻¹ ∈ centSec Y Z :=
      conj_mem_centSec (hGY (hLG hl)) (hGZ (hLG hl)) ((centSec Y Z).inv_mem ha.2)
    have h2 : ⁅a, l⁆ = a * (l * a⁻¹ * l⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact (centSec Y Z).mul_mem ha.2 h1

theorem isA2_autSec {G A : Subgroup (MulAut W)} {Y Z : Subgroup W} (hA : IsA2 G A)
    (hAY : A ≤ stabSub Y) (hAZ : A ≤ stabSub Z) (hf : A ⊓ centSec Y Z = ⊥) :
    IsA2 (autSec G Y Z) (autSec A Y Z) := by
  have hAs : A ≤ stabSub Y ⊓ stabSub Z := le_inf hAY hAZ
  refine ⟨autSec_mono hA.1 Y Z, CFSG.QuasithinUnique.Bridge.autSec_ne_bot hAs ?_,
    CFSG.QuasithinUnique.Bridge.isElemAbelian2_autSec hA.2.2 hAs⟩
  intro h
  apply hA.2.1
  rw [← inf_eq_left.2 h]
  exact hf

section Quot

variable {Y : Type} [CommGroup Y] {U : Subgroup Y}

theorem commIter_autQuot_le (A : Subgroup (MulAut Y)) (n : ℕ) :
    commIter ⊤ (autQuot A U) n ≤ (commIter ⊤ A n).map (QuotientGroup.mk' U) := by
  induction n with
  | zero =>
    show (⊤ : Subgroup (Y ⧸ U)) ≤ (⊤ : Subgroup Y).map (QuotientGroup.mk' U)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective U)]
  | succ n ih =>
    show commSub (commIter ⊤ (autQuot A U) n) (autQuot A U) ≤
      (commSub (commIter ⊤ A n) A).map (QuotientGroup.mk' U)
    refine (commSub_mono ih le_rfl).trans ?_
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨φ, hφ, _, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨g, hgA, rfl⟩ := mem_autQuot.mp hφ
    refine ⟨(g : MulAut Y) y * y⁻¹, Subgroup.subset_closure ⟨g, hgA, y, hy, rfl⟩, ?_⟩
    rw [map_mul, map_inv]
    rfl

theorem commSeries_autQuot_eq_bot {A : Subgroup (MulAut Y)} {k : ℕ} (h : commSeries A k = ⊥) :
    commSeries (autQuot A U) k = ⊥ := by
  have h1 := commIter_autQuot_le (U := U) A k
  rw [show commIter ⊤ A k = commSeries A k from rfl, h, Subgroup.map_bot] at h1
  exact le_bot_iff.mp h1

end Quot

theorem commSeries_autSec_eq_bot {A : Subgroup (MulAut W)} {Y Z : Subgroup W} (hAY : A ≤ stabSub Y)
    {k : ℕ} (h : commSeries A k = ⊥) : commSeries (autSec A Y Z) k = ⊥ :=
  commSeries_autQuot_eq_bot (commSeries_autSub_eq_bot hAY h)

theorem qhatOf_autSec_le_rAV [Finite W] {G A : Subgroup (MulAut W)} {Y Z : Subgroup W} (hA : IsA2 G A)
    (hA3 : commSeries A 3 = ⊥) (hAY : A ≤ stabSub Y) (hAZ : A ≤ stabSub Z) (hf : A ⊓ centSec Y Z = ⊥) :
    qhatOf (autSec G Y Z) ≤ ((rAV (autSec A Y Z) : ℚ) : WithTop ℚ) :=
  kq_le_iff.2 ⟨autSec A Y Z, isA2_autSec hA hAY hAZ hf, commSeries_autSec_eq_bot hAY hA3, le_rfl⟩

end CFSG.Quasithin.Z391

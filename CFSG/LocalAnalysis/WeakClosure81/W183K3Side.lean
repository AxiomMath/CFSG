module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Core
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoBase
import CFSG.RankThree.PartOne.F106.OddRadBlocks

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {R Y T L L₁ L₂ N : Subgroup (LGL 2 V)}

theorem Br3TwoComp.toBase (h : Br3TwoComp Y T L₁ L₂) : TwoCompBase Y T L₁ L₂ :=
  ⟨h.le₁, h.le₂, h.comm, h.ne, h.perm, h.swap, h.gen⟩

private theorem w183K3Side_odd_card_sup_of_commute {A B : Subgroup (LGL 2 V)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : Odd (Nat.card ↥A))
    (hB : Odd (Nat.card ↥B)) : Odd (Nat.card ↥(A ⊔ B)) := by
  let H : Fin 2 → Subgroup (LGL 2 V) := ![A, B]
  have hsup : (⨆ i : Fin 2, H i) = A ⊔ B := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · simpa [H] using le_sup_left
      · simpa [H] using le_sup_right
    · refine sup_le ?_ ?_
      · simpa [H] using le_iSup H 0
      · simpa [H] using le_iSup H 1
  have hc : Pairwise fun i j : Fin 2 =>
      ∀ x y : LGL 2 V, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
    · intro x y hx hy
      have hx' : x ∈ A := by simpa [H] using hx
      have hy' : y ∈ B := by simpa [H] using hy
      exact hcomm x hx' y hy'
    · intro x y hx hy
      have hx' : x ∈ B := by simpa [H] using hx
      have hy' : y ∈ A := by simpa [H] using hy
      exact (hcomm y hy' x hx').symm
  have hodd : ∀ i, Odd (Nat.card ↥(H i)) := by
    intro i
    fin_cases i
    · simpa [H] using hA
    · simpa [H] using hB
  have hmain := CFSG.RankThree.PartOne.F106.odd_card_iSup_of_commute H hc hodd
  rwa [hsup] at hmain

theorem Br3TwoComp.mem_kStar_of_cent (h : Br3TwoComp Y T L₁ L₂) {y : LGL 2 V} (hy : y ∈ Y)
    (h₁ : ∀ l ∈ L₁, y * l = l * y) (h₂ : ∀ l ∈ L₂, y * l = l * y) :
    y ∈ quasiCentre L₁ ⊔ quasiCentre L₂ := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    w183two_exists_mul_of_mem_sup h.comm (h.cent y hy h₁ h₂)
  have ha_cent : a ∈ quasiCentre L₁ := by
    rw [mem_quasiCentre]
    refine ⟨ha, fun l hl => ?_⟩
    have hbl : b * l = l * b := (h.comm l hl b hb).symm
    have key : (a * l) * b = (l * a) * b := by
      calc (a * l) * b = a * (l * b) := by group
        _ = a * (b * l) := by rw [hbl]
        _ = (a * b) * l := by group
        _ = y * l := by rw [hab]
        _ = l * y := h₁ l hl
        _ = l * (a * b) := by rw [hab]
        _ = (l * a) * b := by group
    exact mul_right_cancel key
  have hb_cent : b ∈ quasiCentre L₂ := by
    rw [mem_quasiCentre]
    refine ⟨hb, fun l hl => ?_⟩
    have hal : a * l = l * a := h.comm a ha l hl
    have key : a * (b * l) = a * (l * b) := by
      calc a * (b * l) = (a * b) * l := by group
        _ = y * l := by rw [hab]
        _ = l * y := h₂ l hl
        _ = l * (a * b) := by rw [hab]
        _ = (l * a) * b := by group
        _ = (a * l) * b := by rw [hal]
        _ = a * (l * b) := by group
    exact mul_left_cancel key
  rw [← hab]
  exact Subgroup.mul_mem_sup ha_cent hb_cent

theorem Br3TwoComp.odd_kStar (h : Br3TwoComp Y T L₁ L₂) :
    Odd (Nat.card ↥(quasiCentre L₁ ⊔ quasiCentre L₂)) := by
  have hcard₁ : Nat.card ↥(quasiCentre L₁) = Nat.card ↥(Subgroup.center ↥L₁) :=
    Subgroup.card_map_of_injective (K := Subgroup.center ↥L₁) (f := L₁.subtype)
      L₁.subtype_injective
  have hcard₂ : Nat.card ↥(quasiCentre L₂) = Nat.card ↥(Subgroup.center ↥L₂) :=
    Subgroup.card_map_of_injective (K := Subgroup.center ↥L₂) (f := L₂.subtype)
      L₂.subtype_injective
  have hodd₁ : Odd (Nat.card ↥(quasiCentre L₁)) := by rw [hcard₁]; exact h.odd₁
  have hodd₂ : Odd (Nat.card ↥(quasiCentre L₂)) := by rw [hcard₂]; exact h.odd₂
  have hcomm : ∀ a ∈ quasiCentre L₁, ∀ b ∈ quasiCentre L₂, a * b = b * a :=
    fun a ha b hb => h.comm a (quasiCentre_le L₁ ha) b (quasiCentre_le L₂ hb)
  exact w183K3Side_odd_card_sup_of_commute hcomm hodd₁ hodd₂

theorem Br3TwoComp.core₁ (h : Br3TwoComp Y T L₁ L₂) :
    QuasiCore (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) L₁
      (quasiCentre L₁ ⊔ quasiCentre L₂) where
  le := le_inf h.le₁ fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (h.comm a ha b hb).symm
  normal y hy l hl :=
    (Subgroup.mem_normalizer_iff.mp (h.toBase.mem_normalizer_of_mem_centralizer₂ hy) l).mp hl
  quasi := h.quasi₁
  odd := h.odd_kStar
  cent y hy hcl :=
    h.mem_kStar_of_cent hy.1 hcl fun l hl => (Subgroup.mem_centralizer_iff.mp hy.2 l hl).symm

theorem Br3TwoComp.core₂ (h : Br3TwoComp Y T L₁ L₂) :
    QuasiCore (Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) L₂
      (quasiCentre L₁ ⊔ quasiCentre L₂) where
  le := le_inf h.le₂ fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => h.comm a ha b hb
  normal y hy l hl :=
    (Subgroup.mem_normalizer_iff.mp (h.toBase.mem_normalizer_of_mem_centralizer₁ hy) l).mp hl
  quasi := h.quasi₂
  odd := h.odd_kStar
  cent y hy hcl :=
    h.mem_kStar_of_cent hy.1 (fun l hl => (Subgroup.mem_centralizer_iff.mp hy.2 l hl).symm) hcl

theorem Br3TwoComp.inf_X_le (h : Br3TwoComp Y T L₁ L₂) :
    (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ⊓
      (Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ quasiCentre L₁ ⊔ quasiCentre L₂ :=
  fun _ hy =>
    h.mem_kStar_of_cent hy.1.1 (fun l hl => (Subgroup.mem_centralizer_iff.mp hy.2.2 l hl).symm)
      fun l hl => (Subgroup.mem_centralizer_iff.mp hy.1.2 l hl).symm

theorem Br3TwoComp.cj_X (h : Br3TwoComp Y T L₁ L₂) (hT : T ≤ Y) {x : LGL 2 V} (hx : x ∈ T)
    (hxL : cj x L₁ = L₂) :
    cj x (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) =
      Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
  h.toBase.cj_X hT hx hxL

theorem Br3TwoComp.mem_normalizer_iff (h : Br3TwoComp Y T L₁ L₂) {y : LGL 2 V} (hy : y ∈ Y) :
    y ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) ↔
      y ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
  h.toBase.mem_normalizer_iff hy

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.Sporadic.Presentation.SuzInputs
import Certificates.Kernel.Bounds.Suz
import Certificates.Kernel.Bounds.Suz.Binding
import CFSG.Certificates.Kernel.CosetBounds
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
import all TauCeti.GroupTheory.Presentation.GroupPresentation
import all TauCeti.GroupTheory.Presentation.Relator
import all CFSG.Sporadic.Presentation.SuzInputs

public section

namespace CertificateChecks.KernelBounds

open CFSG.Certificates TauCeti

open CFSG.KBRoute.Suz in
theorem suz : Finite SporadicName.Suz.Group ∧
    Nat.card SporadicName.Suz.Group ≤ 448345497600 := by
  obtain ⟨h1, h2, h3, h4, htop, -, -, -, l1, l2, l3⟩ := Suz.facts_holds
  have hrels := KB.sword_rels _ rels_eq
  delta T1.ok at h1
  delta T2.ok at h2
  delta T3.ok at h3
  delta T4.ok at h4
  have s1 := KB.tableOk_sound _ hrels h1
  have s2 := KB.tableOk_sound _ hrels h2
  have s3 := KB.tableOk_sound _ hrels h3
  have s4 := KB.tableOk_sound _ hrels h4
  rw [KB.linkOk_sound _ (KB.tableOk_lens h1).2 l1] at s1
  rw [KB.linkOk_sound _ (KB.tableOk_lens h2).2 l2] at s2
  rw [KB.linkOk_sound _ (KB.tableOk_lens h3).2 l3] at s3
  rw [show T4.words = [] from rfl, KB.wordSub_nil] at s4
  have c := KB.card_le_step s1 <| KB.card_le_step s2 <| KB.card_le_step s3 <|
    KB.card_le_step s4 KB.card_bot_le
  exact (KB.finite_card_le_of_route _ gens_eq (by norm_num) htop c).imp id
    fun h => h.trans (Nat.le_of_ble_eq_true rfl)

namespace SuzR1

open CFSG.CosetTable CFSG.Sporadic.Presentation.Suz

private abbrev n : ℕ :=
  (subsetOf TauCeti.SporadicName.Suz.presentation.generatorCount [0, 1, 2, 3, 4, 6]).length

private theorem n_eq : n = 6 := by decide

private abbrev G : Type := PG n R1

private noncomputable def gen (g : ℕ) : G :=
  if h : g < n then PresentedGroup.of ⟨g, h⟩ else 1

private def letters : List (List (ℕ × Bool)) :=
  R1.map (List.map fun l => (l.1.val, l.2))

private theorem sword_gen (w : List (Fin n × Bool)) :
    KB.sword gen (w.map fun l => (l.1.val, l.2)) = PresentedGroup.mk _ (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, KB.sword, List.map_cons, List.prod_cons, ← KB.sword, ih,
      show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
    congr 1
    obtain ⟨j, b⟩ := l
    have hj : gen j.val = PresentedGroup.of j := by simp [gen, j.isLt]
    cases b
    · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv]
      simp only [Bool.false_eq_true, ↓reduceIte, hj]
      rfl
    · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl]
      simp only [↓reduceIte, hj]
      rfl

private theorem sword_letters : ∀ r ∈ letters, KB.sword gen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [sword_gen]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

private def bf3 : List (ℕ × Bool) :=
  [(1, true), (5, true), (1, true), (5, true), (1, true), (5, true)]

private theorem rels_sub :
    ∀ r ∈ CFSG.KBRoute.Suz.rels, (∀ x ∈ r, x.1 < 6) → r ∈ letters ∨ r = bf3 := by
  decide +kernel

private theorem sword_bf3 : KB.sword gen bf3 = 1 := by
  have hb := sword_letters [(1, true), (1, true)] (by decide +kernel)
  have hgb := sword_letters [(5, true), (1, true), (5, true), (1, true), (5, true), (1, true)]
    (by decide +kernel)
  simp only [KB.sword, bf3, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    ↓reduceIte, mul_one] at hb hgb ⊢
  have h : gen 1 * (gen 5 * (gen 1 * (gen 5 * (gen 1 * (gen 5 * gen 1))))) * (gen 1)⁻¹ = 1 := by
    rw [hgb, mul_one, mul_inv_cancel]
  simpa [mul_assoc] using h

end SuzR1

open CFSG.KBRoute.Suz SuzR1 in
theorem suzR1 : Finite (CFSG.CosetTable.PG _ CFSG.Sporadic.Presentation.Suz.R1) ∧
    Nat.card (CFSG.CosetTable.PG _ CFSG.Sporadic.Presentation.Suz.R1) ≤ 251596800 := by
  obtain ⟨-, h2, h3, h4, -, t2, t3, t4, -, l2, l3⟩ := Suz.facts_holds
  have h6 : ∀ r ∈ rels, (∀ x ∈ r, x.1 < 6) → KB.sword gen r = 1 := by
    intro r hr hx
    rcases rels_sub r hr hx with h | rfl
    · exact sword_letters r h
    · exact sword_bf3
  have hr : ∀ {amap k : ℕ}, KB.topOk amap k = true → k ≤ 6 →
      ∀ r ∈ rels, (∀ x ∈ r, KB.inAlpha amap x.1) → KB.sword gen r = 1 :=
    fun ht hk r hr hx => h6 r hr fun x hx' =>
      lt_of_lt_of_le (((KB.topOk_sound (by omega) ht) x.1).1 (hx x hx')) hk
  delta T2.ok at h2
  delta T3.ok at h3
  delta T4.ok at h4
  have s2 := KB.tableOk_sound_alpha gen (hr t2 le_rfl) h2
  have s3 := KB.tableOk_sound_alpha gen (hr t3 (by norm_num)) h3
  have s4 := KB.tableOk_sound_alpha gen (hr t4 (by norm_num)) h4
  rw [KB.linkOk_sound _ (KB.tableOk_lens h2).2 l2] at s2
  rw [KB.linkOk_sound _ (KB.tableOk_lens h3).2 l3] at s3
  rw [show T4.words = [] from rfl, KB.wordSub_nil] at s4
  have c := KB.card_le_step s2 <| KB.card_le_step s3 <| KB.card_le_step s4 KB.card_bot_le
  have htop : KB.alphaSub gen T2.amap = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← PresentedGroup.closure_range_of]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨j, rfl⟩
    have hj : j.val < 6 := n_eq ▸ j.isLt
    exact ⟨j.val, (KB.topOk_sound (by norm_num) t2 j.val).2 hj, by simp [gen, j.isLt]⟩
  exact (KB.finite_card_le_of_top htop c).imp id
    fun h => h.trans (Nat.le_of_ble_eq_true rfl)

end CertificateChecks.KernelBounds

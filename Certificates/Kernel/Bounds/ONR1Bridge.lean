module

public import CFSG.Sporadic.Presentation.ONanInputs
public import CFSG.Certificates.Kernel.CosetBounds
public import CFSG.Certificates.Kernel.Bounds.ON.Route
import Certificates.Kernel.Bounds.ON
import all CFSG.Certificates.Kernel.CosetBounds
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.ONan
import all TauCeti.GroupTheory.Presentation.GroupPresentation
import all TauCeti.GroupTheory.Presentation.Relator

public section

namespace CertificateChecks.KernelBounds

open CFSG.Certificates CFSG.CosetTable

noncomputable def pgGen (m : ℕ) (ws : List (List (Fin m × Bool))) (g : ℕ) : PG m ws :=
  if h : g < m then PresentedGroup.of ⟨g, h⟩ else 1

theorem sword_pgGen (m : ℕ) (ws : List (List (Fin m × Bool))) (w : List (Fin m × Bool)) :
    KB.sword (pgGen m ws) (w.map fun l => (l.1.val, l.2)) = PresentedGroup.mk _ (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, KB.sword, List.map_cons, List.prod_cons, ← KB.sword, ih,
      show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
    congr 1
    obtain ⟨j, b⟩ := l
    have hj : pgGen m ws j.val = PresentedGroup.of j := by simp [pgGen, j.isLt]
    cases b
    · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv]
      simp only [Bool.false_eq_true, ↓reduceIte, hj]
      rfl
    · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl]
      simp only [↓reduceIte, hj]
      rfl

open CFSG.Sporadic.Presentation.ONan CFSG.KBRoute.ON
open CFSG.Certificates.KB (byte)

theorem r1_letters : R1.map (fun w => w.map fun l => (l.1.val, l.2)) =
    rels.filter (fun r => r.all fun x => decide (x.1 < 6)) := by
  decide +kernel

theorem r1_length : (subsetOf TauCeti.SporadicName.ONan.presentation.generatorCount
    [0, 1, 2, 3, 4, 5]).length = 6 := by
  decide +kernel

theorem alpha_T2_lt : (List.range 256).all (fun g => byte T2.amap g == 0 || decide (g < 6)) =
    true := by
  decide +kernel

theorem alpha_T3_lt : (List.range 256).all (fun g => byte T3.amap g == 0 || decide (g < 6)) =
    true := by
  decide +kernel

theorem alpha_T2_mem : (List.range 6).all (fun g => byte T2.amap g != 0) = true := by
  decide +kernel

theorem lt_of_inAlpha {amap : ℕ}
    (h : (List.range 256).all (fun g => byte amap g == 0 || decide (g < 6)) = true) {g : ℕ}
    (hg : KB.inAlpha amap g) : g < 6 := by
  obtain ⟨h256, hb⟩ : g < 256 ∧ byte amap g ≠ 0 := hg
  have := List.all_eq_true.mp h g (List.mem_range.mpr h256)
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this.resolve_left hb

theorem sword_rels_R1 {amap : ℕ}
    (hA : (List.range 256).all (fun g => byte amap g == 0 || decide (g < 6)) = true) :
    ∀ r ∈ rels, (∀ x ∈ r, KB.inAlpha amap x.1) → KB.sword (pgGen _ R1) r = 1 := by
  intro r hr hx
  have hf : r ∈ rels.filter (fun r => r.all fun x => decide (x.1 < 6)) :=
    List.mem_filter.mpr ⟨hr, List.all_eq_true.mpr fun x hxr =>
      decide_eq_true (lt_of_inAlpha hA (hx x hxr))⟩
  rw [← r1_letters, List.mem_map] at hf
  obtain ⟨w, hw, rfl⟩ := hf
  rw [sword_pgGen]
  apply PresentedGroup.one_of_mem
  exact List.mem_map_of_mem hw

theorem onanR1 : Finite (PG _ R1) ∧ Nat.card (PG _ R1) ≤ 3753792 := by
  obtain ⟨-, h2, h3, -, -, l2⟩ := ON.facts_holds
  delta T2.ok at h2
  delta T3.ok at h3
  have s2 := KB.tableOk_sound_alpha (pgGen _ R1) (sword_rels_R1 alpha_T2_lt) h2
  have s3 := KB.tableOk_sound_alpha (pgGen _ R1) (sword_rels_R1 alpha_T3_lt) h3
  rw [KB.linkOk_sound _ (KB.tableOk_lens h2).2 l2] at s2
  rw [show T3.words = [] from rfl, KB.wordSub_nil] at s3
  have c := KB.card_le_step s2 <| KB.card_le_step s3 KB.card_bot_le
  have htop : KB.alphaSub (pgGen _ R1) T2.amap = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subgroup.closure (Set.range (PresentedGroup.of (rels := _))) := by
      rw [PresentedGroup.closure_range_of]
      trivial
    refine Subgroup.closure_mono ?_ hx
    rintro _ ⟨j, rfl⟩
    have hj : j.val < 6 := lt_of_lt_of_eq j.isLt r1_length
    have hb := List.all_eq_true.mp alpha_T2_mem j.val (List.mem_range.mpr hj)
    have ha : j.val < 256 ∧ byte T2.amap j.val ≠ 0 := ⟨by omega, by simpa using hb⟩
    exact ⟨j.val, (ha : KB.inAlpha T2.amap j.val), (dif_pos j.isLt).trans rfl⟩
  exact (KB.finite_card_le_of_top htop c).imp id fun h => h.trans (Nat.le_of_ble_eq_true rfl)

end CertificateChecks.KernelBounds

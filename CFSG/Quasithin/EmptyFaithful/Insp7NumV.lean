module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumT
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
import CFSG.Sporadic.Schreier.MathieuOddCoreM22
import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import Certificates.Certificate2193
public import Certificates.Certificate2194
public import Certificates.Certificate2195
public import Certificates.Certificate2200
public import Certificates.Certificate2202
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3157
public import Certificates.Kernel.J4Count.FixCE
import CFSG.Sporadic.Schreier.MathieuOddCore
import CFSG.Walter.J1

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

namespace Insp7

theorem m22_involution_centralizer_card
    : ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
    Nat.card (centralizerIn NativeSporadic.M22 u) = 384 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := CFSG.QuasithinUnique.Ch1.centralizer_card_of_reps hn m22Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m22Rep1, m22CentQ1.originalSubgroup)]
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩)
    2000 hok
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK1, ?_⟩
      dsimp only
      rw [hsz, hKc1, m22Certificate_originalSubgroup, m22_card])
    u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact hcard.trans hKc1

theorem numFactAt_m22
    : NumFactAt (fun L _ => Nonempty (L ≃* NativeSporadic.Carrier .M22)) := by
  have : Finite (NativeSporadic.Carrier .M22) := inferInstanceAs (Finite ↥NativeSporadic.M22)
  refine numFactAt_of_model (X := NativeSporadic.Carrier .M22) (k := 2)
    (CFSG.Sporadic.Schreier.m22_center_eq_bot') ?_ {384} (by decide) ?_
  · have h : Nat.card (MulAut (NativeSporadic.Carrier .M22)) ≤
        2 * Nat.card (NativeSporadic.Carrier .M22) := CFSG.Sporadic.Schreier.m22_mulAut_card
    exact h
  · intro t ht
    let t' : ↥NativeSporadic.M22 := t
    have h := m22_involution_centralizer_card (t' : Equiv.Perm (Fin 22)) t'.2
      (by rw [Subgroup.orderOf_coe]; exact ht)
    rw [← map_centralizer_subtype,
      Subgroup.card_map_of_injective (NativeSporadic.M22).subtype_injective] at h
    exact Finset.mem_singleton.mpr h

theorem m12_involution_centralizer_card
    : ∀ u ∈ NativeSporadic.M12, orderOf u = 2 →
    Nat.card (centralizerIn NativeSporadic.M12 u) = 192 ∨
      Nat.card (centralizerIn NativeSporadic.M12 u) = 240 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  obtain ⟨hok, hsz, -⟩ := m12_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m12_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m12_rep_data2
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  rw [m12InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m12Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := CFSG.QuasithinUnique.Ch1.centralizer_card_of_reps hn m12Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m12Rep1, m12CentQ1.originalSubgroup), (m12Rep2, m12CentQ2.originalSubgroup)]
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨by simpa using hr1, hro1⟩
      · exact ⟨by simpa using hr2, hro2⟩)
    1000 hok
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine ⟨hK1, ?_⟩
        dsimp only
        rw [hsz.1, hKc1, m12Certificate_originalSubgroup, m12_card]
      · refine ⟨hK2, ?_⟩
        dsimp only
        rw [hsz.2, hKc2, m12Certificate_originalSubgroup, m12_card])
    u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact Or.inl (hcard.trans hKc1)
  · exact Or.inr (hcard.trans hKc2)

theorem numFactAt_m12
    : NumFactAt (fun L _ => Nonempty (L ≃* NativeSporadic.Carrier .M12)) := by
  have : Finite (NativeSporadic.Carrier .M12) := inferInstanceAs (Finite ↥NativeSporadic.M12)
  refine numFactAt_of_model (X := NativeSporadic.Carrier .M12) (k := 2)
    (CFSG.Sporadic.Schreier.m12_center_eq_bot') ?_ {192, 240} (by decide) ?_
  · have h : Nat.card (MulAut (NativeSporadic.Carrier .M12)) ≤
        2 * Nat.card (NativeSporadic.Carrier .M12) := CFSG.Sporadic.Schreier.m12_mulAut_card
    exact h
  · intro t ht
    let t' : ↥NativeSporadic.M12 := t
    have h := m12_involution_centralizer_card (t' : Equiv.Perm (Fin 12)) t'.2
      (by rw [Subgroup.orderOf_coe]; exact ht)
    rw [← map_centralizer_subtype,
      Subgroup.card_map_of_injective (NativeSporadic.M12).subtype_injective] at h
    rcases h with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))

end Insp7

end CFSG.Quasithin

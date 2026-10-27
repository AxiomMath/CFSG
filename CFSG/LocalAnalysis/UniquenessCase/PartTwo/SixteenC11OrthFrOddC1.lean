module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrOddC
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrOddC1Pack
import CFSG.Mathlib.Decide.Nodup

public section

set_option maxRecDepth 100000

open scoped Matrix Pointwise

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

theorem s16c11_fr_trips4_nodup : s16c11_fr_trips4.Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (fun t => (t.2.1 * 256 + t.2.2) % 16384) (by decide +kernel)

theorem s16c11_fr_trips4_length : s16c11_fr_trips4.length = 1071 := by
  decide +kernel

theorem s16c11_fr_codeTriple4_injective : Function.Injective s16c11_fr_codeTriple4 := by
  intro k k' h
  have hk : k.1 < s16c11_fr_trips4.length := by
    rw [s16c11_fr_trips4_length]; exact k.2
  have hk' : k'.1 < s16c11_fr_trips4.length := by
    rw [s16c11_fr_trips4_length]; exact k'.2
  have h' : s16c11_fr_trips4[k.1] = s16c11_fr_trips4[k'.1] := by
    have hh := h
    simp only [s16c11_fr_codeTriple4] at hh
    rwa [List.getD_eq_getElem (l := s16c11_fr_trips4) (d := (0, 0, 0)) (hn := hk),
      List.getD_eq_getElem (l := s16c11_fr_trips4) (d := (0, 0, 0)) (hn := hk')] at hh
  exact Fin.ext ((s16c11_fr_trips4_nodup.getElem_inj_iff (hi := hk) (hj := hk')).mp h')

theorem s16c11_fr_tableCodes_card4 : s16c11_fr_tableCodes4.card = 1071 := by
  unfold s16c11_fr_tableCodes4
  rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin 1071))
    s16c11_fr_codeTriple4_injective, Finset.card_univ, Fintype.card_fin]

theorem s16c11_fr_codeTriple4_sorted4 : ∀ k : Fin 1071,
    (s16c11_fr_codeTriple4 k).1 < (s16c11_fr_codeTriple4 k).2.1 ∧
      (s16c11_fr_codeTriple4 k).2.1 < (s16c11_fr_codeTriple4 k).2.2 := by
  intro k
  obtain ⟨h1, h2, -⟩ := S16Pack.triOk_of_triOkB (by decide +kernel) _
    (S16Pack.codeTriple4_mem s16c11_fr_trips4_length k)
  exact ⟨h1, h2⟩

theorem s16c11_fr_codeTriple4_lt4 : ∀ k : Fin 1071,
    (s16c11_fr_codeTriple4 k).1 < 256 ∧ (s16c11_fr_codeTriple4 k).2.1 < 256 ∧
      (s16c11_fr_codeTriple4 k).2.2 < 256 := by
  intro k
  obtain ⟨h1, h2, h3⟩ := S16Pack.triOk_of_triOkB (by decide +kernel) _
    (S16Pack.codeTriple4_mem s16c11_fr_trips4_length k)
  exact ⟨by omega, by omega, h3⟩

private theorem s16c11_fr_sorted_triple_eq {a b c a' b' c' : ℕ}
    (h1 : a < b) (h2 : b < c) (h1' : a' < b') (h2' : b' < c')
    (h : ({a, b, c} : Finset ℕ) = {a', b', c'}) : a = a' ∧ b = b' ∧ c = c' := by
  have key : ∀ x ∈ ({a, b, c} : Finset ℕ), x = a ∨ x = b ∨ x = c := by
    intro x hx
    simpa using hx
  have key' : ∀ x ∈ ({a', b', c'} : Finset ℕ), x = a' ∨ x = b' ∨ x = c' := by
    intro x hx
    simpa using hx
  have haa : a = a' := by
    have h1 : a ≤ a' := by
      rcases key a' (by rw [h]; simp) with rfl | rfl | rfl <;> omega
    have h2 : a' ≤ a := by
      rcases key' a (by rw [← h]; simp) with rfl | rfl | rfl <;> omega
    omega
  have hbb : b = b' := by
    rcases key b' (by rw [h]; simp) with hba | hbb | hbc
    · omega
    · omega
    · exfalso
      rcases key c' (by rw [h]; simp) with hca | hcb | hcc <;> omega
  refine ⟨haa, hbb, ?_⟩
  rcases key c' (by rw [h]; simp) with hca | hcb | hcc <;> omega

private theorem s16c11_fr_decode_nat_image (t : ℕ × ℕ × ℕ) (h1 : t.1 < 256) (h2 : t.2.1 < 256)
    (h3 : t.2.2 < 256) :
    (s16c11_fr_decode 4 t).image (s16c11_fr_nat 4) = {t.1, t.2.1, t.2.2} := by
  rw [s16c11_fr_decode]
  simp only [Finset.image_insert, Finset.image_singleton]
  rw [s16c11_fr_nat_ofNat (m := 4) (Or.inr rfl) t.1 h1,
    s16c11_fr_nat_ofNat (m := 4) (Or.inr rfl) t.2.1 h2,
    s16c11_fr_nat_ofNat (m := 4) (Or.inr rfl) t.2.2 h3]

theorem s16c11_fr_decode_inj4 :
    Set.InjOn (s16c11_fr_decode 4) (s16c11_fr_tableCodes4 : Set (ℕ × ℕ × ℕ)) := by
  intro t ht s hs h
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ht
  obtain ⟨k', -, rfl⟩ := Finset.mem_image.1 hs
  obtain ⟨hk1, hk2, hk3⟩ := s16c11_fr_codeTriple4_lt4 k
  obtain ⟨hk1', hk2', hk3'⟩ := s16c11_fr_codeTriple4_lt4 k'
  obtain ⟨hs1, hs2⟩ := s16c11_fr_codeTriple4_sorted4 k
  obtain ⟨hs1', hs2'⟩ := s16c11_fr_codeTriple4_sorted4 k'
  have himg := congrArg (fun F => F.image (s16c11_fr_nat 4)) h
  rw [s16c11_fr_decode_nat_image _ hk1 hk2 hk3,
    s16c11_fr_decode_nat_image _ hk1' hk2' hk3'] at himg
  obtain ⟨e1, e2, e3⟩ := s16c11_fr_sorted_triple_eq hs1 hs2 hs1' hs2' himg
  exact Prod.ext e1 (Prod.ext e2 e3)

theorem s16c11_fr_tableSet_card4 : s16c11_fr_tableSet4.card = 1071 := by
  unfold s16c11_fr_tableSet4
  rw [Finset.card_image_iff.mpr s16c11_fr_decode_inj4, s16c11_fr_tableCodes_card4]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

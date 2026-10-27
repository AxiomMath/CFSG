module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumT
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel

import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
import CFSG.Sporadic.Schreier.MathieuOddCoreM23
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2204
public import Certificates.Certificate10019
public import Certificates.Certificate3139
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Sporadic.Schreier.M23Check
public import Certificates.Kernel.J4Count.FixCE
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.Sporadic.Schreier.MathieuOddCore
import CFSG.Walter.J1

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

namespace Insp7

theorem m23_involution_centralizer_card
    : ∀ u ∈ NativeSporadic.M23, orderOf u = 2 →
    Nat.card (centralizerIn NativeSporadic.M23 u) = 2688 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m23Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := CFSG.QuasithinUnique.Ch1.centralizer_card_of_reps hn m23Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m23Rep1, m23CentQ1.originalSubgroup)]
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩)
    4000 hok
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK1, ?_⟩
      dsimp only
      rw [hsz, hKc1, m23Certificate_originalSubgroup, m23_card])
    u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact hcard.trans hKc1

theorem numFactAt_m23
    : NumFactAt (fun L _ => Nonempty (L ≃* NativeSporadic.Carrier .M23)) := by
  have : Finite (NativeSporadic.Carrier .M23) := inferInstanceAs (Finite ↥NativeSporadic.M23)
  refine numFactAt_of_model (X := NativeSporadic.Carrier .M23) (k := 1)
    (CFSG.Sporadic.Schreier.m23_center_eq_bot') ?_ {2688} (by decide) ?_
  · have h : Nat.card (MulAut (NativeSporadic.Carrier .M23)) ≤
        Nat.card (NativeSporadic.Carrier .M23) := CFSG.Sporadic.Schreier.m23_mulAut_card
    rw [one_mul]
    exact h
  · intro t ht
    let t' : ↥NativeSporadic.M23 := t
    have h := m23_involution_centralizer_card (t' : Equiv.Perm (Fin 23)) t'.2
      (by rw [Subgroup.orderOf_coe]; exact ht)
    rw [← map_centralizer_subtype,
      Subgroup.card_map_of_injective (NativeSporadic.M23).subtype_injective] at h
    exact Finset.mem_singleton.mpr h

open CFSG.ComponentClassification.J2Cover in
theorem j2_involution_centralizer_card : ∀ u ∈ P, orderOf u = 2 →
    Nat.card (centralizerIn P u) = 240 ∨ Nat.card (centralizerIn P u) = 1920 := by
  obtain ⟨hcov, -, he1, -, he2⟩ := inner_classes
  obtain ⟨-, hK1c, -⟩ := cent2B_facts
  obtain ⟨-, hK2c, -⟩ := cent2A_facts
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  rw [centralizerIn_conj P hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    rw [he1, hK1c]
  · right
    rw [he2, hK2c]

open CFSG.ComponentClassification.J2Cover in
theorem numFactAt_j2
    : NumFactAt (fun L _ => Nonempty (L ≃* NativeSporadic.Carrier .J2)) := by
  have h : NumFactAt (fun L _ => Nonempty (L ≃* P)) := by
    refine numFactAt_of_model (X := P) (k := 2) center_P ?_ {240, 1920} (by decide) ?_
    · rw [card_mulAut_P, card_P]
    · intro t ht
      have h := j2_involution_centralizer_card (t : Equiv.Perm (Fin 315)) t.2
        (by rw [Subgroup.orderOf_coe]; exact ht)
      rw [← map_centralizer_subtype, Subgroup.card_map_of_injective P.subtype_injective] at h
      simpa using h
  exact numFactAt_of_cover (G := fun L _ => Nonempty (L ≃* P)) (H := fun L _ => Nonempty (L ≃* P))
    (fun _ _ ⟨e⟩ => Or.inl ⟨e.trans nativeEquivP⟩) h h

end Insp7

end CFSG.Quasithin

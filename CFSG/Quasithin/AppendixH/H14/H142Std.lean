module

public import CFSG.Quasithin.AppendixH.H14.H141Transport
public import CFSG.Quasithin.AppendixH.H14.H142Sextet
public import CFSG.Quasithin.AppendixH.H14.H142Q
public import CFSG.Quasithin.AppendixH.H14.H142H

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Open
open scoped Pointwise

theorem map_conj_M23g {c : S24} (hc : c ∈ M24g) (a : Fin 24) :
    (M23g a).map (MulAut.conj c).toMonoidHom = M23g (c a) := by
  rw [M23g, map_conj_inf_stabilizer, map_conj_M24g hc, Equiv.Perm.smul_def]
  rfl

theorem map_conj_MY {c : S24} (hc : c ∈ M24g) (a : Fin 24) {α : Type*} [MulAction S24 α]
    (Y : α) :
    (MY (M23g a) Y).map (MulAut.conj c).toMonoidHom = MY (M23g (c a)) (c • Y) := by
  rw [MY, map_conj_inf_stabilizer, map_conj_M23g hc a, MY]

theorem smul_erase_sextet (c : S24) (S : Finset (Finset (Fin 24))) (B : Finset (Fin 24)) :
    c • S.erase B = (c • S).erase (c • B) := by
  rw [Finset.erase_eq, Finset.erase_eq, Finset.smul_finset_sdiff, Finset.smul_finset_singleton]

theorem smul_erase_point (c : S24) (O : Finset (Fin 24)) (a : Fin 24) :
    c • O.erase a = (c • O).erase (c a) := by
  rw [Finset.erase_eq, Finset.erase_eq, Finset.smul_finset_sdiff, Finset.smul_finset_singleton,
    Equiv.Perm.smul_def]

theorem exists_std_data {a : Fin 24} {O : Finset (Fin 24)}
    {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)} (hS : IsSextet S) (hB : B ∈ S)
    (haB : a ∈ B) (haO : a ∈ O) (hOu : ∃ B₁ ∈ S, ∃ B₂ ∈ S, B₁ ≠ B₂ ∧ O = B₁ ∪ B₂) :
    ∃ c ∈ M24g, c a = 8 ∧ c • S.erase B = stdQ ∧ c • O.erase a = stdH := by
  obtain ⟨B₁, hB₁, B₂, hB₂, hB₁B₂, hO⟩ := hOu
  have hdisj := hS.2.2.1
  have ha : a ∈ B₁ ∨ a ∈ B₂ := by
    rw [hO] at haO
    exact Finset.mem_union.mp haO
  have hBcase : B = B₁ ∨ B = B₂ := by
    rcases ha with ha | ha
    · left
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisj B hB B₁ hB₁ hne)) haB ha
    · right
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisj B hB B₂ hB₂ hne)) haB ha
  rcases hBcase with hBcase | hBcase
  · subst hBcase
    obtain ⟨c, hc, hca, hcB, hcB', hcS⟩ := exists_std_conj hS hB hB₂ hB₁B₂ haB
    refine ⟨c, hc, hca, ?_, ?_⟩
    · rw [smul_erase_sextet, hcS, hcB, stdQ]
    · rw [smul_erase_point]
      have hcO : c • O = stdO := by
        rw [hO, Finset.smul_finset_union, hcB, hcB', stdO]
      rw [hcO, hca, stdH]
  · subst hBcase
    obtain ⟨c, hc, hca, hcB, hcB', hcS⟩ := exists_std_conj hS hB hB₁ hB₁B₂.symm haB
    refine ⟨c, hc, hca, ?_, ?_⟩
    · rw [smul_erase_sextet, hcS, hcB, stdQ]
    · rw [smul_erase_point]
      have hcO : c • O = stdO := by
        rw [hO, Finset.smul_finset_union, hcB, hcB', stdO, Finset.union_comm]
      rw [hcO, hca, stdH]

theorem conj_stdQ {a : Fin 24} {Q : Finset (Finset (Fin 24))}
    {c : S24} (hc : c ∈ M24g) (hca : c a = 8) (hQ : c • Q = stdQ) :
    (MY (M23g a) Q).map (MulAut.conj c).toMonoidHom = stdMQ ∧
      (KY (M23g a) Q).map (MulAut.conj c).toMonoidHom = stdEQ := by
  have hM : (MY (M23g a) Q).map (MulAut.conj c).toMonoidHom = stdMQ := by
    rw [map_conj_MY hc a Q, hca, hQ]
    rfl
  constructor
  · exact hM
  · rw [KY, ← pCoreOf_map_conj 2 c (MY (M23g a) Q), hM, pCoreOf_stdMQ]

theorem conj_stdH {a : Fin 24} {H : Finset (Fin 24)}
    {c : S24} (hc : c ∈ M24g) (hca : c a = 8) (hH : c • H = stdH) :
    (MY (M23g a) H).map (MulAut.conj c).toMonoidHom = stdMH ∧
      (KY (M23g a) H).map (MulAut.conj c).toMonoidHom = stdEH := by
  have hM : (MY (M23g a) H).map (MulAut.conj c).toMonoidHom = stdMH := by
    rw [map_conj_MY hc a H, hca, hH]
    rfl
  constructor
  · exact hM
  · rw [KY, ← pCoreOf_map_conj 2 c (MY (M23g a) H), hM, pCoreOf_stdMH]

end CFSG.Quasithin.AppendixH.H14

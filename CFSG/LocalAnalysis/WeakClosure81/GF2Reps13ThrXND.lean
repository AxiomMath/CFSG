module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXNDB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrCasesA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrIso

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

variable {A Q O : Subgroup (MulAut W)} {t : MulAut W}

theorem w16n_rk_commSub_K (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A)
    (hcomm : ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    rk ↥(commSub ⊤ (Q ⊔ Q.map (MulAut.conj g).toMonoidHom)) = 6 := by
  have h1 : commSub ⊤ (Q ⊔ Q.map (MulAut.conj g).toMonoidHom) = commSub ⊤ Q := by
    rw [CFSG.Quasithin.Asc81c.Pf.commSub_sup, w16n_commSub_top_eq_conj h hg hcomm, sup_idem]
  rw [h1, w16n_rk_commSub_top_Q h]

theorem w16n_sSupIndep_commSub_K (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A)
    (hcomm : ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    sSupIndep (conjSubs A (commSub ⊤ (Q ⊔ Q.map (MulAut.conj g).toMonoidHom))) := by
  have hKext := w16n_isPOnePlusTwo_K h hg hcomm
  have hKO := w16n_K_le_O h hg
  have hKrk := w16n_rk_commSub_K h hg hcomm
  have hOK := fun n (hn : n ∈ O) => w16n_K_map_conj h hg hn
  set K : Subgroup (MulAut W) := Q ⊔ Q.map (MulAut.conj g).toMonoidHom with hK
  obtain ⟨z, hzK, hz3, hzc, hZK⟩ := w16g_ext_center_of_extraspecial hKext
  obtain ⟨-, hKirr⟩ := w16g_commSub_extraspecial_eq_and_irreducible h.hW hKext hzK hz3 hzc hZK hKrk
  have hKodd : Odd (Nat.card K) := by rw [hKext.2.1]; norm_num
  have hOstab : StableUnder O (commSub ⊤ K) := s13_commSub_invariant_of_normalizes hOK
  have hirrO : IsIrrOn O (commSub ⊤ K) ⊥ := by
    refine ⟨hKirr.1, hOstab, ?_, ?_⟩
    · intro x hx u hu
      rw [Subgroup.mem_bot.mp hu, map_one]
      exact Subgroup.mem_bot.mpr rfl
    · intro J hJstab hJbot hJle
      exact hKirr.2.2.2 J (fun x hx => hJstab x (hKO hx)) hJbot hJle
  have hiso : IsEntireIsotypic K (commSub ⊤ K) := s13_isotypic_commSub h.hW hKodd
  exact sSupIndep_conjSubs_of_isotypic h.hW A O K h.hOle h.hOA hKO (commSub ⊤ K) hirrO hiso

theorem w16n_K (h : HNon A Q O t) :
    ∃ K : Subgroup (MulAut W), K ≤ O ∧ IsPOnePlusTwo 3 ↥K ∧ rk ↥(commSub ⊤ K) = 6 ∧
      ⁅K, Subgroup.zpowers t⁆ ≠ ⊥ ∧ (∀ n ∈ O, K.map (MulAut.conj n).toMonoidHom = K) ∧
      sSupIndep (conjSubs A (commSub ⊤ K)) := by
  obtain ⟨g, hg, hcomm⟩ := h.hnc
  exact ⟨Q ⊔ Q.map (MulAut.conj g).toMonoidHom,
    w16n_K_le_O h hg, w16n_isPOnePlusTwo_K h hg hcomm, w16n_rk_commSub_K h hg hcomm,
    w16n_commutator_K_t h, fun n hn => w16n_K_map_conj h hg hn,
    w16n_sSupIndep_commSub_K h hg hcomm⟩

end CFSG.LocalAnalysis.WeakClosure81

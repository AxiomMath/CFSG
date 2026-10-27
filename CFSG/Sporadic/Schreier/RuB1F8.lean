module

public import CFSG.Sporadic.Schreier.RuCenters
public import CFSG.Sporadic.Schreier.RuSEnum
public import Certificates.Data.GMS78RuB1SCCheck

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] noncomputable def scLPerm (w : List ℤ) : Equiv.Perm (Fin 4060) :=
  evalSigned [ruC0, ruC1, ruNs0, ruNs1] w

theorem scLPerm_mem (w : List ℤ) : scLPerm w ∈ ruP := by
  refine evalSigned_mem (fun g hg => ?_) w
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ruC0_mem
  · exact ruC1_mem
  · exact ruNs0_mem
  · exact ruNs1_mem

theorem rep_scGens :
    ∀ h < 4, Rep 4060 RuB1.scGens[h]! ([ruC0, ruC1, ruNs0, ruNs1].getD h 1) := by
  intro h hh
  interval_cases h
  · simpa [RuB1.scGens] using rep_ruC0
  · simpa [RuB1.scGens] using rep_ruC1
  · simpa [RuB1.scGens] using rep_ruNs0
  · simpa [RuB1.scGens] using rep_ruNs1

theorem rep_scGensInv :
    ∀ h < 4, Rep 4060 RuB1.scGensInv[h]! ([ruC0, ruC1, ruNs0, ruNs1].getD h 1)⁻¹ := by
  intro h hh
  interval_cases h
  · simpa [RuB1.scGensInv] using rep_ruInv rep_ruC0 ruBasic_check.2.2.2.2.2.2.1
  · simpa [RuB1.scGensInv] using rep_ruInv rep_ruC1 ruBasic_check.2.2.2.2.2.2.2.1
  · simpa [RuB1.scGensInv] using rep_ruInv rep_ruNs0 ruBasic_check.2.2.2.2.2.2.2.2.2.2.1
  · simpa [RuB1.scGensInv] using rep_ruInv rep_ruNs1 ruBasic_check.2.2.2.2.2.2.2.2.2.2.2.1

theorem getElem!_map_of_lt {α β : Type*} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {j : ℕ} (hj : j < a.size) : (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos (a.map f) j (by simpa using hj), Array.getElem_map, getElem!_pos a j hj]

theorem ruB1_F8_of_check
    (h : RuB1.ruB1SCCheck = true) :
    ∀ y ∈ ruS, y * y = 1 → y ∉ Subgroup.centralizer (ruESub : Set (Equiv.Perm (Fin 4060))) →
      ∃ l ∈ ruP, ruESub.map (MulAut.conj l).toMonoidHom ≤
        ruS ⊓ Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 4060))) := by
  simp only [RuB1.ruB1SCCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hsize, hlet⟩, hinv⟩, hsift⟩, hall⟩ := h
  have hl : ∀ w ∈ RuB1.scWords, Rep 4060 (RuB1.scL w) (scLPerm w) := fun w hw =>
    rep_wordA_evalSigned rep_scGens rep_scGensInv w (hlet w hw)
  have hE : ∀ w ∈ RuB1.scWords, ∀ j < 7,
      Rep 4060 (RuB1.scConjE w)[j]! (scLPerm w * ruEElt j * (scLPerm w)⁻¹) := by
    intro w hw j hj
    rw [RuB1.scConjE, getElem!_map_of_lt _ _ (by omega)]
    exact rep_compA (rep_compA (hl w hw) (rep_ruEElt hj)) (rep_ruInv (hl w hw) (hinv w hw))
  have hS : ∀ w ∈ RuB1.scWords, ∀ j < 7, scLPerm w * ruEElt j * (scLPerm w)⁻¹ ∈ ruS := by
    intro w hw j hj
    have hs : ruSift 4060 (ruField4060 4) ruS4060ChainBase (RuB1.scConjE w)[j]! = true :=
      allLt_spec (hsift _ (List.mem_map_of_mem hw)) hj
    rw [← ruChainS4060_sub]
    exact (ruChain_sift ruInv_check.1 (hE w hw j hj)).1 hs
  refine ruS_forall (p := RuB1.scTest) (P := fun y => y * y = 1 →
    y ∉ Subgroup.centralizer (ruESub : Set (Equiv.Perm (Fin 4060))) →
      ∃ l ∈ ruP, ruESub.map (MulAut.conj l).toMonoidHom ≤
        ruS ⊓ Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 4060)))) ?_ hall
  intro t y ht hp hyy hyc
  simp only [RuB1.scTest, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at hp
  rcases hp with (h1 | h2) | ⟨E, hEm, h3⟩
  · rw [(eqA_iff (rep_compA ht ht) rep_idA).2 hyy] at h1
    exact Bool.noConfusion h1
  · refine absurd (Subgroup.mem_centralizer_iff.2 fun g hg => ?_) hyc
    rcases mem_ruESub.1 hg with rfl | ⟨j, hj, rfl⟩
    · rw [one_mul, mul_one]
    · exact (eq_of_eqA (rep_compA ht (rep_ruEElt hj)) (rep_compA (rep_ruEElt hj) ht)
        (allLt_spec h2 hj)).symm
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hEm
    refine ⟨scLPerm w, scLPerm_mem w, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    rcases mem_ruESub.1 hg with rfl | ⟨j, hj, rfl⟩
    · rw [map_one]
      exact one_mem _
    · refine Subgroup.mem_inf.2 ⟨hS w hw j hj, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact (eq_of_eqA (rep_compA ht (hE w hw j hj)) (rep_compA (hE w hw j hj) ht)
        (allLt_spec h3 hj)).symm

end CFSG.Sporadic.RuSchreier

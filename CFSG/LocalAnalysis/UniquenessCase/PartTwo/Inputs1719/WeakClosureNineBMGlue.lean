module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMStat

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

set_option maxRecDepth 100000

theorem closureC_map_code (gens : List P16) : closureC (gens.map code) = closure {g | g ∈ gens} := by
  rw [closureC]
  congr 1
  ext σ
  simp only [Set.mem_setOf_eq, List.mem_map]
  exact ⟨fun ⟨τ, hτ, he⟩ => code_injective he ▸ hτ, fun hσ => ⟨σ, hσ, rfl⟩⟩

variable {i : Fin 4} {tLit : List (List ℕ)}

theorem yGen_codes (hT : LDesc (TB i) tLit) {D : KData} (hC : KChk tLit D = true) :
    ∀ c ∈ D.yGen, ∃ σ : P16, code σ = c := fun c hc => by
  obtain ⟨σ, -, e⟩ := (kchk_parts hT hC).2.2.2.2.2.2.2.2.2.2.1 c hc
  exact ⟨σ, e⟩

@[expose] def KEnumChk (tLit : List (List ℕ)) (D : KData) (sT qT yT : List (ℕ × ℕ))
    (sB qB yB : List (List ℕ)) : Bool :=
  D.sLit == Core.buildCodes cid D.sGen sT && D.qLit == Core.buildCodes cid D.qGen qT &&
  D.yLit == Core.buildCodes cid D.yGen yT &&
  Core.tblCheckC cid D.sGen D.sLit sB && Core.tblCheckC cid D.qGen D.qLit qB &&
  Core.tblCheckC cid D.yGen D.yLit yB &&
  NFA6.Core.nodupB D.sLit && NFA6.Core.nodupB D.qLit && NFA6.Core.nodupB D.yLit &&
  D.sGen.all D.sLit.contains && D.qGen.all D.qLit.contains && D.yGen.all D.yLit.contains &&
  D.sGen.all tLit.contains && D.qGen.all tLit.contains

theorem kEnum_of_chk (hT : LDesc (TB i) tLit) {D : KData} (hC : KChk tLit D = true)
    {sT qT yT : List (ℕ × ℕ)} {sB qB yB : List (List ℕ)}
    (h : KEnumChk tLit D sT qT yT sB qB yB = true) : KEnum D := by
  simp only [KEnumChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hq⟩, hy⟩, hsb⟩, hqb⟩, hyb⟩, hsn⟩, hqn⟩, hyn⟩, hsg⟩, hqg⟩, hyg⟩, hst⟩,
    hqt⟩ := h
  have dec : ∀ {gc : List (List ℕ)}, (∀ c ∈ gc, c ∈ tLit) → ∀ c ∈ gc, ∃ σ : P16, code σ = c :=
    fun hg c hc => by
      obtain ⟨σ, -, e⟩ := hT.surj c (hg c hc)
      exact ⟨σ, e⟩
  refine ⟨?_, ?_, ?_, nodup_of_nodupB' hsn, nodup_of_nodupB' hqn, nodup_of_nodupB' hyn, hsg, hqg,
    hyg⟩
  · rw [hs] at hsb ⊢
    exact ldesc_closureC (dec hst) hsb
  · rw [hq] at hqb ⊢
    exact ldesc_closureC (dec hqt) hqb
  · rw [hy] at hyb ⊢
    exact ldesc_closureC (yGen_codes hT hC) hyb

theorem xdesc_Qx (hT : LDesc (TB i) tLit) {D : KData} (hE : KEnum D) (hC : KChk tLit D = true) :
    XDesc (Qx i D) D.qLit :=
  xdesc_of_ldesc hE.q (kQ_le_GB hT hE hC)

theorem qLit_sub (hT : LDesc (TB i) tLit) {D : KData} (hC : KChk tLit D = true) :
    ∀ c ∈ D.qLit, c ∈ tLit := fun _ hc =>
  (kchk_parts hT hC).1 _ ((kchk_parts hT hC).2.1 _ hc)

@[expose] def InterChk (LA LB L : List (List ℕ)) : Bool :=
  L.all LA.contains && L.all LB.contains && LA.all fun c => !(LB.contains c) || L.contains c

theorem xdesc_inf {A B : Subgroup ↥(GB i)} {LA LB L : List (List ℕ)} (hA : XDesc A LA)
    (hB : XDesc B LB) (h : InterChk LA LB L = true) : XDesc (A ⊓ B) L := by
  simp only [InterChk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · rw [mem_inf, hA.mem, hB.mem]
    constructor
    · rintro ⟨ha, hb⟩
      rcases h3 _ ha with h | h
      · exfalso
        revert h
        rw [List.contains_iff_mem.2 hb]
        decide
      · exact h
    · intro hc
      exact ⟨h1 _ hc, h2 _ hc⟩
  · obtain ⟨x, hx, rfl⟩ := hA.surj c (h1 c hc)
    exact ⟨x, ⟨hx, (hB.mem x).2 (h2 _ hc)⟩, rfl⟩

theorem kList_of {Ks : List KData} {tops : List ℕ}
    (h : ∀ D ∈ Ks, KEnum D ∧ KChk tLit D = true ∧ ∃ ws, O2Chk D ws = true)
    (htop : ∀ j ∈ tops, Sx i (Ks.getD j KData.dflt) = Tb i) : KList i tLit Ks tops := by
  have hmem : ∀ j < Ks.length, Ks.getD j KData.dflt ∈ Ks := fun j hj => by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  exact ⟨fun j hj => (h _ (hmem j hj)).1, fun j hj => (h _ (hmem j hj)).2.1,
    fun j hj => (h _ (hmem j hj)).2.2, htop⟩

theorem subs_parts {qL : List (List ℕ)} (hq : ∀ c ∈ qL, c ∈ tLit) {subs : List (List (List ℕ))}
    {idx : List (List (ℕ × ℕ × ℕ × ℕ))} (h : SubsChk qL subs idx = true) :
    ∀ k < subs.length, cid ∈ subs.getD k [] ∧ (∀ c ∈ subs.getD k [], c ∈ tLit) ∧
      (subs.getD k []).Nodup ∧
      ∀ c ∈ subs.getD k [], ∀ d ∈ subs.getD k [], Core.cmul c d ∈ subs.getD k [] := by
  intro k hk
  have hmem : subs.getD k [] ∈ subs := by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  obtain ⟨h1, h2, h3, h4⟩ := (subsChk_parts h).1 _ hmem
  exact ⟨h1, fun c hc => hq c (h2 c hc), h3, h4⟩

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF

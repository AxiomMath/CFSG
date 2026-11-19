
module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefDefs

@[expose] public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31

noncomputable def wsG (ws : List (List ℤ)) : List (Equiv.Perm (Fin 4060)) := ws.map wG

theorem forall₂_wsA {ws : List (List ℤ)}
    (hws : ∀ w ∈ ws, lettersOK 6 w = true) : List.Forall₂ (Rep 4060) (wsA ws) (wsG ws) := by
  rw [wsA, wsG, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun w hw => rep_wA (hws w hw)

theorem ofFn_vOf {ws : List (List ℤ)} {k : ℕ} (hk : ws.length = k) :
    List.ofFn (vOf ws k) = wsG ws := by
  subst hk
  apply List.ext_getElem
  · simp [wsG]
  · intro i h1 h2
    have hi : i < ws.length := by simpa [wsG] using h2
    simp only [List.getElem_ofFn, vOf, wsG, List.getElem_map]
    rw [List.getD_eq_getElem _ _ hi]

theorem forall₂_vOf {ws : List (List ℤ)} {k : ℕ}
    (hk : ws.length = k) (hws : ∀ w ∈ ws, lettersOK 6 w = true) :
    List.Forall₂ (Rep 4060) (wsA ws) (List.ofFn (vOf ws k)) := by
  rw [ofFn_vOf hk]
  exact forall₂_wsA hws

theorem hbE : List.Forall₂ (Rep 4060) bEA (List.ofFn vE) :=
  forall₂_vOf rfl (by decide)
theorem hb64 : List.Forall₂ (Rep 4060) b64A (List.ofFn v64) :=
  forall₂_vOf rfl (by decide)
theorem hb3 : List.Forall₂ (Rep 4060) b3A (List.ofFn v3) :=
  forall₂_vOf rfl (by decide)
theorem hb16 : List.Forall₂ (Rep 4060) b16A (List.ofFn v16) :=
  forall₂_vOf rfl (by decide)
theorem hb32 : List.Forall₂ (Rep 4060) b32A (List.ofFn v32) :=
  forall₂_vOf rfl (by decide)
theorem hbV32E :
    List.Forall₂ (Rep 4060) bV32EA (List.ofFn vV32E) := forall₂_vOf rfl (by decide)
theorem hbV32p :
    List.Forall₂ (Rep 4060) bV32pA (List.ofFn vV32p) := forall₂_vOf rfl (by decide)

theorem mem_refSub_of_inA {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} {bs : List (Array ℕ)}
    (hbs : List.Forall₂ (Rep 4060) bs (List.ofFn v)) (hv : EBasis v) {t : Array ℕ}
    {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) (h : inA (spanA bs) t = true) :
    g ∈ refSub v := by
  obtain ⟨c, rfl⟩ := (inA_spanA_iff hbs ht).mp h
  rw [refSub_eq hv]
  exact eElt_mem hv c

theorem inA_of_mem_refSub {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} {bs : List (Array ℕ)}
    (hbs : List.Forall₂ (Rep 4060) bs (List.ofFn v)) (hv : EBasis v) {t : Array ℕ}
    {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) (h : g ∈ refSub v) :
    inA (spanA bs) t = true := by
  rw [refSub_eq hv, mem_eSub_iff] at h
  exact (inA_spanA_iff hbs ht).mpr h

theorem exists_rep_of_mem_refSub {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)}
    {bs : List (Array ℕ)} (hbs : List.Forall₂ (Rep 4060) bs (List.ofFn v)) (hv : EBasis v)
    {g : Equiv.Perm (Fin 4060)} (h : g ∈ refSub v) : ∃ u ∈ spanA bs, Rep 4060 u g := by
  have hlen : bs.length = k := by rw [hbs.length_eq, List.length_ofFn]
  rw [refSub_eq hv, mem_eSub_iff] at h
  obtain ⟨c, rfl⟩ := h
  obtain ⟨m, hm, rfl⟩ := exists_maskVec c
  exact ⟨maskA bs m, List.mem_map.mpr ⟨m, by rw [List.mem_range, hlen]; exact hm, rfl⟩,
    rep_maskA v bs hbs m⟩

theorem forall_of_all {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} {bs : List (Array ℕ)}
    (hbs : List.Forall₂ (Rep 4060) bs (List.ofFn v)) {p : Array ℕ → Bool}
    {P : Equiv.Perm (Fin 4060) → Prop} (hp : ∀ t g, Rep 4060 t g → p t = true → P g)
    (h : bs.all p = true) : ∀ i, P (v i) := by
  intro i
  obtain ⟨b, hb, hbi⟩ := exists_left_of_forall₂ hbs (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact hp b _ hbi (List.all_eq_true.mp h b hb)

theorem mem_normalizer_of_normsA {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)}
    {bs : List (Array ℕ)} (hbs : List.Forall₂ (Rep 4060) bs (List.ofFn v)) (hv : EBasis v)
    {t ti : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) (hti : Rep 4060 ti g⁻¹)
    (h : normsA t ti bs (spanA bs) = true) : g ∈ Subgroup.normalizer (refSub v : Set _) := by
  refine mem_normalizer_of_forall fun i => ?_
  obtain ⟨c, hc⟩ := (normsA_iff hbs rfl hbs ht hti).mp h (v i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  rw [← hc, refSub_eq hv]
  exact eElt_mem hv c

theorem normsA_of_mem_normalizer {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)}
    {bs : List (Array ℕ)} (hbs : List.Forall₂ (Rep 4060) bs (List.ofFn v)) (hv : EBasis v)
    {t ti : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) (hti : Rep 4060 ti g⁻¹)
    (h : g ∈ Subgroup.normalizer (refSub v : Set _)) : normsA t ti bs (spanA bs) = true := by
  refine (normsA_iff hbs rfl hbs ht hti).mpr fun b hb => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  have h1 : g * v i * g⁻¹ ∈ refSub v :=
    (Subgroup.mem_normalizer_iff.mp h (v i)).mp (Subgroup.subset_closure ⟨i, rfl⟩)
  rw [refSub_eq hv, mem_eSub_iff] at h1
  exact h1

theorem orderOf_of_pA {p : ℕ} (hp : p.Prime) {t : Array ℕ} {g : Equiv.Perm (Fin 4060)}
    (ht : Rep 4060 t g) (h1 : eqA 4060 (pA p t) (idA 4060) = true)
    (h2 : (!eqA 4060 t (idA 4060)) = true) : orderOf g = p := by
  have : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime (eq_of_eqA (rep_pA ht p) rep_idA h1) fun h => ?_
  rw [Bool.not_eq_true'] at h2
  rw [(eqA_iff ht rep_idA).mpr h] at h2
  exact Bool.noConfusion h2

theorem xE_memN : xE ∈ ruN := wG_memN (by decide)
theorem nE_memN : nE ∈ ruN := wG_memN (by decide)
theorem x32_memC : x32 ∈ ruC := wG_memC (by decide)
theorem cQ_memC : cQ ∈ ruC := wG_memC (by decide)

section Reps

theorem rep_x16 : Rep 4060 x16A x16 := rep_wA (by decide)
theorem rep_g16 : Rep 4060 g16A g16 := rep_wA (by decide)
theorem rep_k16 : Rep 4060 k16A k16 := rep_wA (by decide)
theorem rep_xE : Rep 4060 xEA xE := rep_wA (by decide)
theorem rep_nE : Rep 4060 nEA nE := rep_wA (by decide)
theorem rep_x32 : Rep 4060 x32A x32 := rep_wA (by decide)
theorem rep_cQ : Rep 4060 cQA cQ := rep_wA (by decide)

end Reps

section Facts

theorem conj64W_memC : ∀ w ∈ conj64W, wG w ∈ ruC := fun w hw =>
  wG_memC (List.all_eq_true.mp (by decide :
    conj64W.all (fun w => w.all fun l => l.natAbs == 3 || l.natAbs == 4) = true) w hw)

theorem conj64W_length : conj64W.length = 20 := rfl

end Facts

end CFSG.Quasithin.KGC31.Ru

end

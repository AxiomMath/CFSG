module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordSpecE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordSpecF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordSpecM

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoordA6

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6
  CFSG.LocalAnalysis.WeakClosure81.NFA6.Core CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core

theorem entries_sub {TL TLinv : List (List ℕ)} {Ks : List KData} {Es : List Entry}
    (hE : entriesCheck TL TLinv Ks Es = true) : ∀ L ∈ Es.map Entry.E, L.all TL.contains = true := by
  intro L hL
  obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hL
  exact entry_E_sub (entry_data hE hen).2

theorem sq_spec {L₀ T₀ : Subgroup P10} {TL Lc : List (List ℕ)} (hT : Desc T₀ TL)
    (hLc : ∀ c ∈ Lc, ∃ x ∈ L₀, code x = c)
    (h : (TL.filter Lc.contains).any (fun c => cmul c c != cid) = true) :
    ∃ d ∈ T₀ ⊓ L₀, d ^ 2 ≠ 1 := by
  obtain ⟨c, hc, hcc⟩ := List.any_eq_true.mp h
  rw [List.mem_filter, List.contains_iff_mem] at hc
  obtain ⟨x, hx, rfl⟩ := hT.surj _ hc.1
  obtain ⟨y, hy, hyx⟩ := hLc _ hc.2
  rw [code_injective hyx] at hy
  refine ⟨x, ⟨hx, hy⟩, fun h2 => ?_⟩
  have hxx : cmul (code x) (code x) = cid := by
    rw [← code_mul, ← pow_two, h2, code_one]
  rw [hxx] at hcc
  simp at hcc

theorem mov_model {L₀ T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) {Es : List (List (List ℕ))} (hseed : seedCheck TL Es = true)
    (hEsT : ∀ L ∈ Es, L.all TL.contains = true) {Hs : List KData}
    (hHs : ∀ D ∈ Hs, D.check TL = true)
    (hHg : ∀ D ∈ Hs, ∀ c ∈ D.K.gc, ∃ x ∈ (L₀ : Set P10), code x = c) {ms : List MovW}
    (h : movAll TL Hs (eList TL Es) ms = true) :
    ∀ E : Subgroup P10, E ≤ T₀ → IsElemAbelian 2 E →
      ∃ (H Xh : Subgroup P10) (p : ℕ), Coord.MovModel L₀ T₀ E H Xh p := by
  intro E hET hEe
  obtain ⟨L, hL, hE⟩ := elem_spec hT hseed hEsT hET hEe
  exact mov_spec hT hT2 hHs hHg h hL hE

theorem fix_model {G T₀ Es₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) {Es : List (List (List ℕ))} (hseed : seedCheck TL Es = true)
    (hEsT : ∀ L ∈ Es, L.all TL.contains = true) {Ks : List KData}
    (hKs : ∀ D ∈ Ks, D.check TL = true)
    (hKg : ∀ D ∈ Ks, ∀ c ∈ D.K.gc, ∃ x ∈ (G : Set P10), code x = c)
    {fs : List (Option FixW)} {Est : List (List ℕ)} (hEst : ∀ x, x ∈ Es₀ ↔ code x ∈ Est)
    (h : fixAll TL Ks (eList TL Es) fs Est = true) :
    ∀ E : Subgroup P10, E ≤ T₀ → IsElemAbelian 2 E → E ≠ ⊥ →
      (∃ (K Xh : Subgroup P10) (p : ℕ), Coord.FixModel G T₀ E K Xh p) ∨ E = Es₀ := by
  intro E hET hEe hE1
  obtain ⟨L, hL, hE⟩ := elem_spec hT hseed hEsT hET hEe
  exact fix_spec hT hT2 hKs hKg hEst h hL hE hE1

theorem star_model {L₀ T₀ Es₀ : Subgroup P10} {TL Est : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) (hEst : Desc Es₀ Est) {Es : List (List (List ℕ))}
    (hseed : seedCheck TL Es = true) (hEsT : ∀ L ∈ Es, L.all TL.contains = true)
    {Hs : List KData} (hHs : ∀ D ∈ Hs, D.check TL = true)
    (hHg : ∀ D ∈ Hs, ∀ c ∈ D.K.gc, ∃ x ∈ (L₀ : Set P10), code x = c) {ms : List MovW}
    (h : starAll TL Hs Est (eList TL Es) ms = true) :
    ∀ E : Subgroup P10, E ≤ T₀ ⊓ centralizer (Es₀ : Set P10) → IsElemAbelian 2 E →
      ∃ H Xh : Subgroup P10, Coord.MovModel L₀ T₀ E H Xh 3 ∧ Es₀ ≤ normalizer (H : Set P10) ∧
        ∀ e ∈ Es₀, ∀ x ∈ Xh, e * x * e⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  intro E hE hEe
  obtain ⟨L, hL, hEd⟩ := elem_spec hT hseed hEsT (fun x hx => (hE hx).1) hEe
  exact star_spec hT hT2 hEst hHs hHg h hL hEd fun x hx => (hE hx).2

theorem normal4_eq {T₀ Es₀ : Subgroup P10} {TL TLinv Est : List (List ℕ)} {Ks : List KData}
    {Es : List Entry} {iStar : ℕ} (hT : Desc T₀ TL) (hinv : invCheck TL TLinv = true)
    (hE : entriesCheck TL TLinv Ks Es = true) (hseed : seedCheck TL (Es.map Entry.E) = true)
    (hnn : (List.range Es.length).all (fun i => i == iStar ||
      nonNormal TL TLinv (Es.getD i ⟨[], 0, [], [], [], []⟩).E) = true)
    (hEst : Desc Es₀ Est) (heq : setEq Est (Es.getD iStar ⟨[], 0, [], [], [], []⟩).E = true) :
    ∀ F : Subgroup P10, F ≤ T₀ → T₀ ≤ normalizer (F : Set P10) → IsElemAbelian 2 F →
      4 ≤ Nat.card F → F = Es₀ := by
  intro F hFT hTF hFe hF4
  ext x
  rw [normal4_spec hT hinv hE hseed hnn hFT hTF hFe hF4 x, hEst.mem, setEq_mem heq]

theorem exists_estar {T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL) {D : SubData}
    (hD : D.ok = true) (hg : D.gc.all TL.contains = true) (hnorm : normB TL D.lit = true)
    (he : D.lit.all (fun a => cinvol a && D.lit.all (ccomm a)) = true) (h4 : D.lit.length = 4) :
    ∃ E : Subgroup P10, Desc E D.lit ∧ E ≤ T₀ ∧ T₀ ≤ normalizer (E : Set P10) ∧
      IsElemAbelian 2 E ∧ 4 ≤ Nat.card E := by
  obtain ⟨E, hEc, hE, hnd⟩ := SubData.exists_desc hD (S := (T₀ : Set P10)) fun c hc =>
    hT.surj c (List.contains_iff_mem.mp ((List.all_eq_true.mp hg) c hc))
  have hall := List.all_eq_true.mp he
  have hinv : ∀ a ∈ E, a * a = 1 := fun a ha => by
    have h1 := hall (code a) ((hE.mem a).mp ha)
    simp only [Bool.and_eq_true] at h1
    exact cinvol_iff.mp h1.1
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => by
    have h1 := hall (code a) ((hE.mem a).mp ha)
    simp only [Bool.and_eq_true, List.all_eq_true] at h1
    exact ccomm_iff.mp (h1.2 (code b) ((hE.mem b).mp hb))
  refine ⟨E, hE, hEc.trans (closure_eq T₀).le, fun t ht => ?_,
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun a ha => by
      rw [pow_two]; exact hinv a ha⟩, by rw [hE.card hnd, h4]⟩
  rw [mem_normalizer_iff]
  intro n
  refine ⟨fun hn => normB_spec hT hE hnorm ht hn, fun hn => ?_⟩
  have h := normB_spec hT hE hnorm (inv_mem ht) hn
  have e : t⁻¹ * (t * n * t⁻¹) * t⁻¹⁻¹ = n := by group
  rwa [e] at h

end CFSG.LocalAnalysis.WeakClosure81.CoordA6

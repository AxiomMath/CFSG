module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Spec

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoordA6

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6
  CFSG.LocalAnalysis.WeakClosure81.NFA6.Core CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core

theorem desc_of_mem {T₀ E : Subgroup P10} {TL L : List (List ℕ)} (hT : Desc T₀ TL)
    (hL : L.all TL.contains = true) (hE : ∀ x, x ∈ E ↔ code x ∈ L) : Desc E L := by
  refine ⟨hE, fun c hc => ?_⟩
  obtain ⟨x, hx, hxc⟩ := hT.surj c (List.contains_iff_mem.mp ((List.all_eq_true.mp hL) c hc))
  exact ⟨x, (hE x).mpr (hxc ▸ hc), hxc⟩

private theorem eq_of_mem_ne_one_of_card_two {F : Subgroup P10} (hcard : Nat.card F = 2)
    {x y : P10} (hx : x ∈ F) (hx1 : x ≠ 1) (hy : y ∈ F) (hy1 : y ≠ 1) : y = x := by
  obtain ⟨a, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hcard
  have hxa : (⟨x, hx⟩ : F) = a := huniq _ (by simpa using hx1)
  have hya : (⟨y, hy⟩ : F) = a := huniq _ (by simpa using hy1)
  exact congrArg Subtype.val (hya.trans hxa.symm)

private theorem desc_of_card_two {E : Subgroup P10} {a : P10} (hcard : Nat.card E = 2)
    (ha : a ∈ E) (ha1 : a ≠ 1) : Desc E [cid, code a] := by
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · rw [List.mem_cons, List.mem_singleton]
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · exact Or.inl (by rw [hx1]; exact code_one)
      · exact Or.inr (by rw [eq_of_mem_ne_one_of_card_two hcard hx hx1 ha ha1])
    · rintro (h | h)
      · rw [code_eq_cid_iff.mp h]
        exact one_mem E
      · rw [code_injective h]
        exact ha
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨1, one_mem E, code_one⟩
    · rw [List.mem_singleton] at hc
      exact ⟨a, ha, hc.symm⟩

theorem elem_spec {T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    {Es : List (List (List ℕ))} (hseed : seedCheck TL Es = true)
    (hEsT : ∀ L ∈ Es, L.all TL.contains = true) {E : Subgroup P10} (hET : E ≤ T₀)
    (hEe : IsElemAbelian 2 E) : ∃ L ∈ eList TL Es, Desc E L := by
  obtain ⟨k, hk⟩ := hEe.isPGroup.exists_card_eq
  rcases k with _ | k
  · have hbot : E = ⊥ := Subgroup.eq_bot_of_card_eq E (by simpa using hk)
    subst hbot
    rw [eList]
    refine ⟨[cid], List.mem_cons_self, desc_of_mem hT ?_ ?_⟩
    · rw [List.all_eq_true]
      intro c hc
      rw [List.mem_singleton] at hc
      rw [hc, List.contains_iff_mem, ← code_one]
      exact (hT.mem 1).mp (one_mem T₀)
    · intro x
      rw [mem_bot, List.mem_singleton, code_eq_cid_iff]
  · rcases k with _ | k
    · have hcard : Nat.card E = 2 := by simpa using hk
      obtain ⟨a, ha, -⟩ := (Nat.card_eq_two_iff' (1 : E)).mp hcard
      have ha1 : (a : P10) ≠ 1 := by simpa using ha
      have hcode : code (a : P10) ∈ invs TL := by
        rw [invs, List.mem_filter]
        refine ⟨(hT.mem _).mp (hET a.2), ?_⟩
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
        exact ⟨fun h => ha1 (code_eq_cid_iff.mp h), cinvol_iff.mpr (hEe.mul_self_eq_one a.2)⟩
      refine ⟨[cid, code (a : P10)], ?_, desc_of_card_two hcard a.2 ha1⟩
      rw [eList]
      exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr
        ⟨code (a : P10), hcode, rfl⟩)))
    · have h4 : 4 ≤ Nat.card E := by
        rw [hk]
        exact le_trans (by norm_num : 4 ≤ 2 ^ 2)
          (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))
      obtain ⟨L, hL, hd⟩ := seed_spec hT hseed hET hEe h4
      refine ⟨L, ?_, desc_of_mem hT (hEsT L hL) hd⟩
      rw [eList]
      exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hL))

theorem pairC_spec {L₀ T₀ : Subgroup P10} {TL Lc : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) (hLc : ∀ c ∈ Lc, ∃ x ∈ L₀, code x = c) {ws : List PairC}
    (h : pairCCheck TL Lc ws = true) {x : P10} (hx : x ∈ T₀) (hx1 : x ≠ 1) (hxx : x * x = 1)
    (hxc : ∀ t ∈ T₀, x * t = t * x) : PairProp914 L₀ x := by
  have hxinv : code x ∈ invs TL := by
    rw [invs, List.mem_filter]
    refine ⟨(hT.mem x).mp hx, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨fun h => hx1 (code_eq_cid_iff.mp h), cinvol_iff.mpr hxx⟩
  have hall := (List.all_eq_true.mp h) (code x) hxinv
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  rcases hall with hbad | hwit
  · exfalso
    have htrue : TL.all (ccomm (code x)) = true := by
      rw [List.all_eq_true]
      intro c hc
      obtain ⟨t, ht, rfl⟩ := hT.surj c hc
      exact ccomm_iff.mpr (hxc t ht)
    rw [htrue] at hbad
    exact Bool.noConfusion hbad
  · obtain ⟨w, -, hw⟩ := List.any_eq_true.mp hwit
    simp only [Bool.and_eq_true, and_assoc] at hw
    obtain ⟨-, hwl, hwt, hws₁, hws₂, hwtx, hwtl, hwnc⟩ := hw
    obtain ⟨l, hlL, hlc⟩ := hLc w.l (List.contains_iff_mem.mp hwl)
    obtain ⟨t, -, htc⟩ := hLc w.t (List.contains_iff_mem.mp hwt)
    obtain ⟨σ₁, hσ₁, hσ₁c⟩ := hT.surj w.s₁ (List.contains_iff_mem.mp hws₁)
    obtain ⟨σ₂, hσ₂, hσ₂c⟩ := hT.surj w.s₂ (List.contains_iff_mem.mp hws₂)
    rw [beq_iff_eq, ← htc, ← hσ₁c] at hwtx
    rw [beq_iff_eq, ← hlc, ← htc, ← hσ₂c] at hwtl
    have h₁ : t * x * t⁻¹ = σ₁ := by
      rw [code_mul_eq_iff.mp hwtx]
      group
    have htl : t * l * x = σ₂ * t * l := by
      rw [← code_mul_eq_iff, code_mul, code_mul]
      exact hwtl
    have h₂ : t * (l * x * l⁻¹) * t⁻¹ = σ₂ := by
      calc t * (l * x * l⁻¹) * t⁻¹ = t * l * x * l⁻¹ * t⁻¹ := by group
        _ = σ₂ := by rw [htl]; group
    have hmem : ∀ g ∈ ({x, l * x * l⁻¹} : Set P10), t * g * t⁻¹ ∈ T₀ := by
      intro g hg
      rcases hg with rfl | rfl
      · rw [h₁]
        exact hσ₁
      · rw [h₂]
        exact hσ₂
    refine ⟨l, hlL, IsPGroup.to_le (hT2.comap_of_injective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective) ((Subgroup.closure_le _).mpr fun g hg => ?_), fun hcon => ?_⟩
    · simpa [Subgroup.mem_comap, MulAut.conj_apply] using hmem g hg
    · have hf : ccomm (code σ₁) (code σ₂) = false := by
        rw [hσ₁c, hσ₂c]
        simpa only [Bool.not_eq_true'] using hwnc
      apply Bool.eq_false_iff.mp hf
      rw [ccomm_iff, ← h₁, ← h₂]
      calc t * x * t⁻¹ * (t * (l * x * l⁻¹) * t⁻¹) = t * (x * (l * x * l⁻¹)) * t⁻¹ := by group
        _ = t * (l * x * l⁻¹ * x) * t⁻¹ := by rw [hcon]
        _ = t * (l * x * l⁻¹) * t⁻¹ * (t * x * t⁻¹) := by group

theorem normal_spec {L₀ T₀ Es₀ : Subgroup P10} {TL Lc : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) (hLc : ∀ c ∈ Lc, ∃ x ∈ L₀, code x = c) {ws : List PairC}
    (h : pairCCheck TL Lc ws = true)
    (h4 : ∀ F : Subgroup P10, F ≤ T₀ → T₀ ≤ normalizer (F : Set P10) → IsElemAbelian 2 F →
      4 ≤ Nat.card F → F = Es₀) :
    ∀ F : Subgroup P10, F ≤ T₀ → T₀ ≤ normalizer (F : Set P10) → IsElemAbelian 2 F →
      F = ⊥ ∨ F = Es₀ ∨ (Nat.card F = 2 ∧ ∀ x ∈ F, x ≠ 1 → PairProp914 L₀ x) := by
  intro F hFT hTF hFe
  obtain ⟨k, hk⟩ := hFe.isPGroup.exists_card_eq
  rcases k with _ | k
  · exact Or.inl (Subgroup.eq_bot_of_card_eq F (by simpa using hk))
  · rcases k with _ | k
    · have hcard : Nat.card F = 2 := by simpa using hk
      refine Or.inr (Or.inr ⟨hcard, fun x hx hx1 => ?_⟩)
      have hcomm : ∀ t ∈ T₀, x * t = t * x := by
        intro t ht
        have hmem : t * x * t⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp (hTF ht) x).mp hx
        have hne : t * x * t⁻¹ ≠ 1 := by
          intro h
          apply hx1
          have h' := congrArg (fun u => t⁻¹ * u * t) h
          simpa [mul_assoc] using h'
        have heq : t * x * t⁻¹ = x :=
          eq_of_mem_ne_one_of_card_two hcard hx hx1 hmem hne
        have h' : t * x = x * t := by
          calc t * x = (t * x * t⁻¹) * t := by group
            _ = x * t := by rw [heq]
        exact h'.symm
      exact pairC_spec hT hT2 hLc h (hFT hx) hx1 (hFe.mul_self_eq_one hx) hcomm
    · refine Or.inr (Or.inl (h4 F hFT hTF hFe ?_))
      rw [hk]
      exact le_trans (by norm_num : 4 ≤ 2 ^ 2)
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))

theorem normal4_spec {T₀ : Subgroup P10} {TL TLinv : List (List ℕ)} {Ks : List KData}
    {Es : List Entry} {iStar : ℕ} (hT : Desc T₀ TL) (hinv : invCheck TL TLinv = true)
    (hE : entriesCheck TL TLinv Ks Es = true) (hseed : seedCheck TL (Es.map Entry.E) = true)
    (hnn : (List.range Es.length).all (fun i => i == iStar ||
      nonNormal TL TLinv (Es.getD i ⟨[], 0, [], [], [], []⟩).E) = true)
    {F : Subgroup P10} (hFT : F ≤ T₀) (hTF : T₀ ≤ normalizer (F : Set P10))
    (hFe : IsElemAbelian 2 F) (hF4 : 4 ≤ Nat.card F) :
    ∀ x, x ∈ F ↔ code x ∈ (Es.getD iStar ⟨[], 0, [], [], [], []⟩).E := by
  obtain ⟨A, hA, hAE⟩ := seed_spec hT hseed hFT hFe hF4
  obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hA
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hen
  have hgi : Es.getD i ⟨[], 0, [], [], [], []⟩ = Es[i] := List.getD_eq_getElem _ _ hi
  have hiS : i = iStar := by
    have h1 := (List.all_eq_true.mp hnn) i (List.mem_range.mpr hi)
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exact h1
    · rw [hgi] at h1
      exact absurd hTF (nonNormal_spec hT hinv (entry_E_sub (entry_data hE hen).2) h1 hAE)
  subst hiS
  rw [hgi]
  exact hAE

end CFSG.LocalAnalysis.WeakClosure81.CoordA6

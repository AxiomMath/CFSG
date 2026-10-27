module

public import CFSG.Quasithin.AppendixH.H14.H141F4

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.GH74.KGroups CFSG.ASVolI.ChH

@[expose] def hypCodes : List ℕ := [1, 4, 16, 21, 57, 45]

@[expose] def codes18 : List ℕ := hypCodes.flatMap fun p => [p, smulCode3 2 p, smulCode3 3 p]

@[expose] noncomputable def OmegaH : Set (Submodule GF4 (Fin 3 → GF4)) :=
  {P | ∃ p ∈ hypCodes, P = Submodule.span GF4 {wOfCode3 p}}

lemma hypCodes_lt_all : ∀ p ∈ hypCodes, p < 64 := by decide

lemma hypCodes_ne_zero : ∀ p ∈ hypCodes, p ≠ 0 := by decide

lemma codeOf3_zero : codeOf3 (0 : Fin 3 → GF4) = 0 := by decide

lemma wOfCode3_ne_zero_of_mem_hypCodes {p : ℕ} (hp : p ∈ hypCodes) : wOfCode3 p ≠ 0 := by
  intro h
  have h' : wOfCode3 p = wOfCode3 0 := by rw [h, wOfCode3_zero]
  have hp0 : p = 0 := wOfCode3_injOn (hypCodes_lt_all p hp) (by norm_num) h'
  exact hypCodes_ne_zero p hp hp0

lemma hypCodes_span_inj :
    Set.InjOn (fun p => Submodule.span GF4 ({wOfCode3 p} : Set (Fin 3 → GF4)))
      {p | p ∈ hypCodes} := by
  intro p hp q hq hpq
  have hpq' : Submodule.span GF4 ({wOfCode3 p} : Set (Fin 3 → GF4)) =
      Submodule.span GF4 ({wOfCode3 q} : Set (Fin 3 → GF4)) := hpq
  have hq_mem : wOfCode3 p ∈ Submodule.span GF4 ({wOfCode3 q} : Set (Fin 3 → GF4)) := by
    have hself : wOfCode3 p ∈ Submodule.span GF4 ({wOfCode3 p} : Set (Fin 3 → GF4)) :=
      Submodule.subset_span (Set.mem_singleton (wOfCode3 p))
    rwa [hpq'] at hself
  rw [Submodule.mem_span_singleton] at hq_mem
  obtain ⟨a, ha⟩ := hq_mem
  exact (by decide :
    ∀ p ∈ hypCodes, ∀ q ∈ hypCodes, ∀ a : GF4,
      a • wOfCode3 q = wOfCode3 p → p = q) p hp q hq a ha

lemma span_basis3_eq_top :
    Submodule.span GF4 ({wOfCode3 1, wOfCode3 4, wOfCode3 16} : Set (Fin 3 → GF4)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [eq_smul_basis3 x]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

lemma mem_sup3 {P Q R : Submodule GF4 (Fin 3 → GF4)} {u v w : Fin 3 → GF4}
    (hu : u ∈ P) (hv : v ∈ Q) (hw : w ∈ R) (a b c : GF4) :
    a • u + b • v + c • w ∈ P ⊔ Q ⊔ R := by
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem _ _ hu))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.smul_mem _ _ hv))
  · exact Submodule.mem_sup_right (Submodule.smul_mem _ _ hw)

lemma hypCodes_sup3 : ∀ p ∈ hypCodes, ∀ q ∈ hypCodes, ∀ r ∈ hypCodes,
    p ≠ q → p ≠ r → q ≠ r → ∀ e ∈ [1, 4, 16], ∃ a b c : GF4,
      a • wOfCode3 p + b • wOfCode3 q + c • wOfCode3 r = wOfCode3 e := by
  decide

lemma exists_smul_of_codeOf_mem_codes18 {u : Fin 3 → GF4} (hu : codeOf3 u ∈ codes18) :
    ∃ p ∈ hypCodes, ∃ c : GF4, c ≠ 0 ∧ u = c • wOfCode3 p := by
  rw [codes18, List.mem_flatMap] at hu
  obtain ⟨p, hp, hpu⟩ := hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpu
  have hp64 : p < 64 := hypCodes_lt_all p hp
  rcases hpu with hpu | hpu | hpu
  · refine ⟨p, hp, 1, by decide, ?_⟩
    rw [one_smul, ← wOfCode3_codeOf3 u, hpu]
  · refine ⟨p, hp, GF4.ofNat' 2, by decide, ?_⟩
    rw [← wOfCode3_codeOf3 u, hpu, wOfCode3_smulCode3 (by norm_num) hp64]
  · refine ⟨p, hp, GF4.ofNat' 3, by decide, ?_⟩
    rw [← wOfCode3_codeOf3 u, hpu, wOfCode3_smulCode3 (by norm_num) hp64]

theorem codes18_lt : ∀ v ∈ codes18, v < 64 := by
  intro v hv
  rw [codes18, List.mem_flatMap] at hv
  obtain ⟨p, hp, hpv⟩ := hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpv
  have hp64 : p < 64 := hypCodes_lt_all p hp
  rcases hpv with hpv | hpv | hpv
  · rw [hpv]; exact hp64
  · rw [hpv]; exact smulCode3_lt 2 p (by norm_num) hp64
  · rw [hpv]; exact smulCode3_lt 3 p (by norm_num) hp64

theorem isHyperoval_OmegaH : IsHyperoval GF4 OmegaH := by
  have hfin : ({p | p ∈ hypCodes} : Set ℕ).Finite := by
    rw [show {p | p ∈ hypCodes} = (hypCodes.toFinset : Set ℕ) by ext p; simp]
    exact Finset.finite_toSet _
  have hcard : ({p | p ∈ hypCodes} : Set ℕ).ncard = 6 := by
    rw [show {p | p ∈ hypCodes} = (hypCodes.toFinset : Set ℕ) by ext p; simp]
    rw [Set.ncard_coe_finset]
    decide
  have himg : OmegaH =
      (fun p => Submodule.span GF4 ({wOfCode3 p} : Set (Fin 3 → GF4))) '' {p | p ∈ hypCodes} := by
    ext P
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [himg, (Set.ncard_image_iff hfin).mpr hypCodes_span_inj, hcard]
  · intro P hP
    rw [himg] at hP
    obtain ⟨p, hp, rfl⟩ := hP
    exact finrank_span_singleton (wOfCode3_ne_zero_of_mem_hypCodes hp)
  · intro P hP Q hQ R hR hPQ hPR hQR
    rw [himg] at hP hQ hR
    obtain ⟨p, hp, hP⟩ := hP
    obtain ⟨q, hq, hQ⟩ := hQ
    obtain ⟨r, hr, hR⟩ := hR
    have hpq : p ≠ q := fun h => hPQ (by rw [← hP, ← hQ, h])
    have hpr : p ≠ r := fun h => hPR (by rw [← hP, ← hR, h])
    have hqr : q ≠ r := fun h => hQR (by rw [← hQ, ← hR, h])
    have hu : wOfCode3 p ∈ P := by
      rw [← hP]; exact Submodule.subset_span (Set.mem_singleton _)
    have hv : wOfCode3 q ∈ Q := by
      rw [← hQ]; exact Submodule.subset_span (Set.mem_singleton _)
    have hw : wOfCode3 r ∈ R := by
      rw [← hR]; exact Submodule.subset_span (Set.mem_singleton _)
    have hsup : Submodule.span GF4 ({wOfCode3 1, wOfCode3 4, wOfCode3 16} :
        Set (Fin 3 → GF4)) ≤ P ⊔ Q ⊔ R := by
      rw [Submodule.span_le]
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl
      · obtain ⟨a, b, c, habc⟩ := hypCodes_sup3 p hp q hq r hr hpq hpr hqr 1 (by decide)
        rw [← habc]
        exact mem_sup3 hu hv hw a b c
      · obtain ⟨a, b, c, habc⟩ := hypCodes_sup3 p hp q hq r hr hpq hpr hqr 4 (by decide)
        rw [← habc]
        exact mem_sup3 hu hv hw a b c
      · obtain ⟨a, b, c, habc⟩ := hypCodes_sup3 p hp q hq r hr hpq hpr hqr 16 (by decide)
        rw [← habc]
        exact mem_sup3 hu hv hw a b c
    have htop : P ⊔ Q ⊔ R = ⊤ := by
      rw [eq_top_iff, ← span_basis3_eq_top]
      exact hsup
    rw [htop, finrank_top]
    exact Module.finrank_fin_fun GF4

theorem semilinear_image_span {σ : GF4 ≃+* GF4} {γ : MulAut (Multiplicative (Fin 3 → GF4))}
    (h : SemilinearOf3 σ γ) {w u : Fin 3 → GF4}
    (hu : γ (Multiplicative.ofAdd w) = Multiplicative.ofAdd u) (v : Fin 3 → GF4) :
    (∃ x ∈ Submodule.span GF4 {w}, γ (Multiplicative.ofAdd x) = Multiplicative.ofAdd v) ↔
      v ∈ Submodule.span GF4 {u} := by
  constructor
  · rintro ⟨x, hx, hx'⟩
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    have h1 : γ (Multiplicative.ofAdd x) = Multiplicative.ofAdd (σ c • u) := by
      rw [← hc, h c w, hu, toAdd_ofAdd]
    have hv : v = σ c • u := by
      have := congrArg Multiplicative.toAdd (hx'.symm.trans h1)
      simpa using this
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro hv
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨d, hd⟩ := hv
    refine ⟨σ.symm d • w, Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)),
      ?_⟩
    rw [h (σ.symm d) w, hu, toAdd_ofAdd, σ.apply_symm_apply, hd]

theorem permutesPoints_of_codes {σ : GF4 ≃+* GF4}
    {γ : MulAut (Multiplicative (Fin 3 → GF4))} (h : SemilinearOf3 σ γ)
    (hp : ∀ p ∈ hypCodes, codes18.contains
      (codeOf3 (Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 p))))) = true) :
    PermutesPoints γ OmegaH := by
  intro P hP
  rw [OmegaH] at hP
  obtain ⟨p, hpmem, rfl⟩ := hP
  set u : Fin 3 → GF4 :=
    Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 p))) with hu_def
  have hu : γ (Multiplicative.ofAdd (wOfCode3 p)) = Multiplicative.ofAdd u := by
    rw [hu_def]; exact (ofAdd_toAdd _).symm
  obtain ⟨p', hp', c, hc, hueq⟩ :=
    exists_smul_of_codeOf_mem_codes18 (List.contains_iff_mem.mp (hp p hpmem))
  refine ⟨Submodule.span GF4 ({u} : Set (Fin 3 → GF4)), ?_, ?_⟩
  · refine ⟨p', hp', ?_⟩
    rw [hu_def, hueq]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) (wOfCode3 p')
  · intro v
    exact semilinear_image_span h hu v

theorem codes_of_permutesPoints {σ : GF4 ≃+* GF4}
    {γ : MulAut (Multiplicative (Fin 3 → GF4))} (h : SemilinearOf3 σ γ)
    (hγ : PermutesPoints γ OmegaH) :
    ∀ p ∈ hypCodes, codes18.contains
      (codeOf3 (Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 p))))) = true := by
  intro p hp
  set u : Fin 3 → GF4 :=
    Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 p))) with hu_def
  have hu : γ (Multiplicative.ofAdd (wOfCode3 p)) = Multiplicative.ofAdd u := by
    rw [hu_def]; exact (ofAdd_toAdd _).symm
  have hP : Submodule.span GF4 ({wOfCode3 p} : Set (Fin 3 → GF4)) ∈ OmegaH :=
    ⟨p, hp, rfl⟩
  obtain ⟨Q, hQ, hQiff⟩ := hγ _ hP
  have huQ : u ∈ Q :=
    (hQiff u).mp ⟨wOfCode3 p, Submodule.subset_span (Set.mem_singleton _), hu⟩
  rw [OmegaH] at hQ
  obtain ⟨p', hp', hQeq⟩ := hQ
  rw [hQeq] at huQ
  rw [Submodule.mem_span_singleton] at huQ
  obtain ⟨c, hc⟩ := huQ
  have hu_ne : u ≠ 0 := by
    intro h0
    have h1 : Multiplicative.ofAdd u = 1 := by rw [h0, ofAdd_zero]
    have h2 : γ (Multiplicative.ofAdd (wOfCode3 p)) =
        γ (Multiplicative.ofAdd (0 : Fin 3 → GF4)) := by
      rw [hu, h1, ofAdd_zero, map_one]
    have h3 : Multiplicative.ofAdd (wOfCode3 p) =
        Multiplicative.ofAdd (0 : Fin 3 → GF4) := γ.injective h2
    have h4 : wOfCode3 p = 0 := by simpa using congrArg Multiplicative.toAdd h3
    exact wOfCode3_ne_zero_of_mem_hypCodes hp h4
  have hc_ne : c ≠ 0 := by
    intro hc0
    exact hu_ne (by rw [← hc, hc0, zero_smul])
  have hcode : codeOf3 u = smulCode3 c.toNat p' := by
    rw [← hc, codeOf3_smul, codeOf3_wOfCode3 (hypCodes_lt_all p' hp')]
  have hc_nat : c.toNat ∈ [1, 2, 3] :=
    (by decide : ∀ c : GF4, c ≠ 0 → c.toNat ∈ [1, 2, 3]) c hc_ne
  rw [hcode]
  exact (by decide : ∀ p ∈ hypCodes, ∀ d ∈ [1, 2, 3],
    codes18.contains (smulCode3 d p) = true) p' hp' c.toNat hc_nat

@[expose] def keyGood (s v0 v1 v2 : ℕ) : Bool :=
  hypCodes.all (fun p => codes18.contains (mKey s v0 v1 v2 p)) &&
    (List.range 63).all fun n => mKey s v0 v1 v2 (n + 1) != 0

theorem exists_key3_of_mem_hatS6set {γ : MulAut (Multiplicative (Fin 3 → GF4))}
    (hγ : γ ∈ hatS6set GF4 OmegaH) :
    ∃ s < 2, ∃ v0 ∈ codes18, ∃ v1 ∈ codes18, ∃ v2 ∈ codes18, keyGood s v0 v1 v2 = true ∧
      SemilinearOf3 (sigE s) γ ∧
      ∀ n < 64, codeOf3 (Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 n)))) =
        mKey s v0 v1 v2 n := by
  obtain ⟨hγL, hγP⟩ := hγ
  obtain ⟨s, hs, v0, hv0lt, v1, hv1lt, v2, hv2lt, h0, h1, h2, hσ⟩ :=
    exists_key3_of_mem_gammaLset (γ := γ) hγL
  have mem_of : ∀ {w : Fin 3 → GF4} {n : ℕ},
      γ (Multiplicative.ofAdd w) = Multiplicative.ofAdd (wOfCode3 n) → n < 64 →
      codeOf3 (Multiplicative.toAdd (γ (Multiplicative.ofAdd w))) = n := by
    intro w n hw hn
    rw [hw, toAdd_ofAdd, codeOf3_wOfCode3 hn]
  have hv0 : v0 ∈ codes18 := by
    have hmem := codes_of_permutesPoints hσ hγP 1 (by decide)
    rw [List.contains_iff_mem] at hmem
    rwa [mem_of h0 hv0lt] at hmem
  have hv1 : v1 ∈ codes18 := by
    have hmem := codes_of_permutesPoints hσ hγP 4 (by decide)
    rw [List.contains_iff_mem] at hmem
    rwa [mem_of h1 hv1lt] at hmem
  have hv2 : v2 ∈ codes18 := by
    have hmem := codes_of_permutesPoints hσ hγP 16 (by decide)
    rw [List.contains_iff_mem] at hmem
    rwa [mem_of h2 hv2lt] at hmem
  have hformula : ∀ n < 64,
      codeOf3 (Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 n)))) =
        mKey s v0 v1 v2 n :=
    fun n hn => code_apply_eq_mKey hσ hv0lt hv1lt hv2lt h0 h1 h2 hn
  have hkey : keyGood s v0 v1 v2 = true := by
    unfold keyGood
    rw [Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      intro p hp
      rw [← hformula p (hypCodes_lt_all p hp)]
      exact codes_of_permutesPoints hσ hγP p hp
    · rw [List.all_eq_true]
      intro n hn
      rw [bne_iff_ne]
      have hn64 : n + 1 < 64 := by have := List.mem_range.mp hn; omega
      rw [← hformula (n + 1) hn64]
      intro hzero
      have hx0 : Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 (n + 1)))) = 0 :=
        codeOf3_injective (by rw [hzero, codeOf3_zero])
      have hof : γ (Multiplicative.ofAdd (wOfCode3 (n + 1))) = 1 := by
        have := congrArg Multiplicative.ofAdd hx0
        simpa using this
      have hof' : Multiplicative.ofAdd (wOfCode3 (n + 1)) =
          Multiplicative.ofAdd (0 : Fin 3 → GF4) := by
        apply γ.injective
        rw [hof, ofAdd_zero, map_one]
      have hw : wOfCode3 (n + 1) = wOfCode3 0 := by
        simpa [wOfCode3_zero] using congrArg Multiplicative.toAdd hof'
      have : n + 1 = 0 := wOfCode3_injOn hn64 (by norm_num) hw
      omega
  exact ⟨s, hs, v0, hv0, v1, hv1, v2, hv2, hkey, hσ, hformula⟩

end CFSG.Quasithin.AppendixH.H14

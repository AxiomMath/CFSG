module

public import CFSG.Quasithin.EmptyFaithful.S151cSix
public import CFSG.Quasithin.EmptyFaithful.S151cIrr
public import CFSG.Quasithin.EmptyFaithful.S151cE9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section Shape151c

variable {W : Type*} [CommGroup W] [Finite W]

@[expose] def GenTop (Y H : Subgroup (MulAut W)) : Prop :=
  Subgroup.closure {x | ∃ ψ ∈ Y, ∃ z ∈ fixV H, ψ z = x} = ⊤

omit [Finite W] in
theorem genTop_of_closure_le {Y H : Subgroup (MulAut W)} {Y' : Subgroup (MulAut W)} (hY : Y' ≤ Y)
    (h : Subgroup.closure {x | ∃ ψ ∈ Y', ∃ z ∈ fixV H, ψ z = x} = ⊤) : GenTop Y H := by
  refine eq_top_iff.mpr (le_trans (le_of_eq h.symm) (Subgroup.closure_mono ?_))
  rintro x ⟨ψ, hψ, z, hz, rfl⟩
  exact ⟨ψ, hY hψ, z, hz, rfl⟩

omit [Finite W] in
theorem genTop_invariant {Y H : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ Y) {n : W}
    (hn : n ∈ Subgroup.closure {x | ∃ ψ ∈ Y, ∃ z ∈ fixV H, ψ z = x}) :
    g n ∈ Subgroup.closure {x | ∃ ψ ∈ Y, ∃ z ∈ fixV H, ψ z = x} := by
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, z, hz, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨g * ψ, Y.mul_mem hg hψ, z, hz, rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

omit [Finite W] in
theorem genTop_of_irreducible {Y H : Subgroup (MulAut W)}
    (hirr : ∀ B : Subgroup W, (∀ g ∈ Y, ∀ b ∈ B, g b ∈ B) → B ≠ ⊥ → B = ⊤)
    (hfix : fixV H ≠ ⊥) : GenTop Y H := by
  refine hirr _ (fun g hg b hb => genTop_invariant hg hb) ?_
  intro hbot
  apply hfix
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  have : z ∈ Subgroup.closure {x | ∃ ψ ∈ Y, ∃ z ∈ fixV H, ψ z = x} :=
    Subgroup.subset_closure ⟨1, Y.one_mem, z, hz, rfl⟩
  rw [hbot] at this
  exact this

theorem fittingOf_eq_pCoreOf_of_isPGroup {Y : Subgroup (MulAut W)} {p : ℕ} [Fact p.Prime]
    (hF : IsPGroup p (fittingOf Y)) : fittingOf Y = pCoreOf p Y := by
  apply le_antisymm
  · refine le_pCoreOf_of_le_normalizer p (fittingOf_le Y) ?_ hF
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_fittingOf hg hy, fun hy => ?_⟩
    have := conj_mem_fittingOf (Subgroup.inv_mem _ hg) hy
    simpa [mul_assoc] using this
  · refine le_fittingOf_of_normal_nilpotent (pCoreOf_le p Y) ?_ ?_
    · intro x hx n hn
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf p Y hx) n).mp hn
    · exact (pCoreOf_isPGroup p Y).isNilpotent

theorem rk_eq_of_mem_sylow2Of {Y A : Subgroup (MulAut W)} (hA : A ∈ sylow2Of Y) {a m : ℕ}
    (hm : Odd m) (hcard : Nat.card Y = 2 ^ a * m) : rk A = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (A.subgroupOf Y).card_mul_index
  have h2 : Nat.card (A.subgroupOf Y) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
  rw [h2, hcard] at h1
  have hn0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hidx0 : (A.subgroupOf Y).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hm2 : ¬ 2 ∣ m := fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)
  have hm0 : m ≠ 0 := fun h => hm2 (h ▸ dvd_zero 2)
  have hv := congrArg (padicValNat 2) h1
  rw [padicValNat.mul hn0 hidx0, padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hA.2.2, padicValNat.eq_zero_of_not_dvd hm2] at hv
  unfold rk
  omega

theorem exists_noncyclic_offender (hV : ∀ v : W, v ^ 2 = 1) {Y : Subgroup (MulAut W)} {r : ℚ}
    (hH : D217Hyp Y r) {a m : ℕ} (hm : Odd m) (ha : 1 < a) (hcard : Nat.card Y = 2 ^ a * m) :
    ∃ A ∈ QhatStar Y, 1 < rk A := by
  have hd := d217 W hV Y r hH.qhat hH.le_two hH.jhat hH.comm_fitting hH.indecomposable hH.fstar
    hH.o2 hH.sqtk
  obtain ⟨A, hA⟩ := QhatStar_nonempty hH.qhat hH.le_two
  refine ⟨A, hA, ?_⟩
  have := rk_eq_of_mem_sylow2Of (hd.1 ▸ hA) hm hcard
  omega

theorem fdec_of_pdecomp (hV : ∀ v : W, v ^ 2 = 1) {Y : Subgroup (MulAut W)} {s : ℕ}
    {Pi : Fin s → Subgroup (MulAut W)} (d : PDecomp Y Pi) (hW : fixV (pCoreOf 3 Y) = ⊥)
    (hF : fittingOf Y = pCoreOf 3 Y) : FDec Y Pi where
  mem i := ⟨by rw [hF]; exact d.le_P i, by simpa using d.card_eq i, by simpa using d.rk_eq i⟩
  vindep := d.vindep
  vsup := iSup_commV_eq_top hV d hW
  triv := d.triv

theorem perm_of_range_eq_Pfam {Y : Subgroup (MulAut W)} {s : ℕ} {Pi : Fin s → Subgroup (MulAut W)}
    (hrg : Set.range Pi = Pfam Y) {H : Subgroup (MulAut W)}
    (hHn : ∀ τ ∈ H, ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y) :
    ∀ τ ∈ H, ∀ i, ∃ j, conjBy τ (Pi i) = Pi j := by
  intro τ hτ i
  have hnorm : τ ∈ Subgroup.normalizer (Y : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hHn τ hτ y, fun hy => ?_⟩
    have := hHn τ⁻¹ (H.inv_mem hτ) _ hy
    simpa [mul_assoc] using this
  have hPi : Pi i ∈ Pfam Y := hrg ▸ ⟨i, rfl⟩
  have := Pfam_conj_of_mem_normalizer hnorm hPi
  rw [← hrg] at this
  obtain ⟨j, hj⟩ := this
  exact ⟨j, hj.symm⟩

theorem genTop_of_fdec (hV : ∀ v : W, v ^ 2 = 1) {Y : Subgroup (MulAut W)} {s : ℕ}
    {Pi : Fin s → Subgroup (MulAut W)} (d : FDec Y Pi) (hFY : (⨆ i, Pi i) ≤ Y)
    {H : Subgroup (MulAut W)} (hH2 : IsPGroup 2 H)
    (hperm : ∀ τ ∈ H, ∀ i, ∃ j, conjBy τ (Pi i) = Pi j) : GenTop Y H :=
  genTop_of_closure_le hFY (d.closure_eq_top hV hH2 hperm)

theorem card_eq_of_shape6 {Y : Subgroup (MulAut W)} {r : ℚ} (h6 : Shape6 Y r) :
    Nat.card Y = 2 ^ 2 * 27 := by
  obtain ⟨hE, hF27, ⟨A', hA'X, hA'2, hA'4, hXeq⟩, -, -⟩ := h6
  have hnorm : A' ≤ Subgroup.normalizer (fittingOf Y : Set (MulAut W)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_fittingOf (hA'X ha) hy, fun hy => ?_⟩
    have := conj_mem_fittingOf (Subgroup.inv_mem _ (hA'X ha)) hy
    simpa [mul_assoc] using this
  have hinf : fittingOf Y ⊓ A' = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h3 : x ^ 3 = 1 := hE.2 x hx.1
    have h2 : x ^ 2 = 1 := hA'2.2 x hx.2
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  have hcard := card_sup_of_normalizes hnorm hinf
  rw [← hXeq, hF27, hA'4] at hcard
  rw [hcard]
  norm_num

theorem genTop_of_noncyclic (hV : ∀ v : W, v ^ 2 = 1) {Y : Subgroup (MulAut W)} {r : ℚ}
    (hH : D217Hyp Y r) {A : Subgroup (MulAut W)} (hA : A ∈ QhatStar Y) (hrk : 1 < rk A)
    {H : Subgroup (MulAut W)} (hH2 : IsPGroup 2 H)
    (hHn : ∀ τ ∈ H, ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y) : GenTop Y H := by
  obtain ⟨-, hFp, -, -, -, hW, hcases⟩ := d217_noncyclic_structure hV hH hA hrk
  have key : ∀ {s : ℕ} (Pi : Fin s → Subgroup (MulAut W)), PDecomp Y Pi →
      Set.range Pi = Pfam Y → GenTop Y H := by
    intro s Pi d hrg
    refine genTop_of_fdec hV (fdec_of_pdecomp hV d hW hFp) ?_ hH2
      (perm_of_range_eq_Pfam hrg hHn)
    rw [d.sup_eq]
    exact pCoreOf_le 3 Y
  rcases hcases with ⟨Pi, d, hrg, -⟩ | ⟨Pi, d, hrg, -⟩
  · exact key Pi d hrg
  · exact key Pi d hrg

theorem genTop_of_concl (hV : ∀ v : W, v ^ 2 = 1) {Y : Subgroup (MulAut W)} {r : ℚ}
    (hH : D217Hyp Y r) (hD : D217Concl Y r)
    (hnot : ¬ (Nonempty (↥Y ≃* DihedralGroup 3) ∧ rk W = 4)) {H : Subgroup (MulAut W)}
    (hH2 : IsPGroup 2 H) (hHn : ∀ τ ∈ H, ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y) (hfix : fixV H ≠ ⊥) :
    GenTop Y H := by
  have hfixF := fixV_fittingOf_eq_bot hV hH.o2 hH.comm_fitting
  have hnormH : ∀ τ ∈ H, τ ∈ Subgroup.normalizer (Y : Set (MulAut W)) := by
    intro τ hτ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hHn τ hτ y, fun hy => ?_⟩
    have := hHn τ⁻¹ (H.inv_mem hτ) _ hy
    simpa [mul_assoc] using this
  rcases hD with h1 | h2 | h3 | h4 | h5 | h6
  ·
    obtain ⟨hY, hrk, hr⟩ := h1
    rcases hr with hr1 | hr2
    · have hrk2 : rk W = 2 := by
        have : (rk W : ℚ) = 2 := by rw [hrk, hr1]; norm_num
        exact_mod_cast this
      exact genTop_of_irreducible (fun B hB hne => eq_top_of_invariant_D3 hV hH hY hrk2 hB hne) hfix
    · exfalso
      apply hnot
      refine ⟨hY, ?_⟩
      have : (rk W : ℚ) = 4 := by rw [hrk, hr2]; norm_num
      exact_mod_cast this
  ·
    obtain ⟨hY, hrk, -⟩ := h2
    exact genTop_of_irreducible (fun B hB hne => eq_top_of_invariant_D5 hV hH hY hrk hB hne) hfix
  ·
    obtain ⟨hE, hF9, -, hrk, -⟩ := h3
    obtain ⟨P₁, P₂, hP₁, hP₂, hdisj, hsup, hP12, hP21, hFsup, hchar⟩ :=
      exists_planes_E9 hV hE hF9 hH.comm_fitting hrk
    have hP₁ne : commV P₁ ≠ ⊥ := by
      intro h
      have := hP₁.2.2
      rw [h, rk_bot] at this
      omega
    have hP₂ne : commV P₂ ≠ ⊥ := by
      intro h
      have := hP₂.2.2
      rw [h, rk_bot] at this
      omega
    let Pi : Fin 2 → Subgroup (MulAut W) := ![P₁, P₂]
    have hmem : ∀ i, Pi i ∈ Xk Y 1 := fun i => by fin_cases i <;> simpa [Pi] using ‹_›
    have hfd : FDec Y Pi :=
      { mem := hmem
        vindep := iSupIndep_fin_two_iff.mpr hdisj
        vsup := by rw [iSup_fin_two_eq]; exact hsup
        triv := fun i j hij => by
          fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simpa [Pi] using ‹_› }
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hFpc : fittingOf Y = pCoreOf 3 Y :=
      fittingOf_eq_pCoreOf_of_isPGroup (fun a => ⟨1, Subtype.ext (by
        simpa using hE.2 (a : MulAut W) a.2)⟩)
    have hfixPi : ∀ i, fixV (Pi i) ≠ ⊥ := by
      intro i
      fin_cases i
      · show fixV P₁ ≠ ⊥
        intro h
        apply hP₂ne
        have := hP21
        rw [h, le_bot_iff] at this
        exact this
      · show fixV P₂ ≠ ⊥
        intro h
        apply hP₁ne
        have := hP12
        rw [h, le_bot_iff] at this
        exact this
    have hperm : ∀ τ ∈ H, ∀ i, ∃ j, conjBy τ (Pi i) = Pi j := by
      intro τ hτ i
      have hτn := normalizer_le_normalizer_pCoreOf 3 Y (hnormH τ hτ)
      have hPiF : Pi i ≤ fittingOf Y := (hmem i).1
      have hconj_le : conjBy τ (Pi i) ≤ fittingOf Y := by
        intro x hx
        have h1 : τ⁻¹ * x * τ ∈ Pi i := mem_conjBy_iff.mp hx
        have h2 : τ⁻¹ * x * τ ∈ pCoreOf 3 Y := hFpc ▸ hPiF h1
        have h3 := (Subgroup.mem_normalizer_iff.mp hτn _).mp h2
        have e : τ * (τ⁻¹ * x * τ) * τ⁻¹ = x := by group
        rw [e] at h3
        rw [hFpc]
        exact h3
      have hcard3 : Nat.card (conjBy τ (Pi i)) = 3 := by
        rw [card_conjBy]
        simpa using (hmem i).2.1
      have hfixne : fixV (conjBy τ (Pi i)) ≠ ⊥ := by
        rw [fixV_conjBy]
        intro hbot
        exact hfixPi i ((Subgroup.map_eq_bot_iff_of_injective _ (τ : W ≃* W).injective).mp hbot)
      rcases hchar _ hconj_le hcard3 hfixne with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    exact genTop_of_fdec hV hfd (iSup_le fun i => (hmem i).1.trans (fittingOf_le Y)) hH2 hperm
  ·
    obtain ⟨hF27, hexp, hnc, -, hrk6, -⟩ := h4
    exact genTop_of_irreducible (fun B hB hne => eq_top_of_invariant_shape4 hV hF27 hexp hnc hfixF
      hrk6 (fun g hg b hb => hB g (fittingOf_le Y hg) b hb) hne) hfix
  ·
    obtain ⟨-, -, ⟨e⟩, -⟩ := h5
    have hcard : Nat.card Y = 2 ^ 2 * 9 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod]
      have : Nat.card (DihedralGroup 3) = 6 := by
        rw [Nat.card_eq_fintype_card, DihedralGroup.card]
      rw [this]
      norm_num
    obtain ⟨A, hA, hrkA⟩ := exists_noncyclic_offender hV hH (a := 2) (m := 9) ⟨4, rfl⟩
      (by norm_num) hcard
    exact genTop_of_noncyclic hV hH hA hrkA hH2 hHn
  ·
    have h6' : Shape6 Y r := h6
    obtain ⟨A, hA, hrkA⟩ := exists_noncyclic_offender hV hH (a := 2) (m := 27) ⟨13, rfl⟩
      (by norm_num) (card_eq_of_shape6 h6')
    exact genTop_of_noncyclic hV hH hA hrkA hH2 hHn

end Shape151c

section Transfer151c

variable {V : Type*} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

theorem not_genTop_of_not_le_closure (h : Setting151c X Tb Xc) {L : Subgroup (MulAut V)}
    {U : Subgroup V} (hU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U)
    (hnot : ¬ U ≤ Subgroup.closure {x | ∃ g ∈ L, ∃ z ∈ fixV Tb ⊓ U, g z = x}) :
    ¬ GenTop (autSub L U) (autSub Tb U) := by
  intro hgen
  apply hnot
  have hXs : X ≤ stabSub U := le_stabSub_of_invariant hU
  have hTs : Tb ≤ stabSub U := h.syl.1.trans hXs
  intro u hu
  have h1 : u ∈ (Subgroup.closure {x : ↥U | ∃ ψ ∈ autSub L U, ∃ z ∈ fixV (autSub Tb U),
      ψ z = x}).map U.subtype := ⟨⟨u, hu⟩, by rw [show Subgroup.closure _ = ⊤ from hgen]; trivial, rfl⟩
  rw [MonoidHom.map_closure] at h1
  refine (Subgroup.closure_mono ?_) h1
  rintro _ ⟨x, ⟨ψ, hψ, z, hz, rfl⟩, rfl⟩
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hψ
  refine ⟨g, hg, (z : V), ⟨?_, z.2⟩, rfl⟩
  exact fun t ht => (mem_fixV_autSub.mp hz) t ht (hTs ht)

open Classical in
theorem block_S3rk4_of_not_genTop (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I)
    (hLn : NormalIn X L)
    (hnot : ¬ commV L ≤ Subgroup.closure {x | ∃ g ∈ L, ∃ z ∈ fixV Tb ⊓ commV L, g z = x}) :
    Nonempty (↥(autSub L (commV L)) ≃* DihedralGroup 3) ∧ rk (commV L) = 4 := by
  by_contra hcon
  have hLX : L ≤ X := (block_le_J hI hL).trans (Jhat_le X)
  have hUinv : ∀ x ∈ X, ∀ u ∈ commV L, x u ∈ commV L := fun x hx u hu => hLn.commV_invariant hx hu
  have hXs : X ≤ stabSub (commV L) := le_stabSub_of_invariant hUinv
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have hH := block_d217hyp h hr hr2 hI hL
  have hD := (block_d217 h hr hr2 hI hL).2
  have hH2 : IsPGroup 2 (autSub Tb (commV L)) := isPGroup_autSub h.syl.2.1
  have hHn : ∀ τ ∈ autSub Tb (commV L), ∀ y ∈ autSub L (commV L),
      τ * y * τ⁻¹ ∈ autSub L (commV L) := by
    intro τ hτ y hy
    obtain ⟨t, htT, rfl⟩ := mem_autSub.mp hτ
    exact conj_resHom_mem_autSub hXs hLX hLn (h.syl.1 htT) hy
  have hUne : commV L ≠ ⊥ := fun e => hI.ne_bot L hL (eq_bot_of_commV_eq_bot e)
  have hrkpos : 0 < rk ↥(commV L) := by
    rcases Nat.eq_zero_or_pos (rk ↥(commV L)) with h0 | h0
    · exfalso
      apply hUne
      refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
      have := (rk_eq_zero_iff_of_isPGroup (G := V) (H := commV L)
        ((isPGroup_two_of_sq_eq_one h.sq).to_subgroup _)).mp h0
      rw [this] at hu
      exact hu
    · exact h0
  have hfix : fixV (autSub Tb (commV L)) ≠ ⊥ := by
    have := rk_fixV_pos_of_isPGroup_two hUsq hH2 hrkpos
    intro hbot
    rw [hbot, rk_bot] at this
    exact lt_irrefl _ this
  have hgen := genTop_of_concl hUsq hH hD hcon hH2 hHn hfix
  exact not_genTop_of_not_le_closure h hUinv hnot hgen

end Transfer151c

end CFSG.Quasithin

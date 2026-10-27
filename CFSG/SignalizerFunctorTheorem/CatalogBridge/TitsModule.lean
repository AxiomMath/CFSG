module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.TitsModuleData
import all CFSG.LieType.Simplicity.TitsBits

public noncomputable section

open CFSG.LieType.Simplicity.TitsBits CFSG.SectionRank.TitsOrder CFSG.SectionRank.Native.Tits
open CFSG.LieType.Ree CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

section Linear

variable {K : Type} [Field K] [CharP K ReeTag.F4.prime]

theorem bitK_xorB (n : ℕ) (f : ℕ → Bool) :
    bitK K (xorB n f) = ∑ e ∈ Finset.range n, bitK K (f e) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  induction n with
  | zero => simp [xorB, bitK_false]
  | succ n ih => rw [xorB, bitK_xor, ih, Finset.sum_range_succ]

omit [CharP K ReeTag.F4.prime] in
theorem posCoord_toEnd
    (L : List ℕ) {r : ℕ} (hr : r < 52) (w : RootModule ReeTag.F4.tag K) :
    posCoord ReeTag.F4.tag K r (toEnd K (pack L) w) =
      ∑ c ∈ Finset.range 52,
        posCoord ReeTag.F4.tag K c w * bitK K ((L.getD c 0).testBit r) := by
  rw [toEnd_apply, map_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcol : colVec K (pack L) c = bitVec K (L.getD c 0) :=
    (toEnd_posVec (pack L) (Finset.mem_range.1 hc)).symm.trans
      (toEnd_pack_posVec K L (Finset.mem_range.1 hc))
  rw [map_smul, smul_eq_mul, hcol, posCoord_bitVec hr]

omit [CharP K ReeTag.F4.prime] in
theorem bitK_decide_mul_sum {r : ℕ} (hr : r < 52) (f : ℕ → K) :
    ∑ c ∈ Finset.range 52, bitK K (decide (c = r)) * f c = f r := by
  have : ∀ c, bitK K (decide (c = r)) * f c = if c = r then f c else 0 := fun c => by
    by_cases h : c = r
    · simp [h, bitK_true]
    · simp [h, bitK_false]
  simp only [this]
  rw [Finset.sum_ite_eq' (Finset.range 52) r f, ite_eq_left (Finset.mem_range.2 hr)]

theorem eqn_of_fixed
    (L : List ℕ) {r : ℕ} (hr : r < 52) {w : RootModule ReeTag.F4.tag K}
    (hw : toEnd K (pack L) w = w) :
    ∑ c ∈ Finset.range 52, bitK K (coefB L r c) * posCoord ReeTag.F4.tag K c w = 0 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have h1 := posCoord_toEnd (K := K) L hr w
  rw [hw] at h1
  have h2 : ∑ c ∈ Finset.range 52, bitK K (coefB L r c) * posCoord ReeTag.F4.tag K c w =
      ∑ c ∈ Finset.range 52, posCoord ReeTag.F4.tag K c w * bitK K ((L.getD c 0).testBit r) +
        ∑ c ∈ Finset.range 52, bitK K (decide (c = r)) * posCoord ReeTag.F4.tag K c w := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coefB, bitK_xor]
    ring
  rw [h2, ← h1, bitK_decide_mul_sum hr, CharTwo.add_self_eq_zero]

omit [CharP K ReeTag.F4.prime] in
theorem testBit_rowBits (L : List ℕ) (r c : ℕ) :
    ∀ n, (rowBits L r n).testBit c = (decide (c < n) && coefB L r c)
  | 0 => by simp [rowBits]
  | n + 1 => by
    rw [rowBits, Nat.testBit_or, testBit_rowBits L r c n]
    by_cases hcn : c < n
    · have hne : n ≠ c := by omega
      by_cases hb : coefB L r n = true
      · simp [hcn, hb, hne, show c < n + 1 by omega]
      · simp [hcn, hb, show c < n + 1 by omega]
    · by_cases hcn' : c = n
      · subst hcn'
        by_cases hb : coefB L r c = true
        · simp [hb]
        · simp [hb]
      · have hne : n ≠ c := fun h => hcn' h.symm
        have hlt : ¬ c < n + 1 := by omega
        by_cases hb : coefB L r n = true
        · simp [hcn, hb, hne, hlt]
        · simp [hcn, hb, hlt]

omit [CharP K ReeTag.F4.prime] in
theorem testBit_xorSel (f : ℕ → ℕ) (m c : ℕ) :
    ∀ k, (xorSel f m k).testBit c = xorB k (fun e => m.testBit e && (f e).testBit c)
  | 0 => by simp [xorSel, xorB]
  | k + 1 => by
    rw [xorSel, xorB, ← testBit_xorSel f m c k]
    by_cases h : m.testBit k = true
    · simp [h, Nat.testBit_xor]
    · simp [h]

omit [CharP K ReeTag.F4.prime] in
theorem xorB_congr {n : ℕ} {f g : ℕ → Bool} (h : ∀ e < n, f e = g e) :
    xorB n f = xorB n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [xorB, xorB, ih (fun e he => h e (by omega)), h n (by omega)]

omit [CharP K ReeTag.F4.prime] in
theorem fix_cert_bool : ∀ q < 52, q ≠ 47 → q ≠ 48 → ∀ c < 52,
    xorB 104 (fun e => (fixCert.getD q 0).testBit e &&
      coefB (stabCols.getD (e / 52) []) (e % 52) c) = decide (c = q) := by
  intro q hq h47 h48 c hc
  have h := congrArg (fun x => x.testBit c) (fix_cert q hq h47 h48)
  simp only [testBit_xorSel, Nat.testBit_two_pow] at h
  have h2 : xorB 104 (fun e => (fixCert.getD q 0).testBit e &&
      coefB (stabCols.getD (e / 52) []) (e % 52) c) =
      xorB 104 (fun e => (fixCert.getD q 0).testBit e && (eqRows.getD e 0).testBit c) := by
    refine xorB_congr fun e he => ?_
    have hrow : eqRows.getD e 0 = eqRow e := by
      rw [eqRows_eq]
      simp [List.getD_eq_getElem?_getD, he]
    rw [hrow, eqRow, testBit_rowBits]
    simp [hc]
  rw [h2, h]
  simp [eq_comm]

theorem coord_eq_zero_of_fixed
    {w : RootModule ReeTag.F4.tag K}
    (hw : ∀ j < 2, toEnd K (pack (stabCols.getD j [])) w = w) {q : ℕ} (hq : q < 52)
    (h47 : q ≠ 47) (h48 : q ≠ 48) : posCoord ReeTag.F4.tag K q w = 0 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  set f : ℕ → K := fun c => posCoord ReeTag.F4.tag K c w with hf
  have heq : ∀ e < 104, ∑ c ∈ Finset.range 52,
      bitK K (coefB (stabCols.getD (e / 52) []) (e % 52) c) * f c = 0 := fun e he =>
    eqn_of_fixed (stabCols.getD (e / 52) []) (by omega : e % 52 < 52) (hw (e / 52) (by omega))
  have key : ∑ e ∈ Finset.range 104, bitK K ((fixCert.getD q 0).testBit e) *
      ∑ c ∈ Finset.range 52, bitK K (coefB (stabCols.getD (e / 52) []) (e % 52) c) * f c = 0 :=
    Finset.sum_eq_zero fun e he => by rw [heq e (Finset.mem_range.1 he), mul_zero]
  have expand : ∑ e ∈ Finset.range 104, bitK K ((fixCert.getD q 0).testBit e) *
      ∑ c ∈ Finset.range 52, bitK K (coefB (stabCols.getD (e / 52) []) (e % 52) c) * f c =
      ∑ c ∈ Finset.range 52, bitK K (xorB 104 fun e => (fixCert.getD q 0).testBit e &&
        coefB (stabCols.getD (e / 52) []) (e % 52) c) * f c := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [bitK_xorB, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [bitK_and]
    ring
  rw [expand] at key
  have hcert := fix_cert_bool q hq h47 h48
  rw [Finset.sum_congr rfl fun c hc => by rw [hcert c (Finset.mem_range.1 hc)],
    bitK_decide_mul_sum hq] at key
  exact key


theorem toEnd_pack_bitVec'
    (L : List ℕ) (m : ℕ) : toEnd K (pack L) (bitVec K m) = bitVec K (mv L m) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact toEnd_pack_bitVec L m

theorem bitVec_xorSel' (f : ℕ → ℕ) (m k : ℕ) :
    bitVec K (xorSel f m k) = ∑ i ∈ Finset.range k, bitK K (m.testBit i) • bitVec K (f i) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact bitVec_xorSel f m k

omit [CharP K ReeTag.F4.prime] in
theorem vec_ext
    {v v' : RootModule ReeTag.F4.tag K}
    (h : ∀ p < 52, posCoord ReeTag.F4.tag K p v = posCoord ReeTag.F4.tag K p v') : v = v' := by
  refine Finsupp.ext fun b => ?_
  obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
  have h' := h p hp
  unfold posCoord at h'
  rw [dite_eq_left hp] at h'
  simpa using h'

end Linear


section Labels

theorem short_h_pos : ∀ p : Fin ReeTag.F4.tag.rank, p ∉ ReeTag.F4.longSet ↔ p.1 ∈ modShortPos := by
  decide

theorem short_root_pos : ∀ p < 52, 4 ≤ p →
    (ReeTag.F4.lengthParam (ReeTag.F4.tag.rootCertificate.root (p - 4)) = 1 ↔
      p ∈ modShortPos) := by decide +kernel

theorem posLabel_short_iff {p : ℕ}
    (hp : p < 52) :
    posLabel (τ := ReeTag.F4.tag) p hp ∈ ReeTag.F4.shortLabels ↔ p ∈ modShortPos := by
  by_cases h : p < ReeTag.F4.tag.rank
  · unfold posLabel
    rw [dite_eq_left h]
    exact short_h_pos ⟨p, h⟩
  · unfold posLabel
    rw [dite_eq_right h]
    exact short_root_pos p hp (not_lt.1 h)

end Labels

section Main

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

variable (K) in
@[expose] def cElt
    (pr : List ℤ × List ℤ) : adjointGroup ReeTag.F4.tag K :=
  ⁅(gWordG K pr.1 : adjointGroup ReeTag.F4.tag K), (gWordG K pr.2 : adjointGroup ReeTag.F4.tag K)⁆

theorem pairs_good : ∀ pr ∈ modStab ++ modSpan,
    (∀ l ∈ pr.1, GoodLetter l) ∧ (∀ l ∈ pr.2, GoodLetter l) := by decide

theorem hasBits_cElt
    {pr : List ℤ × List ℤ} (hpr : pr ∈ modStab ++ modSpan) :
    HasBits K (cElt K pr) (pairBits pr) := by
  obtain ⟨h1, h2⟩ := pairs_good pr hpr
  obtain ⟨hx, hx'⟩ := hasBits_gWordG (K := K) pr.1 h1
  obtain ⟨hy, hy'⟩ := hasBits_gWordG (K := K) pr.2 h2
  rw [cElt, commutatorElement_def]
  exact hasBits_commutator hx hx' hy hy'

theorem toEnd_cElt
    {pr : List ℤ × List ℤ} (hpr : pr ∈ modStab ++ modSpan) :
    (((cElt K pr : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) :
      Module.End K (RootModule ReeTag.F4.tag K)) = toEnd K (pack (colsOf (pairBits pr))) := by
  have h : (((cElt K pr : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) :
      Module.End K (RootModule ReeTag.F4.tag K)) = toEnd K (pairBits pr) := hasBits_cElt hpr
  exact h.trans ((toEnd_eq_toEnd_iff _ _).2 (pack_colsOf pr hpr))


theorem getD_mem_stab {j : ℕ} (hj : j < 2) : modStab.getD j ([], []) ∈ modStab ++ modSpan := by
  have : j < modStab.length := by simpa [modStab] using hj
  rw [List.getD_eq_getElem _ _ this]
  exact List.mem_append_left _ (List.getElem_mem this)

theorem getD_mem_span {k : ℕ} (hk : k < 26) : modSpan.getD k ([], []) ∈ modStab ++ modSpan := by
  have : k < modSpan.length := by simpa [modSpan] using hk
  rw [List.getD_eq_getElem _ _ this]
  exact List.mem_append_right _ (List.getElem_mem this)

theorem modShortPos_lt : ∀ q ∈ modShortPos, q < 52 := by decide

theorem scalar_of_commutes
    (e : adjointGroup ReeTag.F4.tag K)
    (hc : ∀ pr ∈ modStab ++ modSpan, cElt K pr * e = e * cElt K pr) :
    ∃ c : K, ∀ v ∈ ReeTag.F4.shortModule K,
      ((e : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) v = c • v := by
  classical
  have hp2 : ((ReeTag.F4.prime : ℕ) : K) = 0 := CharP.cast_eq_zero K ReeTag.F4.prime
  obtain ⟨eE, heE⟩ : ∃ f : Module.End K (RootModule ReeTag.F4.tag K),
      f = ((e : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) := ⟨_, rfl⟩
  rw [← heE]
  have hcE : ∀ pr ∈ modStab ++ modSpan, ∀ v : RootModule ReeTag.F4.tag K,
      toEnd K (pack (colsOf (pairBits pr))) (eE v) =
        eE (toEnd K (pack (colsOf (pairBits pr))) v) := by
    intro pr hpr v
    rw [← toEnd_cElt hpr, heE]
    have h := congrArg (fun g : adjointGroup ReeTag.F4.tag K =>
      ((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) v) (hc pr hpr)
    simpa using h
  have hu : bitVec K (2 ^ 48) = posVec ReeTag.F4.tag K 48 := bitVec_two_pow (by norm_num)
  have hu_short : bitVec K (2 ^ 48) ∈ ReeTag.F4.shortModule K := by
    rw [hu, ReeTag.shortModule_eq_supported ReeTag.F4 K,
      posVec_eq_single (by rw [dim_F4]; norm_num)]
    exact Finsupp.single_mem_supported K 1
      ((posLabel_short_iff (by norm_num)).2 (by decide))
  have hw_short : eE (bitVec K (2 ^ 48)) ∈ ReeTag.F4.shortModule K := by
    rw [heE]
    exact ReeTag.mem_shortModule_of_mem hp2 e.2 hu_short
  have hfix : ∀ j < 2, toEnd K (pack (stabCols.getD j [])) (eE (bitVec K (2 ^ 48))) =
      eE (bitVec K (2 ^ 48)) := by
    intro j hj
    calc toEnd K (pack (stabCols.getD j [])) (eE (bitVec K (2 ^ 48)))
        = eE (toEnd K (pack (stabCols.getD j [])) (bitVec K (2 ^ 48))) := by
          rw [stab_cols j hj]
          exact hcE _ (getD_mem_stab hj) _
      _ = eE (bitVec K (2 ^ 48)) := by rw [toEnd_pack_bitVec', stab_fix j hj]
  have h47 : posCoord ReeTag.F4.tag K 47 (eE (bitVec K (2 ^ 48))) = 0 := by
    have hmem := (ReeTag.shortModule_eq_supported ReeTag.F4 K) ▸ hw_short
    have hnot : posLabel (τ := ReeTag.F4.tag) 47 (by rw [dim_F4]; norm_num) ∉
        ReeTag.F4.shortLabels := fun h => by
      have := (posLabel_short_iff (by norm_num)).1 h
      revert this
      decide
    have h0 := (Finsupp.mem_supported' K _).1 hmem _ hnot
    unfold posCoord
    rw [dite_eq_left (by rw [dim_F4]; norm_num)]
    simpa using h0
  have hscal_u : eE (bitVec K (2 ^ 48)) =
      posCoord ReeTag.F4.tag K 48 (eE (bitVec K (2 ^ 48))) • bitVec K (2 ^ 48) := by
    refine vec_ext fun p hp => ?_
    rw [map_smul, smul_eq_mul, posCoord_bitVec hp]
    by_cases h48 : p = 48
    · subst h48
      rw [Nat.testBit_two_pow_self, bitK_true, mul_one]
    · have hbit : (2 ^ 48 : ℕ).testBit p = false := by
        rw [Nat.testBit_two_pow]
        simp [Ne.symm h48]
      rw [hbit, bitK_false, mul_zero]
      by_cases h47' : p = 47
      · subst h47'
        exact h47
      · exact coord_eq_zero_of_fixed hfix hp h47' h48
  generalize posCoord ReeTag.F4.tag K 48 (eE (bitVec K (2 ^ 48))) = lam at hscal_u
  have hspan_vec : ∀ k < 26, eE (bitVec K (spanVec.getD k 0)) =
      lam • bitVec K (spanVec.getD k 0) := by
    intro k hk
    rw [span_vec k hk, ← toEnd_pack_bitVec', ← hcE _ (getD_mem_span hk), hscal_u, map_smul]
  have hposVec : ∀ q ∈ modShortPos,
      eE (posVec ReeTag.F4.tag K q) = lam • posVec ReeTag.F4.tag K q := by
    intro q hq
    have hq52 := modShortPos_lt q hq
    rw [← bitVec_two_pow hq52, ← span_cert q hq52 hq, bitVec_xorSel', map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [map_smul, hspan_vec k (Finset.mem_range.1 hk), smul_comm]
  refine ⟨lam, fun v hv => ?_⟩
  rw [ReeTag.shortModule_eq_supported ReeTag.F4 K, Finsupp.supported_eq_span_single] at hv
  refine Submodule.span_induction (p := fun v _ => eE v = lam • v) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
    have hp52 : p < 52 := hp
    have hpm : p ∈ modShortPos := (posLabel_short_iff hp52).1 hb
    show eE (Finsupp.single (posLabel p hp) 1) = lam • Finsupp.single (posLabel p hp) 1
    rw [← posVec_eq_single hp]
    exact hposVec p hpm
  · simp
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, smul_add]
  · intro a x _ hx
    rw [map_smul, hx, smul_comm]

end Main

end CFSG.SignalizerFunctorTheorem.CatalogBridge

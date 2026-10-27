module

public import CFSG.RankThree.PartTwo.Toolkit.Statements
public import CFSG.RankThree.PartTwo.Toolkit.RawGL
public import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.RankThree.Asc83Table.Reduction
public meta import CFSG.RankThree.PartTwo.Toolkit.Raw
public meta import CFSG.RankThree.PartTwo.Toolkit.RawGL
public import CFSG.RankThree.PartTwo.Toolkit.Bloom13Inputs
public import Certificates.Certificate8171

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Raw Subgroup
open scoped Matrix

local notation "GL33" => GL (Fin 3) (ZMod 3)

noncomputable def cGL : GL33 := glOf cR (by decide)

theorem ofMat_cGL : ofMat (cGL : Matrix (Fin 3) (Fin 3) (ZMod 3)) = cR := ofMat_glOf _ _

theorem cover13Codes_eq : cover13Codes = cover13.map code := by
  have key : ∀ (F : List R9) (N : List (R9 × R9)) (Rs : List R9),
      (F.map code).filter (fun c => c != 6643) ++ N.flatMap (fun p => Rs.flatMap fun r =>
        (List.range 12).map fun k => nmul (nmul (code p.1) (npow (code r) (k + 1))) (code p.2)) =
      (F.filter (fun r => r != rone) ++ N.flatMap fun p => Rs.flatMap fun r =>
        (List.range 12).map fun k => rmul (rmul p.1 (rpowR r (k + 1))) p.2).map code := by
    intro F N Rs
    have hf : (F.map code).filter (fun c => c != 6643) = (F.filter fun r => r != rone).map code
        := by
      rw [List.filter_map]
      refine congrArg _ (List.filter_congr fun r _ => ?_)
      rw [Function.comp_apply, ← code_rone, Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq,
        ne_eq, code_injective.eq_iff]
    rw [List.map_append, hf]
    refine congrArg _ ?_
    simp only [List.map_flatMap, List.map_map, Function.comp_def, nmul_code, npow_code]
  unfold cover13Codes cover13 f0Codes
  exact key _ _ _

theorem bloom13_check : bloom13Check = true :=
  Certificates.certificate8171

theorem bloom13_parts :
    (rpowR cR 13 = rone ∧ cR ≠ rone) ∧
    (∀ p ∈ nf0Pairs, rmul p.1 p.2 = rone ∧ rmul (rmul p.1 cR) p.2 ∈ f0R ∧ rdet p.1 ≠ 0) ∧
    (nf0Pairs.map Prod.fst).Nodup ∧
    (∀ r ∈ allR9, rdet r ≠ 0 → (∃ k < 13, rmul r cR = rmul (rpowR cR k) r) →
      r ∈ nf0Pairs.map Prod.fst) ∧
    (∀ x : R9, rpowR x 13 = rone → x ≠ rone → code x ∈ cover13.map code) ∧
    (∀ r ∈ reps13, rdet r ≠ 0 ∧ rpowR r 13 = rone ∧
      ∃ C P L : ℕ, slCoverP [code cR, code r] C P L 5616 = true) := by
  have h := bloom13_check
  simp only [bloom13Check, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    List.contains_iff_mem, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hAt : ∀ x : R9, bloom13At (code cR) f0Codes nfMask coverMask (code x) = true :=
    fun x => h5 _ (code_lt x)
  simp only [bloom13At, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    ndet_code, npow_code, ← code_rone] at hAt
  refine ⟨⟨h1, h2⟩, fun p hp => ⟨(h3 p hp).1.1, (h3 p hp).1.2, (h3 p hp).2⟩, h4, ?_, ?_, ?_⟩
  · intro r _ hdet hk
    rcases (hAt r).1 with (h | h) | h
    · exact absurd ((ZMod.val_eq_zero _).1 h) hdet
    · obtain ⟨k, hk1, hk2⟩ := hk
      have : (f0Codes.any fun p => nmul (code r) (code cR) == nmul p (code r)) = true := by
        refine List.any_eq_true.2 ⟨code (rpowR cR k), ?_, ?_⟩
        · exact List.mem_map_of_mem (List.mem_map_of_mem (List.mem_range.2 hk1))
        · rw [nmul_code, nmul_code, hk2, beq_self_eq_true]
      rw [this] at h
      exact absurd h Bool.noConfusion
    · obtain ⟨p, hp, hpr⟩ := List.mem_map.1 (testBit_codeMask.1 h)
      rw [← code_injective hpr]
      exact List.mem_map_of_mem hp
  · intro x hx hx1
    rcases (hAt x).2 with h | h
    · simp only [hx, beq_self_eq_true, Bool.true_and, bne_eq_false_iff_eq] at h
      exact absurd (code_injective h) hx1
    · rw [← cover13Codes_eq]
      exact testBit_codeMask.1 h
  · intro r hr
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    have ht := h8 k (by rw [h7] at hk; exact hk)
    rw [bloom13Tree, List.getD_eq_getElem _ _ hk] at ht
    exact ⟨(h6 _ hr).1, (h6 _ hr).2, _, _, _, ht⟩

noncomputable abbrev F0 : Subgroup GL33 := zpowers cGL

theorem cGL_pow_13 : cGL ^ 13 = 1 := by
  rw [gl_eq_iff, ofMat_glPow, ofMat_cGL, ofMat_glOne]
  exact bloom13_parts.1.1

theorem cGL_ne_one : cGL ≠ 1 := by
  rw [Ne, gl_eq_iff, ofMat_cGL, ofMat_glOne]
  exact bloom13_parts.1.2

theorem orderOf_cGL : orderOf cGL = 13 :=
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  orderOf_eq_prime cGL_pow_13 cGL_ne_one

theorem card_F0 :
    Nat.card F0 = 13 := by rw [Nat.card_zpowers, orderOf_cGL]

theorem mem_F0_iff
    (g : GL33) : g ∈ F0 ↔ ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ f0R := by
  have hfin : IsOfFinOrder cGL := orderOf_pos_iff.1 (by rw [orderOf_cGL]; norm_num)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, orderOf_cGL, f0R, List.mem_map]
  simp only [Finset.mem_image, Finset.mem_range, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [ofMat_glPow, ofMat_cGL]⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, by rw [gl_eq_iff, ofMat_glPow, ofMat_cGL, h]⟩

theorem mem_NF0_iff (g : GL33) : g ∈ normalizer (F0 : Set GL33) ↔
    ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ nf0Pairs.map Prod.fst := by
  constructor
  · intro hg
    have hmem := (mem_normalizer_iff.1 hg cGL).1 (mem_zpowers cGL)
    rw [mem_F0_iff] at hmem
    simp only [f0R, List.mem_map, List.mem_range] at hmem
    obtain ⟨k, hk, hk'⟩ := hmem
    refine bloom13_parts.2.2.2.1 _ (mem_allR9 _) ?_ ⟨k, hk, ?_⟩
    · rw [rdet_ofMat]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit |>.ne_zero
    · have : g * cGL * g⁻¹ = cGL ^ k := by rw [gl_eq_iff, ofMat_glPow, ofMat_cGL, hk']
      have h2 : g * cGL = cGL ^ k * g := by rw [← this]; group
      have h3 := congrArg (fun h : GL33 => ofMat (h : Matrix (Fin 3) (Fin 3) (ZMod 3))) h2
      simp only [ofMat_glMul, ofMat_glPow, ofMat_cGL] at h3
      exact h3
  · intro hg
    obtain ⟨p, hp, hpg⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2, -⟩ := bloom13_parts.2.1 p hp
    rw [hpg] at h1 h2
    have hconj : g * cGL * g⁻¹ ∈ F0 := by
      rw [mem_F0_iff, ofMat_glMul, ofMat_glMul, ofMat_cGL, ofMat_inv_of_rmul h1]
      exact h2
    rw [F0, zpowers_eq_closure]
    refine CFSG.RankThree.Asc83Table.mem_normalizer_closure_of_conj_mem ?_
    rintro s rfl
    rw [← zpowers_eq_closure]
    exact hconj

theorem card_NF0 : Nat.card (normalizer (F0 : Set GL33)) = 78 := by
  classical
  have hnd := bloom13_parts.2.2.1
  let φ : normalizer (F0 : Set GL33) → {r // r ∈ nf0Pairs.map Prod.fst} :=
    fun g => ⟨ofMat (g.1 : Matrix (Fin 3) (Fin 3) (ZMod 3)), (mem_NF0_iff g.1).1 g.2⟩
  have hinj : Function.Injective φ := fun g h e =>
    Subtype.ext (gl_eq_iff.2 (congrArg Subtype.val e))
  have hsurj : Function.Surjective φ := by
    rintro ⟨r, hr⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    have hdet := (bloom13_parts.2.1 p hp).2.2
    exact ⟨⟨glOf p.1 hdet, (mem_NF0_iff _).2 (by rw [ofMat_glOf]; exact hr)⟩,
      Subtype.ext (ofMat_glOf p.1 hdet)⟩
  rw [Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩),
    ← Nat.card_congr (List.Nodup.getEquiv _ hnd), Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem card_GL33 : Nat.card GL33 = 11232 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_three, ZMod.card]

theorem factorization_GL33 : (Nat.card GL33).factorization 13 = 1 := by
  rw [card_GL33]
  exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq (by norm_num)
    (show 11232 = 13 ^ 1 * 864 by norm_num) (by norm_num)

theorem mem_zpowers_pow_of_lt {w : GL33} (hw : w ^ 13 = 1) {k : ℕ} (hk : k < 12) :
    w ∈ zpowers (w ^ (k + 1)) := by
  rw [mem_zpowers_pow_iff]
  have hdvd : orderOf w ∣ 13 := orderOf_dvd_of_pow_eq_one hw
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).1 hdvd with h | h
  · rw [h, Nat.gcd_one_right]
  · rw [h]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 13)).2
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))

theorem statedSL_le_closure_rep
    {r : R9} (hr : r ∈ reps13) (xr : GL33)
    (hxr : ofMat (xr : Matrix (Fin 3) (Fin 3) (ZMod 3)) = r) :
    CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ Subgroup.closure {y | y ∈ [cGL, xr]} := by
  obtain ⟨C, P, L, h⟩ := (bloom13_parts.2.2.2.2.2 r hr).2.2
  apply statedSL_le_closureP _ C P L 5616
  simp only [List.map_cons, List.map_nil, ofMat_cGL, hxr]
  exact h

theorem exists_conj_rep
    {x : GL33} (hx13 : x ^ 13 = 1) (hx1 : x ≠ 1) (hxF0 : x ∉ F0) :
    ∃ c ∈ normalizer (F0 : Set GL33), ∃ r ∈ reps13, ∃ xr : GL33,
      ofMat (xr : Matrix (Fin 3) (Fin 3) (ZMod 3)) = r ∧ ∃ k < 12, x = c * xr ^ (k + 1) * c⁻¹ := by
  have hcode : code (ofMat (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) ∈ cover13.map code := by
    refine bloom13_parts.2.2.2.2.1 _ ?_ ?_
    · rw [← ofMat_glPow, hx13, ofMat_glOne]
    · exact fun h => hx1 (gl_eq_iff.2 (h.trans ofMat_glOne.symm))
  obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hcode
  have hyx' := code_injective hyx
  rw [cover13, List.mem_append] at hy
  rcases hy with hy | hy
  · exact absurd ((mem_F0_iff x).2 (hyx' ▸ (List.mem_filter.1 hy).1)) hxF0
  obtain ⟨p, hp, hy⟩ := List.mem_flatMap.1 hy
  obtain ⟨r, hr, hy⟩ := List.mem_flatMap.1 hy
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_range] at hk
  obtain ⟨hpinv, -, hpdet⟩ := bloom13_parts.2.1 p hp
  obtain ⟨hrdet, -, -⟩ := bloom13_parts.2.2.2.2.2 r hr
  obtain ⟨c, hc⟩ := exists_gl hpdet
  obtain ⟨xr, hxr⟩ := exists_gl hrdet
  have hcinv : ofMat ((c⁻¹ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = p.2 :=
    ofMat_inv_of_rmul (by rw [hc]; exact hpinv)
  refine ⟨c, (mem_NF0_iff c).2 (by rw [hc]; exact List.mem_map_of_mem hp), r, hr, xr, hxr, k, hk,
    ?_⟩
  rw [gl_eq_iff, ofMat_glMul, ofMat_glMul, ofMat_glPow, hcinv, hc, hxr]
  exact hyx'.symm

theorem statedSL_le_sup_F0
    {F : Subgroup GL33} (hF : Nat.card F = 13) (hne : F ≠ F0) :
    CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ F0 ⊔ F := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.1 (by rw [hF]; norm_num)
  obtain ⟨⟨x, hxF⟩, hx1⟩ := exists_ne (1 : F)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx13 : x ^ 13 = 1 := by
    have := pow_card_eq_one' (G := F) (x := ⟨x, hxF⟩)
    rw [hF] at this
    exact congrArg Subtype.val this
  have hord : orderOf x = 13 := orderOf_eq_prime hx13 hx1'
  have hzF : zpowers x = F := Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hxF)
    (by rw [hF, Nat.card_zpowers, hord])
  have hxF0 : x ∉ F0 := by
    intro h
    apply hne
    rw [← hzF]
    exact Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 h)
      (by rw [card_F0, Nat.card_zpowers, hord])
  obtain ⟨c, hcN, r, hr, xr, hxr, k, hk, hxeq⟩ := exists_conj_rep hx13 hx1' hxF0
  have hxr13 : xr ^ 13 = 1 := by
    rw [gl_eq_iff, ofMat_glPow, hxr, (bloom13_parts.2.2.2.2.2 r hr).2.1, ofMat_glOne]
  have hw13 : (c * xr * c⁻¹) ^ 13 = 1 := by
    rw [conj_pow, hxr13, mul_one, mul_inv_cancel]
  have hwF : c * xr * c⁻¹ ∈ F := by
    rw [← hzF, hxeq, ← conj_pow]
    exact mem_zpowers_pow_of_lt hw13 hk
  have hSL := statedSL_le_closure_rep hr xr hxr
  have hle : Subgroup.closure {y | y ∈ [cGL, xr]} ≤
      (F0 ⊔ F).comap (MulAut.conj c).toMonoidHom := by
    rw [closure_le]
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Subgroup.mem_sup_left ((mem_normalizer_iff.1 hcN _).1 (mem_zpowers _))
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact Subgroup.mem_sup_right hwF
      · exact absurd hy (List.not_mem_nil)
  intro s hs
  have hs' : c⁻¹ * s * c ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) := by
    simpa using (CFSG.RankThree.SubgroupLists.statedSL_normal 3 (ZMod 3)).conj_mem s hs c⁻¹
  have h3 := hle (hSL hs')
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h3
  rwa [show c * (c⁻¹ * s * c) * c⁻¹ = s by group] at h3

theorem statedSL_le_sup
    {F₁ F₂ : Subgroup GL33} (h₁ : Nat.card F₁ = 13) (h₂ : Nat.card F₂ = 13)
    (hne : F₁ ≠ F₂) : CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ F₁ ⊔ F₂ := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hF0 : Nat.card F0 = 13 ^ (Nat.card GL33).factorization 13 := by
    rw [factorization_GL33, card_F0, pow_one]
  have hF1 : Nat.card F₁ = 13 ^ (Nat.card GL33).factorization 13 := by
    rw [factorization_GL33, h₁, pow_one]
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_sylow_eq_map hF0 (Sylow.ofCard F₁ hF1)
  rw [Sylow.coe_ofCard] at hg
  set F₂' := F₂.map (MulAut.conj g⁻¹).toMonoidHom with hF₂'
  have hback : F₂'.map (MulAut.conj g).toMonoidHom = F₂ := by
    rw [hF₂', Subgroup.map_map]
    convert Subgroup.map_id F₂ using 2
    ext h
    simp [mul_assoc]
  have hne' : F₂' ≠ F0 := by
    intro h
    apply hne
    rw [hg, ← h, hback]
  have hc2 : Nat.card F₂' = 13 := by
    rw [hF₂', CFSG.RankThree.Asc83Table.card_map_conj, h₂]
  have hle := statedSL_le_sup_F0 hc2 hne'
  intro s hs
  have hs' : g⁻¹ * s * g ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) := by
    simpa using (CFSG.RankThree.SubgroupLists.statedSL_normal 3 (ZMod 3)).conj_mem s hs g⁻¹
  have h2 : s ∈ (F0 ⊔ F₂').map (MulAut.conj g).toMonoidHom :=
    ⟨g⁻¹ * s * g, hle hs', by simp [mul_assoc]⟩
  rwa [Subgroup.map_sup, ← hg, hback] at h2

end CFSG.RankThree.PartTwo.Toolkit

module

public import CFSG.Monster.B.Fischer.InducedSet
public import Certificates.Certificate16010

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

theorem isEchelon_K : IsEchelon 12 pivK rowK :=
  Certificates.certificate16010.1

theorem rowK_eq :
    ∀ l < 12, rowK l = xorSel (coefK l).testBit genQ 12 :=
  Certificates.certificate16010.2.1

theorem red_genK : ∀ j < 12, red 12 pivK rowK (genQ j) = 0 :=
  Certificates.certificate16010.2.2.1

theorem genQ_mem_K₀ {j : ℕ} (hj : j < 12) : vecOf (genQ j) ∈ K₀ := by
  unfold genQ
  split_ifs with h1
  · exact E₀_le_K₀ (rowE_mem_E₀ ⟨j, h1⟩)
  · rw [← v₀_eq_vecOf]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · omega

theorem K₀_eq : K₀ = spanRows 12 rowK := by
  refine le_antisymm ?_ ?_
  · rw [K₀, sup_le_iff, E₀_eq]
    refine ⟨?_, ?_⟩
    · rw [spanRows, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      show vecOf (rowE l) ∈ spanRows 12 rowK
      have e : rowE l = genQ l := by simp [genQ, l.2]
      rw [e]
      exact (vecOf_mem_span_iff isEchelon_K (genQ_lt l (by omega))).2 (red_genK l (by omega))
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, v₀_eq_vecOf]
      exact (vecOf_mem_span_iff isEchelon_K (genQ_lt 11 (by omega))).2 (red_genK 11 (by omega))
  · rw [spanRows, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    show vecOf (rowK l) ∈ K₀
    rw [rowK_eq l l.2, vecOf_xorSel]
    refine Submodule.sum_mem _ fun j _ => ?_
    split_ifs
    · exact genQ_mem_K₀ j.2
    · exact Submodule.zero_mem _

theorem vecOf_mem_K₀_iff
    {m : ℕ} (hm : m < 2 ^ 22) : vecOf m ∈ K₀ ↔ red 12 pivK rowK m = 0 := by
  rw [K₀_eq]
  exact vecOf_mem_span_iff isEchelon_K hm

@[expose] noncomputable def wv (u : ℕ) : W₀ := K₀.mkQ (vecOf (spreadW u))

theorem freeW_lt : ∀ t, freeW t < 22 := by
  intro t
  unfold freeW
  rcases Nat.lt_or_ge t 10 with h | h
  · interval_cases t <;> decide
  · rw [List.getD_eq_default _ _ (by simp; omega)]; decide

theorem spreadW_lt (u : ℕ) : spreadW u < 2 ^ 22 :=
  xorSel_lt _ (fun t => Nat.pow_lt_pow_right (by norm_num) (freeW_lt t)) _

theorem spreadW_xor (a b : ℕ) : spreadW (a ^^^ b) = spreadW a ^^^ spreadW b := by
  rw [spreadW, spreadW, spreadW, ← xorSel_xor]
  congr 1
  funext t
  rw [Nat.testBit_xor]

theorem wv_xor (a b : ℕ) : wv (a ^^^ b) = wv a + wv b := by
  rw [wv, wv, wv, spreadW_xor, vecOf_xor, map_add]

theorem wv_zero : wv 0 = 0 := by
  rw [wv, show spreadW 0 = 0 from rfl, vecOf_zero, map_zero]

theorem red_spreadW :
    ∀ u < 1024, red 12 pivK rowK (spreadW u) = 0 → u = 0 :=
  Certificates.certificate16010.2.2.2.1

theorem wv_eq_zero_iff
    {u : ℕ} (hu : u < 1024) : wv u = 0 ↔ u = 0 := by
  constructor
  · intro h
    rw [wv, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      vecOf_mem_K₀_iff (spreadW_lt u)] at h
    exact red_spreadW u hu h
  · rintro rfl
    exact wv_zero

theorem add_self_W (x : W₀) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem wv_inj
    {u u' : ℕ} (hu : u < 1024) (hu' : u' < 1024) (h : wv u = wv u') : u = u' := by
  have hx : u ^^^ u' < 1024 := Nat.xor_lt_two_pow (n := 10) hu hu'
  have h0 : wv (u ^^^ u') = 0 := by rw [wv_xor, h, add_self_W]
  have := (wv_eq_zero_iff hx).1 h0
  have := congrArg (· ^^^ u') this
  simpa [Nat.xor_assoc] using this

theorem natCard_W₀ : Nat.card W₀ = 1024 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_W₀]
  norm_num

theorem wv_bijective :
    Function.Bijective fun u : Fin 1024 => wv u :=
  Function.Injective.bijective_of_nat_card_le (f := fun u : Fin 1024 => wv u)
    (fun a b h => Fin.ext (wv_inj a.2 b.2 h))
    (by rw [natCard_W₀, Nat.card_eq_fintype_card, Fintype.card_fin])

theorem wv_surj (w : W₀) : ∃ u < 1024, wv u = w := by
  obtain ⟨u, hu⟩ := wv_bijective.2 w
  exact ⟨u, u.2, hu⟩

@[expose] noncomputable def wEquiv :
    Fin 1024 ≃ W₀ := Equiv.ofBijective _ wv_bijective

theorem wEquiv_apply (u : Fin 1024) : wEquiv u = wv u := rfl

theorem matW_check : ∀ g < 2, ∀ u < 1024,
    red 12 pivK rowK (xorSel (spreadW u).testBit (fun t => 2 ^ genAB' g t) 22 ^^^
      spreadW (linW g u)) = 0 :=
  Certificates.certificate16010.2.2.2.2.1

theorem genAB'_spec (g : ℕ) (hg : g < 2) : ∀ t : Fin 22,
    ((psiHom (genAB g : CFSG.Blueprint.NativeSporadic.M22) (coordAt t : Fin 24)) : ℕ) =
      genAB' g t + 2 := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · exact genA_spec
  · exact genB_spec

theorem genAB'_lt (g : ℕ) : ∀ t : Fin 22, genAB' g t < 22 := by
  intro t
  unfold genAB'
  split_ifs
  · exact genA_lt t
  · exact genB_lt t

theorem rhoW_wv
    {g : ℕ} (hg : g < 2) {u : ℕ} (hu : u < 1024) :
    rhoW (genAB g) (wv u) = wv (linW g u) := by
  rw [wv, rhoW_mkQ, rho₀_vecOf (g := genAB g) (genAB'_spec g hg) (genAB'_lt g), wv,
    Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, sub_eq_add_neg,
    ZModModule.neg_eq_self, ← vecOf_xor, vecOf_mem_K₀_iff (Nat.xor_lt_two_pow
      (gen_xor_lt (genAB'_lt g) _) (spreadW_lt _))]
  exact matW_check g hg u hu

theorem linW_lt : ∀ g < 2, ∀ u < 1024, linW g u < 1024 :=
  Certificates.certificate16010.2.2.2.2.2.1

@[expose] noncomputable def cosetWt (w : W₀) : ℕ :=
  sInf {n | ∃ v : V₀, K₀.mkQ v = w ∧ hammingNorm v = n}

theorem cosetWt_le {v : V₀} : cosetWt (K₀.mkQ v) ≤ hammingNorm v :=
  Nat.sInf_le ⟨v, rfl, rfl⟩

theorem exists_cosetWt (w : W₀) : ∃ v : V₀, K₀.mkQ v = w ∧ hammingNorm v = cosetWt w := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective K₀ w
  have hne : ({n | ∃ v' : V₀, K₀.mkQ v' = K₀.mkQ v ∧ hammingNorm v' = n} : Set ℕ).Nonempty :=
    ⟨hammingNorm v, v, rfl, rfl⟩
  exact Nat.sInf_mem hne

theorem cosetWt_eq_iff {w : W₀} {n : ℕ} :
    cosetWt w = n ↔ (∃ v : V₀, K₀.mkQ v = w ∧ hammingNorm v = n) ∧
      ∀ v : V₀, K₀.mkQ v = w → n ≤ hammingNorm v := by
  constructor
  · rintro rfl
    exact ⟨exists_cosetWt w, fun v hv => hv ▸ cosetWt_le⟩
  · rintro ⟨⟨v, hv, rfl⟩, h⟩
    refine le_antisymm (hv ▸ cosetWt_le) ?_
    obtain ⟨v', hv', e⟩ := exists_cosetWt w
    exact e ▸ h v' hv'

theorem hammingNorm_permRep (σ : Equiv.Perm X₀) (v : V₀) :
    hammingNorm (permRep σ v) = hammingNorm v := by
  rw [hammingNorm_eq_sum_val, hammingNorm_eq_sum_val]
  exact Equiv.sum_comp σ.symm fun i => (v i).val

theorem cosetWt_rhoW
    (k : CFSG.Blueprint.NativeSporadic.M22) (w : W₀) :
    cosetWt (rhoW k w) = cosetWt w := by
  have key : ∀ (k : CFSG.Blueprint.NativeSporadic.M22) (w : W₀),
      cosetWt (rhoW k w) ≤ cosetWt w := by
    intro k w
    obtain ⟨v, rfl, e⟩ := exists_cosetWt w
    rw [rhoW_mkQ, ← e]
    refine (cosetWt_le).trans ?_
    rw [rho₀_apply, hammingNorm_permRep]
  refine le_antisymm (key k w) ?_
  have := key k⁻¹ (rhoW k w)
  rwa [rhoW_inv_apply] at this

theorem eq_sum_e (v : V₀) : v = ∑ i ∈ Finset.univ.filter (v · ≠ 0), e i := by
  funext j
  rw [Finset.sum_apply]
  simp only [e, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  have h : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  by_cases hj : v j = 0
  · simp [hj]
  · simp [h _ hj]

theorem e_eq_vecOf (i : X₀) : e i = vecOf (2 ^ (pos i : ℕ)) := by
  rw [vecOf_two_pow, coordAt_pos]

theorem low_weight {v : V₀} (hv : hammingNorm v ≤ 2) :
    v = 0 ∨ (∃ x : Fin 22, v = vecOf (2 ^ (x : ℕ))) ∨
      ∃ x y : Fin 22, v = vecOf (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ)) := by
  rw [eq_sum_e v]
  have hs : (Finset.univ.filter (v · ≠ 0)).card ≤ 2 := hv
  rcases Nat.lt_or_ge (Finset.univ.filter (v · ≠ 0)).card 1 with h0 | h1
  · left
    rw [Finset.card_eq_zero.1 (show (Finset.univ.filter (v · ≠ 0)).card = 0 by omega)]
    simp
  rcases Nat.lt_or_ge (Finset.univ.filter (v · ≠ 0)).card 2 with h1' | h2
  · right; left
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1
      (show (Finset.univ.filter (v · ≠ 0)).card = 1 by omega)
    rw [hx, Finset.sum_singleton, e_eq_vecOf]
    exact ⟨pos x, rfl⟩
  · right; right
    obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.1
      (show (Finset.univ.filter (v · ≠ 0)).card = 2 by omega)
    rw [hxy', Finset.sum_pair hxy, e_eq_vecOf, e_eq_vecOf, ← vecOf_xor]
    exact ⟨pos x, pos y, rfl⟩

theorem seed_check :
    red 12 pivK rowK 1 ≠ 0 ∧ red 12 pivK rowK 3 ≠ 0 ∧
    (∀ x : Fin 22, red 12 pivK rowK (3 ^^^ 2 ^ (x : ℕ)) ≠ 0) ∧
    red 12 pivK rowK 7 ≠ 0 ∧ (∀ x : Fin 22, red 12 pivK rowK (7 ^^^ 2 ^ (x : ℕ)) ≠ 0) ∧
    ∀ x y : Fin 22, red 12 pivK rowK (7 ^^^ (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ))) ≠ 0 :=
  Certificates.certificate16010.2.2.2.2.2.2.1

theorem two_pow_lt_22 (x : Fin 22) : 2 ^ (x : ℕ) < 2 ^ 22 :=
  Nat.pow_lt_pow_right (by norm_num) x.2

theorem not_mem_K₀
    {m : ℕ} (hm : m < 2 ^ 22) (h : red 12 pivK rowK m ≠ 0) : vecOf m ∉ K₀ :=
  fun h' => h ((vecOf_mem_K₀_iff hm).1 h')

theorem mkQ_eq_iff_mem (v w : V₀) : K₀.mkQ v = K₀.mkQ w ↔ v + w ∈ K₀ := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, sub_eq_add_neg,
    ZModModule.neg_eq_self]

theorem cosetWt_seed :
    cosetWt (wv 0) = 0 ∧ cosetWt (wv 1) = 1 ∧ cosetWt (wv 3) = 2 ∧ cosetWt (wv 7) = 3 := by
  obtain ⟨c1, c3, c3x, c7, c7x, c7xy⟩ := seed_check
  have hs1 : spreadW 1 = 1 := Certificates.certificate16010.2.2.2.2.2.2.2.1
  have hs3 : spreadW 3 = 3 := Certificates.certificate16010.2.2.2.2.2.2.2.2.1
  have hs7 : spreadW 7 = 7 := Certificates.certificate16010.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [wv_zero]
    exact cosetWt_eq_iff.2 ⟨⟨(0 : V₀), map_zero _, hammingNorm_zero⟩, fun _ _ => Nat.zero_le _⟩
  · refine cosetWt_eq_iff.2 ⟨⟨vecOf 1, by rw [wv, hs1], ?_⟩, fun v hv => ?_⟩
    · rw [hammingNorm_vecOf]; decide
    · by_contra hlt
      push Not at hlt
      have hv0 : v = 0 := by
        rw [Nat.lt_one_iff, hammingNorm_eq_zero] at hlt
        exact hlt
      rw [hv0, wv, hs1, mkQ_eq_iff_mem, zero_add] at hv
      exact not_mem_K₀ (by norm_num) c1 hv
  · refine cosetWt_eq_iff.2 ⟨⟨vecOf 3, by rw [wv, hs3], ?_⟩, fun v hv => ?_⟩
    · rw [hammingNorm_vecOf]; decide
    · by_contra hlt
      push Not at hlt
      rw [wv, hs3, mkQ_eq_iff_mem] at hv
      rcases low_weight (by omega : hammingNorm v ≤ 2) with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
      · rw [zero_add] at hv
        exact not_mem_K₀ (by norm_num) c3 hv
      · rw [← vecOf_xor, Nat.xor_comm] at hv
        exact not_mem_K₀ (Nat.xor_lt_two_pow (by norm_num) (two_pow_lt_22 x)) (c3x x) hv
      · exfalso
        rw [hammingNorm_vecOf] at hlt
        have : ∀ x y : Fin 22, popc 22 (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ)) = 0 ∨
            popc 22 (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ)) = 2 :=
          Certificates.certificate16010.2.2.2.2.2.2.2.2.2.2
        rcases this x y with h | h
        · have hxy : (2 : ℕ) ^ (x : ℕ) ^^^ 2 ^ (y : ℕ) = 0 := by
            have := congrArg (fun m => hammingNorm (vecOf m)) (rfl :
              (2 : ℕ) ^ (x : ℕ) ^^^ 2 ^ (y : ℕ) = 2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ))
            rw [← hammingNorm_vecOf] at h
            have hz := hammingNorm_eq_zero.1 h
            exact vecOf_inj (Nat.xor_lt_two_pow (two_pow_lt_22 x) (two_pow_lt_22 y))
              (by norm_num) (hz.trans vecOf_zero.symm)
          rw [hxy, vecOf_zero, zero_add] at hv
          exact not_mem_K₀ (by norm_num) c3 hv
        · omega
  · refine cosetWt_eq_iff.2 ⟨⟨vecOf 7, by rw [wv, hs7], ?_⟩, fun v hv => ?_⟩
    · rw [hammingNorm_vecOf]; decide
    · by_contra hlt
      push Not at hlt
      rw [wv, hs7, mkQ_eq_iff_mem] at hv
      rcases low_weight (by omega : hammingNorm v ≤ 2) with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
      · rw [zero_add] at hv
        exact not_mem_K₀ (by norm_num) c7 hv
      · rw [← vecOf_xor, Nat.xor_comm] at hv
        exact not_mem_K₀ (Nat.xor_lt_two_pow (by norm_num) (two_pow_lt_22 x)) (c7x x) hv
      · rw [← vecOf_xor, Nat.xor_comm] at hv
        exact not_mem_K₀ (Nat.xor_lt_two_pow (by norm_num)
          (Nat.xor_lt_two_pow (two_pow_lt_22 x) (two_pow_lt_22 y))) (c7xy x y) hv

end CFSG.Monster.B.Fischer

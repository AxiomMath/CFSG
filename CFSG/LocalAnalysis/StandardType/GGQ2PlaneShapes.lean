module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneRaw

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def unitVec (t : ℕ) (a : Fin t) : V t := Pi.single a 1

@[expose] def LineShapes : Prop :=
  ∀ (t : ℕ) (k : PlaneKind) (v : V t) (c : Code t), v ≠ 0 →
    occurs (Submodule.span F {v}) c → cent k c = Submodule.span F {v} →
      (∃ (a : Fin t) (s : F), s ≠ 0 ∧ v = s • unitVec t a ∧ c = .zero (Finset.univ.erase a)) ∨
        ((∀ i, v i ≠ 0) ∧ (c = .extension v ∨ c = .extension (-v)))

@[expose] def PlaneShapes : Prop :=
  ∀ (t : ℕ) (k : PlaneKind) (U : Submodule F (V t)) (c : Code t), finrank F U = 2 →
    occurs U c → cent k c = U →
      (∃ a b : Fin t, a ≠ b ∧ U = Submodule.span F {unitVec t a, unitVec t b} ∧
          c = .zero (Finset.univ \ {a, b})) ∨
        (∃ (a : Fin t) (e : V t), e a = 0 ∧ (∀ i, i ≠ a → e i ≠ 0) ∧ c = .extension e ∧
          U = Submodule.span F {unitVec t a, e})

private lemma pls_sq_eq_one (a : F) (ha : a ≠ 0) : a * a = 1 := by
  revert a
  decide

private lemma pls_eq_one_or_neg_one (a : F) (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  revert a
  decide

private def pls_zeroSet {t : ℕ} (e : V t) : Finset (Fin t) :=
  Finset.univ.filter fun i => e i = 0

private theorem pls_mem_zeroSet {t : ℕ} (e : V t) (i : Fin t) :
    i ∈ pls_zeroSet e ↔ e i = 0 := by
  simp [pls_zeroSet]

private theorem pls_exists_ne_zero {t : ℕ} {e : V t} (he : e ≠ 0) :
    ∃ i, e i ≠ 0 := by
  by_contra h
  apply he
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

private theorem pls_spanSubset_eq_span_image {t : ℕ} (T : Set (Fin t)) :
    Pi.spanSubset F T = Submodule.span F (unitVec t '' T) := by
  rw [Pi.spanSubset]
  congr 1
  ext w
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [Pi.basisFun_apply]; rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [Pi.basisFun_apply]; rfl⟩

private theorem pls_centZero_eq {t : ℕ} (S : Finset (Fin t)) :
    centZero S = Pi.spanSubset F (Sᶜ : Set (Fin t)) := by
  ext v
  rw [mem_centZero, Pi.mem_spanSubset_iff]
  constructor
  · intro hv i hi
    exact hv i (by simpa using hi)
  · intro hv i hi
    exact hv i (by simpa using hi)

private theorem pls_finrank_centZero {t : ℕ} (S : Finset (Fin t)) :
    finrank F (centZero S) = Sᶜ.card := by
  rw [pls_centZero_eq, Pi.dim_spanSubset, ← Finset.coe_compl, Set.ncard_coe_finset]

private theorem pls_centExt_eq {t : ℕ} (k : PlaneKind) {e : V t} (he : e ≠ 0) :
    cent k (Code.extension e) =
      Submodule.span F {e} ⊔ Pi.spanSubset F (pls_zeroSet e : Set (Fin t)) := by
  obtain ⟨a₀, ha₀⟩ := pls_exists_ne_zero he
  apply le_antisymm
  · intro v hv
    have hw : v - (e a₀ * v a₀) • e ∈
        Pi.spanSubset F (pls_zeroSet e : Set (Fin t)) := by
      rw [Pi.mem_spanSubset_iff]
      intro i hi
      have hei : e i ≠ 0 := by
        intro h
        exact hi (by simpa [pls_mem_zeroSet] using h)
      have hcent := (mem_cent_extension k e v).mp hv i (by simpa using hei)
        a₀ (by simpa using ha₀)
      have hsq := pls_sq_eq_one (e i) hei
      have hμ : v i = (e a₀ * v a₀) * e i := by
        calc v i = (e i * e i) * v i := by rw [hsq, one_mul]
          _ = e i * (e i * v i) := by ring
          _ = e i * (e a₀ * v a₀) := by rw [hcent]
          _ = (e a₀ * v a₀) * e i := by ring
      simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hμ]
    have hv_eq : v = (e a₀ * v a₀) • e + (v - (e a₀ * v a₀) • e) := by abel
    rw [hv_eq]
    exact Submodule.add_mem_sup
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e))) hw
  · apply sup_le
    · rw [Submodule.span_le]
      rintro x rfl
      change x ∈ cent k (Code.extension x)
      rw [mem_cent_extension]
      intro i hi j hj
      rw [pls_sq_eq_one (x i) (by simpa using hi),
        pls_sq_eq_one (x j) (by simpa using hj)]
    · intro v hv
      rw [Pi.mem_spanSubset_iff] at hv
      rw [mem_cent_extension]
      intro i hi j hj
      have hi0 : v i = 0 := hv i (by
        intro hmem
        have hei : e i ≠ 0 := by simpa using hi
        have hei0 : e i = 0 := by simpa [pls_mem_zeroSet] using hmem
        exact hei hei0)
      have hj0 : v j = 0 := hv j (by
        intro hmem
        have hej : e j ≠ 0 := by simpa using hj
        have hej0 : e j = 0 := by simpa [pls_mem_zeroSet] using hmem
        exact hej hej0)
      rw [hi0, hj0, mul_zero, mul_zero]

private theorem pls_centExt_inf {t : ℕ} {e : V t} (he : e ≠ 0) :
    Submodule.span F {e} ⊓ Pi.spanSubset F (pls_zeroSet e : Set (Fin t)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvspan, hvsupp⟩ := hv
  rw [Pi.mem_spanSubset_iff] at hvsupp
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvspan
  obtain ⟨a₀, ha₀⟩ := pls_exists_ne_zero he
  have ha₀Z : a₀ ∉ pls_zeroSet e := by
    rw [pls_mem_zeroSet]
    exact ha₀
  have hv0 : v a₀ = 0 := hvsupp a₀ ha₀Z
  have hce : c * e a₀ = 0 := by
    have := congrFun hc a₀
    simpa [Pi.smul_apply, smul_eq_mul, hv0] using this
  have hc0 : c = 0 := (mul_eq_zero.mp hce).resolve_right ha₀
  rw [Submodule.mem_bot, ← hc, hc0, zero_smul]

private theorem pls_finrank_centExt {t : ℕ} (k : PlaneKind) {e : V t} (he : e ≠ 0) :
    finrank F (cent k (Code.extension e)) = 1 + (pls_zeroSet e).card := by
  rw [pls_centExt_eq k he]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (K := F) (V := V t)
    (s := Submodule.span F {e}) (t := Pi.spanSubset F (pls_zeroSet e : Set (Fin t)))
  rw [pls_centExt_inf he, finrank_bot, add_zero] at hdim
  rw [hdim, finrank_span_singleton he, Pi.dim_spanSubset]
  congr 1
  rw [Set.ncard_coe_finset]

private theorem pls_eq_univ_erase_of_compl_eq {t : ℕ} {S : Finset (Fin t)} {a : Fin t}
    (h : Sᶜ = {a}) : S = Finset.univ.erase a := by
  ext i
  have hi : i ∈ S ↔ i ∉ Sᶜ := by simp
  rw [hi, h]
  simp [Finset.mem_erase]

private theorem pls_eq_univ_sdiff_of_compl_eq {t : ℕ} {S : Finset (Fin t)} {a b : Fin t}
    (h : Sᶜ = {a, b}) : S = Finset.univ \ {a, b} := by
  ext i
  have hi : i ∈ S ↔ i ∉ Sᶜ := by simp
  rw [hi, h]
  simp [Finset.mem_sdiff]

theorem lineShapes_holds : LineShapes := by
  intro t k v c hv hocc hcent
  cases c with
  | zero S =>
      change centZero S = Submodule.span F {v} at hcent
      have hfr : finrank F (centZero S) = 1 := by
        rw [hcent, finrank_span_singleton hv]
      have hcard : Sᶜ.card = 1 := by
        rw [← pls_finrank_centZero S, hfr]
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
      have hS : S = Finset.univ.erase a := pls_eq_univ_erase_of_compl_eq ha
      have hvcent : v ∈ centZero S := by
        rw [hcent]
        exact Submodule.mem_span_singleton_self v
      have hvzero : ∀ i ∈ S, v i = 0 := (mem_cent_zero k S v).mp hvcent
      have hva : v a ≠ 0 := by
        intro h0
        apply hv
        funext i
        by_cases hia : i = a
        · rw [hia]; exact h0
        · have hiS : i ∈ S := by
            rw [hS, Finset.mem_erase]
            exact ⟨hia, Finset.mem_univ i⟩
          rw [hvzero i hiS]
          simp
      refine Or.inl ⟨a, v a, hva, ?_, ?_⟩
      · funext i
        by_cases hia : i = a
        · subst hia
          simp [unitVec, Pi.smul_apply, smul_eq_mul]
        · have hiS : i ∈ S := by
            rw [hS, Finset.mem_erase]
            exact ⟨hia, Finset.mem_univ i⟩
          rw [hvzero i hiS]
          simp [unitVec, hia, Pi.smul_apply, smul_eq_mul]
      · rw [hS]
  | extension e =>
      obtain ⟨he, _⟩ := hocc
      change centExt e = Submodule.span F {v} at hcent
      have hfr : finrank F (centExt e) = 1 := by
        rw [hcent, finrank_span_singleton hv]
      have hfe : finrank F (centExt e) = 1 + (pls_zeroSet e).card := by
        change finrank F (cent k (Code.extension e)) = 1 + (pls_zeroSet e).card
        exact pls_finrank_centExt k he
      have hzcard : (pls_zeroSet e).card = 0 := by
        have h1 : 1 + (pls_zeroSet e).card = 1 := by omega
        omega
      have hzero_empty : pls_zeroSet e = ∅ := Finset.card_eq_zero.mp hzcard
      have hfull : ∀ i, e i ≠ 0 := by
        intro i
        have hi : i ∉ pls_zeroSet e := by rw [hzero_empty]; simp
        simpa [pls_mem_zeroSet] using hi
      have he_cent : e ∈ cent k (.extension e) := by
        rw [mem_cent_extension]
        intro i hi j hj
        rw [pls_sq_eq_one (e i) (by simpa using hi),
          pls_sq_eq_one (e j) (by simpa using hj)]
      have he_mem : e ∈ Submodule.span F {v} := by
        rw [← hcent]
        exact he_cent
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp he_mem
      have hs0 : s ≠ 0 := by
        intro h0
        apply he
        rw [← hs, h0, zero_smul]
      have hvfull : ∀ i, v i ≠ 0 := by
        intro i hvi
        have hei : e i ≠ 0 := hfull i
        have h := congrFun hs i
        simp [Pi.smul_apply, smul_eq_mul, hvi] at h
        exact hei h.symm
      rcases pls_eq_one_or_neg_one s hs0 with h1 | h1
      · refine Or.inr ⟨hvfull, Or.inl ?_⟩
        rw [← hs, h1, one_smul]
      · refine Or.inr ⟨hvfull, Or.inr ?_⟩
        rw [← hs, h1, neg_one_smul]

theorem planeShapes_holds : PlaneShapes := by
  intro t k U c hU hocc hcent
  cases c with
  | zero S =>
      change centZero S = U at hcent
      have hfr : finrank F (centZero S) = 2 := by
        rw [hcent, hU]
      have hcard : Sᶜ.card = 2 := by
        rw [← pls_finrank_centZero S, hfr]
      obtain ⟨a, b, hab, hcompl⟩ := Finset.card_eq_two.mp hcard
      have hS : S = Finset.univ \ {a, b} := pls_eq_univ_sdiff_of_compl_eq hcompl
      have hspanSubset : Pi.spanSubset F ({a, b} : Set (Fin t)) =
          Submodule.span F ({unitVec t a, unitVec t b} : Set (V t)) := by
        rw [pls_spanSubset_eq_span_image]
        congr 1
        ext w
        simp
      have hUeq : U = Submodule.span F ({unitVec t a, unitVec t b} : Set (V t)) := by
        rw [← hcent, pls_centZero_eq, ← Finset.coe_compl, hcompl]
        rw [show (({a, b} : Finset (Fin t)) : Set (Fin t)) = ({a, b} : Set (Fin t)) by simp]
        rw [hspanSubset]
      refine Or.inl ⟨a, b, hab, hUeq, ?_⟩
      rw [hS]
  | extension e =>
      obtain ⟨he, _⟩ := hocc
      change centExt e = U at hcent
      have hfr : finrank F (centExt e) = 2 := by
        rw [hcent, hU]
      have hfe : finrank F (centExt e) = 1 + (pls_zeroSet e).card := by
        change finrank F (cent k (Code.extension e)) = 1 + (pls_zeroSet e).card
        exact pls_finrank_centExt k he
      have hcard : (pls_zeroSet e).card = 1 := by
        have h1 : 1 + (pls_zeroSet e).card = 2 := by omega
        omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
      have ha0 : e a = 0 := by
        have : a ∈ pls_zeroSet e := by rw [ha]; simp
        simpa [pls_mem_zeroSet] using this
      have hother : ∀ i, i ≠ a → e i ≠ 0 := by
        intro i hia hi0
        have : i ∈ pls_zeroSet e := by simpa [pls_mem_zeroSet] using hi0
        rw [ha] at this
        exact hia (by simpa using this)
      have hspanSubset : Pi.spanSubset F ({a} : Set (Fin t)) =
          Submodule.span F ({unitVec t a} : Set (V t)) := by
        rw [pls_spanSubset_eq_span_image]
        simp
      have hUeq : U = Submodule.span F ({unitVec t a, e} : Set (V t)) := by
        rw [← hcent]
        change cent k (Code.extension e) = Submodule.span F ({unitVec t a, e} : Set (V t))
        rw [pls_centExt_eq k he, ha]
        rw [show (({a} : Finset (Fin t)) : Set (Fin t)) = ({a} : Set (Fin t)) by simp]
        rw [hspanSubset]
        rw [show ({unitVec t a, e} : Set (V t)) = insert e {unitVec t a} by
          ext w; simp [or_comm]]
        rw [Submodule.span_insert]
      refine Or.inr ⟨a, e, ha0, hother, rfl, hUeq⟩

end

end CFSG.StandardType.GGQ2Frame.PlaneRaw

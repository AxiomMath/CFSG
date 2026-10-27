module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentPair
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentAssemble
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentOdd
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open TensorProduct Matrix Module CFSG.GroupTheory.SteinbergBK CFSG.Blueprint.EvenSource
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.RankThree.Classical.SteinbergBY

structure DescentSplitting {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (U : similarityPairs Q) (c : Kˣ)
    (Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)) where
  m : ℕ
  δ : ℕ
  hδ : δ ≤ 2
  H : HypSplit Q₀ m δ
  HK : HypSplit ((c : K) • Q) m δ
  hbK : ∀ a, HK.b a = ((H.b a : fixedSpace U.val) : Fin d → K)
  dim : 2 * m + δ = d
  witt : sourceWittIndex ⇑Q = m

variable {K : Type} [Field K] {d : ℕ}

theorem iterate_coordinateSemilinearMap (U : coordinateSemilinearGroup d K) (m : ℕ)
    (v : Fin d → K) :
    (⇑(coordinateSemilinearMap U))^[m] v = coordinateSemilinearMap (U ^ m) v := by
  induction m generalizing v with
  | zero => simp [coordinateSemilinearMap_one]
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, pow_succ, coordinateSemilinearMap_mul]

theorem polarBilin_smul_nondegenerate {V : Type} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (c : Kˣ) :
    (QuadraticMap.polarBilin ((c : K) • Q)).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => ?_
  refine CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero hnd fun w => ?_
  have h := hv w
  simp only [FunLike.coe_smul, QuadraticMap.polar_smul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left c.ne_zero

theorem sourceWittIndex_smul {V : Type} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (c : Kˣ) : sourceWittIndex ⇑((c : K) • Q) = sourceWittIndex ⇑Q := by
  unfold sourceWittIndex
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, _root_.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨W, hW, hn⟩
    exact ⟨W, fun w hw => (mul_eq_zero.mp (hW w hw)).resolve_left c.ne_zero, hn⟩
  · rintro ⟨W, hW, hn⟩
    exact ⟨W, fun w hw => by rw [hW w hw, mul_zero], hn⟩

theorem finrank_fixedField_eq {ℓ f p : ℕ} [Finite K] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (σ : K ≃+* K) (hK : Nat.card K = ℓ ^ f) (hcard : Nat.card (semilinearFixedSubfield σ) =
      ℓ ^ (f / p)) (hdvd : p ∣ f) : finrank (semilinearFixedSubfield σ) K = p := by
  have h1 := Module.natCard_eq_pow_finrank (K := semilinearFixedSubfield σ) (V := K)
  rw [hK, hcard, ← pow_mul] at h1
  have h2 : f = f / p * finrank (semilinearFixedSubfield σ) K :=
    Nat.pow_right_injective hℓ.two_le h1
  obtain ⟨q, hq⟩ := hdvd
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, zero_mul] at hq
      omega
    · exact h
  have hfq : f / p = q := by rw [hq]; exact Nat.mul_div_cancel_left q hp0
  rw [hfq] at h2
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hq
      omega
    · exact h
  have : q * finrank (semilinearFixedSubfield σ) K = q * p := by
    rw [← h2, hq, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hq0 this

theorem descent_core_aux {ℓ f p : ℕ} [Finite K] (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp3 : 3 < p) (hK : Nat.card K = ℓ ^ f) (hd : 0 < d) (Q : QuadraticForm K (Fin d → K))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hS3 : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hgates : OrthogonalGates Q f) (a : MulAut (matrixProjectiveDerived Q))
    (haD : a ∉ (linearConjugationHom Q).range) (hap : orderOf a = p) (g : similarityPairs Q)
    (hg : matrixProjectiveConjugationHom Q g = a) :
    p ∣ f ∧ orderOf g.val.right = p ∧
      Nat.card (semilinearFixedSubfield g.val.right) = ℓ ^ (f / p) ∧
      ∃ (U : similarityPairs Q) (c : Kˣ)
        (Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)),
        matrixProjectiveConjugationHom Q U = a ∧ U.val.right = g.val.right ∧
        FixedFormDescent p Q U c Q₀ ∧ Nonempty (DescentSplitting Q U c Q₀) := by
  classical
  obtain ⟨hker, ⟨ψ, hψg, hψker, -⟩, -⟩ := hgates
  have ha : a ∈ matrixProjectiveImage Q := ⟨g, hg⟩
  have hψa : ψ ⟨a, ha⟩ = g.val.right := by
    rw [← hψg g]
    congr 1
    exact Subtype.ext hg.symm
  have happ : a ^ p = 1 := by
    rw [← hap]
    exact pow_orderOf_eq_one a
  have hσp : g.val.right ^ p = 1 := by
    rw [← hψa, ← map_pow]
    have h1 : (⟨a, ha⟩ : matrixProjectiveImage Q) ^ p = 1 := Subtype.ext happ
    rw [h1, map_one]
  have hσne : g.val.right ≠ 1 := by
    intro h1
    apply haD
    have h2 : (⟨a, ha⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hψa, h1]
    rw [hψker] at h2
    exact h2
  have hσord : orderOf g.val.right = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hσp) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσne
    · exact h
  have hκ : matrixProjectiveConjugationHom Q (g ^ p) = 1 := by rw [map_pow, hg, happ]
  obtain ⟨-, b, hb⟩ := (hker (g ^ p)).mp hκ
  have hb' : (g.val ^ p).left = sc b := hb
  obtain ⟨U, hUr, hUp, hUκ⟩ := exists_normalized_pair Q hd g hσord hb'
  have hσ : orderOf U.val.right = p := by rw [hUr]; exact hσord
  have hap' : ∀ v, (⇑(coordinateSemilinearMap U.val))^[p] v = v := fun v => by
    rw [iterate_coordinateSemilinearMap, hUp, coordinateSemilinearMap_one]
  have hQa : ∀ v, Q (coordinateSemilinearMap U.val v) =
      (multiplier Q U : K) * U.val.right (Q v) := fun v => multiplier_spec Q U v
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨hdvd, hcard, c, Q₀, hQ₀, hnd₀, hfr, Φ, hΦ1, hΦ2⟩ :=
    exists_descent hℓ hf hK U.val.right hσ (coordinateSemilinearMap U.val)
      (coordinateSemilinearMap_smul U.val) hap' Q hnd (multiplier Q U : K) hQa
  have hfr' : finrank (fixedField U.val) (fixedSpace U.val) = d := hfr.trans (by simp)
  have : Finite (fixedField U.val) := inferInstance
  have : FiniteDimensional (fixedField U.val) (fixedSpace U.val) := Module.Finite.of_finite
  have : FiniteDimensional (fixedField U.val) K := Module.Finite.of_finite
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hnd₀
  let ι : fixedSpace U.val →+ (Fin d → K) := (fixedSpace U.val).subtype.toAddMonoidHom
  have hι : ∀ w, ((c : K) • Q) (ι w) = algebraMap (fixedField U.val) K (Q₀ w) := by
    intro w
    have h1 := hQ₀ w
    change (c : K) * Q (w : Fin d → K) = ((Q₀ w : fixedField U.val) : K)
    exact h1.symm
  have hodd : Odd (finrank (fixedField U.val) K) := by
    rw [finrank_fixedField_eq hℓ hf U.val.right hK hcard hdvd]
    exact hp.odd_of_ne_two (by omega)
  let bK : Basis (Fin m ⊕ Fin m ⊕ Fin δ) K (Fin d → K) := (H.b.baseChange K).map Φ
  have hbK : ∀ a, bK a = ι (H.b a) := by
    intro a
    show Φ ((H.b.baseChange K) a) = _
    rw [Basis.baseChange_apply, hΦ1, one_smul]
    rfl
  let HK : HypSplit ((c : K) • Q) m δ := H.extend ι hι hδ hodd bK hbK
  have hndR := polarBilin_smul_nondegenerate Q hnd c
  have hw₀ : sourceWittIndex ⇑Q₀ = m := H.sourceWittIndex_eq hnd₀
  have hw₁ : sourceWittIndex ⇑((c : K) • Q) = m := HK.sourceWittIndex_eq hndR
  have hw₂ : sourceWittIndex ⇑Q = m := by
    rw [← sourceWittIndex_smul Q c]
    exact hw₁
  have hdim : 2 * m + δ = d := H.finrank_eq.symm.trans hfr'
  have hm3 : 3 ≤ m := by
    obtain ⟨T, hT3, hT⟩ := hS3
    have h3 := le_sourceWittIndex (K := K) (V := Fin d → K) (⇑Q) hT
    omega
  refine ⟨hdvd, hσord, ?_, U, c, Q₀, hUκ.trans hg, hUr, ⟨hUp, hQ₀, hnd₀, ⟨Φ, hΦ1, hΦ2, ?_⟩, hfr',
    hw₀.trans hw₂.symm, H.exists_totallySingular_three hm3⟩,
    ⟨⟨m, δ, hδ, H, HK, fun a => hbK a, hdim, hw₂⟩⟩⟩
  · rw [← hUr]
    exact hcard
  · intro x y w w'
    have hpol : ((QuadraticMap.polar Q₀ w w' : fixedField U.val) : K) =
        c * QuadraticMap.polar Q (w : Fin d → K) (w' : Fin d → K) := by
      simp only [QuadraticMap.polar, Subfield.coe_sub, hQ₀, Submodule.coe_add]
      ring
    rw [hΦ1, hΦ1]
    refine ⟨?_, ?_⟩
    · rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hQ₀]
      ring
    · rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hpol]
      ring

end CFSG.RankThree.PartOne.KCOrthogonalDescent

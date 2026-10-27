module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSUCount

public section

namespace CFSG.StandardType

namespace OrdPNsU

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm CFSG.RankThree.PartOne.OddIso

variable {f n : ℕ} {K : Type} [Field K] {p : ℕ} {E : Subgroup ↥(unitarySU 2 f K n)}

theorem exists_su_of_isometry (h : UnitaryFieldData 2 f K) (hp : p.Prime)
    (hpq : ¬ p ∣ 2 ^ f + 1) {z : Module.End K (Fin n → K)}
    (hz : ∀ v w, stdHermForm h n (z v) (z w) = stdHermForm h n v w) (hzp : z ^ p = 1) :
    ∃ g : ↥(unitarySU 2 f K n), lin g = z := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  set M := LinearMap.toMatrixAlgEquiv' z with hM
  have hMv : ∀ v, M *ᵥ v = z v := by
    intro v
    rw [← Matrix.toLinAlgEquiv'_apply, hM, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  have hMp : M ^ p = 1 := by rw [hM, ← map_pow, hzp, map_one]
  have hMiso : ∀ x y, stdHermForm h n (M *ᵥ x) (M *ᵥ y) = stdHermForm h n x y := by
    intro x y
    rw [hMv, hMv]
    exact hz x y
  have hdet := det_eq_one_of_isometry h hp hpq hMiso hMp
  have hMM : M * M ^ (p - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hp1, hMp]
  have hMM' : M ^ (p - 1) * M = 1 := by rw [← pow_succ, Nat.sub_add_cancel hp1, hMp]
  let g₀ : GL (Fin n) K := ⟨M, M ^ (p - 1), hMM, hMM'⟩
  have hg₀ : g₀ ∈ unitarySU 2 f K n := (mem_unitarySU_iff_isometry h).mpr ⟨hdet, hMiso⟩
  exact ⟨⟨g₀, hg₀⟩, LinearMap.ext fun v => by rw [lin_apply]; exact hMv v⟩

theorem nondegOn_orth (h : UnitaryFieldData 2 f K) {X : Submodule K (Fin n → K)}
    (hX : NondegOn (stdHermForm h n) X) :
    NondegOn (stdHermForm h n) (X.orthogonalBilin (stdHermForm h n)) := by
  intro w hw hW
  have hall : ∀ v, stdHermForm h n v w = 0 := by
    intro v
    obtain ⟨m, hm, t, ht, rfl⟩ := exists_add_orth hX v
    rw [map_add, LinearMap.add_apply, (Submodule.mem_orthogonalBilin.mp hw) m hm, hW t ht,
      add_zero]
  refine stdHermForm_separatingLeft h n w fun v => ?_
  rw [← (stdHermForm_isSymm h n).eq v w, hall v, map_zero]

theorem nondegOn_span_of_orthonormal (h : UnitaryFieldData 2 f K) {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : ι → Fin n → K}
    (hF : ∀ i j, stdHermForm h n (F i) (F j) = if i = j then 1 else 0) :
    NondegOn (stdHermForm h n) (Submodule.span K (Set.range F)) := by
  intro v hv hB0
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  have hc : ∀ i, c i = 0 := by
    intro i
    have h1 := hB0 (F i) (Submodule.subset_span ⟨i, rfl⟩)
    rw [map_sum] at h1
    simpa [map_smul, hF] using h1
  simp [hc]

theorem restrictElt_isometry_of_on (h : UnitaryFieldData 2 f K) {W : Submodule K (Fin n → K)}
    (hW : NondegOn (stdHermForm h n) W) {c : Module.End K (Fin n → K)} (hc : ∀ w ∈ W, c w ∈ W)
    (hcB : ∀ v ∈ W, ∀ w ∈ W, stdHermForm h n (c v) (c w) = stdHermForm h n v w)
    (v w : Fin n → K) :
    stdHermForm h n (restrictElt hW c hc v) (restrictElt hW c hc w) = stdHermForm h n v w := by
  set B := stdHermForm h n with hB
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth hW v
  obtain ⟨m', hm', z', hz', rfl⟩ := exists_add_orth hW w
  have hWo : ∀ a ∈ W, ∀ b ∈ W.orthogonalBilin B, B a b = 0 := fun a ha b hb =>
    (Submodule.mem_orthogonalBilin.mp hb) a ha
  have hoW : ∀ a ∈ W, ∀ b ∈ W.orthogonalBilin B, B b a = 0 := fun a ha b hb => by
    rw [← (stdHermForm_isSymm h n).eq a b, hWo a ha b hb, map_zero]
  simp only [map_add, LinearMap.add_apply, restrictElt_apply_of_mem hW hc hm,
    restrictElt_apply_of_mem hW hc hm', restrictElt_apply_of_mem_orth hW hc hz,
    restrictElt_apply_of_mem_orth hW hc hz']
  rw [hWo _ (hc m hm) z' hz', hoW _ (hc m' hm') z hz, hWo m hm z' hz', hoW m' hm' z hz,
    hcB m hm m' hm']

theorem triv_orth_pieceSpan (h : UnitaryFieldData 2 f K) (hE : MaxElemAb p E)
    {S : Finset ↥(unitarySU 2 f K n)} (hS : IsPieceSet h E S)
    (hterm : ∀ c ∈ E, (∀ v ∈ pieceSpan S, lin c v = v) → c = 1) {a : ↥(unitarySU 2 f K n)}
    (ha : a ∈ E) : ∀ w ∈ (pieceSpan S).orthogonalBilin (stdHermForm h n), lin a w = w := by
  set B := stdHermForm h n with hB
  have hp1 : 1 ≤ p := hE.prime.one_lt.le
  have hX : NondegOn B (pieceSpan S) := (hS.nondegOn_card hE).1
  have hW := nondegOn_orth h hX
  have hXE : ∀ b ∈ E, ∀ v ∈ pieceSpan S, lin b v ∈ pieceSpan S := by
    intro b hb v hv
    have hle : pieceSpan S ≤ (pieceSpan S).comap (lin b) := by
      refine iSup₂_le fun y hy u hu => ?_
      exact (le_iSup₂ (f := fun y (_ : y ∈ S) => rng y) y hy) (rng_inv hE (hS.mem y hy) hb u hu)
    exact hle hv
  have hWE : ∀ b ∈ E, ∀ w ∈ (pieceSpan S).orthogonalBilin B, lin b w ∈
      (pieceSpan S).orthogonalBilin B := fun b hb w hw =>
    orth_invariantH (isometry_lin h b) (hE.lin_pow hb) hp1 (hXE b hb) hw
  obtain ⟨g, hgE, hgW, hgW'⟩ := exists_mem_restrict h hE hW hWE ha
  have hg1 : g = 1 := by
    refine hterm g hgE fun v hv => hgW' v ?_
    refine Submodule.mem_orthogonalBilin.mpr fun w hw => ?_
    rw [← (stdHermForm_isSymm h n).eq v w, (Submodule.mem_orthogonalBilin.mp hw) v hv, map_zero]
  intro w hw
  rw [← hgW w hw, hg1, lin_one]
  rfl

theorem finrank_orth_pieceSpan_lt (h : UnitaryFieldData 2 f K) (hE : MaxElemAb p E)
    {S : Finset ↥(unitarySU 2 f K n)} (hS : IsPieceSet h E S)
    (hterm : ∀ c ∈ E, (∀ v ∈ pieceSpan S, lin c v = v) → c = 1) {y₀ : ↥(unitarySU 2 f K n)}
    (hy₀ : y₀ ∈ S) :
    finrank K ((pieceSpan S).orthogonalBilin (stdHermForm h n)) < finrank K (rng y₀) := by
  classical
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  set B := stdHermForm h n with hB
  have hBs : B.IsSymm := stdHermForm_isSymm h n
  have hp := hE.prime
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hy₀E : y₀ ∈ E := hS.mem y₀ hy₀
  set X := pieceSpan S with hXdef
  set W := X.orthogonalBilin B with hWdef
  set U₀ := rng y₀ with hU₀
  have hX : NondegOn B X := (hS.nondegOn_card hE).1
  have hW : NondegOn B W := nondegOn_orth h hX
  have hU₀nd : NondegOn B U₀ := nondegOn_rng hE hy₀E
  have hmpos : 0 < finrank K U₀ := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact rng_ne_bot (hS.ne_one y₀ hy₀)
  by_contra hlt
  push Not at hlt
  have hsep : ∀ {U : Submodule K (Fin n → K)}, NondegOn B U →
      (B.domRestrict₁₂ U U).SeparatingLeft := by
    intro U hU u hu
    refine Subtype.ext (hU u u.2 fun w hw => ?_)
    rw [← hBs.eq (u : Fin n → K) w]
    rw [show B u w = 0 from hu ⟨w, hw⟩, map_zero]
  obtain ⟨e₀, he₀⟩ := h.exists_orthonormal_basis (hBs.domRestrict U₀) (hsep hU₀nd)
  obtain ⟨e₁, he₁⟩ := h.exists_orthonormal_basis (hBs.domRestrict W) (hsep hW)
  set F : Fin (finrank K U₀) → Fin n → K := fun i => (e₀ i : Fin n → K) with hF
  set F' : Fin (finrank K U₀) → Fin n → K := fun i => (e₁ (Fin.castLE hlt i) : Fin n → K)
    with hF'
  have hFo : ∀ i j, B (F i) (F j) = if i = j then 1 else 0 := by
    intro i j
    have h1 := he₀ i j
    simpa only [LinearMap.domRestrict₁₂_apply] using h1
  have hF'o : ∀ i j, B (F' i) (F' j) = if i = j then 1 else 0 := by
    intro i j
    have h1 := he₁ (Fin.castLE hlt i) (Fin.castLE hlt j)
    simp only [LinearMap.domRestrict₁₂_apply] at h1
    rw [hF', h1]
    simp [Fin.castLE_inj]
  have hspanF : Submodule.span K (Set.range F) = U₀ := by
    have h1 : Set.range F = U₀.subtype '' Set.range e₀ := by
      rw [← Set.range_comp]
      rfl
    rw [h1, ← Submodule.map_span, e₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  set W' := Submodule.span K (Set.range F') with hW'
  have hW'W : W' ≤ W := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (e₁ _).2)
  have hW'nd : NondegOn B W' := nondegOn_span_of_orthonormal h hF'o
  have hFnd : NondegOn B (Submodule.span K (Set.range F)) := by rw [hspanF]; exact hU₀nd
  have hG : ∀ i j, B (F i) (F j) = B (F' i) (F' j) := fun i j => by rw [hFo, hF'o]
  have hG' : ∀ i j, B (F' i) (F' j) = B (F i) (F j) := fun i j => (hG i j).symm
  obtain ⟨θ, hθ⟩ := exists_linearMap_of_gram hG hW'nd
  obtain ⟨θ', hθ'⟩ := exists_linearMap_of_gram hG' hFnd
  have hθθ' : ∀ v ∈ U₀, θ' (θ v) = v := by
    intro v hv
    rw [← hspanF] at hv
    have h1 : Set.EqOn (θ' ∘ₗ θ) (LinearMap.id : Module.End K (Fin n → K)) (Set.range F) := by
      rintro _ ⟨i, rfl⟩
      simp [hθ, hθ']
    exact LinearMap.eqOn_span' h1 hv
  have hθ'θ : ∀ v ∈ W', θ (θ' v) = v := by
    intro v hv
    have h1 : Set.EqOn (θ ∘ₗ θ') (LinearMap.id : Module.End K (Fin n → K)) (Set.range F') := by
      rintro _ ⟨i, rfl⟩
      simp [hθ, hθ']
    exact LinearMap.eqOn_span' h1 hv
  have hθ'mem : ∀ v ∈ W', θ' v ∈ U₀ := fun v hv => by
    rw [← hspanF]
    exact gram_map_mem hθ' hv
  have hθmem : ∀ v ∈ U₀, θ v ∈ W' := fun v hv => gram_map_mem hθ (by rw [hspanF]; exact hv)
  set c : Module.End K (Fin n → K) := θ ∘ₗ lin y₀ ∘ₗ θ' with hc
  have hcW' : ∀ w ∈ W', c w ∈ W' := fun w hw =>
    hθmem _ (rng_inv hE hy₀E hy₀E _ (hθ'mem w hw))
  have hcB : ∀ v ∈ W', ∀ w ∈ W', B (c v) (c w) = B v w := by
    intro v hv w hw
    simp only [hc, LinearMap.comp_apply]
    have hv' : lin y₀ (θ' v) ∈ Submodule.span K (Set.range F) := by
      rw [hspanF]; exact rng_inv hE hy₀E hy₀E _ (hθ'mem v hv)
    have hw' : lin y₀ (θ' w) ∈ Submodule.span K (Set.range F) := by
      rw [hspanF]; exact rng_inv hE hy₀E hy₀E _ (hθ'mem w hw)
    rw [gram_map_eq hG hθ hv' hw', isometry_lin h y₀, gram_map_eq hG' hθ' hv hw]
  have hcpow : ∀ k : ℕ, ∀ w ∈ W', (c ^ k) w = θ (lin (y₀ ^ k) (θ' w)) := by
    intro k
    induction k with
    | zero =>
      intro w hw
      rw [pow_zero, pow_zero, lin_one, Module.End.one_apply, Module.End.one_apply, hθ'θ w hw]
    | succ k ih =>
      intro w hw
      have hk : lin (y₀ ^ k) (θ' w) ∈ U₀ := pow_mem_of_inv (rng_inv hE hy₀E hy₀E) k _ (hθ'mem w hw)
      rw [pow_succ', Module.End.mul_apply, ih w hw, hc, LinearMap.comp_apply, LinearMap.comp_apply,
        hθθ' _ hk, pow_succ', lin_mul, Module.End.mul_apply]
  obtain ⟨z, hz⟩ : ∃ z, z = restrictElt hW'nd c hcW' := ⟨_, rfl⟩
  have hzp : z ^ p = 1 := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨m, hm, t, ht, rfl⟩ := exists_add_orth hW'nd v
    rw [hz, restrictElt_pow_apply hW'nd hcW' p hm ht, hcpow p m hm, hE.pow y₀ hy₀E, lin_one,
      Module.End.one_apply, hθ'θ m hm, Module.End.one_apply]
  have hziso : ∀ v w, B (z v) (z w) = B v w := by
    rw [hz]
    exact restrictElt_isometry_of_on h hW'nd hcW' hcB
  obtain ⟨g, hg⟩ := exists_su_of_isometry h hp hE.not_dvd hziso hzp
  have hgp : g ^ p = 1 := lin_injective (by rw [SUTB.lin_pow, hg, hzp, lin_one])
  have htrivW := fun a ha => triv_orth_pieceSpan h hE hS hterm (a := a) ha
  have hcomm : ∀ a ∈ E, g * a = a * g := by
    intro a ha
    have haW' : ∀ w ∈ W', lin a w ∈ W' := fun w hw => by rw [htrivW a ha w (hW'W hw)]; exact hw
    have haW'' : ∀ t ∈ W'.orthogonalBilin B, lin a t ∈ W'.orthogonalBilin B := fun t ht =>
      orth_invariantH (isometry_lin h a) (hE.lin_pow ha) hp1 haW' ht
    have hac : ∀ w ∈ W', lin a (c w) = c (lin a w) := fun w hw => by
      rw [htrivW a ha _ (hW'W (hcW' w hw)), htrivW a ha w (hW'W hw)]
    have h1 := restrictElt_comm hW'nd hcW' haW' haW'' hac
    apply lin_injective
    rw [lin_mul, lin_mul, hg, hz]
    exact h1.symm
  have hgE : g ∈ E := hE.max g hgp hcomm
  have hg1 : g = 1 := by
    refine hterm g hgE fun v hv => ?_
    have hvo : v ∈ W'.orthogonalBilin B := by
      refine Submodule.mem_orthogonalBilin.mpr fun w hw => ?_
      rw [← hBs.eq v w, (Submodule.mem_orthogonalBilin.mp (hW'W hw)) v hv, map_zero]
    rw [hg, hz]
    exact restrictElt_apply_of_mem_orth hW'nd hcW' hvo
  set i₀ : Fin (finrank K U₀) := ⟨0, hmpos⟩ with hi₀
  have hF'W' : F' i₀ ∈ W' := Submodule.subset_span ⟨i₀, rfl⟩
  have hz1 : z (F' i₀) = F' i₀ := by rw [← hg, hg1, lin_one]; rfl
  have hz2 : z (F' i₀) = θ (lin y₀ (F i₀)) := by
    rw [hz, restrictElt_apply_of_mem hW'nd hcW' hF'W', hc, LinearMap.comp_apply,
      LinearMap.comp_apply, hθ' i₀]
  rw [hz2] at hz1
  have hFU : F i₀ ∈ U₀ := (e₀ i₀).2
  have hyF : lin y₀ (F i₀) = F i₀ := by
    have h1 := congrArg θ' hz1
    rwa [hθθ' _ (rng_inv hE hy₀E hy₀E _ hFU), hθ' i₀] at h1
  have hF0 : F i₀ = 0 := eq_zero_of_mem_rng h hE hy₀E hFU hyF
  have h1 := hFo i₀ i₀
  rw [hF0, map_zero, ite_eq_left rfl] at h1
  exact zero_ne_one h1

end OrdPNsU

end CFSG.StandardType

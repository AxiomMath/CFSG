module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOmegaBigRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOmegaBigSpan

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Quasithin.JonesParshall

theorem w183_exists_ne_zero_one {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (ha : 2 ≤ a) : ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
  classical
  by_contra h
  have h' : ∀ l : K, l ≠ 0 → l = 1 := fun l hl => by_contra fun hne => h ⟨l, hl, hne⟩
  have : Fintype K := Fintype.ofFinite K
  have hle : Fintype.card K ≤ 2 := (Finset.card_le_card (s := Finset.univ)
    (t := ({0, 1} : Finset K)) fun x _ => by by_cases hx : x = 0 <;> simp [hx, h' x]).trans
    Finset.card_le_two
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) ha
  rw [← Nat.card_eq_fintype_card, hK] at hle
  omega

theorem w183_root_functional {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (P P' : HypPair Q) (hP : P.Orth P') {l : K} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    {f : ↥(elementaryGroup Q) → V} (hf : f ∈ Z1A (w183ElemAct Q))
    (hd : ∀ c : K, c ≠ 0 →
      ∃ d : ↥(elementaryGroup Q), W183Torus P c (d : V ≃ₗ[K] V) ∧ f d = 0) :
    ∃ v ∈ P.perp, (∀ u ∈ P.perp, f (w183El Q P.e u) = polar Q u v • P.e) ∧
      ∀ u ∈ P.perp, f (w183El Q P.f u) = polar Q u v • P.f := by
  obtain ⟨a, haT, ha, ha'⟩ := w183_root_value P hl0 hl1 hf fun c hc => by
    obtain ⟨d, ⟨hdx, -, hdU⟩, hd0⟩ := hd c hc
    exact ⟨d, hdx, hdU, hd0⟩
  let Ps : HypPair Q := ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩
  have hperp : ∀ x, x ∈ Ps.perp ↔ x ∈ P.perp := fun x => by
    simp only [HypPair.mem_perp]
    exact and_comm
  obtain ⟨b, hbT, hb, hb'⟩ := w183_root_value Ps hl0 hl1 hf fun c hc => by
    obtain ⟨d, ⟨-, hdy, hdU⟩, hd0⟩ := hd c⁻¹ (inv_ne_zero hc)
    exact ⟨d, by rw [inv_inv] at hdy; exact hdy, fun w hw => hdU w ((hperp w).1 hw), hd0⟩
  have hb2 : ∀ u v, u ∈ P.perp → v ∈ P.perp → b (u + v) = b u + b v :=
    fun u v hu hv => hb u v ((hperp u).2 hu) ((hperp v).2 hv)
  have hb3 : ∀ (t : K) u, u ∈ P.perp → b (t • u) = t * b u :=
    fun t u hu => hb' t u ((hperp u).2 hu)
  have hz : ∀ (g : V → K), (∀ u v, u ∈ P.perp → v ∈ P.perp → g (u + v) = g u + g v) →
      g 0 = 0 := fun g hg => by
    have := hg 0 0 P.perp.zero_mem P.perp.zero_mem
    simpa using this
  have hsing : ∀ u ∈ P.perp, Q u = 0 → a u = b u := by
    intro u hu hQu
    by_cases hu0 : u = 0
    · rw [hu0, hz a ha, hz b hb2]
    · exact w183_root_opposite hf P hu hQu hu0 (haT u hu) (hbT u ((hperp u).2 hu))
  have hab := w183_eq_of_singular P P' hP ha ha' hb2 hb3 hsing
  obtain ⟨v, hv, hvu⟩ := w183_dual_vector hQ P ha ha'
  refine ⟨v, hv, fun u hu => ?_, fun u hu => ?_⟩
  · rw [haT u hu, hvu u hu]
  · have := hbT u ((hperp u).2 hu)
    change f (w183El Q P.f u) = b u • P.f at this
    rw [this, ← hab u hu, hvu u hu]

theorem w183_h1_abstract {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (P P' : HypPair Q) (hP : P.Orth P') {a : ℕ} (hK : Nat.card K = 2 ^ a) (ha : 2 ≤ a) :
    Z1A (w183ElemAct Q) = B1A (w183ElemAct Q) := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ a := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hF
  obtain ⟨l, hl0, hl1⟩ := w183_exists_ne_zero_one hK ha
  have hv : P'.e + P'.f ∈ P.perp := HypPair.mem_perp.mpr
    ⟨by rw [polar_add_right, hP.ee, hP.ef, add_zero],
      by rw [polar_add_right, hP.fe, hP.ff, add_zero]⟩
  have hQv : Q (P'.e + P'.f) ≠ 0 := by
    rw [QuadraticMap.map_add Q, P'.Q_e, P'.Q_f, P'.polar_ef]
    simp
  obtain ⟨φ, hφ⟩ := w183_torus_hom P fun c hc => w183_torus_exists P hv hQv hc
  refine le_antisymm (fun f hf => ?_) (B1A_le_Z1A _)
  obtain ⟨m, hm⟩ := w183_normalize_torus hK (by omega) (w183ElemAct Q)
    (fun m => w183_self_add_eq_zero (K := K) m) φ hf
  have hf₁ : f - coboundaryA (w183ElemAct Q) m ∈ Z1A (w183ElemAct Q) :=
    sub_mem hf (B1A_le_Z1A _ ⟨m, rfl⟩)
  obtain ⟨v, hvU, hT, hR⟩ := w183_root_functional hQ P P' hP hl0 hl1 hf₁ fun c hc =>
    ⟨φ (Units.mk0 c hc), by simpa using hφ (Units.mk0 c hc), by
      simp [coboundaryA_apply, hm (Units.mk0 c hc)]⟩
  have hf₂ : f - coboundaryA (w183ElemAct Q) m - coboundaryA (w183ElemAct Q) v ∈
      Z1A (w183ElemAct Q) := sub_mem hf₁ (B1A_le_Z1A _ ⟨v, rfl⟩)
  have hroot : ∀ c u : V, Q c = 0 → polar Q c u = 0 → polar Q c v = 0 →
      eichler Q c u v = v - polar Q v u • c := by
    intro c u hc hcu hcv
    rw [eichler_apply hc hcu, polar_comm Q v c, hcv]
    simp
  have hv0 : ∀ u : V, ∀ x : V, polar Q u v • x + polar Q v u • x = 0 := fun u x => by
    rw [← add_smul, polar_comm Q v u, w183_self_add_eq_zero (K := K)]
    exact zero_smul K _
  have hz := w183_zero_of_roots hQ P hf₂ (fun u hu => ?_) (fun u hu => ?_)
  · refine ⟨v + m, funext fun g => ?_⟩
    have := hz g
    simp only [Pi.sub_apply, coboundaryA_apply, sub_eq_zero] at this
    have h3 : f g = (w183ElemAct Q g v - v) + (w183ElemAct Q g m - m) := by
      rw [← this]; abel
    simp only [coboundaryA_apply, map_add]
    rw [h3]
    abel
  · have h1 := hT u hu
    have h2 : coboundaryA (w183ElemAct Q) v (w183El Q P.e u) = -(polar Q v u • P.e) := by
      rw [coboundaryA_apply, w183ElemAct_apply, w183El_coe,
        hroot P.e u P.Q_e (HypPair.mem_perp.mp hu).1 (HypPair.mem_perp.mp hvU).1]
      abel
    rw [Pi.sub_apply, h1, h2, sub_neg_eq_add]
    exact hv0 u P.e
  · have h1 := hR u hu
    have h2 : coboundaryA (w183ElemAct Q) v (w183El Q P.f u) = -(polar Q v u • P.f) := by
      rw [coboundaryA_apply, w183ElemAct_apply, w183El_coe,
        hroot P.f u P.Q_f (HypPair.mem_perp.mp hu).2 (HypPair.mem_perp.mp hvU).2]
      abel
    rw [Pi.sub_apply, h1, h2, sub_neg_eq_add]
    exact hv0 u P.f

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

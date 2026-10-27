module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldFour

public section

namespace CFSG.StandardType

namespace LIDTwDF

open Module QuadraticMap OrthBstarOdd OrthRestOdd CFSG.RankThree.PartOne.LIT

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_inv_singular {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f)
    {σ : K ≃+* K} (hσp : σ ^ p = 1) (hσ1 : σ ≠ 1) :
    ∀ (a : ℕ) (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X],
      finrank K X = 2 * a → ∀ (Q : QuadraticForm K X), (polarBilin Q).Nondegenerate →
      ∀ (E : Subgroup (X ≃ₗ[K] X)), (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ p = 1) →
      (∀ g ∈ E, ∀ v, Q (g v) = Q v) → p ^ (a - 1) ≤ Nat.card E →
      ∀ (S : SemiSim Q p σ), (∀ g ∈ E, ∀ v, S.G (g v) = g (S.G v)) →
      ∀ Y : Submodule K X, Y ≠ ⊥ → (∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y) → (∀ y ∈ Y, Q y = 0) →
      ∃ Y' : Submodule K X, Y' ≠ ⊥ ∧ (∀ g ∈ E, ∀ y ∈ Y', g y ∈ Y') ∧
        (∀ y ∈ Y', S.G y ∈ Y') ∧ ∀ y ∈ Y', Q y = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro X _ _ _ hX Q hQ E hcomm hpow hQE hE S hSE Y hY hYinv hYsing
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  have : Fact p.Prime := ⟨hp⟩
  have : Finite X := Module.finite_of_finite K
  have : Finite (X ≃ₗ[K] X) := Finite.of_injective (fun e : X ≃ₗ[K] X => (e : X → X))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hEiso : IsoGroup (polarBilin Q) p E := isoGroup_of hQ hcomm hpow hQE
  rcases card_le_or_exists_fix hEiso hp hpK hY hYinv with hle | ⟨g, hgE, hg1, Y', hY'0, hY'Y,
    hY'inv, hgY'⟩
  ·
    have ha : a ≤ 2 := by
      by_contra h
      have h1 : p ^ 2 ≤ p ^ (a - 1) := Nat.pow_le_pow_right hp.pos (by omega)
      have h2 : p < p ^ 2 := by
        rw [_root_.sq]
        exact lt_mul_self hp.one_lt
      omega
    obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
    · exfalso
      rw [mul_zero] at hX
      have : Subsingleton X := Module.finrank_zero_iff.mp hX
      exact hy0 (Subsingleton.elim _ _)
    ·
      refine ⟨Y, hY, hYinv, fun y' hy' => ?_, hYsing⟩
      by_cases hy'0 : y' = 0
      · rw [hy'0, map_zero]
        exact Y.zero_mem
      · obtain ⟨c, hc⟩ := semiSim_stable_of_plane hp hp2 S (Z := ⊤)
          (by rw [finrank_top, hX]) (fun z _ hz => hQ.1 z fun v => hz v Submodule.mem_top)
          (fun _ _ => Submodule.mem_top) Submodule.mem_top hy'0 (hYsing y' hy')
        rw [hc]
        exact Y.smul_mem c hy'
    ·
      have hX4 : finrank K X = 4 := hX
      have hEp : Nat.card E = p := le_antisymm hle (by simpa using hE)
      obtain ⟨s, hsE, hs1⟩ : ∃ s ∈ E, s ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have h0 : E = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
        rw [h0, Subgroup.card_bot] at hEp
        exact hp.one_lt.ne hEp
      have hord : orderOf s = p := orderOf_eq_prime (hpow s hsE) hs1
      have hEz : Subgroup.zpowers s = E := Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr hsE) (by rw [Nat.card_zpowers, hord, hEp])
      have hEs : ∀ g ∈ E, ∃ k : ℕ, s ^ k = g := by
        intro g hg
        rw [← hEz] at hg
        exact (Submonoid.mem_powers_iff _ _).mp
          ((isOfFinOrder_of_finite s).mem_powers_iff_mem_zpowers.mpr hg)
      by_cases hfix0 : fixedSpace s = ⊥
      ·
        refine exists_inv_singular_four hp hp2 hK1 hf hf1 hσp hσ1 hX4 hQ hsE hEs hpow hQE
          (fun v hv hsv => hv ?_) S (hSE s hsE) hY hYinv hYsing
        have : v ∈ fixedSpace s := mem_fixedSpace.mpr hsv
        rw [hfix0] at this
        exact (Submodule.mem_bot K).mp this
      ·
        have hc := hEiso.isCompl hpK hsE
        have hsum := Submodule.finrank_add_eq_of_isCompl hc
        have hEU := hEiso.resFix hpK hsE
        have hEW := hEiso.resComm hpK hsE
        obtain ⟨a', ha'⟩ := hEU.even_finrank
        obtain ⟨b', hb'⟩ := hEW.even_finrank
        have hW0 : finrank K (commSpace s) ≠ 0 := by
          rw [Ne, Submodule.finrank_eq_zero]
          exact commSpace_ne_bot hs1
        have hU0 : finrank K (fixedSpace s) ≠ 0 := by
          rw [Ne, Submodule.finrank_eq_zero]
          exact hfix0
        have hU2 : finrank K (fixedSpace s) = 2 := by omega
        have hW2 : finrank K (commSpace s) = 2 := by omega
        have hWan : ∀ w ∈ commSpace s, w ≠ 0 → Q w ≠ 0 := by
          obtain ⟨-, -, -, han⟩ := plane_facts hp hp2 hK1 (hQE s hsE) (hpow s hsE) hW2
            (commSpace_nondeg hQ hpK (hQE s hsE) (hpow s hsE))
            (fun v hv => map_mem_commSpace rfl hv) (fpf_commSpace hpK (hpow s hsE))
          exact han
        have hYfix : ∀ y ∈ Y, s y = y := by
          intro y hy
          have hmem : y ∈ fixedSpace s ⊔ commSpace s := by rw [hc.sup_eq_top]; trivial
          obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hmem
          have hsy : s (u + w) - (u + w) ∈ Y := Y.sub_mem (hYinv s hsE _ hy) hy
          have hz : s (u + w) - (u + w) = s w - w := by
            rw [map_add, mem_fixedSpace.mp hu]
            abel
          have hwc : s w - w ∈ commSpace s :=
            (commSpace s).sub_mem (map_mem_commSpace rfl hw) hw
          have hsw : s w = w := by
            by_contra hne
            exact hWan _ hwc (sub_ne_zero.mpr hne) (hYsing _ (hz ▸ hsy))
          have hw0 : w = 0 := by
            by_contra hw0
            exact fpf_commSpace hpK (hpow s hsE) w hw hw0 hsw
          rw [hw0, add_zero]
          exact mem_fixedSpace.mp hu
        have hGfix : ∀ v ∈ fixedSpace s, S.G v ∈ fixedSpace s := fun v hv => by
          rw [mem_fixedSpace] at hv ⊢
          rw [← hSE s hsE v, hv]
        refine ⟨Y, hY, hYinv, fun y' hy' => ?_, hYsing⟩
        by_cases hy'0 : y' = 0
        · rw [hy'0, map_zero]
          exact Y.zero_mem
        · have hy'U : y' ∈ fixedSpace s := mem_fixedSpace.mpr (hYfix y' hy')
          obtain ⟨c, hc'⟩ := semiSim_stable_of_plane hp hp2 S (Z := fixedSpace s) hU2
            (fixedSpace_nondeg hQ hpK (hQE s hsE) (hpow s hsE)) hGfix hy'U hy'0 (hYsing y' hy')
          rw [hc']
          exact Y.smul_mem c hy'
  ·
    have hc := hEiso.isCompl hpK hgE
    have hEU := hEiso.resFix hpK hgE
    have hEW := hEiso.resComm hpK hgE
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    obtain ⟨a', ha'⟩ := hEU.even_finrank
    obtain ⟨b', hb'⟩ := hEW.even_finrank
    have hW0 : finrank K (commSpace g) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact commSpace_ne_bot hg1
    have hY'U : Y' ≤ fixedSpace g := fun y hy => mem_fixedSpace.mpr (hgY' y hy)
    set Y'' : Submodule K (fixedSpace g) := Y'.comap (fixedSpace g).subtype with hY''
    have hY''0 : Y'' ≠ ⊥ := by
      intro h
      obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY'0
      have hmem : (⟨y, hY'U hyY⟩ : fixedSpace g) ∈ Y'' := hyY
      rw [h, Submodule.mem_bot] at hmem
      exact hy0 (congrArg Subtype.val hmem)
    have hU0 : finrank K (fixedSpace g) ≠ 0 := by
      intro h
      apply hY''0
      have : Subsingleton (fixedSpace g) := Module.finrank_zero_iff.mp h
      exact Subsingleton.elim _ _
    have hEU' : ∀ e ∈ E, ∀ u ∈ fixedSpace g, e u ∈ fixedSpace g := hEiso.fix_inv hgE
    have hEW' : ∀ e ∈ E, ∀ w ∈ commSpace g, e w ∈ commSpace g := hEiso.comm_inv hgE
    have hcE := card_le_mul_res (E := E) hc hEU' hEW'
    have hEWc := hEW.card_le hp hpK
    rw [hb', show (b' + b') / 2 = b' by omega] at hEWc
    have hab : a = a' + b' := by omega
    have hpb : 0 < p ^ b' := pow_pos hp.pos _
    have hEUcard : p ^ (a' - 1) ≤ Nat.card (resHom E (fixedSpace g) hEU').range := by
      refine Nat.le_of_mul_le_mul_right ?_ hpb
      calc p ^ (a' - 1) * p ^ b' = p ^ (a - 1) := by
            rw [← pow_add]
            congr 1
            omega
        _ ≤ Nat.card E := hE
        _ ≤ _ := hcE
        _ ≤ _ := Nat.mul_le_mul_left _ hEWc
    have hfix : ∀ v ∈ fixedSpace g, S.G v ∈ fixedSpace g := fun v hv => by
      rw [mem_fixedSpace] at hv ⊢
      rw [← hSE g hgE v, hv]
    obtain ⟨Y₁, hY₁0, hY₁E, hY₁G, hY₁Q⟩ := ih a' (by omega) (fixedSpace g) (by omega)
      (Q.comp (fixedSpace g).subtype)
      (nondeg_comp (fixedSpace_nondeg hQ hpK (hQE g hgE) (hpow g hgE)))
      (resHom E (fixedSpace g) hEU').range hEU.comm hEU.pow
      (by rintro _ ⟨t, rfl⟩ v; exact hQE t t.2 v) hEUcard (S.restrict (fixedSpace g) hfix)
      (by
        rintro _ ⟨e, rfl⟩ v
        exact Subtype.ext (hSE e e.2 v))
      Y'' hY''0 (by rintro _ ⟨e, rfl⟩ z hz; exact hY'inv e e.2 z hz)
      (fun z hz => hYsing z (hY'Y hz))
    refine ⟨Y₁.map (fixedSpace g).subtype, ?_, ?_, ?_, ?_⟩
    · intro h
      apply hY₁0
      rw [eq_bot_iff]
      intro y hy
      have hmem : (y : X) ∈ Y₁.map (fixedSpace g).subtype := ⟨y, hy, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      rw [Submodule.mem_bot]
      exact Subtype.ext hmem
    · rintro e he _ ⟨y, hy, rfl⟩
      exact ⟨resHom E (fixedSpace g) hEU' ⟨e, he⟩ y, hY₁E _ ⟨⟨e, he⟩, rfl⟩ y hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨(S.restrict (fixedSpace g) hfix).G y, hY₁G y hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hY₁Q y hy

end LIDTwDF

end CFSG.StandardType

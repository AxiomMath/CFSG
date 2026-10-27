module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2s08ck_gen_diff {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ℓ : ℕ} (s : Fin ℓ → (V ≃ₗ[ZMod 3] V)) (H : Submodule (ZMod 3) V)
    (hsH : ∀ i, ∃ h ∈ H, h ≠ 0 ∧ ∀ v, s i v - v ∈ Submodule.span (ZMod 3) {h}) :
    ∀ g ∈ Subgroup.closure (Set.range s), ∀ v, g v - v ∈ H := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      obtain ⟨h, hhH, _, hhspan⟩ := hsH i
      intro v
      exact (Submodule.span_singleton_le_iff_mem h H).mpr hhH (hhspan v)
  | one => intro v; simp
  | mul a b _ _ iha ihb =>
      intro v
      have h : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
        rw [LinearEquiv.mul_apply]; abel
      rw [h]
      exact H.add_mem (iha (b v)) (ihb v)
  | inv a _ iha =>
      intro v
      have h := iha (a⁻¹ v)
      have ha : a (a⁻¹ v) = v := LinearEquiv.apply_symm_apply a v
      rw [ha] at h
      rw [show a⁻¹ v - v = -(v - a⁻¹ v) by abel]
      exact H.neg_mem h

private lemma ggQ2s08ck_inv_pres {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (g : V ≃ₗ[ZMod 3] V) (hg : ∀ v, g v - v ∈ H) :
    ∀ u ∈ H, g⁻¹ u ∈ H := by
  intro u hu
  have h1 : u - g⁻¹ u ∈ H := by
    have h := hg (g⁻¹ u)
    simpa using h
  have h2 : g⁻¹ u = u - (u - g⁻¹ u) := by abel
  rw [h2]
  exact H.sub_mem hu h1

private lemma ggQ2s08ck_inv_fix {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (g : V ≃ₗ[ZMod 3] V) (hg : ∀ u ∈ H, g u = u) :
    ∀ u ∈ H, g⁻¹ u = u := by
  intro u hu
  have h1 : g (g⁻¹ u) = g u := by rw [hg u hu]; simp
  exact g.injective h1

private lemma ggQ2s08ck_gen_fix {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (s k : V ≃ₗ[ZMod 3] V) (h : V) (hhH : h ∈ H) (hhne : h ≠ 0)
    (hsdiff : ∀ v, s v - v ∈ Submodule.span (ZMod 3) {h})
    (hkfix : ∀ u ∈ H, k u = u) (hkd : ∀ v, k v - v ∈ H)
    (hsinvpres : ∀ u ∈ H, s⁻¹ u ∈ H) (hsA : s ∈ A) (hkA : k ∈ A)
    (hntA : ∀ a ∈ A, ¬ (Module.finrank (ZMod 3)
      (LinearMap.range (a.toLinearMap - LinearMap.id)) = 1 ∧
      ∀ w, a (a w - w) = a w - w)) :
    ∀ v, s (k v - v) = k v - v := by
  classical
  have hspan_le_H : Submodule.span (ZMod 3) {h} ≤ H :=
    (Submodule.span_singleton_le_iff_mem h H).mpr hhH
  have hkinv : ∀ v, k⁻¹ v = v - (k v - v) := by
    intro v
    have h1 : k (v - (k v - v)) = v := by
      rw [map_sub, hkfix _ (hkd v)]
      abel
    have h2 : k (k⁻¹ v) = v := by simp
    exact (k.injective (h1.trans h2.symm)).symm
  have hTapply : ∀ w, (s * k * s⁻¹) w = w + s (k w - w) := by
    intro w
    let z : V := s⁻¹ w
    have hz : s z = w := by simp [z]
    have hdz : s z - z ∈ H := hspan_le_H (hsdiff z)
    have hwz : w = z + (s z - z) := by rw [hz]; abel
    have hkw : k w = k z + (s z - z) := by
      rw [hwz, map_add, hkfix _ hdz]
    have hkz : k z = z + (k w - w) := by
      rw [hkw, hwz]
      abel
    calc (s * k * s⁻¹) w = s (k (s⁻¹ w)) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = s (k z) := rfl
      _ = s (z + (k w - w)) := by rw [hkz]
      _ = s z + s (k w - w) := by rw [map_add]
      _ = w + s (k w - w) := by rw [hz]
  have hTfix : ∀ u ∈ H, (s * k * s⁻¹) u = u := by
    intro u hu
    calc (s * k * s⁻¹) u = s (k (s⁻¹ u)) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = s (s⁻¹ u) := by rw [hkfix _ (hsinvpres u hu)]
      _ = u := by simp
  have hkinvH : ∀ u ∈ H, k⁻¹ u = u := ggQ2s08ck_inv_fix H k hkfix
  have hmfixH : ∀ u ∈ H, (s * k * s⁻¹ * k⁻¹) u = u := by
    intro u hu
    calc (s * k * s⁻¹ * k⁻¹) u = (s * k * s⁻¹) (k⁻¹ u) := by
          rw [LinearEquiv.mul_apply]
      _ = (s * k * s⁻¹) u := by rw [hkinvH u hu]
      _ = u := hTfix u hu
  have hmap : ∀ v, (s * k * s⁻¹ * k⁻¹) v = v + (s (k v - v) - (k v - v)) := by
    intro v
    have hcd : k v - v ∈ H := hkd v
    calc (s * k * s⁻¹ * k⁻¹) v = (s * k * s⁻¹) (k⁻¹ v) := by
          rw [LinearEquiv.mul_apply]
      _ = (s * k * s⁻¹) (v - (k v - v)) := by rw [hkinv v]
      _ = (s * k * s⁻¹) v - (s * k * s⁻¹) (k v - v) := by rw [map_sub]
      _ = (v + s (k v - v)) - (k v - v) := by rw [hTapply v, hTfix _ hcd]
      _ = v + (s (k v - v) - (k v - v)) := by abel
  have hmdiff : ∀ v, (s * k * s⁻¹ * k⁻¹) v - v ∈ Submodule.span (ZMod 3) {h} := by
    intro v
    rw [hmap v]
    have hred : v + (s (k v - v) - (k v - v)) - v = s (k v - v) - (k v - v) := by abel
    rw [hred]
    exact hsdiff (k v - v)
  have hm1 : s * k * s⁻¹ * k⁻¹ = 1 := by
    by_contra hne
    have hmA : s * k * s⁻¹ * k⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem hsA hkA) (A.inv_mem hsA)) (A.inv_mem hkA)
    have hrange_le : LinearMap.range ((s * k * s⁻¹ * k⁻¹).toLinearMap - LinearMap.id) ≤
        Submodule.span (ZMod 3) {h} := by
      rintro y ⟨v, rfl⟩
      simpa using hmdiff v
    obtain ⟨v₀, hv₀⟩ : ∃ v, (s * k * s⁻¹ * k⁻¹) v - v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (LinearEquiv.ext fun v => sub_eq_zero.mp (hc v))
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hmdiff v₀)
    have hc0 : c ≠ 0 := by
      intro h0
      exact hv₀ (by rw [← hc, h0, zero_smul])
    have hh_range : h ∈ LinearMap.range ((s * k * s⁻¹ * k⁻¹).toLinearMap - LinearMap.id) := by
      refine ⟨c⁻¹ • v₀, ?_⟩
      have hsmul :
          ((s * k * s⁻¹ * k⁻¹).toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (c⁻¹ • v₀) =
          c⁻¹ • ((s * k * s⁻¹ * k⁻¹) v₀ - v₀) := by
        rw [LinearMap.sub_apply, map_smul, LinearMap.id_apply, smul_sub]
        rfl
      rw [hsmul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hrange_eq : LinearMap.range ((s * k * s⁻¹ * k⁻¹).toLinearMap - LinearMap.id) =
        Submodule.span (ZMod 3) {h} :=
      le_antisymm hrange_le ((Submodule.span_singleton_le_iff_mem h _).mpr hh_range)
    have hfin : Module.finrank (ZMod 3)
        (LinearMap.range ((s * k * s⁻¹ * k⁻¹).toLinearMap - LinearMap.id)) = 1 := by
      rw [hrange_eq]
      exact finrank_span_singleton hhne
    have hmfixmove : ∀ w, (s * k * s⁻¹ * k⁻¹) ((s * k * s⁻¹ * k⁻¹) w - w) =
        (s * k * s⁻¹ * k⁻¹) w - w := by
      intro w
      exact hmfixH _ (hspan_le_H (hmdiff w))
    exact hntA _ hmA ⟨hfin, hmfixmove⟩
  intro v
  have hv : (s * k * s⁻¹ * k⁻¹) v = v := by rw [hm1]; rfl
  rw [hmap v] at hv
  have hzero : s (k v - v) - (k v - v) = 0 :=
    add_left_cancel (show v + (s (k v - v) - (k v - v)) = v + 0 by
      rw [add_zero]; exact hv)
  exact sub_eq_zero.mp hzero

theorem ggQ2s08_bigC_kernel {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ℓ : ℕ}
    {s : Fin ℓ → (V ≃ₗ[ZMod 3] V)} {W R A : Subgroup (V ≃ₗ[ZMod 3] V)} {xv : V}
    {H : Submodule (ZMod 3) V} (hWs : W = Subgroup.closure (Set.range s))
    (hsH : ∀ i, ∃ h ∈ H, h ≠ 0 ∧ ∀ v, s i v - v ∈ Submodule.span (ZMod 3) {h})
    (hWfix : ∀ v : V, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (hxH : xv ∉ H) (hWR : W ≤ R) (hRA : R ≤ A)
    (hnt : ∀ a ∈ A, ¬
      (Module.finrank (ZMod 3) (LinearMap.range (a.toLinearMap - LinearMap.id)) = 1 ∧
      ∀ w, a (a w - w) = a w - w))
    (hpres : ∀ g ∈ R, ∀ u ∈ H, g u ∈ H)
    (hres : ∀ g ∈ R, ∃ w ∈ W, ∀ u ∈ H, g u = w u) :
    ∀ g ∈ R, ∃ c : ZMod 3, g xv = c • xv := by
  classical
  have hWdiff : ∀ g ∈ W, ∀ v, g v - v ∈ H := by
    intro g hg
    rw [hWs] at hg
    exact ggQ2s08ck_gen_diff s H hsH g hg
  have hK1 : ∀ k ∈ R, (∀ u ∈ H, k u = u) → (∀ v, k v - v ∈ H) → k = 1 := by
    intro k hkR hkfix hkd
    have hgenfix : ∀ i, ∀ v, s i (k v - v) = k v - v := by
      intro i
      obtain ⟨h, hhH, hhne, hhspan⟩ := hsH i
      have hsiW : s i ∈ W := by rw [hWs]; exact Subgroup.subset_closure ⟨i, rfl⟩
      have hsiA : s i ∈ A := hRA (hWR hsiW)
      have hkA : k ∈ A := hRA hkR
      have hsinvpres : ∀ u ∈ H, (s i)⁻¹ u ∈ H :=
        ggQ2s08ck_inv_pres H (s i)
          (fun v => (Submodule.span_singleton_le_iff_mem h H).mpr hhH (hhspan v))
      exact ggQ2s08ck_gen_fix H A (s i) k h hhH hhne hhspan hkfix hkd hsinvpres hsiA hkA hnt
    refine LinearEquiv.ext fun v => ?_
    have hfixW : ∀ w ∈ W, w (k v - v) = k v - v := by
      intro w hw
      rw [hWs] at hw
      induction hw using Subgroup.closure_induction with
      | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact hgenfix i v
      | one => simp
      | mul a b _ _ ha hb => rw [LinearEquiv.mul_apply, hb, ha]
      | inv a _ ha =>
          apply a.injective
          rw [ha]
          simp
    have hmem : k v - v ∈ Submodule.span (ZMod 3) {xv} := (hWfix (k v - v)).mp hfixW
    have hzH : k v - v ∈ H := hkd v
    have hz0 : k v - v = 0 := by
      by_contra hz
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hc0 : c ≠ 0 := by
        intro h0
        exact hz (by rw [← hc, h0, zero_smul])
      apply hxH
      have hxv : xv = c⁻¹ • (k v - v) := by
        rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hxv]
      exact H.smul_mem c⁻¹ hzH
    exact sub_eq_zero.mp hz0
  have hKcent : ∀ k ∈ R, (∀ u ∈ H, k u = u) → ∀ w ∈ W, w * k = k * w := by
    intro k hkR hkfix w hw
    have hwR : w ∈ R := hWR hw
    set k' : V ≃ₗ[ZMod 3] V := w * k * w⁻¹ with hk'def
    have hk'R : k' ∈ R := R.mul_mem (R.mul_mem hwR hkR) (R.inv_mem hwR)
    have hk'fix : ∀ u ∈ H, k' u = u := by
      intro u hu
      have h1 : w⁻¹ u ∈ H :=
        ggQ2s08ck_inv_pres H w (fun v => hWdiff w hw v) u hu
      calc k' u = w (k (w⁻¹ u)) := by
            rw [hk'def, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        _ = w (w⁻¹ u) := by rw [hkfix _ h1]
        _ = u := by simp
    have hk'diff : ∀ v, k v - k' v ∈ H := by
      intro v
      have h1 : w⁻¹ v - v ∈ H := hWdiff w⁻¹ (W.inv_mem hw) v
      have hsplit : w⁻¹ v = v + (w⁻¹ v - v) := by abel
      have hk1 : k (w⁻¹ v) = k v + (w⁻¹ v - v) := by
        rw [hsplit, map_add, hkfix _ h1]
        abel
      have h' : k' v = w (k v) + w (w⁻¹ v - v) := by
        rw [hk'def, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hk1, map_add]
      have h2 : w (k v) - k v ∈ H := hWdiff w hw (k v)
      have h3 : w (w⁻¹ v - v) ∈ H := hpres w hwR _ h1
      have h4 : k v - k' v = -(w (k v) - k v) - w (w⁻¹ v - v) := by rw [h']; abel
      rw [h4]
      exact H.sub_mem (H.neg_mem h2) h3
    have hmR : k'⁻¹ * k ∈ R := R.mul_mem (R.inv_mem hk'R) hkR
    have hmfix : ∀ u ∈ H, (k'⁻¹ * k) u = u := by
      intro u hu
      rw [LinearEquiv.mul_apply, hkfix u hu]
      exact ggQ2s08ck_inv_fix H k' hk'fix u hu
    have hmdiff : ∀ v, (k'⁻¹ * k) v - v ∈ H := by
      intro v
      have hsub : k v - k' v ∈ H := hk'diff v
      have hcalc : (k'⁻¹ * k) v - v = k'⁻¹ (k v - k' v) := by
        have hinv : k'⁻¹ (k' v) = v := LinearEquiv.symm_apply_apply k' v
        calc (k'⁻¹ * k) v - v = k'⁻¹ (k v) - v := by rw [LinearEquiv.mul_apply]
          _ = k'⁻¹ (k v) - k'⁻¹ (k' v) := by rw [hinv]
          _ = k'⁻¹ (k v - k' v) := by rw [map_sub]
      rw [hcalc, ggQ2s08ck_inv_fix H k' hk'fix _ hsub]
      exact hsub
    have hm1 : k'⁻¹ * k = 1 := hK1 (k'⁻¹ * k) hmR hmfix hmdiff
    have hk'eq : k' = k := by
      calc k' = k' * 1 := (mul_one k').symm
        _ = k' * (k'⁻¹ * k) := by rw [hm1]
        _ = (k' * k'⁻¹) * k := (mul_assoc k' k'⁻¹ k).symm
        _ = 1 * k := by rw [mul_inv_cancel]
        _ = k := one_mul k
    have hconj : w * k * w⁻¹ = k := by rw [← hk'def]; exact hk'eq
    have h2 : (w * k * w⁻¹) * w = k * w := by rw [hconj]
    rw [mul_assoc, inv_mul_cancel, mul_one] at h2
    exact h2
  have hKstab : ∀ k ∈ R, (∀ u ∈ H, k u = u) → ∃ c : ZMod 3, k xv = c • xv := by
    intro k hkR hkfix
    have hcomm : ∀ w ∈ W, w * k = k * w := hKcent k hkR hkfix
    have hfix : ∀ w ∈ W, w (k xv) = k xv := by
      intro w hw
      have hwxv : w xv = xv :=
        (hWfix xv).mpr (Submodule.mem_span_singleton_self xv) w hw
      calc w (k xv) = (w * k) xv := by rw [LinearEquiv.mul_apply]
        _ = (k * w) xv := by rw [hcomm w hw]
        _ = k (w xv) := by rw [LinearEquiv.mul_apply]
        _ = k xv := by rw [hwxv]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((hWfix (k xv)).mp hfix)
    exact ⟨c, hc.symm⟩
  intro g hgR
  obtain ⟨w, hwW, hgweq⟩ := hres g hgR
  have hwR : w ∈ R := hWR hwW
  have hkR : g * w⁻¹ ∈ R := R.mul_mem hgR (R.inv_mem hwR)
  have hkfix : ∀ u ∈ H, (g * w⁻¹) u = u := by
    intro u hu
    have h1 : w⁻¹ u ∈ H := ggQ2s08ck_inv_pres H w (fun v => hWdiff w hwW v) u hu
    rw [LinearEquiv.mul_apply, hgweq (w⁻¹ u) h1]
    simp
  obtain ⟨c, hc⟩ := hKstab (g * w⁻¹) hkR hkfix
  refine ⟨c, ?_⟩
  have hwxv : w xv = xv := (hWfix xv).mpr (Submodule.mem_span_singleton_self xv) w hwW
  have hg : (g * w⁻¹) (w xv) = g xv := by
    rw [LinearEquiv.mul_apply]
    have hinv : w⁻¹ (w xv) = xv := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    rw [hinv]
  rw [hwxv] at hg
  rw [← hg, hc]

end CFSG.StandardType

end

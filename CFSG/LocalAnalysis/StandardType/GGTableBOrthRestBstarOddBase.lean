module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddFrame

public section

namespace CFSG.StandardType

namespace OrthBstarOdd

open Module CFSG.RankThree.PartOne.LIT OrthRestOdd

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem frame_base {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1) (hX : finrank K X = 4)
    {Q : QuadraticForm K X} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {T E : Subgroup (X ≃ₗ[K] X)} (hET : E ≤ T) (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    (hpow : ∀ g ∈ T, g ^ p = 1) (hQT : ∀ g ∈ T, ∀ v, Q (g v) = Q v) (hT : p ^ 2 ≤ Nat.card T)
    (hE1 : p ≤ Nat.card E) (hE2 : Nat.card E ≤ p) {Y : Submodule K X} (hY : Y ≠ ⊥)
    (hYinv : ∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y) (hYsing : ∀ y ∈ Y, Q y = 0) :
    ∃ t ∈ T, ∃ t' ∈ T, ∃ s ∈ E, ∃ τ : K, FrameData Q E (commSpace t) (commSpace t') s τ := by
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  have : Fact p.Prime := ⟨hp⟩
  have : Finite X := Module.finite_of_finite K
  have : Finite (X ≃ₗ[K] X) := Finite.of_injective (fun e : X ≃ₗ[K] X => (e : X → X))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hTiso := isoGroup_of hQ hcomm hpow hQT
  obtain ⟨t, htT, -, ht2⟩ := exists_commSpace_two_of_full hp hpK 4 X hX (by norm_num) _ T
    hTiso (by simpa using hT)
  have hc := hTiso.isCompl hpK htT
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hU2 : finrank K (fixedSpace t) = 2 := by omega
  have hTU := hTiso.resFix hpK htT
  have hTW := hTiso.resComm hpK htT
  have h1 := hTU.card_le hp hpK
  have h2 := hTW.card_le hp hpK
  rw [hU2, show (2 : ℕ) / 2 = 1 from rfl, pow_one] at h1
  rw [ht2, show (2 : ℕ) / 2 = 1 from rfl, pow_one] at h2
  have h3 := card_le_mul_res hc (hTiso.fix_inv htT) (hTiso.comm_inv htT)
  have hT' : p * p ≤ Nat.card T := by rw [← sq]; exact hT
  have hmul : Nat.card (resHom T _ (hTiso.fix_inv htT)).range *
      Nat.card (resHom T _ (hTiso.comm_inv htT)).range ≤ Nat.card T :=
    (Nat.mul_le_mul h1 h2).trans hT'
  have hTUp : p ≤ Nat.card (resHom T _ (hTiso.fix_inv htT)).range := by
    by_contra hlt
    push Not at hlt
    have h4 : Nat.card T < p * p :=
      calc Nat.card T ≤ _ := h3
        _ ≤ Nat.card (resHom T _ (hTiso.fix_inv htT)).range * p := Nat.mul_le_mul_left _ h2
        _ < p * p := Nat.mul_lt_mul_of_pos_right hlt hp.pos
    omega
  obtain ⟨x, hxT, hx1⟩ : ∃ x ∈ (resHom T _ (hTiso.fix_inv htT)).range, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h0 : (resHom T _ (hTiso.fix_inv htT)).range = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [h0, Subgroup.card_bot] at hTUp
    exact absurd hTUp (not_le.mpr hp.one_lt)
  obtain ⟨t'', ht'U, ht'W⟩ := exists_lift hc (hTiso.fix_inv htT) (hTiso.comm_inv htT) hmul hxT
    (one_mem _)
  have hW'eq := commSpace_eq_map hc (hTiso.fix_inv htT) (hTiso.comm_inv htT) ht'W
  rw [ht'U] at hW'eq
  set t' : X ≃ₗ[K] X := (t'' : X ≃ₗ[K] X) with ht'def
  have ht'T : t' ∈ T := t''.2
  have hx2 : finrank K (commSpace x) = 2 := by
    obtain ⟨k, hk⟩ := (hTU.resComm hpK hxT).even_finrank
    have h0 : finrank K (commSpace x) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact commSpace_ne_bot hx1
    have hle : finrank K (commSpace x) ≤ 2 := (Submodule.finrank_le (commSpace x)).trans hU2.le
    omega
  have hW'2 : finrank K (commSpace t') = 2 := by
    rw [hW'eq, Submodule.finrank_map_subtype_eq, hx2]
  have hW'U : commSpace t' = fixedSpace t := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [hW'eq]
      exact Submodule.map_subtype_le _ _
    · rw [hW'2, hU2]
  obtain ⟨-, -, -, hWan⟩ := plane_facts hp hp2 hK1 (hQT t htT) (hpow t htT) ht2
    (commSpace_nondeg hQ hpK (hQT t htT) (hpow t htT)) (fun v hv => map_mem_commSpace rfl hv)
    (fpf_commSpace hpK (hpow t htT))
  obtain ⟨-, -, -, hUan⟩ := plane_facts hp hp2 hK1 (hQT t' ht'T) (hpow t' ht'T) hW'2
    (commSpace_nondeg hQ hpK (hQT t' ht'T) (hpow t' ht'T)) (fun v hv => map_mem_commSpace rfl hv)
    (fpf_commSpace hpK (hpow t' ht'T))
  obtain ⟨s, hsE, hs1⟩ : ∃ s ∈ E, s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h0 : E = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [h0, Subgroup.card_bot] at hE1
    exact absurd hE1 (not_le.mpr hp.one_lt)
  have hsT := hET hsE
  have hst : s * t = t * s := hcomm s hsT t htT
  have hst' : s * t' = t' * s := hcomm s hsT t' ht'T
  have hsW : ∀ v ∈ commSpace t, s v ∈ commSpace t := fun v hv => map_mem_commSpace hst hv
  have hsU : ∀ v ∈ commSpace t', s v ∈ commSpace t' := fun v hv => map_mem_commSpace hst' hv
  have hdec : ∀ v : X, ∃ u ∈ commSpace t', ∃ w ∈ commSpace t, v = u + w := by
    intro v
    have hv : v ∈ fixedSpace t ⊔ commSpace t := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    exact ⟨u, by rw [hW'U]; exact hu, w, hw, rfl⟩
  have hs_ne : ¬ ((∀ u ∈ commSpace t', s u = u) ∧ ∀ w ∈ commSpace t, s w = w) := by
    rintro ⟨hU1, hW1⟩
    apply hs1
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, hu, w, hw, rfl⟩ := hdec v
    rw [map_add, hU1 u hu, hW1 w hw]
    rfl
  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  obtain ⟨u, hu, w, hw, rfl⟩ := hdec y
  have hfixW : ∀ {v : X}, v ∈ commSpace t → v ≠ 0 → s v = v → ∀ u ∈ commSpace t, s u = u :=
    fun hv hv0 hsv => fix_all_of_fix hK1 (hpow t htT) hst ht2
      (fun v hv => map_mem_commSpace rfl hv) (fpf_commSpace hpK (hpow t htT)) hv hv0 hsv
  have hfixU : ∀ {v : X}, v ∈ commSpace t' → v ≠ 0 → s v = v → ∀ u ∈ commSpace t', s u = u :=
    fun hv hv0 hsv => fix_all_of_fix hK1 (hpow t' ht'T) hst' hW'2
      (fun v hv => map_mem_commSpace rfl hv) (fpf_commSpace hpK (hpow t' ht'T)) hv hv0 hsv
  have hsy : s (u + w) - (u + w) ∈ Y := Y.sub_mem (hYinv s hsE _ hyY) hyY
  have hfW : ∀ v ∈ commSpace t, v ≠ 0 → s v ≠ v := by
    intro v hv hv0 hsv
    have hW1 := hfixW hv hv0 hsv
    have hz : s (u + w) - (u + w) = s u - u := by rw [map_add, hW1 w hw]; abel
    have hsu : s u = u := by
      by_contra hne
      exact hUan (s u - u) ((commSpace t').sub_mem (hsU u hu) hu) (sub_ne_zero.mpr hne)
        (hYsing _ (hz ▸ hsy))
    by_cases hu0 : u = 0
    · subst hu0
      rw [zero_add] at hyY hy0
      exact hWan w hw hy0 (hYsing w hyY)
    · exact hs_ne ⟨hfixU hu hu0 hsu, hW1⟩
  have hfU : ∀ v ∈ commSpace t', v ≠ 0 → s v ≠ v := by
    intro v hv hv0 hsv
    have hU1 := hfixU hv hv0 hsv
    have hz : s (u + w) - (u + w) = s w - w := by rw [map_add, hU1 u hu]; abel
    have hsw : s w = w := by
      by_contra hne
      exact hWan (s w - w) ((commSpace t).sub_mem (hsW w hw) hw) (sub_ne_zero.mpr hne)
        (hYsing _ (hz ▸ hsy))
    by_cases hw0 : w = 0
    · subst hw0
      rw [add_zero] at hyY hy0
      exact hUan u hu hy0 (hYsing u hyY)
    · exact hs_ne ⟨hU1, hfixW hw hw0 hsw⟩
  obtain ⟨τ₁, hτ₁, hsq₁, -⟩ := plane_facts hp hp2 hK1 (hQT s hsT) (hpow s hsT) ht2
    (commSpace_nondeg hQ hpK (hQT t htT) (hpow t htT)) hsW hfW
  obtain ⟨τ₂, -, hsq₂, -⟩ := plane_facts hp hp2 hK1 (hQT s hsT) (hpow s hsT) hW'2
    (commSpace_nondeg hQ hpK (hQT t' ht'T) (hpow t' ht'T)) hsU hfU
  have hτ : τ₂ = τ₁ := by
    by_contra hne
    have hz : s (s (u + w)) - τ₁ • s (u + w) - (u + w) = (τ₂ - τ₁) • s u := by
      simp only [map_add]
      rw [hsq₁ w hw, hsq₂ u hu]
      module
    have hzY : s (s (u + w)) - τ₁ • s (u + w) - (u + w) ∈ Y :=
      Y.sub_mem (Y.sub_mem (hYinv s hsE _ (hYinv s hsE _ hyY))
        (Y.smul_mem _ (hYinv s hsE _ hyY))) hyY
    have hz0 : (τ₂ - τ₁) • s u = 0 := by
      by_contra h0
      exact hUan _ ((commSpace t').smul_mem _ (hsU u hu)) h0 (hYsing _ (hz ▸ hzY))
    have hsu0 : s u = 0 := (smul_eq_zero.mp hz0).resolve_left (sub_ne_zero.mpr hne)
    have hu0 : u = 0 := by
      have := congrArg s.symm hsu0
      simpa using this
    subst hu0
    rw [zero_add] at hyY hy0
    exact hWan w hw hy0 (hYsing w hyY)
  have hord : orderOf s = p := orderOf_eq_prime (hpow s hsT) hs1
  have hEz : Subgroup.zpowers s = E := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hsE) (by rw [Nat.card_zpowers, hord]; exact hE2)
  have hsq : ∀ v ∈ commSpace t ⊔ commSpace t', s (s v) = τ₁ • s v + v := by
    intro v hv
    obtain ⟨w₁, hw₁, u₁, hu₁, rfl⟩ := Submodule.mem_sup.mp hv
    simp only [map_add]
    rw [hsq₁ w₁ hw₁, hsq₂ u₁ hu₁, hτ]
    module
  have hpowk := act_of_pow hsq
  refine ⟨t, htT, t', ht'T, s, hsE, τ₁,
    { finrank_left := ht2, finrank_right := hW'2, orth := ?_, fpf_left := hfW, fpf_right := hfU,
      sq := hsq, act := ?_, aniso_left := hWan, aniso_right := hUan, tau_ne := hτ₁,
      sing := ⟨u + w, add_comm w u ▸ Submodule.add_mem_sup hw hu, hy0, hYsing _ hyY⟩ }⟩
  · intro w₁ hw₁ w₂ hw₂
    rw [QuadraticMap.polar_comm]
    exact polar_fixed_comm (hQT t htT) w₂ (by rw [← hW'U]; exact hw₂) w₁ hw₁
  · intro e he
    rw [← hEz] at he
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp
      ((isOfFinOrder_of_finite s).mem_powers_iff_mem_zpowers.mpr he)
    exact hpowk k

theorem frame_of_singular {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) :
    ∀ (a : ℕ) (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X],
      finrank K X = 2 * a → ∀ (Q : QuadraticForm K X), (QuadraticMap.polarBilin Q).Nondegenerate →
      ∀ (T E : Subgroup (X ≃ₗ[K] X)), E ≤ T →
      (∀ g ∈ T, ∀ h ∈ T, g * h = h * g) → (∀ g ∈ T, g ^ p = 1) →
      (∀ g ∈ T, ∀ v, Q (g v) = Q v) → p ^ a ≤ Nat.card T → p ^ (a - 1) ≤ Nat.card E →
      ∀ Y : Submodule K X, Y ≠ ⊥ → (∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y) → (∀ y ∈ Y, Q y = 0) →
      ∃ t ∈ T, ∃ t' ∈ T, ∃ s ∈ E, ∃ τ : K, FrameData Q E (commSpace t) (commSpace t') s τ := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro X _ _ _ hX Q hQ T E hET hcomm hpow hQT hT hE Y hY hYinv hYsing
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  have : Finite X := Module.finite_of_finite K
  have : Finite (X ≃ₗ[K] X) := Finite.of_injective (fun e : X ≃ₗ[K] X => (e : X → X))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hTiso := isoGroup_of hQ hcomm hpow hQT
  have hEiso : IsoGroup (QuadraticMap.polarBilin Q) p E :=
    isoGroup_of hQ (fun g hg h hh => hcomm g (hET hg) h (hET hh)) (fun g hg => hpow g (hET hg))
      (fun g hg => hQT g (hET hg))
  rcases card_le_or_exists_fix hEiso hp hpK hY hYinv with hle | ⟨g, hgE, hg1, Y', hY'0, hY'Y,
    hY'inv, hgY'⟩
  ·
    have ha : a ≤ 2 := by
      by_contra h
      have h1 : p ^ 2 ≤ p ^ (a - 1) := Nat.pow_le_pow_right hp.pos (by omega)
      have h2 : p < p ^ 2 := by
        rw [sq]
        exact lt_mul_self hp.one_lt
      omega
    obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
    · exfalso
      rw [mul_zero] at hX
      have : Subsingleton X := Module.finrank_zero_iff.mp hX
      exact hy0 (Subsingleton.elim _ _)
    · exfalso
      have hT1 : 1 < Nat.card T := lt_of_lt_of_le hp.one_lt (by simpa using hT)
      have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp hT1
      obtain ⟨t, ht1⟩ := exists_ne (1 : T)
      exact false_of_dim_two hp hp2 hK1 (by rw [hX]) hQ (hQT t t.2) (hpow t t.2)
        (fun h => ht1 (Subtype.ext h)) hy0 (hYsing y hyY)
    · exact frame_base hp hp2 hK1 (by rw [hX]) hQ hET hcomm hpow hQT hT (by simpa using hE) hle
        hY hYinv hYsing
  ·
    have hgT := hET hgE
    have hc := hTiso.isCompl hpK hgT
    have hTU := hTiso.resFix hpK hgT
    have hTW := hTiso.resComm hpK hgT
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    obtain ⟨a', ha'⟩ := hTU.even_finrank
    obtain ⟨b', hb'⟩ := hTW.even_finrank
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
    have hEU : ∀ e ∈ E, ∀ u ∈ fixedSpace g, e u ∈ fixedSpace g :=
      fun e he => hTiso.fix_inv hgT e (hET he)
    have hEW : ∀ e ∈ E, ∀ w ∈ commSpace g, e w ∈ commSpace g :=
      fun e he => hTiso.comm_inv hgT e (hET he)
    have hEWiso := hEiso.resComm hpK hgE
    have hcT := card_le_mul_res hc (hTiso.fix_inv hgT) (hTiso.comm_inv hgT)
    have hcE := card_le_mul_res (E := E) hc hEU hEW
    have hTWc := hTW.card_le hp hpK
    have hEWc := hEWiso.card_le hp hpK
    have hTUc := hTU.card_le hp hpK
    rw [hb', show (b' + b') / 2 = b' by omega] at hTWc hEWc
    rw [ha', show (a' + a') / 2 = a' by omega] at hTUc
    have hab : a = a' + b' := by omega
    have hpb : 0 < p ^ b' := pow_pos hp.pos _
    have hTUcard : p ^ a' ≤ Nat.card (resHom T (fixedSpace g) (hTiso.fix_inv hgT)).range := by
      refine Nat.le_of_mul_le_mul_right ?_ hpb
      calc p ^ a' * p ^ b' = p ^ a := by rw [hab, pow_add]
        _ ≤ Nat.card T := hT
        _ ≤ _ := hcT
        _ ≤ _ := Nat.mul_le_mul_left _ hTWc
    have hEUcard : p ^ (a' - 1) ≤ Nat.card (resHom E (fixedSpace g) hEU).range := by
      refine Nat.le_of_mul_le_mul_right ?_ hpb
      calc p ^ (a' - 1) * p ^ b' = p ^ (a - 1) := by
            rw [← pow_add]
            congr 1
            omega
        _ ≤ Nat.card E := hE
        _ ≤ _ := hcE
        _ ≤ _ := Nat.mul_le_mul_left _ hEWc
    have hmulT : Nat.card (resHom T (fixedSpace g) (hTiso.fix_inv hgT)).range *
        Nat.card (resHom T (commSpace g) (hTiso.comm_inv hgT)).range ≤ Nat.card T :=
      calc _ ≤ p ^ a' * p ^ b' := Nat.mul_le_mul hTUc hTWc
        _ = p ^ a := by rw [hab, pow_add]
        _ ≤ Nat.card T := hT
    have hEUT : (resHom E (fixedSpace g) hEU).range ≤
        (resHom T (fixedSpace g) (hTiso.fix_inv hgT)).range := by
      rintro _ ⟨e, rfl⟩
      exact ⟨⟨e, hET e.2⟩, LinearEquiv.ext fun u => rfl⟩
    obtain ⟨t₀, ht₀, t₀', ht₀', s₀, hs₀, τ, hFD⟩ := ih a' (by omega) (fixedSpace g) (by omega)
      (Q.comp (fixedSpace g).subtype)
      (nondeg_comp (fixedSpace_nondeg hQ hpK (hQT g hgT) (hpow g hgT)))
      (resHom T (fixedSpace g) (hTiso.fix_inv hgT)).range (resHom E (fixedSpace g) hEU).range hEUT
      hTU.comm hTU.pow (by rintro _ ⟨t, rfl⟩ v; exact hQT t t.2 v) hTUcard hEUcard Y'' hY''0
      (by rintro _ ⟨e, rfl⟩ z hz; exact hY'inv e e.2 z hz) (fun z hz => hYsing z (hY'Y hz))
    obtain ⟨t, htU, htW⟩ := exists_lift hc (hTiso.fix_inv hgT) (hTiso.comm_inv hgT) hmulT ht₀
      (one_mem _)
    obtain ⟨t', ht'U, ht'W⟩ := exists_lift hc (hTiso.fix_inv hgT) (hTiso.comm_inv hgT) hmulT
      ht₀' (one_mem _)
    obtain ⟨s, rfl⟩ := hs₀
    have e1 := commSpace_eq_map hc (hTiso.fix_inv hgT) (hTiso.comm_inv hgT) htW
    have e2 := commSpace_eq_map hc (hTiso.fix_inv hgT) (hTiso.comm_inv hgT) ht'W
    rw [htU] at e1
    rw [ht'U] at e2
    refine ⟨t, t.2, t', t'.2, s, s.2, τ, ?_⟩
    rw [e1, e2]
    exact FrameData.map hEU s.2 hFD

end OrthBstarOdd

end CFSG.StandardType

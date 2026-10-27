module

public import CFSG.Quasithin.Vol2.Ch11G2Q8SiegelM
public import CFSG.Quasithin.Vol2.Ch11G2Q8CartanW
public import CFSG.Quasithin.Vol2.Ch11G2Q8Stmts

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem tL_zero : tL (0 : K) = 1 :=
  cayley_eq_one fun w => by
    rw [q6_eta w, g2Act_tL]
    simp

theorem tL_mul_self (s : K) : tL s * tL s = 1 := by
  rw [tL_mul, CharTwo.add_self_eq_zero, tL_zero]

theorem tL_one_ne_one : tL (1 : K) ≠ 1 := by
  intro h
  have h1 := congrArg (fun y => g2Act y (q6 (0 : K) 0 1 0 0 0)) h
  simp only [g2Act_tL, map_one] at h1
  have h2 := congrFun h1 (.inl 0)
  simp [q6] at h2

theorem inC_of_tL_fix {s : K} (hs : s ≠ 0) {x : Ix3 → K} (h : g2Act (tL s) x = x) : InC x := by
  have h1 := h
  conv_lhs at h1 => rw [q6_eta x]
  rw [g2Act_tL] at h1
  have e0 := congrFun h1 (.inl 0)
  have e5 := congrFun h1 (.inr 2)
  simp only [q6_apply_inl0, q6_apply_inr2] at e0 e5
  refine ⟨?_, ?_⟩
  · have : s * x (.inl 2) = 0 := by linear_combination e0
    exact (mul_eq_zero.mp this).resolve_left hs
  · have : s * x (.inr 0) = 0 := by linear_combination e5
    exact (mul_eq_zero.mp this).resolve_left hs

theorem exists_tL_sub_eq {s : K} (hs : s ≠ 0) {x : Ix3 → K} (hx : x ∈ stdF K 2) :
    ∃ y, g2Act (tL s) y - y = x := by
  obtain ⟨b1, b2, b3, b4⟩ := mem_stdF_two.mp hx
  refine ⟨q6 0 0 (x (.inl 0) / s) (x (.inr 2) / s) 0 0, ?_⟩
  rw [g2Act_tL]
  conv_rhs => rw [q6_eta x]
  rw [b1, b2, b3, b4]
  funext j
  rcases j with j | j <;> fin_cases j <;> simp [q6] <;> field_simp

omit [CharP K 2] in
theorem sq_ne_one_of_ne_one [CharP K 2] {a : K} (ha : a ≠ 1) : a * a ≠ 1 := by
  intro h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (a - 1) ^ 2 = 0 := by linear_combination h + (1 - a) * h2
  exact ha (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))

theorem exists_d0_sub_C {a : Kˣ} (ha : (a : K) ≠ 1) {x : Ix3 → K} (hx : InC x) :
    ∃ y, InC y ∧ g2Act (g2T (torHom2 K a)) y - y - x ∈ stdF K 2 := by
  have hai : (a : K)⁻¹ * (a : K)⁻¹ ≠ 1 := sq_ne_one_of_ne_one (fun h => ha (inv_eq_one.mp h))
  have haa : ((a : K)⁻¹ * (a : K)⁻¹)⁻¹ ≠ 1 := by
    rw [mul_inv, inv_inv]
    exact sq_ne_one_of_ne_one ha
  obtain ⟨c1, c2⟩ := hx
  refine ⟨q6 0 (x (.inl 1) / ((a : K)⁻¹ * (a : K)⁻¹ - 1)) 0 0
    (x (.inr 1) / (((a : K)⁻¹ * (a : K)⁻¹)⁻¹ - 1)) 0, ⟨rfl, rfl⟩, ?_⟩
  rw [g2Act_g2T_q6, torHom2_apply, mem_stdF_two]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Pi.sub_apply, q6_apply_inl1,
    q6_apply_inl2, q6_apply_inr0, q6_apply_inr1, c1, c2]
  refine ⟨?_, by ring, by ring, ?_⟩
  · linear_combination x (.inl 1) * mul_inv_cancel₀ (sub_ne_zero.mpr hai)
  · linear_combination x (.inr 1) * mul_inv_cancel₀ (sub_ne_zero.mpr haa)

theorem exists_d0_sub_F2 {a : Kˣ} (ha : (a : K) ≠ 1) {x : Ix3 → K} (hx : x ∈ stdF K 2) :
    ∃ y ∈ stdF K 2, g2Act (g2T (torHom2 K a)) y - y = x := by
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have h1 : (a : K) - 1 ≠ 0 := sub_ne_zero.mpr ha
  have h2 : (a : K)⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr fun h => ha (inv_eq_one.mp h)
  obtain ⟨b1, b2, b3, b4⟩ := mem_stdF_two.mp hx
  refine ⟨q6 (x (.inl 0) / ((a : K) - 1)) 0 0 0 0 (x (.inr 2) / ((a : K)⁻¹ - 1)),
    mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [g2Act_g2T_q6, torHom2_apply]
  conv_rhs => rw [q6_eta x]
  rw [b1, b2, b3, b4]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  funext j
  rcases j with j | j <;> fin_cases j <;> simp [q6] <;> field_simp

section Real

variable {W : Type*} [CommGroup W]

@[expose] def commHom (τ : MulAut W) : W →* W where
  toFun w := τ w * w⁻¹
  map_one' := by rw [map_one, inv_one, mul_one]
  map_mul' a b := by
    rw [map_mul, mul_inv]
    ac_rfl

theorem commHom_apply (τ : MulAut W) (w : W) : commHom τ w = τ w * w⁻¹ := rfl

variable {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

variable (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
  (g : ↥(cayleyGroup K))
theorem psiG_mem (γ : ↥(cayleyGroup K)) : psiG hc0 hc1 π g γ ∈ H := (rhoG hc0 hc1 π _).2

include hf

theorem f_psiG (γ : ↥(cayleyGroup K)) (w : W) :
    f (psiG hc0 hc1 π g γ w) = g2Act g (g2Act γ (g2Act g⁻¹ (f w))) := by
  rw [psiG_apply, IsCoord.actG hf hc0 hc1, g2Act_mul_apply, g2Act_mul_apply]

theorem eq_of_f_eq {a b : W} (h : f a = f b) : a * b⁻¹ ∈ Z := (hf.eq_iff a b).mp h

theorem ts_fix (hW : ∀ w : W, w ^ 2 = 1) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {s : K} (hs : s ≠ 0)
    {a : Kˣ} (ha : (a : K) ≠ 1) {w : W}
    (hw : InC (g2Act g⁻¹ (f w))) : psiG hc0 hc1 π g (tL s) w = w := by
  set t := psiG hc0 hc1 π g (tL s) with ht
  set d := psiG hc0 hc1 π g (g2T (torHom2 K a)) with hd
  have htd : t * d = d * t := by
    rw [ht, hd, ← map_mul, ← map_mul, g2T_torHom2_comm_tL]
  have htt : t * t = 1 := by
    rw [ht, ← map_mul, tL_mul_self, map_one]
  have hZ1 : ∀ v, InC (g2Act g⁻¹ (f v)) → commHom t v ∈ Z := by
    intro v hv
    rw [commHom_apply]
    apply eq_of_f_eq hf
    rw [ht, f_psiG hf, g2Act_tL_of_inC s hv, g2Act_apply_inv]
  have hsq : ∀ v, commHom t (commHom t v) = 1 := by
    intro v
    rw [commHom_apply, commHom_apply, map_mul, map_inv, ← MulAut.mul_apply, htt,
      MulAut.one_apply]
    have h1 := hW v
    have h2 := hW (t v)
    rw [sq] at h1 h2
    calc v * (t v)⁻¹ * (t v * v⁻¹)⁻¹ = (v * v) * ((t v) * (t v))⁻¹ := by
          rw [mul_inv, inv_inv, mul_inv]
          ac_rfl
      _ = 1 := by rw [h1, h2, inv_one, mul_one]
  have hdinv : ∀ v, InC (g2Act g⁻¹ (f v)) → commHom t (d v * v⁻¹) = 1 := by
    intro v hv
    have h1 : commHom t (d v) = d (commHom t v) := by
      rw [commHom_apply, commHom_apply, map_mul, map_inv, ← MulAut.mul_apply, htd,
        MulAut.mul_apply]
    rw [map_mul, map_inv, h1, hZ d ((rhoG hc0 hc1 π _).2) _ (hZ1 v hv), mul_inv_cancel]
  obtain ⟨y, hyC, hy⟩ := exists_d0_sub_C ha hw
  obtain ⟨w', hw'⟩ := hf.surj (g2Act g y)
  have hw'C : InC (g2Act g⁻¹ (f w')) := by rwa [hw', g2Act_inv_apply]
  have hF : g2Act g⁻¹ (f (w * (d w' * w'⁻¹)⁻¹)) ∈ stdF K 2 := by
    rw [hf.map_mul_inv, map_sub, hf.map_mul_inv, map_sub, hd, f_psiG hf, hw',
      g2Act_inv_apply, g2Act_inv_apply]
    have e : g2Act g⁻¹ (f w) - (g2Act (g2T (torHom2 K a)) y - y) =
        -(g2Act (g2T (torHom2 K a)) y - y - g2Act g⁻¹ (f w)) := by abel
    rw [e]
    exact (stdF K 2).neg_mem hy
  obtain ⟨z, hz⟩ := exists_tL_sub_eq hs hF
  obtain ⟨ŷ, hŷ⟩ := hf.surj (g2Act g z)
  have hfe : f (commHom t ŷ) = f (w * (d w' * w'⁻¹)⁻¹) := by
    rw [commHom_apply, hf.map_mul_inv, ht, f_psiG hf, hŷ, g2Act_inv_apply, ← map_sub, hz,
      g2Act_apply_inv]
  have hq : (w * (d w' * w'⁻¹)⁻¹) * (commHom t ŷ)⁻¹ ∈ Z := eq_of_f_eq hf hfe.symm
  have h1 : commHom t (w * (d w' * w'⁻¹)⁻¹) = 1 := by
    have e : w * (d w' * w'⁻¹)⁻¹ =
        ((w * (d w' * w'⁻¹)⁻¹) * (commHom t ŷ)⁻¹) * commHom t ŷ :=
      (inv_mul_cancel_right _ _).symm
    rw [e, map_mul, hsq, mul_one, commHom_apply, hZ t (psiG_mem hc0 hc1 g _) _ hq,
      mul_inv_cancel]
  have h2 : commHom t w = 1 := by
    have e : w = (w * (d w' * w'⁻¹)⁻¹) * (d w' * w'⁻¹) := by group
    rw [e, map_mul, h1, one_mul, hdinv w' hw'C]
  rw [commHom_apply, mul_inv_eq_one] at h2
  exact h2

theorem vt_inf_Z (hW : ∀ w : W, w ^ 2 = 1) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {s : K}
    (hs : s ≠ 0) {a : Kˣ} (ha : (a : K) ≠ 1) :
    (commHom (psiG hc0 hc1 π g (tL s))).range ⊓ Z = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨w, rfl⟩, hz⟩
  have h1 : f (psiG hc0 hc1 π g (tL s) w) = f w := by
    have h2 := (hf.ker _).mpr hz
    rwa [commHom_apply, hf.map_mul_inv, sub_eq_zero] at h2
  have hC : InC (g2Act g⁻¹ (f w)) := by
    apply inC_of_tL_fix hs
    rw [f_psiG hf] at h1
    have h2 := congrArg (g2Act g⁻¹) h1
    rwa [g2Act_inv_apply] at h2
  rw [Subgroup.mem_bot, commHom_apply, ts_fix hf hc0 hc1 g hW hZ hs ha hC, mul_inv_cancel]

theorem vt_le_U2 (s : K) : (commHom (psiG hc0 hc1 π g (tL s))).range ≤
    hf.pre (gmapG g (stdF K 2)).toAddSubgroup := by
  rintro _ ⟨w, rfl⟩
  change f (commHom _ w) ∈ gmapG g (stdF K 2)
  rw [mem_gmapG, commHom_apply, hf.map_mul_inv, f_psiG hf, map_sub, g2Act_inv_apply]
  exact g2Act_tL_sub_mem s _

theorem exists_vt {s : K} (hs : s ≠ 0) {u : W}
    (hu : u ∈ hf.pre (gmapG g (stdF K 2)).toAddSubgroup) :
    ∃ v ∈ (commHom (psiG hc0 hc1 π g (tL s))).range, u * v⁻¹ ∈ Z := by
  have hx : g2Act g⁻¹ (f u) ∈ stdF K 2 := mem_gmapG.mp hu
  obtain ⟨y, hy⟩ := exists_tL_sub_eq hs hx
  obtain ⟨ŷ, hŷ⟩ := hf.surj (g2Act g y)
  refine ⟨commHom _ ŷ, ⟨ŷ, rfl⟩, eq_of_f_eq hf ?_⟩
  rw [commHom_apply, hf.map_mul_inv, f_psiG hf, hŷ, g2Act_inv_apply, ← map_sub, hy,
    g2Act_apply_inv]

theorem vt_le (hW : ∀ w : W, w ^ 2 = 1) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {s s' : K}
    (hs : s ≠ 0) (hs' : s' ≠ 0) {a : Kˣ} (ha : (a : K) ≠ 1) :
    (commHom (psiG hc0 hc1 π g (tL s'))).range ≤
      (commHom (psiG hc0 hc1 π g (tL s))).range := by
  have hdH := psiG_mem hc0 hc1 g (π := π) (g2T (torHom2 K a))
  have hcomm : ∀ r : K, psiG hc0 hc1 π g (tL r) * psiG hc0 hc1 π g (g2T (torHom2 K a)) =
      psiG hc0 hc1 π g (g2T (torHom2 K a)) * psiG hc0 hc1 π g (tL r) := by
    intro r
    rw [← map_mul, ← map_mul, g2T_torHom2_comm_tL]
  have hinv : ∀ r : K, ∀ v ∈ (commHom (psiG hc0 hc1 π g (tL r))).range,
      psiG hc0 hc1 π g (g2T (torHom2 K a)) v ∈ (commHom (psiG hc0 hc1 π g (tL r))).range := by
    rintro r _ ⟨w, rfl⟩
    refine ⟨psiG hc0 hc1 π g (g2T (torHom2 K a)) w, ?_⟩
    rw [commHom_apply, commHom_apply, map_mul, map_inv, ← MulAut.mul_apply, hcomm,
      MulAut.mul_apply]
  intro x hx
  have hxU := vt_le_U2 hf hc0 hc1 g s' hx
  obtain ⟨y, hyF, hy⟩ := exists_d0_sub_F2 ha (mem_gmapG.mp hxU)
  obtain ⟨u', hu'⟩ := hf.surj (g2Act g y)
  have hu'U : u' ∈ hf.pre (gmapG g (stdF K 2)).toAddSubgroup := by
    change f u' ∈ gmapG g (stdF K 2)
    rw [mem_gmapG, hu', g2Act_inv_apply]
    exact hyF
  obtain ⟨a', ha', ha'z⟩ := exists_vt hf hc0 hc1 g hs' hu'U
  have hfa : f a' = g2Act g y := by rw [← (hf.eq_iff u' a').mpr ha'z, hu']
  have hda : psiG hc0 hc1 π g (g2T (torHom2 K a)) a' * a'⁻¹ = x := by
    have h1 : psiG hc0 hc1 π g (g2T (torHom2 K a)) a' * a'⁻¹ ∈
        (commHom (psiG hc0 hc1 π g (tL s'))).range :=
      Subgroup.mul_mem _ (hinv s' a' ha') (Subgroup.inv_mem _ ha')
    have h2 : f (psiG hc0 hc1 π g (g2T (torHom2 K a)) a' * a'⁻¹) = f x := by
      rw [hf.map_mul_inv, f_psiG hf, hfa, g2Act_inv_apply, ← map_sub, hy, g2Act_apply_inv]
    have h3 : (psiG hc0 hc1 π g (g2T (torHom2 K a)) a' * a'⁻¹) * x⁻¹ ∈
        (commHom (psiG hc0 hc1 π g (tL s'))).range ⊓ Z :=
      ⟨Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hx), eq_of_f_eq hf h2⟩
    rw [vt_inf_Z hf hc0 hc1 g hW hZ hs' ha] at h3
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h3)
  obtain ⟨b₀, hb₀, hb₀z⟩ := exists_vt hf hc0 hc1 g hs (vt_le_U2 hf hc0 hc1 g s' ha')
  have e : psiG hc0 hc1 π g (g2T (torHom2 K a)) a' * a'⁻¹ =
      psiG hc0 hc1 π g (g2T (torHom2 K a)) b₀ * b₀⁻¹ := by
    conv_lhs => rw [← inv_mul_cancel_right a' b₀]
    rw [map_mul, hZ _ hdH _ hb₀z, mul_inv, mul_comm (a' * b₀⁻¹), mul_assoc, mul_inv_cancel_left]
  rw [← hda, e]
  exact Subgroup.mul_mem _ (hinv s b₀ hb₀) (Subgroup.inv_mem _ hb₀)

end Real

theorem factSiegelG2_holds : FactSiegelG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hZ _ P hP U₂ hU₂
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU : Ch11.SecA.IsFlagW H P Z (Nat.card K) 2 U₂ := by rw [hK]; exact hU₂
  have hUeq := eq_U2_of_isFlagWG hW hf hc0 hc1 hg hU
  subst hUeq
  have ha : ((Units.mk0 c₀ hc0 : Kˣ) : K) ≠ 1 := hc1
  have hs1 : (1 : K) ≠ 0 := one_ne_zero
  have hle : Ch11.SecA.commS (perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmapG g (stdF K 2)).toAddSubgroup))) (hf.pre (gmapG g (stdF K 2)).toAddSubgroup) ≤
      (commHom (psiG hc0 hc1 π g (tL 1))).range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, hk, u, hu, rfl⟩
    have hk' : k ∈ (perfectCore (stabQ (stdF K 2))).map (psiG hc0 hc1 π g) := by
      rw [← gammaW_two_eqG hf hc0 hc1 g]
      exact hk
    obtain ⟨γ, hγ, rfl⟩ := hk'
    obtain ⟨v, hv, hvz⟩ := exists_vt hf hc0 hc1 g hs1 hu
    obtain ⟨s', hs'⟩ := conj_tL_mem (perfectCore_le _ hγ) (1 : K)
    have hs'0 : s' ≠ 0 := by
      rintro rfl
      rw [tL_zero, mul_inv_eq_one, mul_eq_left] at hs'
      exact tL_one_ne_one hs'
    have hkv : psiG hc0 hc1 π g γ v ∈ (commHom (psiG hc0 hc1 π g (tL s'))).range := by
      obtain ⟨w, rfl⟩ := hv
      refine ⟨psiG hc0 hc1 π g γ w, ?_⟩
      rw [commHom_apply, commHom_apply, map_mul, map_inv, ← MulAut.mul_apply, ← map_mul, ← hs',
        show γ * tL 1 * γ⁻¹ * γ = γ * tL 1 by group, map_mul, MulAut.mul_apply]
    have hkv' := vt_le hf hc0 hc1 g hW hZ hs1 hs'0 ha hkv
    have e : psiG hc0 hc1 π g γ u * u⁻¹ = psiG hc0 hc1 π g γ v * v⁻¹ := by
      conv_lhs => rw [← inv_mul_cancel_right u v]
      rw [map_mul, hZ _ (psiG_mem hc0 hc1 g _) _ hvz, mul_inv, mul_comm (u * v⁻¹), mul_assoc,
        mul_inv_cancel_left]
    rw [e]
    exact Subgroup.mul_mem _ hkv' (Subgroup.inv_mem _ hv)
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ (commHom (psiG hc0 hc1 π g (tL 1))).range ⊓ Z := ⟨hle hx.1, hx.2⟩
  rwa [vt_inf_Z hf hc0 hc1 g hW hZ hs1 ha] at h1

end CFSG.Quasithin.Vol2.Ch11.G2Q8

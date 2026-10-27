module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Norm
public import CFSG.Quasithin.Vol2.Ch11G2Q8CartanW
public import CFSG.Quasithin.Vol2.Ch11G2Q8N13
public import CFSG.Quasithin.Vol2.KGNatSL3Par

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (pCoreOf_map_of_injective)

variable {K : Type} [Field K] [CharP K 2]

theorem scalar_eq_one {γ : ↥(cayleyGroup K)} {c : K} (h : ∀ w, g2Act γ w = c • w) : c = 1 := by
  have hq : ∀ a b k d e f : K, g2Act γ (q6 a b k d e f) =
      q6 (c * a) (c * b) (c * k) (c * d) (c * e) (c * f) := fun a b k d e f => by
    rw [h, smul_q6]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := h (eu 0 1)
    rw [zero_smul] at h1
    exact g2Act_eu_ne_zero γ h1
  obtain ⟨r₁, e1⟩ := exists_cgE_zI γ (hq 0 1 0 0 0 0)
  obtain ⟨r₂, e2⟩ := exists_cgE_zI γ (hq 0 0 1 0 0 0)
  obtain ⟨r₃, e3⟩ := exists_cgE_zI γ (hq 0 0 0 1 0 0)
  have hm := cg_mul γ (zI (q6 0 1 0 0 0 0)) (zI (q6 0 0 1 0 0 0))
  rw [zI_mul_u1_u2, e1, e2, e3, cayleyMul_zmk] at hm
  obtain ⟨-, -, -, -, k5, -, -, -⟩ := zmk_inj hm
  have hcc : c * (c - 1) = 0 := by linear_combination -k5
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcc).resolve_left hc0)

theorem g2Act_uSL_v1 (t : K) :
    g2Act (g2A (uSL 0 0 t)) (q6 0 0 0 0 1 0) = q6 0 0 0 0 1 t := by
  rw [g2Act_g2A_uSL]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
      q6_apply_inr2]

omit [CharP K 2] in
theorem q6_v1t (t : K) : q6 (0 : K) 0 0 0 1 t = q6 0 0 0 0 1 0 + t • q6 0 0 0 0 0 1 := by
  funext j
  rcases j with j | j <;> fin_cases j <;> simp [q6]

omit [CharP K 2] in
theorem mem_stdF_one_of_three {y : Ix3 → K} (hy : y ∈ stdF K 3) (h1 : y (.inr 1) = 0)
    (h2 : y (.inr 2) = 0) : y ∈ stdF K 1 := by
  obtain ⟨a1, a2, a3⟩ := mem_stdF_three.mp hy
  rw [mem_stdF]
  intro k hk
  rcases k with k | k <;> fin_cases k
  · exact absurd hk (by decide)
  · exact a1
  · exact a2
  · exact a3
  · exact h1
  · exact h2

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem commute_of_trivial_modG (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) {τ : MulAut W} (hτN : ∀ x ∈ H, τ * x * τ⁻¹ ∈ H) (hτ : ∀ w, f (τ w) = f w) :
    ∀ x ∈ H, τ * x = x * τ := by
  have hτi : ∀ w, f (τ⁻¹ w) = f w := fun w => by
    rw [← hτ (τ⁻¹ w), MulAut.apply_inv_self]
  intro x hx
  obtain ⟨X, hX⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨x, hx⟩
  have hxv : ∀ v, f (x v) = g2Act X (f v) := fun v => by
    have h1 := IsCoord.actG hf hc0 hc1 X v
    rwa [hX] at h1
  have hcH : τ * x * τ⁻¹ * x⁻¹ ∈ H := H.mul_mem (hτN x hx) (H.inv_mem hx)
  obtain ⟨C, hC⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨_, hcH⟩
  have hC1 : C = 1 := cayley_eq_one fun v => by
    obtain ⟨w, rfl⟩ := hf.surj v
    rw [← IsCoord.actG hf hc0 hc1, hC]
    change f ((τ * x * τ⁻¹ * x⁻¹) w) = f w
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hτ, hxv, hτi, ← hxv,
      MulAut.apply_inv_self]
  have h1 : τ * x * τ⁻¹ * x⁻¹ = 1 := by
    have h2 := congrArg Subtype.val hC
    rw [hC1, map_one] at h2
    exact h2.symm
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem sigma_eq_id_of_centralizesG [Finite K] (h4 : 4 ≤ Nat.card K)
    (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (g : ↥(cayleyGroup K))
    [Finite (MulAut W)] {s : MulAut W} (hsZ : ∀ z ∈ Z, s z ∈ Z)
    (hsU : s ∈ Ch11.SecA.stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup))
    (hsU₃ : s ∈ Ch11.SecA.stabW (hf.pre (gmapG g (stdF K 3)).toAddSubgroup))
    (hcomm : ∀ k ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)),
      s * k * s⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmapG g (stdF K 1)).toAddSubgroup))))
    {σ : K →+* K}
    (hσ : ∀ (c : K) (x : Ix3 → K), hf.autMap s hsZ (c • x) = σ c • hf.autMap s hsZ x) :
    ∀ c, σ c = c := by
  have := finite_cayleyGroup (F := K)
  set T := hf.autMap s hsZ with hTdef
  have hTf : ∀ w, T (f w) = f (s w) := hf.autMap_apply s hsZ
  have hψ := psiG_injective hf hc0 hc1 g
  have hΓ := gammaW_one_eqG h4 hf hc0 hc1 g
  have hO : pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmapG g (stdF K 1)).toAddSubgroup))) =
      (pCoreOf 2 (stabV0 K)).map (psiG hc0 hc1 π g) := by
    change pCoreOf 2 (Ch11.SecS.gammaW H _) = _
    rw [hΓ, pCoreOf_map_of_injective _ hψ]
  have hT3 : ∀ v ∈ stdF K 3, g2Act g⁻¹ (T (g2Act g v)) ∈ stdF K 3 := by
    intro v hv
    obtain ⟨w, hw⟩ := hf.surj (g2Act g v)
    have hwU : w ∈ hf.pre (gmapG g (stdF K 3)).toAddSubgroup := by
      change f w ∈ gmapG g (stdF K 3)
      rw [mem_gmapG, hw, g2Act_inv_apply]
      exact hv
    have h1 := (Ch11.SecA.mem_stabW.mp hsU₃ w).mp hwU
    change f (s w) ∈ gmapG g (stdF K 3) at h1
    rw [mem_gmapG, ← hTf, hw] at h1
    exact h1
  obtain ⟨y, hydef⟩ : ∃ y : Ix3 → K, g2Act g⁻¹ (T (g2Act g (q6 0 0 0 0 0 1))) = y := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : Ix3 → K, g2Act g⁻¹ (T (g2Act g (q6 0 0 0 0 1 0))) = z := ⟨_, rfl⟩
  have hy3 : y ∈ stdF K 3 := hydef ▸ hT3 _ (mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩)
  have hz3 : z ∈ stdF K 3 := hzdef ▸ hT3 _ (mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩)
  have key : ∀ t : K, σ t * y (.inr 1) = 0 ∧ σ t * y (.inr 2) = t * z (.inr 1) := by
    intro t
    have hγS : g2A (uSL 0 0 t) ∈ stabV0 K := U0_le_stabV0 (g2A_mem_U0 0 0 t)
    set k := psiG hc0 hc1 π g (g2A (uSL 0 0 t)) with hk
    have hkL : k ∈ perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)) := by
      change k ∈ Ch11.SecS.gammaW H _
      rw [hΓ]
      exact ⟨_, hγS, rfl⟩
    have hc := hcomm k hkL
    rw [hO] at hc
    obtain ⟨m, hm, hmeq⟩ := hc
    obtain ⟨hmS, hm1⟩ := mem_pCoreOf_stabV0_iff.mp hm
    obtain ⟨w₀, hw₀⟩ := hf.surj (g2Act g (q6 0 0 0 0 1 0))
    have hid : (s * k * s⁻¹ * k⁻¹) (k (s w₀)) = s (k w₀) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self,
        MulAut.inv_apply_self]
    have hLHS : f ((s * k * s⁻¹ * k⁻¹) (k (s w₀))) =
        g2Act g (g2Act m (g2Act (g2A (uSL 0 0 t)) z)) := by
      rw [← hmeq, psiG_apply, IsCoord.actG hf hc0 hc1, hk, psiG_apply, IsCoord.actG hf hc0 hc1,
        ← hTf, hw₀, ← hzdef]
      simp only [g2Act_mul_apply, g2Act_inv_apply]
    have hRHS : f (s (k w₀)) = T (g2Act g (q6 0 0 0 0 1 0)) +
        σ t • T (g2Act g (q6 0 0 0 0 0 1)) := by
      rw [← hTf, hk, psiG_apply, IsCoord.actG hf hc0 hc1, hw₀]
      simp only [g2Act_mul_apply, g2Act_inv_apply]
      rw [g2Act_uSL_v1, q6_v1t, map_add, g2Act_smul, map_add, hσ]
    have h1 := congrArg (g2Act g⁻¹) (hLHS.symm.trans ((congrArg f hid).trans hRHS))
    rw [g2Act_inv_apply, map_add, g2Act_smul, hydef, hzdef] at h1
    have hγz : g2Act (g2A (uSL 0 0 t)) z ∈ stdF K 3 := mapsF3_of_mem hγS z hz3
    have h2 := congrArg vpart h1
    rw [vpart_act hmS hγz, hm1, Matrix.one_mulVec, vpart_act hγS hz3, levi1Mat_uSL, vpart_add,
      vpart_smul] at h2
    have h21 := congrFun h2 0
    have h22 := congrFun h2 1
    simp only [vpart, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at h21 h22
    exact ⟨by linear_combination -h21, by linear_combination -h22⟩
  obtain ⟨h11, h12⟩ := key 1
  simp only [map_one, one_mul] at h11 h12
  have hy2 : y (.inr 2) ≠ 0 := by
    intro h0
    have hy1 : y ∈ stdF K 1 := mem_stdF_one_of_three hy3 h11 h0
    obtain ⟨w₁, hw₁⟩ := hf.surj (g2Act g (q6 0 0 0 0 0 1))
    have hsw : s w₁ ∈ hf.pre (gmapG g (stdF K 1)).toAddSubgroup := by
      change f (s w₁) ∈ gmapG g (stdF K 1)
      rw [mem_gmapG, ← hTf, hw₁, hydef]
      exact hy1
    have h1 := (Ch11.SecA.mem_stabW.mp hsU w₁).mpr hsw
    change f w₁ ∈ gmapG g (stdF K 1) at h1
    rw [mem_gmapG, hw₁, g2Act_inv_apply] at h1
    exact absurd ((mem_stdF.mp h1) (.inr 2) (by decide)) (by simp [q6])
  intro c
  obtain ⟨-, hc⟩ := key c
  rw [← h12] at hc
  exact mul_right_cancel₀ hy2 hc

end Real

theorem factParG2_holds : Ch11.SecB.FactParG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hfixV hcommV P hP U hU S hS2 hSH hSU
  subst hfixV
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have := finite_cayleyGroup (F := K)
  have h4 := four_le_card hn hK
  have ha : ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U), ∀ u ∈ U, h u = u :=
    fix_of_perfect (U := U) (Z := fixV H) (perfectCore_perfect _)
      (fun h hh z hz => mem_fixV.mp hz h (perfectCore_le _ hh).1)
      (factPointG2A_holds K n hn hK W hW H (fixV H) π hπ P hP U hU)
  refine ⟨ha, fun s hs hcomm u hu => ?_⟩
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU1 : Ch11.SecA.IsFlagW H P (fixV H) (Nat.card K) 1 U := by rw [hK]; exact hU
  have hUeq := eq_U1_of_isFlagWG hW hf hc0 hc1 hg hU1
  subst hUeq
  have hs' : ∀ h ∈ H, s⁻¹ * h * s ∈ H := fun h hh => by
    have := hSH s⁻¹ (S.inv_mem hs) h hh
    rwa [inv_inv] at this
  have hs'' : ∀ h ∈ H, s⁻¹⁻¹ * h * s⁻¹ ∈ H := fun h hh => by
    rw [inv_inv]
    exact hSH s hs h hh
  have hsZ : ∀ z ∈ fixV H, s z ∈ fixV H := maps_fixV hs'
  have hsZ' : ∀ z ∈ fixV H, s⁻¹ z ∈ fixV H := maps_fixV hs''
  have hsZW : s ∈ Ch11.SecA.stabW (fixV H) := Ch11.SecA.mem_stabW.mpr fun z =>
    ⟨hsZ z, fun h => by
      have h1 := hsZ' _ h
      rwa [MulAut.inv_apply_self] at h1⟩
  have hU₃f : Ch11.SecA.IsFlagW H P (fixV H) (2 ^ n) 3
      (hf.pre (gmapG g (stdF K 3)).toAddSubgroup) := by
    rw [← hK]
    exact isFlagW_preG hW hf hc0 hc1 hg (stdF_stable 3) (card_stdF (by norm_num))
  have hsU₃ := (factN13G2_holds K n hn hK W hW H (fixV H) π hπ P hP _ _ hU hU₃f s hsZW
    (hSH s hs)).mp (hSU hs)
  have hx0 : (q6 (1 : K) 0 0 0 0 0) ≠ 0 := fun h => one_ne_zero (congrFun h (.inl 0))
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_g2Derived hc0 hc1 _ T hT)
    hx0 s hsZ hsZ' hs'
  have hσid := sigma_eq_id_of_centralizesG h4 hf hc0 hc1 g hsZ (hSU hs) hsU₃ hcomm hσ
  set T := hf.autMap s hsZ with hTdef
  have hTf : ∀ w, T (f w) = f (s w) := hf.autMap_apply s hsZ
  have hT'f : ∀ w, hf.autMap s⁻¹ hsZ' (f w) = f (s⁻¹ w) := hf.autMap_apply s⁻¹ hsZ'
  let TL : (Ix3 → K) ≃ₗ[K] (Ix3 → K) :=
    { toFun := T
      invFun := hf.autMap s⁻¹ hsZ'
      map_add' := map_add T
      map_smul' := fun c v => by rw [hσ, hσid]; rfl
      left_inv := fun x => by
        obtain ⟨w, rfl⟩ := hf.surj x
        rw [hTf, hT'f, MulAut.inv_apply_self]
      right_inv := fun x => by
        obtain ⟨w, rfl⟩ := hf.surj x
        rw [hT'f, hTf, MulAut.apply_inv_self] }
  let A : (Ix3 → K) ≃ₗ[K] (Ix3 → K) := ((g2LE g).trans TL).trans (g2LE g⁻¹)
  have hAapp : ∀ w, A w = g2Act g⁻¹ (T (g2Act g w)) := fun w => rfl
  have hA : ∀ γ : ↥(cayleyGroup K), ∃ γ' : ↥(cayleyGroup K),
      ∀ w, A (g2Act γ w) = g2Act γ' (A w) := by
    intro γ
    have hk : s * ((rhoG hc0 hc1 π (g * γ * g⁻¹) : ↥H) : MulAut W) * s⁻¹ ∈ H :=
      hSH s hs _ (rhoG hc0 hc1 π _).2
    obtain ⟨δ, hδ⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨_, hk⟩
    refine ⟨g⁻¹ * δ * g, fun w => ?_⟩
    obtain ⟨x, hx⟩ := hf.surj (g2Act g w)
    rw [hAapp, hAapp]
    have e1 : g2Act g (g2Act γ w) =
        f (((rhoG hc0 hc1 π (g * γ * g⁻¹) : ↥H) : MulAut W) x) := by
      rw [IsCoord.actG hf hc0 hc1, hx, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]
    have e2 : s (((rhoG hc0 hc1 π (g * γ * g⁻¹) : ↥H) : MulAut W) x) =
        ((rhoG hc0 hc1 π δ : ↥H) : MulAut W) (s x) := by
      rw [hδ]
      change _ = (s * _ * s⁻¹) (s x)
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [e1, ← hx, hTf, hTf, e2, IsCoord.actG hf hc0 hc1, g2Act_mul_apply, g2Act_mul_apply,
      g2Act_apply_inv]
  obtain ⟨c, h₀, hc0', hAeq⟩ := exists_eq_smul_of_normG2 hK hn A hA
  have hTc : ∀ v, T v = c • g2Act (g * h₀ * g⁻¹) v := by
    intro v
    have h1 := hAeq (g2Act g⁻¹ v)
    rw [hAapp, g2Act_apply_inv] at h1
    have h2 := congrArg (g2Act g) h1
    rw [g2Act_apply_inv, g2Act_smul] at h2
    rw [h2, g2Act_mul_apply, g2Act_mul_apply]
  obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
  have hm' : s ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hpow : ∀ j : ℕ, ∀ w, f ((s ^ j) w) = c ^ j • g2Act ((g * h₀ * g⁻¹) ^ j) (f w) := by
    intro j
    induction j with
    | zero => intro w; rw [pow_zero, pow_zero, pow_zero, one_smul, map_one]; rfl
    | succ j ih =>
      intro w
      rw [pow_succ', MulAut.mul_apply, ← hTf, ih, hσ, hσid, hTc, smul_smul, pow_succ,
        pow_succ']
      simp only [g2Act_mul_apply]
  have hscal : ∀ v, g2Act ((g * h₀ * g⁻¹) ^ 2 ^ m) v = (c ^ 2 ^ m)⁻¹ • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf.surj v
    have h1 := hpow (2 ^ m) w
    rw [hm', MulAut.one_apply] at h1
    conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc0'), one_smul]
  have hcm : c ^ 2 ^ m = 1 := by
    have h1 := scalar_eq_one hscal
    rwa [inv_eq_one] at h1
  have hc1' : c = 1 := eq_one_of_pow_two_pow hcm
  have hh1 : (g * h₀ * g⁻¹) ^ 2 ^ m = 1 := cayley_eq_one fun v => by
    rw [hscal, hcm, inv_one, one_smul]
  set ρs := ((rhoG hc0 hc1 π (g * h₀ * g⁻¹) : ↥H) : MulAut W) with hhdef
  have hsh : ∀ w, f (s w) = f (ρs w) := fun w => by
    rw [← hTf, hTc, hc1', one_smul, hhdef, IsCoord.actG hf hc0 hc1]
  have hhi : ρs⁻¹ = ((rhoG hc0 hc1 π (g * h₀ * g⁻¹)⁻¹ : ↥H) : MulAut W) := by
    rw [hhdef, map_inv, Subgroup.coe_inv]
  have hτ : ∀ w, f ((ρs⁻¹ * s) w) = f w := by
    intro w
    rw [MulAut.mul_apply, hhi, IsCoord.actG hf hc0 hc1, hsh, hhdef, IsCoord.actG hf hc0 hc1,
      g2Act_inv_apply]
  have hτN : ∀ x ∈ H, (ρs⁻¹ * s) * x * (ρs⁻¹ * s)⁻¹ ∈ H := by
    intro x hx
    rw [show (ρs⁻¹ * s) * x * (ρs⁻¹ * s)⁻¹ = ρs⁻¹ * (s * x * s⁻¹) * ρs by group]
    exact H.mul_mem (H.mul_mem (H.inv_mem (rhoG hc0 hc1 π _).2) (hSH s hs x hx))
      (rhoG hc0 hc1 π _).2
  have hτ1 := eq_one_of_commV hcommV (commute_of_trivial_modG hf hc0 hc1 hτN hτ)
    (fun w => (hf.ker _).mp (by rw [hf.map_mul_inv, hτ, sub_self]))
  have hseq : ρs = s := inv_mul_eq_one.mp hτ1
  obtain ⟨u₀, hu₀⟩ := hf.surj (g2Act g (eu 0 1))
  have hu₀U : u₀ ∈ hf.pre (gmapG g (stdF K 1)).toAddSubgroup :=
    mem_gmapG_stdF_one_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩
  obtain ⟨lam₀, hlam₀⟩ :=
    mem_gmapG_stdF_one_iff.mp ((Ch11.SecA.mem_stabW.mp (hSU hs) u₀).mp hu₀U)
  have hh₀ : g2Act h₀ (eu 0 1) = lam₀ • eu 0 1 := by
    have h1 : f (s u₀) = g2Act (g * h₀ * g⁻¹) (f u₀) := by
      rw [← hseq, hhdef, IsCoord.actG hf hc0 hc1]
    rw [hlam₀, hu₀, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply] at h1
    have h2 := congrArg (g2Act g⁻¹) h1
    rwa [g2Act_inv_apply, g2Act_smul, g2Act_inv_apply, eq_comm] at h2
  have hiter : ∀ j : ℕ, g2Act (h₀ ^ j) (eu 0 1) = lam₀ ^ j • eu 0 1 := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, one_smul, map_one]; rfl
    | succ j ih => rw [pow_succ', g2Act_mul_apply, ih, g2Act_smul, hh₀, smul_smul, pow_succ]
  have hh₀1 : h₀ ^ 2 ^ m = 1 := by
    have h1 := hh1
    rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
    exact h1
  have hlam1 : lam₀ = 1 := by
    have h1 := hiter (2 ^ m)
    rw [hh₀1, map_one] at h1
    have h2 := congrFun h1 (.inl 0)
    simp [eu, AddMonoid.End.coe_one] at h2
    first | exact eq_one_of_pow_two_pow h2 | exact eq_one_of_pow_two_pow h2.symm
  have hh₀S : h₀ ∈ stabV0 K := by
    rw [mem_stabV0, hh₀, hlam1, one_smul]
  have hsL : s ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)) := by
    change s ∈ Ch11.SecS.gammaW H _
    rw [gammaW_one_eqG h4 hf hc0 hc1 g, ← hseq]
    exact ⟨h₀, hh₀S, rfl⟩
  exact ha s hsL u hu

end CFSG.Quasithin.Vol2.Ch11.G2Q8

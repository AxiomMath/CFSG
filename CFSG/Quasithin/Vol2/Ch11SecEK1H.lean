module

public import CFSG.Quasithin.Vol2.Ch11SecEK1D
public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8

open EK1 in
theorem factCentLeviG2_holds : FactCentLeviG2 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU β hβH _ hc ⟨m, hmo, hmc, hβm⟩
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have := finite_cayleyGroup (F := K)
  have h4 := four_le_card hn hK
  have hroot : ∀ x : K, x ^ m = 1 → x = 1 := fun x hx =>
    eq_one_of_pow_coprime hK hmo.pos.ne' hmc hx
  have hfix := SecA.factRadicalFixedG2_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hpt := factPointG2A_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hβU := mem_stabW_of_comm hfix hpt hc
  have htorus := factTorusPointG2_holds K n hn hK W hW H π hπ P hP U hU
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU1 := eq_U1_of_isFlagWG hW hf hc0 hc1 hg (by rw [hK]; exact hU)
  subst hU1
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have hU₃f : SecA.IsFlagW H P ⊥ (2 ^ n) 3 (hf.pre (gmapG g (stdF K 3)).toAddSubgroup) := by
    rw [← hK]
    exact isFlagW_preG hW hf hc0 hc1 hg (stdF_stable 3) (card_stdF (by norm_num))
  have hβU₃ := (factN13G2_holds K n hn hK W hW H ⊥ π hπ P hP _ _ hU hU₃f β (mem_stabW_bot β)
    hβH).mp hβU
  have hx0 : (q6 (1 : K) 0 0 0 0 0) ≠ 0 := fun h => one_ne_zero (congrFun h (.inl 0))
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_g2Derived hc0 hc1 _ T hT)
    hx0 β (bot_maps β) (bot_maps β⁻¹) (inv_conj_mem_of_conj_mem hβH)
  have hσid := sigma_eq_id_of_centralizesG h4 hf hc0 hc1 g (bot_maps β) hβU hβU₃ hc hσ
  set T := hf.autMap β (bot_maps β) with hTdef
  have hTf : ∀ w, T (f w) = f (β w) := hf.autMap_apply β (bot_maps β)
  have hT'f : ∀ w, hf.autMap β⁻¹ (bot_maps β⁻¹) (f w) = f (β⁻¹ w) :=
    hf.autMap_apply β⁻¹ (bot_maps β⁻¹)
  have hTs : ∀ (c : K) v, T (c • v) = c • T v := fun c v => by rw [hσ, hσid]
  let TL : (Ix3 → K) ≃ₗ[K] (Ix3 → K) :=
    { toFun := T
      invFun := hf.autMap β⁻¹ (bot_maps β⁻¹)
      map_add' := map_add T
      map_smul' := hTs
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
    have hk : β * ((rhoG hc0 hc1 π (g * γ * g⁻¹) : ↥H) : MulAut W) * β⁻¹ ∈ H :=
      hβH _ (rhoG hc0 hc1 π _).2
    obtain ⟨δ, hδ⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨_, hk⟩
    refine ⟨g⁻¹ * δ * g, fun w => ?_⟩
    obtain ⟨x, hx⟩ := hf.surj (g2Act g w)
    rw [hAapp, hAapp]
    have e1 : g2Act g (g2Act γ w) =
        f (((rhoG hc0 hc1 π (g * γ * g⁻¹) : ↥H) : MulAut W) x) := by
      rw [IsCoord.actG hf hc0 hc1, hx, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]
    have e2 : β (((rhoG hc0 hc1 π (g * γ * g⁻¹) : ↥H) : MulAut W) x) =
        ((rhoG hc0 hc1 π δ : ↥H) : MulAut W) (β x) := by
      rw [hδ]
      change _ = (β * _ * β⁻¹) (β x)
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [e1, ← hx, hTf, hTf, e2, IsCoord.actG hf hc0 hc1, g2Act_mul_apply, g2Act_mul_apply,
      g2Act_apply_inv]
  obtain ⟨c, h₀, hc0', hAeq⟩ := exists_eq_smul_of_normG2 hK hn A hA
  have hTc : ∀ v, T v = c • g2Act (g * h₀ * g⁻¹) v := by
    intro v
    have h1 := hAeq (g2Act g⁻¹ v)
    rw [hAapp, g2Act_apply_inv] at h1
    have h2 := congrArg (g2Act g) h1
    rw [g2Act_apply_inv, G2Q8.g2Act_smul] at h2
    rw [h2, g2Act_mul_apply, g2Act_mul_apply]
  have hpow : ∀ j : ℕ, ∀ w, f ((β ^ j) w) = c ^ j • g2Act ((g * h₀ * g⁻¹) ^ j) (f w) := by
    intro j
    induction j with
    | zero => intro w; rw [pow_zero, pow_zero, pow_zero, one_smul, map_one]; rfl
    | succ j ih =>
      intro w
      rw [pow_succ', MulAut.mul_apply, ← hTf, ih, hTs, hTc, smul_smul, pow_succ, pow_succ']
      simp only [g2Act_mul_apply]
  have hscal : ∀ v, g2Act ((g * h₀ * g⁻¹) ^ m) v = (c ^ m)⁻¹ • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf.surj v
    have h1 := hpow m w
    rw [hβm, MulAut.one_apply] at h1
    conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc0'), one_smul]
  have hcm : c ^ m = 1 := by
    have h1 := scalar_eq_one hscal
    rwa [inv_eq_one] at h1
  have hc1' : c = 1 := hroot c hcm
  have hseq : β = ((rhoG hc0 hc1 π (g * h₀ * g⁻¹) : ↥H) : MulAut W) := MulEquiv.ext fun w =>
    hinj _ _ (by rw [← hTf, hTc, hc1', one_smul, IsCoord.actG hf hc0 hc1])
  have hβH' : β ∈ H := by
    rw [hseq]
    exact (rhoG hc0 hc1 π _).2
  obtain ⟨d, hdU⟩ := exists_scalar_of_mem_stabG hf hc0 hc1 g ⟨hβH', hβU⟩
  obtain ⟨w₀, hw₀⟩ := hf.surj (g2Act g (eu 0 (1 : K)))
  have hw₀U : f w₀ ∈ gmapG g (stdF K 1) :=
    mem_gmapG_stdF_one_iff.mpr ⟨1, by rw [hw₀, one_smul]⟩
  have hv0 : f w₀ ≠ 0 := by
    rw [hw₀]
    exact g2Act_eu_ne_zero g
  have hdpow : ∀ j : ℕ, f ((β ^ j) w₀) = ((d : K) ^ j) • f w₀ := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, one_smul, MulAut.one_apply]
    | succ j ih =>
      rw [pow_succ' β j, MulAut.mul_apply, ← hTf, ih, hTs, hTf, hdU w₀ hw₀U, smul_smul,
        pow_succ (d : K) j]
  have hdm : (d : K) ^ m = 1 := by
    have h1 := hdpow m
    rw [hβm, MulAut.one_apply] at h1
    have h2 : ((d : K) ^ m - 1) • f w₀ = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)
  have hβw₀ : β w₀ = w₀ := hinj _ _ (by rw [hdU w₀ hw₀U, hroot _ hdm, one_smul])
  have hw₀1 : w₀ ≠ 1 := by
    rintro rfl
    exact hv0 hf.map_one
  obtain ⟨a, ha⟩ := htorus β hβH' w₀ hw₀U hw₀1 hβw₀ hc
  exact eq_one_of_odd_of_two_pow hmo hβm ha

end CFSG.Quasithin.Vol2.Ch11.SecE

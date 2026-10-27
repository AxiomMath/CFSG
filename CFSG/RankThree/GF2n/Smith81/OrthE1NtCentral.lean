module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
public import CFSG.RankThree.GF2n.Stroth80.AddAutDescent
public import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial

public section

open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80


theorem e1nt_unip_apply_apply {K E : Type} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]
    (V : Submodule K E) (g : E ≃ₗ[K] E) (β : E →ₗ[K] E) (hg : ∀ e, g e = e + β e)
    (hβV : ∀ e, β e ∈ V) (hβk : ∀ v ∈ V, β v = 0) (e : E) : g (g e) = e := by
  have h1 : β (β e) = 0 := hβk _ (hβV e)
  have h2 : β e + β e = 0 := by
    rw [← two_smul K (β e), CharTwo.two_eq_zero, zero_smul]
  calc g (g e) = (e + β e) + (β e + β (β e)) := by rw [hg e, map_add, hg e, hg (β e)]
    _ = e := by rw [h1, add_zero, add_assoc, h2, add_zero]

theorem e1nt_unip_comm {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (V : Submodule K E) (g h : E ≃ₗ[K] E) (β γ : E →ₗ[K] E) (hg : ∀ e, g e = e + β e)
    (hh : ∀ e, h e = e + γ e) (hβk : ∀ v ∈ V, β v = 0) (hγV : ∀ e, γ e ∈ V)
    (hγk : ∀ v ∈ V, γ v = 0) (hβV : ∀ e, β e ∈ V) (e : E) : g (h e) = h (g e) := by
  have h1 : β (γ e) = 0 := hβk _ (hγV e)
  have h2 : γ (β e) = 0 := hγk _ (hβV e)
  simp only [map_add, hg, hh, h1, h2, add_zero]
  abel

theorem e1nt_elemAbelian (hNt : StrothNtStatement) (hS1 : Step1Statement)
    (hKF1 : ParabolicStatement) (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G)
    (hH : E1Hyp M Q Z B t) :
    (∀ x ∈ Nt M (LB M Q B) t, ∀ y ∈ Nt M (LB M Q B) t, ⁅x, y⁆ ∈ Q) ∧
      ∀ x ∈ Nt M (LB M Q B) t, x ^ 2 ∈ Q := by
  classical
  obtain ⟨AM⟩ := ActionModel.nonempty hH.ctx.hyp
  have hc : Ctx M Q Z B := hH.ctx
  have hsec : Sec5Hyp hc 4 t := hH.sec
  obtain ⟨hE8, hhyp, hTS, hfin⟩ := hS1 G M Q Z B t hH AM
  have hq4 : 4 ≤ Nat.card AM.K := by
    have h := AM.glob.card
    have h4 := hc.hyp.q4
    omega
  have hCN : Nt M (LB M Q B) t = hc.CN t :=
    hNt G M Q Z B hc 4 hsec.width (by norm_num) hsec.noA2 hsec.gen t hsec.mem hsec.notQ
  have hNH : ∀ x ∈ Nt M (LB M Q B) t, x ∈ H0 M Z := fun x hx =>
    hc.Rt_le_H0 t ((orthE1_Nt_le_Rt M (LB M Q B) t) hx)
  have hKF := hKF1 AM.K hq4 AM.S hE8 hhyp (AM.Vsp hc t) hTS hfin
  have hfix : ∀ x (hx : x ∈ Nt M (LB M Q B) t), ∀ v ∈ AM.Vsp hc t,
      AM.φ ⟨x, hNH x hx⟩ v = v := by
    intro x hx v hv
    have hx' : x ∈ hc.CN t := by rw [← hCN]; exact hx
    obtain ⟨u, hu, huQ, rfl⟩ := mem_imgSub.mp hv
    have hcomm : ⁅x, u⁆ ∈ Z := (Ctx.mem_CN.mp hx').2 u hu
    have hZQ : ⁅x, u⁆ ∈ Q := hc.hyp.Z_normal.1 hcomm
    have hφπ : AM.M₀.π (x * u * x⁻¹) = AM.φ ⟨x, hNH x hx⟩ (AM.M₀.π u) :=
      AM.φ_π ⟨x, hNH x hx⟩ u huQ
    have hxu : x * u * x⁻¹ = ⁅x, u⁆ * u := by
      rw [commutatorElement_def]; group
    have hz : AM.M₀.π ⁅x, u⁆ = 0 := (AM.M₀.π_ker _ hZQ).mpr hcomm
    rw [← hφπ, hxu, AM.M₀.π_mul _ hZQ u huQ, hz, zero_add]
  have hunip : ∀ x (hx : x ∈ Nt M (LB M Q B) t), ∃ β : AM.M₀.E →ₗ[AM.K] AM.M₀.E,
      (∀ e, β e ∈ AM.Vsp hc t) ∧ (∀ v ∈ AM.Vsp hc t, β v = 0) ∧
        (∀ e, AM.S.B e (β e) = 0) ∧ ∀ e, AM.φ ⟨x, hNH x hx⟩ e = e + β e := by
    intro x hx
    have hU : AM.φ ⟨x, hNH x hx⟩ ∈ AM.S.U (AM.Vsp hc t) :=
      ⟨fun e => AM.φ_Qf ⟨x, hNH x hx⟩ e, fun v hv => hfix x hx v hv⟩
    exact (hKF.2.2.1 _).mp hU
  have hcomm_sq : ∀ x (hx : x ∈ Nt M (LB M Q B) t) y (hy : y ∈ Nt M (LB M Q B) t),
      AM.φ ⟨x, hNH x hx⟩ * AM.φ ⟨y, hNH y hy⟩ = AM.φ ⟨y, hNH y hy⟩ * AM.φ ⟨x, hNH x hx⟩ := by
    intro x hx y hy
    obtain ⟨β, hβV, hβk, -, hβg⟩ := hunip x hx
    obtain ⟨γ, hγV, hγk, -, hγg⟩ := hunip y hy
    refine LinearEquiv.ext fun e => ?_
    simp only [LinearEquiv.mul_apply]
    exact e1nt_unip_comm (AM.Vsp hc t) _ _ β γ hβg hγg hβk hγV hγk hβV e
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h1 : AM.φ ⁅(⟨x, hNH x hx⟩ : ↥(H0 M Z)), ⟨y, hNH y hy⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm_sq x hx y hy
    have h3 := (AM.φ_ker _).mp h1
    simpa [commutatorElement_def] using h3
  · have h1 : AM.φ ((⟨x, hNH x hx⟩ : ↥(H0 M Z)) ^ 2) = 1 := by
      obtain ⟨β, hβV, hβk, -, hβg⟩ := hunip x hx
      rw [map_pow, pow_two]
      refine LinearEquiv.ext fun e => ?_
      rw [LinearEquiv.mul_apply]
      exact e1nt_unip_apply_apply (AM.Vsp hc t) _ β hβg hβV hβk e
    have h3 := (AM.φ_ker _).mp h1
    simpa using h3

theorem e1nt_ppd_not_dvd_prod (p k : ℕ) (hp : CFSG.Timmesfeld.IsPrimitivePrimeDivisor p (4 * k))
    (hk : 0 < k) : ¬ p ∣ ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) := by
  intro h
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hp.1.prime _).mp h
  have hik : (i : ℕ) < k := i.2
  have e : 2 ^ k - 2 ^ (i : ℕ) = 2 ^ (i : ℕ) * (2 ^ (k - (i : ℕ)) - 1) := by
    have h2 : 2 ^ k = 2 ^ (i : ℕ) * 2 ^ (k - (i : ℕ)) := by
      rw [← pow_add]; congr 1; omega
    rw [h2, Nat.mul_sub_one]
  rw [e] at hi
  rcases (Nat.Prime.dvd_mul hp.1).mp hi with h1 | h1
  · have h2 : p ∣ 2 := hp.1.dvd_of_dvd_pow h1
    have h3 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).mp h2
    exact hp.ne_two (by omega) h3
  · have h4 : 4 * k ∣ k - (i : ℕ) := (hp.dvd_sub_one_iff (by omega) _).mp h1
    have h5 : 4 * k ≤ k - (i : ℕ) := Nat.le_of_dvd (by omega) h4
    omega

theorem e1nt_card_addAut (Mv : Type) [AddCommGroup Mv] [Finite Mv] (hM2 : ∀ y : Mv, y + y = 0)
    (k : ℕ) (hMk : Nat.card Mv = 2 ^ k) :
    Nat.card (AddAut Mv) = ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) := by
  letI : Module (ZMod 2) Mv :=
    AddCommGroup.zmodModule (n := 2) fun x => (two_nsmul x).trans (hM2 x)
  have hfin : Module.finrank (ZMod 2) Mv = k := by
    have h : Nat.card Mv = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) Mv :=
      Module.natCard_eq_pow_finrank
    rw [hMk, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let e : (Mv ≃+ Mv) ≃ (Mv ≃ₗ[ZMod 2] Mv) :=
    { toFun := fun f =>
        { toLinearMap := f.toAddMonoidHom.toZModLinearMap 2
          invFun := f.symm
          left_inv := fun x => f.symm_apply_apply x
          right_inv := fun x => f.apply_symm_apply x }
      invFun := fun ℓ => ℓ.toAddEquiv
      left_inv := fun f => by ext x; rfl
      right_inv := fun ℓ => by ext x; rfl }
  show Nat.card (Mv ≃+ Mv) = _
  rw [Nat.card_congr e]
  classical
  let b : Module.Basis (Fin k) (ZMod 2) Mv := Module.finBasisOfFinrankEq (ZMod 2) Mv hfin
  let g : GL (Fin k) (ZMod 2) ≃* (Mv ≃ₗ[ZMod 2] Mv) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Mv)
  rw [← Nat.card_congr g.toEquiv, Matrix.card_GL_field, ZMod.card]

theorem e1nt_plus_trivial (K : Type) [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    (Mv : Type) [AddCommGroup Mv] [Finite Mv] (hM2 : ∀ y : Mv, y + y = 0)
    (hMq : Nat.card Mv ≤ Nat.card K)
    (π : ↥(StatedOmega (StatedQuadPlus 2 K)) →* Multiplicative (AddAut Mv)) : π = 1 := by
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  obtain ⟨ι⟩ := nonempty_statedSp_one_mulEquiv_statedSL_two K
  have h1 := hom_statedSp_to_addAut_trivial (K := K) (m := 1) hM2 hMq
    (π.comp (e.symm.toMonoidHom.comp
      ((MonoidHom.inl ↥(StatedSL 2 K) ↥(StatedSL 2 K)).comp ι.toMonoidHom)))
  have h2 := hom_statedSp_to_addAut_trivial (K := K) (m := 1) hM2 hMq
    (π.comp (e.symm.toMonoidHom.comp
      ((MonoidHom.inr ↥(StatedSL 2 K) ↥(StatedSL 2 K)).comp ι.toMonoidHom)))
  have key : ∀ x : ↥(StatedOmega (StatedQuadPlus 2 K)),
      x = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
    intro x
    rw [← map_mul]
    simp
  refine MonoidHom.ext fun x => ?_
  have f1 : π (e.symm ((e x).1, 1)) = 1 := by
    have := DFunLike.congr_fun h1 (ι.symm (e x).1)
    simpa using this
  have f2 : π (e.symm (1, (e x).2)) = 1 := by
    have := DFunLike.congr_fun h2 (ι.symm (e x).2)
    simpa using this
  rw [MonoidHom.one_apply, key x, map_mul, f1, f2, one_mul]

open CFSG.ComponentClassification.RankTwoClassical in
theorem e1nt_minus_trivial (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ)
    (hn : Nat.card K = 2 ^ n) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Mv : Type) [AddCommGroup Mv] [Finite Mv] (hM2 : ∀ y : Mv, y + y = 0)
    (hMq : Nat.card Mv = Nat.card K)
    (π : ↥(StatedOmega (StatedQuadMinus 2 K b c)) →* Multiplicative (AddAut Mv)) : π = 1 := by
  haveI := ORigid.isSimpleGroup_statedOmega_quadMinus_of_two_le (K := K) (b := b) (c := c)
    (le_refl 2) hirr
  have hΩ := card_statedOmega_minus_eq_of_two_le (K := K) (m := 2) (le_refl 2) hirr
  have hΩ' : (Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ 2 * (((Nat.card K : ℤ) ^ 2 + 1) * ((Nat.card K : ℤ) ^ 2 - 1)) := by
    rw [hΩ]
    norm_num
    ring
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hn; omega
    · exact h0
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * n)
    (by omega) (by omega)
  have hpZ : (p : ℤ) ∣ ((Nat.card K : ℤ) ^ 2 + 1) * ((Nat.card K : ℤ) ^ 2 - 1) := by
    have hq' : (Nat.card K : ℤ) = 2 ^ n := by rw [hn]; push_cast; ring
    have h1 : ((2 ^ (4 * n) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (4 * n) - 1 := by
      push_cast [Nat.one_le_two_pow]; ring
    have h2 : (p : ℤ) ∣ ((2 ^ (4 * n) - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hp.2.1
    rw [h1] at h2
    have h3 : ((Nat.card K : ℤ) ^ 2 + 1) * ((Nat.card K : ℤ) ^ 2 - 1) =
        (2 : ℤ) ^ (4 * n) - 1 := by
      rw [hq']; ring
    rw [h3]
    exact h2
  have hdvdΩ : p ∣ Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) := by
    have h : (p : ℤ) ∣ (Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) : ℤ) := by
      rw [hΩ']
      exact Dvd.dvd.mul_left hpZ _
    exact Int.natCast_dvd_natCast.mp h
  haveI : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvdΩ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (π.ker) with hker | hker
  · exfalso
    have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
    have h1 : orderOf (π x) = p := (orderOf_injective π hinj x).trans hx
    have h2 : p ∣ Nat.card (AddAut Mv) := by
      have h3 := orderOf_dvd_natCard (π x)
      rw [h1] at h3
      rw [Nat.card_congr (Multiplicative.ofAdd (α := AddAut Mv))]
      exact h3
    rw [e1nt_card_addAut Mv hM2 n (hMq.trans hn)] at h2
    exact e1nt_ppd_not_dvd_prod p n hp (by omega) h2
  · refine MonoidHom.ext fun g => ?_
    have hg : g ∈ π.ker := by rw [hker]; exact Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at hg
    rw [hg, MonoidHom.one_apply]

theorem e1nt_normP {G : Type} [Group G] (M L : Subgroup G) (t : G) (r : G)
    (hr : r ∈ Rt M L t) (x : G) (hx : x ∈ Nt M L t) : r * x * r⁻¹ ∈ Nt M L t := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr ⟨⟨r, hr⟩ * y * (⟨r, hr⟩ : ↥(Rt M L t))⁻¹,
    (pCore_normal (p := 2) (G := ↥(Rt M L t))).conj_mem y hy ⟨r, hr⟩, rfl⟩

theorem e1nt_secHyp (hNt : StrothNtStatement) (hS1 : Step1Statement) (hKF1 : ParabolicStatement)
    (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G) (hH : E1Hyp M Q Z B t) :
    SecHyp (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) Q := by
  have hc : Ctx M Q Z B := hH.ctx
  have hsec : Sec5Hyp hc 4 t := hH.sec
  have hCN : Nt M (LB M Q B) t = hc.CN t :=
    hNt G M Q Z B hc 4 hsec.width (by norm_num) hsec.noA2 hsec.gen t hsec.mem hsec.notQ
  obtain ⟨hcomm, hsq⟩ := e1nt_elemAbelian hNt hS1 hKF1 G M Q Z B t hH
  refine ⟨?_, hcomm, hsq, fun r hr x hx => e1nt_normP M (LB M Q B) t r hr x hx, ?_⟩
  · intro x hx
    rw [hCN]
    exact hc.Q_le_CN hsec.mem hx
  · intro r hr x hx
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) x).mp hx

theorem e1nt_ker_act {G : Type} [Group G] {R P I : Subgroup G} {Mv : Type} [AddCommGroup Mv]
    [DistribMulAction ↥R Mv] {κ : ↥P →* Multiplicative Mv} (hκ : IsSecMod R P I Mv κ)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ I) (x : ↥R) (hx : (x : G) ∈ P) (a : Mv) :
    x • a = a := by
  obtain ⟨y, hy⟩ := hκ.surj (Multiplicative.ofAdd a)
  have hyP : (y : G) ∈ P := y.2
  have hmem : (x : G) * (y : G) * (x : G)⁻¹ ∈ P := hP x x.2 y hyP
  have hk := hκ.act x y ⟨(x : G) * y * (x : G)⁻¹, hmem⟩ rfl
  have hq : κ ⟨(x : G) * y * (x : G)⁻¹, hmem⟩ = κ y := by
    refine (hκ.eq_iff _ _).mpr ?_
    have h := hcomm x hx y hyP
    rw [commutatorElement_def] at h
    exact h
  rw [hq, hy] at hk
  have h2 := congrArg Multiplicative.toAdd hk
  simpa using h2.symm

theorem e1nt_comm_of_act {G : Type} [Group G] {R P I : Subgroup G} {Mv : Type}
    [AddCommGroup Mv] [DistribMulAction ↥R Mv] {κ : ↥P →* Multiplicative Mv}
    (hκ : IsSecMod R P I Mv κ) (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hact : ∀ (r : ↥R) (a : Mv), r • a = a) (r : G) (hr : r ∈ R) (n : G) (hn : n ∈ P) :
    ⁅r, n⁆ ∈ I := by
  have hk := hκ.act ⟨r, hr⟩ ⟨n, hn⟩ ⟨r * n * r⁻¹, hP r hr n hn⟩ rfl
  rw [hact] at hk
  simp only [ofAdd_toAdd] at hk
  have h := (hκ.eq_iff _ _).mp hk
  rw [commutatorElement_def]
  exact h

theorem e1nt_act_of_hom {G : Type} [Group G] {R P I : Subgroup G} {Mv : Type} [AddCommGroup Mv]
    [DistribMulAction ↥R Mv] {κ : ↥P →* Multiplicative Mv} {H : Type} [Group H]
    (hκ : IsSecMod R P I Mv κ) (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ I) (φ : ↥R →* H) (S : Subgroup H)
    (hrange : φ.range = S) (hker : φ.ker = P.subgroupOf R)
    (htriv : ∀ π : ↥S →* Multiplicative (AddAut Mv), π = 1) (x : ↥R) (a : Mv) :
    x • a = a := by
  obtain ⟨π, hπ⟩ := exists_addAut_hom_of_range φ hrange fun y hy b => e1nt_ker_act hκ hP hcomm y
    (by rw [hker] at hy; exact Subgroup.mem_subgroupOf.mp hy) b
  have hx : φ x ∈ S := by
    rw [← hrange]
    exact ⟨x, rfl⟩
  have h1 : π ⟨φ x, hx⟩ a = a := by rw [htriv π]; rfl
  rw [hπ x hx a] at h1
  exact h1

theorem ntCentral_of (hNt : StrothNtStatement) (hN : E1NaturalStatement) (hS1 : Step1Statement)
    (hKF1 : ParabolicStatement) : NtCentralStatement := by
  intro G _ _ M Q Z B t hH r hr n hn
  have hc : Ctx M Q Z B := hH.ctx
  have hsec : Sec5Hyp hc 4 t := hH.sec
  have hCN : Nt M (LB M Q B) t = hc.CN t :=
    hNt G M Q Z B hc 4 hsec.width (by norm_num) hsec.noA2 hsec.gen t hsec.mem hsec.notQ
  obtain ⟨hcomm, -⟩ := e1nt_elemAbelian hNt hS1 hKF1 G M Q Z B t hH
  have hPn : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ Nt M (LB M Q B) t,
      r * x * r⁻¹ ∈ Nt M (LB M Q B) t := fun r hr x hx => e1nt_normP M (LB M Q B) t r hr x hx
  obtain ⟨Mv, hAdd, hAct, κ, hκ⟩ := exists_sectionModule (e1nt_secHyp hNt hS1 hKF1 G M Q Z B t hH)
  obtain ⟨hN1, hN2⟩ := hN G M Q Z B t hH
  obtain ⟨h9, hNcard, hsign⟩ := hH.case
  have hQN : Q ≤ Nt M (LB M Q B) t := by
    intro x hx
    rw [hCN]
    exact hc.Q_le_CN hsec.mem hx
  have hMcard : Nat.card Mv = Nat.card Z := by
    have h1 := natCard_eq_of_isSecMod hQN hκ
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hQpos (hNcard.symm.trans h1)).symm
  have hM2 : ∀ y : Mv, y + y = 0 := hκ.two
  haveI : Finite Mv := hκ.finite
  rcases hsign with hP | hM
  ·
    obtain ⟨K, fK, finK, hKZ, φR, hrange, hker, -⟩ :=
      hN1 (by unfold CaseE1Plus; exact ⟨h9, hNcard, hP⟩)
    obtain ⟨k, -, hZk, -⟩ := hc.hyp.cp
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (k := k) (hKZ.trans hZk)
    have hq4 : 4 ≤ Nat.card K := by rw [hKZ]; exact hc.hyp.q4
    have hact : ∀ (x : ↥(Rt M (LB M Q B) t)) (a : Mv), x • a = a :=
      e1nt_act_of_hom hκ hPn hcomm φR _ hrange (by rw [hker, hCN])
        (fun π => e1nt_plus_trivial K hq4 Mv hM2 (by rw [hMcard, hKZ]) π)
    exact e1nt_comm_of_act hκ hPn hact r hr n hn
  ·
    obtain ⟨K, fK, finK, hKZ, b, c, hirr, φR, hrange, hker, -⟩ :=
      hN2 (by unfold CaseE1Minus; exact ⟨h9, hNcard, hM⟩)
    obtain ⟨k, -, hZk, -⟩ := hc.hyp.cp
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (k := k) (hKZ.trans hZk)
    have hq4 : 4 ≤ Nat.card K := by rw [hKZ]; exact hc.hyp.q4
    have hact : ∀ (x : ↥(Rt M (LB M Q B) t)) (a : Mv), x • a = a :=
      e1nt_act_of_hom hκ hPn hcomm φR _ hrange (by rw [hker, hCN])
        (fun π => e1nt_minus_trivial K k (hKZ.trans hZk) hq4 hirr Mv hM2
          (by rw [hMcard, hKZ]) π)
    exact e1nt_comm_of_act hκ hPn hact r hr n hn

end CFSG.RankThree.GF2n.Smith81.Smith23E1

module

public import CFSG.RankThree.PartOne.KFR4.FrmJoint
public import CFSG.RankThree.PartOne.KFR4.Std
public import CFSG.RankThree.PartOne.S11d.OrthModels

public section

namespace CFSG.RankThree.PartOne.KFR4

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.K159 CFSG.GroupTheory.WeirSylow

namespace Frm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}

theorem isPlusType_fixed_of_finrank_two {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hdim : finrank K V = 8)
    (hV : ¬ IsPlusType Q) (h2 : finrank K (fixedSpace x) = 2) :
    IsPlusType (Q.comp (fixedSpace x).subtype) := by
  classical
  obtain ⟨hcompl, horth⟩ := hx.fixed_others
  set W := fixedSpace x with hW
  set R := othersSpace x.toLinearMap (X - 1) with hR
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  have hRinv : ∀ u ∈ R, x u ∈ R := by
    intro u hu
    have hmap : R.map x.toLinearMap ≤ R := by
      rw [hR]
      unfold othersSpace
      rw [Submodule.map_iSup]
      refine iSup_le fun k => ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun hk => ?_
      refine le_iSup₂_of_le k hk ?_
      rintro _ ⟨v, hv, rfl⟩
      exact apply_mem_primaryComponent (Commute.refl _) hv
    exact hmap ⟨u, hu, rfl⟩
  have hRfix : ∀ u ∈ R, x u = u → u = 0 := fun u hu hxu =>
    (Submodule.disjoint_def.1 hcompl.disjoint) u (mem_fixedSpace.2 hxu) hu
  have hRreg : RegOn Q R := by
    intro u hu hperp
    refine hx.regular u fun v => ?_
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
    rw [QuadraticMap.polar_add_right, hperp r hr, QuadraticMap.polar_comm Q u w,
      horth w hw u hu, add_zero]
  have hRdim : finrank K R = 2 * 3 := by omega
  have hRtype := isPlusType_iff_even_of_fixedFree hx hp hp2 hpq 3 R hRinv hRreg hRfix hRdim
  let eTop : Q.IsometryEquiv (Q.comp (⊤ : Submodule K V).subtype) :=
    { toLinearEquiv := (LinearEquiv.ofTop ⊤ rfl).symm
      map_app' := fun _ => rfl }
  have eV : Q.IsometryEquiv ((Q.comp W.subtype).prod (Q.comp R.subtype)) :=
    eTop.trans ((isometryOfEq Q hcompl.sup_eq_top.symm).trans
      (isometryEquivSup Q W R hcompl.disjoint horth))
  have htype : IsPlusType Q ↔ (IsPlusType (Q.comp W.subtype) ↔ IsPlusType (Q.comp R.subtype)) :=
    (isPlusType_congr eV).trans
      (isPlusType_prod_iff hx.polarBilin_fixed_nondegenerate (nondegenerate_of_regOn hRreg)
        (d₁ := 1) (d₂ := 3) le_rfl (by norm_num) (by omega) hRdim)
  by_contra hW
  apply hV
  rw [htype]
  exact ⟨fun h => absurd h hW, fun h => absurd (hRtype.1 h) (by decide)⟩

theorem exists_frame_data (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8)
    (hV : ¬ IsPlusType Q) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    {E₀ : Subgroup (V ≃ₗ[K] V)} (hE₀O : E₀ ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcard : Nat.card E₀ = p ^ 3) (hexp : ∀ g ∈ E₀, g ^ p = 1)
    (hcomm : ∀ g ∈ E₀, ∀ h ∈ E₀, g * h = h * g) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (D : EvenNormPlane K E) (ζ : E)
      (φ : Fin 3 → E →ₗ[K] V) (h₁ h₂ : V) (c : E₀ → Fin 3 → ZMod p),
      orderOf ζ = p ∧
      (∀ i z, Q (φ i z) = D.N z) ∧
      (∀ i j, i ≠ j → ∀ z w, polar Q (φ i z) (φ j w) = 0) ∧
      (∀ i z, polar Q (φ i z) h₁ = 0) ∧ (∀ i z, polar Q (φ i z) h₂ = 0) ∧
      Q h₁ = 0 ∧ Q h₂ = 0 ∧ polar Q h₁ h₂ = 1 ∧
      (∀ g : E₀, g.1 h₁ = h₁) ∧ (∀ g : E₀, g.1 h₂ = h₂) ∧
      (∀ g : E₀, ∀ i z, g.1 (φ i z) = φ i (ζ ^ (c g i).val * z)) ∧
      Function.Bijective c := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have H : Hyp Q p E₀ := ⟨fun v hv => hQ.1 v fun w => by rw [polarBilin_apply_apply]; exact hv w,
    hp, by omega, hpq, hE₀O, hexp, hcomm⟩
  have hts : ∀ U : Submodule K V, finrank K U = 4 → ∃ u ∈ U, Q u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hV ⟨U, by omega, hcon⟩
  obtain ⟨E, _, _, D, -, -⟩ := exists_evenMinus_model Q hQ (n := 4) (by norm_num) (by omega) hts
  have : Finite E := D.finite_E
  have hpE : p ∣ Nat.card Eˣ := by
    rw [Nat.card_units, D.card_E]
    have hq : 1 ≤ Nat.card K := Nat.card_pos
    have h1 : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      obtain ⟨a, ha⟩ : ∃ a, Nat.card K = a + 1 := ⟨Nat.card K - 1, by omega⟩
      rw [ha]
      simp only [Nat.add_sub_cancel]
      apply Nat.sub_eq_of_eq_add
      ring
    rw [h1]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpE
  obtain ⟨ζ, hζ⟩ : ∃ ζ : E, orderOf ζ = p := ⟨u, by rw [orderOf_units]; exact hu⟩
  obtain ⟨I, hI, φ, c, hinj, hnorm, horth, horth0, hspan, hchar⟩ :=
    H.exists_decomp D.finrank_eq hζ
  have hQφ : ∀ i z, Q (φ i z) = D.N z := fun i z => (algebraMap K E).injective (by
    rw [hnorm, D.algebraMap_N, D.sigma_eq_pow])
  have hpolφ : ∀ i z w, polar Q (φ i z) (φ i w) = polar D.N z w := by
    intro i z w
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hQφ, hQφ, hQφ]
  have hspan' : ∀ v : V, v ∈ W E₀ 0 ⊔ ⨆ i, LinearMap.range (φ i) := fun v => by
    rw [hspan]; trivial
  have hc_inj : Function.Injective c := by
    intro g h hgh
    have hle : W E₀ 0 ⊔ (⨆ i, LinearMap.range (φ i)) ≤
        LinearMap.eqLocus g.1.toLinearMap h.1.toLinearMap := by
      refine sup_le (fun w hw => ?_) (iSup_le fun i => ?_)
      · rw [LinearMap.mem_eqLocus]
        simp only [LinearEquiv.coe_coe]
        rw [H.apply_eq_of_mem_W_zero g.2 hw, H.apply_eq_of_mem_W_zero h.2 hw]
      · rintro _ ⟨z, rfl⟩
        rw [LinearMap.mem_eqLocus]
        simp only [LinearEquiv.coe_coe]
        rw [hchar, hchar, hgh]
    exact Subtype.ext (LinearEquiv.ext fun v => LinearMap.mem_eqLocus.1 (hle (hspan' v)))
  have hI3 : 3 ≤ Fintype.card I := by
    have h1 : Nat.card E₀ ≤ Nat.card (I → ZMod p) := Nat.card_le_card_of_injective c hc_inj
    rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  have hQadd : ∀ x y : V, polar Q x y = 0 → Q (x + y) = Q x + Q y := fun x y h => by
    rw [QuadraticMap.map_add Q x y, h, add_zero]
  have hcoordN : ∀ z : E, (∀ u, polar D.N z u = 0) → z = 0 := by
    intro z h
    by_contra hz
    obtain ⟨u, hu⟩ := polar_N_ne_zero D hz
    exact hu (h u)
  have hI4 : Fintype.card I ≤ 3 := by
    by_contra h4
    push Not at h4
    let j : Fin 4 ↪ I := (Fin.castLEEmb (by omega)).trans (Fintype.equivFin I).symm.toEmbedding
    have hj : ∀ a b : Fin 4, a ≠ b → j a ≠ j b := fun a b hab h => hab (j.injective h)
    let T : (E × E) →ₗ[K] V := (φ (j 0) + φ (j 1)).comp (LinearMap.fst K E E) +
      (φ (j 2) + φ (j 3)).comp (LinearMap.snd K E E)
    have hT : ∀ x : E × E, T x = φ (j 0) x.1 + φ (j 1) x.1 + (φ (j 2) x.2 + φ (j 3) x.2) :=
      fun x => rfl
    have hTs : ∀ x, Q (T x) = 0 := by
      intro x
      have hp1 : polar Q (φ (j 0) x.1 + φ (j 1) x.1) (φ (j 2) x.2 + φ (j 3) x.2) = 0 := by
        rw [polar_add_left, polar_add_right, polar_add_right, horth _ _ (hj 0 2 (by decide)),
          horth _ _ (hj 0 3 (by decide)), horth _ _ (hj 1 2 (by decide)),
          horth _ _ (hj 1 3 (by decide))]
        ring
      rw [hT, hQadd _ _ hp1, hQadd _ _ (horth _ _ (hj 0 1 (by decide)) _ _),
        hQadd _ _ (horth _ _ (hj 2 3 (by decide)) _ _), hQφ, hQφ, hQφ, hQφ,
        CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    have hTinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨z, w⟩ hzw
      rw [hT] at hzw
      have hz : z = 0 := hcoordN z fun u => by
        have := congrArg (fun v => polar Q v (φ (j 0) u)) hzw
        simp only [polar_add_left, polar_zero_left, horth _ _ (hj 1 0 (by decide)),
          horth _ _ (hj 2 0 (by decide)), horth _ _ (hj 3 0 (by decide)), add_zero] at this
        rwa [hpolφ] at this
      have hw : w = 0 := hcoordN w fun u => by
        have := congrArg (fun v => polar Q v (φ (j 2) u)) hzw
        simp only [polar_add_left, polar_zero_left, horth _ _ (hj 0 2 (by decide)),
          horth _ _ (hj 1 2 (by decide)), horth _ _ (hj 3 2 (by decide)), add_zero,
          zero_add] at this
        rwa [hpolφ] at this
      rw [hz, hw]
      rfl
    apply hV
    refine ⟨LinearMap.range T, ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hTinj, Module.finrank_prod, D.finrank_eq, hdim]
    · rintro _ ⟨x, rfl⟩
      exact hTs x
  have hI : Fintype.card I = 3 := le_antisymm hI4 hI3
  have : Module.Finite K E := Module.finite_of_finrank_pos (by rw [D.finrank_eq]; omega)
  let Ψ : (W E₀ 0 × (I → E)) →ₗ[K] V :=
    (W E₀ 0).subtype.coprod (∑ i, (φ i).comp (LinearMap.proj i))
  have hΨ : ∀ (w : W E₀ 0) (z : I → E), Ψ (w, z) = (w : V) + ∑ i, φ i (z i) := by
    intro w z
    simp [Ψ, LinearMap.coprod_apply, LinearMap.sum_apply]
  have hpair : ∀ (w : W E₀ 0) (z : I → E) (i : I) (u : E),
      polar Q (Ψ (w, z)) (φ i u) = polar D.N (z i) u := by
    intro w z i u
    have hs := map_sum ((polarBilin Q).flip (φ i u)) (fun k => φ k (z k)) Finset.univ
    simp only [LinearMap.flip_apply, polarBilin_apply_apply] at hs
    rw [hΨ, polar_add_left, polar_comm Q (w : V), horth0 i u w w.2, zero_add, hs,
      Finset.sum_eq_single i (fun k _ hk => horth k i hk _ _) (by simp), hpolφ]
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w, z⟩ hwz
    have hz : z = 0 := funext fun i => hcoordN _ fun u => by
      rw [← hpair w z i u, hwz, polar_zero_left]
    subst hz
    have hw : (w : V) = 0 := by
      rw [hΨ] at hwz
      simpa using hwz
    exact Prod.ext (Subtype.ext hw) rfl
  have hΨsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan]
    refine sup_le (fun w hw => ⟨(⟨w, hw⟩, 0), by rw [hΨ]; simp⟩) (iSup_le fun i => ?_)
    rintro _ ⟨z, rfl⟩
    refine ⟨(0, Pi.single i z), ?_⟩
    rw [hΨ, Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero])
      (by simp), Pi.single_eq_same]
    simp
  have hW0 : finrank K (W E₀ 0) = 2 := by
    have h1 := (LinearEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩).finrank_eq
    rw [Module.finrank_prod, Module.finrank_pi_fintype, hdim] at h1
    simp only [D.finrank_eq, Finset.sum_const, Finset.card_univ, hI, smul_eq_mul] at h1
    omega
  let e : Fin 3 ≃ I := (Fintype.equivFinOfCardEq hI).symm
  let c' : E₀ → Fin 3 → ZMod p := fun g k => c g (e k)
  have hc'inj : Function.Injective c' := by
    intro g h hgh
    refine hc_inj (funext fun i => ?_)
    have := congrFun hgh (e.symm i)
    simpa [c'] using this
  have hc'bij : Function.Bijective c' := hc'inj.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin])
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  obtain ⟨x, hx⟩ := hc'bij.2 (fun _ => 1)
  have hcx : ∀ i, c x i = 1 := fun i => by
    have := congrFun hx (e.symm i)
    simpa [c'] using this
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hfixW : fixedSpace x.1 = W E₀ 0 := by
    refine le_antisymm (fun v hv => ?_)
      (fun v hv => mem_fixedSpace.2 (H.apply_eq_of_mem_W_zero x.2 hv))
    rw [mem_fixedSpace] at hv
    obtain ⟨⟨w, z⟩, rfl⟩ := hΨsurj v
    have h1 : x.1 (Ψ (w, z)) = Ψ (w, fun i => ζ * z i) := by
      rw [hΨ, hΨ, map_add, map_sum, H.apply_eq_of_mem_W_zero x.2 w.2]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hchar, hcx, ZMod.val_one, pow_one]
    rw [h1] at hv
    have h2 := hΨinj hv
    have hz : z = 0 := funext fun i => by
      have h3 : ζ * z i = z i := congrFun (congrArg Prod.snd h2) i
      have h4 : (ζ - 1) * z i = 0 := by rw [sub_mul, h3, one_mul, sub_self]
      exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hζ1)
    rw [hz, hΨ]
    simp
  have hfin2 : finrank K (fixedSpace x.1) = 2 := by rw [hfixW]; exact hW0
  obtain ⟨T, hT, hTs⟩ :=
    isPlusType_fixed_of_finrank_two (H.odd x.2) hp H.ne_two hpq hdim hV hfin2
  have hT1 : finrank K T = 1 := by omega
  have hTne : T ≠ ⊥ := by
    rintro rfl
    simp at hT1
  obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
  have hQt : Q (t : V) = 0 := hTs t htT
  have ht1 : (t : V) ∈ W E₀ 0 := hfixW ▸ t.2
  have ht0' : (t : V) ≠ 0 := fun h => ht0 (Subtype.ext h)
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ W E₀ 0, polar Q (t : V) w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ht0' (H.regOn_W 0 _ ht1 hcon)
  obtain ⟨w', hw'W, hw'1⟩ : ∃ w' ∈ W E₀ 0, polar Q (t : V) w' = 1 :=
    ⟨_, (W E₀ 0).smul_mem _ hw, by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hw0]⟩
  have htt : polar Q (t : V) (t : V) = 0 := polar_self_zero _
  have hQ2 : Q (w' + Q w' • (t : V)) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, hQt, polar_smul_right, polar_comm Q w',
      hw'1]
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
    exact CharTwo.add_self_eq_zero _
  have hpol12 : polar Q (t : V) (w' + Q w' • (t : V)) = 1 := by
    rw [polar_add_right, polar_smul_right, htt, smul_zero, add_zero, hw'1]
  have hh₂W : w' + Q w' • (t : V) ∈ W E₀ 0 := (W E₀ 0).add_mem hw'W ((W E₀ 0).smul_mem _ ht1)
  refine ⟨E, inferInstance, inferInstance, D, ζ, fun k => φ (e k), t, w' + Q w' • (t : V), c', hζ,
    fun i z => hQφ _ z, fun i j hij z w => horth _ _ (e.injective.ne hij) z w,
    fun i z => horth0 _ z _ ht1, fun i z => horth0 _ z _ hh₂W, hQt, hQ2, hpol12,
    fun g => H.apply_eq_of_mem_W_zero g.2 ht1, fun g => H.apply_eq_of_mem_W_zero g.2 hh₂W,
    fun g i z => hchar g (e i) z, hc'bij⟩

end Frm

section Frame

open Module CFSG.RankThree.PartOne

theorem exists_frame {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8)
    (hV : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) (E₀ : Subgroup (V ≃ₗ[K] V))
    (hE₀O : E₀ ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hcard : Nat.card E₀ = p ^ 3)
    (hexp : ∀ g ∈ E₀, g ^ p = 1) (hcomm : ∀ g ∈ E₀, ∀ h ∈ E₀, g * h = h * g) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Module.Finite K E) (S : StdData K E p)
      (Φ : (Qs S.D).IsometryEquiv Q),
      (Tstd S).map (linConj Φ.toLinearEquiv).toMonoidHom = E₀ := by
  obtain ⟨E, _, _, D, ζ, φ, h₁, h₂, c, hζ, hQφ, horth, horth1, horth2, hQ1, hQ2, hpol12, hfix1,
    hfix2, hchar, hcbij⟩ := Frm.exists_frame_data hQ hdim hV hp hp5 hpq hE₀O hcard hexp hcomm
  have hfin : Module.Finite K E := Module.finite_of_finrank_pos (by rw [D.finrank_eq]; omega)
  obtain ⟨S, hSD, hSζ⟩ : ∃ S : StdData K E p, S.D = D ∧ S.ζ = ζ :=
    ⟨⟨D, hp, hp5, hpq, ζ, hζ ▸ IsPrimitiveRoot.orderOf ζ⟩, rfl, rfl⟩
  subst hSD hSζ
  let Φl : Vs K E →ₗ[K] V := (∑ k : Fin 3, (φ k).comp (LinearMap.proj k)).coprod
    ((LinearMap.toSpanSingleton K V h₁).coprod (LinearMap.toSpanSingleton K V h₂))
  have hΦl : ∀ v : Vs K E, Φl v = ∑ k, φ k (v.1 k) + (v.2.1 • h₁ + v.2.2 • h₂) := by
    intro v
    simp [Φl, LinearMap.coprod_apply, LinearMap.sum_apply]
  have hQadd : ∀ x y : V, polar Q x y = 0 → Q (x + y) = Q x + Q y := fun x y h => by
    rw [QuadraticMap.map_add Q x y, h, add_zero]
  have hΦQ : ∀ v, Q (Φl v) = Qs S.D v := by
    intro v
    have hpH : ∀ k z, polar Q (φ k z) (v.2.1 • h₁ + v.2.2 • h₂) = 0 := by
      intro k z
      rw [polar_add_right, polar_smul_right, polar_smul_right, horth1, horth2]
      simp
    have hpA : polar Q (φ 0 (v.1 0) + φ 1 (v.1 1) + φ 2 (v.1 2))
        (v.2.1 • h₁ + v.2.2 • h₂) = 0 := by
      rw [polar_add_left, polar_add_left, hpH, hpH, hpH]
      simp
    have hp2 : polar Q (φ 0 (v.1 0) + φ 1 (v.1 1)) (φ 2 (v.1 2)) = 0 := by
      rw [polar_add_left, horth 0 2 (by decide), horth 1 2 (by decide), add_zero]
    rw [hΦl, Qs_apply, Fin.sum_univ_three, Fin.sum_univ_three, hQadd _ _ hpA, hQadd _ _ hp2,
      hQadd _ _ (horth 0 1 (by decide) _ _), hQφ, hQφ, hQφ, QuadraticMap.map_add Q,
      QuadraticMap.map_smul Q, QuadraticMap.map_smul Q, polar_smul_left, polar_smul_right, hQ1,
      hQ2, hpol12]
    simp
  have hΦpol : ∀ v w, polar Q (Φl v) (Φl w) = polar (Qs S.D) v w := by
    intro v w
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hΦQ, hΦQ, hΦQ]
  have hΦinj : Function.Injective Φl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine (Qs_nondegenerate S.D).1 v fun w => ?_
    rw [polarBilin_apply_apply, ← hΦpol, hv, polar_zero_left]
  have hfr : finrank K (Vs K E) = finrank K V := by
    rw [hdim, Module.finrank_prod, Module.finrank_prod, Module.finrank_pi_fintype,
      Module.finrank_self]
    simp [S.D.finrank_eq]
  have hΦbij : Function.Bijective Φl :=
    ⟨hΦinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hΦinj⟩
  let Φ : (Qs S.D).IsometryEquiv Q := ⟨LinearEquiv.ofBijective Φl hΦbij, hΦQ⟩
  refine ⟨E, inferInstance, inferInstance, hfin, S, Φ, ?_⟩
  have hkey : ∀ (g : E₀) (v : Vs K E), Φl (tor S (c g) v) = g.1 (Φl v) := by
    intro g v
    rw [hΦl, hΦl, tor_apply, map_add, map_add, map_smul, map_smul, hfix1, hfix2, map_sum]
    simp only [hchar]
    rfl
  have hconj : ∀ g : E₀, linConj Φ.toLinearEquiv (tor S (c g)) = g.1 := by
    intro g
    refine LinearEquiv.ext fun v' => ?_
    obtain ⟨v, rfl⟩ := Φ.toLinearEquiv.surjective v'
    rw [linConj_apply, LinearEquiv.symm_apply_apply]
    exact hkey g v
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    change t ∈ (torHom S).range at ht
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 ht
    obtain ⟨g', hg'⟩ := hcbij.2 (Multiplicative.toAdd a)
    have h1 : torHom S a = tor S (c g') := by rw [hg']; rfl
    rw [MulEquiv.coe_toMonoidHom, h1, hconj g']
    exact g'.2
  · intro hg
    exact ⟨tor S (c ⟨g, hg⟩), ⟨Multiplicative.ofAdd (c ⟨g, hg⟩), rfl⟩, hconj ⟨g, hg⟩⟩

end Frame

end CFSG.RankThree.PartOne.KFR4

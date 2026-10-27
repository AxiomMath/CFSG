module

public import CFSG.Quasithin.Background.Asc81cPfOdd2
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LinearAlgebra.LinearGroups.QuadraticActions

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W] [Finite W]
  {G : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))} {X₀ Y₀ : Subgroup (MulAut W)}

theorem fixes_of_card_two {U : Subgroup W} (hU : Nat.card U = 2) {r : MulAut W}
    (hr : ∀ u ∈ U, r u ∈ U) : ∀ u ∈ U, r u = u := by
  classical
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1, map_one]
  by_contra hne
  have h1 : r u ≠ 1 := fun h => hu1 (r.injective (h.trans (map_one r).symm))
  have : Fintype W := Fintype.ofFinite W
  have hsub : ({1, u, r u} : Finset W) ⊆ (U : Set W).toFinset := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [Set.mem_toFinset]
    rcases hw with rfl | rfl | rfl
    · exact U.one_mem
    · exact hu
    · exact hr u hu
  have h2 := Finset.card_le_card hsub
  rw [Set.toFinset_card, ← Nat.card_eq_fintype_card] at h2
  have h3 : Nat.card (U : Set W) = Nat.card U := rfl
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm hu1, Ne.symm h1]),
    Finset.card_insert_of_notMem (by simp [Ne.symm hne]), Finset.card_singleton] at h2
  omega

theorem TransSetting.false_of_odd (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) (hodd : Odd (Nat.card G))
    (hk : 7 ≤ Nat.card X₀) : False := by
  classical
  have := finite_mulAut (W := W)
  have hXh := (hT.hyp X₀ hX₀).1
  obtain ⟨hD, hΩ⟩ := hT.card_oddU_eq_two hW hX₀ hY₀ hnc hodd hk
  have hD' : ∀ Z ∈ Ω, Nat.card (oddU G Z) = 2 := fun Z hZ => (hT.card_oddU_eq hX₀ hZ).trans hD
  have hsolv : Group.IsSolvable G := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hG1 : G ≠ ⊥ := fun h => hXh.2.1 (le_bot_iff.1 (h ▸ hXh.1))
  obtain ⟨A, hAG, hA1, hAc, hAn⟩ := CFSG.LinearGroups.exists_abelian_normalized_of_isSolvable G hG1
  have hA1' : Nat.card A ≠ 1 := fun h => hA1 (Subgroup.eq_bot_of_card_eq A h)
  obtain ⟨p, hp, hpA⟩ := Nat.exists_prime_and_dvd hA1'
  have : Fact p.Prime := ⟨hp⟩
  let R : Subgroup (MulAut W) :=
    { carrier := {a | a ∈ A ∧ a ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hAc a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨A.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hRA : R ≤ A := fun r hr => hr.1
  have hRG : R ≤ G := hRA.trans hAG
  have hRn : ∀ g ∈ G, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg r hr =>
    ⟨hAn g hg r hr.1, by rw [conj_pow, hr.2, mul_one, mul_inv_cancel]⟩
  have hR1 : R ≠ ⊥ := by
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpA
    intro h0
    have h1 : (a : MulAut W) ∈ R := ⟨a.2, by
      rw [← Subgroup.orderOf_coe] at ha
      rw [← ha, pow_orderOf_eq_one]⟩
    rw [h0, Subgroup.mem_bot] at h1
    have h2 : orderOf a = 1 := by
      rw [← Subgroup.orderOf_coe, h1, orderOf_one]
    rw [h2] at ha
    exact hp.one_lt.ne ha
  have hRodd : Odd (Nat.card R) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hRG)
  have hcover := fun v hv hv1 => hT.exists_oddU hW hX₀ hY₀ hnc hodd hk (v := v) hv hv1
  have hUstable : ∀ Z ∈ Ω, ∀ g ∈ G, Z.map (MulAut.conj g).toMonoidHom = Z →
      ∀ u ∈ oddU G Z, g u = u := by
    intro Z hZ g hg hgZ
    refine fixes_of_card_two (hD' Z hZ) fun u hu => ?_
    have h1 := oddU_map_conj hg hu
    rwa [hgZ] at h1
  have hfixG : ∀ g ∈ G, ∀ c ∈ fixV G, g c = c := fun g hg c hc => hc g hg
  have htriv : ∀ Z ∈ Ω, ∀ y : MulAut W, (∀ c ∈ fixV G, y c = c) →
      (∀ u ∈ oddU G Z, y u = u) → (∀ w ∈ commSub (⊤ : Subgroup W) Z, y w = w) → y = 1 := by
    intro Z hZ y hyG hyU hyW
    have hZh := (hT.hyp Z hZ).1
    ext v
    have hv : v ∈ fixV Z ⊔ commSub ⊤ Z := by
      rw [fixV_sup_commSub_eq_top' hW hZh.2.2.2.1]
      exact Subgroup.mem_top v
    obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
    have hc' : c ∈ fixV G ⊔ oddU G Z := by
      have hbot : fixV G ⊓ oddU G Z = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨hx1, -, hx2⟩
        have h1 : x ∈ fixV G ⊓ commSub ⊤ G := ⟨hx1, hx2⟩
        rwa [fixV_inf_commSub_eq_bot' hW hodd] at h1
      have hle : fixV G ⊔ oddU G Z ≤ fixV Z :=
        sup_le (fun x hx z hz => hx z (hZh.1 hz)) inf_le_left
      have heq : fixV G ⊔ oddU G Z = fixV Z := by
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        rw [card_sup_of_inf_eq_bot hbot, card_fixV_eq_mul_oddU hW hodd hZh.1]
      rw [heq]
      exact hc
    obtain ⟨c₁, hc₁, u, hu, rfl⟩ := Subgroup.mem_sup.1 hc'
    rw [MulAut.one_apply, map_mul, map_mul, hyG c₁ hc₁, hyU u hu, hyW w hw]
  have hRZ : ∀ Z ∈ Ω, ∀ r ∈ R, r ∈ Z → r = 1 := by
    intro Z hZ r hr hrZ
    by_contra hr1
    have hZh := (hT.hyp Z hZ).1
    have hzp : Subgroup.zpowers r ≤ Z := (Subgroup.zpowers_le).2 hrZ
    have hzp1 : Subgroup.zpowers r ≠ ⊥ := fun h => hr1 ((Subgroup.zpowers_eq_bot).1 h)
    have hRNZ : ∀ r' ∈ R, Z.map (MulAut.conj r').toMonoidHom = Z := by
      intro r' hr'
      have h1 := mem_normalizer_of_mapsTo hZh (hRG hr') fun v hv => by
        rw [← fixV_eq_of_le hW hZh hzp hzp1] at hv ⊢
        exact fixV_stable_of_normalizer (show r' ∈ Subgroup.normalizer
          ((Subgroup.zpowers r : Subgroup (MulAut W)) : Set (MulAut W)) from
          Subgroup.mem_normalizer_iff_map_conj_eq.2 (map_conj_eq_of_commutes fun b hb => by
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
            exact ((show Commute r' r from hAc r' (hRA hr') r (hRA hr)).zpow_right k).eq)) hv
      exact Subgroup.mem_normalizer_iff_map_conj_eq.1 h1
    have hRN : ∀ Z' ∈ Ω, ∀ r' ∈ R, Z'.map (MulAut.conj r').toMonoidHom = Z' := by
      intro Z' hZ' r' hr'
      obtain ⟨g, hg, rfl⟩ := hT.trans Z hZ Z' hZ'
      have h1 := hRNZ _ (hRn g⁻¹ (G.inv_mem hg) r' hr')
      rw [map_conj_map_conj]
      calc Z.map (MulAut.conj (r' * g)).toMonoidHom
          = (Z.map (MulAut.conj (g⁻¹ * r' * g⁻¹⁻¹)).toMonoidHom).map
              (MulAut.conj g).toMonoidHom := by
            rw [map_conj_map_conj]
            congr 2
            group
        _ = _ := by rw [h1]
    have hRtriv : ∀ r' ∈ R, r' = 1 := by
      intro r' hr'
      have hV₀ : ∀ v ∈ commSub (⊤ : Subgroup W) G, r' v = v := by
        intro v hv
        by_cases hv1 : v = 1
        · rw [hv1, map_one]
        obtain ⟨Z', hZ', hvZ'⟩ := hcover v hv hv1
        exact hUstable Z' hZ' r' (hRG hr') (hRN Z' hZ' r' hr') v hvZ'
      ext v
      have hv : v ∈ fixV G ⊔ commSub ⊤ G := by
        rw [fixV_sup_commSub_eq_top' hW hodd]
        exact Subgroup.mem_top v
      obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
      rw [MulAut.one_apply, map_mul, hfixG r' (hRG hr') c hc, hV₀ w hw]
    exact hr1 (hRtriv r hr)
  have hRNZ1 : ∀ Z ∈ Ω, ∀ r ∈ R, Z.map (MulAut.conj r).toMonoidHom = Z → r = 1 := by
    intro Z hZ r hr hrZ
    have hZh := (hT.hyp Z hZ).1
    have hrN : r ∈ Subgroup.normalizer (Z : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 hrZ
    have hcomm : ∀ z ∈ Z, r * z = z * r := by
      intro z hz
      have h1 : r * z * r⁻¹ * z⁻¹ ∈ Z := Z.mul_mem (conj_mem hrN ⟨z, hz⟩) (Z.inv_mem hz)
      have h2 : r * z * r⁻¹ * z⁻¹ ∈ R := by
        have h3 := R.mul_mem hr (hRn z (hZh.1 hz) r⁻¹ (R.inv_mem hr))
        have h4 : r * (z * r⁻¹ * z⁻¹) = r * z * r⁻¹ * z⁻¹ := by group
        rwa [h4] at h3
      have h5 := hRZ Z hZ _ h2 h1
      calc r * z = r * z * r⁻¹ * z⁻¹ * (z * r) := by group
        _ = z * r := by rw [h5, one_mul]
    obtain ⟨x₀, hx₀, hx₀v⟩ := exists_eq_on_commSub hZh hcomm
    have hy := htriv Z hZ (x₀⁻¹ * r)
      (fun c hc => by rw [MulAut.mul_apply, hfixG r (hRG hr) c hc, hfixG _ (G.inv_mem
        (hZh.1 hx₀)) c hc])
      (fun u hu => by
        rw [MulAut.mul_apply, hUstable Z hZ r (hRG hr) hrZ u hu]
        have h1 : x₀ u = u := hu.1 x₀ hx₀
        calc x₀⁻¹ u = x₀⁻¹ (x₀ u) := by rw [h1]
          _ = u := by rw [MulAut.inv_apply_self])
      (fun w hw => by rw [MulAut.mul_apply, hx₀v w hw, MulAut.inv_apply_self])
    rw [inv_mul_eq_one] at hy
    exact hRZ Z hZ r hr (hy ▸ hx₀)
  have hfree : ∀ r ∈ R, ∀ v ∈ commSub (⊤ : Subgroup W) G, v ≠ 1 → r v = v → r = 1 := by
    intro r hr v hv hv1 hrv
    obtain ⟨Z, hZ, hvZ⟩ := hcover v hv hv1
    refine hRNZ1 Z hZ r hr ?_
    by_contra hne
    have h1 : v ∈ oddU G (Z.map (MulAut.conj r).toMonoidHom) ⊓ oddU G Z := by
      refine ⟨?_, hvZ⟩
      rw [← hrv]
      exact oddU_map_conj (hRG hr) hvZ
    rw [hT.oddU_inf_eq_bot hW hX₀ hY₀ hnc hodd (hT.inv r (hRG hr) Z hZ) hZ hne] at h1
    exact hv1 h1
  have hfpf : ∀ x ∈ X₀, ∀ r ∈ R, x * r = r * x → x = 1 ∨ r = 1 := by
    intro x hx r hr hxr
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    right
    have hzp : Subgroup.zpowers x ≤ X₀ := (Subgroup.zpowers_le).2 hx
    have hzp1 : Subgroup.zpowers x ≠ ⊥ := fun h => hx1 ((Subgroup.zpowers_eq_bot).1 h)
    refine hRNZ1 X₀ hX₀ r hr (Subgroup.mem_normalizer_iff_map_conj_eq.1
      (mem_normalizer_of_mapsTo hXh (hRG hr) fun v hv => ?_))
    rw [← fixV_eq_of_le hW hXh hzp hzp1] at hv ⊢
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← MulAut.mul_apply, ((show Commute r x from hxr.symm).zpow_right k).eq.symm,
      MulAut.mul_apply, hv _ hb]
  obtain ⟨r₀, hr₀, hr₀1⟩ : ∃ r ∈ R, r ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hR1 ((Subgroup.eq_bot_iff_forall _).2 hall)
  have hXR : Nat.card X₀ + 1 ≤ Nat.card R := by
    have hmem : ∀ x : X₀, (x : MulAut W) * r₀ * (x : MulAut W)⁻¹ ∈ ((R : Set (MulAut W)) \ {1}) :=
      fun x => ⟨hRn x (hXh.1 x.2) r₀ hr₀, fun h => hr₀1 (by
        have h1 : (x : MulAut W) * r₀ * (x : MulAut W)⁻¹ = 1 := h
        rw [mul_inv_eq_one, mul_eq_left] at h1
        exact h1)⟩
    let f : X₀ → ↥((R : Set (MulAut W)) \ {1}) := fun x => ⟨_, hmem x⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (a : MulAut W) * r₀ * (a : MulAut W)⁻¹ = (b : MulAut W) * r₀ * (b : MulAut W)⁻¹ :=
        congrArg Subtype.val hab
      have h2 : ((b : MulAut W)⁻¹ * a) * r₀ = r₀ * ((b : MulAut W)⁻¹ * a) := by
        calc ((b : MulAut W)⁻¹ * a) * r₀ = (b : MulAut W)⁻¹ * (a * r₀ * (a : MulAut W)⁻¹) * a := by
              group
          _ = (b : MulAut W)⁻¹ * ((b : MulAut W) * r₀ * (b : MulAut W)⁻¹) * a := by rw [h1]
          _ = _ := by group
      rcases hfpf _ (X₀.mul_mem (X₀.inv_mem b.2) a.2) r₀ hr₀ h2 with h3 | h3
      · apply Subtype.ext
        rw [inv_mul_eq_one] at h3
        exact h3.symm
      · exact absurd h3 hr₀1
    have h1 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem R.one_mem,
      ← Nat.card_coe_set_eq] at h1
    have h2 : 0 < Nat.card R := Nat.card_pos
    have h3 : Nat.card (R : Set (MulAut W)) = Nat.card R := rfl
    omega
  have : Fintype W := Fintype.ofFinite W
  let S : Finset W := ((commSub (⊤ : Subgroup W) G : Set W) \ {1}).toFinset
  have hmemS : ∀ v, v ∈ S ↔ v ∈ commSub (⊤ : Subgroup W) G ∧ v ≠ 1 := fun v => by
    simp [S]
  have hdvd : Nat.card R ∣ S.card := by
    refine card_dvd_of_free S (fun r hr v hv => ?_) (fun r hr v hv hrv => ?_)
    · obtain ⟨hv1, hv2⟩ := (hmemS v).1 hv
      refine (hmemS _).2 ⟨commSub_stable' (hRG hr) hv1, fun h => hv2 ?_⟩
      exact r.injective (h.trans (map_one r).symm)
    · obtain ⟨hv1, hv2⟩ := (hmemS v).1 hv
      exact hfree r hr v hv1 hv2 hrv
  have hScard : S.card = 2 * Nat.card X₀ + 1 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, card_diff_one,
      card_commSub_G_eq hW hodd hXh.1 hXh.2.2.2.1, hD, card_commSub hXh]
    ring_nf
    omega
  have hRS : Nat.card R = S.card := by
    obtain ⟨c, hc⟩ := hdvd
    have h2 : 2 * Nat.card X₀ + 1 = Nat.card R * c := hScard ▸ hc
    have hc1 : c = 1 := by
      rcases Nat.lt_or_ge c 2 with h | h
      · interval_cases c
        · omega
        · rfl
      · nlinarith
    rw [hc, hc1, mul_one]
  have hRp : IsPGroup p R := fun r => ⟨1, Subtype.ext (by
    show (r : MulAut W) ^ p ^ 1 = 1
    rw [pow_one]
    exact r.2.2)⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hRp
  have hV₀2 := card_eq_two_pow hW (commSub (⊤ : Subgroup W) G)
  have hV₀ : Nat.card (commSub (⊤ : Subgroup W) G) = S.card + 1 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, card_diff_one]
    have : 0 < Nat.card (commSub (⊤ : Subgroup W) G) := Nat.card_pos
    omega
  have hm1 : m = 1 := by
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, pow_zero] at hm
        exact absurd (Subgroup.eq_bot_of_card_eq R hm) hR1
      · exact h
    refine eq_one_of_pow_add_one_eq_two_pow (hp.eq_two_or_odd'.resolve_left ?_) hp.one_lt hm0
      (n := rk (commSub (⊤ : Subgroup W) G)) ?_ ?_
    · rintro rfl
      rw [hm] at hRodd
      exact (Nat.not_even_iff_odd.2 hRodd) (Nat.even_pow.2 ⟨even_two, hm0.ne'⟩)
    · by_contra hn
      push Not at hn
      have h1 : 2 ^ rk (commSub (⊤ : Subgroup W) G) ≤ 2 ^ 1 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · rw [← hm, hRS, ← hV₀, hV₀2]
  rw [hm1, pow_one] at hm
  have hRcyc : IsCyclic R := isCyclic_of_prime_card hm
  have hfixR : fixV R ⊓ commSub ⊤ G = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    by_contra hv
    exact hr₀1 (hfree r₀ hr₀ v hv2 hv (hv1 r₀ hr₀))
  have hcommR : commSub (⊤ : Subgroup W) R = commSub ⊤ G := by
    refine Subgroup.eq_of_le_of_card_ge (commSub_mono le_rfl hRG) ?_
    have h1 := card_fixV_mul_card_commSub hW hRodd
    have h2 := card_fixV_mul_card_commSub hW hodd
    have h3 : Nat.card (fixV R) * Nat.card (commSub (⊤ : Subgroup W) G) ≤ Nat.card W := by
      rw [← card_sup_of_inf_eq_bot hfixR]
      exact Nat.card_le_card_of_injective _ (fixV R ⊔ commSub ⊤ G).subtype_injective
    have hle : Nat.card (fixV G) ≤ Nat.card (fixV R) :=
      Subgroup.card_le_of_le fun v hv r hr => hv r (hRG hr)
    have hpos : 0 < Nat.card (fixV R) := Nat.card_pos
    nlinarith
  have hR101 : Hyp101 R R := by
    refine ⟨le_rfl, hR1, hRcyc, hRodd, ?_, fun g hg _ x hx => R.mul_mem (R.mul_mem hg hx)
      (R.inv_mem hg)⟩
    intro v hv hv1 w hw hw1
    rw [hcommR] at hv hw
    let f : R → ↥((commSub (⊤ : Subgroup W) G : Set W) \ {1}) := fun r =>
      ⟨(r : MulAut W) v, commSub_stable' (hRG r.2) hv, fun h => hv1 ((r : MulAut W).injective
        (h.trans (map_one _).symm))⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (a : MulAut W) v = (b : MulAut W) v := congrArg Subtype.val hab
      have h2 : ((b : MulAut W)⁻¹ * a) v = v := by
        rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
      have h3 := hfree _ (R.mul_mem (R.inv_mem b.2) a.2) v hv hv1 h2
      apply Subtype.ext
      rw [inv_mul_eq_one] at h3
      exact h3.symm
    have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by
      rw [card_diff_one, hm]
      rw [hRS] at hm
      rw [← hm]
      have : Nat.card (commSub (⊤ : Subgroup W) G) - 1 = S.card := by omega
      rw [this, hm])
    obtain ⟨r, hr⟩ := hbij.2 ⟨w, hw, hw1⟩
    refine ⟨r, congrArg Subtype.val hr, fun r' hr' => hf (Subtype.ext ?_)⟩
    rw [hr]
    exact hr'
  have hXN : X₀ ≤ Subgroup.normalizer (R : Set (MulAut W)) := fun x hx =>
    Subgroup.mem_normalizer_iff.2 fun r => ⟨fun hr => hRn x (hXh.1 hx) r hr, fun hr => by
      have h1 := hRn x⁻¹ (G.inv_mem (hXh.1 hx)) _ hr
      have h2 : x⁻¹ * (x * r * x⁻¹) * x⁻¹⁻¹ = r := by group
      rwa [h2] at h1⟩
  have hXC : ∀ y ∈ X₀, (∀ r ∈ R, y * r = r * y) → y = 1 := fun y hy hyR =>
    (hfpf y hy r₀ hr₀ (hyR r₀ hr₀)).resolve_right hr₀1
  have hdiv := card_dvd_rk hW hR101 hXN hXC
  rw [hcommR] at hdiv
  have hk2 := card_eq_two_pow hW (commSub (⊤ : Subgroup W) X₀)
  have hq := card_commSub hXh
  have hn : rk (commSub (⊤ : Subgroup W) G) = rk (commSub (⊤ : Subgroup W) X₀) + 1 := by
    have h1 := card_commSub_G_eq hW hodd hXh.1 hXh.2.2.2.1
    rw [hD, hV₀2, hk2, ← pow_succ'] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  rw [hn] at hdiv
  set k := rk (commSub (⊤ : Subgroup W) X₀)
  have hle := Nat.le_of_dvd (by omega) hdiv
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have h1 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 := two_mul_add_one_lt_two_pow hk3
  omega

theorem TransSetting.commutes (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hk : 7 ≤ Nat.card X₀) : Commutes X₀ Y₀ := by
  by_contra hnc
  exact hT.false_of_odd hW hX₀ hY₀ hnc (hT.odd_card hW hX₀ hY₀ hnc) hk

end Pf

end Asc81c

end CFSG.Quasithin

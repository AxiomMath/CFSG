module

public import CFSG.Quasithin.Vol2.Ch9Facts
public import CFSG.Quasithin.Vol2.Ch9Sec1Adapt
public import CFSG.Quasithin.Background.HOm4UT
public import CFSG.Quasithin.Background.SmithD37Out1
public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.Quasithin.H13.Ch9.FactsFrob

open CFSG.Quasithin CFSG.QuasithinUnique Matrix CFSG.Quasithin.H

variable {K : Type} [Field K]

theorem isUT_of_conj_u1 {G : GL (Fin 2) K} {c : K}
    (h : (G : Matrix (Fin 2) (Fin 2) K) * (u1 K : Matrix (Fin 2) (Fin 2) K) *
      ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1]) : Om4.IsUT G := by
  have h2 : (G : Matrix (Fin 2) (Fin 2) K) * (u1 K : Matrix (Fin 2) (Fin 2) K) =
      !![1, c; 0, 1] * (G : Matrix (Fin 2) (Fin 2) K) := by
    rw [← h, Matrix.mul_assoc _ ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  have h3 := congrFun (congrFun h2 1) 1
  simp [u1, Matrix.mul_apply, Fin.sum_univ_two] at h3
  exact h3

theorem ut_of_mem_normalizer_uni {g : SpecialLinearGroup (Fin 2) K}
    (hg : g ∈ Subgroup.normalizer (uni K : Set (SpecialLinearGroup (Fin 2) K))) :
    Om4.IsUT (Matrix.SpecialLinearGroup.toGL g) := by
  have h := (Subgroup.mem_normalizer_iff.mp hg (u1 K)).mp u1_mem
  obtain ⟨c, hc⟩ := mem_uni_iff.mp h
  refine isUT_of_conj_u1 (c := c) ?_
  rw [← hc, ← map_inv]
  rfl

theorem conj_apply_zero_zero {G : GL (Fin 2) K} (hG : Om4.IsUT G)
    {X : Matrix (Fin 2) (Fin 2) K} (hX : X 1 0 = 0) :
    ((G : Matrix (Fin 2) (Fin 2) K) * X * ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 =
      X 0 0 := by
  have hGG : (G : Matrix (Fin 2) (Fin 2) K) * ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e10 := congrFun (congrFun hGG 1) 0
  have e00 := congrFun (congrFun hGG 0) 0
  unfold Om4.IsUT at hG
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hG, zero_mul, zero_add, Matrix.one_apply_ne
    (show (1 : Fin 2) ≠ 0 by decide), Matrix.one_apply_eq] at e10 e00
  obtain ⟨-, hG1⟩ := (show Om4.IsUT G from hG).apply_ne_zero
  have hinv10 : ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    (mul_eq_zero.mp e10).resolve_left hG1
  rw [hinv10, mul_zero, add_zero] at e00
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hX, hinv10, mul_zero, add_zero]
  linear_combination X 0 0 * e00

theorem exists_frob_pow [Finite K] [CharP K 2] (τ : K ≃+* K) :
    ∃ i : ℕ, ∀ x : K, τ x = x ^ 2 ^ i := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card] at hn
  obtain ⟨σ, hσ, -, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (PNat.pos n) hn
  have hmem : τ ∈ Subgroup.zpowers σ := by rw [hzp]; exact Subgroup.mem_top τ
  have hfin : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (PNat.pos n) hn
    rw [hcard]
    exact (PNat.pos n).ne')
  obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers (x := σ)).mpr hmem
  have hi' : σ ^ i = τ := hi
  have key : ∀ j : ℕ, ∀ x : K, (σ ^ j) x = x ^ 2 ^ j := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ, RingAut.mul_apply, hσ, ih, ← pow_mul, pow_succ, mul_comm]
  exact ⟨i, fun x => by rw [← hi', key]⟩

theorem exists_pow_two_pow_of_uni [Finite K] [CharP K 2]
    {β : MulAut (SpecialLinearGroup (Fin 2) K)} (hβ : (uni K).map β.toMonoidHom = uni K)
    {d : SpecialLinearGroup (Fin 2) K}
    (hd : d ∈ Subgroup.normalizer (uni K : Set (SpecialLinearGroup (Fin 2) K)))
    (hdo : Odd (orderOf d)) (hβd : β d ∈ Subgroup.zpowers d) : ∃ j : ℕ, β d = d ^ 2 ^ j := by
  obtain ⟨G, τ, hGτ⟩ := Om4.exists_eq_conj_map β
  have hu1 : β (u1 K) ∈ uni K := hβ ▸ ⟨u1 K, u1_mem, rfl⟩
  obtain ⟨c, hc⟩ := mem_uni_iff.mp hu1
  have hu1τ : (u1 K : Matrix (Fin 2) (Fin 2) K).map τ = (u1 K : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u1]
  have hG : Om4.IsUT G := by
    refine isUT_of_conj_u1 (c := c) ?_
    rw [← hc, hGτ, hu1τ]
  have hdUT := ut_of_mem_normalizer_uni hd
  set a := (d : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  obtain ⟨ha0, hd11⟩ := hdUT.apply_ne_zero
  obtain ⟨k, hk₀⟩ := (mem_powers_iff_mem_zpowers (x := d)).mpr hβd
  have hk : d ^ k = β d := hk₀
  have h00β : ((β d : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = τ a := by
    rw [hGτ, conj_apply_zero_zero hG (by
      show τ ((d : Matrix (Fin 2) (Fin 2) K) 1 0) = 0
      rw [show (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 from hdUT, map_zero])]
    rfl
  have h00k : ((d ^ k : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = a ^ k := by
    have := hdUT.pow_apply_zero_zero k
    rw [← map_pow] at this
    exact this
  obtain ⟨i, hi⟩ := exists_frob_pow τ
  have hak : a ^ k = a ^ 2 ^ i := by rw [← h00k, hk, h00β, hi]
  set u : Kˣ := Units.mk0 a ha0 with hu
  have huk : u ^ k = u ^ 2 ^ i := Units.ext (by
    simp only [Units.val_pow_eq_pow_val, hu]
    exact hak)
  have hmod := (pow_eq_pow_iff_modEq (x := u)).mp huk
  have hdiv : orderOf d ∣ orderOf u := by
    have hdet : a * (d : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      have h := d.2
      rw [Matrix.det_fin_two, show (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 from hdUT, mul_zero,
        sub_zero] at h
      exact h
    have hN : a ^ orderOf u = 1 := by
      have := congrArg Units.val (pow_orderOf_eq_one u)
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    have hN' : ((d : Matrix (Fin 2) (Fin 2) K) 1 1) ^ orderOf u = 1 := by
      have h2 := congrArg (· ^ orderOf u) hdet
      simp only [mul_pow, hN, one_mul, one_pow] at h2
      exact h2
    have hsq : (Matrix.SpecialLinearGroup.toGL d ^ orderOf u) ^ 2 = 1 :=
      (hdUT.pow _).sq_eq_one (by rw [hdUT.pow_apply_zero_zero]; exact hN)
        (by rw [hdUT.pow_apply_one_one]; exact hN')
    have h2 : d ^ (orderOf u * 2) = 1 := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [map_pow, pow_mul, hsq, map_one]
    exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_two_right.mpr hdo)
      (orderOf_dvd_of_pow_eq_one h2)
  refine ⟨i, ?_⟩
  rw [← hk]
  exact (pow_eq_pow_iff_modEq (x := d)).mpr (hmod.of_dvd hdiv)

theorem isSylowTwoOf_uni [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    IsSylowTwoOf (uni K) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcu : Nat.card ↥(uni K) = 2 ^ n := by rw [card_uni, hK]
  refine ⟨le_top, ?_, ?_⟩
  · rw [IsPGroup.iff_card, hcu]
    exact ⟨_, rfl⟩
  · rw [show ((uni K).subgroupOf ⊤).index = (uni K).index from Subgroup.relIndex_top_right _]
    have hidx : (uni K).index = 4 ^ n - 1 := by
      have h := Subgroup.card_mul_index (uni K)
      rw [hcu, Vol2.Ch10.SecA.card_SL_two_pow hK] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h
    rw [hidx]
    have hodd := Vol2.Ch10.SecA.odd_four_pow_sub_one (m := n) (by omega)
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem factBenderCartanFrob_holds :
    FactBenderCartanFrob := by
  intro Y _ _ m hm hY S hS d hd hdo α hα2 hαS hαd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdodd : Odd (orderOf d) := by
    rw [hdo]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  rcases hY with hY | hY
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
    have := Fintype.ofFinite K
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hK
    let e' : Y ≃* SpecialLinearGroup (Fin 2) K := e.trans (SmithD37.statedProjEquiv.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm)
    have hS' := CFSG.Quasithin.A312.isSylowTwoOf_top_map e'.toMonoidHom e'.surjective hS
    obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hS'
      (isSylowTwoOf_uni (by omega) hK)
    set f : Y ≃* SpecialLinearGroup (Fin 2) K := e'.trans (MulAut.conj g) with hf
    have hfS : S.map f.toMonoidHom = uni K := by
      rw [← hg, Subgroup.map_map]
      rfl
    set β : MulAut (SpecialLinearGroup (Fin 2) K) := f.symm.trans (α.trans f) with hβdef
    have hβapp : ∀ y : Y, β (f y) = f (α y) := fun y => by
      simp [hβdef]
    have hβ : (uni K).map β.toMonoidHom = uni K := by
      rw [← hfS, Subgroup.map_map]
      have : β.toMonoidHom.comp f.toMonoidHom = f.toMonoidHom.comp α.toMonoidHom :=
        MonoidHom.ext hβapp
      rw [this, ← Subgroup.map_map, hαS]
    have hdN : f d ∈ Subgroup.normalizer (uni K : Set (SpecialLinearGroup (Fin 2) K)) := by
      rw [← hfS, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨d, hd, rfl⟩
    have hdo' : Odd (orderOf (f d)) := by rw [MulEquiv.orderOf_eq]; exact hdodd
    have hβd : β (f d) ∈ Subgroup.zpowers (f d) := by
      rw [hβapp]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hαd
      exact ⟨k, by rw [← hk, map_zpow]⟩
    obtain ⟨j, hj⟩ := exists_pow_two_pow_of_uni hβ hdN hdo' hβd
    refine ⟨j, f.injective ?_⟩
    rw [map_pow, ← hj, hβapp]
  ·
    have hout :=
      (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} Y 2 m hY).1.2.2
    have hinn : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y := by
      obtain ⟨k, hk⟩ := hα2
      let π := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner Y)
      have h1 : orderOf (π α) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
      have h2 : orderOf (π α) ∣
          Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) :=
        orderOf_dvd_natCard _
      have h3 : orderOf (π α) = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hout)) h1 h2
      exact (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp h3)
    obtain ⟨y, rfl⟩ := hinn
    have hidx : ¬ 2 ∣ S.index := by
      have h : ¬ 2 ∣ (S.subgroupOf ⊤).index := hS.2.2
      rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
    let T : Sylow 2 Y := hS.2.1.toSylow hidx
    have hTS : (T : Subgroup Y) = S := rfl
    have hY' := hY
    obtain ⟨-, a, ha, K, _, _, hma, hK, ⟨e⟩⟩ := hY'
    let e' : Y ≃* CFSG.Open.Sz a := e.trans ((MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
        (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha (hma ▸ hK)))
    obtain ⟨D, hD⟩ :=
      CFSG.Goldschmidt.G3a.exists_borelSetup (Or.inr (Or.inr ⟨a, ha, ⟨e'⟩⟩)) T
    have hDc := (hD.orders_sz ha e').2.2
    have hdT : Subgroup.zpowers d ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y) :=
      Subgroup.zpowers_le.mpr hd
    have hTd : (T : Subgroup Y) ⊓ Subgroup.zpowers d = ⊥ := by
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hS.2.1
      refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
      rw [hTS, hb, Nat.card_zpowers]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hdodd)
    have hsup : (T : Subgroup Y) ⊔ Subgroup.zpowers d =
        Subgroup.normalizer ((T : Subgroup Y) : Set Y) := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le Subgroup.le_normalizer hdT) ?_
      have h1 := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hdT
      have h2 := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hD.le
      rw [inf_comm, hTd, Subgroup.card_bot, mul_one, sup_comm] at h1
      rw [inf_comm, hD.inf, Subgroup.card_bot, mul_one, sup_comm, hD.sup] at h2
      rw [h1, h2, Nat.card_zpowers, hdo, hDc, hma]
    have hD' : CFSG.Goldschmidt.G3a.BorelSetup T (Subgroup.zpowers d) :=
      { se := hD.se, card := hD.card, le := hdT, cyc := inferInstance
        odd := by rw [Nat.card_zpowers]; exact hdodd
        inf := hTd, sup := hsup, sq := hD.sq, inv := hD.inv, four := hD.four, cent := hD.cent }
    have hyN : y ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y) := by
      rw [hTS]
      refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · rw [← hαS]
        exact ⟨x, hx, rfl⟩
      · rw [← hαS] at hx
        obtain ⟨x', hx', hxx⟩ := hx
        have : x' = x := by
          have := congrArg (fun z => y⁻¹ * z * y) hxx
          simpa [MulAut.conj_apply, mul_assoc] using this
        rwa [← this]
    obtain ⟨s, hs, d', hd', rfl⟩ := hD'.exists_mul hyN
    have hd'd : d' * d = d * d' := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd'
      exact (Commute.zpow_self d k).eq
    have hαd' : MulAut.conj (s * d') d = s * d * s⁻¹ := by
      rw [MulAut.conj_apply]
      calc s * d' * d * (s * d')⁻¹ = s * (d' * d) * d'⁻¹ * s⁻¹ := by group
        _ = s * (d * d') * d'⁻¹ * s⁻¹ := by rw [hd'd]
        _ = s * d * s⁻¹ := by group
    rw [hαd'] at hαd
    have hcomm : s * d * s⁻¹ * d⁻¹ ∈ (T : Subgroup Y) ⊓ Subgroup.zpowers d := by
      refine ⟨?_, (Subgroup.zpowers d).mul_mem hαd ((Subgroup.zpowers d).inv_mem
        (Subgroup.mem_zpowers d))⟩
      have h1 : d * s⁻¹ * d⁻¹ ∈ (T : Subgroup Y) :=
        (Subgroup.mem_normalizer_iff.mp hd _).mp ((T : Subgroup Y).inv_mem hs)
      have h2 := (T : Subgroup Y).mul_mem hs h1
      have h3 : s * d * s⁻¹ * d⁻¹ = s * (d * s⁻¹ * d⁻¹) := by group
      rw [h3]
      exact h2
    rw [hTd, Subgroup.mem_bot] at hcomm
    have hsd : d * s = s * d := by
      have h1 : s * d * s⁻¹ = d := by
        calc s * d * s⁻¹ = s * d * s⁻¹ * d⁻¹ * d := by group
          _ = d := by rw [hcomm, one_mul]
      calc d * s = s * d * s⁻¹ * s := by rw [h1]
        _ = s * d := by group
    have hs1 : s = 1 := hD'.eq_one_of_commute_gen (fun x hx => hx) hs hsd
    refine ⟨0, ?_⟩
    rw [hαd', hs1]
    simp

end CFSG.Quasithin.H13.Ch9.FactsFrob

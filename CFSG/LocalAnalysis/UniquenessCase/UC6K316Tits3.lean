module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Frame
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.Elementary
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

theorem dvd_card_sub_one_of_index {P X : Type*} [Group P] [Finite P] [MulAction P X] [Finite X]
    {x₀ : X} (hx₀ : ∀ g : P, g • x₀ = x₀) {m : ℕ}
    (hm : ∀ x : X, x ≠ x₀ → m ∣ (MulAction.stabilizer P x).index) : m ∣ Nat.card X - 1 := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fintype (MulAction.orbitRel.Quotient P X) := Fintype.ofFinite _
  have hsum : Nat.card X = ∑ ω : MulAction.orbitRel.Quotient P X,
      (MulAction.stabilizer P ω.out).index := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits P X), Nat.card_sigma]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  set ω₀ : MulAction.orbitRel.Quotient P X := Quotient.mk'' x₀ with hω₀
  have hout : ω₀.out = x₀ := by
    have h := Quotient.mk_out (s := MulAction.orbitRel P X) x₀
    obtain ⟨g, hg⟩ := h
    rw [← hg]
    exact hx₀ g
  have h0 : (MulAction.stabilizer P ω₀.out).index = 1 := by
    rw [hout, Subgroup.index_eq_one, eq_top_iff]
    intro g _
    exact MulAction.mem_stabilizer_iff.2 (hx₀ g)
  have hrest : ∀ ω ∈ Finset.univ.erase ω₀, m ∣ (MulAction.stabilizer P ω.out).index := by
    intro ω hω
    refine hm _ fun heq => (Finset.mem_erase.1 hω).1 ?_
    rw [← Quotient.out_eq' ω, heq]
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ω₀), h0, Nat.add_sub_cancel_left]
  exact Finset.dvd_sum hrest

theorem card_dvd_pow_of_isPGroup {X : Type*} [Group X] {p : ℕ} [Fact p.Prime] {H : Subgroup X}
    (hH : IsPGroup p H) [Finite H] {n k : ℕ} (hn : Nat.card H ∣ n) (hk : ¬ p ^ (k + 1) ∣ n) :
    Nat.card H ∣ p ^ k := by
  obtain ⟨j, hj⟩ := hH.exists_card_eq
  rw [hj] at hn ⊢
  refine pow_dvd_pow p ?_
  by_contra hjk
  exact hk ((pow_dvd_pow p (by omega)).trans hn)

@[expose] def centralInvSub {X : Type*} [Group X] (T : Subgroup X) : Subgroup X where
  carrier := {x | x ∈ T ∧ (∀ y ∈ T, x * y = y * x) ∧ x * x = 1}
  one_mem' := ⟨T.one_mem, fun y _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨haT, ha, ha2⟩ ⟨hbT, hb, hb2⟩
    refine ⟨T.mul_mem haT hbT, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hb y hy, ← mul_assoc, ha y hy, mul_assoc]
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← ha b hbT]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haT, ha, ha2⟩
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [Set.mem_setOf_eq, hai]
    exact ⟨haT, ha, ha2⟩

theorem centralInvSub_ne_bot {X : Type*} [Group X] {T : Subgroup X} [Finite T] (hT : IsPGroup 2 T)
    (hne : T ≠ ⊥) : centralInvSub T ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hne
  haveI : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center T) := hT.to_subgroup _
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : Nat.card (Subgroup.center T) = 1 := by rw [hn, pow_zero]
    exact (Finite.one_lt_card_iff_nontrivial.2 inferInstance).ne' h1
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  intro hbot
  have hmem : ((c : T) : X) ∈ centralInvSub T := by
    refine ⟨(c : T).2, fun y hy => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.1 c.2 ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    · have h2 : (c : T) ^ 2 = 1 := by
        rw [← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one, Subgroup.coe_one]
      have := congrArg Subtype.val h2
      simpa [sq] using this
  rw [hbot, Subgroup.mem_bot] at hmem
  have hc1 : c = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hc1, orderOf_one] at hc
  exact absurd hc (by norm_num)

theorem card_sylow_three_titsD
    (S : Sylow 3 CFSG.Sporadic.Schreier.Tits.titsD) :
    Nat.card (S : Subgroup CFSG.Sporadic.Schreier.Tits.titsD) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hdvd : 3 ^ k ∣ 17971200 := by
    rw [← hk, ← CFSG.Sporadic.Schreier.Tits.card_titsD]
    exact Subgroup.card_subgroup_dvd_card _
  have hmul := (S : Subgroup CFSG.Sporadic.Schreier.Tits.titsD).card_mul_index
  have hind : ¬ 3 ∣ (S : Subgroup CFSG.Sporadic.Schreier.Tits.titsD).index := S.not_dvd_index
  rw [hk, CFSG.Sporadic.Schreier.Tits.card_titsD] at hmul
  have hk3 : k ≤ 3 := by
    by_contra h
    exact absurd ((pow_dvd_pow 3 (by omega : 4 ≤ k)).trans hdvd) (by norm_num)
  rw [hk]
  interval_cases k <;> omega

section Tits

open CFSG.Sporadic.Schreier.Tits

theorem card_inf_centralizer_dvd_three {R : Subgroup titsD} (hR : IsPGroup 3 R) {v : titsD}
    (hv : orderOf v = 2) : Nat.card (R ⊓ centralizer ({v} : Set titsD) : Subgroup titsD) ∣ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X : Subgroup titsD := R ⊓ centralizer ({v} : Set titsD) with hX
  have hX3 : IsPGroup 3 X := hR.to_le inf_le_left
  have key : ∀ (c u : titsD), c * u * c⁻¹ = v →
      Nat.card X ∣ Nat.card (centralizer ({u} : Set titsD)) := by
    intro c u hcu
    have hle : X.map (MulAut.conj c⁻¹).toMonoidHom ≤ centralizer ({u} : Set titsD) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxv := Subgroup.mem_centralizer_singleton_iff.1 hx.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hu : u = c⁻¹ * v * c := by rw [← hcu]; group
      rw [hu]
      calc c⁻¹ * x * c * (c⁻¹ * v * c) = c⁻¹ * (x * v) * c := by group
        _ = c⁻¹ * (v * x) * c := by rw [hxv]
        _ = c⁻¹ * v * c * (c⁻¹ * x * c) := by group
    have hcard : Nat.card (X.map (MulAut.conj c⁻¹).toMonoidHom) = Nat.card X :=
      Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hle
  rcases titsD_involution_conj v hv with hz | ht
  · obtain ⟨c, hc⟩ := isConj_iff.1 hz
    have hd := key c _ hc
    rw [card_centralizer_titsZD] at hd
    exact (card_dvd_pow_of_isPGroup hX3 hd (k := 0) (by norm_num)).trans (by norm_num)
  · obtain ⟨c, hc⟩ := isConj_iff.1 ht
    have hd := key c _ hc
    rw [titsD_centralizer_t.2.1] at hd
    exact (card_dvd_pow_of_isPGroup hX3 hd (k := 1) (by norm_num)).trans (by norm_num)

theorem titsConj_of_mem_titsD (s : titsD) :
    titsConj (⟨(s : Equiv.Perm (Fin 1755)), titsD_le_titsA s.2⟩ : titsA) = MulAut.conj s := by
  ext d
  rw [coe_titsConj_apply]
  rfl

theorem twoSigTriv_titsD : TwoSigTriv 3 titsD := by
  classical
  intro S W hW hnorm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hWne
  set W₁ : Subgroup titsA := W.comap titsConjEquiv.toMonoidHom with hW₁
  have hW₁2 : IsPGroup 2 W₁ := hW.comap_of_injective _ titsConjEquiv.injective
  set T : Subgroup (Equiv.Perm (Fin 1755)) := W₁.map titsA.subtype with hT
  have hT2 : IsPGroup 2 T := hW₁2.map _
  have hTne : T ≠ ⊥ := by
    intro hbot
    apply hWne
    have hW₁b : W₁ = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      have : (a : Equiv.Perm (Fin 1755)) ∈ T := Subgroup.mem_map_of_mem _ ha
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨a, rfl⟩ := titsConjEquiv.surjective w
    have ha : a ∈ W₁ := hw
    rw [hW₁b, Subgroup.mem_bot] at ha
    rw [ha, map_one]
    exact Subgroup.one_mem _
  have hTA : T ≤ titsA := Subgroup.map_subtype_le _
  have hST : ∀ s ∈ (S : Subgroup titsD), ∀ x ∈ T,
      (s : Equiv.Perm (Fin 1755)) * x * (s : Equiv.Perm (Fin 1755))⁻¹ ∈ T := by
    intro s hs x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    set sA : titsA := ⟨(s : Equiv.Perm (Fin 1755)), titsD_le_titsA s.2⟩ with hsA
    have hmem : sA * a * sA⁻¹ ∈ W₁ := by
      change titsConjEquiv (sA * a * sA⁻¹) ∈ W
      have h1 : titsConjEquiv (sA * a * sA⁻¹) =
          MulAut.conj s * titsConjEquiv a * (MulAut.conj s)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        change titsConj sA * titsConj a * (titsConj sA)⁻¹ = _
        rw [hsA, titsConj_of_mem_titsD]
        rfl
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.1 (hnorm s hs) _).1 ha
    exact Subgroup.mem_map.2 ⟨_, hmem, rfl⟩
  set V : Subgroup (Equiv.Perm (Fin 1755)) := centralInvSub T with hV
  have hVne : V ≠ ⊥ := centralInvSub_ne_bot hT2 hTne
  have hVT : V ≤ T := fun x hx => hx.1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => ha.2.1 b hb.1
  have hV2 : ∀ a ∈ V, a * a = 1 := fun a ha => ha.2.2
  obtain ⟨hVD, hVcard⟩ :=
    CFSG.LocalAnalysis.EvenBN.Tits.Model.card_le_of_elemAbelian_titsA (hVT.trans hTA) hVc hV2
  have hSV : ∀ s ∈ (S : Subgroup titsD), ∀ x ∈ V,
      (s : Equiv.Perm (Fin 1755)) * x * (s : Equiv.Perm (Fin 1755))⁻¹ ∈ V := by
    intro s hs x hx
    obtain ⟨hxT, hxc, hx2⟩ := hx
    refine ⟨hST s hs x hxT, fun y hy => ?_, ?_⟩
    · have hy' : (s : Equiv.Perm (Fin 1755))⁻¹ * y * (s : Equiv.Perm (Fin 1755)) ∈ T := by
        have := hST s⁻¹ (S.inv_mem hs) y hy
        simpa using this
      have hc := hxc _ hy'
      calc (s : Equiv.Perm (Fin 1755)) * x * (s : Equiv.Perm (Fin 1755))⁻¹ * y
          = (s : Equiv.Perm (Fin 1755)) * (x * ((s : Equiv.Perm (Fin 1755))⁻¹ * y *
              (s : Equiv.Perm (Fin 1755)))) * (s : Equiv.Perm (Fin 1755))⁻¹ := by group
        _ = (s : Equiv.Perm (Fin 1755)) * (((s : Equiv.Perm (Fin 1755))⁻¹ * y *
              (s : Equiv.Perm (Fin 1755))) * x) * (s : Equiv.Perm (Fin 1755))⁻¹ := by rw [hc]
        _ = y * ((s : Equiv.Perm (Fin 1755)) * x * (s : Equiv.Perm (Fin 1755))⁻¹) := by group
    · calc (s : Equiv.Perm (Fin 1755)) * x * (s : Equiv.Perm (Fin 1755))⁻¹ *
            ((s : Equiv.Perm (Fin 1755)) * x * (s : Equiv.Perm (Fin 1755))⁻¹)
          = (s : Equiv.Perm (Fin 1755)) * (x * x) * (s : Equiv.Perm (Fin 1755))⁻¹ := by group
        _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
  let act : ↥(S : Subgroup titsD) →* MulAut ↥V :=
    { toFun := fun s =>
        { toFun := fun x => ⟨((s : titsD) : Equiv.Perm (Fin 1755)) * x *
            ((s : titsD) : Equiv.Perm (Fin 1755))⁻¹, hSV s s.2 x x.2⟩
          invFun := fun x => ⟨((s : titsD) : Equiv.Perm (Fin 1755))⁻¹ * x *
            ((s : titsD) : Equiv.Perm (Fin 1755)), by
              have := hSV (s : titsD)⁻¹ (S.inv_mem s.2) x x.2
              simpa using this⟩
          left_inv := fun x => Subtype.ext (by simp [mul_assoc])
          right_inv := fun x => Subtype.ext (by simp [mul_assoc])
          map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
      map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun s t => MulEquiv.ext fun x => Subtype.ext (by simp [mul_assoc]) }
  letI : MulAction ↥(S : Subgroup titsD) ↥V := MulAction.compHom ↥V act
  have hsmul : ∀ (s : ↥(S : Subgroup titsD)) (x : ↥V),
      ((s • x : ↥V) : Equiv.Perm (Fin 1755)) =
        ((s : titsD) : Equiv.Perm (Fin 1755)) * x * ((s : titsD) : Equiv.Perm (Fin 1755))⁻¹ :=
    fun _ _ => rfl
  have hfix : ∀ s : ↥(S : Subgroup titsD), s • (1 : ↥V) = 1 := by
    intro s
    apply Subtype.ext
    rw [hsmul]
    simp
  have hS27 := card_sylow_three_titsD S
  have hidx : ∀ x : ↥V, x ≠ 1 → 9 ∣ (MulAction.stabilizer ↥(S : Subgroup titsD) x).index := by
    intro x hx1
    have hxD : (x : Equiv.Perm (Fin 1755)) ∈ titsD := hVD x.2
    set v : titsD := ⟨x, hxD⟩ with hv
    have hv2 : orderOf v = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        rw [sq]
        exact hV2 x x.2
      · intro h1
        apply hx1
        apply Subtype.ext
        have := congrArg Subtype.val h1
        exact this
    set St := MulAction.stabilizer ↥(S : Subgroup titsD) x with hSt
    have hle : St.map (S : Subgroup titsD).subtype ≤
        (S : Subgroup titsD) ⊓ centralizer ({v} : Set titsD) := by
      rintro _ ⟨s, hs, rfl⟩
      refine Subgroup.mem_inf.2 ⟨s.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfx : s • x = x := hs
      have h1 := congrArg Subtype.val hfx
      rw [hsmul] at h1
      apply Subtype.ext
      change ((s : titsD) : Equiv.Perm (Fin 1755)) * x = x * ((s : titsD) : Equiv.Perm (Fin 1755))
      calc ((s : titsD) : Equiv.Perm (Fin 1755)) * x
          = ((s : titsD) : Equiv.Perm (Fin 1755)) * x * ((s : titsD) : Equiv.Perm (Fin 1755))⁻¹ *
              ((s : titsD) : Equiv.Perm (Fin 1755)) := by group
        _ = x * ((s : titsD) : Equiv.Perm (Fin 1755)) := by rw [h1]
    have hcardSt : Nat.card St ∣ 3 := by
      have h1 : Nat.card St = Nat.card (St.map (S : Subgroup titsD).subtype) :=
        (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
      rw [h1]
      exact (Subgroup.card_dvd_of_le hle).trans
        (card_inf_centralizer_dvd_three S.isPGroup' hv2)
    have hmul := St.card_mul_index
    rw [hS27] at hmul
    rcases (Nat.dvd_prime Nat.prime_three).1 hcardSt with h | h
    · rw [h, one_mul] at hmul
      rw [hmul]
      norm_num
    · rw [h] at hmul
      have : St.index = 9 := by omega
      rw [this]
  have hdvd := dvd_card_sub_one_of_index hfix hidx
  obtain ⟨r, hr⟩ := (hT2.to_le hVT).exists_card_eq
  have hr1 : 1 ≤ r := by
    by_contra h0
    have : r = 0 := by omega
    rw [this, pow_zero] at hr
    exact hVne (Subgroup.eq_bot_of_card_eq V hr)
  have hr5 : r ≤ 5 := by
    have h := hVcard
    rw [hr] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
  rw [hr] at hdvd
  interval_cases r <;> norm_num at hdvd

theorem twoSigTriv_tits_three {K : Type} [Group K] (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .tits)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : TwoSigTriv 3 K := by
  obtain ⟨x, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨eS⟩ := titsModelEquiv K 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact twoSigTriv_titsD.of_mulEquiv eS.symm

end Tits

end CFSG.LocalAnalysis.UniquenessCase.UCK

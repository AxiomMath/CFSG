module

public import CFSG.Timmesfeld.Bridge.RootStructR2Count
public import CFSG.Timmesfeld.Bridge.RootStructR2Number
public import CFSG.Timmesfeld.Bridge.RootStructR2Fix

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem card_dvd_of_free {P X : Type*} [Group P] [MulAction P X] [Finite P] [Finite X]
    (hfree : ∀ (g : P) (x : X), g • x = x → g = 1) : Nat.card P ∣ Nat.card X := by
  classical
  have := Fintype.ofFinite P
  have := Fintype.ofFinite X
  have hstab : ∀ x : X, MulAction.stabilizer P x = ⊥ := fun x => by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
    exact ⟨hfree g x, fun h => by rw [h, one_smul]⟩
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer P X), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  rw [hstab]
  exact (Nat.card_congr (QuotientGroup.quotientBot (G := P)).toEquiv).symm ▸ dvd_refl _

theorem card_dvd_ncard_of_free [Finite G] {P : Subgroup G} {S : Set (Subgroup G)}
    (hS : ∀ g ∈ P, ∀ H ∈ S, H.map (MulAut.conj g).toMonoidHom ∈ S)
    (hfree : ∀ g ∈ P, ∀ H ∈ S, H.map (MulAut.conj g).toMonoidHom = H → g = 1) :
    Nat.card P ∣ S.ncard := by
  let act : MulAction P S :=
    { smul := fun g H => ⟨(H : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom,
        hS g g.2 H H.2⟩
      one_smul := fun H => Subtype.ext (by
        change (H : Subgroup G).map (MulAut.conj (1 : G)).toMonoidHom = H
        rw [map_one]
        exact Subgroup.map_id _)
      mul_smul := fun g g' H => Subtype.ext (by
        change (H : Subgroup G).map (MulAut.conj ((g : G) * g')).toMonoidHom =
          ((H : Subgroup G).map (MulAut.conj (g' : G)).toMonoidHom).map
            (MulAut.conj (g : G)).toMonoidHom
        rw [Subgroup.map_map, map_mul]
        rfl) }
  rw [← Nat.card_coe_set_eq]
  refine card_dvd_of_free fun g H hgH => Subtype.ext ?_
  exact hfree g g.2 H H.2 (congrArg Subtype.val hgH)

theorem map_conj_eq_self_of_commute {H : Subgroup G} {g : G} (hg : ∀ x ∈ H, Commute g x) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, (hg y hy).eq, mul_inv_cancel_right]
    exact hy
  · intro hx
    exact ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, (hg x hx).eq,
      mul_inv_cancel_right]⟩

theorem map_conj_pow_eq {H : Subgroup G} {h : G} (hH : H.map (MulAut.conj h).toMonoidHom = H)
    (j : ℕ) : H.map (MulAut.conj (h ^ j)).toMonoidHom = H := by
  induction j with
  | zero =>
    rw [pow_zero, map_one]
    exact Subgroup.map_id _
  | succ j ih =>
    have e : (MulAut.conj (h ^ (j + 1))).toMonoidHom =
        (MulAut.conj (h ^ j)).toMonoidHom.comp (MulAut.conj h).toMonoidHom := by
      rw [pow_succ, map_mul]
      rfl
    rw [e, ← Subgroup.map_map, hH, ih]

theorem pow_eq_one_of_map_conj_pow_eq [Finite G] {h : G} {S : Set (Subgroup G)}
    (hS : S.ncard = orderOf h)
    (hinv : ∀ i : ℕ, ∀ L ∈ S, L.map (MulAut.conj (h ^ i)).toMonoidHom ∈ S)
    (htrans : ∀ L ∈ S, ∀ L' ∈ S, ∃ i < orderOf h, L.map (MulAut.conj (h ^ i)).toMonoidHom = L')
    {L : Subgroup G} (hL : L ∈ S) {j : ℕ} (hj : L.map (MulAut.conj (h ^ j)).toMonoidHom = L) :
    h ^ j = 1 := by
  have hn : 0 < orderOf h := orderOf_pos h
  let φ : Fin (orderOf h) → S := fun i => ⟨L.map (MulAut.conj (h ^ (i : ℕ))).toMonoidHom,
    hinv i L hL⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨L', hL'⟩
    obtain ⟨i, hi, hiL⟩ := htrans L hL L' hL'
    exact ⟨⟨i, hi⟩, Subtype.ext hiL⟩
  have hbij := hsurj.bijective_of_nat_card_le (by rw [Nat.card_coe_set_eq, hS, Nat.card_fin])
  have hr : φ ⟨j % orderOf h, Nat.mod_lt _ hn⟩ = φ ⟨0, hn⟩ := by
    apply Subtype.ext
    change L.map (MulAut.conj (h ^ (j % orderOf h))).toMonoidHom =
      L.map (MulAut.conj (h ^ 0)).toMonoidHom
    rw [pow_mod_orderOf, hj, pow_zero, map_one]
    exact (Subgroup.map_id _).symm
  have h0 : j % orderOf h = 0 := congrArg Fin.val (hbij.1 hr)
  rw [← pow_mod_orderOf, h0, pow_zero]

theorem exists_pow_eq_of_mem_zpowers [Finite G] {h g : G} (hg : g ∈ Subgroup.zpowers h) :
    ∃ j : ℕ, h ^ j = g :=
  (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hg)

theorem LineSetting.exists_fixed_of_torus (hL : LineSetting G D) (hAll : AllLinesTI D) {a d : G}
    (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    {T T' : Subgroup G} (hT : T ∈ rootLines D a) (hT' : T' ∈ rootLines D a) (hTT' : T ≠ T')
    {h : G} (hh : h ∈ lineGroup D a d) (hord : orderOf h + 2 = (rootLines D a).ncard)
    (hhT : T.map (MulAut.conj h).toMonoidHom = T) (hhT' : T'.map (MulAut.conj h).toMonoidHom = T')
    (htrans : ∀ L ∈ rootLines D a, ∀ L' ∈ rootLines D a, L ≠ T → L ≠ T' → L' ≠ T → L' ≠ T' →
      ∃ i < orderOf h, L.map (MulAut.conj (h ^ i)).toMonoidHom = L')
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p P)
    (hPh : P ≤ Subgroup.zpowers h) :
    ∃ x ∈ D, ¬ Commute a x ∧ Odd (orderOf (a * x)) ∧ OneOpposite D a x ∧
      T ∈ gatedLines D a x ∧ (∀ g ∈ P, g * x * g⁻¹ ∈ rootSet D x) ∧
      Nat.card P ∣ (gatedLines D a x \ {T, T'}).ncard := by
  have := hL.hyp.finite
  have h' := hL.hyp
  have hc := hL.closure
  have hs := hL.special
  have hD := h'.root
  have hclass := h'.isClass
  have hcomm : ∀ g ∈ Subgroup.zpowers h, ∀ t ∈ rootGroup D a, Commute g t := fun g hg t ht =>
    hL.commute_of_mem_lineGroup ha hd had hadD hdT (Subgroup.zpowers_le.2 hh hg) ht
  have hfixa : ∀ g ∈ Subgroup.zpowers h, (rootGroup D a).map (MulAut.conj g).toMonoidHom =
      rootGroup D a := fun g hg => map_conj_eq_self_of_commute (hcomm g hg)
  have hfixT : ∀ g ∈ Subgroup.zpowers h, T.map (MulAut.conj g).toMonoidHom = T := by
    intro g hg
    obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_zpowers hg
    exact map_conj_pow_eq hhT j
  have hfixT' : ∀ g ∈ Subgroup.zpowers h, T'.map (MulAut.conj g).toMonoidHom = T' := by
    intro g hg
    obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_zpowers hg
    exact map_conj_pow_eq hhT' j
  obtain ⟨B, hB, hBfix⟩ := hL.exists_mem_gatedPoints_fixed hAll hp2 hP ha hT
    (fun g hg => hfixa g (hPh hg)) (fun g hg => hfixT g (hPh hg))
  obtain ⟨⟨x, hx, rfl, hax, hoddax, hx1⟩, x', hx', hxx', q, hq, hqT, h4⟩ := hB
  have hx'T : x' ∈ rootSet D x := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx
    (hxx' ▸ rootSet_subset_rootGroup D x' (mem_rootSet_self hx')) (hD.ne_one hx')
  have hTΓ : T ∈ gatedLines D a x :=
    ⟨hT, q, hq, hqT, (orderOf_mul_eq_four_iff_of_mem_rootSet hD hx hx'T hq).1 h4⟩
  have hgx : ∀ g ∈ P, g * x * g⁻¹ ∈ rootSet D x := by
    intro g hg
    have hmem : g * x * g⁻¹ ∈ rootGroup D x := by
      rw [← hBfix g hg]
      exact ⟨x, rootSet_subset_rootGroup D x (mem_rootSet_self hx), rfl⟩
    exact mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx hmem
      (hD.ne_one (conj_mem_of_isClass hclass g hx))
  refine ⟨x, hx, hax, hoddax, hx1, hTΓ, hgx, ?_⟩
  set S := rootLines D a \ {T, T'} with hSdef
  have hTT'sub : ({T, T'} : Set (Subgroup G)) ⊆ rootLines D a := by
    rintro L (rfl | rfl)
    · exact hT
    · exact hT'
  have hSn : S.ncard = orderOf h := by
    rw [hSdef, Set.ncard_sdiff hTT'sub, Set.ncard_pair hTT']
    omega
  have hmapne : ∀ g ∈ Subgroup.zpowers h, ∀ {L : Subgroup G}, L ∉ ({T, T'} : Set _) →
      L.map (MulAut.conj g).toMonoidHom ∉ ({T, T'} : Set _) := by
    intro g hg L hL hLg
    apply hL
    rcases hLg with hLg | hLg
    · left
      exact Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
        (hLg.trans (hfixT g hg).symm)
    · right
      exact Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
        (hLg.trans (hfixT' g hg).symm)
  have hinvS : ∀ g ∈ Subgroup.zpowers h, ∀ L ∈ S, L.map (MulAut.conj g).toMonoidHom ∈ S :=
    fun g hg L hL => ⟨map_conj_mem_rootLines_of_map_eq h' hc hs ha (hfixa g hg) hL.1,
      hmapne g hg hL.2⟩
  have hfree : ∀ g ∈ P, ∀ L ∈ S, L.map (MulAut.conj g).toMonoidHom = L → g = 1 := by
    intro g hg L hL hLg
    obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_zpowers (hPh hg)
    refine pow_eq_one_of_map_conj_pow_eq hSn (fun i L hL => hinvS _ (pow_mem
      (Subgroup.mem_zpowers h) i) L hL) ?_ hL hLg
    intro L₁ hL₁ L₂ hL₂
    simp only [hSdef, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hL₁ hL₂
    exact htrans L₁ hL₁.1 L₂ hL₂.1 hL₁.2.1 hL₁.2.2 hL₂.2.1 hL₂.2.2
  refine card_dvd_ncard_of_free (fun g hg L hL => ⟨?_, hmapne g (hPh hg) hL.2⟩)
    (fun g hg L hL => hfree g hg L ⟨hL.1.1, hL.2⟩)
  have hga : g * a * g⁻¹ ∈ rootSet D a := by
    rw [(hcomm g (hPh hg) a (rootSet_subset_rootGroup D a (mem_rootSet_self ha))).eq,
      mul_inv_cancel_right]
    exact mem_rootSet_self ha
  have := map_conj_mem_gatedLines hclass hL.1 g
  rwa [gatedLines_eq_of_mem_rootSet h' hc hs ha hga hx (hgx g hg)] at this

theorem LineSetting.ordProj_dvd_of_torus {G : Type} [Group G] {D : Set G} (hL : LineSetting G D)
    (hAll : AllLinesTI D) (hTor : RootLinesTorusStep) {Q k : ℕ}
    (hQ : ∀ c ∈ D, (rootLines D c).ncard = Q + 1) (hQ2 : 2 ≤ Q)
    (hk : ∀ a ∈ D, ∀ x ∈ D, ¬ Commute a x → Odd (orderOf (a * x)) → OneOpposite D a x →
      (gatedLines D a x).ncard = k)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ (Q - 1).factorization p ∣ k - 1 ∨ p ^ (Q - 1).factorization p ∣ k - 2 := by
  have := hL.hyp.finite
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha, d, hd, had, hadD, hdT, -⟩ := hL.line
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨T', hT', hne⟩ := hL.exists_ne_mem_rootLines ha hT
  have h3 : 3 ≤ (rootLines D a).ncard := by rw [hQ a ha]; omega
  obtain ⟨h, hh, hord, hhT, hhT', htrans⟩ := hTor G D hL a ha d hd had hadD hdT h3 _ hT T' hT'
    hne.symm
  have horder : orderOf h = Q - 1 := by rw [hQ a ha] at hord; omega
  set e := (Q - 1).factorization p with he
  have hpe : p ^ e ∣ Q - 1 := Nat.ordProj_dvd _ _
  have hm0 : (Q - 1) / p ^ e ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (by omega) hpe) (pow_pos hp.pos e)
    omega
  have horder_u : orderOf (h ^ ((Q - 1) / p ^ e)) = p ^ e := by
    have hdvd : (Q - 1) / p ^ e ∣ orderOf h := by rw [horder]; exact Nat.div_dvd_of_dvd hpe
    rw [orderOf_pow_of_dvd hm0 hdvd, horder, Nat.div_div_self hpe (by omega)]
  have hP : IsPGroup p (Subgroup.zpowers (h ^ ((Q - 1) / p ^ e))) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, horder_u])
  have hPh : Subgroup.zpowers (h ^ ((Q - 1) / p ^ e)) ≤ Subgroup.zpowers h :=
    Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers h) _)
  obtain ⟨x, hx, hax, hoddax, hx1, hTΓ, -, hdvd⟩ := hL.exists_fixed_of_torus hAll ha hd had hadD
    hdT hT hT' hne.symm hh hord hhT hhT' htrans hp2 hP hPh
  rw [Nat.card_zpowers, horder_u] at hdvd
  have hkx := hk a ha x hx hax hoddax hx1
  by_cases hT'Γ : T' ∈ gatedLines D a x
  · right
    have hsub : ({rootGroup D a ⊔ rootGroup D d, T'} : Set (Subgroup G)) ⊆ gatedLines D a x := by
      rintro L (rfl | rfl)
      · exact hTΓ
      · exact hT'Γ
    rwa [Set.ncard_sdiff hsub, Set.ncard_pair hne.symm, hkx] at hdvd
  · left
    have heq : gatedLines D a x \ {rootGroup D a ⊔ rootGroup D d, T'} =
        gatedLines D a x \ {rootGroup D a ⊔ rootGroup D d} := by
      ext L
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · exact fun hL' => ⟨hL'.1, hL'.2.1⟩
      · exact fun hL' => ⟨hL'.1, hL'.2, fun h' => hT'Γ (h' ▸ hL'.1)⟩
    rwa [heq, Set.ncard_sdiff_singleton_of_mem hTΓ, hkx] at hdvd

theorem LineSetting.dvd_sub_one_mul_sub_two {G : Type} [Group G] {D : Set G}
    (hL : LineSetting G D) (hAll : AllLinesTI D) (hTor : RootLinesTorusStep) {Q k : ℕ}
    (hQ : ∀ c ∈ D, (rootLines D c).ncard = Q + 1) (hQ2 : 2 ≤ Q) (hQodd : Odd (Q - 1))
    (hk : ∀ a ∈ D, ∀ x ∈ D, ¬ Commute a x → Odd (orderOf (a * x)) → OneOpposite D a x →
      (gatedLines D a x).ncard = k) :
    Q - 1 ∣ (k - 1) * (k - 2) := by
  rcases Nat.eq_zero_or_pos ((k - 1) * (k - 2)) with h0 | hpos
  · rw [h0]
    exact dvd_zero _
  refine (Nat.factorization_prime_le_iff_dvd (by omega) hpos.ne').1 fun p hp => ?_
  by_cases hp2 : p = 2
  · subst hp2
    rw [Nat.factorization_eq_zero_of_not_dvd (fun h2 => by
      obtain ⟨r, hr⟩ := hQodd
      omega)]
    exact Nat.zero_le _
  · rcases hL.ordProj_dvd_of_torus hAll hTor hQ hQ2 hk hp hp2 with h' | h'
    · exact (hp.pow_dvd_iff_le_factorization hpos.ne').1 (dvd_mul_of_dvd_left h' _)
    · exact (hp.pow_dvd_iff_le_factorization hpos.ne').1 (dvd_mul_of_dvd_right h' _)

theorem LineSetting.gatedLines_card_mem {G : Type} [Group G] {D : Set G} (hL : LineSetting G D)
    (hAll : AllLinesTI D) (hTor : RootLinesTorusStep) {Q k : ℕ}
    (hQ : ∀ c ∈ D, (rootLines D c).ncard = Q + 1) (hQ4 : 4 ≤ Q)
    (hk : ∀ a ∈ D, ∀ x ∈ D, ¬ Commute a x → Odd (orderOf (a * x)) → OneOpposite D a x →
      (gatedLines D a x).ncard = k)
    {a₀ x₀ : G} (ha₀ : a₀ ∈ D) (hx₀ : x₀ ∈ D) (hax₀ : ¬ Commute a₀ x₀)
    (hoddax₀ : Odd (orderOf (a₀ * x₀))) (hx₀1 : OneOpposite D a₀ x₀) :
    k = 1 ∨ k = 2 ∨ k = Q ∨ k = Q + 1 := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  obtain ⟨μ, hμ⟩ := hL.exists_ncard_rootLines ha₀
  rw [hQ a₀ ha₀] at hμ
  have hQμ : Q = 2 ^ μ := by omega
  have hμ2 : 2 ≤ μ := by
    by_contra hμ2
    have : 2 ^ μ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hQodd : Odd (Q - 1) := by
    rw [hQμ]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).1 (isPGroup_rootGroup hclass hD hL.closure ha₀)
  have hdvd := hL.dvd_sub_one_mul_sub_two hAll hTor hQ (by omega) hQodd hk
  have hk₀ := hk a₀ ha₀ x₀ hx₀ hax₀ hoddax₀ hx₀1
  have hk1 : 1 ≤ k := by
    obtain ⟨e, he, hae, haeD, h4⟩ := hx₀1
    have heT : e ∉ rootSet D a₀ := fun h' => by
      have h4a : orderOf (x₀ * a₀) = 4 := by
        rw [orderOf_mul_comm_eq] at h4 ⊢
        exact (orderOf_mul_eq_four_iff_of_mem_rootSet hD ha₀ h' hx₀).1 h4
      rw [orderOf_mul_comm_eq, h4a] at hoddax₀
      exact absurd hoddax₀ (by decide)
    rw [← hk₀]
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨_, ⟨e, he, hae, haeD, heT, rfl⟩, e, he,
      right_mem_line he, h4⟩
  have hkQ : k ≤ Q + 1 := by
    rw [← hk₀, ← hQ a₀ ha₀]
    exact Set.ncard_le_ncard (fun L hL' => hL'.1) (Set.toFinite _)
  have hcount := hL.ncard_oneOmega_mul hAll hQ ha₀ (hk a₀ ha₀)
  obtain ⟨s, t, ht, hst⟩ := Nat.exists_eq_two_pow_mul_odd (n := k) (by omega)
  have htQ : t ∣ Q + 1 := by
    have h1 : t ∣ (Q + 1) * (Nat.card (rootGroup D a₀) * (Q * Nat.card (rootGroup D a₀) *
        (Q * Nat.card (rootGroup D a₀)))) :=
      ⟨(oneOmega D a₀).ncard * 2 ^ s, by rw [← hcount, hst]; ring⟩
    have h2 : Nat.card (rootGroup D a₀) * (Q * Nat.card (rootGroup D a₀) *
        (Q * Nat.card (rootGroup D a₀))) = 2 ^ (r + (μ + r) + (μ + r)) := by
      rw [hr, hQμ]; ring
    rw [h2] at h1
    exact (Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ht)).dvd_of_dvd_mul_right h1
  rcases eq_or_lt_of_le hkQ with hk' | hk'
  · exact Or.inr (Or.inr (Or.inr hk'))
  rcases eq_or_lt_of_le hk1 with hk1' | hk1'
  · exact Or.inl hk1'.symm
  have hdvdZ : ((2 : ℤ) ^ μ - 1) ∣ ((k : ℤ) - 1) * ((k : ℤ) - 2) := by
    have h1 := Int.natCast_dvd_natCast.2 hdvd
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
      hQμ] at h1
    push_cast at h1
    exact h1
  rcases eq_of_dvd_sub_one_mul_sub_two hμ2 hk1 (by omega) ⟨s, t, hst, hQμ ▸ htQ⟩ hdvdZ with
    h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr (Or.inl (h'.trans hQμ.symm)))

end CFSG.Timmesfeld.Bridge

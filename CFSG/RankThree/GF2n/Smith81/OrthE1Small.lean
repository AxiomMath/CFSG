module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement Pointwise

section Generic

theorem isPGroup_zpowers_of_sq_mem {R' : Type} [Group R'] {H : Subgroup R'} (hH : IsPGroup 2 H)
    {x : R'} (hx : x ^ 2 ∈ H) : IsPGroup 2 (Subgroup.zpowers x) := by
  obtain ⟨n, hn⟩ := hH ⟨x ^ 2, hx⟩
  have h1 : (x ^ 2) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h2 : x ^ 2 ^ (n + 1) = 1 := by
    calc x ^ 2 ^ (n + 1) = (x ^ 2) ^ 2 ^ n := by rw [← pow_mul, pow_succ']
      _ = 1 := h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2)
  apply IsPGroup.of_card (n := j)
  rw [Nat.card_zpowers, hj]

theorem normal_sup_zpowers {R' : Type} [Group R'] {H : Subgroup R'} [H.Normal] {x : R'}
    (hcomm : ∀ g : R', g * x * g⁻¹ ∈ H ⊔ Subgroup.zpowers x) :
    (H ⊔ Subgroup.zpowers x).Normal := by
  have key : ∀ g : R', (H ⊔ Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤
      H ⊔ Subgroup.zpowers x := by
    intro g
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr (hcomm g))
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_sup_left (Subgroup.Normal.conj_mem ‹H.Normal› h hh g)
  exact ⟨fun n hn g => key g (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)⟩

theorem mem_pCore_two_of_comm {R' : Type} [Group R'] {H : Subgroup R'} [H.Normal]
    (hH : IsPGroup 2 H) {x : R'} (hx : x ^ 2 ∈ H)
    (hcomm : ∀ g : R', g * x * g⁻¹ * x⁻¹ ∈ H) : x ∈ pCore 2 R' := by
  have hzp := isPGroup_zpowers_of_sq_mem hH hx
  have hT : IsPGroup 2 ↥(H ⊔ Subgroup.zpowers x) := hH.to_sup_of_normal_left hzp
  have hTn : (H ⊔ Subgroup.zpowers x).Normal := normal_sup_zpowers (fun g => by
    have e : g * x * g⁻¹ = g * x * g⁻¹ * x⁻¹ * x := by group
    rw [e]
    exact Subgroup.mul_mem_sup (hcomm g) (Subgroup.mem_zpowers x))
  have hle : H ⊔ Subgroup.zpowers x ≤ pCore 2 R' := le_sSup ⟨hTn, hT⟩
  exact hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

theorem exists_conj_of_sylow2 {R' : Type} [Group R'] [Finite R'] (A B : Subgroup R')
    (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) (hiA : ¬ 2 ∣ A.index) (hiB : ¬ 2 ∣ B.index) :
    ∃ c : R', ∀ x ∈ A, c * x * c⁻¹ ∈ B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq R' (hA.toSylow hiA) (hB.toSylow hiB)
  refine ⟨c, fun x hx => ?_⟩
  have h3 : MulAut.conj c • (A : Subgroup R') = B := by
    have := congrArg (fun P : Sylow 2 R' => (P : Subgroup R')) hc
    rw [Sylow.coe_subgroup_smul] at this
    exact this
  rw [← h3]
  exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) A hx

theorem odd_sub_one_of_two_dvd {a : ℕ} (h2 : 2 ∣ a) (hpos : 0 < a) : Odd (a - 1) := by
  rw [Nat.odd_iff]
  omega

end Generic

section NtFacts

variable {G : Type} [Group G]

theorem nt_conj_mem_Rt (M L : Subgroup G) (t r : G) (hr : r ∈ Rt M L t) (n : G)
    (hn : n ∈ Nt M L t) : r * n * r⁻¹ ∈ Nt M L t := by
  have hn' : n ∈ (pCore 2 ↥(Rt M L t)).map (Rt M L t).subtype := hn
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hn'
  have h := (CFSG.pCore_normal (p := 2) (G := ↥(Rt M L t))).conj_mem k hk ⟨r, hr⟩
  show _ ∈ (pCore 2 ↥(Rt M L t)).map (Rt M L t).subtype
  exact Subgroup.mem_map.mpr ⟨_, h, by simp⟩

theorem rt_le_normalizer_nt (M L : Subgroup G) (t : G) :
    Rt M L t ≤ Subgroup.normalizer (Nt M L t : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact nt_conj_mem_Rt M L t r hr n hn
  · intro hn
    have h := nt_conj_mem_Rt M L t r⁻¹ (inv_mem hr) _ hn
    have e : r⁻¹ * (r * n * r⁻¹) * r⁻¹⁻¹ = n := by group
    rwa [e] at h

end NtFacts


section Helpers

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}

theorem smith23E1_Q_le_Nt (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) :
    Q ≤ Nt M (LB M Q B) t := by
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  haveI : (Q.subgroupOf (Rt M (LB M Q B) t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => hc.hyp.Q_normal.2 (hRM hx)
  have hp : IsPGroup 2 (Q.subgroupOf (Rt M (LB M Q B) t)) :=
    (isPGroup_Q' hc.hyp).comap_of_injective _ (Subgroup.subtype_injective _)
  have hle : Q.subgroupOf (Rt M (LB M Q B) t) ≤ pCore 2 ↥(Rt M (LB M Q B) t) :=
    le_sSup ⟨inferInstance, hp⟩
  calc Q = (Q.subgroupOf (Rt M (LB M Q B) t)).map (Rt M (LB M Q B) t).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQR).symm
    _ ≤ Nt M (LB M Q B) t := Subgroup.map_mono hle

theorem tMemNt_aux (hH : E1Hyp M Q Z B t) : t ∈ Nt M (LB M Q B) t := by
  have hc := hH.ctx
  have htL : t ∈ LB M Q B := hH.mem
  have htR : t ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) htL htL
  haveI : (Q.subgroupOf (Rt M (LB M Q B) t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => hc.hyp.Q_normal.2 (hc.Rt_le_M t hx)
  have hp : IsPGroup 2 (Q.subgroupOf (Rt M (LB M Q B) t)) :=
    (isPGroup_Q' hc.hyp).comap_of_injective _ (Subgroup.subtype_injective _)
  have hx2 : (⟨t, htR⟩ : ↥(Rt M (LB M Q B) t)) ^ 2 ∈ Q.subgroupOf (Rt M (LB M Q B) t) := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hc.sq_mem_Q_of_mem_LB htL
  have hcore : (⟨t, htR⟩ : ↥(Rt M (LB M Q B) t)) ∈ pCore 2 ↥(Rt M (LB M Q B) t) := by
    apply mem_pCore_two_of_comm hp hx2
    intro g
    rw [Subgroup.mem_subgroupOf]
    have h := hc.Rt_comm_mem_Q g.2
    simpa [commutatorElement_def] using h
  exact Subgroup.mem_map.mpr ⟨⟨t, htR⟩, hcore, rfl⟩

end Helpers

theorem ntTI_of (hLine : NtLineStatement) : NtTIStatement := by
  intro G _ _ M Q Z B t hH g hg
  have hc := hH.ctx
  obtain ⟨AM⟩ := ActionModel.nonempty hc.hyp
  obtain ⟨β, -, -, hN, hsurj⟩ := hLine G M Q Z B t hH AM
  have hNH : ∀ x ∈ Nt M (LB M Q B) t, x ∈ H0 M Z := fun x hx =>
    (orthE1_Nt_le_Rt M (LB M Q B) t).trans (hc.Rt_le_H0 t) hx
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc hH.mem
  have hgM : g ∈ M := hg.1
  have hQg : Q ≤ conjSubgroup g (Nt M (LB M Q B) t) := by
    have h : conjSubgroup g Q ≤ conjSubgroup g (Nt M (LB M Q B) t) := Subgroup.map_mono hQN
    rwa [hc.conj_Q_eq hgM] at h
  by_cases hdis : Nt M (LB M Q B) t ⊓ conjSubgroup g (Nt M (LB M Q B) t) = Q
  · exact Or.inl hdis
  right
  obtain ⟨x, hxN, hxNg, hxQ⟩ : ∃ x, x ∈ Nt M (LB M Q B) t ∧
      x ∈ conjSubgroup g (Nt M (LB M Q B) t) ∧ x ∉ Q := by
    by_contra hno
    push Not at hno
    apply hdis
    refine le_antisymm (fun x hx => ?_) (le_inf hQN hQg)
    exact hno x (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2
  have hxH : x ∈ H0 M Z := hNH x hxN
  have hyN : g⁻¹ * x * g ∈ Nt M (LB M Q B) t := mem_conjSubgroup.mp hxNg
  have hyH : g⁻¹ * x * g ∈ H0 M Z := hNH _ hyN
  have hgH : g ∈ H0 M Z := hg
  obtain ⟨c, hc1⟩ := hN ⟨x, hxH⟩ hxN
  obtain ⟨c', hc2⟩ := hN ⟨g⁻¹ * x * g, hyH⟩ hyN
  have hcomm : ∀ (w : G) (hw : w ∈ H0 M Z) (hwg : g⁻¹ * w * g ∈ H0 M Z) (e : AM.M₀.E),
      AM.φ ⟨g, hgH⟩ (AM.φ ⟨g⁻¹ * w * g, hwg⟩ e) = AM.φ ⟨w, hw⟩ (AM.φ ⟨g, hgH⟩ e) := by
    intro w hw hwg e
    have h1 : AM.φ ⟨g, hgH⟩ * AM.φ ⟨g⁻¹ * w * g, hwg⟩ = AM.φ ⟨w, hw⟩ * AM.φ ⟨g, hgH⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group
    simpa only [LinearEquiv.mul_apply] using
      congrArg (fun f : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => f e) h1
  have hc0 : c ≠ 0 := by
    intro h0
    apply hxQ
    have h1 : AM.φ ⟨x, hxH⟩ = 1 := LinearEquiv.ext fun e => by simp [hc1 e, h0]
    exact (AM.φ_ker ⟨x, hxH⟩).mp h1
  have hstar : ∀ e, c • β (AM.φ ⟨g, hgH⟩ e) = c' • AM.φ ⟨g, hgH⟩ (β e) := by
    intro e
    have h1 := hcomm x hxH hyH e
    rw [hc2 e, hc1 (AM.φ ⟨g, hgH⟩ e), map_add, map_smul] at h1
    exact (add_left_cancel h1).symm
  have hβP : ∀ e, β (AM.φ ⟨g, hgH⟩ e) = (c' * c⁻¹) • AM.φ ⟨g, hgH⟩ (β e) := by
    intro e
    calc β (AM.φ ⟨g, hgH⟩ e) = c⁻¹ • (c • β (AM.φ ⟨g, hgH⟩ e)) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • (c' • AM.φ ⟨g, hgH⟩ (β e)) := by rw [hstar e]
      _ = (c' * c⁻¹) • AM.φ ⟨g, hgH⟩ (β e) := by rw [smul_smul, mul_comm]
  have hle : Nt M (LB M Q B) t ≤ conjSubgroup g (Nt M (LB M Q B) t) := by
    intro z hz
    have hzH : z ∈ H0 M Z := hNH z hz
    obtain ⟨d, hd⟩ := hN ⟨z, hzH⟩ hz
    have hz'H : g⁻¹ * z * g ∈ H0 M Z := mul_mem (mul_mem (inv_mem hgH) hzH) hgH
    have hF : ∀ e, AM.φ ⟨g⁻¹ * z * g, hz'H⟩ e = e + (d * (c' * c⁻¹)) • β e := by
      intro e
      apply (AM.φ ⟨g, hgH⟩).injective
      rw [hcomm z hzH hz'H e, hd, hβP e, map_add, map_smul, smul_smul]
    obtain ⟨⟨w, hwH⟩, hwN, hw⟩ := hsurj (d * (c' * c⁻¹))
    have hφ : AM.φ ⟨w, hwH⟩ = AM.φ ⟨g⁻¹ * z * g, hz'H⟩ :=
      LinearEquiv.ext fun e => (hw e).trans (hF e).symm
    have hwz : w⁻¹ * (g⁻¹ * z * g) ∈ Q := by
      have h1 : AM.φ (⟨w, hwH⟩⁻¹ * ⟨g⁻¹ * z * g, hz'H⟩) = 1 := by
        rw [map_mul, map_inv, hφ, inv_mul_cancel]
      exact (AM.φ_ker _).mp h1
    have h2 := (Nt M (LB M Q B) t).mul_mem hwN (hQN hwz)
    rw [mul_inv_cancel_left] at h2
    exact mem_conjSubgroup.mpr h2
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])).symm

theorem tMemNt_of (_hC : NtCentralStatement) (_hN : E1NaturalStatement)
    (_hKF3 : Omega4BasicStatement) : TMemNtStatement := by
  intro G _ _ M Q Z B t hH
  exact tMemNt_aux hH

theorem ntConjLB_of (hSplit : RtSplitStatement) : NtConjLBStatement := by
  intro G _ _ M Q Z B t hH g hgL hleg
  have hc := hH.ctx
  obtain ⟨-, hNX, -, -, -, hLsup, hLX, -, -⟩ := hSplit G M Q Z B t hH
  obtain ⟨-, hNcard, hQuot⟩ := hH.case
  obtain ⟨n, -, hqn, -⟩ := hc.hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hqn] at hq4
    norm_num at hq4
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have htL : t ∈ LB M Q B := hH.mem
  haveI : (Q.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => hc.hyp.Q_normal.2 hx
  have hgM : g ∈ M := Lgen_le_M hc hgL
  have hgM' : g⁻¹ ∈ M := inv_mem hgM
  have hQ2 : IsPGroup 2 Q := isPGroup_Q' hc.hyp
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ2
  set L := LB M Q B with hLdef
  set R := Rt M L t with hRdef
  set N := Nt M L t with hNdef
  set X := E1Xpre M Q B t with hXdef
  have hLR : L ≤ R := le_Rt L htL
  have hNR : N ≤ R := orthE1_Nt_le_Rt M L t
  have hQN : Q ≤ N := smith23E1_Q_le_Nt hc htL
  have hQL : Q ≤ L := le_sup_left
  have hQX : Q ≤ X := le_sup_right
  have hRnorm : R ≤ Subgroup.normalizer (N : Set G) := rt_le_normalizer_nt M L t
  have hNLX : N ⊓ (L ⊓ X) = Q := by
    apply le_antisymm
    · calc N ⊓ (L ⊓ X) ≤ N ⊓ X := inf_le_inf_left _ inf_le_right
        _ = Q := hNX
    · exact le_inf hQN (le_inf hQL hQX)
  have hEN : L ⊓ X ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    hRnorm (hLR (Subgroup.mem_inf.mp hx).1)
  have hLcard : Nat.card L = Nat.card Q * Nat.card Z ^ 3 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hEN
    rw [← hLsup, hNLX, hNcard, hLX] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hQpos
    rw [h1]
    ring
  obtain ⟨u, hu, hRN⟩ : ∃ u : ℕ, Odd u ∧ Nat.card (↥R ⧸ N.subgroupOf R) = Nat.card Z ^ 2 * u := by
    have h2 : 2 ∣ Nat.card Z := by
      rw [hqn]
      exact dvd_pow_self 2 hn0
    have hsq1 : 1 ≤ Nat.card Z ^ 2 := Nat.one_le_pow _ _ hpos
    rcases hQuot with ⟨hnorm, K, hKf, hKfin, hK, ⟨e⟩⟩ | ⟨hnorm, K, hKf, hKfin, hK, b, c, hirr, ⟨e⟩⟩
    · haveI := hnorm
      have _hchar : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (Nat.pos_of_ne_zero hn0) (hK.trans hqn)
      have h := orthE1_card_plus hK hq4 e
      refine ⟨(Nat.card Z ^ 2 - 1) ^ 2,
        Odd.pow (odd_sub_one_of_two_dvd (dvd_pow h2 two_ne_zero) (pow_pos hpos 2)), ?_⟩
      zify [hsq1] at h ⊢
      exact h
    · haveI := hnorm
      have _hchar : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (Nat.pos_of_ne_zero hn0) (hK.trans hqn)
      have h := orthE1_card_minus hK hirr e
      have hsq4 : 1 ≤ Nat.card Z ^ 4 := Nat.one_le_pow _ _ hpos
      refine ⟨Nat.card Z ^ 4 - 1,
        odd_sub_one_of_two_dvd (dvd_pow h2 (by norm_num)) (pow_pos hpos 4), ?_⟩
      zify [hsq1, hsq4] at h ⊢
      exact h
  have hRcard : Nat.card R = Nat.card L * u := by
    rw [← orthE1_card_quot_mul hNR, hRN, hNcard, hLcard]
    ring
  have hidx : ∀ T : Subgroup G, T ≤ R → Nat.card T = Nat.card L →
      (T.subgroupOf R).index = u := by
    intro T hTR hTc
    have h1 := Subgroup.card_mul_index (T.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv, hTc, hRcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hLpow : Nat.card L = 2 ^ (m + 3 * n) := by
    rw [hLcard, hm, hqn]
    ring
  have hpg : ∀ T : Subgroup G, T ≤ R → Nat.card T = Nat.card L →
      IsPGroup 2 (T.subgroupOf R) := by
    intro T hTR hTc
    apply IsPGroup.of_card (n := m + 3 * n)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv, hTc, hLpow]
  obtain ⟨L', hL'⟩ : ∃ L' : Subgroup G, L' = conjSubgroup g⁻¹ L := ⟨_, rfl⟩
  have hL'card : Nat.card L' = Nat.card L := by
    rw [hL']
    exact card_conjSubgroup _ _
  have hL'mem : ∀ y : G, y ∈ L' ↔ g * y * g⁻¹ ∈ L := by
    intro y
    rw [hL', mem_conjSubgroup, inv_inv]
  have hNL' : N ≤ L' := by
    intro x hx
    rw [hL'mem]
    apply hleg
    rw [mem_conjSubgroup]
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e]
    exact hx
  have htc : t ∈ conjSubgroup g⁻¹ L := by
    rw [← hL']
    exact hNL' (tMemNt_aux hH)
  have hL'R : L' ≤ R := by
    rw [hL']
    exact le_iSup₂_of_le g⁻¹ hgM' (le_iSup_of_le htc le_rfl)
  have hpgL : IsPGroup 2 (L.subgroupOf R) := hpg L hLR rfl
  have hpgL' : IsPGroup 2 (L'.subgroupOf R) := hpg L' hL'R hL'card
  have hu2 : ¬ 2 ∣ u := fun h => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)
  have hiL : ¬ 2 ∣ (L.subgroupOf R).index := by
    rw [hidx L hLR rfl]
    exact hu2
  have hiL' : ¬ 2 ∣ (L'.subgroupOf R).index := by
    rw [hidx L' hL'R hL'card]
    exact hu2
  obtain ⟨c, hc'⟩ := exists_conj_of_sylow2 (L.subgroupOf R) (L'.subgroupOf R) hpgL hpgL' hiL hiL'
  have hcG : ∀ x ∈ L, (c : G) * x * (c : G)⁻¹ ∈ L' := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mp (hc' ⟨x, hLR hx⟩ (Subgroup.mem_subgroupOf.mpr hx))
  have hcL : conjSubgroup (c : G) L ≤ L' := by
    intro y hy
    have h := hcG _ (mem_conjSubgroup.mp hy)
    have e : (c : G) * ((c : G)⁻¹ * y * (c : G)) * (c : G)⁻¹ = y := by group
    rwa [e] at h
  have hcL_eq : conjSubgroup (c : G) L = L' :=
    Subgroup.eq_of_le_of_card_ge hcL (le_of_eq (by rw [card_conjSubgroup, hL'card]))
  refine ⟨g * (c : G), mul_mem hgL (Rt_le_Lgen M L t c.2), ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have e : g * (c : G) * x * (g * (c : G))⁻¹ = g * ((c : G) * x * (c : G)⁻¹) * g⁻¹ := by
      group
    constructor
    · intro hx
      rw [e]
      exact (hL'mem _).mp (hcG x hx)
    · intro hx
      rw [e] at hx
      have hy : (c : G) * x * (c : G)⁻¹ ∈ L' := (hL'mem _).mpr hx
      rw [← hcL_eq] at hy
      have h2 := mem_conjSubgroup.mp hy
      have e2 : (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) * (c : G) = x := by group
      rwa [e2] at h2
  · ext z
    rw [mem_conjSubgroup, mem_conjSubgroup]
    have hcN : ∀ w : G, w ∈ N ↔ (c : G)⁻¹ * w * (c : G) ∈ N := fun w => by
      have h := Subgroup.mem_normalizer_iff.mp (hRnorm (inv_mem c.2)) w
      rwa [inv_inv] at h
    have e3 : (g * (c : G))⁻¹ * z * (g * (c : G)) = (c : G)⁻¹ * (g⁻¹ * z * g) * (c : G) := by
      group
    rw [e3]
    exact hcN _

end CFSG.RankThree.GF2n.Smith81.Smith23E1

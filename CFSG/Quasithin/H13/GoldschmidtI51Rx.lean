module

public import CFSG.Quasithin.H13.GoldschmidtI51Dist

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

@[expose] def Rx (Gs : Fin 3 → Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Gs 0 ∧ ∀ p : G ⧸ Gs 0, Col Gs (oPt Gs) p → g • p = p}
  mul_mem' := fun {a b} ha hb => ⟨(Gs 0).mul_mem ha.1 hb.1, fun p hp => by
    rw [mul_smul, hb.2 p hp, ha.2 p hp]⟩
  one_mem' := ⟨(Gs 0).one_mem, fun p _ => one_smul _ _⟩
  inv_mem' := fun {a} ha => ⟨(Gs 0).inv_mem ha.1, fun p hp => by
    rw [inv_smul_eq_iff, ha.2 p hp]⟩

omit [Finite G] in
theorem Rx_conj {h g : G} (hh : h ∈ Gs 0) (hg : g ∈ Rx Gs) : h * g * h⁻¹ ∈ Rx Gs := by
  refine ⟨(Gs 0).mul_mem ((Gs 0).mul_mem hh hg.1) ((Gs 0).inv_mem hh), fun p hp => ?_⟩
  have h1 : Col Gs (oPt Gs) (h⁻¹ • p) := (col_oPt_smul ((Gs 0).inv_mem hh) p).2 hp
  rw [mul_smul, mul_smul, hg.2 _ h1, smul_inv_smul]

theorem loc2_center (hD : IsDSystem .C3 Gs) {n : G} (hn : n ∈ Gs 0 ⊓ Gs 2)
    (hc : ∀ a ∈ Gs 0 ⊓ Gs 2, a * n = n * a) : n ∈ QQ Gs 2 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model2 hD
  have h1 : φ ⟨n, hn.2⟩ ∈ A := by
    rw [← hA]; exact ⟨⟨n, hn.2⟩, Subgroup.mem_subgroupOf.2 hn, rfl⟩
  have h2 : ∀ a ∈ A, a * φ ⟨n, hn.2⟩ = φ ⟨n, hn.2⟩ * a := by
    intro a ha
    rw [← hA] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc x (Subgroup.mem_subgroupOf.1 hx))
  have h3 := hM.centerA _ h1 h2
  rw [← mem_ker_iff_mem_pCoreOf φ hker hn.2]
  exact h3

theorem Rx_le_Q0 (hD : IsDSystem .C3 Gs) {g : G} (hg : g ∈ Rx Gs) : g ∈ QQ Gs 0 := by
  obtain ⟨s0, hs0, hs00⟩ := exists_s0 hD
  refine (gqLoc hD).core g hg.1 (fun h hh => ?_)
  have hpt : g • ((h * s0 : G) : G ⧸ Gs 0) = ((h * s0 : G) : G ⧸ Gs 0) :=
    hg.2 _ (col_oPt.2 ⟨h, hh, s0, hs0, 1, (Gs 0).one_mem, by group⟩)
  have hpt' : ((g * (h * s0) : G) : G ⧸ Gs 0) = ((h * s0 : G) : G ⧸ Gs 0) := hpt
  rw [QuotientGroup.eq] at hpt'
  have hu : h⁻¹ * g * h ∈ Gs 0 :=
    (Gs 0).mul_mem ((Gs 0).mul_mem ((Gs 0).inv_mem hh) hg.1) hh
  have hrel : s0⁻¹ * (h⁻¹ * g * h) * s0 ∈ Gs 0 := by
    have := (Gs 0).inv_mem hpt'
    have e : ((g * (h * s0))⁻¹ * (h * s0))⁻¹ = s0⁻¹ * (h⁻¹ * g * h) * s0 := by group
    rwa [e] at this
  exact ⟨hu, uniq_line hD hs0 hs00 hs0 hu hrel⟩

theorem center_le_Rx (hD : IsDSystem .C3 Gs) {n : G} (hn : n ∈ Gs 0)
    (hc : ∀ a ∈ Gs 0, a * n = n * a) : n ∈ Rx Gs := by
  have hnQ0 : n ∈ QQ Gs 0 := loc0_center hD n hn (fun g hg => hc g hg)
  have hnT := QQ_le_TT hD 0 hnQ0
  have hnQ2 : n ∈ QQ Gs 2 :=
    loc2_center hD ⟨hn, TT_le 2 hnT⟩ (fun a ha => hc a ha.1)
  refine ⟨hn, fun p hp => ?_⟩
  induction p using QuotientGroup.induction_on with | _ a => ?_
  rw [col_oPt] at hp
  obtain ⟨x, hx, s, hs, c, hc', rfl⟩ := hp
  show ((n * (x * s * c) : G) : G ⧸ Gs 0) = ((x * s * c : G) : G ⧸ Gs 0)
  rw [QuotientGroup.eq]
  have e : n * (x * s * c) = x * (n * s) * c := by
    calc n * (x * s * c) = (n * x) * s * c := by group
      _ = (x * n) * s * c := by rw [← hc x hx]
      _ = x * (n * s) * c := by group
  have e2 : (x * (n * s) * c)⁻¹ * (x * s * c) = c⁻¹ * (s⁻¹ * n * s)⁻¹ * c := by group
  rw [e, e2]
  exact (Gs 0).mul_mem ((Gs 0).mul_mem ((Gs 0).inv_mem hc')
    ((Gs 0).inv_mem (Q2_core10 hD n hnQ2 s hs).1)) hc'

theorem stab_Q0_le_Rx (hD : IsDSystem .C3 Gs) {q : G} (hq : q ∈ QQ Gs 0) {z : G ⧸ Gs 0}
    (hz : z ∈ D2 Gs) (hqz : q • z = z) : q ∈ Rx Gs := by
  have hqG0 : q ∈ Gs 0 := TT_le 0 (QQ_le_TT hD 0 hq)
  refine ⟨hqG0, fun p hp => ?_⟩
  by_cases hpo : p = oPt Gs
  · rw [hpo]; exact smul_oPt hqG0
  have hpD : p ∈ Dlt Gs := ⟨hpo, hp⟩
  obtain ⟨h, hh, t, ht, ht0, rfl⟩ := rep_of_Dlt hpD
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨hz1, y, hy, hyz⟩ := hz
  have hg : g ∉ Nbd Gs := fun h' => hz1 (col_oPt.2 h')
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  have ha := col_oPt.1 hy.2
  have hag := col_mk.1 hyz
  obtain ⟨s, hs, hs0, hcol⟩ := line_has_point hD hg ha hag h hh
  have huQ : h⁻¹ * q * h ∈ QQ Gs 0 := by
    simpa using normalizes_pCoreOf (Gs 0) ((Gs 0).inv_mem hh) hq
  have huG1 : h⁻¹ * q * h ∈ Gs 1 := TT_le 1 (QQ_le_TT hD 0 huQ)
  have hc1 : Col Gs ((h * s : G) : G ⧸ Gs 0) (g : G ⧸ Gs 0) :=
    col_mk.2 (by have := Nbd_inv hcol; simpa using this)
  have hc2 := (col_smul q _ _).2 hc1
  rw [hqz] at hc2
  have e : q • ((h * s : G) : G ⧸ Gs 0) = ((h * ((h⁻¹ * q * h) * s) : G) : G ⧸ Gs 0) := by
    show ((q * (h * s) : G) : G ⧸ Gs 0) = _
    congr 1; group
  rw [e] at hc2
  have h2 := col_of_mem hc2
  have hus := line_point_unique hD hg hh hs hs0 ((Gs 1).mul_mem huG1 hs) hcol h2
  have hs'u : s⁻¹ * (h⁻¹ * q * h) * s ∈ Gs 0 := by simpa [mul_assoc] using hus
  have huQ1 : h⁻¹ * q * h ∈ QQ Gs 1 := (fix_iff hD hs hs0 huQ).1 hs'u
  show ((q * (h * t) : G) : G ⧸ Gs 0) = ((h * t : G) : G ⧸ Gs 0)
  rw [QuotientGroup.eq]
  have e3 : (q * (h * t))⁻¹ * (h * t) = (t⁻¹ * (h⁻¹ * q * h) * t)⁻¹ := by group
  rw [e3]
  exact (Gs 0).inv_mem (TT_le 0 (QQ_le_TT hD 1 (by
    simpa using normalizes_pCoreOf (Gs 1) ((Gs 1).inv_mem ht) huQ1)))

omit [Finite G] in
theorem D2_smul (_hD : IsDSystem .C3 Gs) {q : G} (hq : q ∈ Gs 0) {z : G ⧸ Gs 0} (hz : z ∈ D2 Gs) :
    q • z ∈ D2 Gs := by
  obtain ⟨hz1, y, hy, hyz⟩ := hz
  refine ⟨fun h => hz1 ((col_oPt_smul hq z).1 h), q • y, ⟨?_, ?_⟩, (col_smul q y z).2 hyz⟩
  · intro he
    apply hy.1
    have : q • y = q • oPt Gs := by rw [he, smul_oPt hq]
    exact MulAction.injective q this
  · exact (col_oPt_smul hq y).2 hy.2

theorem Q0_card_le_of_Rx_trivial (hD : IsDSystem .C3 Gs) (hR : ∀ g ∈ Rx Gs, g = 1) :
    Nat.card ↥(QQ Gs 0) ≤ 32 := by
  have hne : (D2 Gs).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [ncard_D2 hD]; norm_num)
  obtain ⟨z, hz⟩ := hne
  let f : ↥(QQ Gs 0) → ↥(D2 Gs) := fun q =>
    ⟨(q : G) • z, D2_smul hD (TT_le 0 (QQ_le_TT hD 0 q.2)) hz⟩
  have hinj : Function.Injective f := by
    intro q1 q2 h12
    have h12' : (q1 : G) • z = (q2 : G) • z := congrArg Subtype.val h12
    have hfix : ((q1 : G)⁻¹ * q2) • z = z := by
      rw [mul_smul, ← h12', inv_smul_smul]
    have hmem : (q1 : G)⁻¹ * q2 ∈ QQ Gs 0 := (QQ Gs 0).mul_mem ((QQ Gs 0).inv_mem q1.2) q2.2
    have := hR _ (stab_Q0_le_Rx hD hmem hz hfix)
    apply Subtype.ext
    have h3 : (q1 : G) = q2 := by
      have := congrArg (fun w => (q1 : G) * w) this
      simpa using this.symm
    exact h3
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_coe_set_eq, ncard_D2 hD] at this
  exact this

theorem Rx_ne (hD : IsDSystem .C3 Gs) : ∃ g ∈ Rx Gs, g ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hle := Q0_card_le_of_Rx_trivial hD hcon
  rcases hD.d5 rfl with hz | hbig
  · obtain ⟨n, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hz)
    have hcen : ∀ a ∈ Gs 0, a * (n : ↥(Gs 0)) = (n : ↥(Gs 0)) * a := fun a ha =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 n.2 ⟨a, ha⟩)
    have := center_le_Rx hD (n : ↥(Gs 0)).2 hcen
    exact hn1 (Subtype.ext (Subtype.ext (hcon _ this)))
  · have : Nat.card ↥(pCoreOf 2 (Gs 0)) ≤ 32 := hle
    omega

theorem D2_rep (hD : IsDSystem .C3 Gs) {s0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    {z : G ⧸ Gs 0} (hz : z ∈ D2 Gs) :
    ∃ h1 ∈ Gs 0, ∃ w ∈ Fpts Gs, z = h1 • (s0 • w) := by
  obtain ⟨q0, hq0, hq01⟩ := exists_q0 hD
  obtain ⟨hz1, y, hy, hyz⟩ := hz
  have hy' := hy
  rw [Dlt_eq_orbit hD hs0 hs00 hq0 hq01, MulAction.mem_orbit_iff] at hy'
  obtain ⟨h1, rfl⟩ := hy'
  have h1' : ((h1 : ↥(Gs 0)) • ((s0 : G) : G ⧸ Gs 0)) = (h1 : G) • ((s0 : G) : G ⧸ Gs 0) := rfl
  rw [h1'] at hyz
  have hz1' : (h1 : G)⁻¹ • z ∈ Ey Gs ((s0 : G) : G ⧸ Gs 0) := by
    refine ⟨fun h => hz1 ?_, ?_⟩
    · have := (col_oPt_smul ((Gs 0).inv_mem h1.2) z).1 h
      exact this
    · have := (col_smul (h1 : G)⁻¹ _ z).2 hyz
      rwa [inv_smul_smul] at this
  rw [Ey_s0 hD hs0 hs00] at hz1'
  obtain ⟨w, hw, hwz⟩ := hz1'
  refine ⟨h1, h1.2, w, hw, ?_⟩
  have hwz' : s0 • w = (h1 : G)⁻¹ • z := hwz
  rw [hwz', smul_inv_smul]

theorem Fpts_trans (hD : IsDSystem .C3 Gs) {s0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    {w w' : G ⧸ Gs 0} (hw : w ∈ Fpts Gs) (hw' : w' ∈ Fpts Gs) :
    ∃ k ∈ Gs 0, s0 * k * s0⁻¹ ∈ Gs 0 ∧ k • w = w' := by
  obtain ⟨hwD, hwF⟩ := hw
  obtain ⟨hwD', hwF'⟩ := hw'
  obtain ⟨f, hf, t, ht, ht0, rfl⟩ := rep_of_Dlt hwD
  obtain ⟨f', hf', t', ht', ht'0, rfl⟩ := rep_of_Dlt hwD'
  rw [lineOf_eq hD hf ht ht0] at hwF
  rw [lineOf_eq hD hf' ht' ht'0] at hwF'
  have hnf := far_of_lineOf (x := ⟨f, hf⟩) hwF
  have hnf' := far_of_lineOf (x := ⟨f', hf'⟩) hwF'
  obtain ⟨k, hk, hks, hkc⟩ := T16 hD ((Gs 1).inv_mem hs0)
    (fun h => hs00 (by simpa using (Gs 0).inv_mem h)) hf hnf ht ht0 hf' hnf' ht' ht'0
  refine ⟨k, hk, by simpa using hks, ?_⟩
  show ((k * (f * t) : G) : G ⧸ Gs 0) = ((f' * t' : G) : G ⧸ Gs 0)
  rw [QuotientGroup.eq]
  have := (Gs 0).inv_mem hkc
  have e : ((f' * t')⁻¹ * (k * f * t))⁻¹ = (k * (f * t))⁻¹ * (f' * t') := by group
  rw [e.symm.symm] at this
  simpa [mul_assoc] using this

theorem D2_trans (hD : IsDSystem .C3 Gs) {z z' : G ⧸ Gs 0} (hz : z ∈ D2 Gs) (hz' : z' ∈ D2 Gs) :
    ∃ h ∈ Gs 0, h • z = z' := by
  obtain ⟨s0, hs0, hs00⟩ := exists_s0 hD
  obtain ⟨h1, hh1, w, hw, rfl⟩ := D2_rep hD hs0 hs00 hz
  obtain ⟨h2, hh2, w', hw', rfl⟩ := D2_rep hD hs0 hs00 hz'
  obtain ⟨k, hk, hks, hkw⟩ := Fpts_trans hD hs0 hs00 hw hw'
  refine ⟨h2 * (s0 * k * s0⁻¹) * h1⁻¹,
    (Gs 0).mul_mem ((Gs 0).mul_mem hh2 hks) ((Gs 0).inv_mem hh1), ?_⟩
  simp only [mul_smul, inv_smul_smul, hkw]

end CFSG.Quasithin.H13.I51

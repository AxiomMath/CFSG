module

public import CFSG.Monster.B.CTIB.Census
public import CFSG.Monster.B.TwoA.Amalgam.CoFiber

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native
  CFSG.Monster.B.Short CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam

theorem rs0_eq :
    rs 0 = xs := by
  show hs 0 * qS 4194304 = xs
  rw [show hs 0 = 1 from rfl, one_mul, show (4194304 : ℕ) = 2 ^ 22 by norm_num, qS_two_pow_22]

theorem rs1_eq :
    rs 1 = qS 1 := by
  show hs 0 * qS 1 = qS 1
  rw [show hs 0 = 1 from rfl, one_mul]

theorem rs2_eq :
    rs 2 = qS 3 := by
  show hs 0 * qS 3 = qS 3
  rw [show hs 0 = 1 from rfl, one_mul]

theorem rs3_eq :
    rs 3 = qS 7 := by
  show hs 0 * qS 7 = qS 7
  rw [show hs 0 = 1 from rfl, one_mul]

theorem census_valid_one : censusValid 1 = true := by decide
theorem census_valid_three : censusValid 3 = true := by decide
theorem census_valid_seven : censusValid 7 = true := by decide

theorem psiS_qS_ne_zero
    {r : ℕ} (hr : censusValid r = true) : psiS (qS r) ≠ 0 :=
  vecW_ne_zero hr

theorem qS_ne_one
    {r : ℕ} (hr : censusValid r = true) : qS r ≠ 1 := fun h => by
  apply psiS_qS_ne_zero hr
  rw [h, psiS_one]

theorem xs_ne_one : xs ≠ 1 := fun h => xbar_ne_one (op_injective h)

theorem mem_censusRecs {r : ℕ × ℕ} (hr : r ∈ censusRecs) :
    r = (1, 2300) ∨ r = (3, 46575) ∨ r = (7, 2049300) ∨ r = (17, 1619200) ∨ r = (19, 476928) := by
  simpa [censusRecs] using hr

theorem census_ncard
    (r : ℕ × ℕ) (hr : r ∈ censusRecs) : (jOrbit (qS r.1)).ncard = r.2 :=
  (census_facts hr).2.1

theorem ncard_jOrbit_one :
    (jOrbit (qS 1)).ncard = 2300 := census_ncard (1, 2300) (by decide)
theorem ncard_jOrbit_three :
    (jOrbit (qS 3)).ncard = 46575 := census_ncard (3, 46575) (by decide)
theorem ncard_jOrbit_seven :
    (jOrbit (qS 7)).ncard = 2049300 :=
  census_ncard (7, 2049300) (by decide)
theorem ncard_jOrbit_17 :
    (jOrbit (qS 17)).ncard = 1619200 :=
  census_ncard (17, 1619200) (by decide)
theorem ncard_jOrbit_19 :
    (jOrbit (qS 19)).ncard = 476928 :=
  census_ncard (19, 476928) (by decide)

theorem census_cover'
    {w : WS} (hw : w ≠ 0) :
    w ∈ jOrbit (qS 1) ∨ w ∈ jOrbit (qS 3) ∨ w ∈ jOrbit (qS 7) ∨ w ∈ jOrbit (qS 17) ∨
      w ∈ jOrbit (qS 19) := by
  obtain ⟨r, hr, hw⟩ := census_cover hw
  rcases mem_censusRecs hr with rfl | rfl | rfl | rfl | rfl
  · exact .inl hw
  · exact .inr (.inl hw)
  · exact .inr (.inr (.inl hw))
  · exact .inr (.inr (.inr (.inl hw)))
  · exact .inr (.inr (.inr (.inr hw)))

theorem orbits_ne_zero
    {w : WS} {r : ℕ} (hr : r ∈ [1, 3, 7, 17, 19]) (hw : w ∈ jOrbit (qS r)) :
    w ≠ 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ne_zero_of_mem_census (r := (1, 2300)) (by decide) hw
  · exact ne_zero_of_mem_census (r := (3, 46575)) (by decide) hw
  · exact ne_zero_of_mem_census (r := (7, 2049300)) (by decide) hw
  · exact ne_zero_of_mem_census (r := (17, 1619200)) (by decide) hw
  · exact ne_zero_of_mem_census (r := (19, 476928)) (by decide) hw

theorem orbit_set :
    {O : Set WS | ∃ y ∈ Qs, psiS y ≠ 0 ∧ O = jOrbit y} =
    {jOrbit (qS 1), jOrbit (qS 3), jOrbit (qS 7), jOrbit (qS 17), jOrbit (qS 19)} := by
  ext O
  constructor
  · rintro ⟨y, hy, h0, rfl⟩
    rcases census_cover' h0 with h | h | h | h | h
    · exact .inl (jOrbit_eq_of_mem (qS_mem _) hy h)
    · exact .inr (.inl (jOrbit_eq_of_mem (qS_mem _) hy h))
    · exact .inr (.inr (.inl (jOrbit_eq_of_mem (qS_mem _) hy h)))
    · exact .inr (.inr (.inr (.inl (jOrbit_eq_of_mem (qS_mem _) hy h))))
    · exact .inr (.inr (.inr (.inr (jOrbit_eq_of_mem (qS_mem _) hy h))))
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨_, qS_mem 1, psiS_qS_ne_zero (by decide), rfl⟩
    · exact ⟨_, qS_mem 3, psiS_qS_ne_zero (by decide), rfl⟩
    · exact ⟨_, qS_mem 7, psiS_qS_ne_zero (by decide), rfl⟩
    · exact ⟨_, qS_mem 17, psiS_qS_ne_zero (by decide), rfl⟩
    · exact ⟨_, qS_mem 19, psiS_qS_ne_zero (by decide), rfl⟩

theorem sq_one_of_mem
    {y : Sbp} (hy : y ∈ Qs)
    (h : psiS y ∈ jOrbit (qS 1) ∪ jOrbit (qS 3) ∪ jOrbit (qS 7)) : y * y = 1 := by
  rcases h with (h | h) | h
  · rw [sq_eq_of_mem_jOrbit hy (qS_mem _) h, sq_qS_one (.inl rfl)]
  · rw [sq_eq_of_mem_jOrbit hy (qS_mem _) h, sq_qS_one (.inr (.inl rfl))]
  · rw [sq_eq_of_mem_jOrbit hy (qS_mem _) h, sq_qS_one (.inr (.inr rfl))]

theorem sq_x_of_mem
    {y : Sbp} (hy : y ∈ Qs) (h : psiS y ∈ jOrbit (qS 17) ∪ jOrbit (qS 19)) :
    y * y = xs := by
  rcases h with h | h
  · rw [sq_eq_of_mem_jOrbit hy (qS_mem _) h, sq_qS_x (.inl rfl)]
  · rw [sq_eq_of_mem_jOrbit hy (qS_mem _) h, sq_qS_x (.inr rfl)]

theorem ncard_jClass_qS
    {r : ℕ} (hr : censusValid r = true) :
    (jClass (qS r)).ncard = 2 * (jOrbit (qS r)).ncard := by
  rw [jClass_eq_fiber (qS_mem r) (psiS_qS_ne_zero hr), ncard_fiber]

theorem mem_jClass_of
    {t : Sbp} {r : ℕ} (hr : censusValid r = true) (ht : t ∈ Qs)
    (h : psiS t ∈ jOrbit (qS r)) : t ∈ jClass (qS r) := by
  rw [jClass_eq_fiber (qS_mem r) (psiS_qS_ne_zero hr)]
  exact ⟨ht, h⟩

theorem invs_eq :
    {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} =
    jClass (rs 0) ∪ jClass (rs 1) ∪ jClass (rs 2) ∪ jClass (rs 3) := by
  rw [rs0_eq, rs1_eq, rs2_eq, rs3_eq]
  ext t
  constructor
  · rintro ⟨ht, hsq, hne⟩
    by_cases h0 : psiS t = 0
    · rcases eq_of_psiS_eq ht Qs.one_mem (h0.trans psiS_one.symm) with h | h
      · exact absurd h hne
      · rw [mul_one] at h
        subst h
        exact .inl (.inl (.inl (mem_jClass_self xs)))
    · rcases census_cover' h0 with h | h | h | h | h
      · exact .inl (.inl (.inr (mem_jClass_of (by decide) ht h)))
      · exact .inl (.inr (mem_jClass_of (by decide) ht h))
      · exact .inr (mem_jClass_of (by decide) ht h)
      · exact absurd (hsq.symm.trans (sq_x_of_mem ht (.inl h))) xs_ne_one.symm
      · exact absurd (hsq.symm.trans (sq_x_of_mem ht (.inr h))) xs_ne_one.symm
  · have key : ∀ z, z ∈ Qs → z * z = 1 → z ≠ 1 → ∀ t ∈ jClass z, t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1 := by
      rintro z hz hsq hne _ ⟨g, hg, rfl⟩
      refine ⟨conj_mem_Qs hg hz, ?_, fun h => hne ?_⟩
      · calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
          _ = 1 := by rw [hsq]; group
      · calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
    rintro (((h | h) | h) | h)
    · exact key xs xs_mem xs_mul_self xs_ne_one t h
    · exact key _ (qS_mem 1) (sq_qS_one (.inl rfl)) (qS_ne_one (by decide)) t h
    · exact key _ (qS_mem 3) (sq_qS_one (.inr (.inl rfl))) (qS_ne_one (by decide)) t h
    · exact key _ (qS_mem 7) (sq_qS_one (.inr (.inr rfl))) (qS_ne_one (by decide)) t h

theorem ncard_jClass_rs0 :
    (jClass (rs 0)).ncard = 1 := by
  rw [rs0_eq, jClass_xs, Set.ncard_singleton]

theorem ncard_jClass_rs1 :
    (jClass (rs 1)).ncard = 4600 := by
  rw [rs1_eq, ncard_jClass_qS (by decide), ncard_jOrbit_one]

theorem ncard_jClass_rs2 :
    (jClass (rs 2)).ncard = 93150 := by
  rw [rs2_eq, ncard_jClass_qS (by decide), ncard_jOrbit_three]

theorem ncard_jClass_rs3 :
    (jClass (rs 3)).ncard = 4098600 := by
  rw [rs3_eq, ncard_jClass_qS (by decide), ncard_jOrbit_seven]

theorem class_set :
    {C : Set Sbp | ∃ t, t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1 ∧ C = jClass t} =
    {jClass (rs 0), jClass (rs 1), jClass (rs 2), jClass (rs 3)} := by
  ext C
  constructor
  · rintro ⟨t, ht, hsq, hne, rfl⟩
    have hmem : t ∈ {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} := ⟨ht, hsq, hne⟩
    rw [invs_eq] at hmem
    rcases hmem with ((h | h) | h) | h
    · exact .inl (jClass_eq_of_mem h)
    · exact .inr (.inl (jClass_eq_of_mem h))
    · exact .inr (.inr (.inl (jClass_eq_of_mem h)))
    · exact .inr (.inr (.inr (jClass_eq_of_mem h)))
  · have hmem : ∀ i, i < 4 → rs i ∈ {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} := by
      intro i hi
      rw [invs_eq]
      interval_cases i
      · exact .inl (.inl (.inl (mem_jClass_self _)))
      · exact .inl (.inl (.inr (mem_jClass_self _)))
      · exact .inl (.inr (mem_jClass_self _))
      · exact .inr (mem_jClass_self _)
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, (hmem 0 (by norm_num)).1, (hmem 0 (by norm_num)).2.1, (hmem 0 (by norm_num)).2.2,
        rfl⟩
    · exact ⟨_, (hmem 1 (by norm_num)).1, (hmem 1 (by norm_num)).2.1, (hmem 1 (by norm_num)).2.2,
        rfl⟩
    · exact ⟨_, (hmem 2 (by norm_num)).1, (hmem 2 (by norm_num)).2.1, (hmem 2 (by norm_num)).2.2,
        rfl⟩
    · exact ⟨_, (hmem 3 (by norm_num)).1, (hmem 3 (by norm_num)).2.1, (hmem 3 (by norm_num)).2.2,
        rfl⟩

theorem classes_disjoint :
    [jClass (rs 0), jClass (rs 1), jClass (rs 2), jClass (rs 3)].Pairwise Disjoint := by
  have hn : ∀ i < 4, (jClass (rs i)).ncard = [1, 4600, 93150, 4098600].getD i 0 := by
    intro i hi
    interval_cases i
    · exact ncard_jClass_rs0
    · exact ncard_jClass_rs1
    · exact ncard_jClass_rs2
    · exact ncard_jClass_rs3
  have hd : ∀ i < 4, ∀ j < 4, i ≠ j → Disjoint (jClass (rs i)) (jClass (rs j)) := by
    intro i hi j hj hij
    refine jClass_disjoint ?_
    rw [hn i hi, hn j hj]
    interval_cases i <;> interval_cases j <;> simp_all
  rw [show [jClass (rs 0), jClass (rs 1), jClass (rs 2), jClass (rs 3)] =
    (List.range 4).map fun i => jClass (rs i) from rfl, List.pairwise_map]
  exact List.pairwise_lt_range.imp_of_mem fun {i j} hi hj hij =>
    hd i (List.mem_range.1 hi) j (List.mem_range.1 hj) (by omega)

@[expose] noncomputable def labelS : Sbp := op ((ehatEquiv.symm cE : Ebar) : Cbar)

theorem labelS_mem : labelS ∈ Qs := (ehatEquiv.symm cE).2

theorem iotaD_labelS : iotaD labelS.unop = cQ := by
  show iotaD ((ehatEquiv.symm cE : Ebar) : Cbar) = cQ
  rw [← coe_ehatEquiv, MulEquiv.apply_symm_apply]
  rfl

theorem wv_psiS_labelS :
    wvEquiv hv0 (psiS labelS) = Unitary.sigmaW := by
  rw [psiS_of_mem labelS_mem, ← native_Co2_coset_fiber_data.2.2.2.1,
    ← MulEquiv.apply_symm_apply ehatEquiv cE, psiW_ehatEquiv]
  rfl

theorem image_range_wvEquiv {a b : L2} (h : a = b) (x : Wv a) :
    wvEquiv h '' (Set.range fun k : Kstab a => wAct a k x) =
      Set.range fun k : Kstab b => wAct b k (wvEquiv h x) := by
  subst h
  ext w
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (wvEquiv_wAct rfl k x).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, wvEquiv_wAct rfl k x⟩

theorem ncard_jOrbit_labelS :
    (jOrbit labelS).ncard = 2300 := by
  have himg : wvEquiv hv0 '' jOrbit labelS = Unitary.OmegaW := by
    rw [jOrbit_eq_range labelS_mem, image_range_wvEquiv, wv_psiS_labelS,
      native_Co2_coset_fiber_data.2.2.2.2.1]
    rfl
  rw [← Set.ncard_image_of_injective _ (wvEquiv hv0).injective, himg,
    native_Co2_coset_fiber_data.2.2.2.2.2.1]

theorem psiS_labelS_ne_zero :
    psiS labelS ≠ 0 := by
  intro h0
  have hsub : jOrbit labelS ⊆ {0} := by
    rintro _ ⟨g, hg, rfl⟩
    rw [psiS_conj hg labelS_mem, h0, map_zero]
    rfl
  have := Set.ncard_le_ncard hsub (Set.finite_singleton 0)
  rw [ncard_jOrbit_labelS, Set.ncard_singleton] at this
  omega

theorem labelS_mem_jClass :
    labelS ∈ jClass (qS 1) := by
  have h1 : psiS labelS ∈ jOrbit (qS 1) := by
    rcases census_cover' psiS_labelS_ne_zero with h | h | h | h | h
    · exact h
    all_goals
      have e := congrArg Set.ncard (jOrbit_eq_of_mem (qS_mem _) labelS_mem h)
      rw [ncard_jOrbit_labelS] at e
      first
        | rw [ncard_jOrbit_three] at e | rw [ncard_jOrbit_seven] at e
        | rw [ncard_jOrbit_17] at e | rw [ncard_jOrbit_19] at e
      omega
  exact mem_jClass_of (by decide) labelS_mem h1

theorem sClass_eq {a b g : Sbp} (h : a = g⁻¹ * b * g) :
    {u | ∃ k : Sbp, u = k⁻¹ * a * k} = {u | ∃ k : Sbp, u = k⁻¹ * b * k} := by
  subst h
  ext u
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨g * k, by group⟩
  · rintro ⟨k, rfl⟩
    exact ⟨g⁻¹ * k, by group⟩

theorem image_sClass_labelS :
    (fun u : Sbp => (toShat u : Dfull)) '' {u | ∃ k : Sbp, u = k⁻¹ * labelS * k} =
      {d | ∃ g : Shat, d = (g : Dfull)⁻¹ * cQ * g} := by
  ext d
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨(toShat k)⁻¹, ?_⟩
    show iotaD (k⁻¹ * labelS * k).unop = (iotaD k.unop)⁻¹⁻¹ * cQ * (iotaD k.unop)⁻¹
    rw [unop_mul, unop_mul, unop_inv, map_mul, map_mul, map_inv, iotaD_labelS, inv_inv,
      mul_assoc]
  · rintro ⟨g, rfl⟩
    obtain ⟨c, hc⟩ := g.2
    refine ⟨op c * labelS * (op c)⁻¹, ⟨(op c)⁻¹, by rw [inv_inv]⟩, ?_⟩
    show iotaD (op c * labelS * (op c)⁻¹).unop = (g : Dfull)⁻¹ * cQ * g
    simp only [unop_mul, unop_inv, unop_op]
    rw [map_mul, map_mul, map_inv, iotaD_labelS, hc, mul_assoc]

theorem range_clabel :
    Set.range clabel = {d | ∃ g : Shat, d = (g : Dfull)⁻¹ * cQ * g} := by
  ext d
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨g, rfl⟩ := cvOf_surjective v
    exact ⟨g, clabel_cvOf g⟩
  · rintro ⟨g, rfl⟩
    exact ⟨cvOf g, clabel_cvOf g⟩

theorem native_core_involution_orbit_census :
    {O : Set WS | ∃ y ∈ Qs, psiS y ≠ 0 ∧ O = jOrbit y} =
      {jOrbit (qS 1), jOrbit (qS 3), jOrbit (qS 7), jOrbit (qS 17), jOrbit (qS 19)} ∧
    (∀ w : WS, w ≠ 0 ↔ ∃ r ∈ [1, 3, 7, 17, 19], w ∈ jOrbit (qS r)) ∧
    [jOrbit (qS 1), jOrbit (qS 3), jOrbit (qS 7), jOrbit (qS 17), jOrbit (qS 19)].Pairwise
      Disjoint ∧
    (jOrbit (qS 1)).ncard = 2300 ∧ (jOrbit (qS 3)).ncard = 46575 ∧
    (jOrbit (qS 7)).ncard = 2049300 ∧ (jOrbit (qS 17)).ncard = 1619200 ∧
    (jOrbit (qS 19)).ncard = 476928 ∧
    (∀ y ∈ Qs, psiS y ∈ jOrbit (qS 1) ∪ jOrbit (qS 3) ∪ jOrbit (qS 7) → y * y = 1) ∧
    (∀ y ∈ Qs, psiS y ∈ jOrbit (qS 17) ∪ jOrbit (qS 19) → y * y = xs) ∧
    rs 0 = xs ∧ rs 1 = qS 1 ∧ rs 2 = qS 3 ∧ rs 3 = qS 7 ∧
    {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} =
      jClass (rs 0) ∪ jClass (rs 1) ∪ jClass (rs 2) ∪ jClass (rs 3) ∧
    {C : Set Sbp | ∃ t, t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1 ∧ C = jClass t} =
      {jClass (rs 0), jClass (rs 1), jClass (rs 2), jClass (rs 3)} ∧
    [jClass (rs 0), jClass (rs 1), jClass (rs 2), jClass (rs 3)].Pairwise Disjoint ∧
    (jClass (rs 0)).ncard = 1 ∧ (jClass (rs 1)).ncard = 4600 ∧
    (jClass (rs 2)).ncard = 93150 ∧ (jClass (rs 3)).ncard = 4098600 ∧
    (fun u : Sbp => (toShat u : Dfull)) '' {u | ∃ g : Sbp, u = g⁻¹ * rs 1 * g} =
      {d | ∃ g : Shat, d = (g : Dfull)⁻¹ * cQ * g} ∧
    Set.range clabel = {d | ∃ g : Shat, d = (g : Dfull)⁻¹ * cQ * g} := by
  refine ⟨orbit_set, fun w => ⟨fun hw => ?_, fun ⟨r, hr, hw⟩ => orbits_ne_zero hr hw⟩,
    censusList_disjoint, ncard_jOrbit_one, ncard_jOrbit_three, ncard_jOrbit_seven, ncard_jOrbit_17,
    ncard_jOrbit_19, fun y hy h => sq_one_of_mem hy h, fun y hy h => sq_x_of_mem hy h, rs0_eq,
    rs1_eq, rs2_eq, rs3_eq, invs_eq, class_set, classes_disjoint, ncard_jClass_rs0,
    ncard_jClass_rs1, ncard_jClass_rs2, ncard_jClass_rs3, ?_, range_clabel⟩
  · rcases census_cover' hw with h | h | h | h | h
    · exact ⟨1, by simp, h⟩
    · exact ⟨3, by simp, h⟩
    · exact ⟨7, by simp, h⟩
    · exact ⟨17, by simp, h⟩
    · exact ⟨19, by simp, h⟩
  · obtain ⟨g, -, hg⟩ := labelS_mem_jClass
    rw [rs1_eq, ← sClass_eq hg]
    exact image_sClass_labelS

end CFSG.Monster.B.CTIB

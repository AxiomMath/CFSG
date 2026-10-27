module

public import CFSG.Quasithin.Vol2.KGFactJ4M3Q
public import CFSG.Quasithin.H13.KGFactA314J4
public import CFSG.Quasithin.H13.KGFactT3J4Lat

public section

namespace CFSG.Quasithin.J4M3

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9
  CFSG.Quasithin.KGC31 CFSG.Quasithin.Special2 CFSG.Quasithin.J4Fam CFSG.Quasithin.J4Rad
open CFSG.LieType.BorelTits (le_pCoreOf_of_le_normalizer le_normalizer_pCoreOf)
open CFSG.Open (pCoreOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped commutatorElement

theorem card_eq_120_of_odd {R : Subgroup (Equiv.Perm (Fin 5))} (h60 : 60 ∣ Nat.card R)
    (hodd : ∃ g ∈ R, Equiv.Perm.sign g = -1) : Nat.card R = 120 := by
  have h120 : Nat.card R ∣ 120 := by
    have := Subgroup.card_subgroup_dvd_card R
    rw [Nat.card_perm, Nat.card_fin] at this
    exact this
  obtain ⟨t, ht⟩ := h60
  have ht2 : t ∣ 2 := by
    rw [ht] at h120
    exact Nat.dvd_of_mul_dvd_mul_left (k := 60) (by norm_num) (by simpa using h120)
  have ht' : t = 1 ∨ t = 2 := by
    have := Nat.le_of_dvd (by norm_num) ht2
    interval_cases t <;> simp_all
  rcases ht' with rfl | rfl
  · exfalso
    obtain ⟨g, hgR, hg⟩ := hodd
    set s : ↥R →* ℤˣ := Equiv.Perm.sign.comp R.subtype with hs
    have hsurj : Function.Surjective s := by
      intro u
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact ⟨1, map_one s⟩
      · exact ⟨⟨g, hgR⟩, hg⟩
    have hker : Nat.card s.ker = 30 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup s.ker
      have h2 : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective s hsurj).toEquiv, h2, ht] at h1
      omega
    set K' : Subgroup (alternatingGroup (Fin 5)) :=
      (s.ker.map R.subtype).subgroupOf (alternatingGroup (Fin 5)) with hK'
    have hle : s.ker.map R.subtype ≤ alternatingGroup (Fin 5) := by
      rintro _ ⟨x, hx, rfl⟩
      exact Equiv.Perm.mem_alternatingGroup.mpr hx
    have hK'card : Nat.card K' = 30 := by
      rw [hK', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
        Subgroup.card_map_of_injective R.subtype_injective, hker]
    have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      have := two_mul_card_alternatingGroup (α := Fin 5)
      rw [Fintype.card_perm, Fintype.card_fin] at this
      rw [Nat.card_eq_fintype_card]
      have h5 : Nat.factorial 5 = 120 := rfl
      omega
    have hidx : K'.index = 2 := by
      have := Subgroup.card_mul_index K'
      rw [hK'card, hA] at this
      omega
    have hN : K'.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal K') with h | h
    · rw [h, Subgroup.card_bot] at hK'card
      omega
    · rw [h, Subgroup.card_top, hA] at hK'card
      omega
  · rw [ht]

section Pts


theorem eta_mem_M3 (c : ℕ) : eta uJ 11 c ∈ M3 :=
  D_le_M3 (Eg_le_D j4Facts.mat (eta_mem_Eg 11 le_rfl c))

theorem gPt_mem_M3 (c : ℕ) : gPt c ∈ M3 :=
  M3.mul_mem (eta_mem_M3 c) nJ_mem_normalizer

theorem gPt_mem_X5 (c : ℕ) : gPt c • basePt ∈ X5 :=
  ⟨gPt c, gPt_mem_M3 c, rfl⟩

theorem X5_smul_mem {m : J} (hm : m ∈ M3) {w : J ⧸ Hj} (hw : w ∈ X5) : m • w ∈ X5 := by
  obtain ⟨m', hm', rfl⟩ := hw
  exact ⟨m * m', M3.mul_mem hm hm', mul_smul _ _ _⟩

theorem pJ_mem_Hj {i : ℕ} (hi : i < 12) : pJ i ∈ Hj := by
  unfold pJ
  split_ifs with h
  · exact Eg_le_Hj (eta_mem_Eg 11 le_rfl _)
  · exact wordProd_mem_Hj (sWords_letters (i - 6) (by omega))

theorem xM_mem_Hj : xM ∈ Hj := wordProd_mem_Hj xWord_letters

theorem cJ_mem_Hj : cJ ∈ Hj := wordProd_mem_Hj cWord_letters

noncomputable abbrev K3 : Subgroup J := Subgroup.centralizer (V0 : Set J) ⊓ fixingSubgroup J X5

theorem M3_le_normalizer_K3 : M3 ≤ Subgroup.normalizer (K3 : Set J) := by
  intro m hm
  refine CFSG.Quasithin.A4.mem_normalizer_of_conj_mem fun k hk => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V0 := by
      have := (Subgroup.mem_normalizer_iff.mp (M3.inv_mem hm) v).mp hv
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).1 _ hv'
    calc v * (m * k * m⁻¹) = m * ((m⁻¹ * v * m) * k) * m⁻¹ := by group
      _ = m * (k * (m⁻¹ * v * m)) * m⁻¹ := by rw [hc]
      _ = m * k * m⁻¹ * v := by group
  · rw [mem_fixingSubgroup_iff]
    intro w hw
    have h1 := (mem_fixingSubgroup_iff J).mp (Subgroup.mem_inf.mp hk).2 _
      (X5_smul_mem (M3.inv_mem hm) hw)
    rw [mul_smul, mul_smul, h1, smul_inv_smul]

end Pts

section X5


theorem X5_eq : X5 = {basePt, gPt 0 • basePt, gPt 1 • basePt, gPt 16 • basePt,
    gPt 17 • basePt} := by
  have h0 : (0 : ℕ) ∈ ptMasks := by simp [ptMasks]
  have h1 : (1 : ℕ) ∈ ptMasks := by simp [ptMasks]
  have h16 : (16 : ℕ) ∈ ptMasks := by simp [ptMasks]
  have h17 : (17 : ℕ) ∈ ptMasks := by simp [ptMasks]
  have hsub : ({basePt, gPt 0 • basePt, gPt 1 • basePt, gPt 16 • basePt, gPt 17 • basePt} :
      Set (J ⧸ Hj)) ⊆ X5 := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact basePt_mem_X5
    all_goals exact gPt_mem_X5 _
  have hne : ∀ {c d : ℕ}, c ∈ ptMasks → d ∈ ptMasks → c ≠ d → gPt c • basePt ≠ gPt d • basePt :=
    fun hc hd hcd h => hcd (gPt_inj hc hd h)
  have hcard : ({basePt, gPt 0 • basePt, gPt 1 • basePt, gPt 16 • basePt, gPt 17 • basePt} :
      Set (J ⧸ Hj)).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_singleton]
    · simp only [Set.mem_singleton_iff]
      exact hne h16 h17 (by norm_num)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne h1 h16 (by norm_num), hne h1 h17 (by norm_num)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne h0 h1 (by norm_num), hne h0 h16 (by norm_num), hne h0 h17 (by norm_num)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨(gPt_ne_basePt h0).symm, (gPt_ne_basePt h1).symm, (gPt_ne_basePt h16).symm,
        (gPt_ne_basePt h17).symm⟩
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_X5 j4Facts, hcard])
    (Set.toFinite _)).symm

theorem fix_X5 {y : J} (hyH : y ∈ Hj) (hy : ∀ c ∈ ptMasks, y • (gPt c • basePt) = gPt c • basePt) :
    ∀ w ∈ X5, y • w = w := by
  rw [X5_eq]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact smul_basePt_eq_self_iff.mpr hyH
  · exact hy 0 (by simp [ptMasks])
  · exact hy 1 (by simp [ptMasks])
  · exact hy 16 (by simp [ptMasks])
  · exact hy 17 (by simp [ptMasks])

theorem pJ_mem_fix {i : ℕ} (hi : i < 12) : pJ i ∈ fixingSubgroup J X5 :=
  (mem_fixingSubgroup_iff J).mpr (fix_X5 (pJ_mem_Hj hi) fun _ hc => pJ_fix hi hc)

theorem xM_mem_fix : xM ∈ fixingSubgroup J X5 :=
  (mem_fixingSubgroup_iff J).mpr (fix_X5 xM_mem_Hj fun _ hc => xM_fix hc)

theorem V0_le_fix : V0 ≤ fixingSubgroup J X5 := by
  have hM := j4Facts.mat
  intro v hv
  have hvE : v ∈ Eg uJ 11 := V0_le_Eg' hM hv
  refine (mem_fixingSubgroup_iff J).mpr (fix_X5 (Eg_le_Hj hvE) fun c _ => ?_)
  have hn := nJ_mem_normalizer
  have hv' : nJ⁻¹ * v * nJ ∈ V0 := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) v).mp hv
    simpa using this
  have hH : nJ⁻¹ * v * nJ ∈ Hj := Eg_le_Hj (V0_le_Eg' hM hv')
  rw [smul_smul, smul_basePt_eq_iff]
  have e : (gPt c)⁻¹ * (v * gPt c) = nJ⁻¹ * v * nJ := by
    have hcomm : v * eta uJ 11 c = eta uJ 11 c * v :=
      Eg_comm (elem_uJ hM) hvE (eta_mem_Eg 11 le_rfl c)
    calc (gPt c)⁻¹ * (v * gPt c)
        = nJ⁻¹ * ((eta uJ 11 c)⁻¹ * (v * eta uJ 11 c)) * nJ := by rw [gPt]; group
      _ = nJ⁻¹ * ((eta uJ 11 c)⁻¹ * (eta uJ 11 c * v)) * nJ := by rw [hcomm]
      _ = nJ⁻¹ * v * nJ := by group
  rw [e]
  exact hH

theorem Q_le_K3 : Qg ≤ K3 := by
  refine sup_le ((Subgroup.closure_le _).mpr ?_) ?_
  · rintro _ ⟨i, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => qJ_centralizes i.2 v hv, ?_⟩
    show ⁅pJ i, xM⁆ ∈ fixingSubgroup J X5
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (pJ_mem_fix i.2) xM_mem_fix)
      (Subgroup.inv_mem _ (pJ_mem_fix i.2))) (Subgroup.inv_mem _ xM_mem_fix)
  · rw [eSub_v0]
    exact le_inf (fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw =>
      V0_comm j4Facts.mat w hw v hv) V0_le_fix

theorem rho3_eq_one_of_fix {m : ↥M3} (hm : ∀ w ∈ X5, (m : J) • w = w) : rho3 j4Facts m = 1 := by
  refine Equiv.Perm.ext fun j => ?_
  obtain ⟨x, rfl⟩ := (eOrb j4Facts).surjective j
  rw [rho3_apply, Equiv.Perm.coe_one, id]
  congr 1
  apply Subtype.ext
  have hx : (x : J ⧸ Hj) ∈ X5 := orbit_M3_eq ▸ x.2
  exact hm _ hx

theorem cJ_mem_centralizer : cJ ∈ Subgroup.centralizer (V0 : Set J) := by
  have hle : V0 ≤ Subgroup.centralizer {cJ} := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl | rfl
    · exact (cJ_commute (by simp [v0Gens])).symm
    · exact (cJ_commute (by simp [v0Gens])).symm
    · exact (cJ_commute (by simp [v0Gens])).symm
  exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hv)

theorem cJ_mem_M3 : cJ ∈ M3 := D_le_M3 cJ_mem_centralizer

theorem gPt_mem_orb (c : ℕ) : gPt c • basePt ∈ OrbM3 := by
  have h := gPt_mem_X5 c
  rw [← orbit_M3_eq] at h
  exact h

theorem sign_rho3_cJ : Equiv.Perm.sign (rho3 j4Facts ⟨cJ, cJ_mem_M3⟩) = -1 := by
  classical
  set a : ↥OrbM3 := ⟨gPt 16 • basePt, gPt_mem_orb 16⟩ with ha
  set b : ↥OrbM3 := ⟨gPt 17 • basePt, gPt_mem_orb 17⟩ with hb
  have hab : a ≠ b := fun h =>
    absurd (gPt_inj (by simp [ptMasks]) (by simp [ptMasks]) (congrArg Subtype.val h))
      (by norm_num)
  have hσ : MulAction.toPermHom ↥M3 ↥OrbM3 ⟨cJ, cJ_mem_M3⟩ = Equiv.swap a b := by
    obtain ⟨h0, h1, h16, h17⟩ := cJ_points
    refine Equiv.ext fun x => Subtype.ext ?_
    have hx : (x : J ⧸ Hj) ∈ X5 := orbit_M3_eq ▸ x.2
    rw [X5_eq] at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    show cJ • (x : J ⧸ Hj) = ((Equiv.swap a b x : ↥OrbM3) : J ⧸ Hj)
    have hxa : (x : J ⧸ Hj) = gPt 16 • basePt → x = a := fun h => Subtype.ext h
    have hxb : (x : J ⧸ Hj) = gPt 17 • basePt → x = b := fun h => Subtype.ext h
    have hna : ∀ c ∈ ptMasks, c ≠ 16 → (x : J ⧸ Hj) = gPt c • basePt → x ≠ a := by
      intro c hc hc16 h e
      rw [e] at h
      exact hc16 (gPt_inj (by simp [ptMasks]) hc h).symm
    have hnb : ∀ c ∈ ptMasks, c ≠ 17 → (x : J ⧸ Hj) = gPt c • basePt → x ≠ b := by
      intro c hc hc17 h e
      rw [e] at h
      exact hc17 (gPt_inj (by simp [ptMasks]) hc h).symm
    rcases hx with h | h | h | h | h
    · have hxa' : x ≠ a := fun e => gPt_ne_basePt (c := 16) (by simp [ptMasks])
        ((congrArg Subtype.val e).symm.trans h)
      have hxb' : x ≠ b := fun e => gPt_ne_basePt (c := 17) (by simp [ptMasks])
        ((congrArg Subtype.val e).symm.trans h)
      rw [Equiv.swap_apply_of_ne_of_ne hxa' hxb', h]
      exact smul_basePt_eq_self_iff.mpr cJ_mem_Hj
    · rw [Equiv.swap_apply_of_ne_of_ne (hna 0 (by simp [ptMasks]) (by norm_num) h)
        (hnb 0 (by simp [ptMasks]) (by norm_num) h), h]
      exact h0
    · rw [Equiv.swap_apply_of_ne_of_ne (hna 1 (by simp [ptMasks]) (by norm_num) h)
        (hnb 1 (by simp [ptMasks]) (by norm_num) h), h]
      exact h1
    · rw [hxa h, Equiv.swap_apply_left]
      rw [h] at *
      exact h16
    · rw [hxb h, Equiv.swap_apply_right]
      rw [h] at *
      exact h17
  have e : rho3 j4Facts ⟨cJ, cJ_mem_M3⟩ =
      (eOrb j4Facts).permCongr (MulAction.toPermHom ↥M3 ↥OrbM3 ⟨cJ, cJ_mem_M3⟩) := by
    refine Equiv.ext fun j => ?_
    obtain ⟨x, rfl⟩ := (eOrb j4Facts).surjective j
    rw [rho3_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rfl
  rw [e, Equiv.Perm.sign_permCongr, hσ, Equiv.Perm.sign_swap hab]

theorem card_ker_rho3_Dm : Nat.card ((rho3 j4Facts).comp Dm.subtype).ker = 2 ^ 15 := by
  have h60 := sixty_dvd_card_rho3 j4Facts
  have hcDm : (⟨cJ, cJ_mem_M3⟩ : ↥M3) ∈ Dm := Subgroup.mem_subgroupOf.mpr cJ_mem_centralizer
  have hodd : ∃ g ∈ ((rho3 j4Facts).comp Dm.subtype).range, Equiv.Perm.sign g = -1 :=
    ⟨_, ⟨⟨⟨cJ, cJ_mem_M3⟩, hcDm⟩, rfl⟩, sign_rho3_cJ⟩
  have h120 := card_eq_120_of_odd h60 hodd
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ((rho3 j4Facts).comp Dm.subtype).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, card_Dm j4Facts, h120] at h
  rw [show (2 : ℕ) ^ 15 = 32768 by norm_num]
  omega

theorem card_K3_le : Nat.card ↥K3 ≤ 2 ^ 15 := by
  rw [← card_ker_rho3_Dm]
  have hmem : ∀ k : ↥K3, (⟨(k : J), D_le_M3 (Subgroup.mem_inf.mp k.2).1⟩ : ↥M3) ∈ Dm :=
    fun k => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp k.2).1
  refine Nat.card_le_card_of_injective (fun k => ⟨⟨⟨k, D_le_M3 (Subgroup.mem_inf.mp k.2).1⟩,
    hmem k⟩, ?_⟩) ?_
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact rho3_eq_one_of_fix ((mem_fixingSubgroup_iff J).mp (Subgroup.mem_inf.mp k.2).2)
  · intro a b h
    have := congrArg (fun x : ((rho3 j4Facts).comp Dm.subtype).ker => ((x : ↥Dm) : ↥M3).1) h
    exact Subtype.ext this

theorem K3_eq_Q : K3 = Qg := by
  symm
  apply Subgroup.eq_of_le_of_card_ge Q_le_K3
  rw [card_Q]
  exact card_K3_le

end X5

section Core


theorem P0_le_M3 : P0 ≤ M3 := CFSG.Quasithin.H13.KGT3J4.P0_le_NV.trans inf_le_right

theorem isSylowTwoOf_P0_M3 : IsSylowTwoOf P0 M3 := by
  have hF := j4Facts
  refine ⟨P0_le_M3, isPGroup_P0 hF, ?_⟩
  have h := Subgroup.card_mul_index (P0.subgroupOf M3)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P0_le_M3).toEquiv, card_P0 hF.mat hF,
    card_M3 hF] at h
  omega

theorem pCoreOf_le_P0 : pCoreOf 2 M3 ≤ P0 :=
  CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf isSylowTwoOf_P0_M3

theorem pCoreOf_le_fix : pCoreOf 2 M3 ≤ fixingSubgroup J X5 := by
  intro q hq
  refine (mem_fixingSubgroup_iff J).mpr fun w hw => ?_
  obtain ⟨m, hm, rfl⟩ := hw
  have hN := le_normalizer_pCoreOf 2 M3 (M3.inv_mem hm)
  have hq' : m⁻¹ * q * m ∈ pCoreOf 2 M3 := by
    have := (Subgroup.mem_normalizer_iff.mp hN q).mp hq
    simpa using this
  have hH : m⁻¹ * q * m ∈ Hj := P0_le_Hj (pCoreOf_le_P0 hq')
  calc q • (m • basePt) = m • ((m⁻¹ * q * m) • basePt) := by
        rw [smul_smul, smul_smul, show q * m = m * (m⁻¹ * q * m) by group]
    _ = m • basePt := by rw [smul_basePt_eq_self_iff.mpr hH]

theorem pCoreOf_le_centralizer_V0 : pCoreOf 2 M3 ≤ Subgroup.centralizer (V0 : Set J) := by
  have hM := j4Facts.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α : ↥M3 →* MulAut ↥V0 := V0.normalizerMonoidHom with hα
  have hsurj : Function.Surjective α := by
    intro σ
    obtain ⟨n, hn⟩ := conjAut_NV_surjective hM σ
    exact ⟨Subgroup.inclusion CV_le_normalizer n, hn⟩
  have hNn : ((pCoreOf 2 M3).subgroupOf M3).Normal := by
    refine ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M3 g.2) n).mp
      (Subgroup.mem_subgroupOf.mp hn)
    simpa using this
  have hN2 : IsPGroup 2 ↥((pCoreOf 2 M3).subgroupOf M3) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M3).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 M3)).symm
  have hsimp := isSimpleGroup_mulAut_of_subgroup_eight V0 (V0_comm hM) (V0_sq hM) (card_V0 hM)
  have hNmap : (((pCoreOf 2 M3).subgroupOf M3).map α).Normal := hNn.map α hsurj
  have himg : ((pCoreOf 2 M3).subgroupOf M3).map α = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((pCoreOf 2 M3).subgroupOf M3).map α) with
      h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := (hN2.map α).exists_card_eq
      rw [h, Subgroup.card_top, card_mulAut_V0 hM] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 168)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  intro q hq
  have hqM : q ∈ M3 := CFSG.LieType.BorelTits.pCoreOf_le 2 M3 hq
  have h1 : α ⟨q, hqM⟩ ∈ ((pCoreOf 2 M3).subgroupOf M3).map α := ⟨⟨q, hqM⟩, hq, rfl⟩
  rw [himg, Subgroup.mem_bot] at h1
  exact (normalizerMonoidHom_eq_one_iff' V0 ⟨q, hqM⟩).mp h1

theorem pCoreOf_le_K3 : pCoreOf 2 M3 ≤ K3 := le_inf pCoreOf_le_centralizer_V0 pCoreOf_le_fix

theorem K3_le_pCoreOf : K3 ≤ pCoreOf 2 M3 := by
  refine le_pCoreOf_of_le_normalizer 2 (fun k hk => D_le_M3 (Subgroup.mem_inf.mp hk).1)
    M3_le_normalizer_K3 ?_
  rw [K3_eq_Q]
  exact IsPGroup.of_card card_Q

theorem pCoreOf_M3_eq : pCoreOf 2 M3 = Qg :=
  le_antisymm (pCoreOf_le_K3.trans K3_eq_Q.le) (K3_eq_Q ▸ K3_le_pCoreOf)

theorem special_pCoreOf_M3 : IsSpecial2Group 3 12 ↥(pCoreOf 2 M3) := by
  rw [pCoreOf_M3_eq]
  exact Q_special

theorem centralizer_pCoreOf_M3_le :
    Subgroup.centralizer ((pCoreOf 2 M3 : Subgroup J) : Set J) ≤ V0 := by
  intro c hc
  have hV0 : V0 ≤ pCoreOf 2 M3 := pCoreOf_M3_eq ▸ V0_le_Q
  have hcV : c ∈ Subgroup.centralizer (V0 : Set J) :=
    Subgroup.mem_centralizer_iff.mpr fun v hv => Subgroup.mem_centralizer_iff.mp hc v (hV0 hv)
  have hcQ : c ∈ pCoreOf 2 M3 :=
    CFSG.Quasithin.H13.KGA314J4.charTwo_M3 ⟨D_le_M3 hcV, hc⟩
  rw [pCoreOf_M3_eq] at hcQ hc
  refine mem_V0_of_commute hcQ fun j => ?_
  exact (Subgroup.mem_centralizer_iff.mp hc (qF j) (mem_tabGroup j)).symm

theorem M3_maximal [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    ∀ X : Subgroup J, M3 ≤ X → X = M3 ∨ X = ⊤ := by
  intro X hX
  by_cases htop : X = ⊤
  · exact Or.inr htop
  left
  have hP : P0 ≤ X := P0_le_M3.trans hX
  have hcases : X ≤ Hj ∨ X ≤ Subgroup.centralizer ({z0} : Set J) ∨
      X ≤ Subgroup.normalizer (V0 : Set J) := by
    by_cases hs : Group.IsSolvable ↥X
    · exact overgroup_of_solvable hP hs
    · exact CFSG.Quasithin.J4Ov.j4OvergroupLocal_holds X hP htop hs
  rcases hcases with h | h | h
  · exfalso
    have hn : nJ ∈ Hj := h (hX nJ_mem_normalizer)
    apply gPt_ne_basePt (c := 0) (by simp [ptMasks])
    rw [gPt, eta_zero, one_mul]
    exact smul_basePt_eq_self_iff.mpr hn
  · exfalso
    have hx : xM ∈ Subgroup.centralizer ({z0} : Set J) := h (hX xM_mem_normalizer)
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    apply xM_ne
    rw [hx, mul_inv_cancel_right]
  · exact le_antisymm h hX

end Core

end CFSG.Quasithin.J4M3

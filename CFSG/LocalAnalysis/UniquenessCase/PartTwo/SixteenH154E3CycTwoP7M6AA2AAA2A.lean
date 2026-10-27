module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA2AAA2AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23CoreA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycTwoP7M6AA2AAA2A_le_of_normal_of_relIndex
    {A : Type} [Group A] [Finite A] {H P : Subgroup A}
    (hnorm : (P.subgroupOf H).Normal) (hrank : IsElemAbelianOfRank 7 3 ↥P)
    (hrel : ¬ 7 ∣ P.relIndex H) :
    ∀ Q : Subgroup A, Q ≤ H → IsPGroup 7 ↥Q → Q ≤ P := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hPp : IsPGroup 7 ↥P := by
    obtain ⟨e⟩ := hrank
    exact (ZModModule.isPGroup_multiplicative (n := 7) (G := Fin 3 → ZMod 7)).of_equiv e.symm
  have hP' : IsPGroup 7 (P.subgroupOf H) := hPp.comap_subtype
  have hrel' : ¬ 7 ∣ (P.subgroupOf H).index := hrel
  let S7 : Sylow 7 ↥H := hP'.toSylow hrel'
  haveI : (S7 : Subgroup ↥H).Normal := hnorm
  intro Q hQH hQ
  obtain ⟨R, hR⟩ := (hQ.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H S7 R
  have hRS : R = S7 := by rw [← hg, Sylow.smul_eq_of_normal]
  intro x hx
  have hx' : (⟨x, hQH hx⟩ : ↥H) ∈ R := hR hx
  rw [hRS] at hx'
  exact hx'

theorem s16h_e3_CycTwoP7M6AA2AAA2A_exists_normal_sylow_structure
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs2 : s15 D.M V₀ V hV L = 2)
    (hres : ∀ q ∈ D.sig, q = p ∨
      (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ q = 3))
    (hp7 : p = 7) (hm : rk ↥(wTil V₀ V hV L) = 6)
    (hbad : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    ∃ P : Subgroup (MulAut (Vtil V₀ V hV)),
      P ≤ Mbar D.M V₀ V hV ∧
      (P.subgroupOf (Mbar D.M V₀ V hV)).Normal ∧
      IsElemAbelianOfRank 7 3 ↥P ∧
      ¬ 7 ∣ P.relIndex (Mbar D.M V₀ V hV) ∧
      (∀ Q : Subgroup (MulAut (Vtil V₀ V hV)), Q ≤ Mbar D.M V₀ V hV →
        IsPGroup 7 ↥Q → Q ≤ P) := by
  classical
  set W : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L with hWdef
  set Lb : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L with hLbdef
  set B : Subgroup (MulAut (Vtil V₀ V hV)) :=
    Mbar D.M V₀ V hV ⊓ normalizer (Lb : Set (MulAut (Vtil V₀ V hV))) with hBdef
  have hsq : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hWsq : ∀ w : W, w ^ 2 = 1 := fun w => Subtype.ext (hsq (w : Vtil V₀ V hV))
  have hodd7 : Odd 7 := by decide
  have hLbcard : Nat.card ↥Lb = 7 := by
    have h1 : Nat.card ↥(lBar V₀ V hV L) = p := hLp.2
    rw [← hLbdef] at h1
    rw [h1, hp7]
  have hoddLb : Odd (Nat.card ↥Lb) := by rw [hLbcard]; exact hodd7
  haveI : IsCyclic ↥Lb := hLp.1
  letI : CommGroup ↥Lb := IsCyclic.commGroup
  have hLstab : Lb ≤ stabSub W := by
    intro g hg
    rw [mem_stabSub]
    have hcomm : ∀ x ∈ Lb, g * x = x * g := by
      intro x hx
      exact congrArg Subtype.val (mul_comm (⟨g, hg⟩ : ↥Lb) ⟨x, hx⟩)
    have hcommi : ∀ x ∈ Lb, g⁻¹ * x = x * g⁻¹ := by
      intro x hx
      exact congrArg Subtype.val (mul_comm ((⟨g, hg⟩ : ↥Lb)⁻¹) ⟨x, hx⟩)
    intro u
    constructor
    · intro hu
      have hmem : g⁻¹ (g u) ∈ W :=
        CFSG.Quasithin.Asc81c.Pf.commSub_stable_of_commute (X := Lb) hcommi hu
      simpa using hmem
    · intro hu
      exact CFSG.Quasithin.Asc81c.Pf.commSub_stable_of_commute (X := Lb) hcomm hu
  have hLbB : Lb ≤ B := by
    refine le_inf ?_ ?_
    · rw [hLbdef]
      exact barSub_mono V₀ V hV h.hyp151.le
    · exact Subgroup.le_normalizer
  have hAnorm : autSub B W ≤ normalizer ((autSub Lb W : Subgroup (MulAut W)) : Set _) :=
    s15_T7_autSub_le_normalizer (E := Lb) (A := B) (U := W)
      (inf_le_right : B ≤ normalizer (Lb : Set _))
  have hLn : ∀ g ∈ autSub B W,
      (autSub Lb W).map (MulAut.conj g).toMonoidHom = autSub Lb W := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAnorm hg)
  have hLbCentBot : Lb ⊓ centSub W = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
    have hoddx : Odd (orderOf x) :=
      Odd.of_dvd_nat hoddLb (Subgroup.orderOf_dvd_natCard Lb hxL)
    have hfix : ∀ s ∈ W, x s = s := fun s hs => hxC s hs
    have hgen : ∀ v : Vtil V₀ V hV, x v * v⁻¹ ∈ W := fun v =>
      Subgroup.subset_closure ⟨x, hxL, v, Subgroup.mem_top v, rfl⟩
    have hx1 : x = 1 :=
      CFSG.Quasithin.Asc81c.Pf.eq_one_of_stab (W := Vtil V₀ V hV) hsq hoddx hfix hgen
    simpa using hx1
  have hKcard : Nat.card ↥(autSub Lb W) = 7 := by
    have hcard := card_autSub_mul (A := Lb) (U := W) hLstab
    have hcent : Nat.card ↥(Lb ⊓ centSub W) = 1 := by rw [hLbCentBot, Subgroup.card_bot]
    rw [hcent, mul_one, hLbcard] at hcard
    exact hcard
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Lb)
  have hgcard : orderOf g = 7 := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hLbcard
  set l : MulAut (Vtil V₀ V hV) := (g : MulAut (Vtil V₀ V hV)) with hldef
  have hlmem : l ∈ Lb := g.2
  have hlstab : l ∈ stabSub W := hLstab hlmem
  have hLbz : Lb = Subgroup.zpowers l := by
    have htop : Subgroup.zpowers g = ⊤ := (Subgroup.zpowers g).eq_top_iff'.mpr hg
    have hmap : (Subgroup.zpowers g).map Lb.subtype = Subgroup.zpowers l :=
      MonoidHom.map_zpowers Lb.subtype g
    rw [htop] at hmap
    rw [← hmap]
    exact le_antisymm (fun x hx => ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩)
      (Subgroup.map_subtype_le (⊤ : Subgroup ↥Lb))
  have hmapinc : (⊤ : Subgroup ↥Lb).map (Subgroup.inclusion hLstab) =
      Lb.subgroupOf (stabSub W) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have h1 : (⊤ : Subgroup ↥Lb).map (Subgroup.inclusion hLstab) =
      Subgroup.zpowers (⟨l, hlstab⟩ : stabSub W) := by
    have htop : Subgroup.zpowers g = (⊤ : Subgroup ↥Lb) :=
      (Subgroup.zpowers g).eq_top_iff'.mpr hg
    rw [← htop, MonoidHom.map_zpowers]
    congr 1
  set X : MulAut W := resHom W ⟨l, hlstab⟩ with hXdef
  have hLz : autSub Lb W = Subgroup.zpowers X := by
    unfold autSub
    rw [← hmapinc, h1, MonoidHom.map_zpowers]
  have hXorder : orderOf X = 7 := by
    have h := Nat.card_zpowers X
    rw [← hLz, hKcard] at h
    exact h.symm
  have hfixVbot : fixV (autSub Lb W) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hmem : (w : Vtil V₀ V hV) ∈
        fixV Lb ⊓ commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb := by
      refine ⟨?_, w.2⟩
      change (w : Vtil V₀ V hV) ∈ fixV Lb
      rw [mem_fixV]
      intro x hx
      exact (mem_fixV_autSub.mp hw) x hx (hLstab hx)
    have hbot := CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot'
      (W := Vtil V₀ V hV) hsq (Y := Lb) hoddLb
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact Subtype.ext hmem
  have hoddAut : Odd (Nat.card ↥(autSub Lb W)) := by rw [hKcard]; exact hodd7
  have hWL : commSub (⊤ : Subgroup W) (autSub Lb W) = ⊤ := by
    have h := CFSG.Quasithin.Asc81c.fixV_sup_commSub_eq_top' (W := W) hWsq hoddAut
    rwa [hfixVbot, bot_sup_eq] at h
  have hfpf : ∀ w : W, X w = w → w = 1 :=
    s168e3_cyc_fpf (W := W) hWsq hLz (by rw [hXorder]; decide) hWL
  have hcK : Conc4_136 D V₀ V hV L := hc
  obtain ⟨t, htM, ht2, ht1, htr, hW'⟩ := hc
  have hW'B : Conc4_136W (Mbar D.M V₀ V hV) t Lb := by simpa [Lb] using hW'
  have h133 := s16h_conc4_133_of_prime_card hp hLp.2 hW'
  obtain ⟨q, hq, -, hLt, hind, -⟩ := h133
  have hLtB : ⁅Lb, Subgroup.zpowers t⁆ ≠ ⊥ := by simpa [Lb] using hLt
  have hnorm_or := s16h_bl_mem_normalizer_or_rk (A := Mbar D.M V₀ V hV) (L := Lb)
    hW'B hind htM htr
  have ht0norm : t ∈ normalizer (Lb : Set (MulAut (Vtil V₀ V hV))) := by
    rcases hnorm_or with h | h
    · exact h
    · have h6 : rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb) = 6 := by
        have hWeq : commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb = W := rfl
        rw [hWeq]
        exact hm
      omega
  have htB : t ∈ B := ⟨htM, ht0norm⟩
  have htmap : W.map t.toMonoidHom = W := by
    have hLmap : Lb.map (MulAut.conj t).toMonoidHom = Lb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ht0norm
    have h := CFSG.Quasithin.Asc81c.commSub_map_conj Lb t
    rw [hLmap] at h
    exact h.symm
  have ht2' : t * t = 1 := by simpa [pow_two] using ht2
  have htinv : ∀ x : Vtil V₀ V hV, t (t x) = x := by
    intro x
    have h := congrArg (fun f : MulAut (Vtil V₀ V hV) => f x) ht2'
    simpa [MulAut.mul_apply] using h
  have hts : t ∈ stabSub W := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have hmem : t (t u) ∈ W.map t.toMonoidHom := Subgroup.mem_map_of_mem t.toMonoidHom hu
      rw [htmap] at hmem
      rwa [htinv u] at hmem
    · intro hu
      have hmem : t u ∈ W.map t.toMonoidHom := Subgroup.mem_map_of_mem t.toMonoidHom hu
      rwa [htmap] at hmem
  set T : MulAut W := resHom W ⟨t, hts⟩ with hTdef
  have hT : T ∈ autSub B W := mem_autSub.mpr ⟨⟨t, hts⟩, htB, rfl⟩
  have hinvV : t * l * t⁻¹ = l⁻¹ := by
    have hcardL : Nat.card ↥Lb = 7 := hLbcard
    rcases CFSG.Walter.conj_eq_or_conj_eq_inv_of_card_eq_prime (p := 7)
      (by norm_num) hcardL ht2' ht0norm with hcom | hinv
    · exfalso
      apply hLtB
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have htx : Commute t x := by
        show t * x = x * t
        calc t * x = (t * x * t⁻¹) * t := by group
          _ = x * t := by rw [hcom x hx]
      exact (htx.zpow_left k).eq
    · exact hinv l hlmem
  have hTX : T * X * T⁻¹ = X⁻¹ := by
    have hconj : (⟨t, hts⟩ : stabSub W) * ⟨l, hlstab⟩ * ⟨t, hts⟩⁻¹ =
        ⟨l, hlstab⟩⁻¹ := by
      ext x
      exact congrArg (fun f : MulAut (Vtil V₀ V hV) => f x) hinvV
    have h := congrArg (resHom W) hconj
    simp only [map_mul, map_inv] at h
    simpa [hTdef, hXdef, mul_assoc] using h
  have hcardW : Nat.card W = 2 ^ 6 := by
    rw [CFSG.Quasithin.card_eq_two_pow_rk hWsq, hm]
  have hsig : D.sig = {7} :=
    s16h_e3_CycTwoP7M6A_sig_eq D S hr3 hσ hV h hcK hp hLp hχ hs2 hres hp7 hm hbad
  have h7mem : 7 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 7
  have h2p := s16h_e3_CycTwoP7M6A_rank_two_of_bad D S hr3 hσ hV h hcK hp hLp hχ hs2 hres hp7
    hm hbad 7 h7mem
  have h7 : 2 ≤ CFSG.Open.pRank 7 (autSub B W) := by
    have h2p' : 2 ≤ CFSG.pRank 7 (autSub B W) := by
      simpa only [← hBdef, ← hWdef] using h2p
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h2p'
    exact h2p'
  have hLA : autSub Lb W ≤ autSub B W := autSub_mono hLbB W
  obtain ⟨hA1dvd, hT1ab, hT1norm, hT1cent⟩ :=
    s16h_e3_CycTwoP7M6AA2AAA1_cyc7_structure hWsq hcardW hLz hXorder hLn hfpf hT hTX hLA h7
  obtain ⟨x, hxM, hxn⟩ := s16c34_exists_not_mem_nBar D h.hyp151 (by omega)
  have hxs : x ∈ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀ hxM
  set c : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨x, hxs⟩ with hcdef
  have hcMb : c ∈ Mbar D.M V₀ V hV := actTil_mem_barSub V₀ V hV hxM hxs
  set W₂ : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV (conjSubgroup L x) with hW₂def
  have hW₂eq : W₂ = W.map c⁻¹.toMonoidHom := by
    rw [hW₂def, hWdef]
    simpa [hcdef] using s15_Infra_wTil_conjSubgroup V₀ V L hV hxs
  have hLbne : barSub V₀ V hV L ≠ ⊥ := by
    have h0 : Lb ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hLbcard
      omega
    exact h0
  have hWsup : W ⊔ W₂ = ⊤ := by
    rw [hWdef, hW₂def]
    refine le_antisymm le_top ?_
    rw [← hW'B.1]
    refine iSup₂_le fun X hX => ?_
    obtain ⟨g, hg, rfl⟩ := hX
    rcases c23_perm_wTil h.hyp151 hV hs2 hLbne hxM hxn g hg with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (le_of_eq h1).trans le_sup_left
    · exact (le_of_eq h1).trans le_sup_right
  letI : MulAction ↥(Mbar D.M V₀ V hV) (Subgroup (MulAut (Vtil V₀ V hV))) :=
    MulAction.compHom (Subgroup (MulAut (Vtil V₀ V hV)))
      ((MulAut.conj : MulAut (Vtil V₀ V hV) →* MulAut (MulAut (Vtil V₀ V hV))).comp
        (Mbar D.M V₀ V hV).subtype)
  have hsmulM : ∀ m : ↥(Mbar D.M V₀ V hV), m • Lb =
      Lb.map (MulAut.conj (m : MulAut (Vtil V₀ V hV))).toMonoidHom := by
    intro m
    show (MulAut.conj (m : MulAut (Vtil V₀ V hV))) • Lb =
      Lb.map (MulAut.conj (m : MulAut (Vtil V₀ V hV))).toMonoidHom
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hstabM : MulAction.stabilizer ↥(Mbar D.M V₀ V hV) Lb =
      B.subgroupOf (Mbar D.M V₀ V hV) := by
    ext m
    rw [MulAction.mem_stabilizer_iff, hsmulM, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    simp [hBdef]
  have horbM : MulAction.orbit ↥(Mbar D.M V₀ V hV) Lb =
      {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV, X = Lb.map (MulAut.conj φ).toMonoidHom} := by
    ext X
    constructor
    · intro hX
      rw [MulAction.mem_orbit_iff] at hX
      obtain ⟨m, hm⟩ := hX
      exact ⟨(m : MulAut (Vtil V₀ V hV)), m.2, hm.symm.trans (hsmulM m)⟩
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨⟨φ, hφ⟩, hsmulM ⟨φ, hφ⟩⟩
  have hidx : (MulAction.stabilizer ↥(Mbar D.M V₀ V hV) Lb).index = 2 := by
    have h := MulAction.index_stabilizer (G := ↥(Mbar D.M V₀ V hV)) (x := Lb)
    rw [horbM] at h
    rw [h]
    exact hs2
  have hBnorm : (B.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
    rw [← hstabM]
    exact Subgroup.normal_of_index_eq_two hidx
  have hMbB : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (B : Set (MulAut (Vtil V₀ V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : B ≤ Mbar D.M V₀ V hV)).1 hBnorm
  obtain ⟨P, hPM, hPnorm, hPrank, hPrel⟩ :=
    s16h_e3_CycTwoP7M6AA2AAA2AA_exists_normal_sylow_core D S hr3 hσ hV h hcK hp hLp hχ hs2 hres
      hp7 hm hbad
  exact ⟨P, hPM, hPnorm, hPrank, hPrel,
    s16h_e3_CycTwoP7M6AA2AAA2A_le_of_normal_of_relIndex hPnorm hPrank hPrel⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

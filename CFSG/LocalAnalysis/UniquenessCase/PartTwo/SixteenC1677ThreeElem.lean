module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSevenOpen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeElemA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1E9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Sym

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Generic

variable {W : Type} [CommGroup W]

private theorem s168e3_e3_card_GL_two : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field, ZMod.card]
  norm_num [Fin.prod_univ_succ]

private theorem s168e3_e3_coprime_six {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    Nat.Coprime q 6 := by
  rw [hq.coprime_iff_not_dvd]
  intro hd
  have hd' : q ∣ 2 * 3 := by simpa using hd
  rcases hq.dvd_mul.mp hd' with h | h
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
  · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h)

private theorem s168e3_e3_stab_of_map_eq {T : Type} [CommGroup T] {U : Subgroup T}
    {φ : MulAut T} (h : U.map φ.toMonoidHom = U) : φ ∈ stabSub U := by
  intro u
  constructor
  · intro hu
    have hu' : φ u ∈ U.map φ.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := φ.injective hwu
    rw [← this]; exact hw
  · intro hu
    have hu' : φ u ∈ U.map φ.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [h] at hu'; exact hu'

private theorem s168e3_e3_pRank_lt_two_of_blocks [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} {Z : Subgroup W} (hZ : rk ↥Z = 2)
    (hsup : sSup (conjSubs A Z) = ⊤) (hcard3 : (conjSubs A Z).ncard = 3) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) : CFSG.Open.pRank q A < 2 := by
  by_contra hlt
  have hge : 2 ≤ CFSG.Open.pRank q A := not_lt.1 hlt
  have hfin : (conjSubs A Z).Finite := Set.finite_of_ncard_pos (by rw [hcard3]; omega)
  letI : Fintype ↥(conjSubs A Z) := hfin.fintype
  let Y : ↥(conjSubs A Z) → Subgroup W := Subtype.val
  have hYinj : Function.Injective Y := Subtype.val_injective
  have hYsSup : ⨆ i, Y i = ⊤ := by
    rw [← sSup_eq_iSup']
    exact hsup
  have hYrk : ∀ i, rk ↥(Y i) = 2 := by
    intro i
    show rk ↥(i.1) = 2
    obtain ⟨g, hg, hgi⟩ := i.2
    rw [hgi, s16n9b_rk_map, hZ]
  have hYperm : ∀ g ∈ A, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j := by
    intro g hg i
    obtain ⟨h, hh, hhi⟩ := i.2
    refine ⟨⟨Z.map (g * h).toMonoidHom, g * h, A.mul_mem hg hh, rfl⟩, ?_⟩
    show (i.1).map g.toMonoidHom = Z.map (g * h).toMonoidHom
    rw [hhi, Subgroup.map_map]
    rfl
  have hcardι : Nat.card ↥(conjSubs A Z) = 3 := by
    rw [Nat.card_eq_fintype_card]
    exact (Set.fintypeCard_eq_ncard (conjSubs A Z)).trans hcard3
  obtain ⟨E, hEA, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt A
  have hcop : Nat.Coprime q 6 := s168e3_e3_coprime_six hq hq2 hq3
  let pick : ↥E → ↥(conjSubs A Z) → ↥(conjSubs A Z) :=
    fun g i => Classical.choose (hYperm g.1 (hEA g.2) i)
  have hpick : ∀ (g : ↥E) (i : ↥(conjSubs A Z)),
      (Y i).map (g.1).toMonoidHom = Y (pick g i) :=
    fun g i => Classical.choose_spec (hYperm g.1 (hEA g.2) i)
  have hpick_inj : ∀ g : ↥E, Function.Injective (pick g) := by
    intro g i j hij
    have hmap : (Y i).map (g.1).toMonoidHom = (Y j).map (g.1).toMonoidHom := by
      rw [hpick g i, hpick g j, hij]
    exact hYinj (Subgroup.map_injective g.1.injective hmap)
  let σ : ↥E → Equiv.Perm ↥(conjSubs A Z) := fun g =>
    Equiv.ofBijective (pick g)
      ((Fintype.bijective_iff_injective_and_card (pick g)).mpr ⟨hpick_inj g, rfl⟩)
  have hσ_apply : ∀ (g : ↥E) (i : ↥(conjSubs A Z)), σ g i = pick g i := fun _ _ => rfl
  have hσ_mul : ∀ g h : ↥E, σ (g * h) = σ g * σ h := by
    intro g h
    apply Equiv.ext
    intro i
    show pick (g * h) i = pick g (pick h i)
    apply hYinj
    have h1 := hpick (g * h) i
    have h2 := hpick h i
    have h3 := hpick g (pick h i)
    have hcomp : ((g * h).1).toMonoidHom = (g.1).toMonoidHom.comp (h.1).toMonoidHom := by
      ext x; rfl
    calc Y (pick (g * h) i) = (Y i).map ((g * h).1).toMonoidHom := h1.symm
      _ = (Y i).map ((g.1).toMonoidHom.comp (h.1).toMonoidHom) := by rw [hcomp]
      _ = ((Y i).map (h.1).toMonoidHom).map (g.1).toMonoidHom :=
            (Subgroup.map_map (K := Y i) (g.1).toMonoidHom (h.1).toMonoidHom).symm
      _ = (Y (pick h i)).map (g.1).toMonoidHom := by rw [h2]
      _ = Y (pick g (pick h i)) := h3
  let ρ : ↥E →* Equiv.Perm ↥(conjSubs A Z) := MonoidHom.mk' σ hσ_mul
  have hρ_apply : ∀ (g : ↥E) (i : ↥(conjSubs A Z)), ρ g i = pick g i := fun g i => hσ_apply g i
  have hYρ : ∀ (g : ↥E) (i : ↥(conjSubs A Z)),
      (Y i).map (g.1).toMonoidHom = Y (ρ g i) := by
    intro g i
    rw [hρ_apply, hpick]
  have hker : ∀ g : ↥E, ρ g = 1 → g = 1 := by
    intro g hg
    have hstab : ∀ i, (g.1 : MulAut W) ∈ stabSub (Y i) := by
      intro i
      apply s168e3_e3_stab_of_map_eq
      have h := hYρ g i
      rw [hg] at h
      simpa using h
    have hfix : ∀ i, ∀ u ∈ Y i, (g.1 : MulAut W) u = u := by
      intro i u hu
      have hYsq : ∀ t : ↥(Y i), t ^ 2 = 1 := by
        intro t
        apply Subtype.ext
        simpa using hW (t : W)
      have hYcard : Nat.card ↥(Y i) = 2 ^ 2 := by
        rw [card_eq_two_pow hW (Y i), hYrk i]
      have hcardMulAut : Nat.card (MulAut ↥(Y i)) ∣ Nat.card (GL (Fin 2) (ZMod 2)) :=
        CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
          (fun a b => mul_comm a b) hYsq hYcard
      rw [s168e3_e3_card_GL_two] at hcardMulAut
      have hresq : (resHom (Y i) ⟨g.1, hstab i⟩) ^ q = 1 := by
        rw [← map_pow]
        have hxq : (⟨g.1, hstab i⟩ : stabSub (Y i)) ^ q = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow]
          exact hE.2 g.1 g.2
        rw [hxq, map_one]
      have horderq : orderOf (resHom (Y i) ⟨g.1, hstab i⟩) ∣ q :=
        orderOf_dvd_of_pow_eq_one hresq
      have horder6 : orderOf (resHom (Y i) ⟨g.1, hstab i⟩) ∣ 6 :=
        (_root_.orderOf_dvd_natCard (resHom (Y i) ⟨g.1, hstab i⟩)).trans hcardMulAut
      have horder1 : orderOf (resHom (Y i) ⟨g.1, hstab i⟩) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop horderq horder6
      have hres1 : resHom (Y i) ⟨g.1, hstab i⟩ = 1 := orderOf_eq_one_iff.mp horder1
      have h := congrArg (fun φ : MulAut ↥(Y i) => ((φ ⟨u, hu⟩ : ↥(Y i)) : W)) hres1
      simp only [MulAut.one_apply] at h
      rwa [resHom_apply] at h
    apply Subtype.ext
    ext w
    have htop : (⊤ : Subgroup W) ≤ (g.1 : W →* W).eqLocus (MonoidHom.id W) := by
      rw [← hYsSup]
      exact iSup_le (fun i u hu => hfix i u hu)
    have hw := htop (Subgroup.mem_top w)
    change (g.1 : W →* W) w = (MonoidHom.id W) w at hw
    simpa using hw
  have hρ_inj : Function.Injective ρ := by
    intro g h hgh
    have hk : ρ (g⁻¹ * h) = 1 := by
      rw [map_mul, map_inv, hgh, inv_mul_cancel]
    exact inv_mul_eq_one.mp (hker (g⁻¹ * h) hk)
  have hdvdE : q ^ 2 ∣ Nat.card ↥E := by
    rw [hEcard]
    exact pow_dvd_pow q hge
  have hcard_range : Nat.card ↥(ρ.range) = Nat.card ↥E := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hρ_inj, Subgroup.card_top]
  have hdvd_perm : Nat.card ↥E ∣ Nat.card (Equiv.Perm ↥(conjSubs A Z)) :=
    hcard_range ▸ Subgroup.card_subgroup_dvd_card ρ.range
  have hperm : Nat.card (Equiv.Perm ↥(conjSubs A Z)) = 6 := by
    rw [Nat.card_perm, hcardι]
    norm_num
  have hdvd6 : q ^ 2 ∣ 6 := by
    rw [hperm] at hdvd_perm
    exact hdvdE.trans hdvd_perm
  have hq2le : 2 ≤ q := hq.two_le
  have hqle2 : q ≤ 2 := by
    have h6 : q ^ 2 ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    by_contra h
    have h3 : 3 ≤ q := by omega
    nlinarith
  exact hq2 (le_antisymm hqle2 hq2le)

theorem s168e3_pRank_lt_two_of_e9_six [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {A L : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) (hL : IsElemAbelianOfRank 3 2 ↥L)
    (hWL : commSub ⊤ L = ⊤) (htr : IrrSpanTrans A L) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) : CFSG.Open.pRank q A < 2 := by
  obtain ⟨Z, hZ, -, hsup, hcard3⟩ := s168e3_e9_blocks hW hcard hLA hLn hL hWL htr
  exact s168e3_e3_pRank_lt_two_of_blocks hW hZ hsup hcard3 hq hq2 hq3


private theorem s168e3_normal_subgroupOf_of_conj {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} (h : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) :
    (L.subgroupOf A).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg := h g g.2
  have hmem : (MulAut.conj (g : MulAut W)).toMonoidHom (n : MulAut W) ∈
      L.map (MulAut.conj (g : MulAut W)).toMonoidHom := Subgroup.mem_map_of_mem _ hn
  rw [hg] at hmem
  simpa [MulAut.conj_apply] using hmem

end Generic

theorem s168e3_mem_sig_of_elem {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) {p r : ℕ} (hp : p = 3 ∨ p = 7)
    (hr : 2 ≤ r) (hE : IsElemAbelianOfRank p r ↥(lBar V₀ V hV L))
    (hsym : SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) r (dParam p)) :
    p ∈ D.sig := by
  by_cases hsm : p = 3 ∧ r ≤ 5
  · obtain ⟨rfl, hr5⟩ := hsm
    rw [s16c1610_dParam_three] at hsym
    exact s168e3_mem_sig_three_of_symSum c hr5 hsym
  · by_cases h6 : 6 ≤ r
    · exact s16e_mem_sig_of_elem_core D c.std.hSg c.std.h127 c.std.h1110 hV c.setting c.conc hs
        hp h6 hE
    · have hp7 : p = 7 := by
        rcases hp with rfl | rfl
        · exact absurd ⟨rfl, by omega⟩ hsm
        · rfl
      subst hp7
      rw [s16c1610_dParam_seven] at hsym
      exact s168e3_mem_sig_seven_of_elem c hs hr (by omega) hE hsym

theorem s168e3_s1_case4_of_elem {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) {p r : ℕ} (hp : p = 3 ∨ p = 7)
    (hr : 2 ≤ r) (hE : IsElemAbelianOfRank p r ↥(lBar V₀ V hV L))
    (hrk : rk ↥(wTil V₀ V hV L) = (r + 1) * dParam p) : Case168_4 D V₀ V hV L := by
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hrkV : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = (r + 1) * dParam p := by
    rw [← hwT]
    exact hrk
  have hLA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV c.setting.hyp151.le
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = lBar V₀ V hV L :=
    fun g hg => lBar_conj_eq_of_s15_eq_one hs hg
  obtain ⟨t, htA, ht2, ht1, htrk, hW⟩ := id c.conc
  have hsym : SymSumOfConj (Mbar D.M V₀ V hV) ⊤ r (dParam p) := by
    refine s16e_symSum_of_conc4136W hp hr hE hwT hrkV hW ?_
    rintro rfl rfl hinv
    have hT := s15_Infra_vtil_sq_eq_one V₀ V hV
    rw [s16c1610_dParam_three] at hrkV
    have hcard : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
      rw [s16e_card_eq_two_pow_rk_top hT, hrkV]
    have hLcard : Nat.card ↥(lBar V₀ V hV L) = 9 := by
      have := A38.card_eq_of_isElemAbelianOfRank Nat.prime_three hE
      simpa using this
    have hX1 : lBar V₀ V hV L ≠ ⊥ := by
      intro hb
      have := Subgroup.card_eq_one.mpr hb
      omega
    have htr : IrrSpanTrans (Mbar D.M V₀ V hV) (lBar V₀ V hV L) :=
      twelve_seventeen D c.std.hx c.std.h61 c.std.h127 c.std.h1214 c.setting.hyp16.hyp125
        (lBar V₀ V hV L) hX1 hLA (s168e3_normal_subgroupOf_of_conj hLn)
        (Or.inl (by rw [hLcard]; exact ⟨4, by norm_num⟩))
    have hsig : D.sig = {3} :=
      c.sig_eq_singleton_of_pRank_lt_two 3 (fun q hq hq2 hq3 =>
        s168e3_pRank_lt_two_of_e9_six hT hcard hLA hLn hE hwT htr hq hq2 hq3)
    have h3 : 3 ∈ D.sig := by
      rw [hsig]
      exact Set.mem_singleton 3
    have hO3 : ∀ N : Subgroup ↥(Mbar D.M V₀ V hV), N.Normal → N.index ≠ 3 := by
      intro N hN
      haveI := hN
      exact s16e_mbar_index_ne_three D c.std.h638 h3 c.setting.hyp16 hV N
    exact s16e_symSum_two_of_E9 hT hcard hLA hLn hE hwT htr hO3
  have hsig := s168e3_mem_sig_of_elem c hs hp hr hE hsym
  exact ⟨p, r, hp, by omega, hE, hsym, hsig⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

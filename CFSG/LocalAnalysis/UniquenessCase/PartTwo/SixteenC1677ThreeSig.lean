module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeP1p2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem S168e3Ctx.sig_eq_singleton_of_pRank_lt_two {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (p : ℕ)
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → CFSG.Open.pRank q (Mbar D.M V₀ V hV) < 2) :
    D.sig = {p} := by
  obtain ⟨p₀, hp₀⟩ := c.std.hx.sig_nonempty
  have key : ∀ q ∈ D.sig, q = p := by
    intro q hq
    by_contra hne
    have h1 := c.two_le_pRank_mbar hq
    have h2 := h q (D.sig_prime q hq).1 (D.sig_prime q hq).2 hne
    omega
  ext q
  constructor
  · intro hq
    exact key q hq
  · intro hq
    rw [Set.mem_singleton_iff.1 hq, ← key p₀ hp₀]
    exact hp₀

section Generic

variable {W : Type} [CommGroup W]

private theorem s168e3_sig_card_GL_two : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field, ZMod.card]
  norm_num [Fin.prod_univ_succ]

private theorem s168e3_sig_coprime_six {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    Nat.Coprime q 6 := by
  rw [hq.coprime_iff_not_dvd]
  intro hd
  have hd' : q ∣ 2 * 3 := by simpa using hd
  rcases hq.dvd_mul.mp hd' with h | h
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
  · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h)

private theorem s168e3_sig_not_sq_dvd_factorial_six {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) : ¬ q ^ 2 ∣ Nat.factorial 6 := by
  intro h
  have hdvd : q ∣ Nat.factorial 6 := (dvd_pow_self q (by norm_num)).trans h
  have hqle : q ≤ 6 := (hq.dvd_factorial).mp hdvd
  have hq2le : 2 ≤ q := hq.two_le
  interval_cases q <;> first
    | exact hq2 rfl
    | exact hq3 rfl
    | (norm_num at h; done)
    | (norm_num at hq; done)

private theorem s168e3_sig_stab_of_map_eq {T : Type} [CommGroup T] {U : Subgroup T}
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

theorem s168e3_pRank_lt_two_of_symSum_two [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} {r : ℕ} (hr : r ≤ 5) (h : SymSumOfConj A ⊤ r 2) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) : CFSG.Open.pRank q A < 2 := by
  by_contra hlt
  have hge : 2 ≤ CFSG.Open.pRank q A := not_lt.1 hlt
  obtain ⟨Z, hZ, hind, hsup, hcard, _⟩ := h
  have hfin : (conjSubs A Z).Finite := Set.finite_of_ncard_pos (by rw [hcard]; omega)
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
  have hcardι : Nat.card ↥(conjSubs A Z) = r + 1 := by
    rw [Nat.card_eq_fintype_card]
    exact (Set.fintypeCard_eq_ncard (conjSubs A Z)).trans hcard
  obtain ⟨E, hEA, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt A
  have hcop : Nat.Coprime q 6 := s168e3_sig_coprime_six hq hq2 hq3
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
      apply s168e3_sig_stab_of_map_eq
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
      rw [s168e3_sig_card_GL_two] at hcardMulAut
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
  have hperm_dvd : Nat.card (Equiv.Perm ↥(conjSubs A Z)) ∣ Nat.factorial 6 := by
    rw [Nat.card_perm, hcardι]
    exact Nat.factorial_dvd_factorial (by omega)
  exact s168e3_sig_not_sq_dvd_factorial_six hq hq2 hq3
    (hdvdE.trans (hdvd_perm.trans hperm_dvd))

end Generic

theorem s168e3_mem_sig_three_of_symSum {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) {r : ℕ} (hr : r ≤ 5)
    (hsym : SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) r 2) : 3 ∈ D.sig := by
  have h := c.sig_eq_singleton_of_pRank_lt_two 3 fun q hq hq2 hq3 =>
    s168e3_pRank_lt_two_of_symSum_two (s15_Infra_vtil_sq_eq_one V₀ V hV) hr hsym hq hq2 hq3
  rw [h]
  exact Set.mem_singleton 3

theorem s168e3_sig_eq_three_of_p1p2 {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hP : IsPOnePlusTwo 3 ↥(lBar V₀ V hV L)) (hrk : rk ↥(wTil V₀ V hV L) = 6) :
    D.sig = {3} := by
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hT := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hrkV : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := by
    rw [← hwT]
    exact hrk
  have hcard : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
    rw [s16e_card_eq_two_pow_rk_top hT, hrkV]
  exact c.sig_eq_singleton_of_pRank_lt_two 3 fun q hq hq2 hq3 =>
    s168e3_pRank_lt_two_of_p1p2 hT hcard (barSub_mono V₀ V hV c.setting.hyp151.le)
      (fun g hg => lBar_conj_eq_of_s15_eq_one hs hg) hP hwT hq hq2 hq3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Aut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

private theorem s16n9b_case4_perm_dParam_three : dParam 3 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

theorem s16n9b_case4_perm_normal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {I : Type} [Fintype I]
    [DecidableEq I] (hI : 4 ≤ Fintype.card I) {N : Subgroup (Equiv.Perm I)} (hN : N.Normal)
    (hNp : IsPGroup p ↥N) : N = ⊥ := by
  have hpodd : Odd p := (hp.eq_two_or_odd').resolve_left hp2
  by_cases h4 : Fintype.card I = 4
  · let e : I ≃ Fin 4 := Fintype.equivFinOfCardEq h4
    exact CFSG.GorensteinWalter.normal_pSubgroup_eq_bot_of_mulEquiv_perm_four
      ⟨Equiv.permCongrHom e⟩ p hp hpodd N hN hNp
  · have h5 : 5 ≤ Fintype.card I := by omega
    by_contra hNne
    haveI : N.Normal := hN
    have hntN : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
    have hle : alternatingGroup I ≤ N :=
      Equiv.Perm.alternatingGroup_le_of_normal (α := I)
        (by rw [Nat.card_eq_fintype_card]; omega) hntN
    have hdvd : Nat.card ↥(alternatingGroup I) ∣ Nat.card ↥N :=
      Subgroup.card_dvd_of_le hle
    have hNodd : Odd (Nat.card ↥N) := by
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨m, hm⟩ := hNp.exists_card_eq
      rw [hm]
      exact hpodd.pow
    have hAltodd : Odd (Nat.card ↥(alternatingGroup I)) :=
      hNodd.of_dvd_nat hdvd
    haveI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hEven : Even (Nat.card ↥(alternatingGroup I)) := by
      have h2A : 2 * Nat.card ↥(alternatingGroup I) = Nat.factorial (Fintype.card I) := by
        rw [two_mul_nat_card_alternatingGroup, Nat.card_perm,
          Nat.card_eq_fintype_card]
      obtain ⟨k, hk⟩ := Nat.dvd_factorial (show 0 < 4 by norm_num)
        (show 4 ≤ Fintype.card I by omega)
      refine even_iff_two_dvd.mpr ⟨k, ?_⟩
      exact Nat.mul_left_cancel (show 0 < 2 by norm_num) (by rw [h2A, hk]; ring)
    exact (Nat.not_even_iff_odd.mpr hAltodd) hEven

theorem s16n9b_case4_perm_small {p : ℕ} (hp : p.Prime) {I : Type} [Fintype I] [DecidableEq I]
    (hI : Fintype.card I < p) {H : Subgroup (Equiv.Perm I)} (hH : IsPGroup p ↥H) : H = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnot : ¬ p ∣ Nat.card (Equiv.Perm I) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hp.dvd_factorial]
    exact not_le.mpr hI
  obtain ⟨m, hm⟩ := hH.exists_card_eq
  by_cases hm0 : m = 0
  · apply Subgroup.eq_bot_of_card_eq
    rw [hm, hm0, pow_zero]
  · exfalso
    have hpH : p ∣ Nat.card ↥H := by rw [hm]; exact dvd_pow_self p hm0
    exact hnot (hpH.trans (Subgroup.card_subgroup_dvd_card H))

theorem s16n9b_case4_perm_E (hT : ∀ t : T, t ^ 2 = 1) {I : Type} [Fintype I]
    (hI : Fintype.card I = 3) {Y : I → Subgroup T} (hind : iSupIndep Y)
    (hinj : Function.Injective Y) (hsup : ⨆ i, Y i = ⊤) (hrk : ∀ i, rk ↥(Y i) = 2)
    {E : Subgroup (MulAut T)} (hE : IsElemAbelian 3 E) (hcard : 3 ^ 3 ≤ Nat.card E)
    (hperm : ∀ g ∈ E, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) :
    ∀ g ∈ E, ∀ i, (Y i).map g.toMonoidHom = Y i := by
  classical
  haveI : IsMulCommutative ↥E := hE.1
  let pick : ↥E → I → I := fun g i => Classical.choose (hperm g.1 g.2 i)
  have hpick : ∀ (g : ↥E) (i : I), (Y i).map g.1.toMonoidHom = Y (pick g i) :=
    fun g i => Classical.choose_spec (hperm g.1 g.2 i)
  have hpick_inj : ∀ g : ↥E, Function.Injective (pick g) := by
    intro g i j hij
    have hmap : (Y i).map g.1.toMonoidHom = (Y j).map g.1.toMonoidHom := by
      rw [hpick g i, hpick g j, hij]
    exact hinj (Subgroup.map_injective g.1.injective hmap)
  let σ : ↥E → Equiv.Perm I := fun g =>
    Equiv.ofBijective (pick g)
      ((Fintype.bijective_iff_injective_and_card (pick g)).mpr ⟨hpick_inj g, rfl⟩)
  have hσ_apply : ∀ (g : ↥E) (i : I), σ g i = pick g i := fun _ _ => rfl
  have hσ_mul : ∀ g h : ↥E, σ (g * h) = σ g * σ h := by
    intro g h
    ext i
    show pick (g * h) i = pick g (pick h i)
    apply hinj
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
  let ρ : ↥E →* Equiv.Perm I := MonoidHom.mk' σ hσ_mul
  have hρ_apply : ∀ (g : ↥E) (i : I), ρ g i = pick g i := fun g i => hσ_apply g i
  have hYρ : ∀ (g : ↥E) (i : I), (Y i).map g.1.toMonoidHom = Y (ρ g i) := by
    intro g i
    rw [hρ_apply, hpick]
  by_contra hcon
  rw [not_forall] at hcon
  obtain ⟨g0, hg0⟩ := hcon
  obtain ⟨hg0E, hg0act⟩ := not_imp.mp hg0
  have hg0ne : ρ ⟨g0, hg0E⟩ ≠ 1 := by
    intro hρ
    apply hg0act
    intro i
    have h := hYρ ⟨g0, hg0E⟩ i
    rw [hρ] at h
    simpa using h
  have h3g : (ρ ⟨g0, hg0E⟩) ^ 3 = 1 := by
    have hg03 : (⟨g0, hg0E⟩ : ↥E) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      simpa using hE.2 g0 hg0E
    rw [← map_pow, hg03, map_one]
  have horder : orderOf (ρ ⟨g0, hg0E⟩) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime h3g hg0ne
  have hcycle : (ρ ⟨g0, hg0E⟩).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order'' (α := I)
      (by rw [hI]; norm_num) (by rw [hI]; exact horder)
  have hsupport : (ρ ⟨g0, hg0E⟩).support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hcycle.orderOf, horder, hI]
  have hmoved : ∀ x : I, (ρ ⟨g0, hg0E⟩) x ≠ x := by
    intro x hx
    have hxmem : x ∈ (ρ ⟨g0, hg0E⟩).support := by
      rw [hsupport]; exact Finset.mem_univ x
    exact (Equiv.Perm.mem_support.mp hxmem) hx
  have horbit : ∀ x j : I, ∃ n : ℕ, ((ρ ⟨g0, hg0E⟩) ^ n) x = j :=
    fun x j => hcycle.exists_pow_eq (hmoved x) (hmoved j)
  let e : I ≃ Fin 3 := Fintype.equivFinOfCardEq hI
  let i₀ : I := e.symm 0
  have hYρ_pow : ∀ (n : ℕ) (i : I),
      (Y i).map ((⟨g0, hg0E⟩ ^ n : ↥E).1).toMonoidHom =
        Y (((ρ ⟨g0, hg0E⟩) ^ n) i) := by
    intro n i
    have h := hYρ (⟨g0, hg0E⟩ ^ n) i
    rwa [map_pow] at h
  have hYorbit : ∀ j : I, ∃ n : ℕ,
      (Y i₀).map ((⟨g0, hg0E⟩ ^ n : ↥E).1).toMonoidHom = Y j := by
    intro j
    obtain ⟨n, hn⟩ := horbit i₀ j
    exact ⟨n, by rw [hYρ_pow n i₀, hn]⟩
  let B : Subgroup ↥E := ρ.ker
  let F : Subgroup (MulAut T) := B.map E.subtype
  have hFle : F ≤ E := by
    intro f hf
    obtain ⟨b, _, rfl⟩ := Subgroup.mem_map.mp hf
    exact b.2
  have hF3 : IsElemAbelian 3 F := CFSG.Open.IsElemAbelian.mono hE hFle
  have hFY3 : ∀ f ∈ F, (Y i₀).map f.toMonoidHom = Y i₀ := by
    intro f hf
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hf
    have hbker : ρ b = 1 := MonoidHom.mem_ker.mp hb
    have h := hYρ b i₀
    rw [hbker] at h
    simpa using h
  have hFcent : F ⊓ centSub (Y i₀) = ⊥ := by
    apply le_bot_iff.mp
    intro b hb
    rw [Subgroup.mem_inf] at hb
    obtain ⟨hbF, hbcent⟩ := hb
    obtain ⟨β, _, hβeq⟩ := Subgroup.mem_map.mp hbF
    rw [← hβeq]
    apply Subgroup.mem_bot.mpr
    have hβE : (β : MulAut T) ∈ E := β.2
    have hβcent : ∀ u ∈ Y i₀, (β : MulAut T) u = u := by
      intro u hu
      have h := mem_centSub.mp hbcent u hu
      rwa [← hβeq] at h
    have hcomm : ∀ n : ℕ,
        (β : MulAut T) * ((⟨g0, hg0E⟩ : ↥E) ^ n).1 =
          ((⟨g0, hg0E⟩ : ↥E) ^ n).1 * (β : MulAut T) := by
      intro n
      have h := mul_comm' (⟨(β : MulAut T), hβE⟩ : ↥E) ((⟨g0, hg0E⟩ : ↥E) ^ n)
      simpa using congrArg Subtype.val h
    have hβone : (β : MulAut T) = 1 := by
      let K : Subgroup T := ((β : MulAut T) : T →* T).eqLocus (MonoidHom.id T)
      have hKle : (⨆ j, Y j) ≤ K := by
        apply iSup_le
        intro j y hy
        obtain ⟨n, hn⟩ := hYorbit j
        rw [← hn] at hy
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
        change (β : MulAut T) (((⟨g0, hg0E⟩ : ↥E) ^ n).1 z) =
          (MonoidHom.id T) (((⟨g0, hg0E⟩ : ↥E) ^ n).1 z)
        calc (β : MulAut T) (((⟨g0, hg0E⟩ : ↥E) ^ n).1 z)
            = ((β : MulAut T) * ((⟨g0, hg0E⟩ : ↥E) ^ n).1) z := rfl
          _ = (((⟨g0, hg0E⟩ : ↥E) ^ n).1 * (β : MulAut T)) z := by rw [hcomm n]
          _ = ((⟨g0, hg0E⟩ : ↥E) ^ n).1 ((β : MulAut T) z) := rfl
          _ = ((⟨g0, hg0E⟩ : ↥E) ^ n).1 z := by rw [hβcent z hz]
      have htop : (⊤ : Subgroup T) ≤ K := hsup ▸ hKle
      ext t
      have ht : t ∈ K := htop (Subgroup.mem_top t)
      change (β : MulAut T) t = (MonoidHom.id T) t at ht
      simpa using ht
    simpa using hβone
  have hEcard : Nat.card ↥E = Nat.card ρ.range * Nat.card ρ.ker := by
    have h1 := Subgroup.card_mul_index ρ.ker
    rw [Subgroup.index_ker] at h1
    rw [mul_comm] at h1
    exact h1.symm
  have hρrange3 : Nat.card ρ.range ≤ 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
    have hdvdE : Nat.card ρ.range ∣ 3 ^ n := by
      rw [← hn]
      exact ⟨Nat.card ρ.ker, hEcard⟩
    obtain ⟨m, hm⟩ := (IsPGroup.of_card_dvd_pow hdvdE).exists_card_eq
    have hdvd6 : Nat.card ρ.range ∣ 6 := by
      have h := Subgroup.card_subgroup_dvd_card ρ.range
      rw [Nat.card_perm] at h
      have hI3 : Nat.card I = 3 := by rw [Nat.card_eq_fintype_card, hI]
      rw [hI3] at h
      norm_num at h
      simpa [Nat.card_eq_fintype_card] using h
    rw [hm] at hdvd6
    have hm1 : m ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ m := by omega
      have h3 : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 h2).trans hdvd6
      norm_num at h3
    rw [hm]
    interval_cases m <;> norm_num
  have hBcard : 9 ≤ Nat.card ρ.ker := by
    have h3 : 27 ≤ Nat.card ρ.range * Nat.card ρ.ker := by
      rw [← hEcard]
      norm_num at hcard ⊢
      exact hcard
    have h4 : Nat.card ρ.range * Nat.card ρ.ker ≤ 3 * Nat.card ρ.ker :=
      Nat.mul_le_mul_right _ hρrange3
    omega
  have hFcard : Nat.card F = Nat.card ρ.ker := by
    exact (Nat.card_congr (Subgroup.equivMapOfInjective ρ.ker E.subtype
      (by intro a b hab; exact Subtype.ext hab))).symm
  have hYrk : rk ↥(Y i₀) = dParam 3 := by
    rw [s16n9b_case4_perm_dParam_three, hrk i₀]
  have hindex := s16n9b_case4_aut_index_le (p := 3) (Or.inl rfl) hT hYrk hF3 hFY3
  rw [hFcent] at hindex
  rw [Subgroup.card_bot, mul_one] at hindex
  have h9 : 9 ≤ Nat.card F := by rw [hFcard]; exact hBcard
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

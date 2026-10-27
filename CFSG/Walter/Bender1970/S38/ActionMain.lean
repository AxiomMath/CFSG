module

public import CFSG.Walter.Bender1970.S38.AbelianNormal
public import CFSG.Walter.Bender1970.S38.Omega
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Walter

variable {A Y : Type*} [CommGroup A] [Group Y]

theorem omegaCenter_ne_bot [Finite Y] {p : ℕ} (hp : p.Prime) {D : Subgroup Y}
    (hDp : IsPGroup p D) (hD : D ≠ ⊥) : omegaCenter p D ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hD
  have hZ := hDp.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center D)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hDp) (z : D)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hz1 (Subtype.ext hk)
  set x : Y := ((z : D) : Y) ^ p ^ (k - 1) with hx
  have hxord : orderOf x = p := by
    have h1 : orderOf ((z : D) : Y) = p ^ k := by rw [Subgroup.orderOf_coe]; exact hk
    rw [hx, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (h1 ▸ pow_dvd_pow p (Nat.sub_le k 1)),
      h1, Nat.pow_div (Nat.sub_le k 1) hp.pos, Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hk0),
      pow_one]
  intro hbot
  have hxP : x ∈ omegaCenter p D := by
    refine ⟨D.pow_mem (z : D).2 _, by rw [← hxord, pow_orderOf_eq_one], fun d hd => ?_⟩
    have hzd : ((z : D) : Y) * d = d * (z : D) := by
      have := (Subgroup.mem_center_iff.mp z.2) ⟨d, hd⟩
      exact (congrArg Subtype.val this).symm
    exact (Commute.pow_left hzd _).eq
  rw [hbot, Subgroup.mem_bot] at hxP
  rw [hxP, orderOf_one] at hxord
  exact hp.one_lt.ne hxord

theorem mem_pCore_of_mem_normal_nilpotent [Finite Y] {p : ℕ} (hp : p.Prime) {N : Subgroup Y}
    (hN : N.Normal) (hNnil : Group.IsNilpotent N) {x : Y} (hxN : x ∈ N) {k : ℕ}
    (hx : x ^ p ^ k = 1) : x ∈ CFSG.pCore p Y := by
  have : Fact p.Prime := ⟨hp⟩
  have hxp : IsPGroup p (Subgroup.zpowers (⟨x, hxN⟩ : N)) := by
    have hdvd : Nat.card (Subgroup.zpowers (⟨x, hxN⟩ : N)) ∣ p ^ k := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    exact IsPGroup.of_card hj
  obtain ⟨S, hS⟩ := hxp.exists_le_sylow
  have h1 : (⟨x, hxN⟩ : N) ∈ (S : Subgroup N) := hS (Subgroup.mem_zpowers _)
  exact Sylow.map_le_pCore hN hNnil p S ⟨⟨x, hxN⟩, h1, rfl⟩

namespace Bender38Action

variable {ρ : Y →* MulAut A} {W Q : Subgroup A} {X R : Subgroup Y}
  (hD : Bender38Action ρ W Q X R)
include hD

theorem le_fittingSubgroupOf [Finite Y] : R ≤ CFSG.fittingSubgroupOf X := by
  intro r hr
  have hRn : (R.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hD.conj_mem g g.2 n hn⟩
  have hRnil : Group.IsNilpotent (R.subgroupOf X) := by
    have : IsCyclic R := hD.isCyclic
    have : IsMulCommutative R := IsCyclic.isMulCommutative
    have : Group.IsNilpotent R := CommGroup.isNilpotent
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hD.le_X).symm
  have h1 : R.subgroupOf X ≤ CFSG.fittingSubgroup X := by
    rw [CFSG.fitting_eq_sup_pCore]
    exact CFSG.normal_nilpotent_le_sup_pCore hRn hRnil
  exact ⟨⟨r, hD.le_X hr⟩, h1 hr, rfl⟩

theorem pCore_inf_ne_bot [Finite A] [Finite Y] (hne : ¬ (Nat.card W = 2 ∧ Nat.card Q = 4))
    {p : ℕ} (hp : p.Prime) (hU : CFSG.pCore p Y ≠ ⊥) : CFSG.pCore p Y ⊓ X ≠ ⊥ := by
  intro hUX
  apply hne
  have : Fact p.Prime := ⟨hp⟩
  set U := CFSG.pCore p Y with hUdef
  set N := U ⊓ Subgroup.centralizer (U : Set Y) with hN
  have hUn : U.Normal := CFSG.pCore_normal
  refine hD.card_eq_of_abelian_normal (N := N) ?_ ?_ ?_ ?_
  ·
    have : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU
    have hZ := (CFSG.pCore_isPGroup (p := p) (G := Y)).center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center U)
    intro hbot
    have hzN : ((z : U) : Y) ∈ N := by
      refine ⟨(z : U).2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have := (Subgroup.mem_center_iff.mp z.2) ⟨u, hu⟩
      exact congrArg Subtype.val this
    rw [hbot, Subgroup.mem_bot] at hzN
    exact hz1 (Subtype.ext (Subtype.ext hzN))
  ·
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1
  ·
    have : (Subgroup.centralizer (U : Set Y)).Normal := inferInstance
    exact inferInstance
  · rw [eq_bot_iff]
    intro x hx
    have : x ∈ U ⊓ X := ⟨hx.1.1, hx.2⟩
    rwa [hUX] at this

theorem pCore_le [Finite A] [Finite Y] (hne : ¬ (Nat.card W = 2 ∧ Nat.card Q = 4))
    {p : ℕ} (hp : p.Prime) : CFSG.pCore p Y ≤ X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set U := CFSG.pCore p Y with hUdef
  have hUn : U.Normal := CFSG.pCore_normal
  have hUp : IsPGroup p U := CFSG.pCore_isPGroup
  by_cases hU : U = ⊥
  · rw [hU]
    exact bot_le
  have hUX := hD.pCore_inf_ne_bot hne hp hU
  set F₀ := CFSG.fittingSubgroupOf X with hF₀
  have hF₀X : F₀ ≤ X := CFSG.fittingSubgroupOf_le X
  have hF₀nil : Group.IsNilpotent F₀ := CFSG.fittingSubgroupOf_isNilpotent X
  have hRF₀ : R ≤ F₀ := hD.le_fittingSubgroupOf
  set D := (CFSG.pCore p X).map X.subtype with hDdef
  have hDp : IsPGroup p D := CFSG.pCore_isPGroup.map X.subtype
  have hDF : D ≤ F₀ := by
    refine Subgroup.map_mono ?_
    rw [CFSG.fitting_eq_sup_pCore]
    exact CFSG.normal_nilpotent_le_sup_pCore CFSG.pCore_normal CFSG.pCore_isNilpotent
  have hDX : D ≤ X := hDF.trans hF₀X
  have hpelem : ∀ x ∈ F₀, ∀ k : ℕ, x ^ p ^ k = 1 → x ∈ D := by
    rintro _ ⟨x, hx, rfl⟩ k hk
    have hk' : x ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
    exact ⟨x, mem_pCore_of_mem_normal_nilpotent hp CFSG.fittingSubgroup_normal
      CFSG.fittingSubgroup_nilpotent hx hk', rfl⟩
  have hUXD : U ⊓ X ≤ D := by
    rintro u ⟨huU, huX⟩
    have hUn' : (U.subgroupOf X).Normal := hUn.subgroupOf X
    have hUp' : IsPGroup p (U.subgroupOf X) := fun g => by
      obtain ⟨k, hk⟩ := hUp ⟨((g : X) : Y), g.2⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
    have hUnil : Group.IsNilpotent (U.subgroupOf X) := hUp'.isNilpotent
    obtain ⟨k, hk⟩ := hUp ⟨u, huU⟩
    have hk' : (⟨u, huX⟩ : X) ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
    exact ⟨⟨u, huX⟩, mem_pCore_of_mem_normal_nilpotent hp hUn' hUnil
      (show (⟨u, huX⟩ : X) ∈ U.subgroupOf X from huU) hk', rfl⟩
  have hDne : D ≠ ⊥ := fun h => hUX (le_bot_iff.mp (h ▸ hUXD))
  have hP := omegaCenter_ne_bot hp hDp hDne
  by_contra hUle
  have hUD : ¬ U ≤ D := fun h => hUle (h.trans hDX)
  set E := D ⊔ U with hE
  have hEp : IsPGroup p E := hDp.to_sup_of_normal_right hUp
  have hEnil : Group.IsNilpotent E := hEp.isNilpotent
  set H := D.subgroupOf E with hH
  have hHlt : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hUD
    intro u hu
    have : (⟨u, (le_sup_right : U ≤ E) hu⟩ : E) ∈ H := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨u, hu, huH⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent H hHlt)
  have hnorm : ∀ g ∈ Subgroup.normalizer (H : Set E), ∀ d ∈ D, (g : Y) * d * (g : Y)⁻¹ ∈ D := by
    intro g hg d hd
    have h1 := (Subgroup.mem_normalizer_iff.mp hg ⟨d, (le_sup_left : D ≤ E) hd⟩).mp hd
    exact h1
  have hu1 : ∀ d ∈ D, (u : Y) * d * (u : Y)⁻¹ ∈ D := hnorm u hu
  have hu2 : ∀ d ∈ D, (u : Y)⁻¹ * d * (u : Y) ∈ D := by
    intro d hd
    have h1 := hnorm u⁻¹ (Subgroup.inv_mem _ hu) d hd
    simpa using h1
  have huX : (u : Y) ∈ X := hD.mem_X_of_normalizes hF₀X hRF₀ hF₀nil hp hDF hDp hpelem hP
    (fun z hz => conj_mem_omegaCenter hu1 hu2 hz)
  have huE : (u : Y) ∈ ((D ⊔ U : Subgroup Y) : Set Y) := u.2
  rw [Subgroup.mul_normal] at huE
  obtain ⟨d, hd, u', hu', hdu⟩ := huE
  have hu'X : u' ∈ X := by
    have : u' = d⁻¹ * u := by rw [← hdu]; group
    rw [this]
    exact X.mul_mem (X.inv_mem (hDX hd)) huX
  have hu'D : u' ∈ D := hUXD ⟨hu', hu'X⟩
  exact huH (show (u : Y) ∈ D by rw [← hdu]; exact D.mul_mem hd hu'D)

theorem card_eq_of_ne_top [Finite A] [Finite Y] (hXY : X ≠ ⊤) :
    Nat.card W = 2 ∧ Nat.card Q = 4 := by
  classical
  by_contra hne
  have hFY : CFSG.fittingSubgroup Y ≤ X := by
    rw [CFSG.fitting_eq_sup_pCore]
    exact iSup_le fun p => hD.pCore_le hne (Nat.prime_of_mem_primeFactors p.1.2)
  have hF₀X : CFSG.fittingSubgroupOf X ≤ X := CFSG.fittingSubgroupOf_le X
  have hF₀nil := CFSG.fittingSubgroupOf_isNilpotent X
  have hRF₀ := hD.le_fittingSubgroupOf
  have hFYF₀ : CFSG.fittingSubgroup Y ≤ CFSG.fittingSubgroupOf X :=
    CFSG.le_fittingSubgroupOf_of_normal_nilpotent hFY CFSG.fittingSubgroup_normal
      CFSG.fittingSubgroup_nilpotent
  have hsolv : Group.IsSolvable Y := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hD.odd_card
  have hRFY : R ≤ CFSG.fittingSubgroup Y := by
    intro r hr
    apply CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hD.commute_of_mem hF₀X hRF₀ hF₀nil (hFYF₀ hx) hr
  obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one
  have hord1 : orderOf r ≠ 1 := fun h => hr1 (orderOf_eq_one_iff.mp h)
  set p := (orderOf r).minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hord1
  have hord0 : orderOf r ≠ 0 := (isOfFinOrder_of_finite r).orderOf_pos.ne'
  set s := r ^ (orderOf r / p) with hs
  have hsord : orderOf s = p := orderOf_pow_orderOf_div hord0 (Nat.minFac_dvd _)
  set D := CFSG.pCore p Y with hDdef
  have hDp : IsPGroup p D := CFSG.pCore_isPGroup
  have hDF : D ≤ CFSG.fittingSubgroup Y := by
    rw [CFSG.fitting_eq_sup_pCore]
    by_cases hpY : p ∈ (Nat.card Y).primeFactors
    · exact le_iSup_of_le ⟨⟨p, hpY⟩, Finset.mem_attach _ _⟩ le_rfl
    · exfalso
      apply hpY
      refine Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩
      exact hsord ▸ orderOf_dvd_natCard s
  have hpelem : ∀ x ∈ CFSG.fittingSubgroup Y, ∀ k : ℕ, x ^ p ^ k = 1 → x ∈ D :=
    fun x hx k hk => mem_pCore_of_mem_normal_nilpotent hp CFSG.fittingSubgroup_normal
      CFSG.fittingSubgroup_nilpotent hx hk
  have hDne : D ≠ ⊥ := by
    intro h
    have hsD : s ∈ D := hpelem s (hRFY (R.pow_mem hr _)) 1
      (by rw [pow_one, ← hsord, pow_orderOf_eq_one])
    rw [h, Subgroup.mem_bot] at hsD
    rw [hsD, orderOf_one] at hsord
    exact hp.one_lt.ne hsord
  have hP := omegaCenter_ne_bot hp hDp hDne
  have hDn : D.Normal := CFSG.pCore_normal
  apply hXY
  rw [eq_top_iff]
  intro y _
  refine hD.mem_X_of_normalizes hFY hRFY CFSG.fittingSubgroup_nilpotent hp hDF hDp hpelem hP
    fun z hz => conj_mem_omegaCenter (fun d hd => hDn.conj_mem d hd y)
      (fun d hd => by simpa using hDn.conj_mem d hd y⁻¹) hz

end Bender38Action

end CFSG.Walter

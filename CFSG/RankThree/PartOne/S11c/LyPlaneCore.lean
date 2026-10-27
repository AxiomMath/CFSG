module

public import CFSG.RankThree.PartOne.SPOR.OuterLy
public import CFSG.RankThree.GroupTheory.SteinbergBMMovingPlaneTwoSubgroupObstruction
public import CFSG.RankThree.GroupTheory.SteinbergCESmallAlternatingFiveActor
public import CFSG.RankThree.PartOne.S11c.LyPerm
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.ComponentClassification CFSG.RankThree.GroupTheory
open CFSG.Blueprint
open CFSG.Sporadic.LySchreier (involution_centralizers_quasisimple)

theorem inner_of_pow_prime_eq_one {T : Type*} [Group T] [Finite T]
    (hout : Nat.card (OuterAutomorphisms.Outer T) ≤ 4) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {α : MulAut T} (hα : α ^ p = 1) : α ∈ OuterAutomorphisms.inner T := by
  set q := QuotientGroup.mk' (OuterAutomorphisms.inner T) α
  have hqp : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hα, map_one])
  have hqle : orderOf q ≤ 4 :=
    (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard q)).trans hout
  have hq1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime hp).mp hqp with h | h
    · exact h
    · omega
  exact (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp hq1)

theorem prime_eq_five_of_sq_dvd_card_Ly {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hdvd : p ^ 2 ∣ 51765179004000000) : p = 5 := by
  have hN : (51765179004000000 : ℕ) = 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67 := by norm_num
  have hpd : p ∣ 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67 := by
    rw [← hN]
    exact (Dvd.intro_left p (sq p).symm).trans hdvd
  have hpr : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp h
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 31 ∨ p = 37 ∨ p = 67 := by
    simp only [Nat.Prime.dvd_mul hp] at hpd
    rcases hpd with ((((((h | h) | h) | h) | h) | h) | h) | h
    · exact Or.inl (hpr 2 Nat.prime_two (hp.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl (hpr 3 Nat.prime_three (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl (hpr 5 (by norm_num) (hp.dvd_of_dvd_pow h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hpr 7 (by norm_num) h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hpr 11 (by norm_num) h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hpr 31 (by norm_num) h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hpr 37 (by norm_num) h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hpr 67 (by norm_num) h)))))))
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | omega


theorem ly_plane_core
    {T : Type} [Group T] [Finite T]
    (hT : Nonempty (T ≃* NativeSporadic.Ly))
    (hcenter : Subgroup.center T = ⊥) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (E : Subgroup (MulAut T)) [IsElementaryAbelian p E] (hEcard : Nat.card E = p ^ 2)
    (U : Subgroup T) (hU2 : IsPGroup 2 U) (hEU : ∀ e ∈ E, ∀ u ∈ U, e u ∈ U) :
    p = 5 ∧ ∀ e ∈ E, ∀ u ∈ U, e u = u := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hout2, -⟩ := SPOR.outer_order_divides_two' hT
  have hout : Nat.card (OuterAutomorphisms.Outer T) ≤ 4 :=
    (Nat.le_of_dvd (by norm_num) hout2).trans (by norm_num)
  have hEinner : E ≤ OuterAutomorphisms.inner T := fun α hα =>
    inner_of_pow_prime_eq_one hout hp hp5 (elemPow_eq_one_of_isElementaryAbelian α hα)
  have hconj_inj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    intro a c hac
    have hz : c⁻¹ * a ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h : a * x * a⁻¹ = c * x * c⁻¹ := by
        simpa only [MulAut.conj_apply] using congrArg (fun φ : MulAut T => φ x) hac
      calc x * (c⁻¹ * a) = c⁻¹ * (c * x * c⁻¹) * a := by group
        _ = c⁻¹ * (a * x * a⁻¹) * a := by rw [h]
        _ = c⁻¹ * a * x := by group
    rw [hcenter, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hz.symm
  have hdvd : p ^ 2 ∣ Nat.card T := by
    have h1 := Subgroup.card_dvd_of_le hEinner
    rw [hEcard] at h1
    have h2 : Nat.card (OuterAutomorphisms.inner T) = Nat.card T :=
      Nat.card_congr (MonoidHom.ofInjective hconj_inj).symm.toEquiv
    rwa [h2] at h1
  have hcardT : Nat.card T = 51765179004000000 := by
    obtain ⟨e⟩ := hT
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly'
  have hp5' : p = 5 := prime_eq_five_of_sq_dvd_card_Ly hp hp5 (hcardT ▸ hdvd)
  refine ⟨hp5', ?_⟩
  subst hp5'
  by_contra hnc
  push Not at hnc
  obtain ⟨α₀, hα₀, u₀, hu₀, hne⟩ := hnc
  have hinv : CFSG.IsInvariant E T U :=
    ⟨fun a g => ⟨fun hg => hEU a a.2 g hg, fun hg => by
      have h1 := hEU (a⁻¹ : E) (a⁻¹).2 ((a : MulAut T) g) hg
      have h2 : ((a⁻¹ : E) : MulAut T) ((a : MulAut T) g) = g := by
        change ((a : MulAut T)⁻¹ * (a : MulAut T)) g = g
        rw [inv_mul_cancel]
        rfl
      rwa [h2] at h1⟩⟩
  have hcomm : commutatorAction ↥E ↥U ≠ ⊥ := by
    intro h0
    have hmem : (⟨u₀, hu₀⟩ : U)⁻¹ * ((⟨α₀, hα₀⟩ : E) • (⟨u₀, hu₀⟩ : U)) ∈
        commutatorAction ↥E ↥U :=
      Subgroup.subset_closure ⟨⟨α₀, hα₀⟩, ⟨u₀, hu₀⟩, Subgroup.mem_top _, rfl⟩
    rw [h0, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hne (congrArg Subtype.val hmem.symm)
  obtain ⟨R, hR, D, hDcard, -, hRne, -, -, -, -, h16, -, -, hel, hβfix, hγmove⟩ :=
    SteinbergBM.moving_large_prime_plane_two_subgroup_fixed_line_and_small_order_obstruction hp
      (by norm_num) hEcard hU2 hcomm
  have hR16 := h16 rfl
  obtain ⟨β, hβD, hβ1⟩ : ∃ b ∈ D, b ≠ 1 := by
    by_contra h
    push Not at h
    have hD : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr h
    rw [hD, Subgroup.card_bot] at hDcard
    omega
  obtain ⟨b, hb⟩ : ∃ b : T, MulAut.conj b = (β : MulAut T) := hEinner β.2
  have hβ5 : (β : MulAut T) ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian _ β.2
  have hβord : orderOf (β : MulAut T) = 5 := by
    have hdvd5 : orderOf (β : MulAut T) ∣ 5 := orderOf_dvd_of_pow_eq_one hβ5
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd5 with h | h
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h)) hβ1
    · exact h
  have hbord : orderOf b = 5 := by
    rw [← orderOf_injective (MulAut.conj : T →* MulAut T) hconj_inj b, hb]
    exact hβord
  have hb5 : b ^ 5 = 1 := hbord ▸ pow_orderOf_eq_one b
  set R' : Subgroup T := R.map U.subtype with hR'
  have hR'2 : IsPGroup 2 R' := hU2.to_le (Subgroup.map_subtype_le R)
  have hcardR' : Nat.card R' = Nat.card R := Subgroup.card_map_of_injective U.subtype_injective
  have hbR : ∀ u ∈ R', b * u * b⁻¹ = u := by
    intro u hu
    have h1 : (β : MulAut T) u = u := by
      obtain ⟨r, hr, rfl⟩ := hu
      exact congrArg Subtype.val (hβfix β hβD hβ1 r hr)
    rw [← hb, MulAut.conj_apply] at h1
    exact h1
  have hRnt : Nontrivial R' :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardR']; omega)
  have hZnt : Nontrivial (Subgroup.center R') := hR'2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center R') :=
    hR'2.of_injective (Subgroup.center R').subtype (Subgroup.center R').subtype_injective
  have h2dvd : 2 ∣ Nat.card (Subgroup.center R') := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hZ2
    have hn0 : n ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card_iff_nontrivial.mpr hZnt
      rw [hn] at this
      omega
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R') 2 h2dvd
  set w : T := (((z : Subgroup.center R') : R') : T) with hwdef
  have hwR : w ∈ R' := ((z : Subgroup.center R') : R').2
  have hw2 : orderOf w = 2 := by
    rw [hwdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have hwcomm : ∀ r ∈ R', r * w = w * r := by
    intro r hr
    have := Subgroup.mem_center_iff.mp z.2 ⟨r, hr⟩
    exact congrArg Subtype.val this
  set C : Subgroup T := Subgroup.centralizer ({w} : Set T) with hC
  have hRC : R' ≤ C := fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hwcomm r hr)
  have hbC : b ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have := hbR w hwR
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨-, hcard2, ⟨φ⟩⟩ := involution_centralizers_quasisimple hT w hw2
  let ψ : ↥C →* ↥(alternatingGroup (Fin 11)) :=
    (φ : ↥C ⧸ Subgroup.center ↥C →* ↥(alternatingGroup (Fin 11))).comp
      (QuotientGroup.mk' (Subgroup.center ↥C))
  have hψker : ∀ x : ↥C, ψ x = 1 ↔ x ∈ Subgroup.center ↥C := by
    intro x
    change φ (x : ↥C ⧸ Subgroup.center ↥C) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let ι : ↥R' →* ↥C := Subgroup.inclusion hRC
  let θ : ↥R' →* Equiv.Perm (Fin 11) :=
    (alternatingGroup (Fin 11)).subtype.comp (ψ.comp ι)
  have hkercard : Nat.card θ.ker ≤ 2 := by
    rw [← hcard2]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨ι (x : ↥R'), (hψker (ι x)).mp (Subtype.ext (by
        have h1 : θ (x : ↥R') = 1 := x.2
        exact h1))⟩ : Subgroup.center ↥C)) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subgroup.inclusion_injective hRC
    exact congrArg Subtype.val hxy
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set σ' : ↥(alternatingGroup (Fin 11)) := ψ ⟨b, hbC⟩ with hσ'
  set σ : Equiv.Perm (Fin 11) := (σ' : Equiv.Perm (Fin 11)) with hσ
  have hσ5 : orderOf σ = 5 := by
    have hpow : σ' ^ 5 = 1 := by
      rw [hσ', ← map_pow]
      have : (⟨b, hbC⟩ : ↥C) ^ 5 = 1 := Subtype.ext (by simpa using hb5)
      rw [this, map_one]
    have hne : σ' ≠ 1 := by
      intro h1
      have hcen : (⟨b, hbC⟩ : ↥C) ∈ Subgroup.center ↥C := (hψker ⟨b, hbC⟩).mp (hσ' ▸ h1)
      have h2 : (⟨b, hbC⟩ : ↥C) ^ 2 = 1 := by
        have := pow_card_eq_one' (G := Subgroup.center ↥C) (x := ⟨⟨b, hbC⟩, hcen⟩)
        rw [hcard2] at this
        exact congrArg Subtype.val this
      have h2' : b ^ 2 = 1 := congrArg Subtype.val h2
      have : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one h2'
      rw [hbord] at this
      omega
    have hσ'ord : orderOf σ' = 5 := orderOf_eq_prime hpow hne
    rw [hσ, Subgroup.orderOf_coe]
    exact hσ'ord
  have hXσ : ∀ r : ↥R', θ r * σ = σ * θ r := by
    intro r
    have hcomm' : ι r * ⟨b, hbC⟩ = ⟨b, hbC⟩ * ι r := by
      apply Subtype.ext
      have := hbR (r : T) r.2
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have h1 : ψ (ι r) * σ' = σ' * ψ (ι r) := by
      rw [hσ', ← map_mul, ← map_mul, hcomm']
    exact congrArg Subtype.val h1
  have hX2 : IsPGroup 2 θ.range := hR'2.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hXA : θ.range ≤ alternatingGroup (Fin 11) := by
    rintro _ ⟨r, rfl⟩
    exact (ψ (ι r)).2
  have hX8 : Nat.card θ.range ≤ 8 :=
    card_le_eight_of_commute_orderOf_five (n := 11) (by norm_num) hσ5 hX2 hXA (by
      rintro _ ⟨r, rfl⟩
      exact hXσ r)
  have hkerrange := Subgroup.card_ker_mul_card_range θ
  have hkpos : 0 < Nat.card θ.ker := Nat.card_pos
  have hrpos : 0 < Nat.card θ.range := Nat.card_pos
  have hR'ge : 16 ≤ Nat.card R' := by rw [hcardR']; exact hR16
  have hrange8 : Nat.card θ.range = 8 := by
    have hk : Nat.card θ.ker = 1 ∨ Nat.card θ.ker = 2 := by omega
    rcases hk with hk | hk
    · rw [hk, one_mul] at hkerrange
      omega
    · rw [hk] at hkerrange
      omega
  have hcardR16 : Nat.card R = 16 := by
    have hk : Nat.card θ.ker = 1 ∨ Nat.card θ.ker = 2 := by omega
    rcases hk with hk | hk
    · rw [hk, hrange8] at hkerrange
      omega
    · rw [hk, hrange8] at hkerrange
      rw [← hcardR']
      omega
  have hRel : IsElementaryAbelian 2 ↥R := hel rfl hcardR16
  have hR2 : ∀ r : ↥R', r ^ 2 = 1 := by
    intro r
    obtain ⟨r0, hr0, hr0eq⟩ : ∃ r0 ∈ R, (U.subtype r0 : T) = (r : T) := r.2
    have hel2 : (⟨r0, hr0⟩ : ↥R) ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 ↥R)
        ⟨r0, hr0⟩
    have h3 : ((r0 : U) : T) ^ 2 = 1 := by
      have := congrArg (fun x : ↥R => (((x : U) : T))) hel2
      simpa using this
    have h4 : (r : T) ^ 2 = 1 := by
      rw [← hr0eq]
      exact h3
    exact Subtype.ext (by simpa using h4)
  have hXsq : ∀ u ∈ θ.range, u ^ 2 = 1 := by
    rintro _ ⟨r, rfl⟩
    rw [← map_pow, hR2 r, map_one]
  have h4 := LyPerm.card_le_four_of_commute_five (U := θ.range) hXA hXsq hσ5 (by
    rintro _ ⟨r, rfl⟩
    exact hXσ r)
  omega

end CFSG.RankThree.PartOne

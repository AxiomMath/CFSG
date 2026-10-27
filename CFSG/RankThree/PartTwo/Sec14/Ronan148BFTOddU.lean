module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148VFieldTopB
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BFTMainU
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BFTArith
import CFSG.RankThree.PartTwo.Sec18.Item185OuterLin

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField)

section Certificates


theorem kf148FieldTopTwistROddU_holds : Ronan148V.KF148FieldTopTwistROddU := by
  intro X _ _ J K E σ n hn hJ hind hσ3 hKJ hKC hKs hK hEJ hEC hEc hE3 z hz hz1 hodd hq R hRK
    hR3 hRN hRc hR1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσN : σ ∈ Subgroup.normalizer (J : Set X) := hind.mem_normalizer
  have hf : Odd (3 * n) := by
    rcases Nat.even_or_odd (3 * n) with ⟨k, hk⟩ | h
    · exfalso
      rw [hk, ← two_mul, pow_mul, Nat.pow_mod] at hq
      norm_num at hq
    · exact h
  have hnodd : Odd n := (Nat.odd_mul.mp hf).2
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by obtain ⟨k, rfl⟩ := hnodd; omega
    subst hn1
    haveI := hKs
    rcases hK with ⟨hq', -⟩ | ⟨-, ⟨φ⟩⟩
    · norm_num at hq'
    · exact Sec18.Item185Proof.not_isSimpleGroup_projSU_three_two_one φ.symm.isSimpleGroup
  obtain ⟨hU, χ, τ, hτ, hχ⟩ :=
    Ronan148V.exists_fieldAut_model_unitary hn hJ hq hind hσ3 hσN hKJ hKC hK
  set F := GaloisField 2 (2 * (3 * n)) with hFdef
  have hcardF : Nat.card F = 2 ^ (2 * (3 * n)) := GaloisField.card 2 _ (by omega)
  obtain ⟨hτ3, hτω, hτfix⟩ := Sec4.Ronan148B.fieldAut_three_facts hn hcardF hτ
  obtain ⟨r, hrp, hr3, hrc, hr2, hr4⟩ := Sec4.Ronan148B.exists_prime_dvd_cube_add_one hnodd hn3
  haveI : Fact r.Prime := ⟨hrp⟩
  have hdvdF : r ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hcardF]
    have e : 2 ^ (2 * (3 * n)) = ((2 ^ n) ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
    rw [e]
    have h2 : ((2 ^ n) ^ 3) ^ 2 - 1 = ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 3 - 1) := by
      have := Nat.sq_sub_sq ((2 ^ n) ^ 3) 1
      simpa using this
    rw [h2]
    exact Dvd.dvd.mul_right hrc _
  obtain ⟨lam, hlam⟩ := exists_prime_orderOf_dvd_card' r hdvdF
  have hlm : lam ^ r = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
  have hm : Nat.Coprime r 3 := (Nat.coprime_primes hrp Nat.prime_three).mpr hr3
  have hlN : hU.norm (lam : F) = 1 := by
    rw [hU.norm_eq_pow, ← Units.val_pow_eq_pow_val]
    have : lam ^ ((2 : ℕ) ^ (3 * n) + 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hlam, pow_mul']
      exact hrc
    rw [this, Units.val_one]
  have hτl : τ lam ≠ lam := by
    intro h
    have hcases := hτfix (lam : F) h
    have hpow : ∀ k : ℕ, 1 ≤ k → (lam : F) ^ k = lam → r ∣ k - 1 := by
      intro k hk hlk
      have hu : lam ^ k = lam := Units.ext (by rw [Units.val_pow_eq_pow_val, hlk])
      have hu1 : lam ^ (k - 1) = 1 := by
        have : lam ^ (k - 1) * lam = 1 * lam := by
          rw [← pow_succ, Nat.sub_add_cancel hk, one_mul, hu]
        exact mul_right_cancel this
      rw [← hlam]
      exact orderOf_dvd_of_pow_eq_one hu1
    rcases hcases with h2 | h4
    · exact hr2 (hpow _ (Nat.one_le_pow _ _ (by positivity)) h2)
    · exact hr4 (hpow _ (Nat.one_le_pow _ _ (by positivity)) h4)
  have hσJ : ∀ x : J, ((J.normalizerMonoidHom ⟨σ, hσN⟩ x : J) : X) = σ * x * σ⁻¹ := fun x =>
    Sec4.normalizerMonoidHom_apply_coe hσN x
  have hfixσ : ∀ x : J, (x : X) * σ = σ * x → psuField hU τ (χ x) = χ x := by
    intro x hx
    rw [← hχ]
    congr 1
    apply Subtype.ext
    rw [hσJ, ← hx, mul_inv_cancel_right]
  set E' := (E.subgroupOf J).map χ.toMonoidHom with hE'
  set R' := (R.subgroupOf J).map χ.toMonoidHom with hR'
  have hRJ : R ≤ J := (hRK.trans inf_le_left).trans hKJ
  have hmemE : ∀ w, w ∈ E' ↔ ∃ e : J, (e : X) ∈ E ∧ χ e = w := by
    intro w
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
  have hmemR : ∀ w, w ∈ R' ↔ ∃ e : J, (e : X) ∈ R ∧ χ e = w := by
    intro w
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hχcomm : ∀ a b : J, (a : X) * b = b * a → χ a * χ b = χ b * χ a := by
    intro a b hab
    rw [← map_mul, ← map_mul]
    exact congrArg χ (Subtype.ext hab)
  set zJ : J := ⟨z, hEJ hz⟩ with hzJ
  have hEc' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (hmemE x).mp hx
    obtain ⟨b, hb, rfl⟩ := (hmemE y).mp hy
    exact hχcomm a b (hEcomm _ ha _ hb)
  have hE3' : ∀ x ∈ E', x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (hmemE x).mp hx
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hE3 _ ha)
    rw [this, map_one]
  have hEs' : ∀ x ∈ E', psuField hU τ x = x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (hmemE x).mp hx
    exact hfixσ a (Subgroup.mem_centralizer_singleton_iff.mp (hEC ha))
  have hz' : χ zJ ∈ E' := (hmemE _).mpr ⟨zJ, hz, rfl⟩
  have hz1' : χ zJ ≠ 1 := by
    intro h
    apply hz1
    have : zJ = 1 := χ.injective (h.trans (map_one χ).symm)
    exact congrArg Subtype.val this
  have hodd' : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({χ zJ} : Set (unitaryPSU hU 3))) := by
    rw [← CFSG.RankThree.PartTwo.map_centralizer_singleton χ zJ,
      Subgroup.card_map_of_injective χ.injective]
    have hcard : Nat.card (Subgroup.centralizer ({zJ} : Set J)) =
        Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set X)) := by
      have heq : Subgroup.centralizer ({zJ} : Set J) =
          (J ⊓ Subgroup.centralizer ({z} : Set X)).subgroupOf J := by
        ext y
        rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
          Subgroup.mem_centralizer_singleton_iff]
        constructor
        · intro h
          exact ⟨y.2, congrArg Subtype.val h⟩
        · intro h
          exact Subtype.ext h.2
      rw [heq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    rw [hcard]
    exact hodd
  have hRz' : ∀ x ∈ R', x * χ zJ = χ zJ * x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (hmemR x).mp hx
    exact hχcomm a zJ (Subgroup.mem_centralizer_singleton_iff.mp (hRK ha).2)
  have hR3' : ¬ 3 ∣ Nat.card R' := by
    rw [hR', Subgroup.card_map_of_injective χ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRJ).toEquiv]
    exact hR3
  have hRs' : ∀ x ∈ R', psuField hU τ x = x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (hmemR x).mp hx
    exact hfixσ a (Subgroup.mem_centralizer_singleton_iff.mp (hKC (hRK ha).1))
  have hEN : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R := fun e he r hr =>
    (Subgroup.mem_normalizer_iff.mp (hRN (Subgroup.mem_sup_right he)) r).mp hr
  have hRE' : ∀ e ∈ E', ∀ x ∈ R', e * x * e⁻¹ ∈ R' := by
    intro e he x hx
    obtain ⟨a, ha, rfl⟩ := (hmemE e).mp he
    obtain ⟨b, hb, rfl⟩ := (hmemR x).mp hx
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (hmemR _).mpr ⟨_, by simpa using hEN _ ha _ hb, rfl⟩
  have hER' : ∃ e ∈ E', ∃ x ∈ R', e * x ≠ x * e := by
    by_contra hno
    push Not at hno
    apply hR1
    have hcomm : ∀ e ∈ E, ∀ x ∈ R, e * x = x * e := by
      intro e he x hx
      have h1 := hno (χ ⟨e, hEJ he⟩) ((hmemE _).mpr ⟨_, he, rfl⟩) (χ ⟨x, hRJ hx⟩)
        ((hmemR _).mpr ⟨_, hx, rfl⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (χ.injective h1)
    have hcent : Subgroup.zpowers σ ⊔ E ≤ Subgroup.centralizer (R : Set X) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) fun y hy => ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.mp (hKC (hRK hx).1)
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (hcomm y hy x hx).symm
    have hbot : ⁅R, Subgroup.zpowers σ ⊔ E⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      exact hcent
    rw [hRc, hbot]
  obtain ⟨A', hA'3, hA'E, hA's, hA'z, u', hu'A, hu'1, hu'θ⟩ :=
    Sec4.Ronan148B.exists_twist_torus_model (hU := hU) hf τ hτ3 hτω hm hlm hlN hτl hEc' hE3' hEs'
      hz' hz1' hodd' hRz' hR3' hRs' hRE' hER'
  set A : Subgroup X := (A'.comap χ.toMonoidHom).map J.subtype with hAdef
  have hmemA : ∀ x : J, (x : X) ∈ A ↔ χ x ∈ A' := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro h
      exact ⟨x, h, rfl⟩
  have hAJ : A ≤ J := Subgroup.map_subtype_le _
  have hA3 : ¬ 3 ∣ Nat.card A := by
    rw [hAdef, Subgroup.card_map_of_injective J.subtype_injective]
    have : Nat.card (A'.comap χ.toMonoidHom) = Nat.card A' := by
      have e := A'.comap χ.toMonoidHom |>.equivMapOfInjective χ.toMonoidHom χ.injective
      rw [Nat.card_congr e.toEquiv, Subgroup.map_comap_eq_self_of_surjective χ.surjective]
    rw [this]
    exact hA'3
  have hσA : σ ∈ Subgroup.normalizer (A : Set X) := by
    apply Subgroup.mem_normalizer_fintype
    intro a ha
    obtain ⟨x, hx, rfl⟩ := ha
    have h1 : σ * (x : X) * σ⁻¹ = ((J.normalizerMonoidHom ⟨σ, hσN⟩ x : J) : X) := (hσJ x).symm
    change σ * (x : X) * σ⁻¹ ∈ A
    rw [h1, hmemA, hχ]
    exact hA's _ hx
  have hEA : ∀ e ∈ E, e ∈ Subgroup.normalizer (A : Set X) := by
    intro e he
    apply Subgroup.mem_normalizer_fintype
    intro a ha
    obtain ⟨x, hx, rfl⟩ := ha
    have h1 : e * (x : X) * e⁻¹ = (((⟨e, hEJ he⟩ : J) * x * (⟨e, hEJ he⟩ : J)⁻¹ : J) : X) := by
      simp
    change e * (x : X) * e⁻¹ ∈ A
    rw [h1, hmemA, map_mul, map_mul, map_inv]
    exact hA'E _ ((hmemE _).mpr ⟨_, he, rfl⟩) _ hx
  have hAN : Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (A : Set X) :=
    sup_le (Subgroup.zpowers_le.mpr hσA) hEA
  have hfpf : ∀ a ∈ A, a * z = z * a → a = 1 := by
    rintro _ ⟨x, hx, rfl⟩ hxz
    have h1 := hA'z _ hx (hχcomm x zJ hxz)
    have h2 : x = 1 := χ.injective (h1.trans (map_one χ).symm)
    rw [h2]
    rfl
  have hne : ∃ u ∈ A, u ≠ 1 ∧ u * (σ * z) = (σ * z) * u := by
    set uJ := χ.symm u' with huJ
    refine ⟨uJ, (hmemA uJ).mpr (by rw [huJ, MulEquiv.apply_symm_apply]; exact hu'A), ?_, ?_⟩
    · intro h1
      apply hu'1
      have : uJ = 1 := Subtype.ext h1
      rw [← MulEquiv.apply_symm_apply χ u', ← huJ, this, map_one]
    ·
      have hχu : χ (zJ * uJ * zJ⁻¹) = χ zJ * u' * (χ zJ)⁻¹ := by
        rw [map_mul, map_mul, map_inv, huJ, MulEquiv.apply_symm_apply]
      have hθ : χ (J.normalizerMonoidHom ⟨σ, hσN⟩ (zJ * uJ * zJ⁻¹)) = χ uJ := by
        rw [hχ, hχu, huJ, MulEquiv.apply_symm_apply]
        exact hu'θ
      have h1 : σ * (z * (uJ : X) * z⁻¹) * σ⁻¹ = uJ := by
        have := congrArg Subtype.val (χ.injective hθ)
        rw [hσJ] at this
        simpa [hzJ] using this
      have h2 : (σ * z) * (uJ : X) * (σ * z)⁻¹ = uJ := by
        calc (σ * z) * (uJ : X) * (σ * z)⁻¹ = σ * (z * (uJ : X) * z⁻¹) * σ⁻¹ := by group
          _ = uJ := h1
      calc (uJ : X) * (σ * z) = (σ * z) * (uJ : X) * (σ * z)⁻¹ * (σ * z) := by rw [h2]
        _ = (σ * z) * uJ := by group
  exact Ronan148V.exists_twist_of_fpf hKC hz hEC hEc hAJ hA3 hAN hfpf hne

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148B

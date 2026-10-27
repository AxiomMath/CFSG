module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HA5Base
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.CentralizerM

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore

section RM


theorem le_XR_of_isPerfect {H : Subgroup RM} (hH : Group.IsPerfect H) : H ≤ XR := by
  have h2 : Nat.card (↥RM ⧸ XR) = 2 := by
    rw [← Subgroup.index, XR_index]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := isCyclic_of_prime_card (α := ↥RM ⧸ XR) h2
  have hcomm : IsMulCommutative (↥RM ⧸ XR) := IsCyclic.isMulCommutative
  have hle : commutator ↥RM ≤ XR :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp hcomm
  calc H = ⁅H, H⁆ := (Subgroup.isPerfect_iff.mp hH).symm
    _ ≤ ⁅(⊤ : Subgroup RM), ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ = commutator ↥RM := (commutator_def ↥RM).symm
    _ ≤ XR := hle

theorem eq_onq_sq {g : Equiv.Perm (Fin N)} (hg : g ∈ onQ) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    g = onq ^ 2 := by
  have h4 := orderOf_onq
  have hq4 : onq ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one onq
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr hg)
  dsimp only at hn
  subst hn
  have hr : onq ^ n = onq ^ (n % 4) := by
    conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, hq4, one_pow, one_mul]
  rw [hr] at hg1 hg2 ⊢
  have hne : ∀ k, 0 < k → k < 4 → onq ^ k ≠ 1 := fun k hk hk4 =>
    pow_ne_one_of_lt_orderOf (by omega) (by rw [h4]; exact hk4)
  have hlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 4
  · exact absurd (pow_zero _) hg1
  · rw [← pow_mul] at hg2
    exact absurd hg2 (hne 2 (by norm_num) (by norm_num))
  · rfl
  · rw [← pow_mul, show 3 * 2 = 4 + 2 by norm_num, pow_add, hq4, one_mul] at hg2
    exact absurd hg2 (hne 2 (by norm_num) (by norm_num))

end RM

namespace A5Cfg

set_option linter.unusedSectionVars false


variable {X : Type} [Group X] [Finite X] {P : Subgroup X} {q : X} {M F : Subgroup X}

theorem thetaM_eq_bot (h : A5Cfg P q M F) : thetaM M = ⊥ := by
  rcases h.card_theta with h1 | h4
  · exact Subgroup.eq_bot_of_card_eq _ h1
  exfalso
  obtain ⟨hZ3, ⟨e⟩⟩ := h.triple
  set ρ : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) with hρ
  have hρker : ∀ x, ρ x = 1 ↔ x ∈ Subgroup.center X := fun x => QuotientGroup.eq_one_iff x
  set θ := thetaM M with hθ
  have hθM : θ ≤ M := thetaM_le M
  have hθZ : ∀ x ∈ θ, x ∈ Subgroup.center X → x = 1 := by
    intro x hxθ hxZ
    obtain ⟨k, hk⟩ := h.isPGroup_thetaM ⟨x, hxθ⟩
    have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hx3 : x ^ 3 = 1 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hxZ
      rw [hZ3] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hxk, hx3⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hρinj : ∀ x ∈ θ, ∀ y ∈ θ, ρ x = ρ y → x = y := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ = 1 := hθZ _ (θ.mul_mem hx (θ.inv_mem hy))
      ((hρker _).mp (by rw [map_mul, map_inv, hxy, mul_inv_cancel]))
    exact mul_inv_eq_one.mp h1
  have h2θ : 2 ∣ Nat.card θ := by rw [h4]; norm_num
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥θ) 2 h2θ
  set t : X := (t₀ : X) with ht
  have htθ : t ∈ θ := t₀.2
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← SubgroupClass.coe_pow, ← ht₀, pow_orderOf_eq_one, OneMemClass.coe_one]
  have ht1 : t ≠ 1 := by
    intro h1
    have : t₀ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht₀
    norm_num at ht₀
  have hρt : orderOf (ρ t) = 2 := by
    refine orderOf_eq_prime (by rw [← map_pow, ht2, map_one]) fun h1 => ht1 ?_
    exact hρinj t htθ 1 θ.one_mem (by rw [h1, map_one])
  let ψ := CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.centralizerEquivM e hρt
  have hcomm : ∀ m ∈ M, ∀ x ∈ θ, m * x = x * m := fun m hm x hx =>
    ((Subgroup.mem_centralizer_iff.mp (h.le_centralizer_thetaM hm)) x hx).symm
  have hMC : ∀ m : ↥M, (ρ.comp M.subtype) m ∈
      Subgroup.centralizer ({ρ t} : Set (X ⧸ Subgroup.center X)) := by
    intro m
    rw [Subgroup.mem_centralizer_singleton_iff]
    change ρ m * ρ t = ρ t * ρ m
    rw [← map_mul, ← map_mul, hcomm m m.2 t htθ]
  let φ : ↥M →* ↥onM := ψ.toMonoidHom.comp ((ρ.comp M.subtype).codRestrict _ hMC)
  have hφinj : ∀ x (hx : x ∈ θ) y (hy : y ∈ θ), φ ⟨x, hθM hx⟩ = φ ⟨y, hθM hy⟩ → x = y := by
    intro x hx y hy hxy
    have h1 := congrArg Subtype.val (ψ.injective hxy)
    exact hρinj x hx y hy h1
  let Φ : ↥M →* RM := piR.comp φ
  have hqθ : q ∈ Subgroup.normalizer (θ : Set X) := h.le_normalizer_thetaM h.qP
  have hfix := h.inf_centralizer_theta
  set t' := q * t * q⁻¹ with ht'
  set t'' := q * t' * q⁻¹ with ht''
  have ht'θ : t' ∈ θ := (Subgroup.mem_normalizer_iff.mp hqθ t).mp htθ
  have ht''θ : t'' ∈ θ := (Subgroup.mem_normalizer_iff.mp hqθ t').mp ht'θ
  have ht'2 : t' ^ 2 = 1 := by rw [ht', conj_pow, ht2, mul_one, mul_inv_cancel]
  have ht''2 : t'' ^ 2 = 1 := by rw [ht'', conj_pow, ht'2, mul_one, mul_inv_cancel]
  have ht'1 : t' ≠ 1 := by
    intro h1
    apply ht1
    calc t = q⁻¹ * t' * q := by rw [ht']; group
      _ = 1 := by rw [h1]; group
  have ht''1 : t'' ≠ 1 := by
    intro h1
    apply ht'1
    calc t' = q⁻¹ * t'' * q := by rw [ht'']; group
      _ = 1 := by rw [h1]; group
  have hne : t' ≠ t'' := by
    intro h1
    have hmem : t' ∈ θ ⊓ Subgroup.centralizer ({q} : Set X) := by
      refine ⟨ht'θ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc t' * q = q * t' * q⁻¹ * q := by rw [← ht'', ← h1]
        _ = q * t' := by group
    rw [hfix, Subgroup.mem_bot] at hmem
    exact ht'1 hmem
  have hΦ : ∃ u, ∃ hu : u ∈ θ, Φ ⟨u, hθM hu⟩ ≠ 1 ∧ u ^ 2 = 1 := by
    by_contra hall
    push Not at hall
    have hker : ∀ u (hu : u ∈ θ), u ^ 2 = 1 → u ≠ 1 →
        ((φ ⟨u, hθM hu⟩ : ↥onM) : Equiv.Perm (Fin N)) = onq ^ 2 := by
      intro u hu hu2 hu1
      have h1 : φ ⟨u, hθM hu⟩ ∈ piR.ker := by
        rw [MonoidHom.mem_ker]
        by_contra hne
        exact hall u hu hne hu2
      rw [ker_piR, Subgroup.mem_subgroupOf] at h1
      refine eq_onq_sq h1 ?_ ?_
      · have : φ ⟨u, hθM hu⟩ ^ 2 = 1 := by
          rw [← map_pow, show (⟨u, hθM hu⟩ : ↥M) ^ 2 = 1 from Subtype.ext (by simpa using hu2),
            map_one]
        simpa using congrArg Subtype.val this
      · intro h1
        have : φ ⟨u, hθM hu⟩ = φ ⟨1, hθM θ.one_mem⟩ := by
          rw [show (⟨1, hθM θ.one_mem⟩ : ↥M) = 1 from rfl, map_one]
          exact Subtype.ext h1
        exact hu1 (hφinj u hu 1 θ.one_mem this)
    have e1 := hker t' ht'θ ht'2 ht'1
    have e2 := hker t'' ht''θ ht''2 ht''1
    exact hne (hφinj t' ht'θ t'' ht''θ (Subtype.ext (e1.trans e2.symm)))
  obtain ⟨u, huθ, hΦu, hu2⟩ := hΦ
  haveI : Group.IsPerfect ↥M := h.Mp
  have hΦp : Group.IsPerfect Φ.range :=
    Group.IsPerfect.ofSurjective (f := Φ.rangeRestrict) Φ.rangeRestrict_surjective
  have hΦX : ∀ m : ↥M, Φ m ∈ XR := fun m => le_XR_of_isPerfect hΦp ⟨m, rfl⟩
  let Ψ : ↥M →* CFSG.ComponentClassification.PSL3Four.S :=
    CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.xrEquivS.toMonoidHom.comp
      (Φ.codRestrict XR hΦX)
  set u' : ↥M := ⟨u, hθM huθ⟩ with hu'
  have hΨu1 : Ψ u' ≠ 1 := by
    intro h1
    apply hΦu
    have h2 : Φ.codRestrict XR hΦX u' = 1 :=
      CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.xrEquivS.injective
        (by rw [map_one]; exact h1)
    exact congrArg Subtype.val h2
  have hΨu : orderOf (Ψ u') = 2 := by
    refine orderOf_eq_prime ?_ hΨu1
    rw [← map_pow, show u' ^ 2 = 1 from Subtype.ext (by simpa using hu2), map_one]
  have hle : Ψ.range ≤ Subgroup.centralizer ({Ψ u'} : Set _) := by
    rintro _ ⟨m, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm m m.2 u huθ)
  have h64 : Nat.card Ψ.range ∣ 2 ^ 6 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [CFSG.ComponentClassification.PSL3Four.card_centralizer_involution_S _ hΨu] at this
  have hp : IsPGroup 2 Ψ.range := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h64
    exact IsPGroup.of_card hk
  haveI : Group.IsPerfect Ψ.range :=
    Group.IsPerfect.ofSurjective (f := Ψ.rangeRestrict) Ψ.rangeRestrict_surjective
  have hnt : Nontrivial Ψ.range :=
    ⟨⟨⟨Ψ u', u', rfl⟩, 1, fun h1 => hΨu1 (congrArg Subtype.val h1)⟩⟩
  exact Group.IsPerfect.not_isNilpotent (G := Ψ.range) hp.isNilpotent

end A5Cfg

end CFSG.RankThree.PartTwo.Sec14.Ronan148H

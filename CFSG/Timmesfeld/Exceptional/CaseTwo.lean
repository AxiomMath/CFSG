module

public import CFSG.Timmesfeld.Exceptional.Polar
public import CFSG.Timmesfeld.Exceptional.Residual

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Timmesfeld.Special
open scoped commutatorElement

variable {G : Type*} [Group G] {D : Set G}

@[expose] def ExcLambdaNC (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ y ∈ D, Commute d y → d * y ∈ D →
    ∃ z ∈ D, Commute d z ∧ d * z ∈ D ∧ ¬ Commute y z

theorem mul_sq_comm_of_orderOf_eq_four {d e : G} (hd : d * d = 1) (he : e * e = 1)
    (h4 : orderOf (d * e) = 4) : (d * e) ^ 2 = (e * d) ^ 2 := by
  have hinv : (d * e)⁻¹ = e * d := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hd, inv_eq_of_mul_eq_one_right he]
  have hx4 : (d * e) ^ 4 = 1 := h4 ▸ pow_orderOf_eq_one (d * e)
  rw [← hinv, inv_pow, eq_inv_iff_mul_eq_one, ← pow_add]
  exact hx4

theorem NoLevi.orderOf_eq_four (hD : IsRootInvolutionSet D) (hNL : NoLevi D) {d p f : G}
    (hd : d ∈ D) (hp : p ∈ D) (hf : f ∈ D) (hdp : Commute d p) (hdf : Commute d f)
    (hpf : ¬ Commute p f) : orderOf (p * f) = 4 := by
  rcases hD.orderOf_mul hp hf with h2 | h4 | hodd
  · exfalso
    apply hpf
    rw [commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hp) (hD.mul_self_eq_one hf), ← h2]
    exact pow_orderOf_eq_one _
  · exact h4
  · exact absurd hdf (hNL p hp f hf hpf hodd d hd hdp)

theorem exists_commute_not_commute [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hsing : ∀ x ∈ D, rootSet D x = {x}) {d p : G} (hd : d ∈ D) (hp : p ∈ D)
    (hdp : Commute d p) (hne : p ≠ d) : ∃ g ∈ D, Commute d g ∧ ¬ Commute p g := by
  by_contra h
  have hmem : p ∈ rootSet D d := (mem_rootSet_iff hclass hd).2 ⟨hp, hdp, fun f hf hdf => by
    by_contra hpf
    exact h ⟨f, hf, hdf, hpf⟩⟩
  rw [hsing d hd, Set.mem_singleton_iff] at hmem
  exact hne hmem

theorem conj_mem_lambda (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    {d g z : G} (hg : g ∈ D) (hdg : Commute d g) (hz : z ∈ D) (hdz : Commute d z)
    (hdzD : d * z ∈ D) : g * z * g ∈ D ∧ Commute d (g * z * g) ∧ d * (g * z * g) ∈ D := by
  have hginv : g⁻¹ = g := hD.inv_eq hg
  refine ⟨by simpa [hginv] using conj_mem_of_isClass hclass g hz,
    (hdg.mul_right hdz).mul_right hdg, ?_⟩
  have : d * (g * z * g) = g * (d * z) * g⁻¹ := by
    rw [hginv, ← mul_assoc, ← mul_assoc, hdg.eq, mul_assoc g d z]
  rw [this]
  exact conj_mem_of_isClass hclass g hdzD

theorem NoLevi.exists_not_commute [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hNL : NoLevi D)
    {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : Commute d x) (hne : x ≠ d) :
    ∃ z ∈ D, Commute d z ∧ d * z ∈ D ∧ ¬ Commute x z := by
  classical
  by_contra hZx
  set Z : Set G := {y | y ∈ D ∧ Commute d y ∧ y ≠ d ∧
    ∀ z ∈ D, Commute d z → d * z ∈ D → Commute y z} with hZ
  have hxZ : x ∈ Z := ⟨hx, hdx, hne, fun z hz hdz hdzD => by
    by_contra h
    exact hZx ⟨z, hz, hdz, hdzD, h⟩⟩
  set K : Subgroup G := Subgroup.closure {y | y ∈ D ∧ Commute y d} with hK
  have hK2 : IsPGroup 2 K := (isPGroup_twoCore d).to_le (hNL.closure_le_twoCore hclass hD hd)
  have hmemK : ∀ y ∈ D, Commute y d → y ∈ K := fun y hy hyd => Subgroup.subset_closure ⟨hy, hyd⟩
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries K).1 hK2.isNilpotent
  have hstep : ∀ y ∈ Z, ∃ g ∈ D, Commute d g ∧ (y * g) ^ 2 = ⁅y, g⁆ ∧ (y * g) ^ 2 ∈ Z := by
    rintro y ⟨hy, hdy, hyd, hyc⟩
    obtain ⟨g, hg, hdg, hyg⟩ := exists_commute_not_commute hclass hsing hd hy hdy hyd
    have hg2 : g * g = 1 := hD.mul_self_eq_one hg
    have hginv : g⁻¹ = g := hD.inv_eq hg
    have h4 := hNL.orderOf_eq_four hD hd hy hg hdy hdg hyg
    obtain ⟨hcD, -, -, hconj⟩ := sq_mem_of_orderOf_eq_four hD hy hg h4
    refine ⟨g, hg, hdg,
      (commutatorElement_eq_mul_sq (hD.mul_self_eq_one hy) hg2).symm, hcD,
      (hdy.mul_right hdg).pow_right 2, fun hcd => hyg ?_, fun z hz hdz hdzD => ?_⟩
    ·
      refine hyc g hg hdg ?_
      have : d * g = y * g * y⁻¹ := by
        calc d * g = (y * g) ^ 2 * g := by rw [hcd]
          _ = y * g * y * (g * g) := by rw [pow_two]; simp only [mul_assoc]
          _ = y * g * y⁻¹ := by rw [hg2, mul_one, hD.inv_eq hy]
      rw [this]
      exact conj_mem_of_isClass hclass y hg
    ·
      obtain ⟨hz', hdz', hdzD'⟩ := conj_mem_lambda hclass hD hg hdg hz hdz hdzD
      have h1 : Commute y (g * z * g) := hyc _ hz' hdz' hdzD'
      have h2 : Commute (g * y * g) z := by
        have := (Commute.conj_iff g).2 h1
        rwa [hginv, show g * (g * z * g) * g = (g * g) * z * (g * g) by group, hg2, one_mul,
          mul_one] at this
      have hc : (y * g) ^ 2 = y * (g * y * g) := by
        rw [hconj, ← mul_assoc, hD.mul_self_eq_one hy, one_mul]
      rw [hc]
      exact (hyc z hz hdz hdzD).mul_left h2
  have key : ∀ k, ∃ y ∈ Z, y ∈ K.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact ⟨x, hxZ, hmemK x hx hdx.symm⟩
    | succ k ih =>
      obtain ⟨y, hyZ, hyk⟩ := ih
      obtain ⟨g, hg, hdg, hcomm, hcZ⟩ := hstep y hyZ
      refine ⟨_, hcZ, ?_⟩
      rw [hcomm, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mem_commutator hyk (hmemK g hg hdg.symm)
  obtain ⟨y, hyZ, hyn⟩ := key n
  rw [hn, Subgroup.mem_bot] at hyn
  exact hD.ne_one hyZ.1 hyn

theorem NoLevi.lambdaNC [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hNL : NoLevi D) :
    ExcLambdaNC D := by
  intro d hd y hy hdy hdyD
  refine hNL.exists_not_commute hclass hD hsing hd hy hdy ?_
  rintro rfl
  rw [hD.mul_self_eq_one hy] at hdyD
  exact hD.ne_one hdyD rfl

theorem noPolar_of_noLevi [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hNL : NoLevi D)
    (hPl : ExcNoPlane D) (hL : ExcLambdaNC D) : NoPolar D := by
  classical
  intro d hd p₀ hp₀ hdp₀ hne₀
  by_contra hpol₀
  have hconjD : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  set P : Set G := {p | p ∈ D ∧ Commute d p ∧ p ≠ d ∧ d * p ∉ D} with hP
  have hp₀P : p₀ ∈ P := ⟨hp₀, hdp₀, fun h => hne₀ h.symm, hpol₀⟩
  set K : Subgroup G := Subgroup.closure {x | x ∈ D ∧ Commute x d} with hK
  have hK2 : IsPGroup 2 K := (isPGroup_twoCore d).to_le (hNL.closure_le_twoCore hclass hD hd)
  have hmemK : ∀ x ∈ D, Commute x d → x ∈ K := fun x hx hxd => Subgroup.subset_closure ⟨hx, hxd⟩
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries K).1 hK2.isNilpotent
  have hcomm : ∀ p ∈ P, ∀ f ∈ D, Commute d f → ¬ Commute p f →
      orderOf (p * f) = 4 ∧ (p * f) ^ 2 ∈ D ∧ Commute d ((p * f) ^ 2) ∧ (p * f) ^ 2 ≠ d ∧
        Commute p ((p * f) ^ 2) ∧ Commute f ((p * f) ^ 2) ∧ f * p * f = p * (p * f) ^ 2 := by
    rintro p ⟨hp, hdp, -, hpol⟩ f hf hdf hpf
    have h4 := hNL.orderOf_eq_four hD hd hp hf hdp hdf hpf
    obtain ⟨hcD, hpc, hfc, hconj⟩ := sq_mem_of_orderOf_eq_four hD hp hf h4
    refine ⟨h4, hcD, (hdp.mul_right hdf).pow_right 2, fun hcd => hpol ?_, hpc, hfc, hconj⟩
    rw [hdp.eq, ← hcd, ← hconj]
    simpa [hD.inv_eq hf] using hconjD f p hp
  have hex : ∃ m, ¬ ∃ p ∈ P, p ∈ K.lowerCentralSeries m := ⟨n, by
    rintro ⟨p, hpP, hpn⟩
    rw [hn, Subgroup.mem_bot] at hpn
    exact hD.ne_one hpP.1 hpn⟩
  have hm₀ : ¬ ∃ p ∈ P, p ∈ K.lowerCentralSeries (Nat.find hex) := Nat.find_spec hex
  have hm₀pos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hm₀
    exact hm₀ ⟨p₀, hp₀P, hmemK p₀ hp₀ hdp₀.symm⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_succ_of_ne_zero hm₀pos
  have hS : ∃ p ∈ P, p ∈ K.lowerCentralSeries k := by
    by_contra h
    exact Nat.find_min hex (show k < Nat.find hex by omega) h
  have hS' : ¬ ∃ p ∈ P, p ∈ K.lowerCentralSeries (k + 1) := hk ▸ hm₀
  have hT1 : ∀ p ∈ P, p ∈ K.lowerCentralSeries k → ∀ f ∈ D, Commute d f → ¬ Commute p f →
      d * (p * f) ^ 2 ∈ D := by
    intro p hpP hpk f hf hdf hpf
    obtain ⟨-, hcD, hdc, hcd, -⟩ := hcomm p hpP f hf hdf hpf
    by_contra hcpol
    have hmem : ⁅p, f⁆ ∈ K.lowerCentralSeries (k + 1) := by
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mem_commutator hpk (hmemK f hf hdf.symm)
    rw [commutatorElement_eq_mul_sq (hD.mul_self_eq_one hpP.1) (hD.mul_self_eq_one hf)] at hmem
    exact hS' ⟨_, ⟨hcD, hdc, hcd, hcpol⟩, hmem⟩
  have hT2 : ∀ p ∈ P, p ∈ K.lowerCentralSeries k → ∀ g ∈ D, Commute d g →
      g * p * g ∈ P ∧ g * p * g ∈ K.lowerCentralSeries k := by
    rintro p ⟨hp, hdp, hpd, hpol⟩ hpk g hg hdg
    have hginv : g⁻¹ = g := hD.inv_eq hg
    have hg2 : g * g = 1 := hD.mul_self_eq_one hg
    refine ⟨⟨by simpa [hginv] using hconjD g p hp, (hdg.mul_right hdp).mul_right hdg,
      fun h => hpd ?_, fun h => hpol ?_⟩, ?_⟩
    ·
      calc p = g * (g * p * g) * g := by
              rw [show g * (g * p * g) * g = (g * g) * p * (g * g) by group, hg2, one_mul,
                mul_one]
        _ = d := by rw [h, ← hdg.eq, mul_assoc, hg2, mul_one]
    ·
      have : d * p = g * (d * (g * p * g)) * g⁻¹ := by
        rw [hginv]
        calc d * p = (g * g) * d * p * (g * g) := by rw [hg2, one_mul, mul_one]
          _ = g * (g * d) * p * (g * g) := by group
          _ = g * (d * g) * p * (g * g) := by rw [← hdg.eq]
          _ = g * (d * (g * p * g)) * g := by group
      rw [this]
      exact hconjD g _ h
    · have hnorm := Subgroup.self_le_normalizer_lowerCentralSeries K k (hmemK g hg hdg.symm)
      rw [Subgroup.mem_normalizer_iff] at hnorm
      have := (hnorm p).1 hpk
      rwa [hginv] at this
  have hT3 : ∀ p ∈ P, p ∈ K.lowerCentralSeries k → ∀ z ∈ D, Commute d z → d * z ∈ D →
      Commute p z := by
    intro p hpP hpk z hz hdz hdzD
    by_contra hpz
    have hp := hpP.1
    have hdp := hpP.2.1
    obtain ⟨h4, hcD, hdc, hcd, hpc, hzc, -⟩ := hcomm p hpP z hz hdz hpz
    have hdcD := hT1 p hpP hpk z hz hdz hpz
    have hz2 : z * z = 1 := hD.mul_self_eq_one hz
    have hp2 : p * p = 1 := hD.mul_self_eq_one hp
    have hdz' : d ≠ z := by
      intro h
      rw [← h, hD.mul_self_eq_one hd] at hdzD
      exact hD.ne_one hdzD rfl
    have hzc' : z * (p * z) ^ 2 = p * z * p := by
      rw [mul_sq_comm_of_orderOf_eq_four hp2 hz2 h4, pow_two]
      simp only [← mul_assoc, hz2, one_mul]
    have hpzp : p * z * p ∈ D := by simpa [hD.inv_eq hp] using hconjD p z hz
    refine hPl d hd z hz ((p * z) ^ 2) hcD hdz hdc hzc hdz' hcd (fun h => hpz ?_) ?_ hdzD
      hdcD (hzc' ▸ hpzp) ?_
    · rw [← h]
      exact hpc
    · intro h
      apply hdz'
      have h1 : p * z * p = d := by
        rw [← hzc', h, ← mul_assoc, ← hdz.eq, mul_assoc, hz2, mul_one]
      calc d = p * (p * z * p) * p := by
            rw [h1, ← hdp.eq, mul_assoc, hp2, mul_one]
        _ = z := by
            rw [show p * (p * z * p) * p = (p * p) * z * (p * p) by group, hp2, one_mul, mul_one]
    ·
      rw [mul_assoc, hzc', show d * (p * z * p) = p * (d * z) * p by
        rw [← mul_assoc, ← mul_assoc, hdp.eq, mul_assoc p d z]]
      simpa [hD.inv_eq hp] using hconjD p _ hdzD
  obtain ⟨p, hpP, hpk⟩ := hS
  obtain ⟨g, hg, hdg, hpg⟩ :=
    exists_commute_not_commute hclass hsing hd hpP.1 hpP.2.1 hpP.2.2.1
  obtain ⟨-, hcD, hdc, -, -, -, hconj⟩ := hcomm p hpP g hg hdg hpg
  have hdcD := hT1 p hpP hpk g hg hdg hpg
  obtain ⟨hp'P, hp'k⟩ := hT2 p hpP hpk g hg hdg
  obtain ⟨z, hz, hdz, hdzD, hcz⟩ := hL d hd _ hcD hdc hdcD
  apply hcz
  have h1 := hT3 p hpP hpk z hz hdz hdzD
  have h2 := hT3 _ hp'P hp'k z hz hdz hdzD
  have hc : (p * g) ^ 2 = p * (g * p * g) := by
    rw [hconj, ← mul_assoc, hD.mul_self_eq_one hpP.1, one_mul]
  rw [hc]
  exact h1.mul_left h2

theorem NoLevi.noPolar [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hNL : NoLevi D)
    (hPl : ExcNoPlane D) : NoPolar D :=
  noPolar_of_noLevi hclass hD hsing hNL hPl (hNL.lambdaNC hclass hD hsing)

theorem NoLevi.residual_of_to5 (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hNL : NoLevi D) (hPl : ExcNoPlane D) (hTO : ExcTO5 D) :
    ExcOrderBound D ∧ NoPolar D ∧ ExcNoPlane D :=
  have := h.finite
  have hNP := hNL.noPolar h.isClass h.root hsing hPl
  ⟨orderBound_of_to5 h hNP hPl hTO, hNP, hPl⟩

end CFSG.Timmesfeld.Moufang

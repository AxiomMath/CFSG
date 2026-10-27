module

public import CFSG.ClassicalGroups.UnitaryFlag.HomologyEigen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.CoprimeInvolutionFix
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Perfect
public import CFSG.RankThree.PartTwo.Sec6.Item65Two

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {m : ℕ} {K : Type} [Field K]

theorem eq_bot_of_isPerfect_of_le_normalizer_unitarySU3 (h : UnitaryFieldData 2 m K)
    (hm : 2 ≤ m) {D P : Subgroup (unitarySU 2 m K 3)} (hD : IsPGroup 2 D) (hD1 : D ≠ ⊥)
    (hP : Group.IsPerfect P) (hPD : P ≤ Subgroup.normalizer (D : Set (unitarySU 2 m K 3))) :
    P = ⊥ := by
  have : Finite K := h.finite
  have : Finite (unitarySU 2 m K 3) :=
    CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts.model3U4_finite_group h
  have hK : Nat.card K = (2 ^ m) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hq : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := by
    intro he
    have h2 : 2 ^ m = 2 := (Prod.mk.inj he).2
    have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hL : CFSG.Blueprint.LieModel (StatedProj (StatedSU 3 (2 ^ m) K)) .PSU 3 2 m :=
    Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, le_refl 3, hq⟩, K, inferInstance,
      inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have : Finite (StatedProj (StatedSU 3 (2 ^ m) K)) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_PSU3 hL
  let φ : unitarySU 2 m K 3 →* StatedProj (StatedSU 3 (2 ^ m) K) :=
    (unitaryPSUEquiv h (n := 3) (by norm_num)).toMonoidHom.comp (unitaryProj h 3)
  have hkerφ : φ.ker = unitaryScalars h 3 := by
    rw [← ker_unitaryProj h 3]
    ext g
    simp [φ, MonoidHom.mem_ker]
  have hker3 : Nat.card φ.ker ∣ 3 := by
    rw [hkerφ, card_unitaryScalars h (n := 3) (by norm_num)]
    exact Nat.gcd_dvd_left 3 (2 ^ m + 1)
  have hD'1 : D.map φ ≠ ⊥ := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
    intro hbot
    have hφx : φ x ∈ D.map φ := Subgroup.mem_map_of_mem φ x.2
    rw [hbot, Subgroup.mem_bot] at hφx
    obtain ⟨k, hk⟩ := hD x
    have h1 : orderOf (x : unitarySU 2 m K 3) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hk
    have h2 : orderOf (x : unitarySU 2 m K 3) ∣ 3 :=
      (Subgroup.orderOf_dvd_natCard φ.ker hφx).trans hker3
    have h3 : orderOf (x : unitarySU 2 m K 3) ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num))] at h3
    exact hx (Subtype.ext (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)))
  have := hP
  have hP' : Group.IsPerfect (P.map φ) := Group.IsPerfect.map φ
  have hPD' : P.map φ ≤ Subgroup.normalizer ((D.map φ : Subgroup _) : Set _) :=
    (Subgroup.map_mono hPD).trans (Subgroup.le_normalizer_map φ)
  have hbot := CFSG.LocalAnalysis.EvenBN.GMSK.eq_bot_of_isPerfect_of_le_normalizer_of_lieModel_PSU3
    hL (hD.map φ) hD'1 hP' hPD'
  have hPcen : P ≤ Subgroup.center (unitarySU 2 m K 3) := by
    have hc := unitaryScalars_le_center h 3
    rw [← hkerφ] at hc
    exact ((Subgroup.map_eq_bot_iff P).mp hbot).trans hc
  have hcomm : ⁅P, P⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hPcen.trans (Subgroup.center_le_centralizer _))
  calc P = ⁅P, P⁆ := (Subgroup.isPerfect_iff.mp hP).symm
    _ = ⊥ := hcomm

theorem exists_range_subOne_ne_of_isPerfect (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    {P : Subgroup (unitarySU 2 m K 3)} (hP : Group.IsPerfect P) (hP1 : P ≠ ⊥) :
    ∃ t ∈ P, ∃ u ∈ P, t ^ 2 = 1 ∧ t ≠ 1 ∧ u ^ 2 = 1 ∧ u ≠ 1 ∧
      LinearMap.range (subOne t) ≠ LinearMap.range (subOne u) := by
  have : Finite (unitarySU 2 m K 3) :=
    CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts.model3U4_finite_group h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2
    (CFSG.RankThree.PartTwo.Sec6.two_dvd_card_of_isPerfect hP hP1)
  have ht2 : (x : unitarySU 2 m K 3) ^ 2 = 1 := by
    have h2 : x ^ 2 = 1 := by
      have h0 := pow_orderOf_eq_one x
      rwa [hx] at h0
    simpa using congrArg Subtype.val h2
  have ht1 : (x : unitarySU 2 m K 3) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  by_contra hall
  push Not at hall
  obtain ⟨hL, -, -⟩ := involution_mem_isotropicTransvectionGroup h ht2 ht1
  have hDle : CFSG.Quasithin.omegaOneOf P ≤
      isotropicTransvectionGroup h 3 (LinearMap.range (subOne (x : unitarySU 2 m K 3))) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨huP, hu2⟩
    by_cases hu1 : u = 1
    · rw [hu1]
      exact one_mem _
    · have hmem := (involution_mem_isotropicTransvectionGroup h hu2 hu1).2.1
      rwa [← hall _ x.2 u huP ht2 ht1 hu2 hu1] at hmem
  have hD : IsPGroup 2 (CFSG.Quasithin.omegaOneOf P) :=
    (isPGroup_isotropicTransvectionGroup h hL).to_le hDle
  have hD1 : CFSG.Quasithin.omegaOneOf P ≠ ⊥ := by
    intro hbot
    have hmem : (x : unitarySU 2 m K 3) ∈ CFSG.Quasithin.omegaOneOf P :=
      Subgroup.subset_closure ⟨x.2, ht2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ht1 hmem
  have key : ∀ g ∈ P, ∀ y ∈ CFSG.Quasithin.omegaOneOf P,
      g * y * g⁻¹ ∈ CFSG.Quasithin.omegaOneOf P := by
    intro g hg y (hy : y ∈ Subgroup.closure {x | x ∈ P ∧ x ^ 2 = 1})
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨hzP, hz2⟩ := hz
      exact Subgroup.subset_closure ⟨P.mul_mem (P.mul_mem hg hzP) (P.inv_mem hg),
        by rw [conj_pow, hz2, mul_one, mul_inv_cancel]⟩
    | one => simp
    | mul y z _ _ hy hz =>
      have := (CFSG.Quasithin.omegaOneOf P).mul_mem hy hz
      simpa only [mul_assoc, inv_mul_cancel_left] using this
    | inv y _ hy =>
      have := (CFSG.Quasithin.omegaOneOf P).inv_mem hy
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
  have hPD : P ≤ Subgroup.normalizer ((CFSG.Quasithin.omegaOneOf P : Subgroup _) :
      Set (unitarySU 2 m K 3)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key g hg y, fun hy => ?_⟩
    have := key g⁻¹ (P.inv_mem hg) _ hy
    simpa [mul_assoc] using this
  exact hP1 (eq_bot_of_isPerfect_of_le_normalizer_unitarySU3 h hm hD hD1 hP hPD)

theorem range_subOne_perp_of_homology (h : UnitaryFieldData 2 m K) {r : ℕ} (hr : r.Prime)
    {a : unitarySU 2 m K 3} (har : a ^ r = 1) {P : Subgroup (unitarySU 2 m K 3)}
    (hrP : ¬ r ∣ Nat.card P) (haP : a ∈ Subgroup.normalizer (P : Set (unitarySU 2 m K 3)))
    {v : Fin 3 → K} {c d : K} (hv : stdHermForm h 3 v v ≠ 0) (hc : c ≠ 0) (hcd : c ≠ d)
    (hav : a • v = d • v) (haW : ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 → a • w = c • w)
    {t : unitarySU 2 m K 3} (htP : t ∈ P) (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∀ x ∈ LinearMap.range (subOne t), stdHermForm h 3 v x = 0 := by
  have : Finite (unitarySU 2 m K 3) :=
    CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts.model3U4_finite_group h
  obtain ⟨hL, -, hker⟩ := involution_mem_isotropicTransvectionGroup h ht ht1
  obtain ⟨w, hw0, hww, hLw⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_eq_span_of_mem_isotropicLines hL
  have hmain : stdHermForm h 3 v w = 0 := by
    by_contra hvw
    obtain ⟨β, w₀, u₀, hβ0, hβw, hw_def, hvw₀, hw₀w₀, hu₀, hvu₀, hw₀u₀, hwu₀, hexp⟩ :=
      exists_orthogonal_completion_of_isotropic h hv hww hvw
    have htu₀ : t • u₀ = u₀ := by
      have hmem : u₀ ∈ LinearMap.ker (subOne t) := by
        rw [hker, hLw, mem_hermPerp]
        intro y hy
        obtain ⟨ν, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [LinearMap.map_smulₛₗ₂, hwu₀, smul_eq_mul, mul_zero]
      have h0 : subOne t u₀ = 0 := LinearMap.mem_ker.mp hmem
      rw [subOne_apply h] at h0
      exact sub_eq_zero.mp h0
    let Y : Subgroup (unitarySU 2 m K 3) :=
      P ⊓ MulAction.stabilizer (unitarySU 2 m K 3) u₀
    have htY : t ∈ Y :=
      Subgroup.mem_inf.mpr ⟨htP, MulAction.mem_stabilizer_iff.mpr htu₀⟩
    have hau₀ : a • u₀ = c • u₀ := haW u₀ hvu₀
    have hainv : a⁻¹ • u₀ = c⁻¹ • u₀ := by
      have h1 : c • (a⁻¹ • u₀) = u₀ := by
        rw [← smul_comm a⁻¹ c u₀, ← hau₀, smul_smul, inv_mul_cancel, one_smul]
      calc a⁻¹ • u₀ = c⁻¹ • (c • (a⁻¹ • u₀)) := (inv_smul_smul₀ hc _).symm
        _ = c⁻¹ • u₀ := by rw [h1]
    have haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := by
      intro y hy
      obtain ⟨hyP, hyu⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp haP y).mp hyP, ?_⟩
      rw [MulAction.mem_stabilizer_iff] at hyu ⊢
      rw [mul_smul, mul_smul, hainv, smul_comm y c⁻¹ u₀, hyu, smul_comm a c⁻¹ u₀,
        hau₀, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hrY : ¬ r ∣ Nat.card Y := fun hdvd =>
      hrP (hdvd.trans (Subgroup.card_dvd_of_le (show Y ≤ P from inf_le_left)))
    set s : unitarySU 2 m K 3 := a * t * a⁻¹ with hs
    have hsY : s ∈ Y := by
      rw [hs]
      exact haY t htY
    have hs2 : s ^ 2 = 1 := by
      rw [hs, conj_pow, ht, mul_one, mul_inv_cancel]
    have hs1 : s ≠ 1 := by
      intro h1
      apply ht1
      rw [hs] at h1
      rwa [conj_eq_one_iff] at h1
    have haw : a • w = c • w₀ + (β * d) • v := by
      rw [hw_def, smul_add, haW w₀ hvw₀, smul_comm a β v, hav, smul_smul]
    have hw₀v : stdHermForm h 3 w₀ v = 0 := by
      rw [← (stdHermForm_isSymm h 3).eq v w₀, hvw₀, map_zero]
    have haw_notmem : a • w ∉ Submodule.span K {w} := by
      intro hmem
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
      have h1 : μ * (β * stdHermForm h 3 v v) = β * d * stdHermForm h 3 v v := by
        have hB := congrArg (stdHermForm h 3 v) (hμ.trans haw)
        simp only [map_add, map_smul, hvw₀, hβw, smul_eq_mul, mul_zero, zero_add] at hB
        exact hB
      have h2 : μ * stdHermForm h 3 w₀ w₀ = c * stdHermForm h 3 w₀ w₀ := by
        have hB := congrArg (stdHermForm h 3 w₀) (hμ.trans haw)
        rw [map_smul, smul_eq_mul] at hB
        rw [map_add, map_smul, map_smul, hw₀v, smul_zero, add_zero] at hB
        have hw : stdHermForm h 3 w₀ w = stdHermForm h 3 w₀ w₀ := by
          rw [hw_def, map_add, map_smul, hw₀v, smul_zero, add_zero]
        rw [hw] at hB
        exact hB
      have hdμ : d = μ := by
        have hfac : β * stdHermForm h 3 v v ≠ 0 := mul_ne_zero hβ0 hv
        have h3 : d * (β * stdHermForm h 3 v v) = μ * (β * stdHermForm h 3 v v) := by
          rw [h1]; ring
        exact mul_right_cancel₀ hfac h3
      have hcμ : c = μ := (mul_right_cancel₀ hw₀w₀ h2).symm
      exact hcd (hcμ.trans hdμ.symm)
    have hne : LinearMap.range (subOne t) ≠ LinearMap.range (subOne s) := by
      intro heq
      apply haw_notmem
      have hline : a • Submodule.span K {w} = Submodule.span K {w} := by
        rw [← hLw, ← range_subOne_conj h a t, ← hs, heq]
      have hmem := Submodule.smul_mem_pointwise_smul w a (Submodule.span K {w})
        (Submodule.mem_span_singleton_self w)
      exact hline ▸ hmem
    obtain ⟨t', ht'Y, ht'2, ht'1, hat'⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_commute_involution_of_conj_transitive
        hr har haY hrY htY ht ht1 fun u huY hu2 hu1 =>
          exists_conj_of_range_subOne_ne h htY hsY huY ht ht1 hs2 hs1 hu2 hu1 hne
    obtain ⟨hL', -, hker'⟩ := involution_mem_isotropicTransvectionGroup h ht'2 ht'1
    obtain ⟨e₁, he₁0, he₁e₁, hL'e₁⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_eq_span_of_mem_isotropicLines hL'
    have ht'u₀ : t' • u₀ = u₀ := by
      have h := (Subgroup.mem_inf.mp ht'Y).2
      rwa [MulAction.mem_stabilizer_iff] at h
    have hu₀perp' : u₀ ∈ hermPerp h (LinearMap.range (subOne t')) := by
      rw [← hker']
      exact LinearMap.mem_ker.mpr (by rw [subOne_apply h, ht'u₀, sub_self])
    have he₁u₀ : stdHermForm h 3 e₁ u₀ = 0 :=
      mem_hermPerp.mp hu₀perp' e₁ (hL'e₁ ▸ Submodule.mem_span_singleton_self e₁)
    have hu₀e₁ : stdHermForm h 3 u₀ e₁ = 0 := by
      rw [← (stdHermForm_isSymm h 3).eq e₁ u₀, he₁u₀, map_zero]
    have hconj : a * t' * a⁻¹ = t' := by
      rw [hat', mul_assoc, mul_inv_cancel, mul_one]
    have hline : a • Submodule.span K {e₁} = Submodule.span K {e₁} := by
      rw [← hL'e₁, ← range_subOne_conj h a t', hconj]
    obtain ⟨μ, hμ⟩ : ∃ μ : K, a • e₁ = μ • e₁ := by
      have hmem := Submodule.smul_mem_pointwise_smul e₁ a (Submodule.span K {e₁})
        (Submodule.mem_span_singleton_self e₁)
      have hmem' : a • e₁ ∈ Submodule.span K {e₁} := hline ▸ hmem
      obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp hmem'
      exact ⟨ν, hν.symm⟩
    exact (stdHermForm_self_ne_zero_of_homology_eigen h hv hw₀w₀ hvw₀ hexp hu₀e₁ he₁0 hcd
      hμ (haW w₀ hvw₀) hav) he₁e₁
  intro x hx
  rw [hLw] at hx
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, smul_eq_mul, hmain, mul_zero]

theorem mem_centralizer_of_isPerfect_unitarySU3 (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {a : unitarySU 2 m K 3} (har : a ^ r = 1)
    {P : Subgroup (unitarySU 2 m K 3)} (hP : Group.IsPerfect P) (hrP : ¬ r ∣ Nat.card P)
    (haP : a ∈ Subgroup.normalizer (P : Set (unitarySU 2 m K 3))) :
    a ∈ Subgroup.centralizer (P : Set (unitarySU 2 m K 3)) := by
  have : Finite (unitarySU 2 m K 3) :=
    CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts.model3U4_finite_group h
  have hext : ∀ g g' : unitarySU 2 m K 3, (∀ x : Fin 3 → K, g • x = g' • x) → g = g' := by
    intro g g' hgg
    refine Subtype.ext (Units.ext (Matrix.ext_iff_mulVec.mpr fun x => ?_))
    have hx := hgg x
    rw [unitarySU_smul_def h, unitarySU_smul_def h, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply] at hx
    exact hx
  rw [Subgroup.mem_centralizer_iff]
  by_cases hP1 : P = ⊥
  · intro g hg
    have hgP : g ∈ P := hg
    rw [hP1, Subgroup.mem_bot] at hgP
    rw [hgP, one_mul, mul_one]
  obtain ⟨t₁, ht₁P, u₁, hu₁P, ht₁, ht₁1, hu₁, hu₁1, hne⟩ :=
    exists_range_subOne_ne_of_isPerfect h hm hP hP1
  have haP' : ∀ y ∈ P, a * y * a⁻¹ ∈ P := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp haP y).mp hy
  obtain ⟨t₀, -, ht₀, ht₀1, hat₀⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_commute_involution_of_conj_transitive hr har
      haP' hrP ht₁P ht₁ ht₁1
      fun t htP ht ht1 =>
        exists_conj_of_range_subOne_ne h ht₁P hu₁P htP ht₁ ht₁1 hu₁ hu₁1 ht ht1 hne
  rcases scalar_or_homology_of_commute_involution h (hr.odd_of_ne_two hr2) har ht₀ ht₀1 hat₀ with
    ⟨c, hc⟩ | ⟨v, c, d, hv, hc0, hcd, hav, haW⟩
  · intro g _
    refine hext _ _ fun x => ?_
    rw [mul_smul, mul_smul, hc, hc, smul_comm]
  have hcent : ∀ t ∈ P, t ^ 2 = 1 → t ≠ 1 → ∀ x ∈ LinearMap.range (subOne t),
      stdHermForm h 3 v x = 0 := fun t htP ht ht1 =>
    range_subOne_perp_of_homology h hr har hrP haP hv hc0 hcd hav haW htP ht ht1
  have hsymm : ∀ x y : Fin 3 → K, stdHermForm h 3 x y = 0 → stdHermForm h 3 y x = 0 := by
    intro x y hxy
    rw [← (stdHermForm_isSymm h 3).eq x y, hxy, map_zero]
  obtain ⟨hL₁, -, -⟩ := involution_mem_isotropicTransvectionGroup h ht₁ ht₁1
  obtain ⟨hL₂, -, -⟩ := involution_mem_isotropicTransvectionGroup h hu₁ hu₁1
  obtain ⟨e₁, -, -, hLe₁⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_eq_span_of_mem_isotropicLines hL₁
  obtain ⟨e₂, -, -, hLe₂⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_eq_span_of_mem_isotropicLines hL₂
  have he₁L : e₁ ∈ LinearMap.range (subOne t₁) := hLe₁ ▸ Submodule.mem_span_singleton_self e₁
  have he₂L : e₂ ∈ LinearMap.range (subOne u₁) := hLe₂ ▸ Submodule.mem_span_singleton_self e₂
  have he₁v : stdHermForm h 3 e₁ v = 0 := hsymm _ _ (hcent t₁ ht₁P ht₁ ht₁1 e₁ he₁L)
  have he₂v : stdHermForm h 3 e₂ v = 0 := hsymm _ _ (hcent u₁ hu₁P hu₁ hu₁1 e₂ he₂L)
  have hperpL : ∀ (L : Submodule K (Fin 3 → K)) (e z : Fin 3 → K), L = K ∙ e →
      stdHermForm h 3 e z = 0 → z ∈ hermPerp h L := by
    intro L e z hLe hez
    rw [mem_hermPerp]
    intro y hy
    rw [hLe] at hy
    obtain ⟨κ, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [LinearMap.map_smulₛₗ₂, hez, smul_zero]
  have hvL : v ∉ LinearMap.range (subOne t₁) := fun hvL =>
    hv ((mem_isotropicLines.mp hL₁).2 v hvL)
  have hspan := hermPerp_eq_span_pair h hL₁ hLe₁ (hperpL _ _ _ hLe₁ he₁v) hvL
  have hzero : ∀ z : Fin 3 → K, stdHermForm h 3 e₁ z = 0 → stdHermForm h 3 e₂ z = 0 →
      stdHermForm h 3 v z = 0 → z = 0 := by
    intro z hz₁ hz₂ hzv
    have hz₁' := hperpL _ _ _ hLe₁ hz₁
    have hz₂' := hperpL _ _ _ hLe₂ hz₂
    rw [hspan] at hz₁'
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hz₁'
    have hβ : β = 0 := by
      have h1 : stdHermForm h 3 v z = β * stdHermForm h 3 v v := by
        rw [← hαβ, map_add, map_smul, map_smul, hsymm _ _ he₁v, smul_zero, zero_add,
          smul_eq_mul]
      rw [hzv] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right hv
    have hzL₁ : z ∈ LinearMap.range (subOne t₁) := by
      rw [← hαβ, hβ, zero_smul, add_zero, hLe₁]
      exact Submodule.smul_mem _ α (Submodule.mem_span_singleton_self e₁)
    have hin : z ∈ LinearMap.range (subOne t₁) ⊓ hermPerp h (LinearMap.range (subOne u₁)) :=
      Submodule.mem_inf.mpr ⟨hzL₁, hz₂'⟩
    rw [inf_hermPerp_eq_bot hL₁ hL₂ (Ne.symm hne)] at hin
    exact (Submodule.mem_bot K).mp hin
  have hgv : ∀ g ∈ P, g • v = (stdHermForm h 3 v (g • v) / stdHermForm h 3 v v) • v := by
    intro g hg
    have hperp : ∀ s ∈ P, s ^ 2 = 1 → s ≠ 1 → ∀ e ∈ LinearMap.range (subOne s),
        stdHermForm h 3 e (g • v) = 0 := by
      intro s hsP hs hs1 e he
      have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ P :=
        P.mul_mem (P.mul_mem (P.inv_mem hg) hsP) (P.inv_mem (P.inv_mem hg))
      have hs'2 : (g⁻¹ * s * g⁻¹⁻¹) ^ 2 = 1 := by
        rw [conj_pow, hs, mul_one, mul_inv_cancel]
      have hs'1 : g⁻¹ * s * g⁻¹⁻¹ ≠ 1 := by
        intro h1
        apply hs1
        rwa [conj_eq_one_iff] at h1
      have hmem : g⁻¹ • e ∈ LinearMap.range (subOne (g⁻¹ * s * g⁻¹⁻¹)) := by
        rw [range_subOne_conj h]
        exact Submodule.smul_mem_pointwise_smul e g⁻¹ _ he
      have h0 := hcent _ hs' hs'2 hs'1 _ hmem
      rw [← stdHermForm_smul_smul h g v (g⁻¹ • e), smul_inv_smul] at h0
      exact hsymm _ _ h0
    set κ : K := stdHermForm h 3 v (g • v) / stdHermForm h 3 v v with hκ
    have hz := hzero (g • v - κ • v)
      (by rw [map_sub, hperp t₁ ht₁P ht₁ ht₁1 e₁ he₁L, map_smul (stdHermForm h 3 e₁) κ v, he₁v,
        smul_zero, sub_zero])
      (by rw [map_sub, hperp u₁ hu₁P hu₁ hu₁1 e₂ he₂L, map_smul (stdHermForm h 3 e₂) κ v, he₂v,
        smul_zero, sub_zero])
      (by rw [map_sub, map_smul (stdHermForm h 3 v) κ v, smul_eq_mul, hκ, div_mul_cancel₀ _ hv,
        sub_self])
    exact sub_eq_zero.mp hz
  intro g hg
  refine hext _ _ fun x => ?_
  set β := stdHermForm h 3 v x / stdHermForm h 3 v v with hβ
  set κ := stdHermForm h 3 v (g • v) / stdHermForm h 3 v v with hκ
  have hxW : stdHermForm h 3 v (x - β • v) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, hβ, div_mul_cancel₀ _ hv, sub_self]
  have hgxW : stdHermForm h 3 v (g • (x - β • v)) = 0 := by
    have hg' := hgv g⁻¹ (P.inv_mem hg)
    have hrw : stdHermForm h 3 v (g • (x - β • v)) =
        stdHermForm h 3 (g⁻¹ • v) (x - β • v) := by
      rw [← stdHermForm_smul_smul h g⁻¹ v (g • (x - β • v)), inv_smul_smul]
    rw [hrw, hg', LinearMap.map_smulₛₗ₂, hxW, smul_zero]
  have hgv' : g • v = κ • v := hgv g hg
  have e1 : (g * a) • ((x - β • v) + β • v) = c • (g • (x - β • v)) + (β * d * κ) • v := by
    rw [mul_smul, smul_add, haW _ hxW, smul_comm a β v, hav, smul_add, smul_comm g c,
      smul_smul, smul_comm g (β * d) v, hgv', smul_smul]
  have e2 : (a * g) • ((x - β • v) + β • v) = c • (g • (x - β • v)) + (β * d * κ) • v := by
    rw [mul_smul, smul_add, smul_add, haW _ hgxW, smul_comm g β v, hgv', smul_smul,
      smul_comm a (β * κ) v, hav, smul_smul, mul_assoc, mul_comm κ d, ← mul_assoc]
  rw [← sub_add_cancel x (β • v), e1, e2]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

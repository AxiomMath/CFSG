module

public import CFSG.RankThree.PartOne.S9.Sylow.GlobalEndgame
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.RankThree.PartOne.FTL

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.Sec9B
open scoped commutatorElement

theorem commutator_commutator_le_of_rotate {G : Type*} [Group G] {N H₁ H₂ H₃ : Subgroup G}
    (hn₁ : H₁ ≤ normalizer (N : Set G)) (hn₂ : H₂ ≤ normalizer (N : Set G))
    (hn₃ : H₃ ≤ normalizer (N : Set G)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have hconj : ∀ g ∈ normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have key : ∀ w ∈ ⁅H₁, H₂⁆, w ∈ normalizer (N : Set G) ∧ ∀ z ∈ H₃, ⁅w, z⁆ ∈ N := by
    intro w hw
    have hw' : w ∈ Subgroup.closure {g : G | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g} := hw
    clear hw
    induction hw' using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hw
      refine ⟨?_, fun z hz => ?_⟩
      · have hxN := hn₁ hx
        have hyN := hn₂ hy
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN)
      · have hu : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ ∈ N := by
          rw [← commutatorElement_inv]
          exact N.inv_mem (h2 (Subgroup.commutator_mem_commutator
            (Subgroup.commutator_mem_commutator (H₃.inv_mem hz) (H₁.inv_mem hx)) hy))
        have hv : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ ∈ N := by
          rw [← commutatorElement_inv]
          exact N.inv_mem (h1 (Subgroup.commutator_mem_commutator
            (Subgroup.commutator_mem_commutator (H₂.inv_mem hy) hz) (H₁.inv_mem hx)))
        have hxz := mul_mem (hn₁ hx) (hn₃ hz)
        have hxy := mul_mem (hn₁ hx) (hn₂ hy)
        have e1 : ⁅⁅x, y⁆, z⁆ = (x * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ * (x * y)⁻¹) *
            (x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ * (x * z)⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e1]
        exact mul_mem (hconj _ hxy _ hv) (hconj _ hxz _ hu)
    | one => exact ⟨one_mem _, fun z _ => by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨mul_mem iha.1 ihb.1, fun z hz => ?_⟩
      have e1 : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (hconj _ iha.1 _ (ihb.2 z hz)) (iha.2 z hz)
    | inv a _ iha =>
      refine ⟨inv_mem iha.1, fun z hz => ?_⟩
      have e1 : ⁅a⁻¹, z⁆ = a⁻¹ * (⁅a, z⁆)⁻¹ * a := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      have := hconj _ (inv_mem iha.1) _ (N.inv_mem (iha.2 z hz))
      simpa using this
  exact Subgroup.commutator_le.mpr fun w hw z hz => (key w hw).2 z hz

theorem eq_bot_of_active {G : Type} [Group G] [Finite G] {R E Z : Subgroup G}
    (hZ : Z = ⁅R, E⁆) (hEE : ⁅E, E⁆ = E) (hR2 : IsPGroup 2 R) (hZs : Group.IsSolvable ↥Z)
    (hO2 : inSubgroup (pCore 2) Z = ⊥)
    (hact : ∀ s : ℕ, s.Prime → ⁅R, inSubgroup (pCore s) Z⁆ ≠ ⊥ →
      E ≤ Subgroup.centralizer (inSubgroup (pCore s) Z : Set G)) : Z = ⊥ := by
  classical
  set M : ℕ → Subgroup G := fun s => inSubgroup (pCore s) Z with hM
  have hRZ : R ≤ normalizer (Z : Set G) := by
    rw [hZ]; exact Subgroup.normalizer_commutator_ge_left R E
  have hEZ : E ≤ normalizer (Z : Set G) := by
    rw [hZ]; exact Subgroup.normalizer_commutator_ge_right R E
  have hMZ : ∀ s, M s ≤ Z := fun s => SteinbergBY.inSubgroup_pCore_le s Z
  have hRM : ∀ s, R ≤ normalizer (M s : Set G) := fun s r hr =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s Z (hRZ hr)
  have hEM : ∀ s, E ≤ normalizer (M s : Set G) := fun s e he =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s Z (hEZ he)
  have hZM : ∀ s, Z ≤ normalizer (M s : Set G) := fun s =>
    SteinbergBY.le_normalizer_inSubgroup_pCore s Z
  have hcentM : ∀ s : ℕ, s.Prime → Z ≤ Subgroup.centralizer (M s : Set G) := by
    intro s hs
    by_cases h : ⁅R, M s⁆ = ⊥
    · have hRC : R ≤ Subgroup.centralizer (M s : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have := commutator_le_centralizer_of_centralizes (hEM s) hRC
      rw [hZ, Subgroup.commutator_comm]
      exact this
    · have hEC : E ≤ Subgroup.centralizer (M s : Set G) := hact s hs h
      rw [hZ]
      exact commutator_le_centralizer_of_centralizes (hRM s) hEC
  have hFC : inSubgroup fittingSubgroup Z ≤ Subgroup.centralizer (Z : Set G) := by
    rw [inSubgroup, LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    have hsp : (s : ℕ).Prime := Nat.prime_of_mem_primeFactors s.2
    exact Subgroup.le_centralizer_iff.mp (hcentM s hsp)
  have hZC : Z ≤ Subgroup.centralizer (inSubgroup fittingSubgroup Z : Set G) :=
    Subgroup.le_centralizer_iff.mp hFC
  have hZF : Z ≤ inSubgroup fittingSubgroup Z := fun z hz =>
    inf_centralizer_fitting_le hZs ⟨hz, hZC hz⟩
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hFC (hZF hy)) x hx
  set Nact : Subgroup G := ⨆ s : {s : ℕ // s.Prime ∧ ⁅R, M s⁆ ≠ ⊥}, M s.1 with hNact
  set Nin : Subgroup G := ⨆ s : {s : ℕ // s.Prime ∧ ⁅R, M s⁆ = ⊥}, M s.1 with hNin
  have hNactZ : Nact ≤ Z := iSup_le fun s => hMZ s.1
  have hNinZ : Nin ≤ Z := iSup_le fun s => hMZ s.1
  have hFle : inSubgroup fittingSubgroup Z ≤ Nact ⊔ Nin := by
    rw [inSubgroup, LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    have hsp : (s : ℕ).Prime := Nat.prime_of_mem_primeFactors s.2
    by_cases hact' : ⁅R, M (s : ℕ)⁆ = ⊥
    · exact le_sup_of_le_right (le_iSup (fun t : {t : ℕ // t.Prime ∧ ⁅R, M t⁆ = ⊥} => M t.1)
        ⟨s, hsp, hact'⟩)
    · exact le_sup_of_le_left (le_iSup (fun t : {t : ℕ // t.Prime ∧ ⁅R, M t⁆ ≠ ⊥} => M t.1)
        ⟨s, hsp, hact'⟩)
  have hZN : Z ≤ normalizer (Nin : Set G) := fun g hg => mem_normalizer_iSup fun s => hZM s.1 hg
  have hRN : R ≤ normalizer (Nin : Set G) := fun g hg => mem_normalizer_iSup fun s => hRM s.1 hg
  have hEN : E ≤ normalizer (Nin : Set G) := fun g hg => mem_normalizer_iSup fun s => hEM s.1 hg
  have hNin_R : Nin ≤ Subgroup.centralizer (R : Set G) := iSup_le fun s =>
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp s.2.2)
  have hNact_E : Nact ≤ Subgroup.centralizer (E : Set G) := iSup_le fun s =>
    Subgroup.le_centralizer_iff.mp (hact s.1 s.2.1 s.2.2)
  have hconj : ∀ g ∈ normalizer (Nin : Set G), ∀ n ∈ Nin, g * n * g⁻¹ ∈ Nin := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have hsupN : Nact ⊔ Nin ≤ normalizer (Nin : Set G) :=
    sup_le (hNactZ.trans hZN) (hNinZ.trans hZN)
  have key : ∀ w ∈ Nact ⊔ Nin, ∀ e ∈ E, ⁅w, e⁆ ∈ Nin := by
    intro w hw e he
    rw [Subgroup.sup_eq_closure] at hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · have hc : e * x = x * e := Subgroup.mem_centralizer_iff.mp (hNact_E hx) e he
        have h1 : ⁅x, e⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc.symm
        rw [h1]
        exact one_mem _
      · rw [commutatorElement_def]
        have := hconj e (hEN he) x⁻¹ (inv_mem hx)
        have e1 : x * e * x⁻¹ * e⁻¹ = x * (e * x⁻¹ * e⁻¹) := by group
        rw [e1]
        exact mul_mem hx this
    | one => simp
    | mul a b ha hb iha ihb =>
      have haN : a ∈ normalizer (Nin : Set G) := hsupN (by rwa [Subgroup.sup_eq_closure])
      have e1 : ⁅a * b, e⁆ = (a * ⁅b, e⁆ * a⁻¹) * ⁅a, e⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (hconj a haN _ ihb) iha
    | inv a ha iha =>
      have haN : a ∈ normalizer (Nin : Set G) := hsupN (by rwa [Subgroup.sup_eq_closure])
      have e1 : ⁅a⁻¹, e⁆ = a⁻¹ * (⁅a, e⁆)⁻¹ * a := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      have := hconj a⁻¹ (inv_mem haN) _ (Nin.inv_mem iha)
      simpa using this
  have hZE : ⁅Z, E⁆ ≤ Nin := Subgroup.commutator_le.mpr fun z hz e he =>
    key z (hFle (hZF hz)) e he
  have hZNin : Z ≤ Nin := by
    have h1 : ⁅⁅E, R⁆, E⁆ ≤ Nin := by
      rw [Subgroup.commutator_comm E R, ← hZ]
      exact hZE
    have h2 : ⁅⁅R, E⁆, E⁆ ≤ Nin := by
      rw [← hZ]
      exact hZE
    have h3 := commutator_commutator_le_of_rotate (H₁ := E) (H₂ := E) (H₃ := R) hEN hEN hRN h1 h2
    rw [hEE, Subgroup.commutator_comm E R, ← hZ] at h3
    exact h3
  have hRZc : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r := fun r hr z hz =>
    (Subgroup.mem_centralizer_iff.mp (hNin_R (hZNin hz)) r hr)
  rw [hZ]
  refine eq_bot_iff.mpr (Subgroup.commutator_le.mpr fun r hr e he => ?_)
  rw [Subgroup.mem_bot]
  have hzZ : ⁅r, e⁆ ∈ Z := hZ ▸ Subgroup.commutator_mem_commutator hr he
  have hpow : ∀ n : ℕ, ⁅r ^ n, e⁆ = ⁅r, e⁆ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hz : ⁅r ^ n, e⁆ ∈ Z := hZ ▸ Subgroup.commutator_mem_commutator (R.pow_mem hr n) he
      have hcomm := hRZc r hr _ hz
      have e1 : ⁅r ^ (n + 1), e⁆ = (r * ⁅r ^ n, e⁆ * r⁻¹) * ⁅r, e⁆ := by
        simp only [commutatorElement_def, pow_succ']
        group
      have e2 : r * ⁅r ^ n, e⁆ * r⁻¹ = ⁅r ^ n, e⁆ := by
        rw [hcomm]; group
      rw [e1, e2, ih, pow_succ]
  obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
  have hrk : r ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hz2 : ⁅r, e⁆ ^ (2 ^ k) = 1 := by rw [← hpow, hrk]; simp
  set z : G := ⁅r, e⁆ with hz
  have hQ2 : IsPGroup 2 (Subgroup.zpowers z) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz2)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hQZ : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le.mpr hzZ
  have hZQ : Z ≤ normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      exact (Commute.zpow_left (show Commute z g from hZcomm z hzZ g hg) m).eq)
  have hle := SteinbergBY.le_inSubgroup_pCore hQ2 hQZ hZQ
  rw [hO2] at hle
  exact (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers z)))

end CFSG.RankThree.PartOne.FTL

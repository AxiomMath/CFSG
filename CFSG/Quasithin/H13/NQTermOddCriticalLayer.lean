module

public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.Quasithin.H13.NQTerm

open CFSG Subgroup
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

@[expose] def IsOddCriticalDetector (r : ℕ) {P : Type*} [Group P] (D : Subgroup P) : Prop :=
  D ≠ ⊥ ∧ D.Characteristic ∧ (∀ x ∈ D, x ^ r = 1) ∧
    ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ centralizer (D : Set P) ∧
    IsPGroup r (fixingSubgroup (MulAut P) (D : Set P))

variable (Γ) in
@[expose] def oddPrimeCoreSupport : Set ℕ :=
  {r | r.Prime ∧ r ≠ 2 ∧ pCore r Γ ≠ ⊥}

variable (Γ) in
@[expose] def oddCriticalLayer (D : (r : ℕ) → Subgroup (pCore r Γ)) : Subgroup Γ :=
  layer Γ ⊔ ⨆ r ∈ oddPrimeCoreSupport Γ, (D r).map (pCore r Γ).subtype

theorem oddCriticalLayer_characteristic (D : (r : ℕ) → Subgroup (pCore r Γ))
    (hD : ∀ r ∈ oddPrimeCoreSupport Γ, (D r).Characteristic) :
    (oddCriticalLayer Γ D).Characteristic := by
  have hE : (layer Γ).Characteristic := LocalCores.layer_characteristic
  have hDr : ∀ r ∈ oddPrimeCoreSupport Γ, ((D r).map (pCore r Γ).subtype).Characteristic :=
    fun r hr => by
      have := hD r hr
      infer_instance
  have := Subgroup.characteristic_biSup hDr
  unfold oddCriticalLayer
  infer_instance

theorem le_centralizer_of_isOddCriticalDetector {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {D : Subgroup (pCore r Γ)} (hD : IsOddCriticalDetector r D) {u : Γ} (hu2 : u ^ 2 = 1)
    (hu : ∀ d ∈ D, u * (d : Γ) * u⁻¹ = d) : pCore r Γ ≤ centralizer {u} := by
  obtain ⟨-, -, -, -, hfix⟩ := hD
  intro x hx
  let φ : MulAut (pCore r Γ) := MulAut.conjNormal u
  have hφ : φ ∈ fixingSubgroup (MulAut (pCore r Γ)) (D : Set (pCore r Γ)) := by
    rw [mem_fixingSubgroup_iff]
    intro d hd
    apply Subtype.ext
    rw [MulAut.smul_def, MulAut.conjNormal_apply]
    exact hu d hd
  obtain ⟨k, hk⟩ := hfix ⟨φ, hφ⟩
  have hk' : φ ^ (r ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : φ ^ 2 = 1 := by
    change (MulAut.conjNormal u) ^ 2 = 1
    rw [← map_pow, hu2, map_one]
  have hodd : Nat.Coprime 2 (r ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_left.2 (hr.eq_two_or_odd'.resolve_left hr2))
  have h1 : φ = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h2, hk'⟩
    rwa [hodd, pow_one] at this
  have hx' := congrArg (fun ψ : MulAut (pCore r Γ) => ((ψ ⟨x, hx⟩ : pCore r Γ) : Γ)) h1
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at hx'
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.mp hy]
  calc u * x = u * x * u⁻¹ * u := by group
    _ = x * u := by rw [hx']

theorem odd_critical_fitting_layer_detects_every_two_subgroup (Γ : Type*) [Group Γ] [Finite Γ]
    (h2 : pCore 2 Γ = ⊥) :
    (∀ r ∈ oddPrimeCoreSupport Γ, ∃ D : Subgroup (pCore r Γ), IsOddCriticalDetector r D) ∧
    ∀ D : (r : ℕ) → Subgroup (pCore r Γ),
      (∀ r ∈ oddPrimeCoreSupport Γ, IsOddCriticalDetector r (D r)) →
      (oddCriticalLayer Γ D).Characteristic ∧ pCore 2 (oddCriticalLayer Γ D) = ⊥ ∧
        Odd (Nat.card (centralizer (oddCriticalLayer Γ D : Set Γ))) := by
  refine ⟨fun r ⟨hr, hr2, hne⟩ => ?_, fun D hD => ?_⟩
  · have : Fact r.Prime := ⟨hr⟩
    have : Nontrivial (pCore r Γ) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    obtain ⟨D, hc, h1, hcomm, hexp, hfix⟩ :=
      CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hr2 (pCore_isPGroup (p := r) (G := Γ))
    exact ⟨D, h1, hc, hexp, hcomm, hfix⟩
  set Θ := oddCriticalLayer Γ D with hΘ
  have hchar : Θ.Characteristic :=
    oddCriticalLayer_characteristic D fun r hr => (hD r hr).2.1
  refine ⟨hchar, ?_, ?_⟩
  ·
    have hn : ((pCore 2 Θ).map Θ.subtype).Normal := inferInstance
    have hle : (pCore 2 Θ).map Θ.subtype ≤ pCore 2 Γ :=
      le_sSup ⟨hn, (pCore_isPGroup (p := 2) (G := Θ)).map Θ.subtype⟩
    rw [h2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Θ.subtype_injective] at hle
    exact hle
  ·
    have key : ∀ u ∈ centralizer (Θ : Set Γ), u ^ 2 = 1 → u = 1 := by
      intro u hu hu2
      have huΘ : ∀ x ∈ Θ, u * x = x * u := fun x hx => (mem_centralizer_iff.mp hu x hx).symm
      have hcore : ∀ r : ℕ, r.Prime → pCore r Γ ≤ centralizer {u} := by
        intro r hr
        by_cases hr2 : r = 2
        · subst hr2
          rw [h2]
          exact bot_le
        by_cases hne : pCore r Γ = ⊥
        · rw [hne]
          exact bot_le
        have hrS : r ∈ oddPrimeCoreSupport Γ := ⟨hr, hr2, hne⟩
        refine le_centralizer_of_isOddCriticalDetector hr hr2 (hD r hrS) hu2 fun d hd => ?_
        have hdΘ : (d : Γ) ∈ Θ := by
          refine Subgroup.mem_sup_right ?_
          exact Subgroup.mem_iSup_of_mem r (Subgroup.mem_iSup_of_mem hrS
            (Subgroup.mem_map_of_mem _ hd))
        rw [huΘ _ hdΘ]
        group
      have hF : fittingSubgroup Γ ≤ centralizer {u} := by
        rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
        exact iSup_le fun p => hcore p (Nat.prime_of_mem_primeFactors p.2)
      have hE : layer Γ ≤ centralizer {u} := by
        intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact huΘ x (Subgroup.mem_sup_left hx)
      have hFs : generalizedFitting Γ ≤ centralizer {u} := sup_le hF hE
      have huN : u ∈ centralizer (generalizedFitting Γ : Set Γ) := by
        rw [mem_centralizer_iff]
        intro x hx
        have := mem_centralizer_iff.mp (hFs hx) u rfl
        exact this.symm
      have huF := centralizer_generalizedFitting_le Γ huN
      set N := centralizer (generalizedFitting Γ : Set Γ) with hN
      have : (generalizedFitting Γ).Normal := (LocalCores.generalized_fitting_characteristic).2
      have hNn : N.Normal := inferInstance
      have : IsMulCommutative N := ⟨⟨fun a b => Subtype.ext
        (mem_centralizer_iff.mp a.2 b (centralizer_generalizedFitting_le Γ b.2)).symm⟩⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hx2 : (⟨u, huN⟩ : N) ^ 2 = 1 := Subtype.ext hu2
      have hU : IsPGroup 2 (zpowers (⟨u, huN⟩ : N)) := by
        rintro ⟨g, n, rfl⟩
        refine ⟨1, Subtype.ext ?_⟩
        change ((⟨u, huN⟩ : N) ^ n) ^ 2 ^ 1 = 1
        rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
      obtain ⟨P, hP⟩ := hU.exists_le_sylow
      have hPle := Sylow.map_le_pCore hNn (CommGroup.isNilpotent) 2 P
      rw [h2, le_bot_iff] at hPle
      have hmem : (u : Γ) ∈ (P : Subgroup N).map N.subtype :=
        ⟨⟨u, huN⟩, hP (mem_zpowers _), rfl⟩
      rw [hPle] at hmem
      exact hmem
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro hdvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (Θ : Set Γ)) 2 hdvd
    have hu2 : (u : Γ) ^ 2 = 1 := by
      have := pow_orderOf_eq_one u
      rw [hu] at this
      exact congrArg Subtype.val this
    have h1 := key u u.2 hu2
    have : u = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)

end CFSG.Quasithin.H13.NQTerm

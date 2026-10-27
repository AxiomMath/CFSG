module

public import CFSG.Quasithin.Background.P4InspEndAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut

public section

namespace CFSG.Quasithin.G11.P4InspEnd

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3

theorem p4inspend_a6_outer {K : Type*} [Group K] (e : K ≃* ↥(alternatingGroup (Fin 6)))
    (α : K ≃* K) (P : Sylow 2 K) (hαP : ∀ s ∈ P, α s ∈ P) (hα2 : ∀ s, α (α s) = s)
    (hord : ∀ s ∈ P, (s⁻¹ * α s) * (s⁻¹ * α s) = 1) :
    ∃ σ : Equiv.Perm (Fin 6), ∀ k : K,
      ((e (α k) : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) =
        σ * ((e k : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) * σ⁻¹ := by
  classical
  have hKfin : Finite K := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨ψ, hψ⟩ := exists_psl_equiv
  let φ : K ≃* ↥A6Models.psl29 := e.trans ψ.symm
  have hφe : ∀ k : K, e k = ψ (φ k) := fun k => by simp [φ]
  obtain ⟨b, hbA, hb⟩ := exists_aut_model φ α
  have hbb : b * b = 1 := by
    have hc : b * b ∈ A6Models.autA6 := A6Models.autA6.mul_mem hbA hbA
    refine centralizer_psl29 hc fun x hx => ?_
    set k := φ.symm ⟨x, hx⟩ with hkdef
    have hk : ((φ k : ↥A6Models.psl29) : P10) = x := by simp [hkdef]
    have h1 := hb k
    have h2 := hb (α k)
    rw [hα2 k, h1, hk] at h2
    calc b * b * x = (b * (b * x * b⁻¹) * b⁻¹) * (b * b) := by group
      _ = x * (b * b) := by rw [← h2]
  by_cases hs6 : b ∈ s6
  ·
    rcases s6_cases hs6 with hpsl | hpsl
    · refine ⟨((ψ ⟨b, hpsl⟩ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)), fun k => ?_⟩
      have h1 : φ (α k) = ⟨b, hpsl⟩ * φ k * ⟨b, hpsl⟩⁻¹ := Subtype.ext (hb k)
      rw [hφe, hφe, h1, map_mul, map_mul, map_inv]
      simp
    · have hy : b * A6Models.tFrob ∈ A6Models.psl29 := hpsl
      have hb' : b = (b * A6Models.tFrob) * A6Models.tFrob := by
        rw [mul_assoc, tFrob_mul_self, mul_one]
      refine ⟨((ψ ⟨b * A6Models.tFrob, hy⟩ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) *
        tau, fun k => ?_⟩
      obtain ⟨hmem, hrel⟩ := hψ ((φ k : ↥A6Models.psl29) : P10) (φ k).2
      have h1 : φ (α k) = ⟨b * A6Models.tFrob, hy⟩ * ⟨_, hmem⟩ * ⟨b * A6Models.tFrob, hy⟩⁻¹ := by
        apply Subtype.ext
        rw [hb k]
        show _ = (b * A6Models.tFrob) * (A6Models.tFrob * ((φ k : ↥A6Models.psl29) : P10) *
          A6Models.tFrob⁻¹) * (b * A6Models.tFrob)⁻¹
        calc b * ((φ k : ↥A6Models.psl29) : P10) * b⁻¹
            = ((b * A6Models.tFrob) * A6Models.tFrob) * ((φ k : ↥A6Models.psl29) : P10) *
                ((b * A6Models.tFrob) * A6Models.tFrob)⁻¹ := by rw [← hb']
          _ = _ := by group
      rw [hφe, hφe, h1, map_mul, map_mul, map_inv]
      have h2 : ((ψ ⟨_, hmem⟩ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) =
          tau * ((ψ ⟨((φ k : ↥A6Models.psl29) : P10), (φ k).2⟩ : ↥(alternatingGroup (Fin 6))) :
            Equiv.Perm (Fin 6)) * tau⁻¹ := hrel
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, h2]
      have h3 : (⟨((φ k : ↥A6Models.psl29) : P10), (φ k).2⟩ : ↥A6Models.psl29) = φ k := rfl
      rw [h3]
      group
  ·
    exfalso
    have hbne1 : b ≠ 1 := fun h => hs6 (h ▸ s6.one_mem)
    have hbpsl : b ∉ A6Models.psl29 := fun h => hs6 (psl29_le_s6 h)
    have hcard10 := card_psl29_centralizer_of_not_mem hbA hbb hbne1 hbpsl hs6
    let C : Subgroup K :=
      { carrier := {x | x ∈ P ∧ α x = x}
        mul_mem' := fun {a b} ha hb => ⟨P.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
        one_mem' := ⟨P.one_mem, map_one α⟩
        inv_mem' := fun {a} ha => ⟨P.inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
    have hC : ∀ x, x ∈ C ↔ x ∈ P ∧ α x = x := fun x => Iff.rfl
    have hsq := p4inspend_card_le_sq (P : Subgroup K) C α hC hαP hα2 hord
    have hKcard : Nat.card K = 360 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_alt6'
    have hP8 : Nat.card ↥(P : Subgroup K) = 8 := by
      have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [Sylow.card_eq_multiplicity, hKcard, Nat.factorization_def _ Nat.prime_two]
      have : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num
      rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
      norm_num
    have hCP : C ≤ (P : Subgroup K) := fun x hx => ((hC x).1 hx).1
    have hd8 : Nat.card ↥C ∣ 8 := hP8 ▸ Subgroup.card_dvd_of_le hCP
    have hd10 : Nat.card ↥C ∣ 10 := by
      let f : K →* P10 := A6Models.psl29.subtype.comp φ.toMonoidHom
      have hfinj : Function.Injective f := Subtype.val_injective.comp φ.injective
      have hle : C.map f ≤ A6Models.psl29 ⊓ Subgroup.centralizer ({b} : Set P10) := by
        rintro _ ⟨c, hc, rfl⟩
        refine ⟨(φ c).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hfc : α c = c := ((hC c).1 hc).2
        have h1 := hb c
        rw [hfc] at h1
        show ((φ c : ↥A6Models.psl29) : P10) * b = b * ((φ c : ↥A6Models.psl29) : P10)
        calc ((φ c : ↥A6Models.psl29) : P10) * b
            = (b * ((φ c : ↥A6Models.psl29) : P10) * b⁻¹) * b := by rw [← h1]
          _ = b * ((φ c : ↥A6Models.psl29) : P10) := by group
      have := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective hfinj, hcard10] at this
      exact this
    have hd2 : Nat.card ↥C ∣ 2 := by
      have := Nat.dvd_gcd hd8 hd10
      simpa using this
    have hC2 : Nat.card ↥C ≤ 2 := Nat.le_of_dvd (by norm_num) hd2
    rw [hP8] at hsq
    nlinarith

end CFSG.Quasithin.G11.P4InspEnd

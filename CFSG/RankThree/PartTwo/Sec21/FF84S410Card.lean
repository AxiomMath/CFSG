module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410Act
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmOrder
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2OmegaPts

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega

variable {G : Type} [Group G] {S : Subgroup G}

theorem range_psi0_le_O (e : ↥S ≃* Multiplicative F6)
    (hinv : ∀ (n : ↥(Nor S)) (v : F6), qMinus (psi0 e n v) = qMinus v) :
    (psi0 e).range ≤ TauCeti.QuadraticMap.orthogonalGroup qMinusForm := by
  rintro _ ⟨n, rfl⟩
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro m
  rw [qMinusForm_apply, qMinusForm_apply]
  exact hinv n m

theorem card_range_psi0_ge (e : ↥S ≃* Multiplicative F6) (v₀ : F6) (D : Set F6)
    (hD : 36 ≤ D.ncard) (hDo : ∀ v ∈ D, ∃ n : ↥(Nor S), psi0 e n v₀ = v)
    (K : Subgroup ↥(Nor S)) (hKfix : ∀ n ∈ K, psi0 e n v₀ = v₀)
    (hKker : ∀ n ∈ K, psi0 e n = 1 → n = 1) (hK : 720 ≤ Nat.card K) :
    25920 ≤ Nat.card (psi0 e).range := by
  classical
  set R := (psi0 e).range with hR
  have hprod := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup R v₀)
  rw [Nat.card_prod] at hprod
  have horb : 36 ≤ Nat.card (MulAction.orbit R v₀) := by
    rw [Nat.card_coe_set_eq]
    refine hD.trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    intro v hv
    obtain ⟨n, hn⟩ := hDo v hv
    rw [MulAction.mem_orbit_iff]
    exact ⟨⟨psi0 e n, n, rfl⟩, hn⟩
  have hstab : 720 ≤ Nat.card (MulAction.stabilizer R v₀) := by
    refine hK.trans (Nat.card_le_card_of_injective
      (fun n : K => (⟨⟨psi0 e n, n.1, rfl⟩, ?_⟩ : MulAction.stabilizer R v₀)) ?_)
    · rw [MulAction.mem_stabilizer_iff]
      exact hKfix n n.2
    · intro n m hnm
      have h1 : psi0 e n = psi0 e m := by
        have := congrArg (fun z : MulAction.stabilizer R v₀ => (z : R).1) hnm
        simpa using this
      have h2 : psi0 e ((n : ↥(Nor S))⁻¹ * m) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 := hKker _ (K.mul_mem (K.inv_mem n.2) m.2) h2
      exact Subtype.ext (inv_mul_eq_one.1 h3)
  calc 25920 = 36 * 720 := by norm_num
    _ ≤ Nat.card (MulAction.orbit R v₀) * Nat.card (MulAction.stabilizer R v₀) :=
        Nat.mul_le_mul horb hstab
    _ = Nat.card R := hprod

theorem eq_Omega_or_eq_O (H : Subgroup (F6 ≃ₗ[ZMod 2] F6))
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup qMinusForm) (hc : 25920 ≤ Nat.card H) :
    H = CFSG.Open.timmesfeldOmega qMinus ∨
      H = TauCeti.QuadraticMap.orthogonalGroup qMinusForm := by
  have hΩ := Om_ge_of_card H hH hc
  have hd1 : Nat.card (CFSG.Open.timmesfeldOmega qMinus) ∣ Nat.card H :=
    Subgroup.card_dvd_of_le hΩ
  have hd2 : Nat.card H ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup qMinusForm) :=
    Subgroup.card_dvd_of_le hH
  rw [card_timmesfeldOmega] at hd1
  rw [card_orthogonalGroup_qMinusForm] at hd2
  obtain ⟨k, hk⟩ := hd1
  obtain ⟨m, hm⟩ := hd2
  have hkm : k * m = 2 := by
    rw [hk] at hm
    nlinarith
  have hk2 : k ∣ 2 := ⟨m, hkm.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with h1 | h2
  · left
    refine (Subgroup.eq_of_le_of_card_ge hΩ ?_).symm
    rw [card_timmesfeldOmega, hk, h1]
  · right
    refine Subgroup.eq_of_le_of_card_ge hH ?_
    rw [card_orthogonalGroup_qMinusForm, hk, h2]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end

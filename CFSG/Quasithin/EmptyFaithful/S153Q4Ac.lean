module

public import CFSG.Quasithin.EmptyFaithful.S153Q4Ab

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q4A

set_option synthInstance.maxSize 4096 in
theorem alt6_involution : ∀ σ : Equiv.Perm (Fin 6), σ * σ = 1 → σ ≠ 1 → Equiv.Perm.sign σ = 1 →
    ∃ i j : Fin 6, i ≠ j ∧ σ i = i ∧ σ j = j := by
  decide +kernel

end Q4A

theorem hat_core_A {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w * w = 1)
    (hWc : Nat.card W = 2 ^ 6) {Γ Ah P : Subgroup (MulAut W)} {z : MulAut W} (hG : HatGrp Γ Ah z)
    (hfpf : ∀ w : W, z w = w → w = 1) {lab : Fin 6 → Subgroup W} (hO : OvalData Ah z lab)
    (hPΓ : P ≤ Γ) (hP2 : IsPGroup 2 ↥P) (hP1 : P ≠ ⊥) (V : Subgroup W) (hV16 : Nat.card ↥V = 16)
    (hPV : ∀ p ∈ P, ∀ v ∈ V, p v = v) :
    ∃ i j : Fin 6, i ≠ j ∧ V = lab i ⊔ lab j := by
  have hz3 := hG.z_cube
  obtain ⟨p, hpP, hpA, hp1⟩ := Q4A.exists_elation hWc hG hfpf hPΓ hP1 hV16 hPV
  have hpz : p * z = z * p := hG.z_central p hpA
  obtain ⟨k, hk⟩ := hP2 ⟨p, hpP⟩
  have hpk : p ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨hpp, hVeq⟩ := Q4A.elation_core hWc hW2 hz3 hfpf hpz hp1 hpk hV16 (hPV p hpP)
  obtain ⟨σ, hσA, hσ⟩ := hO.equiv p hpA
  have hp2apply : ∀ w : W, p (p w) = w := fun w => by
    have := congrArg (fun g : MulAut W => g w) hpp
    simpa [MulAut.mul_apply] using this
  have hσσ : σ * σ = 1 := by
    refine Equiv.ext fun k => ?_
    obtain ⟨w, hwk, hw1⟩ := Q4A.pt_exists_ne_one (hO.pt k)
    have h1 : p w ∈ lab (σ k) := hσ k w hwk
    have h2 : p (p w) ∈ lab (σ (σ k)) := hσ (σ k) (p w) h1
    rw [hp2apply] at h2
    by_contra hne
    have hne' : lab k ≠ lab (σ (σ k)) := fun h => hne (by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact (hO.inj h).symm)
    have hbot := Q4A.pt_inf_eq_bot hz3 hfpf (hO.pt k) (hO.pt (σ (σ k))) hne'
    have hmem : w ∈ lab k ⊓ lab (σ (σ k)) := Subgroup.mem_inf.2 ⟨hwk, h2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hw1 hmem
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    have hker : p ∈ Subgroup.zpowers z := hO.ker p hpA (fun k w hw => by simpa using hσ k w hw)
    apply hp1
    have h2 : orderOf p ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hpp)
    have h3 : orderOf p ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z) hker
      rw [Nat.card_zpowers] at this
      exact this.trans (orderOf_dvd_of_pow_eq_one hz3)
    have h1 : orderOf p ∣ Nat.gcd 2 3 := Nat.dvd_gcd h2 h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (by simpa using h1))
  obtain ⟨i, j, hij, hi, hj⟩ := Q4A.alt6_involution σ hσσ hσ1 (Equiv.Perm.mem_alternatingGroup.1 hσA)
  have hle : ∀ l : Fin 6, σ l = l → lab l ≤ V := by
    intro l hl x hx
    have hstab : ∀ x ∈ lab l, p x ∈ lab l := fun x hx => by simpa [hl] using hσ l x hx
    have hfix := Q4A.fix_of_stable hz3 hfpf hpz (hO.pt l) hstab (m := 2) (by omega)
      (by rw [pow_two]; exact hpp)
    rw [hVeq]
    exact Q4A.mem_fixSub.2 (hfix x hx)
  refine ⟨i, j, hij, ?_⟩
  have hne : lab i ≠ lab j := fun h => hij (hO.inj h)
  have hinf : lab i ⊓ lab j = ⊥ := Q4A.pt_inf_eq_bot hz3 hfpf (hO.pt i) (hO.pt j) hne
  have hcard := Q4A.card_mul_le_card_sup hinf
  rw [(Q4A.isPt_iff.1 (hO.pt i)).1, (Q4A.isPt_iff.1 (hO.pt j)).1] at hcard
  exact (Subgroup.eq_of_le_of_card_ge (sup_le (hle i hi) (hle j hj)) (by omega)).symm

end S153Q

end CFSG.Quasithin

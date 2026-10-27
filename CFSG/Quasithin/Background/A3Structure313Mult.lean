module

public import CFSG.Quasithin.Background.A3Structure313SL2
public import CFSG.Quasithin.Background.A3StructureFacts

public section

namespace CFSG.Quasithin.A313

open Matrix

theorem ker_eq_bot_of_quasisimple {X M : Type} [Group X] [Finite X] [Group M]
    (hmult : L2MultiplierFact) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hM : IsSL2 r M)
    (ρ : X →* M) (hρ : Function.Surjective ρ) (hq : CFSG.IsQuasisimple X) : ρ.ker = ⊥ := by
  have hMq := IsSL2.isQuasisimple hr hr5 hM
  have hcM : Nat.card (Subgroup.center M) = 2 := IsSL2.card_center hr (by omega) hM
  have hMcard : Nat.card M = r * (r ^ 2 - 1) := IsSL2.card_eq hr hM
  have hMnt : Nontrivial M := CFSG.LocalCores.isQuasisimple_nontrivial hMq
  have : Finite M := Finite.of_surjective ρ hρ
  have hkerZ : ρ.ker ≤ Subgroup.center X := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (N := ρ.ker) inferInstance with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne M
      obtain ⟨x, rfl⟩ := hρ a
      obtain ⟨y, rfl⟩ := hρ b
      apply hab
      have hx : x ∈ ρ.ker := by rw [h]; trivial
      have hy : y ∈ ρ.ker := by rw [h]; trivial
      rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
    · exact h
  have hZM : (Subgroup.center X).map ρ ≤ Subgroup.center M := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hρ y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  have hZne : (Subgroup.center X).map ρ ≠ ⊥ := by
    intro hbot
    have hle : Subgroup.center X ≤ ρ.ker := by
      intro z hz
      have : ρ z ∈ (Subgroup.center X).map ρ := ⟨z, hz, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hker : ρ.ker = Subgroup.center X := le_antisymm hkerZ hle
    have hsimple : IsSimpleGroup M := by
      have := hq.2.1
      let e : M ≃* X ⧸ Subgroup.center X :=
        (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm.trans
          (QuotientGroup.quotientMulEquivOfEq hker)
      exact e.isSimpleGroup
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
    · rw [h, Subgroup.card_bot] at hcM
      omega
    · rw [h, Subgroup.card_top, hMcard] at hcM
      have h1 : 2 ≤ r ^ 2 - 1 := by
        have : 25 ≤ r ^ 2 := by nlinarith
        omega
      have : r * 2 ≤ r * (r ^ 2 - 1) := Nat.mul_le_mul_left r h1
      omega
  have hZM' : (Subgroup.center X).map ρ = Subgroup.center M := by
    refine Subgroup.eq_of_le_of_card_ge hZM ?_
    rw [hcM]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hZne
  have hPSL : IsPSL 2 r 1 (X ⧸ Subgroup.center X) := by
    obtain ⟨eM⟩ := hM
    let f : X →* M ⧸ Subgroup.center M := (QuotientGroup.mk' (Subgroup.center M)).comp ρ
    have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hρ
    have hfker : f.ker = Subgroup.center X := by
      ext x
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' (Subgroup.center M) (ρ x) = 1) ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hZM']
      constructor
      · rintro ⟨z, hz, hzx⟩
        have hxz : x * z⁻¹ ∈ ρ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hzx, mul_inv_cancel]
        have : x = (x * z⁻¹) * z := by group
        rw [this]
        exact (Subgroup.center X).mul_mem (hkerZ hxz) hz
      · intro hx
        exact ⟨x, hx, rfl⟩
    let e1 : X ⧸ Subgroup.center X ≃* M ⧸ Subgroup.center M :=
      (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf)
    have hc : (Subgroup.center M).map (eM : M →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) =
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :=
      Subgroup.map_center_eq eM
    exact isPSL_two_of_mulEquiv hr hr5 (e1.trans (QuotientGroup.congr _ _ eM hc))
  have hZcard : Nat.card (Subgroup.center X) ≤ 2 :=
    hmult r hr hr5 X hq.1 (Subgroup.center X) le_rfl hPSL
  obtain ⟨⟨_, ⟨z, hz, rfl⟩⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZne
  have hzker : z ∉ ρ.ker := fun h => hz1 (Subtype.ext (MonoidHom.mem_ker.mp h))
  have hdvd : Nat.card ρ.ker ∣ Nat.card (Subgroup.center X) := Subgroup.card_dvd_of_le hkerZ
  have hne : Nat.card ρ.ker ≠ Nat.card (Subgroup.center X) := by
    intro h
    have : ρ.ker = Subgroup.center X := Subgroup.eq_of_le_of_card_ge hkerZ (le_of_eq h.symm)
    exact hzker (this ▸ hz)
  obtain ⟨k, hk⟩ := hdvd
  have hpos1 : 0 < Nat.card ρ.ker := Nat.card_pos
  have hpos2 : 0 < Nat.card (Subgroup.center X) := Nat.card_pos
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hk; omega
    · simp at hk; exact absurd hk.symm hne
    · omega
  have : 2 * Nat.card ρ.ker ≤ Nat.card (Subgroup.center X) := by
    rw [hk]
    calc 2 * Nat.card ρ.ker ≤ k * Nat.card ρ.ker := Nat.mul_le_mul_right _ hk2
      _ = Nat.card ρ.ker * k := mul_comm _ _
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

end CFSG.Quasithin.A313

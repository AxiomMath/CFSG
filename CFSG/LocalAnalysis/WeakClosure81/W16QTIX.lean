module

public import CFSG.LocalAnalysis.WeakClosure81.W16QKInput

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin
open CFSG.CGT.Timmesfeld75
open scoped Pointwise
open Subgroup

variable {X : Type} [Group X] [Finite X] {n : ℕ}

private theorem w16q_smul_centralizer (g : X) (R : Subgroup X) :
    (MulAut.conj g) • (Subgroup.centralizer (R : Set X)) =
      Subgroup.centralizer (((MulAut.conj g) • R : Subgroup X) : Set X) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, rfl⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g)
        (Subgroup.centralizer (R : Set X))).mp hx
    rw [Subgroup.mem_centralizer_iff] at hs ⊢
    intro y hy
    obtain ⟨r, hr, rfl⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists y (MulAut.conj g) R).mp hy
    have h := hs r hr
    simpa only [MulAut.smul_def, map_mul] using congrArg (MulAut.conj g) h
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    refine (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g)
      (Subgroup.centralizer (R : Set X))).mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h := hx ((MulAut.conj g) • r)
        (Subgroup.smul_mem_pointwise_smul r (MulAut.conj g) R hr)
      have h2 := congrArg (MulAut.conj g⁻¹) h
      rw [map_mul, map_mul] at h2
      have key : MulAut.conj g⁻¹ ((MulAut.conj g) • r) = r := by
        rw [MulAut.smul_def, MulAut.conj_apply, MulAut.conj_apply]
        group
      rw [key, MulAut.conj_apply, inv_inv] at h2
      exact h2
    · rw [MulAut.smul_def, MulAut.conj_apply]
      group

private theorem w16q_sylowCenter_smul (g : X) (R : Sylow 2 X) :
    sylowCenter (g • R) = CFSG.Quasithin.conjSubgroup (sylowCenter R) g⁻¹ := by
  have h : CFSG.Quasithin.conjSubgroup (sylowCenter R) g⁻¹ =
      (MulAut.conj g) • sylowCenter R := by
    ext x
    simp only [CFSG.Quasithin.mem_conjSubgroup_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, inv_inv]
  rw [h, sylowCenter, sylowCenter, Sylow.coe_subgroup_smul, Subgroup.smul_inf,
    w16q_smul_centralizer]

theorem exists_sylow_center_eq (hK : KGroup1616Input) (hn : 1 < n) (hX : IsU3Shape X n)
    {Y : Subgroup X} (hY : IsElemAbelian 2 Y) (hYc : Nat.card Y = 2 ^ n) :
    ∃ R : Sylow 2 X, Y = sylowCenter R := by
  obtain ⟨R, hR⟩ := hY.isPGroup.exists_le_sylow
  refine ⟨R, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · intro y hy
    have hyR : y ∈ (R : Subgroup X) := hR hy
    exact (hK.u3_omega n X hn hX R y hyR).1 (hY.mul_self_eq_one hy)
  · rw [hK.u3_center_card n X hn hX R, hYc]

theorem not_comm_of_ne_conj (hK : KGroup1616Input) (hn : 1 < n) (hX : IsU3Shape X n)
    {Y : Subgroup X} (hY : IsElemAbelian 2 Y) (hYc : Nat.card Y = 2 ^ n) {x y : X}
    (hxy : conjSubgroup Y x ≠ conjSubgroup Y y) :
    ¬ ∀ a ∈ conjSubgroup Y x, ∀ b ∈ conjSubgroup Y y, a * b = b * a := by
  intro hcomm
  have hAel : IsElemAbelian 2 (conjSubgroup Y x) :=
    hY.map (MulAut.conj x⁻¹).toMonoidHom
  have hBel : IsElemAbelian 2 (conjSubgroup Y y) :=
    hY.map (MulAut.conj y⁻¹).toMonoidHom
  have hsup : IsElemAbelian 2 (conjSubgroup Y x ⊔ conjSubgroup Y y) :=
    hAel.sup_of_commute hBel hcomm
  obtain ⟨R', hR'⟩ := hsup.isPGroup.exists_le_sylow
  have hAcard : Nat.card (conjSubgroup Y x) = 2 ^ n := by
    rw [CFSG.Quasithin.conjSubgroup,
      Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hYc]
  have hleA : conjSubgroup Y x ≤ sylowCenter R' := by
    intro a ha
    have haR' : a ∈ (R' : Subgroup X) := hR' (Subgroup.mem_sup_left ha)
    exact (hK.u3_omega n X hn hX R' a haR').1 (hAel.mul_self_eq_one ha)
  have hAeq : conjSubgroup Y x = sylowCenter R' :=
    Subgroup.eq_of_le_of_card_ge hleA (by rw [hK.u3_center_card n X hn hX R', hAcard])
  have hBcard : Nat.card (conjSubgroup Y y) = 2 ^ n := by
    rw [CFSG.Quasithin.conjSubgroup,
      Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective, hYc]
  have hleB : conjSubgroup Y y ≤ sylowCenter R' := by
    intro b hb
    have hbR' : b ∈ (R' : Subgroup X) := hR' (Subgroup.mem_sup_right hb)
    exact (hK.u3_omega n X hn hX R' b hbR').1 (hBel.mul_self_eq_one hb)
  have hBeq : conjSubgroup Y y = sylowCenter R' :=
    Subgroup.eq_of_le_of_card_ge hleB (by rw [hK.u3_center_card n X hn hX R', hBcard])
  exact hxy (hAeq.trans hBeq.symm)

theorem ncard_conj (hK : KGroup1616Input) (hn : 1 < n) (hX : IsU3Shape X n)
    {Y : Subgroup X} (hY : IsElemAbelian 2 Y) (hYc : Nat.card Y = 2 ^ n) :
    Set.ncard {A : Subgroup X | ∃ x : X, A = conjSubgroup Y x} = (2 ^ n) ^ 3 + 1 := by
  obtain ⟨R₀, hR₀⟩ := exists_sylow_center_eq hK hn hX hY hYc
  have hf_inj : Function.Injective (fun R : Sylow 2 X => sylowCenter R) := by
    intro R R' h
    change sylowCenter R = sylowCenter R' at h
    by_contra hne
    have hti := hK.u3_sylow_ti n X hn hX R R' hne
    have hle : sylowCenter R ≤ (R : Subgroup X) ⊓ (R' : Subgroup X) := by
      refine le_inf inf_le_left ?_
      rw [h]
      exact inf_le_left
    rw [hti] at hle
    have hcard : Nat.card (sylowCenter R) = 2 ^ n := hK.u3_center_card n X hn hX R
    have hcard1 : Nat.card (sylowCenter R) = 1 := by
      rw [le_antisymm hle bot_le, Subgroup.card_bot]
    have hgt : 1 < 2 ^ n := by
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrange : Set.range (fun R : Sylow 2 X => sylowCenter R) =
      {A : Subgroup X | ∃ x : X, A = conjSubgroup Y x} := by
    ext A
    rw [Set.mem_range]
    constructor
    · rintro ⟨R, rfl⟩
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R₀ R
      refine ⟨g⁻¹, ?_⟩
      rw [← hg, w16q_sylowCenter_smul, ← hR₀]
    · rintro ⟨x, rfl⟩
      refine ⟨x⁻¹ • R₀, ?_⟩
      rw [w16q_sylowCenter_smul, ← hR₀, inv_inv]
  rw [← hrange]
  exact (Set.ncard_range_of_injective hf_inj).trans (hK.u3_card_sylow n X hn hX)

theorem isL2Pair_conj (hK : KGroup1616Input) (hn : 1 < n) (hX : IsU3Shape X n)
    {Y : Subgroup X} (hY : IsElemAbelian 2 Y) (hYc : Nat.card Y = 2 ^ n) {x y : X}
    (hxy : conjSubgroup Y x ≠ conjSubgroup Y y) :
    IsL2Pair ↥(conjSubgroup Y x ⊔ conjSubgroup Y y)
      ((conjSubgroup Y x).subgroupOf (conjSubgroup Y x ⊔ conjSubgroup Y y)) (2 ^ n) := by
  obtain ⟨R₀, hR₀⟩ := exists_sylow_center_eq hK hn hX hY hYc
  have hA : conjSubgroup Y x = sylowCenter (x⁻¹ • R₀) := by
    rw [w16q_sylowCenter_smul, ← hR₀, inv_inv]
  have hB : conjSubgroup Y y = sylowCenter (y⁻¹ • R₀) := by
    rw [w16q_sylowCenter_smul, ← hR₀, inv_inv]
  have hne : x⁻¹ • R₀ ≠ y⁻¹ • R₀ := by
    intro h
    exact hxy (hA.trans (h.symm ▸ hB.symm))
  have hp := hK.u3_pair n X hn hX (x⁻¹ • R₀) (y⁻¹ • R₀) hne
  rw [hA, hB]
  exact hp

theorem sz_not_comm (hK : KGroup1616Input) {m : ℕ} (hm : 1 < m) {Z : Type} [Group Z]
    (hZ : CFSG.Quasithin.IsSz m Z) : ∃ a b : Z, a * b ≠ b * a := by
  by_contra h
  have hcomm : ∀ a b : Z, a * b = b * a := by
    intro a b
    by_contra hne
    exact h ⟨a, b, hne⟩
  letI : CommGroup Z := { ‹Group Z› with mul_comm := hcomm }
  haveI : IsSimpleGroup Z := hK.sz_simple m Z hm hZ
  have hprime : (Nat.card Z).Prime := IsSimpleGroup.prime_card
  have hcard := hK.sz_card m Z hm hZ
  rw [hcard] at hprime
  have hm2 : 2 ≤ m := by omega
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have h1 : (2 ^ m) ^ 2 * (2 ^ m - 1) ≠ 1 := by
    have hlt : 1 < (2 ^ m) ^ 2 * (2 ^ m - 1) := by
      rw [Nat.one_lt_mul_iff]
      refine ⟨by positivity, by omega, Or.inl ?_⟩
      have : 2 ≤ 2 ^ m := by omega
      nlinarith
    omega
  have h2 : (2 ^ m) ^ 2 + 1 ≠ 1 := by
    have : 0 < (2 ^ m) ^ 2 := by positivity
    omega
  exact (Nat.not_prime_of_mul_eq rfl h1 h2) hprime

end CFSG.LocalAnalysis.WeakClosure81

end

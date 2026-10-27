module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltGrid

public section

namespace CFSG.StandardType

open Equiv Equiv.Perm

section Orbit

variable {V : Type} [DecidableEq V] [Fintype V] (E : Subgroup (Perm V))

open Classical in
@[expose] noncomputable def ggOrb (ω : V) : Finset V :=
  Finset.univ.filter fun v => ∃ g ∈ E, g ω = v

@[expose] def ggStab (ω : V) : Subgroup (Perm V) :=
  E ⊓ MulAction.stabilizer (Perm V) ω

variable {E}

theorem ggMem_orb {ω v : V} : v ∈ ggOrb E ω ↔ ∃ g ∈ E, g ω = v := by
  classical
  unfold ggOrb
  simp

theorem ggMem_orb_self (ω : V) : ω ∈ ggOrb E ω :=
  ggMem_orb.mpr ⟨1, E.one_mem, rfl⟩

omit [DecidableEq V] [Fintype V] in
theorem ggMem_stab {ω : V} {x : Perm V} : x ∈ ggStab E ω ↔ x ∈ E ∧ x ω = ω := by
  unfold ggStab
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Perm.smul_def]

theorem ggOrb_symm {ω v : V} (h : v ∈ ggOrb E ω) : ω ∈ ggOrb E v := by
  obtain ⟨g, hg, rfl⟩ := ggMem_orb.mp h
  exact ggMem_orb.mpr ⟨g⁻¹, E.inv_mem hg, by simp⟩

theorem ggOrb_trans {ω v w : V} (h1 : v ∈ ggOrb E ω) (h2 : w ∈ ggOrb E v) : w ∈ ggOrb E ω := by
  obtain ⟨g, hg, rfl⟩ := ggMem_orb.mp h1
  obtain ⟨h, hh, rfl⟩ := ggMem_orb.mp h2
  exact ggMem_orb.mpr ⟨h * g, E.mul_mem hh hg, rfl⟩

theorem ggOrb_eq_of_mem {ω v : V} (h : v ∈ ggOrb E ω) : ggOrb E v = ggOrb E ω := by
  ext w
  exact ⟨fun hw => ggOrb_trans h hw, fun hw => ggOrb_trans (ggOrb_symm h) hw⟩

theorem ggOrb_eq_or_disjoint (ω v : V) : ggOrb E ω = ggOrb E v ∨ Disjoint (ggOrb E ω) (ggOrb E v) := by
  by_cases h : ∃ w, w ∈ ggOrb E ω ∧ w ∈ ggOrb E v
  · obtain ⟨w, h1, h2⟩ := h
    exact Or.inl ((ggOrb_eq_of_mem h1).symm.trans (ggOrb_eq_of_mem h2))
  · push Not at h
    exact Or.inr (Finset.disjoint_left.mpr h)

theorem ggFix_orb_of_mem_stab (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {ω : V} {x : Perm V}
    (hx : x ∈ ggStab E ω) {v : V} (hv : v ∈ ggOrb E ω) : x v = v := by
  obtain ⟨hxE, hxω⟩ := ggMem_stab.mp hx
  obtain ⟨g, hg, rfl⟩ := ggMem_orb.mp hv
  have h := congrArg (fun f : Perm V => f ω) (hEab x hxE g hg)
  simp only [Perm.coe_mul, Function.comp_apply] at h
  rw [h, hxω]

theorem ggStab_eq_of_mem (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {ω v : V}
    (hv : v ∈ ggOrb E ω) : ggStab E v = ggStab E ω := by
  ext x
  constructor
  · intro hx
    exact ggMem_stab.mpr ⟨(ggMem_stab.mp hx).1,
      ggFix_orb_of_mem_stab hEab hx (ggOrb_symm hv)⟩
  · intro hx
    exact ggMem_stab.mpr ⟨(ggMem_stab.mp hx).1, ggFix_orb_of_mem_stab hEab hx hv⟩

omit [DecidableEq V] [Fintype V] in
theorem ggCard_stab_dvd (ω : V) : Nat.card (ggStab E ω) ∣ Nat.card E :=
  Subgroup.card_dvd_of_le inf_le_left

theorem ggCard_orb_mul_stab (ω : V) : (ggOrb E ω).card * Nat.card (ggStab E ω) = Nat.card E := by
  classical
  have h1 := MulAction.index_stabilizer (↥E) ω
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer (↥E) ω)
  have horb : (MulAction.orbit (↥E) ω).ncard = (ggOrb E ω).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp only [MulAction.mem_orbit_iff, Finset.coe_filter, ggOrb, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq, Subtype.exists, Subgroup.mk_smul, Perm.smul_def, exists_prop]
  have hstab : Nat.card (MulAction.stabilizer (↥E) ω) = Nat.card (ggStab E ω) := by
    refine Nat.card_congr ⟨fun x => ⟨(x : E), ggMem_stab.mpr ⟨(x : E).2, ?_⟩⟩,
      fun y => ⟨⟨y, (ggMem_stab.mp y.2).1⟩, ?_⟩, fun x => rfl, fun y => rfl⟩
    · have := x.2
      rw [MulAction.mem_stabilizer_iff] at this
      exact this
    · rw [MulAction.mem_stabilizer_iff]
      exact (ggMem_stab.mp y.2).2
  rw [← horb, ← h1, ← hstab, mul_comm]
  exact h2

end Orbit

section Regular

variable {V : Type} [DecidableEq V] [Fintype V] {E : Subgroup (Perm V)}

omit [DecidableEq V] [Fintype V] in
theorem ggMem_zpowers_pow {p : ℕ} (hp : p.Prime) {v : Perm V} (hvp : v ^ p = 1) {m : ℕ}
    (hm : ¬ p ∣ m) : v ∈ Subgroup.zpowers (v ^ m) := by
  have hcop : Nat.Coprime m p := Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr hm)
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine Subgroup.mem_zpowers_iff.mpr ⟨(c : ℤ), ?_⟩
  rw [zpow_natCast, ← pow_mul, ggPow_eq_pow_mod hvp, hc, pow_one]

omit [DecidableEq V] in
theorem ggExists_mem_notMem_zpowers {p : ℕ} (hp : p.Prime) (hEcard : Nat.card E = p ^ 2)
    {x : Perm V} (hxp : x ^ p = 1) : ∃ v ∈ E, v ∉ Subgroup.zpowers x := by
  by_contra h
  push Not at h
  have hle : E ≤ Subgroup.zpowers x := h
  have hcard := Subgroup.card_le_of_le hle
  rw [hEcard, Nat.card_zpowers] at hcard
  have hord : orderOf x ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hxp)
  have h2 := hp.two_le
  nlinarith

omit [DecidableEq V] in
theorem ggExists_grid_of_regular {p : ℕ} [Fact p.Prime] (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hEp : ∀ x ∈ E, x ^ p = 1) (hEcard : Nat.card E = p ^ 2) {ω : V}
    (hω : Nat.card (ggStab E ω) = 1) :
    ∃ x ∈ E, x ≠ 1 ∧ ∃ β : ZMod p → V, (∀ i, x (β i) ≠ β i) ∧
      ∀ i i' (k : ℕ), (x ^ k) (β i) = β i' → i = i' := by
  have hp : p.Prime := Fact.out
  have hstab : ∀ y ∈ E, y ω = ω → y = 1 := by
    intro y hy hyω
    have hmem : y ∈ ggStab E ω := ggMem_stab.mpr ⟨hy, hyω⟩
    rw [Subgroup.card_eq_one.mp hω] at hmem
    exact hmem
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
    rw [hbot, Subgroup.card_bot] at hEcard
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨v, hvE, hvx⟩ := ggExists_mem_notMem_zpowers hp hEcard (hEp x hxE)
  have hvp : v ^ p = 1 := hEp v hvE
  have hcomm : Commute v x := hEab v hvE x hxE
  refine ⟨x, hxE, hx1, fun i => (v ^ i.val) ω, ?_, ?_⟩
  · intro i h
    apply hx1
    apply hstab x hxE
    have hc := congrArg (fun f : Perm V => f ω) ((hcomm.pow_left i.val).eq)
    simp only [Perm.coe_mul, Function.comp_apply] at hc
    apply (v ^ i.val).injective
    rw [hc]
    exact h
  · intro i i' k h
    have hi := ZMod.val_lt i
    have hi' := ZMod.val_lt i'
    have hyω : (v ^ (p - i'.val) * x ^ k * v ^ i.val) ω = ω := by
      simp only [Perm.coe_mul, Function.comp_apply]
      rw [h, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hi'.le, hvp, Perm.one_apply]
    have hyE : v ^ (p - i'.val) * x ^ k * v ^ i.val ∈ E :=
      E.mul_mem (E.mul_mem (E.pow_mem hvE _) (E.pow_mem hxE _)) (E.pow_mem hvE _)
    have hy1 := hstab _ hyE hyω
    have hy' : x ^ k * v ^ (p - i'.val + i.val) = 1 := by
      rw [← hy1, pow_add, ← mul_assoc, ((hcomm.pow_pow (p - i'.val) k).eq)]
    have hmem : v ^ (p - i'.val + i.val) ∈ Subgroup.zpowers x := by
      have : v ^ (p - i'.val + i.val) = (x ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hy'
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k)
    have hdvd : p ∣ p - i'.val + i.val := by
      by_contra hnd
      exact hvx ((Subgroup.zpowers_le.mpr hmem) (ggMem_zpowers_pow hp hvp hnd))
    obtain ⟨t, ht⟩ := hdvd
    have hval : i.val = i'.val := by
      rcases t with _ | _ | t
      · simp at ht
        omega
      · simp at ht
        omega
      · have h2 : p * 2 ≤ p * (t + 1 + 1) := Nat.mul_le_mul_left p (by omega)
        omega
    exact ZMod.val_injective p hval

end Regular

end CFSG.StandardType

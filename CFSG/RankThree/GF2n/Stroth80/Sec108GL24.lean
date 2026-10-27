module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Tactic.Abel
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec108

open MulAction
open scoped Nat

private abbrev tauCyclic {C : Type} [Group C] (τ : MulAut C) : Subgroup (MulAut C) :=
  Subgroup.zpowers τ

private abbrev Nonidentity (C : Type) [Group C] : Type := {c : C // c ≠ 1}

private instance instMulActionMulAutNonidentity {C : Type} [Group C] :
    MulAction (MulAut C) (Nonidentity C) where
  smul σ x := ⟨σ x, by
    rintro hx
    have h : σ.symm (σ x) = σ.symm 1 := congrArg σ.symm hx
    exact x.2 (by simpa using h)⟩
  one_smul x := Subtype.ext rfl
  mul_smul a b x := Subtype.ext (by
    change (a * b : MulAut C) x = a (b x)
    rw [MulAut.mul_apply])

private abbrev OrbitQuotient {C : Type} [Group C] (τ : MulAut C) : Type :=
  Quotient (MulAction.orbitRel (tauCyclic τ) (Nonidentity C))

private lemma tau_apply_three {C : Type} [Group C] {τ : MulAut C} (hτ3 : τ ^ 3 = 1)
    (c : C) : τ (τ (τ c)) = c := by
  have h := congrArg (fun e : MulAut C => e c) hτ3
  simpa [pow_succ, MulAut.mul_apply] using h

private lemma tau_apply_ne_self {C : Type} [Group C] {τ : MulAut C}
    (hτ : ∀ c : C, τ c = c → c = 1) {c : C} (hc : c ≠ 1) : τ c ≠ c :=
  fun h => hc (hτ c h)

private lemma tau_sq_apply_ne_self {C : Type} [Group C] {τ : MulAut C} (hτ3 : τ ^ 3 = 1)
    (hτ : ∀ c : C, τ c = c → c = 1) {c : C} (hc : c ≠ 1) : τ (τ c) ≠ c := by
  intro h
  have h3 := tau_apply_three hτ3 c
  rw [h] at h3
  exact tau_apply_ne_self hτ hc h3

private lemma tau_apply_ne_tau_sq {C : Type} [Group C] {τ : MulAut C}
    (hτ : ∀ c : C, τ c = c → c = 1) {c : C} (hc : c ≠ 1) : τ c ≠ τ (τ c) := by
  intro h
  exact tau_apply_ne_self hτ hc (τ.injective h).symm

private lemma mem_tauCyclic_cases {C : Type} [Group C] {τ : MulAut C} (hτ3 : τ ^ 3 = 1)
    (h : tauCyclic τ) :
    h = 1 ∨ h = (⟨τ, Subgroup.mem_zpowers τ⟩ : tauCyclic τ) ∨
      h = (⟨τ ^ 2, pow_mem (Subgroup.mem_zpowers τ) 2⟩ : tauCyclic τ) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hEq : (h : MulAut C) = τ ^ n := hn.symm
  have hmod : τ ^ n = τ ^ (n % 3 : ℤ) :=
    zpow_eq_zpow_emod' (x := τ) n (n := 3) hτ3
  rw [hmod] at hEq
  have hn0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hn3 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  have hn' : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hn' with h | h | h
  · left; apply Subtype.ext; rw [hEq, h]; simp
  · right; left; apply Subtype.ext; rw [hEq, h]; simp [zpow_natCast]
  · right; right; apply Subtype.ext; rw [hEq, h]; simp [zpow_natCast]

private lemma zmod3_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  have ha : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 := by
    have h := ZMod.val_lt a
    omega
  rcases ha with h | h | h
  · left; exact (ZMod.val_eq_zero a).mp h
  · right; left; exact (ZMod.val_eq_one (n := 3) (by norm_num) a).mp h
  · right; right
    apply ZMod.val_injective 3
    simpa [h, ZMod.val_two_eq_two_mod]

private lemma tau_orbit_eq {C : Type} [Group C] {τ : MulAut C} (hτ3 : τ ^ 3 = 1)
    (hτ : ∀ c : C, τ c = c → c = 1) {c : C} (hc : c ≠ 1) :
    (MulAction.orbit (tauCyclic τ) c : Set C) = ({c, τ c, τ (τ c)} : Set C) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hx
    rw [Subgroup.smul_def, MulAut.smul_def] at hh
    rcases mem_tauCyclic_cases hτ3 h with h1 | hτ' | hτ2
    · have h1' : (h : MulAut C) = 1 := congrArg Subtype.val h1
      rw [← hh, h1']; simp
    · have hτ'' : (h : MulAut C) = τ := congrArg Subtype.val hτ'
      rw [← hh, hτ'']; simp
    · have hτ2' : (h : MulAut C) = τ ^ 2 := congrArg Subtype.val hτ2
      rw [← hh, hτ2', pow_two, MulAut.mul_apply]; simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact MulAction.mem_orbit_self c
    · rw [hx]
      exact MulAction.mem_orbit_iff.mpr ⟨⟨τ, Subgroup.mem_zpowers τ⟩, by
        rw [Subgroup.smul_def, MulAut.smul_def]⟩
    · rw [hx]
      refine MulAction.mem_orbit_iff.mpr
        ⟨⟨τ ^ 2, pow_mem (Subgroup.mem_zpowers τ) 2⟩, ?_⟩
      change (τ ^ 2 : MulAut C) c = τ (τ c)
      rw [pow_two, MulAut.mul_apply]

private lemma tau_orbit_set_ncard {C : Type} [Group C] {τ : MulAut C} (hτ3 : τ ^ 3 = 1)
    (hτ : ∀ c : C, τ c = c → c = 1) {c : C} (hc : c ≠ 1) :
    ({c, τ c, τ (τ c)} : Set C).ncard = 3 := by
  classical
  have h1 : c ∉ ({τ c, τ (τ c)} : Set C) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨(tau_apply_ne_self hτ hc).symm, (tau_sq_apply_ne_self hτ3 hτ hc).symm⟩
  have h2 : τ c ∉ ({τ (τ c)} : Set C) := by
    simp only [Set.mem_singleton_iff]
    exact tau_apply_ne_tau_sq hτ hc
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]

private lemma card_tau_orbit {C : Type} [Group C] {τ : MulAut C} (hτ3 : τ ^ 3 = 1)
    (hτ : ∀ c : C, τ c = c → c = 1) {c : C} (hc : c ≠ 1) :
    Nat.card (MulAction.orbit (tauCyclic τ) c) = 3 := by
  rw [Nat.card_coe_set_eq, tau_orbit_eq hτ3 hτ hc]
  exact tau_orbit_set_ncard hτ3 hτ hc

private lemma orbit_subtype_val_image {C : Type} [Group C] {τ : MulAut C}
    (x : Nonidentity C) :
    Subtype.val '' (MulAction.orbit (tauCyclic τ) x : Set (Nonidentity C)) =
      (MulAction.orbit (tauCyclic τ) (x : C) : Set C) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hz
    refine MulAction.mem_orbit_iff.mpr ⟨g, ?_⟩
    have hval := congrArg Subtype.val hg
    change (g : MulAut C) (x : C) = (z : C) at hval
    exact hval
  · intro hy
    have hyne : y ≠ 1 := by
      intro hy1
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
      have hx1 : (x : C) = 1 := by
        have := congrArg (fun z => g⁻¹ • z) hg
        simpa [hy1] using this
      exact x.2 hx1
    refine ⟨⟨y, hyne⟩, ?_, rfl⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    refine MulAction.mem_orbit_iff.mpr ⟨g, ?_⟩
    apply Subtype.ext
    change (g : MulAut C) (x : C) = y
    exact hg

private lemma card_tau_orbit_subtype {C : Type} [Group C] {τ : MulAut C} (hτ3 : τ ^ 3 = 1)
    (hτ : ∀ c : C, τ c = c → c = 1) (x : Nonidentity C) :
    Nat.card (MulAction.orbit (tauCyclic τ) x) = 3 := by
  calc
    Nat.card (MulAction.orbit (tauCyclic τ) x) =
        (MulAction.orbit (tauCyclic τ) x : Set (Nonidentity C)).ncard :=
      Nat.card_coe_set_eq _
    _ = (Subtype.val '' (MulAction.orbit (tauCyclic τ) x : Set (Nonidentity C))).ncard :=
      (Set.ncard_image_of_injective (s := (MulAction.orbit (tauCyclic τ) x :
        Set (Nonidentity C))) Subtype.val_injective).symm
    _ = (MulAction.orbit (tauCyclic τ) (x : C) : Set C).ncard := by
      rw [orbit_subtype_val_image]
    _ = Nat.card (MulAction.orbit (tauCyclic τ) (x : C)) := (Nat.card_coe_set_eq _).symm
    _ = 3 := card_tau_orbit hτ3 hτ x.2

private lemma card_nonidentity_le_fifteen {C : Type} [Group C] [Finite C]
    (hC : Nat.card C ≤ 16) : Nat.card (Nonidentity C) ≤ 15 := by
  classical
  have hsum : Nat.card ({c : C // c = 1} ⊕ Nonidentity C) = Nat.card C :=
    Nat.card_congr (Equiv.sumCompl (fun c : C => c = 1))
  rw [Nat.card_sum, Nat.card_unique] at hsum
  omega

private lemma card_orbitQuotient_le_five {C : Type} [Group C] [Finite C]
    {τ : MulAut C} (hC : Nat.card C ≤ 16) (hτ3 : τ ^ 3 = 1)
    (hτ : ∀ c : C, τ c = c → c = 1) : Nat.card (OrbitQuotient τ) ≤ 5 := by
  classical
  let H : Subgroup (MulAut C) := tauCyclic τ
  let α := Nonidentity C
  have hα : Nat.card α ≤ 15 := card_nonidentity_le_fifteen hC
  letI : Fintype (OrbitQuotient τ) := Fintype.ofFinite _
  have hdecomp : α ≃ Σ ω : OrbitQuotient τ, MulAction.orbit H ω.out :=
    MulAction.selfEquivSigmaOrbits H α
  have hcard : Nat.card α = ∑ ω : OrbitQuotient τ, Nat.card (MulAction.orbit H ω.out) := by
    rw [Nat.card_congr hdecomp]
    exact Nat.card_sigma
  have horb : ∀ ω : OrbitQuotient τ, Nat.card (MulAction.orbit H ω.out) = 3 := by
    intro ω
    simpa [H] using card_tau_orbit_subtype hτ3 hτ ω.out
  have hsum : (∑ ω : OrbitQuotient τ, Nat.card (MulAction.orbit H ω.out)) =
      ∑ _ : OrbitQuotient τ, (3 : ℕ) :=
    Finset.sum_congr rfl (fun ω _ => horb ω)
  have hconst : (∑ _ : OrbitQuotient τ, (3 : ℕ)) = Nat.card (OrbitQuotient τ) * 3 := by
    simp [Finset.sum_const, Nat.card_eq_fintype_card, smul_eq_mul]
  have : Nat.card (OrbitQuotient τ) * 3 ≤ 15 := by
    calc
      Nat.card (OrbitQuotient τ) * 3 = ∑ _ : OrbitQuotient τ, (3 : ℕ) := hconst.symm
      _ = ∑ ω : OrbitQuotient τ, Nat.card (MulAction.orbit H ω.out) := hsum.symm
      _ = Nat.card α := hcard.symm
      _ ≤ 15 := hα
  omega

private lemma mulAut_apply_comm {C : Type} [Group C] {σ h : MulAut C}
    (hcomm : Commute σ h) (c : C) : h (σ c) = σ (h c) := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcomm.eq]

private def smulNonidentity {C W : Type} [Group C] [Group W] (φ : W →* MulAut C) (w : W)
    (x : Nonidentity C) : Nonidentity C :=
  ⟨φ w x, by
    rintro hx
    have h : (φ w).symm (φ w x) = (φ w).symm 1 := congrArg (φ w).symm hx
    exact x.2 (by simpa using h)⟩

private lemma phi_apply_mem_orbit {C W : Type} [Group C] [Group W] {τ : MulAut C}
    {φ : W →* MulAut C} (hφ : ∀ w : W, φ w * τ = τ * φ w) (w : W)
    {x y : Nonidentity C}
    (hxy : (MulAction.orbitRel (tauCyclic τ) (Nonidentity C)) x y) :
    (MulAction.orbitRel (tauCyclic τ) (Nonidentity C))
      (smulNonidentity φ w x) (smulNonidentity φ w y) := by
  rw [MulAction.orbitRel_apply] at hxy ⊢
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hxy
  have hcomm : Commute (φ w) (h : MulAut C) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
    rw [← hn]
    exact (show Commute (φ w) τ from hφ w).zpow_right n
  refine MulAction.mem_orbit_iff.mpr ⟨h, ?_⟩
  apply Subtype.ext
  have hh' : (h : MulAut C) (y : C) = (x : C) := by
    have hval := congrArg Subtype.val hh
    change (h : MulAut C) (y : C) = (x : C) at hval
    exact hval
  change (h : MulAut C) ((φ w) (y : C)) = (φ w) (x : C)
  rw [mulAut_apply_comm hcomm (y : C), hh']

@[instance_reducible]
private def actionOnOrbits {C W : Type} [Group C] [Group W] {τ : MulAut C}
    (φ : W →* MulAut C) (hφ : ∀ w : W, φ w * τ = τ * φ w) :
    MulAction W (OrbitQuotient τ) where
  smul w q :=
    Quotient.map (fun x => smulNonidentity φ w x)
      (fun x y hxy => phi_apply_mem_orbit hφ w hxy) q
  one_smul q := by
    refine Quotient.inductionOn q ?_
    intro x
    change Quotient.map (fun y => smulNonidentity φ 1 y) _ (Quotient.mk'' x) =
      Quotient.mk'' x
    rw [Quotient.map_mk]
    congr 1
    apply Subtype.ext
    simp [smulNonidentity]
  mul_smul a b q := by
    refine Quotient.inductionOn q ?_
    intro x
    change Quotient.map (fun y => smulNonidentity φ (a * b) y) _ (Quotient.mk'' x) =
      Quotient.map (fun y => smulNonidentity φ a y) _
        (Quotient.map (fun y => smulNonidentity φ b y) _ (Quotient.mk'' x))
    rw [Quotient.map_mk, Quotient.map_mk, Quotient.map_mk]
    congr 1
    apply Subtype.ext
    simp [smulNonidentity, map_mul]

private lemma tau_pow_val_injective {C : Type} [Group C] {τ : MulAut C} (hτ3 : τ ^ 3 = 1)
    (hτ : ∀ c : C, τ c = c → c = 1) {c : C} (hc : c ≠ 1) {a b : ZMod 3}
    (h : (τ ^ a.val) c = (τ ^ b.val) c) : a = b := by
  set d : ZMod 3 := a - b with hd
  have haeq : a = b + d := by rw [hd]; abel
  have hval : a.val = (b.val + d.val) % 3 := by rw [haeq, ZMod.val_add]
  have hpow : τ ^ a.val = τ ^ (b.val + d.val) := by
    rw [hval]
    exact (pow_eq_pow_mod (b.val + d.val) hτ3).symm
  have h' : (τ ^ (b.val + d.val)) c = (τ ^ b.val) c := by
    rw [← hpow]
    exact h
  have hd' : (τ ^ d.val) c = c := by
    rw [pow_add, MulAut.mul_apply] at h'
    exact (τ ^ b.val).injective h'
  rcases zmod3_cases d with h0 | h1 | h2
  · rw [h0] at hd
    exact sub_eq_zero.mp hd.symm
  · rw [h1] at hd'
    norm_num at hd'
    exact absurd hd' (tau_apply_ne_self hτ hc)
  · have hval2 : (2 : ZMod 3).val = 2 := by decide
    rw [h2, hval2] at hd'
    exact absurd (by simpa [pow_two, MulAut.mul_apply] using hd')
      (tau_sq_apply_ne_self hτ3 hτ hc)

private lemma existsUnique_tau_pow_val {C : Type} [Group C] {τ : MulAut C} (hτ3 : τ ^ 3 = 1)
    (hτ : ∀ c : C, τ c = c → c = 1) {c : C} (hc : c ≠ 1) {x : C}
    (hx : x ∈ MulAction.orbit (tauCyclic τ) c) :
    ∃! k : ZMod 3, x = (τ ^ k.val) c := by
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hx' : x = (h : MulAut C) c := by
    rw [← hh]; rfl
  have hpow : (τ ^ n) c = (τ ^ (n % 3 : ℤ)) c :=
    congrArg (fun e : MulAut C => e c) (zpow_eq_zpow_emod' (x := τ) n (n := 3) hτ3)
  have hval : ((n : ZMod 3).val : ℤ) = n % 3 := ZMod.val_intCast n
  have hn' : x = (τ ^ (n : ZMod 3).val) c := by
    calc
      x = (h : MulAut C) c := hx'
      _ = (τ ^ n) c := by rw [hn]
      _ = (τ ^ (n % 3 : ℤ)) c := hpow
      _ = (τ ^ ((n : ZMod 3).val : ℤ)) c := by rw [hval]
      _ = (τ ^ (n : ZMod 3).val) c := by rw [zpow_natCast]
  refine ⟨(n : ZMod 3), hn', ?_⟩
  intro l hl
  exact tau_pow_val_injective hτ3 hτ hc (hl.symm.trans hn')

private noncomputable def orbitCoord {C W : Type} [Group C] [Group W] {τ : MulAut C}
    {φ : W →* MulAut C} (hτ3 : τ ^ 3 = 1) (hτ : ∀ c : C, τ c = c → c = 1)
    {c : C} (hc : c ≠ 1) (horbit : ∀ w : W, φ w c ∈ MulAction.orbit (tauCyclic τ) c)
    (w : W) : ZMod 3 :=
  Classical.choose (existsUnique_tau_pow_val hτ3 hτ hc (horbit w))

private lemma orbitCoord_spec {C W : Type} [Group C] [Group W] {τ : MulAut C}
    {φ : W →* MulAut C} (hτ3 : τ ^ 3 = 1) (hτ : ∀ c : C, τ c = c → c = 1)
    {c : C} (hc : c ≠ 1) (horbit : ∀ w : W, φ w c ∈ MulAction.orbit (tauCyclic τ) c)
    (w : W) : φ w c = (τ ^ (orbitCoord hτ3 hτ hc horbit w).val) c :=
  (Classical.choose_spec (existsUnique_tau_pow_val hτ3 hτ hc (horbit w))).1

private lemma tau_pow_val_add {C : Type} [Group C] {τ : MulAut C} (hτ3 : τ ^ 3 = 1)
    (a b : ZMod 3) (c : C) :
    (τ ^ (a + b).val) c = (τ ^ (a.val + b.val)) c := by
  rw [ZMod.val_add]
  exact congrArg (fun e : MulAut C => e c) (pow_eq_pow_mod (a.val + b.val) hτ3).symm

private lemma orbitCoord_add {C W : Type} [Group C] [Group W] {τ : MulAut C}
    {φ : W →* MulAut C} (hτ3 : τ ^ 3 = 1) (hτ : ∀ c : C, τ c = c → c = 1)
    {c : C} (hc : c ≠ 1) (horbit : ∀ w : W, φ w c ∈ MulAction.orbit (tauCyclic τ) c)
    (hφ : ∀ w : W, φ w * τ = τ * φ w) (a b : W) :
    orbitCoord hτ3 hτ hc horbit (a * b) =
      orbitCoord hτ3 hτ hc horbit a + orbitCoord hτ3 hτ hc horbit b := by
  apply tau_pow_val_injective hτ3 hτ hc
  calc
    (τ ^ (orbitCoord hτ3 hτ hc horbit (a * b)).val) c
        = φ (a * b) c := (orbitCoord_spec hτ3 hτ hc horbit (a * b)).symm
    _ = φ a (φ b c) := by rw [map_mul]; rfl
    _ = φ a ((τ ^ (orbitCoord hτ3 hτ hc horbit b).val) c) := by
          rw [orbitCoord_spec hτ3 hτ hc horbit b]
    _ = (τ ^ (orbitCoord hτ3 hτ hc horbit b).val) (φ a c) := by
          have hcomm : Commute (φ a) (τ ^ (orbitCoord hτ3 hτ hc horbit b).val) :=
            (show Commute (φ a) τ from hφ a).pow_right _
          exact (mulAut_apply_comm hcomm c).symm
    _ = (τ ^ (orbitCoord hτ3 hτ hc horbit b).val)
          ((τ ^ (orbitCoord hτ3 hτ hc horbit a).val) c) := by
          rw [orbitCoord_spec hτ3 hτ hc horbit a]
    _ = ((τ ^ (orbitCoord hτ3 hτ hc horbit b).val) *
          (τ ^ (orbitCoord hτ3 hτ hc horbit a).val)) c := rfl
    _ = (τ ^ ((orbitCoord hτ3 hτ hc horbit b).val +
          (orbitCoord hτ3 hτ hc horbit a).val)) c := by rw [pow_add]
    _ = (τ ^ ((orbitCoord hτ3 hτ hc horbit a).val +
          (orbitCoord hτ3 hτ hc horbit b).val)) c := by rw [Nat.add_comm]
    _ = (τ ^ (orbitCoord hτ3 hτ hc horbit a + orbitCoord hτ3 hτ hc horbit b).val) c :=
          (tau_pow_val_add hτ3 _ _ c).symm

private lemma orbitCoord_one {C W : Type} [Group C] [Group W] {τ : MulAut C}
    {φ : W →* MulAut C} (hτ3 : τ ^ 3 = 1) (hτ : ∀ c : C, τ c = c → c = 1)
    {c : C} (hc : c ≠ 1) (horbit : ∀ w : W, φ w c ∈ MulAction.orbit (tauCyclic τ) c) :
    orbitCoord hτ3 hτ hc horbit 1 = 0 := by
  apply tau_pow_val_injective hτ3 hτ hc
  rw [← orbitCoord_spec hτ3 hτ hc horbit 1]
  simp

private lemma phi_apply_eq_self {C W : Type} [Group C] [Group W] [IsSimpleGroup W] {τ : MulAut C}
    (hτ3 : τ ^ 3 = 1) (hτ : ∀ c : C, τ c = c → c = 1) (hW : 180 < Nat.card W)
    {φ : W →* MulAut C} (hφ : ∀ w : W, φ w * τ = τ * φ w)
    {c : C} (hc : c ≠ 1) (horbit : ∀ w : W, φ w c ∈ MulAction.orbit (tauCyclic τ) c)
    (w : W) : φ w c = c := by
  let k0 : W → ZMod 3 := orbitCoord hτ3 hτ hc horbit
  have hk0_one : k0 1 = 0 := orbitCoord_one hτ3 hτ hc horbit
  have hk0_mul : ∀ a b : W, k0 (a * b) = k0 a + k0 b :=
    fun a b => orbitCoord_add hτ3 hτ hc horbit hφ a b
  let k : W →* Multiplicative (ZMod 3) :=
    { toFun := fun y => Multiplicative.ofAdd (k0 y)
      map_one' := by simp [hk0_one]
      map_mul' := by intro a b; simp [hk0_mul a b] }
  have hker : k.ker = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top k.ker with hbot | htop
    · exfalso
      have hinj : Function.Injective k := (MonoidHom.ker_eq_bot_iff k).mp hbot
      haveI : Fintype (Multiplicative (ZMod 3)) :=
        Fintype.ofEquiv (ZMod 3) Multiplicative.toAdd.symm
      have hle : Nat.card W ≤ Nat.card (Multiplicative (ZMod 3)) :=
        Nat.card_le_card_of_injective k hinj
      have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      omega
    · exact htop
  have hkw : k w = 1 := by
    have : w ∈ k.ker := by rw [hker]; exact Subgroup.mem_top w
    exact MonoidHom.mem_ker.mp this
  have hkw0 : k0 w = 0 := by
    have := congrArg Multiplicative.toAdd hkw
    simpa [k] using this
  rw [orbitCoord_spec hτ3 hτ hc horbit w]
  change (τ ^ (k0 w).val) c = c
  rw [hkw0]
  simp

private lemma orbitAction_fixes {C W : Type} [Group C] [Finite C] [Group W]
    [IsSimpleGroup W] {τ : MulAut C} (hC : Nat.card C ≤ 16) (hτ3 : τ ^ 3 = 1)
    (hτ : ∀ c : C, τ c = c → c = 1) (hW : 180 < Nat.card W)
    {φ : W →* MulAut C} (hφ : ∀ w : W, φ w * τ = τ * φ w) (w : W)
    (x : Nonidentity C) :
    Quotient.mk'' (smulNonidentity φ w x) = (Quotient.mk'' x : OrbitQuotient τ) := by
  classical
  let Ω := OrbitQuotient τ
  letI : MulAction W Ω := actionOnOrbits φ hφ
  have hΩ : Nat.card Ω ≤ 5 := card_orbitQuotient_le_five hC hτ3 hτ
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hperm : Nat.card (Equiv.Perm Ω) ≤ 120 := by
    rw [Nat.card_perm]
    calc
      (Nat.card Ω)! = (Fintype.card Ω)! := by rw [Nat.card_eq_fintype_card]
      _ ≤ 5! := Nat.factorial_le (by simpa using hΩ)
      _ = 120 := by decide
  let ψ : W →* Equiv.Perm Ω := MulAction.toPermHom W Ω
  have hψ : ψ = 1 := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ψ.ker with hbot | htop
    · exfalso
      have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hbot
      have hle : Nat.card W ≤ Nat.card (Equiv.Perm Ω) :=
        Nat.card_le_card_of_injective ψ hinj
      omega
    · apply MonoidHom.ext
      intro y
      exact MonoidHom.mem_ker.mp (by rw [htop]; exact Subgroup.mem_top y)
  have hwx : ψ w = 1 := by simpa using DFunLike.congr_fun hψ w
  have h := congrArg (fun e : Equiv.Perm Ω => e (Quotient.mk'' x)) hwx
  have h' : (w • (Quotient.mk'' x) : Ω) = Quotient.mk'' x := by
    simpa [ψ] using h
  change Quotient.map (fun y => smulNonidentity φ w y) _ (Quotient.mk'' x) =
    Quotient.mk'' x at h'
  rw [Quotient.map_mk] at h'
  exact h'

private lemma phi_preserves_orbit_of_card {C W : Type} [Group C] [Finite C] [Group W]
    [IsSimpleGroup W] {τ : MulAut C} (hC : Nat.card C ≤ 16) (hτ3 : τ ^ 3 = 1)
    (hτ : ∀ c : C, τ c = c → c = 1) (hW : 180 < Nat.card W)
    {φ : W →* MulAut C} (hφ : ∀ w : W, φ w * τ = τ * φ w)
    (w : W) {c : C} (hc : c ≠ 1) :
    φ w c ∈ MulAction.orbit (tauCyclic τ) c := by
  classical
  let x : Nonidentity C := ⟨c, hc⟩
  have hq := orbitAction_fixes hC hτ3 hτ hW hφ w x
  have hrel : smulNonidentity φ w x ∈ MulAction.orbit (tauCyclic τ) x :=
    Quotient.exact hq
  have hmem : (smulNonidentity φ w x : C) ∈
      Subtype.val '' (MulAction.orbit (tauCyclic τ) x : Set (Nonidentity C)) :=
    ⟨_, hrel, rfl⟩
  rw [orbit_subtype_val_image] at hmem
  simpa [x, smulNonidentity] using hmem

theorem eq_one_of_commute_fixedPointFree {C W : Type} [Group C] [Finite C] [Group W]
    [IsSimpleGroup W] (h2 : ∀ c : C, c * c = 1) (hC : Nat.card C ≤ 16) {τ : MulAut C}
    (hτ3 : τ ^ 3 = 1) (hτ : ∀ c : C, τ c = c → c = 1) (hW : 180 < Nat.card W)
    (φ : W →* MulAut C) (hφ : ∀ w : W, φ w * τ = τ * φ w) (w : W) : φ w = 1 := by
  ext c
  by_cases hc : c = 1
  · subst c
    exact map_one (φ w)
  · exact phi_apply_eq_self hτ3 hτ hW hφ hc
      (fun y => phi_preserves_orbit_of_card hC hτ3 hτ hW hφ y hc) w

end CFSG.RankThree.GF2n.Stroth80.Sec108

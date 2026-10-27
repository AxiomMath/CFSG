module

public import Certificates.Data.TwoDepSmallLow
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nLA_closure_inv {p N : ℕ} {S : Set (Module.End (ZMod p) (GGTWE p N))}
    (hS : ∀ s ∈ S, s * s = 1) :
    ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1 := by
  intro g hg
  induction hg using Submonoid.closure_induction with
  | mem x hx => exact ⟨x, Submonoid.subset_closure hx, hS x hx, hS x hx⟩
  | one => exact ⟨1, Submonoid.one_mem _, one_mul 1, mul_one 1⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨x', hx'mem, hxx', hx'x⟩ := ihx
      obtain ⟨y', hy'mem, hyy', hy'y⟩ := ihy
      exact ⟨y' * x', Submonoid.mul_mem _ hy'mem hx'mem,
        by rw [mul_assoc, ← mul_assoc y y' x', hyy', one_mul, hxx'],
        by rw [mul_assoc, ← mul_assoc x' x y, hx'x, one_mul, hy'y]⟩

private lemma l05nLA_card_subgroup {p N : ℕ} {S : Set (Module.End (ZMod p) (GGTWE p N))}
    (hinv : ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1)
    (H : Subgroup (Module.End (ZMod p) (GGTWE p N))ˣ)
    (hH : ∀ u : (Module.End (ZMod p) (GGTWE p N))ˣ,
      u ∈ H ↔ (u : Module.End (ZMod p) (GGTWE p N)) ∈ Submonoid.closure S) :
    Nat.card ↥H = Nat.card ↥(Submonoid.closure S) := by
  apply Nat.card_eq_of_bijective
    (fun u : ↥H => (⟨(u.1 : Module.End (ZMod p) (GGTWE p N)), (hH u.1).mp u.2⟩ :
      ↥(Submonoid.closure S)))
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Units.ext
    simpa using congrArg Subtype.val hab
  · intro g
    obtain ⟨g', hg'mem, hg'1, hg'2⟩ := hinv (g : Module.End (ZMod p) (GGTWE p N)) g.2
    refine ⟨⟨Units.mkOfMulEqOne (g : Module.End (ZMod p) (GGTWE p N)) g' hg'1, ?_⟩, ?_⟩
    · exact (hH _).mpr (by
        rw [Units.val_mkOfMulEqOne]
        exact g.2)
    · apply Subtype.ext
      change ((Units.mkOfMulEqOne (g : Module.End (ZMod p) (GGTWE p N)) g' hg'1 :
        (Module.End (ZMod p) (GGTWE p N))ˣ) : Module.End (ZMod p) (GGTWE p N)) =
        (g : Module.End (ZMod p) (GGTWE p N))
      rw [Units.val_mkOfMulEqOne]

theorem ggTWL_card_dvd {p N : ℕ} [Fact p.Prime] {S S' : Set (Module.End (ZMod p) (GGTWE p N))}
    (hS : ∀ s ∈ S, s * s = 1) (hS' : ∀ s ∈ S', s * s = 1) (hsub : S' ⊆ Submonoid.closure S) :
    Nat.card ↥(Submonoid.closure S') ∣ Nat.card ↥(Submonoid.closure S) := by
  let M := Module.End (ZMod p) (GGTWE p N)
  have hinv := l05nLA_closure_inv (p := p) (N := N) hS
  have hinv' := l05nLA_closure_inv (p := p) (N := N) hS'
  let H : Subgroup Mˣ :=
    { carrier := {u | (u : M) ∈ Submonoid.closure S}
      one_mem' := by
        show ((1 : Mˣ) : M) ∈ Submonoid.closure S
        rw [Units.val_one]
        exact Submonoid.one_mem _
      mul_mem' := by
        intro u v hu hv
        show ((u * v : Mˣ) : M) ∈ Submonoid.closure S
        rw [Units.val_mul]
        exact Submonoid.mul_mem _ hu hv
      inv_mem' := by
        intro u hu
        obtain ⟨g', hg'mem, hg'1, hg'2⟩ := hinv (u : M) hu
        have hunit : ((u⁻¹ : Mˣ) : M) * (u : M) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have hcalc : ((u⁻¹ : Mˣ) : M) = g' := by
          calc ((u⁻¹ : Mˣ) : M) = ((u⁻¹ : Mˣ) : M) * 1 := (mul_one _).symm
            _ = ((u⁻¹ : Mˣ) : M) * ((u : M) * g') := by rw [hg'1]
            _ = (((u⁻¹ : Mˣ) : M) * (u : M)) * g' := (mul_assoc _ _ _).symm
            _ = 1 * g' := by rw [hunit]
            _ = g' := one_mul g'
        change ((u⁻¹ : Mˣ) : M) ∈ Submonoid.closure S
        rw [hcalc]
        exact hg'mem }
  let H' : Subgroup Mˣ :=
    { carrier := {u | (u : M) ∈ Submonoid.closure S'}
      one_mem' := by
        show ((1 : Mˣ) : M) ∈ Submonoid.closure S'
        rw [Units.val_one]
        exact Submonoid.one_mem _
      mul_mem' := by
        intro u v hu hv
        show ((u * v : Mˣ) : M) ∈ Submonoid.closure S'
        rw [Units.val_mul]
        exact Submonoid.mul_mem _ hu hv
      inv_mem' := by
        intro u hu
        obtain ⟨g', hg'mem, hg'1, hg'2⟩ := hinv' (u : M) hu
        have hunit : ((u⁻¹ : Mˣ) : M) * (u : M) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have hcalc : ((u⁻¹ : Mˣ) : M) = g' := by
          calc ((u⁻¹ : Mˣ) : M) = ((u⁻¹ : Mˣ) : M) * 1 := (mul_one _).symm
            _ = ((u⁻¹ : Mˣ) : M) * ((u : M) * g') := by rw [hg'1]
            _ = (((u⁻¹ : Mˣ) : M) * (u : M)) * g' := (mul_assoc _ _ _).symm
            _ = 1 * g' := by rw [hunit]
            _ = g' := one_mul g'
        change ((u⁻¹ : Mˣ) : M) ∈ Submonoid.closure S'
        rw [hcalc]
        exact hg'mem }
  have hle : H' ≤ H := by
    intro u hu
    change (u : M) ∈ Submonoid.closure S
    change (u : M) ∈ Submonoid.closure S' at hu
    exact (Submonoid.closure_le.mpr hsub) hu
  have hcard : Nat.card ↥H = Nat.card ↥(Submonoid.closure S) :=
    l05nLA_card_subgroup hinv H (fun u => Iff.rfl)
  have hcard' : Nat.card ↥H' = Nat.card ↥(Submonoid.closure S') :=
    l05nLA_card_subgroup hinv' H' (fun u => Iff.rfl)
  have hdv := Subgroup.card_dvd_of_le hle
  rwa [hcard', hcard] at hdv

private lemma l05nLA_fact_eq (n : ℕ) : ggTWLFact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (n + 1) * ggTWLFact n = (n + 1).factorial
      rw [ih, Nat.factorial_succ]

private lemma l05nLA_weylType_mem {r n c : ℕ} (h : GGWeylTypeData r n c) :
    (n, c) ∈ ggTWLWeylTypes r := by
  rcases h with ⟨h1, hn, hc⟩ | ⟨h2, hn, hc⟩ | ⟨h4, hn, hc⟩ | ⟨hr, hn, hc⟩ |
    ⟨hr, hn, hc⟩ | ⟨hr, hn, hc⟩ | ⟨hr, hn, hc⟩ | ⟨hr, hn, hc⟩
  · obtain rfl := hn; obtain rfl := hc
    simp [ggTWLWeylTypes, h1, l05nLA_fact_eq]
  · obtain rfl := hn; obtain rfl := hc
    simp [ggTWLWeylTypes, h2, l05nLA_fact_eq]
  · obtain rfl := hn
    have hev : Even r ↔ r % 2 = 0 := by rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    have hc' : c = if r % 2 = 0 then 2 else 1 := by rw [hc, if_congr hev rfl rfl]
    obtain rfl := hc'
    simp [ggTWLWeylTypes, h4, l05nLA_fact_eq]
  · obtain rfl := hr; obtain rfl := hn; obtain rfl := hc; decide
  · obtain rfl := hr; obtain rfl := hn; obtain rfl := hc; decide
  · obtain rfl := hr; obtain rfl := hn; obtain rfl := hc; decide
  · obtain rfl := hr; obtain rfl := hn; obtain rfl := hc; decide
  · obtain rfl := hr; obtain rfl := hn; obtain rfl := hc; decide

theorem ggTWLPZArith_sound {N K : ℕ} {hasCen : Bool} (h : ggTWLPZArith N K hasCen = true)
    {r n c : ℕ} (ht : GGWeylTypeData r n c) (hlo : N - 3 ≤ r) (hhi : r ≤ N - 1)
    (hKn : K ∣ n) : n = K ∧ c = 1 ∧ hasCen = true := by
  have hmem := l05nLA_weylType_mem ht
  simp only [ggTWLPZArith, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, hall⟩ := h
  have hall' : ∀ i ∈ List.range 3, (ggTWLWeylTypes (N - 3 + i)).all (fun t =>
      t.1 % K != 0 || (t.1 == K && t.2 == 1 && hasCen)) = true :=
    List.all_eq_true.mp hall
  have hi : r - (N - 3) ∈ List.range 3 := by
    rw [List.mem_range]
    omega
  have hsum : N - 3 + (r - (N - 3)) = r := by omega
  have hinner := hall' (r - (N - 3)) hi
  rw [hsum] at hinner
  have hcond := (List.all_eq_true.mp hinner) (n, c) hmem
  have hmod : n % K = 0 := Nat.mod_eq_zero_of_dvd hKn
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcond
  rcases hcond with hne | ⟨⟨hnK, hc⟩, hcen⟩
  · exact absurd hmod hne
  · exact ⟨hnK, hc, hcen⟩

end CFSG.StandardType

end

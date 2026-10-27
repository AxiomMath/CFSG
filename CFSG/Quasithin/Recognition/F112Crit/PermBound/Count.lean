module

public import CFSG.Quasithin.Recognition.F112Crit.PermBound.Basic
import Mathlib.Tactic.Abel
public import CFSG.Quasithin.Recognition.F112Crit.GaloisDescent
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.F112Crit.PermBound

open GaloisDescent

variable {H : Type*} [Group H] {Ω : Type*} [MulAction H Ω] {M : Type*} [AddCommGroup M]
  [DistribMulAction H M]

private theorem nsmul_mod_two (h2 : ∀ m : M, m + m = 0) (n : ℕ) (m : M) :
    (n % 2) • m = n • m := by
  conv_rhs => rw [← Nat.mod_add_div n 2, add_nsmul, mul_nsmul, two_nsmul, h2, nsmul_zero, add_zero]

private theorem zmod_val_add_smul (h2 : ∀ m : M, m + m = 0) (a b : ZMod 2) (m : M) :
    (a + b).val • m = a.val • m + b.val • m := by
  rw [ZMod.val_add, nsmul_mod_two h2, add_nsmul]

private def avgSub [Fintype Ω] (h2 : ∀ m : M, m + m = 0) (d : Ω → M) (X : AddSubgroup M) :
    AddSubgroup (Ω → ZMod 2) where
  carrier := {f | ∑ ν, f ν = 0 ∧ ∑ ν, (f ν).val • d ν ∈ X}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨by simp [Finset.sum_add_distrib, hf1, hg1], ?_⟩
    simp only [Pi.add_apply, zmod_val_add_smul h2, Finset.sum_add_distrib]
    exact X.add_mem hf2 hg2
  neg_mem' := by
    intro f hf
    have : -f = f := funext fun ν => CharTwo.neg_eq (f ν)
    rw [this]
    exact hf

private theorem smul_mem_avgSub [Fintype Ω] {h2 : ∀ m : M, m + m = 0} {d : Ω → M}
    {X : AddSubgroup M} {L : Subgroup H} (hXL : ∀ l ∈ L, ∀ x ∈ X, l • x ∈ X)
    (hd : ∀ l ∈ L, ∀ μ, l • d μ - d (l • μ) ∈ X) {l : H} (hl : l ∈ L) {f : Ω → ZMod 2}
    (hf : f ∈ avgSub h2 d X) : (fun ν => f (l⁻¹ • ν)) ∈ avgSub h2 d X := by
  obtain ⟨hf1, hf2⟩ := hf
  refine ⟨?_, ?_⟩
  · rw [← hf1]
    exact Equiv.sum_comp (MulAction.toPerm l⁻¹) f
  · have e1 : ∑ ν, (f (l⁻¹ • ν)).val • d ν = ∑ ν, (f ν).val • d (l • ν) := by
      rw [← Equiv.sum_comp (MulAction.toPerm l) (fun ν => (f (l⁻¹ • ν)).val • d ν)]
      simp [MulAction.toPerm_apply, inv_smul_smul]
    rw [e1]
    have e2 : l • ∑ ν, (f ν).val • d ν - ∑ ν, (f ν).val • d (l • ν) =
        ∑ ν, (f ν).val • (l • d ν - d (l • ν)) := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [smul_comm, nsmul_sub]
    have e3 : ∑ ν, (f ν).val • (l • d ν - d (l • ν)) ∈ X :=
      X.sum_mem fun ν _ => X.nsmul_mem (hd l hl ν) _
    have e4 : ∑ ν, (f ν).val • d (l • ν) =
        l • ∑ ν, (f ν).val • d ν - ∑ ν, (f ν).val • (l • d ν - d (l • ν)) := by
      rw [← e2, sub_sub_cancel]
    rw [e4]
    exact X.sub_mem (hXL l hl _ hf2) e3

private theorem exists_smul_eq_self_ne_zero {G V : Type*} [Group G] [MulAction G V]
    [AddCommGroup V] [Finite V] (hG : IsPGroup 2 G) (h2 : ∀ a : V, a + a = 0) (A : AddSubgroup V)
    (hA : ∀ g : G, ∀ a ∈ A, g • a ∈ A) (h0 : ∀ g : G, g • (0 : V) = 0) {a₀ : V}
    (ha₀ : a₀ ∈ A) (ha₀' : a₀ ≠ 0) : ∃ a ∈ A, a ≠ 0 ∧ ∀ g : G, g • a = a := by
  let S : SubMulAction G V := ⟨(A : Set V), fun g a ha => hA g a ha⟩
  have hdvd : 2 ∣ Nat.card S := by
    have h1 : addOrderOf (⟨a₀, ha₀⟩ : A) = 2 := by
      rw [AddSubgroup.addOrderOf_mk]
      exact addOrderOf_eq_prime (by rw [two_nsmul]; exact h2 a₀) ha₀'
    have h3 : Nat.card S = Nat.card A := Nat.card_congr (Equiv.refl _)
    rw [h3, ← h1]
    exact addOrderOf_dvd_natCard _
  have hfix0 : (⟨0, A.zero_mem⟩ : S) ∈ MulAction.fixedPoints G S := fun g =>
    Subtype.ext (h0 g)
  obtain ⟨b, hb, hne⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point S hdvd hfix0
  refine ⟨b.1, b.2, fun h => hne (Subtype.ext h.symm), fun g => ?_⟩
  exact congrArg Subtype.val (hb g)

private theorem eq_zero_of_mem_avgSub [Fintype Ω] [DecidableEq Ω] {h2 : ∀ m : M, m + m = 0}
    {L : Subgroup H} (htrans : ∀ μ ν : Ω, ∃ l ∈ L, l • μ = ν) (hodd : Odd (Fintype.card Ω))
    {ω₀ : Ω} {U : Subgroup H} (hUL : U ≤ L) (hU2 : IsPGroup 2 U)
    (hUtrans : ∀ μ ν : Ω, μ ≠ ω₀ → ν ≠ ω₀ → ∃ u ∈ U, u • μ = ν)
    {X : AddSubgroup M} {c : M} (hXL : ∀ l ∈ L, ∀ x ∈ X, l • x ∈ X)
    (hcK : c ∈ commL M L) (hcX : c ∉ X)
    (hXK : ∀ y ∈ commL M L, (∀ l ∈ L, l • y - y ∈ X) → y ∈ X)
    {d : Ω → M} (hd1 : ∀ l ∈ L, ∀ μ, l • d μ - d (l • μ) ∈ X)
    (hdc : ∀ l ∈ L, l • c - d (l • ω₀) ∈ X)
    {f : Ω → ZMod 2} (hf : f ∈ avgSub h2 d X) : f = 0 := by
  by_contra hf0
  letI : MulAction U (Ω → ZMod 2) := arrowAction
  obtain ⟨g, hgA, hg0, hgfix⟩ := exists_smul_eq_self_ne_zero (V := Ω → ZMod 2) hU2
    (fun a => funext fun ν => CharTwo.add_self_eq_zero (a ν)) (avgSub h2 d X)
    (fun u a ha => smul_mem_avgSub hXL hd1 (hUL u.2) ha) (fun u => rfl) hf hf0
  obtain ⟨hgs, hgX⟩ := hgA
  have hgc : ∀ u ∈ U, ∀ ν, g (u • ν) = g ν := by
    intro u hu ν
    have h := congrFun (hgfix (⟨u, hu⟩ : U)⁻¹) ν
    change g (((⟨u, hu⟩ : U)⁻¹)⁻¹ • ν) = g ν at h
    rwa [inv_inv] at h
  have hconst : ∀ μ ν : Ω, μ ≠ ω₀ → ν ≠ ω₀ → g μ = g ν := by
    intro μ ν hμ hν
    obtain ⟨u, hu, hμν⟩ := hUtrans μ ν hμ hν
    rw [← hμν, hgc u hu μ]
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ZMod 2, ∀ ν, ν ≠ ω₀ → g ν = c₁ := by
    by_cases h : ∃ μ, μ ≠ ω₀
    · obtain ⟨μ, hμ⟩ := h
      exact ⟨g μ, fun ν hν => hconst ν μ hν hμ⟩
    · exact ⟨0, fun ν hν => (h ⟨ν, hν⟩).elim⟩
  have hsum0 : ∑ ν ∈ Finset.univ.erase ω₀, g ν = 0 := by
    rw [Finset.sum_congr rfl fun ν hν => hc₁ ν (Finset.ne_of_mem_erase hν), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    obtain ⟨k, hk⟩ := hodd
    have : Fintype.card Ω - 1 = 2 * k := by omega
    rw [this, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero, nsmul_zero]
  have hgω : g ω₀ = 0 := by
    have := Finset.add_sum_erase Finset.univ g (Finset.mem_univ ω₀)
    rw [hsum0, hgs, add_zero] at this
    exact this
  have hg1 : ∀ ν, ν ≠ ω₀ → g ν = 1 := by
    obtain ⟨ν₀, hν₀⟩ := Function.ne_iff.mp hg0
    have hν₀' : ν₀ ≠ ω₀ := fun h => hν₀ (by rw [h, hgω]; rfl)
    have hc1 : c₁ = 1 := by
      have : c₁ ≠ 0 := by rw [← hc₁ ν₀ hν₀']; exact hν₀
      revert this
      generalize c₁ = x
      revert x
      decide
    intro ν hν
    rw [hc₁ ν hν, hc1]
  have hsumX : ∑ ν ∈ Finset.univ.erase ω₀, d ν ∈ X := by
    have := Finset.add_sum_erase Finset.univ (fun ν => (g ν).val • d ν) (Finset.mem_univ ω₀)
    rw [hgω, ZMod.val_zero, zero_smul, zero_add,
      Finset.sum_congr rfl fun ν hν => by rw [hg1 ν (Finset.ne_of_mem_erase hν)]] at this
    have h1 : (1 : ZMod 2).val = 1 := rfl
    simp only [h1, one_smul] at this
    rw [this]
    exact hgX
  have hsub : ∑ ν, d ν - d ω₀ ∈ X := by
    rw [← Finset.sum_erase_eq_sub (Finset.mem_univ ω₀)]
    exact hsumX
  have hT : ∀ μ, ∑ ν, d ν - d μ ∈ X := by
    intro μ
    obtain ⟨l, hl, hlμ⟩ := htrans ω₀ μ
    have h1 : l • (∑ ν, d ν - d ω₀) ∈ X := hXL l hl _ hsub
    have h2' : l • ∑ ν, d ν - ∑ ν, d ν ∈ X := by
      have : l • ∑ ν, d ν - ∑ ν, d ν = ∑ ν, (l • d ν - d (l • ν)) := by
        rw [Finset.smul_sum, Finset.sum_sub_distrib,
          Fintype.sum_equiv (MulAction.toPerm l) (fun ν => d (l • ν)) d fun _ => rfl]
      rw [this]
      exact X.sum_mem fun ν _ => hd1 l hl ν
    have h3 : l • d ω₀ - d μ ∈ X := by simpa [hlμ] using hd1 l hl ω₀
    have : ∑ ν, d ν - d μ =
        -(l • ∑ ν, d ν - ∑ ν, d ν) + l • (∑ ν, d ν - d ω₀) + (l • d ω₀ - d μ) := by
      rw [smul_sub]; abel
    rw [this]
    exact X.add_mem (X.add_mem (X.neg_mem h2') h1) h3
  have hall : ∀ l ∈ L, l • c - c ∈ X := by
    intro l hl
    have h1 := hdc l hl
    have h2' := hdc 1 L.one_mem
    simp only [one_smul] at h2'
    have h3 : d (l • ω₀) - d ω₀ ∈ X := by
      have := X.sub_mem (hT ω₀) (hT (l • ω₀))
      simpa using this
    have : l • c - c = (l • c - d (l • ω₀)) - (c - d ω₀) + (d (l • ω₀) - d ω₀) := by abel
    rw [this]
    exact X.add_mem (X.sub_mem h1 h2') h3
  exact hcX (hXK c hcK hall)

theorem sum_not_mem [Fintype Ω] [DecidableEq Ω] (h2 : ∀ m : M, m + m = 0)
    {L : Subgroup H} (htrans : ∀ μ ν : Ω, ∃ l ∈ L, l • μ = ν) (hodd : Odd (Fintype.card Ω))
    {ω₀ : Ω} {U : Subgroup H} (hUL : U ≤ L) (hU2 : IsPGroup 2 U)
    (hUtrans : ∀ μ ν : Ω, μ ≠ ω₀ → ν ≠ ω₀ → ∃ u ∈ U, u • μ = ν)
    {X : AddSubgroup M} {c : M} (hXL : ∀ l ∈ L, ∀ x ∈ X, l • x ∈ X)
    (hcK : c ∈ commL M L) (hcX : c ∉ X)
    (hXK : ∀ y ∈ commL M L, (∀ l ∈ L, l • y - y ∈ X) → y ∈ X)
    {d : Ω → M} (hd1 : ∀ l ∈ L, ∀ μ, l • d μ - d (l • μ) ∈ X)
    (hdc : ∀ l ∈ L, l • c - d (l • ω₀) ∈ X) {B : Finset Ω} (hB : B.Nonempty)
    (hBe : Even B.card) : ∑ ν ∈ B, d ν ∉ X := by
  intro hX
  have h1 : (1 : ZMod 2).val = 1 := rfl
  have hmem : (fun ν => if ν ∈ B then (1 : ZMod 2) else 0) ∈ avgSub h2 d X := by
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact ZMod.natCast_eq_zero_iff_even.mpr hBe
    · have : ∀ ν : Ω, (if ν ∈ B then (1 : ZMod 2) else 0).val • d ν =
          if ν ∈ B then d ν else 0 := by
        intro ν
        by_cases h : ν ∈ B <;> simp [h, h1]
      simp only [this]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      exact hX
  have h0 := eq_zero_of_mem_avgSub (h2 := h2) htrans hodd hUL hU2 hUtrans hXL hcK hcX hXK hd1 hdc
    hmem
  obtain ⟨ν, hν⟩ := hB
  have := congrFun h0 ν
  simp [hν] at this

theorem exists_d {L : Subgroup H} (htrans : ∀ μ ν : Ω, ∃ l ∈ L, l • μ = ν) (ω₀ : Ω)
    {S : Set H} (hSL : ∀ z ∈ S, ∀ l ∈ L, z * l * z⁻¹ ∈ L) {X : AddSubgroup M} {c : M}
    (hXL : ∀ l ∈ L, ∀ x ∈ X, l • x ∈ X)
    (hcfix : ∀ l ∈ L, l • ω₀ = ω₀ → l • c - c ∈ X)
    (hcS : ∀ z ∈ S, ∀ l ∈ L, l • ω₀ = z • ω₀ → z • c - l • c ∈ X) :
    ∃ d : Ω → M, (∀ l ∈ L, ∀ μ, l • d μ - d (l • μ) ∈ X) ∧
      (∀ l ∈ L, l • c - d (l • ω₀) ∈ X) ∧ ∀ z ∈ S, ∀ μ, z • d μ - d (z • μ) ∈ X := by
  choose s hsL hsω using fun μ => htrans ω₀ μ
  have P0 : ∀ l ∈ L, ∀ μ, l • ω₀ = μ → l • c - s μ • c ∈ X := by
    intro l hl μ hlμ
    have hh : (s μ)⁻¹ * l ∈ L := L.mul_mem (L.inv_mem (hsL μ)) hl
    have hfix : ((s μ)⁻¹ * l) • ω₀ = ω₀ :=
      calc ((s μ)⁻¹ * l) • ω₀ = (s μ)⁻¹ • (l • ω₀) := mul_smul _ _ _
        _ = (s μ)⁻¹ • (s μ • ω₀) := by rw [hlμ, hsω]
        _ = ω₀ := inv_smul_smul _ _
    have h1 := hXL _ (hsL μ) _ (hcfix _ hh hfix)
    rwa [smul_sub, ← mul_smul, mul_inv_cancel_left] at h1
  refine ⟨fun μ => s μ • c, ?_, ?_, ?_⟩
  · intro l hl μ
    have := P0 (l * s μ) (L.mul_mem hl (hsL μ)) (l • μ) (by rw [mul_smul, hsω])
    simpa only [mul_smul] using this
  · intro l hl
    exact P0 l hl _ rfl
  · intro z hz μ
    obtain ⟨l₁, hl₁, hl₁ω⟩ := htrans ω₀ (z • ω₀)
    have hw : z * s μ * z⁻¹ ∈ L := hSL z hz _ (hsL μ)
    have hwz : z * s μ * z⁻¹ * z = z * s μ := by rw [mul_assoc, inv_mul_cancel, mul_one]
    have h1 := hXL _ hw _ (hcS z hz l₁ hl₁ hl₁ω)
    have h2 := P0 (z * s μ * z⁻¹ * l₁) (L.mul_mem hw hl₁) (z • μ)
      (by rw [mul_smul, hl₁ω, ← mul_smul, hwz, mul_smul, hsω])
    have e1 : (z * s μ * z⁻¹) • z • c = z • s μ • c := by rw [← mul_smul, hwz, mul_smul]
    have e2 : (z * s μ * z⁻¹) • l₁ • c = (z * s μ * z⁻¹ * l₁) • c := (mul_smul _ _ _).symm
    have : z • s μ • c - s (z • μ) • c =
        (z * s μ * z⁻¹) • (z • c - l₁ • c) + ((z * s μ * z⁻¹ * l₁) • c - s (z • μ) • c) := by
      rw [smul_sub, e1, e2]
      abel
    rw [this]
    exact X.add_mem h1 h2

private theorem exists_transversal [Fintype Ω] [DecidableEq Ω] {z : H} (hz : z * z = 1) :
    ∃ T : Finset Ω, Disjoint T (T.image (z • ·)) ∧
      2 * T.card + Nat.card (MulAction.fixedBy Ω z) = Fintype.card Ω := by
  have hzz : ∀ ω : Ω, z • z • ω = ω := fun ω => by rw [← mul_smul, hz, one_smul]
  obtain ⟨e, he⟩ : ∃ e : Ω → ℕ, Function.Injective e :=
    ⟨fun ω => (Fintype.equivFin Ω ω : ℕ), fun a b h => (Fintype.equivFin Ω).injective (Fin.ext h)⟩
  let Fc : Finset Ω := Finset.univ.filter (fun ω => ¬ z • ω = ω)
  let T : Finset Ω := Fc.filter (fun ω => e ω < e (z • ω))
  have hFc : ∀ ω, ω ∈ Fc ↔ ¬ z • ω = ω := fun ω => by simp [Fc]
  have hT : ∀ ω, ω ∈ T ↔ ¬ z • ω = ω ∧ e ω < e (z • ω) := fun ω => by simp [T, hFc]
  have hdisj : Disjoint T (T.image (z • ·)) := by
    rw [Finset.disjoint_left]
    intro ω hω hω'
    obtain ⟨ω', hω'T, rfl⟩ := Finset.mem_image.mp hω'
    have h1 := ((hT _).mp hω).2
    have h2 := ((hT _).mp hω'T).2
    rw [hzz] at h1
    omega
  have hunion : Fc = T ∪ T.image (z • ·) := by
    ext ω
    rw [Finset.mem_union, Finset.mem_image, hFc]
    constructor
    · intro hω
      rcases lt_or_gt_of_ne (he.ne (Ne.symm hω)) with h | h
      · exact Or.inl ((hT ω).mpr ⟨hω, h⟩)
      · refine Or.inr ⟨z • ω, (hT _).mpr ⟨by rw [hzz]; exact Ne.symm hω, by rw [hzz]; exact h⟩,
          hzz ω⟩
    · rintro (h | ⟨ω', hω', rfl⟩)
      · exact ((hT ω).mp h).1
      · intro h
        rw [hzz] at h
        exact ((hT ω').mp hω').1 h.symm
  have hcard : Fc.card = 2 * T.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (MulAction.injective z), two_mul]
  have hfix : Nat.card (MulAction.fixedBy Ω z) =
      (Finset.univ.filter (fun ω : Ω => z • ω = ω)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  refine ⟨T, hdisj, ?_⟩
  rw [hfix, ← hcard, add_comm, ← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not (fun ω : Ω => z • ω = ω)

private theorem sum_symmDiff_two [DecidableEq Ω] (h2 : ∀ m : M, m + m = 0) (g : Ω → M)
    (D₁ D₂ : Finset Ω) :
    ∑ μ ∈ symmDiff D₁ D₂, g μ = ∑ μ ∈ D₁, g μ + ∑ μ ∈ D₂, g μ := by
  have e1 := Finset.sum_inter_add_sum_sdiff D₁ D₂ g
  have e2 := Finset.sum_inter_add_sum_sdiff D₂ D₁ g
  have e3 : ∑ μ ∈ symmDiff D₁ D₂, g μ = ∑ μ ∈ D₁ \ D₂, g μ + ∑ μ ∈ D₂ \ D₁, g μ :=
    Finset.sum_union disjoint_sdiff_sdiff
  have e4 : ∑ μ ∈ D₁ ∩ D₂, g μ + ∑ μ ∈ D₁ ∩ D₂, g μ = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun μ _ => h2 _
  rw [Finset.inter_comm] at e2
  rw [← e1, ← e2, e3]
  have : ∑ μ ∈ D₁ ∩ D₂, g μ + ∑ μ ∈ D₁ \ D₂, g μ + (∑ μ ∈ D₁ ∩ D₂, g μ + ∑ μ ∈ D₂ \ D₁, g μ) =
      (∑ μ ∈ D₁ \ D₂, g μ + ∑ μ ∈ D₂ \ D₁, g μ) +
        (∑ μ ∈ D₁ ∩ D₂, g μ + ∑ μ ∈ D₁ ∩ D₂, g μ) := by abel
  rw [this, e4, add_zero]

theorem two_pow_le_of_avg [Finite Ω] [Finite M] (h2 : ∀ m : M, m + m = 0) {L : Subgroup H}
    (htrans : ∀ μ ν : Ω, ∃ l ∈ L, l • μ = ν) (hodd : Odd (Nat.card Ω))
    {ω₀ : Ω} {U : Subgroup H} (hUL : U ≤ L) (hU2 : IsPGroup 2 U) (hUfix : ∀ u ∈ U, u • ω₀ = ω₀)
    (hUtrans : ∀ μ ν : Ω, μ ≠ ω₀ → ν ≠ ω₀ → ∃ u ∈ U, u • μ = ν)
    {z : H} (hz : z * z = 1) (hzL : ∀ l ∈ L, z * l * z⁻¹ ∈ L)
    {X : AddSubgroup M} {c : M} (hXL : ∀ l ∈ L, ∀ x ∈ X, l • x ∈ X)
    (hcK : c ∈ commL M L) (hcX : c ∉ X)
    (hcfix : ∀ l ∈ L, l • ω₀ = ω₀ → l • c - c ∈ X)
    (hcz : ∀ l ∈ L, l • ω₀ = z • ω₀ → z • c - l • c ∈ X)
    (hXK : ∀ y ∈ commL M L, (∀ l ∈ L, l • y - y ∈ X) → y ∈ X) :
    2 ^ ((Nat.card Ω - Nat.card (MulAction.fixedBy Ω z)) / 2) ≤
      Nat.card (commSub (DistribMulAction.toAddEquiv M z)) := by
  classical
  haveI := Fintype.ofFinite Ω
  have hN : Nat.card Ω = Fintype.card Ω := Nat.card_eq_fintype_card
  rw [hN] at hodd ⊢
  obtain ⟨d, hd1, hdc, hd2⟩ := exists_d htrans ω₀ (S := {z}) (fun _ h => h ▸ hzL) hXL hcfix
    (fun _ h => h ▸ hcz)
  replace hd2 : ∀ μ, z • d μ - d (z • μ) ∈ X := hd2 z rfl
  obtain ⟨T, hTdisj, hTcard⟩ := exists_transversal (Ω := Ω) hz
  have hexp : (Fintype.card Ω - Nat.card (MulAction.fixedBy Ω z)) / 2 = T.card := by omega
  rw [hexp]
  have key : ∀ D : Finset Ω, D ⊆ T → D.Nonempty → ∑ μ ∈ D, (z • d μ - d μ) ∉ X := by
    intro D hDT hD hmem
    have hdisjD : Disjoint D (D.image (z • ·)) :=
      Finset.disjoint_of_subset_left hDT
        (Finset.disjoint_of_subset_right (Finset.image_subset_image hDT) hTdisj)
    refine sum_not_mem h2 htrans hodd hUL hU2 hUtrans hXL hcK hcX hXK hd1 hdc
      (B := D ∪ D.image (z • ·)) (hD.mono Finset.subset_union_left) ?_ ?_
    · rw [Finset.card_union_of_disjoint hdisjD,
        Finset.card_image_of_injective _ (MulAction.injective z)]
      exact ⟨D.card, rfl⟩
    · have e1 : ∑ ν ∈ D ∪ D.image (z • ·), d ν = ∑ μ ∈ D, d μ + ∑ μ ∈ D, d (z • μ) := by
        rw [Finset.sum_union hdisjD, Finset.sum_image fun a _ b _ h => MulAction.injective z h]
      have hBB : ∑ μ ∈ D, d μ + ∑ μ ∈ D, d μ = 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun μ _ => h2 _
      have e2 : ∑ μ ∈ D, d μ + ∑ μ ∈ D, d (z • μ) =
          ∑ μ ∈ D, (z • d μ - d μ) - ∑ μ ∈ D, (z • d μ - d (z • μ)) := by
        simp only [Finset.sum_sub_distrib]
        have : ∑ μ ∈ D, z • d μ - ∑ μ ∈ D, d μ - (∑ μ ∈ D, z • d μ - ∑ μ ∈ D, d (z • μ)) =
            ∑ μ ∈ D, d (z • μ) - ∑ μ ∈ D, d μ := by abel
        rw [this]
        have h3 : ∑ μ ∈ D, d (z • μ) - ∑ μ ∈ D, d μ =
            ∑ μ ∈ D, d μ + ∑ μ ∈ D, d (z • μ) - (∑ μ ∈ D, d μ + ∑ μ ∈ D, d μ) := by abel
        rw [h3, hBB, sub_zero]
      rw [e1, e2]
      exact X.sub_mem hmem (X.sum_mem fun μ _ => hd2 μ)
  have hΦ : ∀ D : Finset Ω,
      ∑ μ ∈ D, (z • d μ - d μ) ∈ commSub (DistribMulAction.toAddEquiv M z) := by
    intro D
    refine ⟨∑ μ ∈ D, d μ, ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => rfl
  have hinj : Set.InjOn (fun D : Finset Ω => ∑ μ ∈ D, (z • d μ - d μ))
      (T.powerset : Set (Finset Ω)) := by
    intro D₁ hD₁ D₂ hD₂ heq
    have hD₁T : D₁ ⊆ T := Finset.mem_powerset.mp hD₁
    have hD₂T : D₂ ⊆ T := Finset.mem_powerset.mp hD₂
    by_contra hne
    have hsd : (symmDiff D₁ D₂).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      exact fun h => hne (Finset.symmDiff_eq_empty.mp h)
    have hsdT : symmDiff D₁ D₂ ⊆ T := by
      intro μ hμ
      rcases Finset.mem_symmDiff.mp hμ with h | h
      · exact hD₁T h.1
      · exact hD₂T h.1
    have h0 : ∑ μ ∈ symmDiff D₁ D₂, (z • d μ - d μ) = 0 := by
      rw [sum_symmDiff_two h2 (fun μ => z • d μ - d μ) D₁ D₂]
      have heq' : ∑ μ ∈ D₁, (z • d μ - d μ) = ∑ μ ∈ D₂, (z • d μ - d μ) := heq
      rw [heq']
      exact h2 _
    exact key _ hsdT hsd (h0 ▸ X.zero_mem)
  let F : T.powerset → commSub (DistribMulAction.toAddEquiv M z) :=
    fun D => ⟨∑ μ ∈ (D : Finset Ω), (z • d μ - d μ), hΦ D⟩
  have hFinj : Function.Injective F := fun D₁ D₂ h =>
    Subtype.ext (hinj D₁.2 D₂.2 (congrArg Subtype.val h))
  have := Nat.card_le_card_of_injective F hFinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powerset] at this

end CFSG.Quasithin.F112Crit.PermBound

end

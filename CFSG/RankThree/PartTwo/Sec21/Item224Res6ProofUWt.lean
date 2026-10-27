module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUAux
public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofWt

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.Classical

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_lift_E9 {G : Type*} [Group G] [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZ3 : Nat.Coprime (Nat.card Z) 3) {E : Subgroup (G ⧸ Z)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ E₀ : Subgroup G, E₀.map (QuotientGroup.mk' Z) = E ∧ Nat.card E₀ = 9 ∧
      (∀ x ∈ E₀, x ^ 3 = 1) ∧ (∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) ∧
      ∀ x ∈ E₀, ∀ y ∈ E₀, QuotientGroup.mk' Z x = QuotientGroup.mk' Z y → x = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
  obtain ⟨E₀, hE₀3, hE₀map⟩ := exists_isPGroup_map_eq Z hE3
  have hker : ∀ x ∈ E₀, QuotientGroup.mk' Z x = 1 → x = 1 := by
    intro x hx hx1
    have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).mp hx1
    obtain ⟨k, hk⟩ := hE₀3 ⟨x, hx⟩
    have h1 : orderOf x ∣ 3 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hk
    have h2 : orderOf x ∣ Nat.card Z := by
      rw [← Subgroup.orderOf_mk x hxZ]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (3 ^ k) (Nat.card Z) := Nat.Coprime.pow_left k hZ3.symm
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hinj : ∀ x ∈ E₀, ∀ y ∈ E₀, QuotientGroup.mk' Z x = QuotientGroup.mk' Z y → x = y := by
    intro x hx y hy hxy
    have := hker (x * y⁻¹) (mul_mem hx (inv_mem hy)) (by rw [map_mul, map_inv, hxy,
      mul_inv_cancel])
    rwa [mul_inv_eq_one] at this
  refine ⟨E₀, hE₀map, ?_, ?_, ?_, hinj⟩
  ·
    have hbij : Function.Bijective ((QuotientGroup.mk' Z).subgroupMap E₀) := by
      refine ⟨fun a b hab => Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab)),
        (QuotientGroup.mk' Z).subgroupMap_surjective E₀⟩
    rw [← hE9, ← hE₀map]
    exact Nat.card_congr (Equiv.ofBijective _ hbij)
  · intro x hx
    apply hker _ (pow_mem hx 3)
    rw [map_pow]
    have hxE : QuotientGroup.mk' Z x ∈ E := hE₀map ▸ Subgroup.mem_map_of_mem _ hx
    exact hE.2 _ hxE
  · intro x hx y hy
    apply hinj _ (mul_mem hx hy) _ (mul_mem hy hx)
    have hxE : QuotientGroup.mk' Z x ∈ E := hE₀map ▸ Subgroup.mem_map_of_mem _ hx
    have hyE : QuotientGroup.mk' Z y ∈ E := hE₀map ▸ Subgroup.mem_map_of_mem _ hy
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hxE⟩ ⟨_, hyE⟩)

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
variable (h : UnitaryFieldData 2 f K) {n : ℕ}

@[expose] noncomputable def avgE (E₀ : Subgroup (uS h n)) [Fintype E₀] :
    Module.End K (Fin n → K) :=
  ∑ e : E₀, natRep (uS h n) (e : uS h n)

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem avgE_apply (E₀ : Subgroup (uS h n)) [Fintype E₀] (v : Fin n → K) :
    avgE h E₀ v = ∑ e : E₀, natRep (uS h n) (e : uS h n) v := by
  rw [avgE, LinearMap.sum_apply]

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem avgE_fixed (E₀ : Subgroup (uS h n)) [Fintype E₀] (v : Fin n → K) {e : uS h n}
    (he : e ∈ E₀) : natRep (uS h n) e (avgE h E₀ v) = avgE h E₀ v := by
  rw [avgE_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨e, he⟩ : E₀)) _ _ fun x => by
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply]

omit [Finite K] [Fact (Nat.Prime 2)] in
theorem nine_eq_one : (9 : K) = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination 4 * h2

omit [Finite K] [Fact (Nat.Prime 2)] in
theorem avgE_of_fixed (E₀ : Subgroup (uS h n)) [Fintype E₀] (hcard : Nat.card E₀ = 9)
    {m : Fin n → K} (hm : ∀ e ∈ E₀, natRep (uS h n) e m = m) : avgE h E₀ m = m := by
  rw [avgE_apply]
  simp only [fun e : E₀ => hm e e.2, Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, hcard, ← Nat.cast_smul_eq_nsmul K, Nat.cast_ofNat,
    nine_eq_one, one_smul]

theorem form_fixed_ker_avgE (E₀ : Subgroup (uS h n)) [Fintype E₀] (hcard : Nat.card E₀ = 9)
    {m : Fin n → K} (hm : ∀ e ∈ E₀, natRep (uS h n) e m = m) {w : Fin n → K}
    (hw : avgE h E₀ w = 0) : (uF h n).β m w = 0 := by
  classical
  have key : ∀ s : Finset E₀, (uF h n).β m (∑ e ∈ s, natRep (uS h n) (e : uS h n) w) =
      ∑ _e ∈ s, (uF h n).β m w := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, (uF h n).β_zero_right]
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, (uF h n).add_right, ih]
      congr 1
      have h1 := isIsometric_uS h (x : uS h n) m w
      rw [natRep_apply, natRep_apply] at h1
      rw [natRep_apply, ← h1]
      congr 1
      have := hm x x.2
      rw [natRep_apply] at this
      exact this.symm
  have h1 := key Finset.univ
  rw [← avgE_apply, hw, (uF h n).β_zero_right, Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, hcard, ← Nat.cast_smul_eq_nsmul K, Nat.cast_ofNat, nine_eq_one,
    one_smul] at h1
  exact h1.symm

theorem weights_uS (hf : Even f) (hn : n = 4 ∨ n = 5) (E₀ : Subgroup (uS h n)) [Fintype E₀]
    (hcard : Nat.card E₀ = 9) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) :
    (∀ s : uS h n, (∀ e ∈ E₀, s * e = e * s) → ∀ k : ℕ, s ^ 2 ^ k = 1 → s = 1) ∧
      finrank K (LinearMap.ker (avgE h E₀)) = 4 ∧
      ∀ m : Fin n → K, m ≠ 0 → (∀ e ∈ E₀, natRep (uS h n) e m = m) → (uF h n).β m m ≠ 0 := by
  classical
  let : CommGroup E₀ :=
    { (inferInstance : Group E₀) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  set ρ : E₀ →* Module.End K (Fin n → K) := (natRep (uS h n)).comp E₀.subtype with hρdef
  have : Finite (Additive E₀) := Finite.of_equiv E₀ Additive.ofMul
  have : Finite (Additive E₀ →+ ZMod 3) := Finite.of_injective _ DFunLike.coe_injective
  let : Fintype (Additive E₀ →+ ZMod 3) := Fintype.ofFinite _
  obtain ⟨ζ, hζ, hζq⟩ := exists_primitive_cube_root h hf
  have hσζ : (uF h n).σ ζ = ζ := by rw [uF_σ, UnitaryFieldData.bar_apply, hζq]
  have hρ : ∀ g u v, (uF h n).β (ρ g u) (ρ g v) = (uF h n).β u v := fun g u v =>
    isIsometric_uS h (g : uS h n) u v
  have hexpΓ : ∀ g : E₀, g ^ 3 = 1 := fun g => Subtype.ext (hexp g g.2)
  have hΓ : (Fintype.card E₀ : K) ≠ 0 := by
    rw [Fintype.card_eq_nat_card, hcard, Nat.cast_ofNat, nine_eq_one]
    exact one_ne_zero
  have hfaith : ∀ g : E₀, ρ g = 1 → g = 1 := by
    intro g hg
    apply Subtype.ext
    apply natRep_injective (uS h n)
    rw [Subgroup.coe_one, map_one]
    exact hg
  have hdim : finrank K (Fin n → K) = 4 ∨ finrank K (Fin n → K) = 5 := by
    rw [Module.finrank_fin_fun]
    exact hn
  obtain ⟨hle, hd0⟩ := weights_dim_four_five (uF h n) hζ hσζ hρ hexpΓ hΓ hcard hfaith hdim
  have hmem0 : ∀ v : Fin n → K, v ∈ charSpace ρ ζ (0 : Additive E₀ →+ ZMod 3) ↔
      ∀ e : E₀, natRep (uS h n) (e : uS h n) v = v := by
    intro v
    rw [mem_charSpace]
    simp [hρdef]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro s hs k hk
    apply natRep_injective (uS h n)
    rw [map_one]
    refine eq_one_of_commute_of_pow hζ hexpΓ hΓ hle (k := k) ?_ fun g => ?_
    · rw [← map_pow, hk, map_one]
    · change natRep (uS h n) s * natRep (uS h n) (g : uS h n) =
        natRep (uS h n) (g : uS h n) * natRep (uS h n) s
      rw [← map_mul, ← map_mul, hs g g.2]
  ·
    have hrange : LinearMap.range (avgE h E₀) = charSpace ρ ζ (0 : Additive E₀ →+ ZMod 3) := by
      apply le_antisymm
      · rintro _ ⟨v, rfl⟩
        rw [hmem0]
        intro e
        rw [avgE_apply, map_sum]
        exact Fintype.sum_equiv (Equiv.mulLeft e) _ _ fun x => by
          rw [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      · intro m hm
        rw [hmem0] at hm
        refine ⟨m, ?_⟩
        rw [avgE_apply]
        simp only [hm, Finset.sum_const, Finset.card_univ]
        rw [Fintype.card_eq_nat_card, hcard, ← Nat.cast_smul_eq_nsmul K, Nat.cast_ofNat,
          nine_eq_one, one_smul]
    have hrn := LinearMap.finrank_range_add_finrank_ker (avgE h E₀)
    rw [hrange, Module.finrank_fin_fun] at hrn
    have hd0' := hd0
    rw [Module.finrank_fin_fun] at hd0'
    omega
  ·
    intro m hm0 hmfix hmm
    have hm : m ∈ charSpace ρ ζ (0 : Additive E₀ →+ ZMod 3) :=
      (hmem0 m).mpr fun e => hmfix e e.2
    apply hm0
    apply (uF h n).nondeg m
    intro w
    apply (uF h n).refl
    refine form_eq_zero_of_forall_charSpace (ρ := ρ) (uF h n) hζ hexpΓ hΓ
      (fun ψ w' hw' => ?_) w
    by_cases hψ : ψ = 0
    · subst hψ
      have hspan : charSpace ρ ζ (0 : Additive E₀ →+ ZMod 3) = K ∙ m := by
        symm
        apply Submodule.eq_of_le_of_finrank_le
        · exact (Submodule.span_singleton_le_iff_mem m _).mpr hm
        · rw [finrank_span_singleton hm0]
          exact hle 0
      have hw'' : w' ∈ K ∙ m := hspan ▸ hw'
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw''
      rw [(uF h n).smul_left, hmm, mul_zero]
    · exact form_eq_zero_of_mem_charSpace (uF h n) hζ hσζ hρ (by rwa [add_zero]) hw' hm

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

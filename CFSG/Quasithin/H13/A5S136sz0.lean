module

public import CFSG.Quasithin.H13.KGFactSzCent
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.Quasithin.H13.A5.ConfSz

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin

variable {X : Type} [Group X] {n : ℕ}

theorem three_not_dvd_card (hX : IsSz n X) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := hX
  rw [Nat.card_congr e.toEquiv, suzuki_order hK]
  have h1 : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  set q := 2 ^ (2 * a + 1) with hq
  have h0 : 1 ≤ q := Nat.one_le_two_pow
  have hsq : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, h1]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h' | h'
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h' with h'' | h''
    · have := Nat.mod_eq_zero_of_dvd h''
      omega
    · have := Nat.mod_eq_zero_of_dvd h''
      omega
  · have := Nat.mod_eq_zero_of_dvd h'
    omega

theorem isSimpleGroup (hX : IsSz n X) : IsSimpleGroup X := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hX
  have := (suzuki_simple ha hK).2.2
  exact e.isSimpleGroup

theorem exists_conj_of_two_pow (hX : IsSz n X) (α : MulAut X)
    {k : ℕ} (hk : α ^ 2 ^ k = 1) : ∃ g : X, α = MulAut.conj g := by
  have hodd :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} X 2 n hX).1.2.2
  set β : CFSG.ComponentClassification.OuterAutomorphisms.Outer X := QuotientGroup.mk α
  have hβ : β ^ 2 ^ k = 1 := by rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have h1 : orderOf β ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hβ
  have h2 : orderOf β ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    orderOf_dvd_natCard β
  have hcop : Nat.Coprime (2 ^ k)
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h3 : orderOf β = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  have h4 : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
    (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp h3)
  obtain ⟨g, hg⟩ := h4
  exact ⟨g, hg.symm⟩

theorem exists_conj_suzukiU [Finite X] {a : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K) (P : Sylow 2 X) :
    ∃ g : X, ∀ x : X, x ∈ (P : Subgroup X) ↔ e (g * x * g⁻¹) ∈ suzukiU a K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set UX : Subgroup X := (suzukiU a K).comap e.toMonoidHom with hUX
  have hmemUX : ∀ y, y ∈ UX ↔ e y ∈ suzukiU a K := fun y => Iff.rfl
  have hUXcard : Nat.card UX = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [Nat.card_congr (e.toEquiv.subtypeEquiv hmemUX), (suzuki_unipotent_structure hK).2.1]
  have hXcard : Nat.card X = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv, suzuki_order hK]
  have hUXp : IsPGroup 2 UX := IsPGroup.of_card (n := (2 * a + 1) * 2) (by rw [hUXcard, pow_mul])
  have hUXidx : ¬ 2 ∣ UX.index := by
    have h1 := Subgroup.card_mul_index UX
    rw [hUXcard, hXcard, mul_assoc] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]
    have hq : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
    have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h3 | h3
    · omega
    · have : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 := dvd_pow hq (by norm_num)
      omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P (hUXp.toSylow hUXidx)
  have hcrit : ∀ y, y ∈ UX ↔ g⁻¹ * y * g ∈ (P : Subgroup X) := by
    intro y
    have h1 : ((g • P : Sylow 2 X) : Subgroup X) = UX := by
      rw [hg, IsPGroup.toSylow_coe]
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  refine ⟨g, fun x => ?_⟩
  rw [← hmemUX, hcrit]
  simp [mul_assoc]

theorem comm_of_sq_eq_one [Finite X] (hX : IsSz n X)
    (P : Sylow 2 X) {x y : X} (hx : x ∈ (P : Subgroup X)) (hx2 : x ^ 2 = 1)
    (hy : y ∈ (P : Subgroup X)) : x * y = y * x := by
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := hX
  obtain ⟨g, hg⟩ := exists_conj_suzukiU hK e P
  obtain ⟨u, v, huv⟩ := (mem_suzukiU_iff hK).1 ((hg x).1 hx)
  obtain ⟨c, d, hcd⟩ := (mem_suzukiU_iff hK).1 ((hg y).1 hy)
  have hu : u = 0 := by
    have h1 : e (g * x * g⁻¹) * e (g * x * g⁻¹) = 1 := by
      rw [← map_mul, show g * x * g⁻¹ * (g * x * g⁻¹) = g * x ^ 2 * g⁻¹ by rw [pow_two]; group,
        hx2, mul_one, mul_inv_cancel, map_one]
    rw [← huv, KGSz.suzukiSElt_sq hK, ← suzukiSElt_zero_zero hK (a := a), suzukiSElt_inj] at h1
    exact pow_eq_zero_iff (Nat.succ_ne_zero _) |>.mp h1.2
  have h2 : e (g * x * g⁻¹) * e (g * y * g⁻¹) = e (g * y * g⁻¹) * e (g * x * g⁻¹) := by
    rw [← huv, ← hcd, hu]
    exact suzukiSElt_zero_commute hK v c d
  rw [← map_mul, ← map_mul] at h2
  have h3 := e.injective h2
  calc x * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by rw [h3]
    _ = y * x := by group

theorem exists_two_involutions [Finite X] (hX : IsSz n X)
    (P : Sylow 2 X) : ∃ x ∈ (P : Subgroup X), ∃ y ∈ (P : Subgroup X),
      x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hX
  obtain ⟨g, hg⟩ := exists_conj_suzukiU hK e P
  obtain ⟨c, hc0, hc1⟩ : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
      intro c
      by_cases hc : c = 0
      · exact ⟨false, by simp [hc]⟩
      · exact ⟨true, by simp [h c hc]⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [hK, Nat.card_eq_fintype_card, Fintype.card_bool] at h1
    have h2 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set f : K → X := fun w => g⁻¹ * e.symm (suzukiSElt a K 0 w) * g with hf
  have hfP : ∀ w, f w ∈ (P : Subgroup X) := by
    intro w
    rw [hg, hf]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one, MulEquiv.apply_symm_apply]
    exact suzukiSElt_mem_suzukiU a K 0 w
  have hf2 : ∀ w, f w ^ 2 = 1 := by
    intro w
    have h1 : e.symm (suzukiSElt a K 0 w) ^ 2 = 1 := by
      rw [pow_two, ← map_mul, KGSz.suzukiSElt_sq hK, zero_pow (Nat.succ_ne_zero _),
        suzukiSElt_zero_zero hK, map_one]
    rw [hf, show (g⁻¹ * e.symm (suzukiSElt a K 0 w) * g) ^ 2 =
      g⁻¹ * e.symm (suzukiSElt a K 0 w) ^ 2 * g by rw [pow_two, pow_two]; group, h1]
    group
  have hfinj : ∀ w w', f w = f w' → w = w' := by
    intro w w' h
    have h1 : e.symm (suzukiSElt a K 0 w) = e.symm (suzukiSElt a K 0 w') := by
      have := congrArg (fun x => g * x * g⁻¹) h
      simpa [hf, mul_assoc] using this
    exact (suzukiSElt_inj.mp (e.symm.injective h1)).2
  have hf0 : f 0 = 1 := by
    rw [hf]
    simp [suzukiSElt_zero_zero hK]
  refine ⟨f 1, hfP 1, f c, hfP c, hf2 1, hf2 c, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact one_ne_zero (hfinj 1 0 (h.trans hf0.symm))
  · exact hc0 (hfinj c 0 (h.trans hf0.symm))
  · exact hc1 (hfinj 1 c h).symm

end CFSG.Quasithin.H13.A5.ConfSz

module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerProjectiveImage
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerOvergroupArithmetic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.ShultStronglyClosedTI.Singer Module

theorem lt_pow_sub_one {N t r : ℕ} (hN : 2 ^ r ≤ N) (hN2 : 2 ≤ N) (ht : 2 ≤ t) :
    t * r * (N - 1) < N ^ t - 1 := by
  have h2r : 2 * r ≤ N := (two_mul_le_two_pow r).trans hN
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hpow : (s + 2) * (M + 1) ^ 2 ≤ 2 * (M + 1) ^ (s + 2) := by
    have h1 : 2 ^ s ≤ (M + 1) ^ s := Nat.pow_le_pow_left (by omega) s
    have h2 : s + 2 ≤ 2 ^ (s + 1) := Nat.lt_two_pow_self
    calc (s + 2) * (M + 1) ^ 2 ≤ 2 ^ (s + 1) * (M + 1) ^ 2 := Nat.mul_le_mul_right _ h2
      _ = 2 * 2 ^ s * (M + 1) ^ 2 := by ring
      _ ≤ 2 * (M + 1) ^ s * (M + 1) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      _ = 2 * (M + 1) ^ (s + 2) := by ring
  have h3 : 2 * r * ((s + 2) * M) ≤ (M + 1) * ((s + 2) * M) := Nat.mul_le_mul_right _ h2r
  have h4 : 4 ≤ (s + 2) * (M + 1) := by nlinarith
  rw [Nat.add_sub_cancel]
  have : (s + 2) * r * M + 1 < (M + 1) ^ (s + 2) := by nlinarith
  omega

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem linear_of_comm {h : F ≃ₗ[k] F} {q : F} (hq : ∀ x, h (q * x) = q * h x) :
    ∀ a ∈ IntermediateField.adjoin k {q}, ∀ x, h (a * x) = a * h x := by
  let A : IntermediateField k F :=
    { carrier := {a | ∀ x, h (a * x) = a * h x}
      mul_mem' := fun {a b} ha hb x => by rw [mul_assoc, ha, hb, mul_assoc]
      one_mem' := fun x => by rw [one_mul, one_mul]
      add_mem' := fun {a b} ha hb x => by rw [add_mul, map_add, ha, hb, add_mul]
      zero_mem' := fun x => by rw [zero_mul, map_zero, zero_mul]
      algebraMap_mem' := fun r x => by rw [← Algebra.smul_def, map_smul, Algebra.smul_def]
      inv_mem' := fun a ha x => by
        by_cases h0 : a = 0
        · rw [h0, inv_zero, zero_mul, map_zero, zero_mul]
        · have e := ha (a⁻¹ * x)
          rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul] at e
          rw [e, ← mul_assoc, inv_mul_cancel₀ h0, one_mul] }
  have hle : IntermediateField.adjoin k {q} ≤ A := IntermediateField.adjoin_simple_le_iff.mpr hq
  exact fun a ha => hle ha

theorem card_le_card_sub_one_of_gen [Finite F] {Q : Subgroup Fˣ} {q : Q}
    (hq : ∀ u : Q, u ∈ Subgroup.zpowers q) {K₀ : IntermediateField k F}
    (hqK : ((q : Fˣ) : F) ∈ K₀) : Nat.card Q ≤ Nat.card K₀ - 1 := by
  have hmem : ∀ u : Q, ((u : Fˣ) : F) ∈ K₀ := by
    intro u
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hq u)
    rw [← hn, Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val]
    exact zpow_mem hqK n
  rw [← Nat.card_units]
  refine Nat.card_le_card_of_injective
    (fun u => Units.mk0 (⟨((u : Fˣ) : F), hmem u⟩ : K₀) fun h0 => ?_) fun u v huv => ?_
  · exact (u : Fˣ).ne_zero (congrArg Subtype.val h0)
  · have h1 := congrArg (fun w : K₀ˣ => ((w : K₀) : F)) huv
    simp only [Units.val_mk0] at h1
    exact Subtype.ext (Units.ext h1)

theorem normalizes_of_conj_le [Finite F] {G₁ : Subgroup (F ≃ₗ[k] F)}
    (hN : ∀ h ∈ G₁, ∀ c : Fˣ, ∃ c' : Fˣ, ∀ x, h (c * x) = c' * h x)
    {g : F ≃ₗ[k] F} (hg : ∀ c : Fˣ, g * scalarHom k F c * g⁻¹ ∈ G₁) (c : Fˣ) :
    ∃ c' : Fˣ, ∀ x, g (c * x) = c' * g x := by
  have : FiniteDimensional k F := Module.Finite.of_finite
  have : Finite k := Finite.of_injective _ (algebraMap k F).injective
  have : Finite (F ≃ₗ[k] F) :=
    Finite.of_injective (fun g : F ≃ₗ[k] F => (g : F → F)) fun g h hgh =>
      LinearEquiv.ext (congrFun hgh)
  set T : Subgroup (F ≃ₗ[k] F) := (scalars k F).map (MulAut.conj g).toMonoidHom with hT
  have hTG : T ≤ G₁ := by
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact hg c
  have hσT : ∀ h ∈ T, ∃ σ : (⊤ : IntermediateField k F) ≃ₐ[k] (⊤ : IntermediateField k F),
      ∀ (a : (⊤ : IntermediateField k F)) (x : F), h (a * x) = σ a * h x := by
    intro h hh
    apply exists_algEquiv_of_normalizes ⊤ h
    intro a _
    by_cases ha : a = 0
    · exact ⟨0, IntermediateField.zero_mem _, fun x => by rw [ha, zero_mul, map_zero, zero_mul]⟩
    · obtain ⟨c', hc'⟩ := hN h (hTG hh) (Units.mk0 a ha)
      exact ⟨c', IntermediateField.mem_top, hc'⟩
  obtain ⟨T₁, hT₁T, hT₁lin, -, d, hd, hcardT⟩ := exists_card_eq_mul_of_semilinear T ⊤ hσT
  rw [IntermediateField.finrank_top'] at hd
  set Q₀ : Subgroup Fˣ := T.comap (scalarHom k F) with hQ₀
  have hT₁Q : T₁ ≤ Q₀.map (scalarHom k F) := by
    intro h hh
    have h10 : h 1 ≠ 0 := fun h0 => one_ne_zero (h.injective (h0.trans h.map_zero.symm))
    have heq : scalarHom k F (Units.mk0 (h 1) h10) = h := by
      refine LinearEquiv.ext fun x => ?_
      have e := hT₁lin h hh ⟨x, IntermediateField.mem_top⟩ 1
      rw [mul_one] at e
      rw [scalarHom_apply, Units.val_mk0, mul_comm]
      exact e.symm
    refine ⟨Units.mk0 (h 1) h10, ?_, heq⟩
    show scalarHom k F (Units.mk0 (h 1) h10) ∈ T
    rw [heq]
    exact hT₁T hh
  have hcardQ : Nat.card T₁ ≤ Nat.card Q₀ := by
    have := Subgroup.card_le_of_le hT₁Q
    rwa [Subgroup.card_map_of_injective scalarHom_injective] at this
  have hcardT' : Nat.card T = Nat.card F - 1 := by
    rw [hT, Subgroup.card_map_of_injective (MulAut.conj g).injective, scalars,
      MonoidHom.range_eq_map, Subgroup.card_map_of_injective scalarHom_injective,
      Subgroup.card_top, Nat.card_units]
  have hQm : Nat.card F - 1 ≤ Nat.card Q₀ * finrank k F := by
    rw [← hcardT', hcardT]
    exact Nat.mul_le_mul hcardQ hd
  have : IsCyclic Q₀ := isCyclic_subgroup_units Q₀
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := Q₀)
  by_cases hK : IntermediateField.adjoin k {((q : Fˣ) : F)} = ⊤
  ·
    set h := g * scalarHom k F c * g⁻¹ with hh
    have hcomm : h * scalarHom k F (q : Fˣ) = scalarHom k F (q : Fˣ) * h := by
      obtain ⟨_, ⟨c₂, rfl⟩, h2⟩ := (q.2 : scalarHom k F (q : Fˣ) ∈ T)
      have e : h = MulAut.conj g (scalarHom k F c) := rfl
      rw [e, ← h2]
      change MulAut.conj g (scalarHom k F c) * MulAut.conj g (scalarHom k F c₂) =
        MulAut.conj g (scalarHom k F c₂) * MulAut.conj g (scalarHom k F c)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm c c₂]
    have hlin : ∀ x, h (((q : Fˣ) : F) * x) = ((q : Fˣ) : F) * h x := fun x => by
      have e := LinearEquiv.congr_fun hcomm x
      simpa only [LinearEquiv.mul_apply, scalarHom_apply] using e
    have hF := linear_of_comm hlin
    rw [hK] at hF
    have h10 : h 1 ≠ 0 := fun h0 => one_ne_zero (h.injective (h0.trans h.map_zero.symm))
    refine ⟨Units.mk0 (h 1) h10, fun x => ?_⟩
    have e1 : g ((c : F) * x) = h (g x) := by
      rw [hh, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
        LinearEquiv.symm_apply_apply, scalarHom_apply]
    have e2 := hF (g x) IntermediateField.mem_top 1
    rw [mul_one] at e2
    rw [e1, e2, Units.val_mk0, mul_comm]
  ·
    exfalso
    set K₀ := IntermediateField.adjoin k {((q : Fˣ) : F)} with hK₀
    have hQK := card_le_card_sub_one_of_gen hq (IntermediateField.mem_adjoin_simple_self k _)
    have ht : 2 ≤ finrank K₀ F := by
      have h1 : finrank K₀ F ≠ 1 := fun h1 => hK (IntermediateField.finrank_eq_one_iff_eq_top.mp h1)
      have := Module.finrank_pos (R := K₀) (M := F)
      omega
    have hF := Module.natCard_eq_pow_finrank (K := K₀) (V := F)
    have hK₀ := Module.natCard_eq_pow_finrank (K := k) (V := K₀)
    have hk2 : 2 ≤ Nat.card k := Finite.one_lt_card
    have hr : 2 ^ finrank k K₀ ≤ Nat.card K₀ := by
      rw [hK₀]
      exact Nat.pow_le_pow_left hk2 _
    have hN2 : 2 ≤ Nat.card K₀ := Finite.one_lt_card
    have htower := Module.finrank_mul_finrank k K₀ F
    have hlt := lt_pow_sub_one hr hN2 ht
    rw [← hF] at hlt
    have hle : (Nat.card K₀ - 1) * finrank k F ≤
        finrank K₀ F * finrank k K₀ * (Nat.card K₀ - 1) := by
      rw [← htower]
      exact le_of_eq (by ring)
    have hchain : Nat.card F - 1 < Nat.card F - 1 :=
      calc Nat.card F - 1 ≤ Nat.card Q₀ * finrank k F := hQm
        _ ≤ (Nat.card K₀ - 1) * finrank k F := Nat.mul_le_mul_right _ hQK
        _ ≤ finrank K₀ F * finrank k K₀ * (Nat.card K₀ - 1) := hle
        _ < Nat.card F - 1 := hlt
    exact lt_irrefl _ hchain

end CFSG.Quasithin.Vol2.Ch10.V1C

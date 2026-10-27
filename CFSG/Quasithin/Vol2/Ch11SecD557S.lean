module

public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Vol2.Ch11SecD557N
public import CFSG.Quasithin.Vol2.Ch11SecD557NatA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)

theorem exists_sub_eq_of_order_three {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {M : Matrix (Fin 2) (Fin 2) F} (hdet : M.det = 1) (h3 : M ^ 3 = 1) (hne : M ≠ 1)
    (w : Fin 2 → F) : ∃ v, M.mulVec v - v = w := by
  have hdetN : (M - 1).det ≠ 0 := by
    intro h0
    rw [Matrix.det_fin_two] at h0 hdet
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide :
      (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h0
    have htr : M 0 0 + M 1 1 = 0 := by linear_combination -h0 + hdet + h2
    have hM2 : M ^ 2 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (M 0 0) * htr - hdet - h2
      · simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (M 0 1) * htr
      · simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (M 1 0) * htr
      · simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (M 1 1) * htr - hdet - h2
    apply hne
    calc M = M ^ 2 * M := by rw [hM2, one_mul]
      _ = M ^ 3 := by rw [← pow_succ]
      _ = 1 := h3
  have hU : IsUnit (M - 1).det := isUnit_iff_ne_zero.mpr hdetN
  refine ⟨(M - 1)⁻¹.mulVec w, ?_⟩
  rw [show M.mulVec ((M - 1)⁻¹.mulVec w) - (M - 1)⁻¹.mulVec w =
      (M - 1).mulVec ((M - 1)⁻¹.mulVec w) by rw [Matrix.sub_mulVec, Matrix.one_mulVec],
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]

variable {G : Type} [Group G] [Finite G]

theorem mem_of_forall_conj_eq_of_natural {K U V₁ : Subgroup G} {s : ℕ} (W : Fin s → Subgroup G)
    {F : Type} [Field F] (h2 : (2 : F) = 0) (hW : ∀ i, W i ≤ U) (hV₁U : V₁ ≤ U)
    (hsup : V₁ ⊔ ⨆ i, W i = U)
    (hnat : ∀ i, IsNaturalSection K (W i) V₁ (CFSG.pCore 2 ↥K) (StatedSL 2 F))
    (hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ V₁)
    (hUV₁ : U ≤ Subgroup.normalizer (V₁ : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hKV₁ : K ≤ Subgroup.normalizer (V₁ : Set G))
    (hK3 : 3 ∣ Nat.card K) {c : G} (hc : c ∈ U) (hcK : ∀ k ∈ K, k * c * k⁻¹ = c) :
    c ∈ V₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 hK3
  have hkO : k ∉ CFSG.pCore 2 ↥K := by
    intro hkO
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨k, hkO⟩
    have h1 : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hm
      simpa using this)
    rw [hk] at h1
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1) (by norm_num)
  have : (V₁.subgroupOf U).Normal := normal_subgroupOf_of_le hV₁U hUV₁
  have hEcomm : ∀ a b : ↥U ⧸ V₁.subgroupOf U, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
          Subgroup.coe_mul]
        have h1 := hUcomm _ (U.inv_mem b.2) _ (U.inv_mem a.2)
        convert h1 using 1
        group
  let ρ := quotAct hKU hKV₁
  let φ : (↥U ⧸ V₁.subgroupOf U) →* (↥U ⧸ V₁.subgroupOf U) :=
    { toFun := fun e => ρ k e * e⁻¹
      map_one' := by rw [map_one, inv_one, mul_one]
      map_mul' := fun a b => by
        rw [map_mul, mul_inv_rev]
        calc ρ k a * ρ k b * (b⁻¹ * a⁻¹) = ρ k a * (ρ k b * (a⁻¹ * b⁻¹)) := by
              rw [mul_assoc, hEcomm b⁻¹ a⁻¹]
          _ = ρ k a * ((a⁻¹ * ρ k b) * b⁻¹) := by rw [← mul_assoc (ρ k b), hEcomm (ρ k b) a⁻¹]
          _ = ρ k a * a⁻¹ * (ρ k b * b⁻¹) := by simp only [mul_assoc] }
  have hφsurj : Function.Surjective φ := by
    let B : Subgroup G :=
      ((φ.range).comap (QuotientGroup.mk' (V₁.subgroupOf U))).map U.subtype
    have hBU : U ≤ B := by
      rw [← hsup]
      refine sup_le (fun v hv => ⟨⟨v, hV₁U hv⟩, ?_, rfl⟩) (iSup_le fun i w hw => ?_)
      · have h1 : (QuotientGroup.mk' (V₁.subgroupOf U) ⟨v, hV₁U hv⟩ :
            ↥U ⧸ V₁.subgroupOf U) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hv)
        show QuotientGroup.mk' (V₁.subgroupOf U) ⟨v, hV₁U hv⟩ ∈ φ.range
        rw [h1]
        exact φ.range.one_mem
      · obtain ⟨hKW, α, -, hαk, β, hβs, hβk, hβe⟩ := hnat i
        set M := (((α k : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hMdef
        have hdet : M.det = 1 := by
          rw [hMdef, ← coe_statedSLEquiv']
          exact (statedSLEquiv' 2 F (α k)).2
        have hM3 : M ^ 3 = 1 := by
          have h1 : α k ^ 3 = 1 := by rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
          have h3 := congrArg (fun g : ↥(StatedSL 2 F) =>
            ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h1
          simpa using h3
        have hMne : M ≠ 1 := by
          intro h1
          apply hkO
          rw [← hαk, MonoidHom.mem_ker]
          exact Subtype.ext (Units.ext (h1.trans (by simp)))
        obtain ⟨v, hv⟩ := exists_sub_eq_of_order_three h2 hdet hM3 hMne
          (Multiplicative.toAdd (β ⟨w, hw⟩))
        obtain ⟨w', hw'⟩ := hβs (Multiplicative.ofAdd v)
        have hw''W : (k : G) * w' * (k : G)⁻¹ ∈ W i :=
          (Subgroup.mem_normalizer_iff.mp (hKW k.2) w').mp w'.2
        have hβw'' := hβe k w' ⟨_, hw''W⟩ rfl
        have hβeq : β (⟨_, hw''W⟩ * w'⁻¹) = β ⟨w, hw⟩ := by
          apply Multiplicative.toAdd.injective
          rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hβw'', hw', toAdd_ofAdd,
            ← sub_eq_add_neg, hv]
        have hker : ((⟨_, hw''W⟩ * w'⁻¹)⁻¹ * ⟨w, hw⟩ : ↥(W i)) ∈ β.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hβeq, inv_mul_cancel]
        rw [hβk, Subgroup.mem_subgroupOf] at hker
        refine ⟨⟨w, hW i hw⟩, ⟨QuotientGroup.mk ⟨w', hW i w'.2⟩, ?_⟩, rfl⟩
        show ρ k (QuotientGroup.mk ⟨w', hW i w'.2⟩) * (QuotientGroup.mk ⟨w', hW i w'.2⟩)⁻¹ =
          QuotientGroup.mk' (V₁.subgroupOf U) ⟨w, hW i hw⟩
        rw [quotAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.mk'_apply,
          QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_coe_apply] at hker ⊢
        exact hker
    intro e
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective e
    obtain ⟨u', hu', hu'u⟩ := hBU u.2
    have h1 : u' = u := Subtype.ext hu'u
    rw [← h1]
    exact hu'
  have hφinj : Function.Injective φ := Finite.injective_iff_surjective.mpr hφsurj
  have h1 : φ (QuotientGroup.mk ⟨c, hc⟩) = φ 1 := by
    show ρ k (QuotientGroup.mk ⟨c, hc⟩) * (QuotientGroup.mk ⟨c, hc⟩)⁻¹ = ρ k 1 * 1⁻¹
    have e : conjAct U ⟨k, hKU k.2⟩ ⟨c, hc⟩ = ⟨c, hc⟩ :=
      Subtype.ext (by rw [conjAct_coe_apply]; exact hcK k k.2)
    rw [quotAct_mk, e, map_one, inv_one, mul_one, mul_inv_cancel]
  have h3 := hφinj h1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

end CFSG.Quasithin.Vol2.Ch11.SecD

module

public import CFSG.Quasithin.H13.L32NSet14Act

public section

namespace CFSG.Quasithin.H13.L32NSet14

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem sl2_eq_one_of_conj : ∀ s r : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), r ^ 3 = 1 →
    r ≠ 1 → s ^ 2 = 1 → (s * (r * s * r⁻¹)) ^ 2 = 1 → s = 1 := by
  decide

theorem sl2_sq_of_two {s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)} {k : ℕ}
    (h : s ^ 2 ^ k = 1) : s ^ 2 = 1 := by
  have h6 := orderOf_dvd_of_pow_eq_one (sl2_pow_six s)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  have hi1 : i ≤ 1 := by
    by_contra hlt
    push Not at hlt
    exact absurd ((Nat.pow_dvd_pow 2 hlt).trans (hi ▸ h6)) (by decide)
  refine orderOf_dvd_iff_pow_eq_one.mp ?_
  rw [hi]
  simpa using Nat.pow_dvd_pow 2 hi1

theorem mem_smul_sylow {X : Type*} [Group X] {p : ℕ} {P : Sylow p X} {g x : X} :
    x ∈ g • P ↔ g⁻¹ * x * g ∈ P := by
  show x ∈ ((g • P : Sylow p X) : Subgroup X) ↔ g⁻¹ * x * g ∈ (P : Subgroup X)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

namespace Setting

variable [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V] (S : Setting G T L V V₂)
include S

theorem pCoreOf_L1T_le : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ trivSub V (fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ⟩ := S.exists_rep
  have hHX : L₁Of L (fsuV1 T V) ⊔ T ≤ nX T V := sup_le S.L1_le_X S.T_le_X
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S.exists_basis
  obtain ⟨x, hxL, -, hxa, -⟩ := S.exists_x hz hz1 ha haV hb hbV
  have hψx : ψ ⟨x, S.L1_le_X hxL⟩ ≠ 1 := by
    rw [Ne, hψ]
    intro h
    have h1 := h.2.2 a (S.hV2.2.1 ha)
    rw [hxa] at h1
    apply hbV
    have h2 := mul_mem (S.hV2.1 h1) ha
    rwa [inv_mul_cancel_right] at h2
  have h2el : ∀ q (hq : q ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)),
      ψ ⟨q, hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq)⟩ ^ 2 = 1 := by
    intro q hq
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (L₁Of L (fsuV1 T V) ⊔ T)) ⟨q, hq⟩
    refine sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have : (⟨q, hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq)⟩ : ↥(nX T V)) ^ 2 ^ k = 1 :=
      Subtype.ext (by
        have := congrArg Subtype.val hk
        rw [Subgroup.coe_pow] at this ⊢
        exact this)
    rw [this, map_one]
  intro q hq
  have hq' : x * q * x⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (mem_sup_left hxL)) q).mp hq
  have hqq := h2el _ (mul_mem hq hq')
  have e : (⟨q * (x * q * x⁻¹), hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 _
      (mul_mem hq hq'))⟩ : ↥(nX T V)) = ⟨q, hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq)⟩ *
        (⟨x, S.L1_le_X hxL⟩ * ⟨q, hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq)⟩ *
          (⟨x, S.L1_le_X hxL⟩ : ↥(nX T V))⁻¹) := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv] at hqq
  exact (hψ _).mp (sl2_eq_one_of_conj _ _ (S.cube_eq_one ψ hxL) hψx (h2el q hq) hqq)

theorem exists_swap {z a b : G} (hz : z ∈ fsuV1 T V) (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (hb : b ∈ V) (hbV : b ∉ V₂) :
    ∃ y ∈ L, y ^ 2 ∈ centralizer (V : Set G) ∧ y * z * y⁻¹ = z ∧ y * a * y⁻¹ = b := by
  let _ := zmodModuleOf (fun v hv => S.sq_V hv)
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := S.hV2.1 hz
  have haV' : a ∈ V := S.hV2.2.1 ha
  let c : Additive ↥V → G := fun q => ((Additive.toMul q : ↥V) : G)
  have hcadd : ∀ q r, c (q + r) = c q * c r := fun _ _ => rfl
  have hself : ∀ q : Additive ↥V, q + q = 0 := fun q => by
    apply Additive.toMul.injective
    apply Subtype.ext
    show c q * c q = 1
    exact S.mul_self_V (Additive.toMul q).2
  set z' : Additive ↥V := Additive.ofMul ⟨z, hzV⟩
  set a' : Additive ↥V := Additive.ofMul ⟨a, haV'⟩
  set b' : Additive ↥V := Additive.ofMul ⟨b, hb⟩
  have hnot : a' ∉ (ZMod 2) ∙ z' ⊔ (ZMod 2) ∙ (a' + b') := fun h => by
    rcases mem_span_pair_zmod2 h with h | h | h | h
    · exact haV (by rw [show a = 1 from congrArg c h]; exact one_mem _)
    · exact haV (by rw [show a = z from congrArg c h]; exact hz)
    · have e : a = a * b := (congrArg c h).trans (hcadd _ _)
      have e' : b = a⁻¹ * (a * b) := by group
      rw [← e, inv_mul_cancel] at e'
      exact hbV (e' ▸ one_mem _)
    · have e : a = z * (a * b) := (congrArg c h).trans (by rw [hcadd, hcadd]; rfl)
      have e' : b = (z * a)⁻¹ * (z * (a * b)) := by group
      rw [← e] at e'
      exact hbV (e' ▸ mul_mem (inv_mem (mul_mem hzV₂ ha)) ha)
  obtain ⟨f, hfa, hker⟩ := Submodule.exists_le_ker_of_notMem hnot
  have h01 : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
  have hf1 : f a' = 1 := (h01 _).resolve_left hfa
  have hfz : f z' = 0 := hker (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
  have hfab : f (a' + b') = 0 :=
    hker (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  let τ : Additive ↥V →ₗ[ZMod 2] Additive ↥V := LinearMap.id + f.smulRight (a' + b')
  have hτ : ∀ v, τ v = v + f v • (a' + b') := fun v => rfl
  have hinv : Function.Involutive τ := fun v => by
    rw [hτ, hτ, map_add, map_smul, hfab, smul_zero, add_zero, add_assoc, hself, add_zero]
  obtain ⟨y, hyL, hy⟩ := S.exists_lift (LinearEquiv.ofInvolutive τ hinv)
  have hyτ : ∀ v (hv : v ∈ V),
      y * v * y⁻¹ = ((Additive.toMul (τ (Additive.ofMul ⟨v, hv⟩)) : ↥V) : G) := hy
  refine ⟨y, hyL, ?_, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro v hv
    have e : y ^ 2 * v * (y ^ 2)⁻¹ = v := by
      have e1 : y ^ 2 * v * (y ^ 2)⁻¹ = y * (y * v * y⁻¹) * y⁻¹ := by
        rw [pow_two]
        group
      rw [e1, hyτ v hv, hyτ _ (Additive.toMul (τ (Additive.ofMul ⟨v, hv⟩))).2]
      show c (τ (τ (Additive.ofMul ⟨v, hv⟩))) = v
      rw [hinv]
      rfl
    calc v * y ^ 2 = (y ^ 2 * v * (y ^ 2)⁻¹) * y ^ 2 := by rw [e]
      _ = y ^ 2 * v := by group
  · rw [hyτ z hzV]
    show c (τ z') = z
    rw [hτ, hfz, zero_smul, add_zero]
    rfl
  · rw [hyτ a haV']
    show c (τ a') = b
    rw [hτ, hf1, one_smul, ← add_assoc, hself, zero_add]
    rfl

theorem exists_T_not_triv : ∃ t ∈ T, t ∉ trivSub V (fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S.exists_basis
  obtain ⟨y, hyL, hy2, hyz, hya⟩ := S.exists_swap hz ha haV hb hbV
  have hyX : y ∈ nX T V := ⟨S.LV hyL, S.mem_g1 hz hz1 hyz⟩
  have hy_not : y ∉ trivSub V (fsuV1 T V) := fun h => by
    have h1 := h.2.2 a (S.hV2.2.1 ha)
    rw [hya] at h1
    apply hbV
    have h2 := mul_mem (S.hV2.1 h1) ha
    rwa [inv_mul_cancel_right] at h2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, y ^ 2 ^ m = 1 := by
    have hc : y ^ 2 ∈ pCoreOf 2 L := by
      rw [← S.cent_eq]
      exact ⟨L.pow_mem hyL 2, hy2⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hc⟩
    refine ⟨k + 1, ?_⟩
    have := congrArg Subtype.val hk
    rw [Subgroup.coe_pow] at this
    rw [pow_succ', pow_mul]
    exact this
  have hTp : IsPGroup 2 ↥(T.subgroupOf (nX T V)) := by
    rintro ⟨t, ht⟩
    obtain ⟨k, hk⟩ := S.hH.sylow.1 ⟨t, Subgroup.mem_subgroupOf.mp ht⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hTidx : ¬ 2 ∣ (T.subgroupOf (nX T V)).index := by
    have h1 := Subgroup.relIndex_mul_index S.T_le_X
    intro h2
    apply S.hH.sylow.2
    rw [← h1]
    exact Dvd.dvd.mul_right h2 _
  have hyp : IsPGroup 2 ↥(zpowers (⟨y, hyX⟩ : ↥(nX T V))) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨m, Subtype.ext ?_⟩
    have hm' : (⟨y, hyX⟩ : ↥(nX T V)) ^ 2 ^ m = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hm)
    show ((⟨y, hyX⟩ : ↥(nX T V)) ^ n) ^ 2 ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm', one_zpow]
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(nX T V) Q (hTp.toSylow hTidx)
  have hmem : g * ⟨y, hyX⟩ * g⁻¹ ∈ g • Q := mem_smul_sylow.mpr (by
    rw [show g⁻¹ * (g * ⟨y, hyX⟩ * g⁻¹) * g = ⟨y, hyX⟩ by group]
    exact hQ (mem_zpowers _))
  rw [hg] at hmem
  have hmem' : g * ⟨y, hyX⟩ * g⁻¹ ∈ T.subgroupOf (nX T V) := hmem
  refine ⟨(g : G) * y * (g : G)⁻¹, Subgroup.mem_subgroupOf.mp hmem', fun h => hy_not ?_⟩
  have := conj_mem_trivSub (inv_mem g.2.1) (inv_mem g.2.2) h
  rwa [show (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G)⁻¹⁻¹ = y by group] at this

theorem index2_eq : (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).relIndex T = 2 := by
  have h2 := S.index2_le
  obtain ⟨t, htT, htnot⟩ := S.exists_T_not_triv
  have h1 : (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).relIndex T ≠ 1 := fun h =>
    htnot (S.pCoreOf_L1T_le (Subgroup.relIndex_eq_one.mp h htT))
  have h0 : (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).relIndex T ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  omega

end Setting

end CFSG.Quasithin.H13.L32NSet14

module

public import CFSG.Milestones.ASVolI.F429.C6Sp4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {E : Type} [Group E]

theorem burnsideF429_c2ab_of_hom {S T : Subgroup E} {Q : Type*} [Group Q] (π : E →* Q)
    (hST : S ≤ T) (hker : ∀ r ∈ T, π r = 1 → r ∈ S) (hS1 : ∀ s ∈ S, π s = 1) {t₁ : E}
    (ht₁T : t₁ ∈ T) (hgen : Subgroup.zpowers (π t₁) = T.map π)
    (hord : t₁ ^ orderOf (π t₁) = 1) :
    (∃ t ∈ T, T = Subgroup.zpowers t ⊔ S) ∧ ∃ H : Subgroup E, IsComplementIn H S T := by
  have hpow : ∀ r ∈ T, ∃ n : ℤ, π t₁ ^ n = π r := fun r hr =>
    Subgroup.mem_zpowers_iff.mp (by rw [hgen]; exact ⟨r, hr, rfl⟩)
  have hsplit : ∀ r ∈ T, ∃ n : ℤ, r * t₁ ^ (-n) ∈ S ∧ r = r * t₁ ^ (-n) * t₁ ^ n := by
    intro r hr
    obtain ⟨n, hn⟩ := hpow r hr
    refine ⟨n, hker _ (T.mul_mem hr (T.zpow_mem ht₁T _)) ?_, by group⟩
    rw [map_mul, map_zpow, ← hn, ← zpow_add, add_neg_cancel, zpow_zero]
  refine ⟨⟨t₁, ht₁T, le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr ht₁T) hST)⟩,
    ⟨Subgroup.zpowers t₁, hST, Subgroup.zpowers_le.mpr ht₁T, ?_, ?_⟩⟩
  · intro r hr
    obtain ⟨n, hnS, hn⟩ := hsplit r hr
    have h := Subgroup.mul_mem_sup hnS (Subgroup.zpow_mem_zpowers t₁ n)
    rw [← hn, sup_comm] at h
    exact h
  · rw [eq_bot_iff]
    rintro x ⟨hxS, hxH⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxH
    have h1 : π t₁ ^ n = 1 := by rw [← map_zpow]; exact hS1 _ hxS
    obtain ⟨c, rfl⟩ := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [Subgroup.mem_bot, zpow_mul, zpow_natCast, hord, one_zpow]
  · intro g hg
    obtain ⟨n, hnS, hn⟩ := hsplit g hg
    exact ⟨g * t₁ ^ (-n), hnS, t₁ ^ n, Subgroup.zpow_mem_zpowers t₁ n, hn.symm⟩

end Generic

section L3

open CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3
  CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.QTGen4.DSGen4.L34

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}


theorem burnsideF429_c2ab_L3 {f : ℕ} (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    (∃ t ∈ T, T = Subgroup.zpowers t ⊔ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
      ∃ H : Subgroup E, IsComplementIn H (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, hFf, hFfin, hFchar, Φ, ρ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hρ, hΦρ, hE, hD, hO,
    h₁, h₂, -⟩ := burnsideF447_setup hf hyp.toHypF_4_4g
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hNp := burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ := by
    have hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := burnsideF4d_Y2_pCore_le hf hyp.toHypF_4_4g
    rw [burnsideF4d_pCoreOf_inf_eq (M₁ ⊓ M₂) hle]
    exact hNp.2
  have C : burnsideF447_Ctx f Φ ρ Gp := ⟨hf, hFcard, hΦ, hρ, hrange, hΦρ, hE⟩
  have hTG := burnsideF429_T_inf_Gp hyp hT
  have hST := burnsideF429_sbar_le (Gp := Gp) hT
  set fp := burnsideF447_fpE C.hE with hfp
  have hfpΦ : ∀ p : projectiveSL 3 F, fp (Φ p) = 1 := by
    intro p
    refine (burnsideF447_fpE_one_iff C.hE _).mpr ?_
    rw [burnsideF447_rho_Phi C.hΦ C.hΦρ]
    obtain ⟨g, rfl⟩ := proj_surjective 3 F p
    rw [← conjAut_toGL]
    exact conjAut_mem_linearAutGroup _
  have hker : ∀ r ∈ T, fp r = 1 → r ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    intro r hr h
    obtain ⟨k, hk⟩ := hT.2.1 ⟨r, hr⟩
    have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [← hTG]
    exact ⟨hr, burnsideF429_L3_mem_of_fp C hrk h⟩
  have hS1 : ∀ s ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)), fp s = 1 := by
    intro s hs
    rw [hS] at hs
    obtain ⟨p, -, rfl⟩ := hs
    exact hfpΦ p
  obtain ⟨φ, -, -, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two
    (le_trans (by norm_num) hf) hFcard
  haveI : IsCyclic (F ≃+* F) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨φ, hzp⟩
  obtain ⟨σ₀, hσ₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (T.map fp)).mp inferInstance
  obtain ⟨t₀, ht₀T, rfl⟩ : σ₀ ∈ T.map fp := by rw [← hσ₀]; exact Subgroup.mem_zpowers σ₀
  have hTN : t₀ ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E) := by
    rw [← hNp.1]
    exact hT.1 ht₀T
  obtain ⟨u, hu, b, hb, hub⟩ := burnsideF447_frattini C.hq C.hΦ hTN
  obtain ⟨p, hpU, rfl⟩ := hu
  have huT : Φ p ∈ T := hST (by rw [hS]; exact ⟨p, hpU, rfl⟩)
  have hbT : b ∈ T := by
    have e : b = (Φ p)⁻¹ * t₀ := by rw [hub]; group
    rw [e]
    exact T.mul_mem (T.inv_mem huT) ht₀T
  have hfpb : fp b = fp t₀ := by rw [hub, map_mul, hfpΦ, one_mul]
  refine burnsideF429_c2ab_of_hom fp hST hker hS1 hbT (by rw [hfpb, hσ₀]) ?_
  have h1 : fp (b ^ orderOf (fp b)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
  have h2 := hker _ (T.pow_mem hbT _) h1
  rw [hS] at h2
  obtain ⟨p', hp'U, hp'⟩ := h2
  have hbB : b ^ orderOf (fp b) ∈ burnsideF447_Bt Φ := Subgroup.pow_mem _ hb _
  have hp'N : p' ∈ Subgroup.normalizer ((torus3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) :=
    (burnsideF447_Phi_mem_normalizer C.hΦ _ p').mp (by rw [hp']; exact hbB.2)
  rw [← hp', burnsideF447_U_inf_normB0 C.hq hp'U hp'N, map_one]

end L3

section Sp4

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.SteinbergBS
  CFSG.QuasithinUnique.Fin257.Sp4 CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpOut2 CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F
  CFSG.ComponentClassification.OuterAutomorphisms

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem burnsideF429_frobAut_pow_dSp (j : ℕ) (s t : Fˣ) :
    (frobAut F ^ j) (dSp s t) = dSp (s ^ 2 ^ j) (t ^ 2 ^ j) := by
  apply mat_ext
  rw [mat_frobAut_pow]
  show (dSpMat s t).map (fun x => x ^ 2 ^ j) = dSpMat (s ^ 2 ^ j) (t ^ 2 ^ j)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [dSpMat, Matrix.diagonal_apply, Units.val_pow_eq_pow_val, inv_pow]

theorem burnsideF429_conj_dSp_frob_pow (s t : Fˣ) (k m : ℕ) :
    ∃ s' t' : Fˣ, (MulAut.conj (dSp s t) * frobAut F ^ k) ^ m =
      MulAut.conj (dSp s' t') * frobAut F ^ (k * m) := by
  induction m with
  | zero => exact ⟨1, 1, by rw [pow_zero, dSp_one, map_one, mul_zero, pow_zero, mul_one]⟩
  | succ m ih =>
    obtain ⟨s', t', h⟩ := ih
    refine ⟨s' * s ^ 2 ^ (k * m), t' * t ^ 2 ^ (k * m), ?_⟩
    rw [pow_succ, h, burnsideF429_conj_mul_conj, burnsideF429_frobAut_pow_dSp, dSp_mul, ← pow_add,
      mul_add, mul_one]

theorem burnsideF429_dSp_mem_U {s t : Fˣ} (h : dSp s t ∈ antiUnipotent F) : dSp s t = 1 := by
  have h0 := glMat_diag_of_mem_U h 0
  have h1 := glMat_diag_of_mem_U h 1
  rw [(glMat_dSp_diag (F := F) s t).1] at h0
  rw [(glMat_dSp_diag (F := F) s t).2] at h1
  have hs : s = 1 := Units.ext h0
  have ht : t = 1 := Units.ext h1
  rw [hs, ht, dSp_one]

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}


omit [Finite F] [CharP F 2] in
theorem burnsideF429_c2ab_Sp4 {f : ℕ} (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    (∃ t ∈ T, T = Subgroup.zpowers t ⊔ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
      ∃ H : Subgroup E, IsComplementIn H (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, hKf, hKfin, hKchar, Ψ, hKcard, hS, hform⟩ := burnsideF429_Sp4_model hyp hf
  have hf1 : 1 ≤ f := le_trans (by norm_num) hf
  set φ : antiSp K →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hTG := burnsideF429_T_inf_Gp hyp hT
  have hST := burnsideF429_sbar_le (Gp := Gp) hT
  let act : E →* MulAut (antiSp K) :=
    (MulAut.congr Ψ.symm).toMonoidHom.comp (burnsideF4d_rho Gp)
  have hact : ∀ (r : E) (x : antiSp K), ((Ψ (act r x) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹ := by
    intro r x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp r (Ψ x))) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply r (Ψ x)
  have hact_eq : ∀ (r : E) (α : MulAut (antiSp K)),
      (∀ x, ((Ψ (α x) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹) → act r = α := by
    intro r α h
    refine MulEquiv.ext fun x => Ψ.injective (Subtype.ext ?_)
    rw [hact, h]
  have hact_phi : ∀ x : antiSp K, act (φ x) = MulAut.conj x := by
    intro x
    refine hact_eq _ _ fun y => ?_
    show ((Ψ (x * y * x⁻¹) : ↥Gp) : E) = φ x * ((Ψ y : ↥Gp) : E) * (φ x)⁻¹
    rw [map_mul, map_mul, map_inv]
    rfl
  let π : E →* Outer (antiSp K) := (QuotientGroup.mk' (inner (antiSp K))).comp act
  have hπ1 : ∀ r : E, π r = 1 ↔ act r ∈ inner (antiSp K) := fun r => by
    show QuotientGroup.mk' (inner (antiSp K)) (act r) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : ∀ r ∈ T, π r = 1 → r ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    intro r hr h
    obtain ⟨x, hx⟩ := (hπ1 r).mp h
    have hrG : r ∈ Gp := burnsideF429_mem_of_inner hyp.centralizer_trivial Ψ
      (β := MulAut.conj x) (fun y => by rw [hx]; exact hact r y) ⟨x, rfl⟩
    rw [← hTG]
    exact ⟨hr, hrG⟩
  have hS1 : ∀ s ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)), π s = 1 := by
    intro s hs
    rw [hS] at hs
    obtain ⟨x, -, rfl⟩ := hs
    exact (hπ1 _).mpr ⟨x, (hact_phi x).symm⟩
  have hπform : ∀ r ∈ M₁ ⊓ M₂, ∃ g ∈ bor K, ∃ k : ℕ,
      act r = MulAut.conj g * frobAut K ^ k := by
    intro r hr
    obtain ⟨g, hg, k, hgk⟩ := hform r hr
    exact ⟨g, hg, k, hact_eq r _ hgk⟩
  have hTle : T.map π ≤ Subgroup.zpowers (QuotientGroup.mk' (inner (antiSp K)) (frobAut K)) := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨g, -, k, hgk⟩ := hπform r (hT.1 hr)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    show _ = QuotientGroup.mk' (inner (antiSp K)) (act r)
    have hg1 : QuotientGroup.mk' (inner (antiSp K)) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff (MulAut.conj g)).mpr ⟨g, rfl⟩
    rw [hgk, map_mul, hg1, one_mul, map_pow, zpow_natCast]
  haveI : IsCyclic (T.map π) := Subgroup.isCyclic_of_le hTle
  obtain ⟨σ₀, hσ₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (T.map π)).mp inferInstance
  obtain ⟨t₀, ht₀T, rfl⟩ : σ₀ ∈ T.map π := by rw [← hσ₀]; exact Subgroup.mem_zpowers σ₀
  obtain ⟨g, hg, k, hgk⟩ := hπform t₀ (hT.1 ht₀T)
  obtain ⟨s, t, A, B, C, D, rfl⟩ := burnsideF429_Sp_bor_decomp hg
  set u' : antiSp K := dSp s t * uElt A B C D * (dSp s t)⁻¹ with hu'
  have hu'U : u' ∈ antiUnipotent K :=
    (Subgroup.mem_normalizer_iff.mp (dSp_mem_normalizer s t) _).mp (uElt_mem_antiUnipotent _ _ _ _)
  have hu'S : φ u' ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by rw [hS]; exact ⟨u', hu'U, rfl⟩
  set t₁ : E := (φ u')⁻¹ * t₀ with ht₁
  have ht₁T : t₁ ∈ T := T.mul_mem (T.inv_mem (hST hu'S)) ht₀T
  have hact₁ : act t₁ = MulAut.conj (dSp s t) * frobAut K ^ k := by
    rw [ht₁, map_mul, map_inv, hact_phi, hgk, hu', ← mul_assoc, ← map_inv, ← map_mul]
    congr 2
    group
  have hπ₁ : π t₁ = π t₀ := by rw [ht₁, map_mul, map_inv, hS1 _ hu'S, inv_one, one_mul]
  refine burnsideF429_c2ab_of_hom π hST hker hS1 ht₁T (by rw [hπ₁, hσ₀]) ?_
  set n := orderOf (π t₁)
  have hn1 : π (t₁ ^ n) = 1 := by rw [map_pow, pow_orderOf_eq_one]
  have hnS := hker _ (T.pow_mem ht₁T n) hn1
  have hnS' := hnS
  rw [hS] at hnS'
  obtain ⟨x, hxU, hx⟩ := hnS'
  obtain ⟨s', t', hst'⟩ := burnsideF429_conj_dSp_frob_pow s t k n
  have hactn : act (t₁ ^ n) = MulAut.conj (dSp s' t') * frobAut K ^ (k * n) := by
    rw [map_pow, hact₁, hst']
  have hconj : MulAut.conj ((dSp s' t')⁻¹ * x) = frobAut K ^ (k * n) := by
    rw [map_mul, map_inv, ← hact_phi x, hx, hactn]
    group
  have hx1 := conj_eq_frobAut_pow hf1 hKcard hconj
  have hxd : x = dSp s' t' := by
    have := congrArg (dSp s' t' * ·) hx1
    simpa using this
  rw [hxd] at hxU
  rw [← hx, hxd, burnsideF429_dSp_mem_U hxU, map_one]

end Sp4

end CFSG.ASVolI

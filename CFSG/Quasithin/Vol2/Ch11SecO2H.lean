module

public import CFSG.Quasithin.Vol2.Ch11SecO2G
public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGJ
public import CFSG.Quasithin.Vol2.Ch11SecA14Lines
public import CFSG.Quasithin.Vol2.Ch11SecAKA14
public import CFSG.Quasithin.Vol2.Ch11SecO2B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usp)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open CFSG.ClassicalGroups.Alternating (symplecticTransvection symplecticTransvection_apply)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torus)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (eq_map_psiSp_of_sylow inf_normalizer_eq_sp
  exists_eq_map_torus_sp Usp_eq_unipotent gammaW_pre_eq)
open SecB.K7 (trv trv_mulVec trv_conj trv_smul)
open scoped IsMulCommutative commutatorElement

namespace O2

variable {K : Type} [Field K]

theorem mem_closure_trv (γ : ↥(StatedSp 2 K)) :
    γ ∈ Subgroup.closure
      {x : ↥(StatedSp 2 K) | ∃ (a : Fin 2 ⊕ Fin 2 → K) (c : K), x = trv a c} := by
  set S := Subgroup.closure {x : ↥(StatedSp 2 K) | ∃ (a : Fin 2 ⊕ Fin 2 → K) (c : K),
    x = trv a c} with hS
  have hB := toBilin'_spJ_isAlt (K := K)
  have hBn := toBilin'_spJ_nondegenerate (K := K)
  set φ : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K) →* GL (Fin 2 ⊕ Fin 2) K :=
    Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom with hφ
  have hg : Matrix.GeneralLinearGroup.toLin (γ : GL (Fin 2 ⊕ Fin 2) K) ∈
      bilinIsometryGroup (Matrix.toBilin' (spJ K)) := fun x y => by
    rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    exact spB_mat γ x y
  rw [CFSG.ClassicalGroups.Alternating.alternating_transvection_generation hB hBn] at hg
  have hmem : φ (Matrix.GeneralLinearGroup.toLin (γ : GL (Fin 2 ⊕ Fin 2) K)) ∈
      S.map (StatedSp 2 K).subtype := by
    refine (Subgroup.closure_le ((S.map (StatedSp 2 K).subtype).comap φ)).mpr ?_ hg
    rintro _ ⟨a, c, rfl⟩
    refine ⟨trv a c, Subgroup.subset_closure ⟨a, c, rfl⟩, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have h1 : ∀ x : Fin 2 ⊕ Fin 2 → K,
        (((φ (symplecticTransvection (Matrix.toBilin' (spJ K)) hB a c) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) =
          mat 2 K (trv a c) *ᵥ x := by
      intro x
      rw [trv_mulVec, hφ, MulEquiv.coe_toMonoidHom, ← Matrix.mulVecLin_apply,
        ← Matrix.GeneralLinearGroup.coe_toLin, MulEquiv.apply_symm_apply,
        symplecticTransvection_apply]
    have h2 := congrFun (h1 (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h2
    exact h2.symm
  obtain ⟨γ', hγ', hγ'eq⟩ := hmem
  have : γ' = γ := Subtype.ext (by
    rw [Subgroup.coe_subtype] at hγ'eq
    rw [hγ'eq, hφ, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply])
  rw [← this]
  exact hγ'

theorem conj_mulVec_g (g u : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (g * u * g⁻¹) *ᵥ (mat 2 K g *ᵥ v) = mat 2 K g *ᵥ (mat 2 K u *ᵥ v) := by
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mat_inv_mulVec]

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem inf_centralizer_le_pCoreOf (hS : SecD.NatSetting11 G T L I n) :
    (L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hS.sylow.1
  have hCV : Subgroup.normalizer (fsuV T I : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (fsuV T I : Set G) : Set G) :=
    fun t ht => SecA.mem_normalizer_centralizer ht
  have hXV : L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    sup_le hS.le_normalizer (SecA.T_le_normalizer_fsuV T I)
  set N := (L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) with hN
  have hN2 : IsPGroup 2 N := isPGroup_two_of_forall fun x hx => by
    obtain ⟨j, hj⟩ := E1.exists_pow_mem_of_mem_sup hT2 hS.normal hx.1
    have hjC : x ^ 2 ^ j ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
      ⟨hj, Subgroup.pow_mem _ hx.2 _⟩
    rw [SecO1.inf_centralizer_eq hS] at hjC
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hjC
    exact ⟨j + k, by rw [pow_add, pow_mul, hk]⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2
      fun x hx => SecD.mem_normalizer_inf (Subgroup.le_normalizer hx) (hCV (hXV hx))) hN2

theorem le_sup_of_autOn_le (hS : SecD.NatSetting11 G T L I n) {A : Subgroup G}
    (hA : A ≤ L ⊔ T) (h : autOn L (fsuV T I) ≤ autOn A (fsuV T I)) :
    L ≤ A ⊔ pCoreOf 2 (L ⊔ T) := by
  intro l hl
  have hlV := hS.le_normalizer hl
  obtain ⟨z, hz, hzV, hzl⟩ := SecA.mem_autOn_iff.mp (h (SecA.conjV_mem_autOn hl hlV))
  have h1 : z⁻¹ * l ∈ (L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).inv_mem (hA hz)) (le_sup_left (α := Subgroup G) hl),
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h5 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) hzl
    simp only [SecA.conjV_apply_coe] at h5
    calc v * (z⁻¹ * l) = z⁻¹ * (z * v * z⁻¹) * z * (z⁻¹ * l) := by group
      _ = z⁻¹ * (l * v * l⁻¹) * z * (z⁻¹ * l) := by rw [← h5]
      _ = z⁻¹ * l * v := by group
  have := Subgroup.mul_mem_sup hz (inf_centralizer_le_pCoreOf hS h1)
  rwa [mul_inv_cancel_left] at this

end O2

open O2 in
theorem factSp4Gen_holds : FactSp4Gen := by
  intro G _ _ T L I n V₁ V₃ X hS hk hV₁ hV₃ hX P hP hPV₃ hPV hXP y hy hyopp
  have := SecO1.isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hπ, hg, hV₁g, -, hV₃g⟩ := exists_coord hS hk
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : Fin 2 ⊕ Fin 2 → K, y₁ = mat 2 K g *ᵥ vec4 1 0 0 0 := ⟨_, rfl⟩
  have hPtrv : ∀ p (hp : p ∈ P), ∃ c : K,
      SecA.conjV (fsuV T I) p (r1_le hS hV₁ (hP hp)).1.1.1 =
        ((π (trv y₁ c) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := fun p hp => by
    rw [hy₁]
    exact exists_trv_of_r1 hS hK hπ hf hV₁ (hV₁g V₁ hV₁) (hV₃g V₃ hV₃) (hP hp)
      (SecF.O2.mul_comm_of_commutator_eq_bot hPV₃ hp)
  obtain ⟨p₀, hp₀, c₀, hc₀, hp₀c⟩ : ∃ p, ∃ hp : p ∈ P, ∃ c : K, c ≠ 0 ∧
      SecA.conjV (fsuV T I) p (r1_le hS hV₁ (hP hp)).1.1.1 =
        ((π (trv y₁ c) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by
    by_contra hall
    push Not at hall
    apply hPV
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv p hp
    obtain ⟨c, hc⟩ := hPtrv p hp
    have hc0 : c = 0 := by
      by_contra hc0
      exact hall p hp c hc0 hc
    rw [hc0, SecB.K7.trv_zero, map_one, Subgroup.coe_one] at hc
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have h1 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) hc
    simp only [SecA.conjV_apply_coe, MulAut.one_apply] at h1
    calc v * p = p * v * p⁻¹ * p := by rw [h1]
      _ = p * v := by group
  have hD := SecO1.isHall_autOn_cartan hS hX
  rw [eq_map_psiSp_of_sylow hg, inf_normalizer_eq_sp hf g] at hD
  obtain ⟨x₀, hx₀, hDx⟩ := exists_eq_map_torus_sp hf g hD
  rw [← Usp_eq_unipotent] at hx₀
  have htor : ∀ (s : K) (hs0 : s ≠ 0),
      mat 2 K (torusHom ![Units.mk0 s hs0, 1]) *ᵥ vec4 1 0 0 0 = s • vec4 1 0 0 0 := by
    intro s hs0
    rw [← KA.single_inl0, SecA.C11P9B.torusHom_mulVec_e0]
    simp
  have hPall : ∀ c : K, ∃ p ∈ P, ∃ hp : p ∈ Subgroup.normalizer (fsuV T I : Set G),
      SecA.conjV (fsuV T I) p hp =
        ((π (trv y₁ c) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by
    intro c
    by_cases hc : c = 0
    · refine ⟨1, P.one_mem, Subgroup.one_mem _, ?_⟩
      rw [hc, SecB.K7.trv_zero, map_one, Subgroup.coe_one]
      ext v
      rw [SecA.conjV_apply_coe, one_mul, inv_one, mul_one, MulAut.one_apply]
    obtain ⟨s, hs⟩ := isSquare_of_charTwo' (c / c₀)
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero, div_eq_zero_iff] at hs
      exact hs.elim hc hc₀
    have hmem : psiSp π (g * x₀) (torusHom ![Units.mk0 s hs0, 1]) ∈ autOn X (fsuV T I) := by
      rw [hDx]
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    obtain ⟨x, hx, hxV, hxeq⟩ := SecA.mem_autOn_iff.mp hmem
    have hp₀V := (r1_le hS hV₁ (hP hp₀)).1.1.1
    have hxp : x * p₀ * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hXP hx) p₀).mp hp₀
    have hA : mat 2 K (g * x₀ * torusHom ![Units.mk0 s hs0, 1] * (g * x₀)⁻¹) *ᵥ y₁ = s • y₁ := by
      rw [hy₁, show g * x₀ * torusHom ![Units.mk0 s hs0, 1] * (g * x₀)⁻¹ =
          g * (x₀ * torusHom ![Units.mk0 s hs0, 1] * x₀⁻¹) * g⁻¹ by group, conj_mulVec_g, map_mul,
        map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        (mulVec_of_mem_Usp (inv_mem hx₀) 0).2, htor s hs0, Matrix.mulVec_smul,
        (mulVec_of_mem_Usp hx₀ 0).2, Matrix.mulVec_smul]
    have hkey : g * x₀ * torusHom ![Units.mk0 s hs0, 1] * (g * x₀)⁻¹ * trv y₁ c₀ *
        (g * x₀ * torusHom ![Units.mk0 s hs0, 1] * (g * x₀)⁻¹)⁻¹ = trv y₁ c := by
      rw [trv_conj, hA, trv_smul, show s ^ 2 * c₀ = c by rw [sq, ← hs, div_mul_cancel₀ c hc₀]]
    refine ⟨_, hxp, Subgroup.mul_mem _ (Subgroup.mul_mem _ hxV hp₀V) (Subgroup.inv_mem _ hxV), ?_⟩
    rw [SecA.conjV_mul _ (Subgroup.mul_mem _ hxV hp₀V) (Subgroup.inv_mem _ hxV),
      SecA.conjV_mul _ hxV hp₀V, SecA.conjV_inv _ hxV, ← hxeq, hp₀c, psiSp_apply, ← hkey]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hyV := hS.le_normalizer hy
  obtain ⟨γ, hγ⟩ : ∃ γ : StatedSp 2 K, π γ = ⟨_, SecA.conjV_mem_autOn hy hyV⟩ := hf.onto _
  have hγ' : SecA.conjV (fsuV T I) y hyV =
      ((π γ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by rw [hγ]
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : Fin 2 ⊕ Fin 2 → K, y₂ = mat 2 K γ⁻¹ *ᵥ y₁ := ⟨_, rfl⟩
  have hPy : ∀ c : K, ((π (trv y₂ c) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) ∈
      autOn (conjSubgroup P y) (fsuV T I) := by
    intro c
    obtain ⟨p, hp, hpV, hpc⟩ := hPall c
    have hyp : y⁻¹ * p * y ∈ conjSubgroup P y := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff]
      simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hp
    have hypV : y⁻¹ * p * y ∈ Subgroup.normalizer (fsuV T I : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyV) hpV) hyV
    have hkey : γ⁻¹ * trv y₁ c * γ = trv y₂ c := by rw [hy₂, ← trv_conj, inv_inv]
    have h1 : SecA.conjV (fsuV T I) (y⁻¹ * p * y) hypV =
        ((π (trv y₂ c) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by
      rw [SecA.conjV_mul _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyV) hpV) hyV,
        SecA.conjV_mul _ (Subgroup.inv_mem _ hyV) hpV, SecA.conjV_inv _ hyV, hγ', hpc, ← hkey]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← h1]
    exact SecA.conjV_mem_autOn hyp hypV
  have hu0 : (mat 2 K g⁻¹ *ᵥ y₂) (.inr 0) ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hf.surj y₂
    have hv1 : (v : G) ∈ conjSubgroup V₁ y :=
      (mem_conj_v1_iff (hV₁g V₁ hV₁) hyV hγ' v).mpr ⟨1, by rw [hv, one_smul, hy₂, hy₁]⟩
    have hv3 : (v : G) ∈ V₃ := by
      rw [mem_iff_of_eq (hV₃g V₃ hV₃), hv]
      exact h0
    have h4 : (v : G) ∈ conjSubgroup V₁ y ⊓ V₃ := ⟨hv1, hv3⟩
    rw [hyopp, Subgroup.mem_bot] at h4
    have h5 : v = 1 := Subtype.ext h4
    rw [h5, hf.map_one, hy₂, hy₁] at hv
    have h6 := congrArg (fun x => mat 2 K g⁻¹ *ᵥ (mat 2 K γ *ᵥ x)) hv
    simp only [Matrix.mulVec_zero, mat_mulVec_inv, mat_inv_mulVec] at h6
    exact one_ne_zero (congrFun h6 (.inl 0)).symm
  have hL₁ : ∀ M ∈ perfectCore (Q2 K 0), psiSp π g M ∈ autOn (LOf L V₁) (fsuV T I) := by
    intro M hM
    rw [SecA.autOn_lOf hS.le_normalizer hV₁V, hV₁g V₁ hV₁]
    change _ ∈ SecS.gammaW _ _
    rw [gammaW_pre_eq hf g 0 _ flag_one_eq]
    exact ⟨M, hM, rfl⟩
  have htrv : ∀ (a : Fin 2 ⊕ Fin 2 → K) (c : K),
      ((π (trv a c) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) ∈
        autOn (LOf L V₁ ⊔ conjSubgroup P y) (fsuV T I) := by
    intro a c
    by_cases ha : (mat 2 K g⁻¹ *ᵥ a) (.inr 0) = 0
    ·
      have hfix : mat 2 K (g⁻¹ * trv a c * g) *ᵥ vec4 1 0 0 0 = vec4 1 0 0 0 := by
        have hB : Matrix.toBilin' (spJ K) (mat 2 K g *ᵥ vec4 1 0 0 0) a = 0 :=
          (mem_gS3_iff g a).mp (mem_gmapSp.mpr ha)
        rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, trv_mulVec, hB,
          mul_zero, zero_smul, add_zero, mat_inv_mulVec]
      have h1 := hL₁ _ (KA.mem_N0_of_fix hK4 hfix)
      rw [psiSp_apply, show g * (g⁻¹ * trv a c * g) * g⁻¹ = trv a c by group] at h1
      exact SecA.autOn_mono le_sup_left h1
    ·
      obtain ⟨u, hu⟩ : ∃ u : Fin 2 ⊕ Fin 2 → K, u = mat 2 K g⁻¹ *ᵥ y₂ := ⟨_, rfl⟩
      obtain ⟨u', hu'⟩ : ∃ u' : Fin 2 ⊕ Fin 2 → K, u' = mat 2 K g⁻¹ *ᵥ a := ⟨_, rfl⟩
      have hu0' : u (.inr 0) ≠ 0 := by rw [hu]; exact hu0
      have ha' : u' (.inr 0) ≠ 0 := by rw [hu']; exact ha
      set N₁ := eltE ((u' (.inr 0))⁻¹ • u') * (eltE ((u (.inr 0))⁻¹ • u))⁻¹ with hN₁
      have hN₁mem : N₁ ∈ pCoreOf 2 (perfectCore (Q2 K 0)) :=
        mul_mem (eltE_mem hK4 _) (inv_mem (eltE_mem hK4 _))
      have hEa : mat 2 K (eltE ((u' (.inr 0))⁻¹ • u')) *ᵥ vec4 0 0 1 0 =
          (u' (.inr 0))⁻¹ • u' := by
        rw [mulVec_E_f0]
        refine vec4_eq rfl rfl ?_ rfl
        simp only [vec4, Sum.elim_inr, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
        rw [inv_mul_cancel₀ ha']
      have hEu : mat 2 K (eltE ((u (.inr 0))⁻¹ • u)) *ᵥ vec4 0 0 1 0 = (u (.inr 0))⁻¹ • u := by
        rw [mulVec_E_f0]
        refine vec4_eq rfl rfl ?_ rfl
        simp only [vec4, Sum.elim_inr, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
        rw [inv_mul_cancel₀ hu0']
      have h0 : vec4 0 0 1 0 = mat 2 K (eltE ((u (.inr 0))⁻¹ • u))⁻¹ *ᵥ ((u (.inr 0))⁻¹ • u) := by
        have h := congrArg (fun x => mat 2 K (eltE ((u (.inr 0))⁻¹ • u))⁻¹ *ᵥ x) hEu
        simpa only [mat_inv_mulVec] using h
      have hN₁u : mat 2 K N₁ *ᵥ u = (u (.inr 0) / u' (.inr 0)) • u' := by
        have h2 : mat 2 K N₁ *ᵥ u = u (.inr 0) • ((u' (.inr 0))⁻¹ • u') := by
          conv_lhs => rw [show u = u (.inr 0) • ((u (.inr 0))⁻¹ • u) by
            rw [smul_smul, mul_inv_cancel₀ hu0', one_smul]]
          rw [Matrix.mulVec_smul, hN₁, map_mul, ← Matrix.mulVec_mulVec, ← h0, hEa]
        rw [h2, smul_smul, div_eq_mul_inv]
      have hr0 : u (.inr 0) / u' (.inr 0) ≠ 0 := div_ne_zero hu0' ha'
      have hga : mat 2 K g *ᵥ u' = a := by rw [hu', mat_mulVec_inv]
      have hδ : mat 2 K (g * N₁ * g⁻¹) *ᵥ y₂ = (u (.inr 0) / u' (.inr 0)) • a := by
        rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu, hN₁u,
          Matrix.mulVec_smul, hga]
      have heq : trv a c = (g * N₁ * g⁻¹) * trv y₂ ((u (.inr 0) / u' (.inr 0))⁻¹ ^ 2 * c) *
          (g * N₁ * g⁻¹)⁻¹ := by
        rw [trv_conj, hδ, trv_smul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr0, one_pow, one_mul]
      have h1 : ((π (g * N₁ * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) ∈
          autOn (LOf L V₁ ⊔ conjSubgroup P y) (fsuV T I) :=
        SecA.autOn_mono le_sup_left (hL₁ _ (Subgroup.map_subtype_le _ hN₁mem))
      have h2 := SecA.autOn_mono (le_sup_right : conjSubgroup P y ≤ LOf L V₁ ⊔ conjSubgroup P y)
        (hPy ((u (.inr 0) / u' (.inr 0))⁻¹ ^ 2 * c))
      rw [heq, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)
  have hgen : ∀ {B : Subgroup G}, (∀ (a : Fin 2 ⊕ Fin 2 → K) (c : K),
      ((π (trv a c) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) ∈ autOn B (fsuV T I)) →
      autOn L (fsuV T I) ≤ autOn B (fsuV T I) := by
    intro B hB h hh
    obtain ⟨γ', hγ'⟩ : ∃ γ' : StatedSp 2 K, π γ' = ⟨h, hh⟩ := hf.onto _
    have h1 : γ' ∈ (autOn B (fsuV T I)).comap ((autOn L (fsuV T I)).subtype.comp π) :=
      (Subgroup.closure_le _).mpr (by rintro _ ⟨a, c, rfl⟩; exact hB a c)
        (mem_closure_trv γ')
    have h2 : ((autOn L (fsuV T I)).subtype.comp π) γ' = h := by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hγ']
    rw [← h2]
    exact h1
  have hPLT : P ≤ L ⊔ T := fun p hp =>
    (sup_le (((perfectCore_le _).trans inf_le_left).trans le_sup_left) le_sup_right)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _ (hP hp))
  have hPyLT : conjSubgroup P y ≤ L ⊔ T := by
    intro z hz
    have h1 := CFSG.Quasithin.mem_conjSubgroup_iff.mp hz
    have h2 := (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).inv_mem (le_sup_left (α := Subgroup G)
      hy)) (hPLT h1)) (le_sup_left (α := Subgroup G) hy)
    simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h2
  have hL₁LT : LOf L V₁ ≤ L ⊔ T := ((perfectCore_le _).trans inf_le_left).trans le_sup_left
  have hPyV : conjSubgroup P y ≤ Subgroup.normalizer (fsuV T I : Set G) := fun z hz =>
    sup_le hS.le_normalizer (SecA.T_le_normalizer_fsuV T I) (hPyLT hz)
  refine ⟨le_sup_of_autOn_le hS (sup_le hL₁LT hPyLT) (hgen htrv),
    le_sup_of_autOn_le hS ?_ (hgen fun a c => ?_)⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨l, hl, z, hz, rfl⟩
    exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (le_sup_left (α := Subgroup G) hl) (hPyLT hz))
      ((L ⊔ T).inv_mem (le_sup_left (α := Subgroup G) hl))
  ·
    by_cases ha : a = 0
    · have h0 : trv a c = 1 := SecB.K7.sp_ext fun x => by
        rw [trv_mulVec, ha, smul_zero, add_zero, map_one, Matrix.one_mulVec]
      rw [h0, map_one, Subgroup.coe_one]
      exact Subgroup.one_mem _
    have hy₂0 : y₂ ≠ 0 := fun h => hu0 (by simp [h])
    obtain ⟨δ, hδ⟩ := exists_sp4_lin_eq y₂ a hy₂0 ha
    rw [linModelNat_lin, ← mat_apply] at hδ
    obtain ⟨l, hl, hlV, hleq, -⟩ := SecO1.IsCoord.exists_mem hf δ
    have hleq' : ((π δ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) =
        SecA.conjV (fsuV T I) l hlV := hleq
    obtain ⟨p, hp, hpV, hpc⟩ := hPall c
    have hyp : y⁻¹ * p * y ∈ conjSubgroup P y := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff]
      simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hp
    have hz : l * (y⁻¹ * p * y) * l⁻¹ ∈ conjClosure (conjSubgroup P y) L :=
      Subgroup.subset_closure ⟨l, hl, _, hyp, rfl⟩
    have hypV : y⁻¹ * p * y ∈ Subgroup.normalizer (fsuV T I : Set G) := hPyV hyp
    have hzV : l * (y⁻¹ * p * y) * l⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hlV hypV) (Subgroup.inv_mem _ hlV)
    have hkey : δ * (γ⁻¹ * trv y₁ c * γ) * δ⁻¹ = trv a c := by
      rw [show δ * (γ⁻¹ * trv y₁ c * γ) * δ⁻¹ = (δ * γ⁻¹) * trv y₁ c * (δ * γ⁻¹)⁻¹ by group,
        trv_conj, map_mul, ← Matrix.mulVec_mulVec, ← hy₂, hδ]
    have h1 : SecA.conjV (fsuV T I) (l * (y⁻¹ * p * y) * l⁻¹) hzV =
        ((π (trv a c) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by
      rw [SecA.conjV_mul _ (Subgroup.mul_mem _ hlV hypV) (Subgroup.inv_mem _ hlV),
        SecA.conjV_mul _ hlV hypV, SecA.conjV_inv _ hlV,
        SecA.conjV_mul _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyV) hpV) hyV,
        SecA.conjV_mul _ (Subgroup.inv_mem _ hyV) hpV, SecA.conjV_inv _ hyV, hγ', hpc, ← hleq',
        ← hkey]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← h1]
    exact SecA.conjV_mem_autOn hz hzV

end CFSG.Quasithin.Vol2.Ch11.SecF

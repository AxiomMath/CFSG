module

public import CFSG.Quasithin.H13.L32NLem1444d
public import CFSG.Quasithin.H13.L32NThm1443
public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Odd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L1444

section LinAlg

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem eq_of_trivial_on {P₁ P₂ S : Submodule (ZMod 2) W} (h12 : P₁ ⊔ P₂ = ⊤)
    (hS1 : S ⊔ P₁ = ⊤) (hS2 : S ⊓ P₂ = ⊥) (κ : W →ₗ[ZMod 2] W) (hκ2 : ∀ w ∈ P₂, κ w ∈ P₂)
    (hκS : ∀ w ∈ S, κ w ∈ S) (hκ1 : ∀ w ∈ P₁, κ w = w) (w : W) : κ w = w := by
  have hP2 : ∀ w ∈ P₂, κ w = w := by
    intro w hw
    have hw' : w ∈ S ⊔ P₁ := hS1 ▸ Submodule.mem_top
    obtain ⟨s, hs, p, hp, rfl⟩ := Submodule.mem_sup.mp hw'
    have h1 : κ (s + p) - (s + p) = κ s - s := by rw [map_add, hκ1 p hp]; abel
    have h2 : κ (s + p) - (s + p) ∈ S ⊓ P₂ := by
      refine ⟨?_, P₂.sub_mem (hκ2 _ hw) hw⟩
      rw [h1]
      exact S.sub_mem (hκS s hs) hs
    rw [hS2, Submodule.mem_bot, sub_eq_zero] at h2
    exact h2
  have hw' : w ∈ P₁ ⊔ P₂ := h12 ▸ Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hw'
  rw [map_add, hκ1 p hp, hP2 q hq]

theorem mat_inv : ∀ A K : Matrix (Fin 2) (Fin 2) (ZMod 2), A * A ≠ 1 ∨ A = 1 ∨
    K * K * K ≠ 1 ∨ A * K * A * K = 1 := by
  decide

theorem mat_range : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2), A * A ≠ 1 ∨ A = 1 ∨
    ∃ p : Fin 2 → ZMod 2, p ≠ 0 ∧ (∀ w, (A - 1).mulVec w = 0 ∨ (A - 1).mulVec w = p) ∧
      ∃ w₀, (A - 1).mulVec w₀ = p := by
  decide

variable {P : Submodule (ZMod 2) W}

noncomputable def resMat (b : Module.Basis (Fin 2) (ZMod 2) P) (f : W →ₗ[ZMod 2] W)
    (hf : ∀ w ∈ P, f w ∈ P) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  LinearMap.toMatrix b b (f.restrict hf)

theorem resMat_mul (b : Module.Basis (Fin 2) (ZMod 2) P) {f g : W →ₗ[ZMod 2] W}
    (hf : ∀ w ∈ P, f w ∈ P) (hg : ∀ w ∈ P, g w ∈ P) :
    resMat b (f * g) (fun w hw => hf _ (hg w hw)) = resMat b f hf * resMat b g hg := by
  rw [resMat, resMat, resMat, ← LinearMap.toMatrix_mul]
  rfl

theorem resMat_eq_one_iff (b : Module.Basis (Fin 2) (ZMod 2) P) {f : W →ₗ[ZMod 2] W}
    (hf : ∀ w ∈ P, f w ∈ P) : resMat b f hf = 1 ↔ ∀ w ∈ P, f w = w := by
  rw [resMat, ← LinearMap.toMatrix_one b, (LinearMap.toMatrix b b).injective.eq_iff]
  constructor
  · intro h w hw
    have := congrArg (fun g : P →ₗ[ZMod 2] P => (g ⟨w, hw⟩ : W)) h
    simpa using this
  · intro h
    ext ⟨w, hw⟩
    simpa using h w hw

theorem inv_of_involution (b : Module.Basis (Fin 2) (ZMod 2) P) {f k : W →ₗ[ZMod 2] W}
    (hf : ∀ w ∈ P, f w ∈ P) (hk : ∀ w ∈ P, k w ∈ P) (hff : ∀ w ∈ P, f (f w) = w)
    (hf1 : ∃ w ∈ P, f w ≠ w) (hk3 : ∀ w ∈ P, k (k (k w)) = w) :
    ∀ w ∈ P, f (k (f (k w))) = w := by
  have hA : resMat b f hf * resMat b f hf = 1 := by
    rw [← resMat_mul, resMat_eq_one_iff]
    exact hff
  have hA1 : resMat b f hf ≠ 1 := by
    rw [ne_eq, resMat_eq_one_iff]
    obtain ⟨w, hw, hfw⟩ := hf1
    exact fun h => hfw (h w hw)
  have hK : resMat b k hk * resMat b k hk * resMat b k hk = 1 := by
    rw [← resMat_mul, ← resMat_mul, resMat_eq_one_iff]
    exact hk3
  rcases mat_inv (resMat b f hf) (resMat b k hk) with h | h | h | h
  · exact absurd hA h
  · exact absurd h hA1
  · exact absurd hK h
  · rw [← resMat_mul, ← resMat_mul, ← resMat_mul, resMat_eq_one_iff] at h
    exact h

theorem range_of_involution (b : Module.Basis (Fin 2) (ZMod 2) P) {f : W →ₗ[ZMod 2] W}
    (hf : ∀ w ∈ P, f w ∈ P) (hff : ∀ w ∈ P, f (f w) = w) (hf1 : ∃ w ∈ P, f w ≠ w) :
    ∃ p ∈ P, p ≠ 0 ∧ (∀ w ∈ P, f w - w = 0 ∨ f w - w = p) ∧ ∃ w₀ ∈ P, f w₀ - w₀ = p := by
  have hA : resMat b f hf * resMat b f hf = 1 := by
    rw [← resMat_mul, resMat_eq_one_iff]
    exact hff
  have hA1 : resMat b f hf ≠ 1 := by
    rw [ne_eq, resMat_eq_one_iff]
    obtain ⟨w, hw, hfw⟩ := hf1
    exact fun h => hfw (h w hw)
  rcases mat_range (resMat b f hf) with h | h | ⟨p', hp0, hp, w₀, hw₀⟩
  · exact absurd hA h
  · exact absurd h hA1
  have key : ∀ x : P, b.equivFun (f.restrict hf x - x) =
      (resMat b f hf - 1).mulVec (b.equivFun x) := by
    intro x
    have e : resMat b f hf - 1 = LinearMap.toMatrix b b (f.restrict hf - 1) := by
      rw [map_sub, LinearMap.toMatrix_one]
      rfl
    rw [e, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
      LinearMap.toMatrix_mulVec_repr]
    rfl
  refine ⟨(b.equivFun.symm p' : W), (b.equivFun.symm p').2, ?_, ?_, ?_⟩
  · intro h0
    apply hp0
    have h1 : b.equivFun.symm p' = 0 := Subtype.ext h0
    have h2 := congrArg b.equivFun h1
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  · intro w hw
    rcases hp (b.equivFun ⟨w, hw⟩) with h0 | h0
    · left
      rw [← key, LinearEquiv.map_eq_zero_iff] at h0
      simpa [LinearMap.restrict_apply] using congrArg Subtype.val h0
    · right
      rw [← key] at h0
      have h1 : f.restrict hf ⟨w, hw⟩ - ⟨w, hw⟩ = b.equivFun.symm p' := by
        rw [← h0, LinearEquiv.symm_apply_apply]
      simpa [LinearMap.restrict_apply] using congrArg Subtype.val h1
  · refine ⟨(b.equivFun.symm w₀ : W), (b.equivFun.symm w₀).2, ?_⟩
    have h1 : f.restrict hf (b.equivFun.symm w₀) - b.equivFun.symm w₀ = b.equivFun.symm p' := by
      apply b.equivFun.injective
      rw [key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hw₀]
    simpa [LinearMap.restrict_apply] using congrArg Subtype.val h1

end LinAlg

variable {G : Type} [Group G] [Finite G]

open Q8SqE9 in
structure Setup3 (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (Q₁ Q₂ : Subgroup G) : Prop
    extends Setup2 G T L V V₂ g D where
  cfg : Cfg Q₁ Q₂
  sup : Q₁ ⊔ Q₂ = fsuU T V
  kElem : IsElemAbelian 3 (imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V)))

open Q8SqE9 in
theorem exists_setup3 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hRest : Lemma14323Rest) {T L V V₂ : Subgroup G} {g : G} (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (h32 : Nat.card ↥(fsuU T V) = 2 ^ 5)
    (hG2 : ¬ LieModel G .G2 0 3 1) (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgH : g ∉ l32nH T V) :
    ∃ (D : HatModelU (fsuU T V)) (Q₁ Q₂ : Subgroup G), Setup3 G T L V V₂ g D Q₁ Q₂ := by
  obtain ⟨D, S⟩ := exists_setup2 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h hext h32 hV₂ hgP
    hgH
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hQ8 : IsQ8Sq ↥(fsuU T V) :=
    isQ8Sq_of_isQ8CentralPow_two (lemma1442Q8Four_of_inputs hV h hext h32)
  obtain ⟨hQ32, A', B', ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := hQ8
  have hsup : A'.map (fsuU T V).subtype ⊔ B'.map (fsuU T V).subtype = fsuU T V := by
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top, Subgroup.range_subtype]
  have hcomm : A'.map (fsuU T V).subtype ≤
      Subgroup.centralizer (B'.map (fsuU T V).subtype : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb)
  have hcfg : Cfg (A'.map (fsuU T V).subtype) (B'.map (fsuU T V).subtype) :=
    ⟨hcomm,
      ⟨(A'.equivMapOfInjective _ (fsuU T V).subtype_injective).symm.trans eA⟩,
      ⟨(B'.equivMapOfInjective _ (fsuU T V).subtype_injective).symm.trans eB⟩,
      by rw [hsup]; exact hQ32⟩
  obtain ⟨hK, -⟩ :=
    lemma1444One_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest G T L V h hext h32 hG2
  exact ⟨D, _, _, { toSetup2 := S, cfg := hcfg, sup := hsup, kElem := hK }⟩

theorem q8_sq_ne : ∀ u : Q8SqE9.Q8, u = 1 ∨ u = QuaternionGroup.a 2 ∨ u * u ≠ 1 := by
  decide

namespace Setup3

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup3 G T L V V₂ g D Q₁ Q₂)
include S

theorem Q₁_le : Q₁ ≤ fsuU T V := S.sup ▸ le_sup_left

theorem Q₂_le : Q₂ ≤ fsuU T V := S.sup ▸ le_sup_right

theorem mem_center_iff {x : G} : x ∈ centerOf (fsuU T V) ↔ x = 1 ∨ x = S.cfg.z := by
  constructor
  · rintro ⟨hxU, hxc⟩
    have hxU' : x ∈ Q₁ ⊔ Q₂ := S.sup ▸ hxU
    refine (S.cfg.center_iff hxU').mp fun q hq => ?_
    exact (Subgroup.mem_centralizer_iff.mp hxc q (S.sup ▸ hq)).symm
  · rintro (rfl | rfl)
    · exact (centerOf (fsuU T V)).one_mem
    · refine ⟨S.Q₁_le S.cfg.z_mem_A, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      exact S.cfg.z_comm_sup (S.sup ▸ hq)

theorem center_le_Q₁ : centerOf (fsuU T V) ≤ Q₁ := by
  intro x hx
  rcases S.mem_center_iff.mp hx with rfl | rfl
  · exact Q₁.one_mem
  · exact S.cfg.z_mem_A

theorem center_le_Q₂ : centerOf (fsuU T V) ≤ Q₂ := by
  intro x hx
  rcases S.mem_center_iff.mp hx with rfl | rfl
  · exact Q₂.one_mem
  · exact S.cfg.z_mem_B

theorem sq_ne_one_of_mem_Q₁ {q : G} (hq : q ∈ Q₁) (hqZ : q ∉ centerOf (fsuU T V)) :
    q * q ≠ 1 := by
  obtain ⟨u, rfl⟩ := S.cfg.exists_phiA hq
  rcases q8_sq_ne u with rfl | rfl | hu
  · exact absurd (S.mem_center_iff.mpr (Or.inl (map_one _))) hqZ
  · exact absurd (S.mem_center_iff.mpr (Or.inr rfl)) hqZ
  · rw [← map_mul]
    exact fun h1 => hu (S.cfg.phiA_inj (by rw [h1, map_one]))

theorem sq_ne_one_of_mem_Q₂ {q : G} (hq : q ∈ Q₂) (hqZ : q ∉ centerOf (fsuU T V)) :
    q * q ≠ 1 := by
  obtain ⟨u, rfl⟩ := S.cfg.exists_phiB hq
  rcases q8_sq_ne u with rfl | rfl | hu
  · exact absurd (S.mem_center_iff.mpr (Or.inl (map_one _))) hqZ
  · exact absurd (S.mem_center_iff.mpr (Or.inr S.cfg.phiB_a2)) hqZ
  · rw [← map_mul]
    exact fun h1 => hu (S.cfg.phiB_inj (by rw [h1, map_one]))

omit [Finite G] S in
theorem hat_inf_eq_bot {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ∈ fsuU T V → a⁻¹ * b ∈ centerOf (fsuU T V) →
      b ∈ centerOf (fsuU T V)) : D.hat A ⊓ D.hat B = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwA, hwB⟩
  obtain ⟨a, ha, haU, rfl⟩ := (L128A.HatU.mem_hat D).mp hwA
  obtain ⟨b, hb, hbU, hba⟩ := (L128A.HatU.mem_hat D).mp hwB
  have h1 : a⁻¹ * b ∈ centerOf (fsuU T V) := (D.π_eq_iff a haU b hbU).mp hba.symm
  rw [Submodule.mem_bot, ← hba]
  exact (L128A.HatU.π_eq_zero_iff D hbU).mpr (hAB a ha b hb haU h1)

theorem hat_Q_inf : D.hat Q₁ ⊓ D.hat Q₂ = ⊥ := by
  refine hat_inf_eq_bot fun a ha b hb _ hab => ?_
  have hb1 : b ∈ Q₁ := by
    have : b = a * (a⁻¹ * b) := by group
    rw [this]
    exact Q₁.mul_mem ha (S.center_le_Q₁ hab)
  rcases (S.cfg.mem_inf_iff b).mp ⟨hb1, hb⟩ with rfl | rfl
  · exact (centerOf (fsuU T V)).one_mem
  · exact S.mem_center_iff.mpr (Or.inr rfl)

theorem hat_V_inf_Q₁ : D.hat V ⊓ D.hat Q₁ = ⊥ := by
  refine hat_inf_eq_bot fun a ha b hb _ hab => ?_
  have hbV : b ∈ V := by
    have : b = a * (a⁻¹ * b) := by group
    rw [this, S.zU] at *
    exact V.mul_mem ha (S.plane.1.1 (S.plane.2 hab))
  have hb2 : b * b = 1 := by rw [← pow_two]; exact S.elem.2 b hbV
  by_contra hbZ
  exact S.sq_ne_one_of_mem_Q₁ hb hbZ hb2

theorem hat_V_inf_Q₂ : D.hat V ⊓ D.hat Q₂ = ⊥ := by
  refine hat_inf_eq_bot fun a ha b hb _ hab => ?_
  have hbV : b ∈ V := by
    have : b = a * (a⁻¹ * b) := by group
    rw [this, S.zU] at *
    exact V.mul_mem ha (S.plane.1.1 (S.plane.2 hab))
  have hb2 : b * b = 1 := by rw [← pow_two]; exact S.elem.2 b hbV
  by_contra hbZ
  exact S.sq_ne_one_of_mem_Q₂ hb hbZ hb2

theorem card_hat_Q₁ : Nat.card ↥(D.hat Q₁) = 4 := by
  have h := D.card_eq_mul_range S.Q₁_le
  rw [← L14323.card_hat_eq D S.Q₁_le, S.cfg.card_A, inf_eq_right.mpr S.center_le_Q₁, S.zU,
    S.card2] at h
  omega

theorem card_hat_Q₂ : Nat.card ↥(D.hat Q₂) = 4 := by
  have h := D.card_eq_mul_range S.Q₂_le
  rw [← L14323.card_hat_eq D S.Q₂_le, S.cfg.card_B, inf_eq_right.mpr S.center_le_Q₂, S.zU,
    S.card2] at h
  omega

omit [Finite G] S in
theorem finrank_eq_two {P : Submodule (ZMod 2) D.V} (h : Nat.card P = 4) :
    Module.finrank (ZMod 2) P = 2 := by
  have h2 := L14323.card_submodule P
  rw [h] at h2
  exact Nat.pow_right_injective le_rfl (h2.symm.trans (by norm_num))

theorem sup_eq_top {A B : Submodule (ZMod 2) D.V} (hA : Nat.card A = 4) (hB : Nat.card B = 4)
    (hAB : A ⊓ B = ⊥) : A ⊔ B = ⊤ := by
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hAB, finrank_bot, finrank_eq_two hA, finrank_eq_two hB] at h
  exact Submodule.eq_top_of_finrank_eq (by rw [S.dim]; omega)

theorem hat_Q_sup : D.hat Q₁ ⊔ D.hat Q₂ = ⊤ := S.sup_eq_top S.card_hat_Q₁ S.card_hat_Q₂ S.hat_Q_inf

theorem hat_V_sup_Q₁ : D.hat V ⊔ D.hat Q₁ = ⊤ :=
  S.sup_eq_top S.hatE.2 S.card_hat_Q₁ S.hat_V_inf_Q₁

theorem hat_V_sup_Q₂ : D.hat V ⊔ D.hat Q₂ = ⊤ :=
  S.sup_eq_top S.hatE.2 S.card_hat_Q₂ S.hat_V_inf_Q₂

omit [Finite G] S in
theorem rho_mem_hat {A : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G)) (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    {w : D.V} (hw : w ∈ D.hat A) : D.ρ ⟨x, hxN⟩ w ∈ D.hat A := by
  obtain ⟨a, ha, haU, rfl⟩ := (L128A.HatU.mem_hat D).mp hw
  rw [D.ρ_π ⟨x, hxN⟩ a haU]
  exact L128A.HatU.π_mem_hat D (hxA a ha) (L128A.HatU.conj_mem hxN haU)

theorem K_norm : oTwoUpper (l32nH T V) ≤
    Subgroup.normalizer (Q₁ : Set G) ⊓ Subgroup.normalizer (Q₂ : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyH, hyodd⟩
  have hyU : ∀ q ∈ Q₁ ⊔ Q₂, y * q * y⁻¹ ∈ Q₁ ⊔ Q₂ := fun q hq => by
    rw [S.sup] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp (L14332.l32nH_le_normalizer_fsuU T V hyH) q).mp hq
  exact S.cfg.mem_normalizers_of_odd hyU hyodd

theorem Wg_norm_V {x : G} (hx : x ∈ CFSG.conjugate (l32nW T V V₂) g) :
    x ∈ Subgroup.normalizer (V : Set G) := by
  have hxU := L14332.l32nH_le_normalizer_fsuU T V (S.Wg_le_H hx)
  have hxc := Wg_le_cent S.g_normV₂ hx
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  rw [S.eq_E] at hv ⊢
  obtain ⟨⟨hvU, hvc⟩, hvWg⟩ := hv
  have hvc' : v ∈ Subgroup.centralizer (V₂ : Set G) := hvc
  refine ⟨⟨L128A.HatU.conj_mem hxU hvU, ?_⟩, ?_⟩
  · show x * v * x⁻¹ ∈ Subgroup.centralizer (V₂ : Set G)
    rw [Subgroup.mem_centralizer_iff] at hvc' hxc ⊢
    intro a ha
    calc a * (x * v * x⁻¹) = (a * x) * v * x⁻¹ := by group
      _ = (x * a) * v * x⁻¹ := by rw [hxc a ha]
      _ = x * (a * v) * x⁻¹ := by group
      _ = x * (v * a) * x⁻¹ := by rw [hvc' a ha]
      _ = x * v * (x⁻¹ * (x * a) * x⁻¹) := by group
      _ = x * v * (x⁻¹ * (a * x) * x⁻¹) := by rw [← hxc a ha]
      _ = x * v * x⁻¹ * a := by group
  · exact (CFSG.conjugate (l32nW T V V₂) g).mul_mem
      ((CFSG.conjugate (l32nW T V V₂) g).mul_mem hx hvWg)
      ((CFSG.conjugate (l32nW T V V₂) g).inv_mem hx)

theorem sq_mem_Q {x : G} (hx : x ∈ CFSG.conjugate (l32nW T V V₂) g) :
    x * x ∈ pCoreOf 2 (l32nH T V) := by
  have hxH := S.Wg_le_H hx
  have hy : (QuotientGroup.mk ⟨x, hxH⟩ : OTwoQuot (l32nH T V)) ∈
      imageOTwoQuot (l32nH T V) (CFSG.conjugate (l32nW T V V₂) g) := ⟨⟨x, hxH⟩, hx, rfl⟩
  have h2 := Subgroup.orderOf_dvd_natCard _ hy
  rw [S.card_Wg] at h2
  have hy2 : (QuotientGroup.mk (⟨x, hxH⟩ * ⟨x, hxH⟩ : ↥(l32nH T V)) :
      OTwoQuot (l32nH T V)) = 1 := by
    rw [QuotientGroup.mk_mul, ← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  rw [QuotientGroup.eq_one_iff] at hy2
  exact ⟨_, hy2, rfl⟩

theorem rho_eq_one_of_mem_Q {h : G} (hhQ : h ∈ pCoreOf 2 (l32nH T V))
    (hN : h ∈ Subgroup.normalizer (fsuU T V : Set G)) : D.ρ ⟨h, hN⟩ = 1 := by
  have hhH : h ∈ l32nH T V := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hhQ
  rw [L14332.rho_eq_one_iff_mem (D := D) hhH hN, S.cHat]
  exact hhQ

section NonSwap

variable {x : G} (hxW : x ∈ CFSG.conjugate (l32nW T V V₂) g) (hxQ : x ∉ pCoreOf 2 (l32nH T V))
  (hx₁ : x ∈ Subgroup.normalizer (Q₁ : Set G)) (hx₂ : x ∈ Subgroup.normalizer (Q₂ : Set G))
include hxW hxQ hx₁ hx₂

omit hxQ hx₁ hx₂ in
theorem xN : x ∈ Subgroup.normalizer (fsuU T V : Set G) :=
  L14332.l32nH_le_normalizer_fsuU T V (S.Wg_le_H hxW)

omit hxQ hx₁ hx₂ in
theorem rho_x_sq : ∀ w : D.V, D.ρ ⟨x, S.xN hxW⟩ (D.ρ ⟨x, S.xN hxW⟩ w) = w := by
  intro w
  have h1 := S.rho_eq_one_of_mem_Q (S.sq_mem_Q hxW)
    ((Subgroup.normalizer _).mul_mem (S.xN hxW) (S.xN hxW))
  have h2 : D.ρ ⟨x * x, (Subgroup.normalizer _).mul_mem (S.xN hxW) (S.xN hxW)⟩ =
      D.ρ ⟨x, S.xN hxW⟩ * D.ρ ⟨x, S.xN hxW⟩ := by
    rw [← map_mul]
    rfl
  rw [h2] at h1
  exact congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ w) h1

omit hx₁ hx₂ in
theorem rho_x_ne : D.ρ ⟨x, S.xN hxW⟩ ≠ 1 := by
  intro h1
  apply hxQ
  rw [← S.cHat]
  exact (L14332.rho_eq_one_iff_mem (D := D) (S.Wg_le_H hxW) (S.xN hxW)).mp h1

omit hxQ hx₂ in
theorem rho_x_Q₁ {w : D.V} (hw : w ∈ D.hat Q₁) : D.ρ ⟨x, S.xN hxW⟩ w ∈ D.hat Q₁ :=
  rho_mem_hat (S.xN hxW) (fun a ha => (Subgroup.mem_normalizer_iff.mp hx₁ a).mp ha) hw

omit hxQ hx₁ in
theorem rho_x_Q₂ {w : D.V} (hw : w ∈ D.hat Q₂) : D.ρ ⟨x, S.xN hxW⟩ w ∈ D.hat Q₂ :=
  rho_mem_hat (S.xN hxW) (fun a ha => (Subgroup.mem_normalizer_iff.mp hx₂ a).mp ha) hw

omit hxQ hx₁ hx₂ in
theorem rho_x_V {w : D.V} (hw : w ∈ D.hat V) : D.ρ ⟨x, S.xN hxW⟩ w ∈ D.hat V :=
  rho_mem_hat (S.xN hxW) (fun a ha => (Subgroup.mem_normalizer_iff.mp (S.Wg_norm_V hxW) a).mp ha)
    hw

omit hx₁ in
theorem nontriv₁ : ∃ w ∈ D.hat Q₁, D.ρ ⟨x, S.xN hxW⟩ w ≠ w := by
  by_contra hne
  push Not at hne
  apply S.rho_x_ne hxW hxQ
  refine LinearEquiv.ext fun w => ?_
  exact eq_of_trivial_on S.hat_Q_sup S.hat_V_sup_Q₁ S.hat_V_inf_Q₂
    (D.ρ ⟨x, S.xN hxW⟩).toLinearMap (fun _ hw => S.rho_x_Q₂ hxW hx₂ hw)
    (fun _ hw => S.rho_x_V hxW hw) hne w

omit hx₂ in
theorem nontriv₂ : ∃ w ∈ D.hat Q₂, D.ρ ⟨x, S.xN hxW⟩ w ≠ w := by
  by_contra hne
  push Not at hne
  apply S.rho_x_ne hxW hxQ
  refine LinearEquiv.ext fun w => ?_
  exact eq_of_trivial_on (by rw [sup_comm]; exact S.hat_Q_sup) S.hat_V_sup_Q₂ S.hat_V_inf_Q₁
    (D.ρ ⟨x, S.xN hxW⟩).toLinearMap (fun _ hw => S.rho_x_Q₁ hxW hx₁ hw)
    (fun _ hw => S.rho_x_V hxW hw) hne w

noncomputable def basis₁ : Module.Basis (Fin 2) (ZMod 2) ↥(D.hat Q₁) :=
  have : Module.Finite (ZMod 2) ↥(D.hat Q₁) := Module.Finite.of_finite
  Module.finBasisOfFinrankEq (ZMod 2) _ (finrank_eq_two S.card_hat_Q₁)

noncomputable def basis₂ : Module.Basis (Fin 2) (ZMod 2) ↥(D.hat Q₂) :=
  have : Module.Finite (ZMod 2) ↥(D.hat Q₂) := Module.Finite.of_finite
  Module.finBasisOfFinrankEq (ZMod 2) _ (finrank_eq_two S.card_hat_Q₂)

theorem inv_of_normalizes {k : G} (hk : k ∈ oTwoUpper (l32nH T V)) :
    x * k * x⁻¹ * k ∈ pCoreOf 2 (l32nH T V) := by
  have hkH : k ∈ l32nH T V := oTwoUpper_le _ hk
  have hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G) := L14332.l32nH_le_normalizer_fsuU T V hkH
  set ρx := D.ρ ⟨x, S.xN hxW⟩ with hρx
  set ρk := D.ρ ⟨k, hkN⟩ with hρk
  have hk3 : ∀ w : D.V, ρk (ρk (ρk w)) = w := by
    have hkK : (QuotientGroup.mk ⟨k, hkH⟩ : OTwoQuot (l32nH T V)) ∈
        imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V)) := ⟨⟨k, hkH⟩, hk, rfl⟩
    have h1 := S.kElem.2 _ hkK
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    have hk3Q : k ^ 3 ∈ pCoreOf 2 (l32nH T V) := ⟨_, h1, by simp⟩
    have h2 := S.rho_eq_one_of_mem_Q hk3Q ((Subgroup.normalizer _).pow_mem hkN 3)
    have h3 : D.ρ ⟨k ^ 3, (Subgroup.normalizer _).pow_mem hkN 3⟩ = ρk ^ 3 := by
      rw [← map_pow]
      rfl
    intro w
    rw [h3] at h2
    have := congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ w) h2
    simpa [pow_succ] using this
  have hxx := S.rho_x_sq hxW
  have hk₁ : ∀ a ∈ Q₁, k * a * k⁻¹ ∈ Q₁ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (S.K_norm hk).1 a).mp ha
  have hk₂ : ∀ a ∈ Q₂, k * a * k⁻¹ ∈ Q₂ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (S.K_norm hk).2 a).mp ha
  obtain ⟨w₁, hw₁, hw₁'⟩ := S.nontriv₁ hxW hxQ hx₂
  obtain ⟨w₂, hw₂, hw₂'⟩ := S.nontriv₂ hxW hxQ hx₁
  have h₁ := inv_of_involution S.basis₁ (f := ρx.toLinearMap) (k := ρk.toLinearMap)
    (fun _ hw => S.rho_x_Q₁ hxW hx₁ hw) (fun _ hw => rho_mem_hat hkN hk₁ hw)
    (fun w _ => hxx w) ⟨w₁, hw₁, hw₁'⟩ (fun w _ => hk3 w)
  have h₂ := inv_of_involution S.basis₂ (f := ρx.toLinearMap) (k := ρk.toLinearMap)
    (fun _ hw => S.rho_x_Q₂ hxW hx₂ hw) (fun _ hw => rho_mem_hat hkN hk₂ hw)
    (fun w _ => hxx w) ⟨w₂, hw₂, hw₂'⟩ (fun w _ => hk3 w)
  have hcN : x * k * x⁻¹ * k ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem
      ((Subgroup.normalizer _).mul_mem (S.xN hxW) hkN)
      ((Subgroup.normalizer _).inv_mem (S.xN hxW))) hkN
  have hρinv : ρx⁻¹ = ρx := by
    refine inv_eq_of_mul_eq_one_right (LinearEquiv.ext fun w => ?_)
    exact hxx w
  have hc : D.ρ ⟨x * k * x⁻¹ * k, hcN⟩ = ρx * ρk * ρx⁻¹ * ρk := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have hc1 : D.ρ ⟨x * k * x⁻¹ * k, hcN⟩ = 1 := by
    rw [hc, hρinv]
    refine LinearEquiv.ext fun w => ?_
    have hw : w ∈ D.hat Q₁ ⊔ D.hat Q₂ := S.hat_Q_sup ▸ Submodule.mem_top
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
    have e1 := h₁ p hp
    have e2 := h₂ q hq
    simp only [LinearEquiv.coe_coe] at e1 e2
    simp only [LinearEquiv.mul_apply, map_add, e1, e2]
    rfl
  have hcH : x * k * x⁻¹ * k ∈ l32nH T V :=
    (l32nH T V).mul_mem ((l32nH T V).mul_mem ((l32nH T V).mul_mem (S.Wg_le_H hxW) hkH)
      ((l32nH T V).inv_mem (S.Wg_le_H hxW))) hkH
  rw [← S.cHat]
  exact (L14332.rho_eq_one_iff_mem (D := D) hcH hcN).mp hc1

omit hxQ hx₁ hx₂ in
theorem rho_zpow {y : G} (hy : y ∈ Subgroup.zpowers x)
    (hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨y, hyN⟩ = 1 ∨ D.ρ ⟨y, hyN⟩ = D.ρ ⟨x, S.xN hxW⟩ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hσ : D.ρ ⟨x, S.xN hxW⟩ * D.ρ ⟨x, S.xN hxW⟩ = 1 :=
    LinearEquiv.ext fun w => S.rho_x_sq hxW w
  have e : D.ρ ⟨x ^ n, hyN⟩ = D.ρ ⟨x, S.xN hxW⟩ ^ n := by
    rw [← map_zpow]
    rfl
  rw [e]
  rcases Int.even_or_odd' n with ⟨r, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hσ, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hσ, one_zpow, one_mul, zpow_one]

end NonSwap

theorem pow_four_of_mem_Q₁ {q : G} (hq : q ∈ Q₁) : q ^ 4 = 1 := by
  obtain ⟨u, rfl⟩ := S.cfg.exists_phiA hq
  have key : ∀ u : Q8SqE9.Q8, u ^ 4 = 1 := by decide
  rw [← map_pow, key, map_one]

theorem pow_four_of_mem_Q₂ {q : G} (hq : q ∈ Q₂) : q ^ 4 = 1 := by
  obtain ⟨u, rfl⟩ := S.cfg.exists_phiB hq
  have key : ∀ u : Q8SqE9.Q8, u ^ 4 = 1 := by decide
  rw [← map_pow, key, map_one]

omit [Finite G] S in
theorem orderOf_eq_four {q : G} (hq4 : q ^ 4 = 1) (hq2 : q * q ≠ 1) : orderOf q = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one, pow_two]; exact hq2)
    (by simpa using hq4)

section NonSwap

variable {x : G} (hxW : x ∈ CFSG.conjugate (l32nW T V V₂) g) (hxQ : x ∉ pCoreOf 2 (l32nH T V))
  (hx₁ : x ∈ Subgroup.normalizer (Q₁ : Set G)) (hx₂ : x ∈ Subgroup.normalizer (Q₂ : Set G))
include hxW hxQ hx₁ hx₂

theorem card_of_normalizes :
    Nat.card ↥(⁅fsuU T V, Subgroup.zpowers x⁆ ⊔ fsuV1 T V) = 8 ∧
      ∃ a ∈ ⁅fsuU T V, Subgroup.zpowers x⁆ ⊔ fsuV1 T V, a ^ 2 ≠ 1 := by
  set σ := D.ρ ⟨x, S.xN hxW⟩ with hσ
  have hxx := S.rho_x_sq hxW
  obtain ⟨p₁, hp₁, hp₁0, hp₁r, w₁, hw₁, hw₁p⟩ := range_of_involution S.basis₁
    (f := σ.toLinearMap) (fun _ hw => S.rho_x_Q₁ hxW hx₁ hw) (fun w _ => hxx w)
    (S.nontriv₁ hxW hxQ hx₂)
  obtain ⟨p₂, hp₂, hp₂0, hp₂r, w₂, hw₂, hw₂p⟩ := range_of_involution S.basis₂
    (f := σ.toLinearMap) (fun _ hw => S.rho_x_Q₂ hxW hx₂ hw) (fun w _ => hxx w)
    (S.nontriv₂ hxW hxQ hx₁)
  simp only [LinearEquiv.coe_coe] at hp₁r hw₁p hp₂r hw₂p
  obtain ⟨q₁, hq₁, -, hq₁p⟩ := (L128A.HatU.mem_hat D).mp hp₁
  obtain ⟨q₂, hq₂, -, hq₂p⟩ := (L128A.HatU.mem_hat D).mp hp₂
  have hq₁U := S.Q₁_le hq₁
  have hq₂U := S.Q₂_le hq₂
  have hq₁Z : q₁ ∉ centerOf (fsuU T V) := fun h =>
    hp₁0 (by rw [← hq₁p]; exact (L128A.HatU.π_eq_zero_iff D hq₁U).mpr h)
  have hq₂Z : q₂ ∉ centerOf (fsuU T V) := fun h =>
    hp₂0 (by rw [← hq₂p]; exact (L128A.HatU.π_eq_zero_iff D hq₂U).mpr h)
  have hq₁2 := S.sq_ne_one_of_mem_Q₁ hq₁ hq₁Z
  have hq₂2 := S.sq_ne_one_of_mem_Q₂ hq₂ hq₂Z
  have hsq : ∀ u : Q8SqE9.Q8, u * u = 1 ∨ u * u = QuaternionGroup.a 2 := by decide
  have hq₁z : q₁ * q₁ = S.cfg.z := by
    obtain ⟨u, rfl⟩ := S.cfg.exists_phiA hq₁
    rcases hsq u with h | h
    · exact absurd (by rw [← map_mul, h, map_one]) hq₁2
    · rw [← map_mul, h]
      rfl
  have hq₂z : q₂ * q₂ = S.cfg.z := by
    obtain ⟨u, rfl⟩ := S.cfg.exists_phiB hq₂
    rcases hsq u with h | h
    · exact absurd (by rw [← map_mul, h, map_one]) hq₂2
    · rw [← map_mul, h]
      exact S.cfg.phiB_a2
  set R := Subgroup.zpowers q₁ ⊔ Subgroup.zpowers q₂ with hR
  have hzR : S.cfg.z ∈ R := by
    rw [← hq₁z]
    exact Subgroup.mem_sup_left ((Subgroup.zpowers q₁).mul_mem (Subgroup.mem_zpowers q₁)
      (Subgroup.mem_zpowers q₁))
  have hZR : centerOf (fsuU T V) ≤ R := by
    intro c hc
    rcases S.mem_center_iff.mp hc with rfl | rfl
    · exact R.one_mem
    · exact hzR
  have hpre : ∀ n ∈ fsuU T V, D.π n ∈ Submodule.span (ZMod 2) ({p₁, p₂} : Set D.V) → n ∈ R := by
    intro n hn hpn
    obtain ⟨c₁, c₂, hc⟩ := Submodule.mem_span_pair.mp hpn
    have key : ∀ m ∈ R, m ∈ fsuU T V → D.π m = D.π n → n ∈ R := by
      intro m hmR hmU hmn
      have h1 : m⁻¹ * n ∈ centerOf (fsuU T V) := (D.π_eq_iff m hmU n hn).mp hmn
      have : n = m * (m⁻¹ * n) := by group
      rw [this]
      exact R.mul_mem hmR (hZR h1)
    have hq₁R : q₁ ∈ R := Subgroup.mem_sup_left (Subgroup.mem_zpowers q₁)
    have hq₂R : q₂ ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers q₂)
    have hc' : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc' c₁ with rfl | rfl <;> rcases hc' c₂ with rfl | rfl
    · exact key 1 R.one_mem (one_mem _) (by rw [L128A.HatU.π_one, ← hc]; simp)
    · exact key q₂ hq₂R hq₂U (by rw [hq₂p, ← hc]; simp)
    · exact key q₁ hq₁R hq₁U (by rw [hq₁p, ← hc]; simp)
    · exact key (q₁ * q₂) (R.mul_mem hq₁R hq₂R) ((fsuU T V).mul_mem hq₁U hq₂U)
        (by rw [D.π_mul _ hq₁U _ hq₂U, hq₁p, hq₂p, ← hc]; simp)
  have hspan₁ : p₁ ∈ Submodule.span (ZMod 2) ({p₁, p₂} : Set D.V) :=
    Submodule.subset_span (by simp)
  have hspan₂ : p₂ ∈ Submodule.span (ZMod 2) ({p₁, p₂} : Set D.V) :=
    Submodule.subset_span (by simp)
  have hrange : ∀ u ∈ fsuU T V,
      σ (D.π u) - D.π u ∈ Submodule.span (ZMod 2) ({p₁, p₂} : Set D.V) := by
    intro u hu
    have hu' : D.π u ∈ D.hat Q₁ ⊔ D.hat Q₂ := S.hat_Q_sup ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu'
    rw [← hab, map_add]
    have e : σ a + σ b - (a + b) = (σ a - a) + (σ b - b) := by abel
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · rcases hp₁r a ha with h | h <;> rw [h]
      · exact Submodule.zero_mem _
      · exact hspan₁
    · rcases hp₂r b hb with h | h <;> rw [h]
      · exact Submodule.zero_mem _
      · exact hspan₂
  have hcommR : ⁅fsuU T V, Subgroup.zpowers x⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro u hu y hy
    have hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G) :=
      Subgroup.zpowers_le.mpr (S.xN hxW) hy
    have hyu : y * u⁻¹ * y⁻¹ ∈ fsuU T V := L128A.HatU.conj_mem hyN ((fsuU T V).inv_mem hu)
    have hcU : ⁅u, y⁆ ∈ fsuU T V := by
      rw [commutatorElement_def, mul_assoc u y, mul_assoc u]
      exact (fsuU T V).mul_mem hu (by simpa [mul_assoc] using hyu)
    refine hpre _ hcU ?_
    have hπ : D.π ⁅u, y⁆ = D.π u - D.ρ ⟨y, hyN⟩ (D.π u) := by
      have e1 : ⁅u, y⁆ = u * (y * u⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [e1, D.π_mul _ hu _ hyu, ← D.ρ_π ⟨y, hyN⟩ _ ((fsuU T V).inv_mem hu),
        L128A.HatU.π_inv D hu, map_neg, sub_eq_add_neg]
    rw [hπ]
    rcases S.rho_zpow hxW hy hyN with h | h
    · rw [h]
      show D.π u - D.π u ∈ _
      rw [sub_self]
      exact Submodule.zero_mem _
    · rw [h, ← neg_sub]
      exact Submodule.neg_mem _ (hrange u hu)
  have hNR : ⁅fsuU T V, Subgroup.zpowers x⁆ ⊔ fsuV1 T V ≤ R := by
    refine sup_le hcommR ?_
    rw [← S.zU]
    exact hZR
  have hRN : R ≤ ⁅fsuU T V, Subgroup.zpowers x⁆ ⊔ fsuV1 T V := by
    have hmem : ∀ (q : G) (w : D.V), q ∈ fsuU T V → w ∈ D.hat Q₁ ⊔ D.hat Q₂ →
        D.π q = σ w - w → q ∈ ⁅fsuU T V, Subgroup.zpowers x⁆ ⊔ fsuV1 T V := by
      intro q w hqU _ hqw
      obtain ⟨u, hu, rfl⟩ := D.π_surj w
      have hc : x * u * x⁻¹ * u⁻¹ ∈ ⁅fsuU T V, Subgroup.zpowers x⁆ := by
        have : x * u * x⁻¹ * u⁻¹ = ⁅u, x⁆⁻¹ := by rw [commutatorElement_def]; group
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers x))
      have hcU : x * u * x⁻¹ * u⁻¹ ∈ fsuU T V :=
        (fsuU T V).mul_mem (L128A.HatU.conj_mem (S.xN hxW) hu) ((fsuU T V).inv_mem hu)
      have h1 : D.π (x * u * x⁻¹ * u⁻¹) = D.π q := by
        rw [hqw, ← L128A.HatU.rho_sub_π D (S.xN hxW) hu]
      have h2 : (x * u * x⁻¹ * u⁻¹)⁻¹ * q ∈ centerOf (fsuU T V) :=
        (D.π_eq_iff _ hcU q hqU).mp h1
      have : q = (x * u * x⁻¹ * u⁻¹) * ((x * u * x⁻¹ * u⁻¹)⁻¹ * q) := by group
      rw [this]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right ?_)
      rw [← S.zU]
      exact h2
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact hmem q₁ w₁ hq₁U (Submodule.mem_sup_left hw₁) (by rw [hq₁p, hw₁p])
    · exact hmem q₂ w₂ hq₂U (Submodule.mem_sup_right hw₂) (by rw [hq₂p, hw₂p])
  have hNeq : ⁅fsuU T V, Subgroup.zpowers x⁆ ⊔ fsuV1 T V = R := le_antisymm hNR hRN
  have hq₁4 := orderOf_eq_four (S.pow_four_of_mem_Q₁ hq₁) hq₁2
  have hq₂4 := orderOf_eq_four (S.pow_four_of_mem_Q₂ hq₂) hq₂2
  have hcomm : ∀ a ∈ Subgroup.zpowers q₁, ∀ b ∈ Subgroup.zpowers q₂, a * b = b * a := by
    intro a ha b hb
    have haQ : a ∈ Q₁ := Subgroup.zpowers_le.mpr hq₁ ha
    have hbQ : b ∈ Q₂ := Subgroup.zpowers_le.mpr hq₂ hb
    exact (Subgroup.mem_centralizer_iff.mp (S.cfg.comm haQ) b hbQ).symm
  have hinf : Subgroup.zpowers q₁ ⊓ Subgroup.zpowers q₂ = centerOf (fsuU T V) := by
    apply le_antisymm
    · rintro c ⟨hc₁, hc₂⟩
      have := (S.cfg.mem_inf_iff c).mp
        ⟨Subgroup.zpowers_le.mpr hq₁ hc₁, Subgroup.zpowers_le.mpr hq₂ hc₂⟩
      exact S.mem_center_iff.mpr this
    · intro c hc
      rcases S.mem_center_iff.mp hc with rfl | rfl
      · exact one_mem _
      · refine ⟨?_, ?_⟩
        · rw [← hq₁z]
          exact Subgroup.mul_mem _ (Subgroup.mem_zpowers q₁) (Subgroup.mem_zpowers q₁)
        · rw [← hq₂z]
          exact Subgroup.mul_mem _ (Subgroup.mem_zpowers q₂) (Subgroup.mem_zpowers q₂)
  have hcard := RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hcomm
  rw [hinf, S.zU, S.card2, Nat.card_zpowers, Nat.card_zpowers, hq₁4, hq₂4] at hcard
  have hR8 : Nat.card ↥R = 8 := by rw [hR]; omega
  refine ⟨by rw [hNeq]; exact hR8, q₁, ?_, by rw [pow_two]; exact hq₁2⟩
  rw [hNeq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers q₁)

end NonSwap

end Setup3

end L1444

end CFSG.Quasithin.H13

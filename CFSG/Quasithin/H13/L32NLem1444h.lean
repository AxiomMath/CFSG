module

public import CFSG.Quasithin.H13.L32NLem1444g
public import CFSG.Quasithin.H13.L32NLem1444c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

section LinAlg

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem mat_fix3 : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2), A * A * A ≠ 1 ∨ A = 1 ∨
    ∀ v : Fin 2 → ZMod 2, A.mulVec v = v → v = 0 := by
  decide

variable {P : Submodule (ZMod 2) W}

theorem equivFun_restrict (b : Module.Basis (Fin 2) (ZMod 2) P) {f : W →ₗ[ZMod 2] W}
    (hf : ∀ w ∈ P, f w ∈ P) (x : P) :
    b.equivFun (f.restrict hf x) =
      (LinearMap.toMatrix b b (f.restrict hf)).mulVec (b.equivFun x) := by
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]

theorem trivial_of_fix (b : Module.Basis (Fin 2) (ZMod 2) P) {f : W →ₗ[ZMod 2] W}
    (hf : ∀ w ∈ P, f w ∈ P) (hf3 : ∀ w ∈ P, f (f (f w)) = w) {w₀ : W} (hw₀ : w₀ ∈ P)
    (hw₀0 : w₀ ≠ 0) (hfix : f w₀ = w₀) : ∀ w ∈ P, f w = w := by
  set M := LinearMap.toMatrix b b (f.restrict hf) with hM
  have h3 : f.restrict hf * f.restrict hf * f.restrict hf = 1 := by
    ext x
    simp [LinearMap.restrict_apply, hf3 x x.2]
  have hK : M * M * M = 1 := by
    rw [hM, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, h3, LinearMap.toMatrix_one]
  have hone : ∀ N : P →ₗ[ZMod 2] P, LinearMap.toMatrix b b N = 1 → N = 1 := fun N hN =>
    (LinearMap.toMatrix b b).injective (by rw [hN, LinearMap.toMatrix_one])
  rcases mat_fix3 M with h | h | h
  · exact absurd hK h
  · intro w hw
    have := congrArg (fun N : P →ₗ[ZMod 2] P => (N ⟨w, hw⟩ : W)) (hone _ h)
    simpa [LinearMap.restrict_apply] using this
  · exfalso
    apply hw₀0
    have h1 : M.mulVec (b.equivFun ⟨w₀, hw₀⟩) = b.equivFun ⟨w₀, hw₀⟩ := by
      rw [hM, ← equivFun_restrict]
      congr 1
      exact Subtype.ext hfix
    have h2 : (⟨w₀, hw₀⟩ : P) = 0 := b.equivFun.injective (by rw [h _ h1, map_zero])
    exact congrArg Subtype.val h2

end LinAlg

variable {G : Type} [Group G] [Finite G]

structure Setup4 (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (Q₁ Q₂ : Subgroup G) : Prop
    extends Setup3 G T L V V₂ g D Q₁ Q₂ where
  vO : V = pCoreOf 2 L
  cardL : Nat.card L = 1344
  centL : L ⊓ Subgroup.centralizer (V : Set G) = V
  TL : T ≤ Subgroup.normalizer (L : Set G)
  QT : pCoreOf 2 (l32nH T V) ≤ T
  y_ex : ∃ y ∈ L, y ∈ l32nH T V ∧ y ^ 3 = 1 ∧ y ≠ 1
  normVL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G)
  TH : T ≤ l32nH T V

theorem exists_setup4 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hRest : Lemma14323Rest) {T L V V₂ : Subgroup G} {g : G} (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (h32 : Nat.card ↥(fsuU T V) = 2 ^ 5)
    (hG2 : ¬ LieModel G .G2 0 3 1) (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgH : g ∉ l32nH T V) :
    ∃ (D : HatModelU (fsuU T V)) (Q₁ Q₂ : Subgroup G), Setup4 G T L V V₂ g D Q₁ Q₂ := by
  obtain ⟨D, Q₁, Q₂, S⟩ :=
    exists_setup3 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h hext h32 hG2 hV₂ hgP hgH
  have hVO := lemma1444Four_of_inputs h1332 h1334 h1222 h12213 G T L V h hext h32 hG2
  obtain ⟨_, S'⟩ := L14332.exists_setting h1332 h1334 h1222 h hV₂
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hTS := h.isSylowTwoOf_l32nH hV
  have hcardL : Nat.card L = 1344 := by
    rw [S'.card_L, ← hVO, S.card8]
  have hcent : L ⊓ Subgroup.centralizer (V : Set G) = V := by rw [S'.cent_eq, ← hVO]
  obtain ⟨z, a, b, hz, hz1, haV₂, haV₁, hb, hbV₂⟩ := S'.exists_basis
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := S'.hV2.1 hz
  have ha : a ∈ V := S'.hV2.2.1 haV₂
  obtain ⟨y, hyL, hy3, hyz, hya, -⟩ := S'.exists_rot hzV ha hb
    (fun h => haV₁ (h ▸ one_mem _)) (fun h => hbV₂ (h ▸ one_mem _))
    (fun h => haV₁ (h ▸ hz)) (fun h => hbV₂ (h ▸ hzV₂)) (fun h => hbV₂ (h ▸ haV₂))
    (fun h => hbV₂ (h ▸ mul_mem hzV₂ haV₂))
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hbV₂
    rw [← hya]
    simpa using haV₂
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    ((lemma1433Five_of_inputs h1332 h1334 G T L V h.hyp h.fsu).le hx).1
  exact ⟨D, Q₁, Q₂, S, hVO, hcardL, hcent, S'.TL, pCoreOf_two_le_of_isSylowTwoOf hTS,
    ⟨y, hyL, S'.mem_g1 hz hz1 hyz, hy3, hy1⟩, hNL, hTS.1⟩

namespace Setup4

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem V_le_L : V ≤ L := S.vO ▸ pCoreOf_le 2 L

theorem L_le_normV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans S.normV

theorem g_normL : g ∈ Subgroup.normalizer (L : Set G) :=
  (sup_le Subgroup.le_normalizer S.TL) S.gP.1

theorem rho_y_fpf {y : G} (hyL : y ∈ L) (hyH : y ∈ l32nH T V) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (w : D.V) (hw : D.ρ ⟨y, L14332.l32nH_le_normalizer_fsuU T V hyH⟩ w = w) : w = 0 := by
  set yN : ↥(Subgroup.normalizer (fsuU T V : Set G)) :=
    ⟨y, L14332.l32nH_le_normalizer_fsuU T V hyH⟩ with hyN
  have hyK : y ∈ oTwoUpper (l32nH T V) :=
    mem_oTwoUpper_of_odd hyH (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy3))
  have hy₁ : ∀ a ∈ Q₁, y * a * y⁻¹ ∈ Q₁ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (S.K_norm hyK).1 a).mp ha
  have hy₂ : ∀ a ∈ Q₂, y * a * y⁻¹ ∈ Q₂ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (S.K_norm hyK).2 a).mp ha
  have hyV : ∀ a ∈ V, y * a * y⁻¹ ∈ V := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (S.L_le_normV hyL) a).mp ha
  have h3 : ∀ v : D.V, D.ρ yN (D.ρ yN (D.ρ yN v)) = v := by
    have hρ3 : D.ρ yN ^ 3 = 1 := by
      rw [← map_pow]
      have : yN ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    intro v
    have := congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ v) hρ3
    simpa [pow_succ] using this
  have hne : ∀ P₁ P₂ : Submodule (ZMod 2) D.V, P₁ ⊔ P₂ = ⊤ → D.hat V ⊔ P₁ = ⊤ →
      D.hat V ⊓ P₂ = ⊥ → (∀ v ∈ P₂, D.ρ yN v ∈ P₂) → ¬ ∀ v ∈ P₁, D.ρ yN v = v := by
    intro P₁ P₂ h12 hS1 hS2 hP₂ hP₁
    apply hy1
    refine eq_one_of_mem_pCoreOf (H := l32nH T V) ?_ hy3
    rw [← S.cHat]
    refine (L14332.rho_eq_one_iff_mem (D := D) hyH yN.2).mp (LinearEquiv.ext fun v => ?_)
    exact eq_of_trivial_on h12 hS1 hS2 (D.ρ yN).toLinearMap hP₂
      (fun _ hv => Setup3.rho_mem_hat yN.2 hyV hv) hP₁ v
  have hw' : w ∈ D.hat Q₁ ⊔ D.hat Q₂ := S.hat_Q_sup ▸ Submodule.mem_top
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hw'
  have hρ₁ : D.ρ yN w₁ ∈ D.hat Q₁ := Setup3.rho_mem_hat yN.2 hy₁ hw₁
  have hρ₂ : D.ρ yN w₂ ∈ D.hat Q₂ := Setup3.rho_mem_hat yN.2 hy₂ hw₂
  have hdiff : D.ρ yN w₁ - w₁ ∈ D.hat Q₁ ⊓ D.hat Q₂ := by
    refine ⟨Submodule.sub_mem _ hρ₁ hw₁, ?_⟩
    have e : D.ρ yN w₁ - w₁ = w₂ - D.ρ yN w₂ := by
      rw [map_add] at hw
      calc D.ρ yN w₁ - w₁ = (D.ρ yN w₁ + D.ρ yN w₂) - w₁ - D.ρ yN w₂ := by abel
        _ = (w₁ + w₂) - w₁ - D.ρ yN w₂ := by rw [hw]
        _ = w₂ - D.ρ yN w₂ := by abel
    rw [e]
    exact Submodule.sub_mem _ hw₂ hρ₂
  rw [S.hat_Q_inf, Submodule.mem_bot, sub_eq_zero] at hdiff
  have hfix₂ : D.ρ yN w₂ = w₂ := by
    rw [map_add, hdiff] at hw
    exact add_left_cancel hw
  have hz₁ : w₁ = 0 := by
    by_contra h0
    exact hne _ _ S.hat_Q_sup S.hat_V_sup_Q₁ S.hat_V_inf_Q₂
      (fun _ hv => Setup3.rho_mem_hat yN.2 hy₂ hv)
      (trivial_of_fix S.basis₁ (fun _ hv => Setup3.rho_mem_hat yN.2 hy₁ hv) (fun v _ => h3 v)
        hw₁ h0 hdiff)
  have hz₂ : w₂ = 0 := by
    by_contra h0
    exact hne _ _ (by rw [sup_comm]; exact S.hat_Q_sup) S.hat_V_sup_Q₂ S.hat_V_inf_Q₁
      (fun _ hv => Setup3.rho_mem_hat yN.2 hy₁ hv)
      (trivial_of_fix S.basis₂ (fun _ hv => Setup3.rho_mem_hat yN.2 hy₂ hv) (fun v _ => h3 v)
        hw₂ h0 hfix₂)
  rw [hz₁, hz₂, add_zero]

theorem U_le_L : fsuU T V ≤ L := by
  obtain ⟨y, hyL, hyH, hy3, hy1⟩ := S.y_ex
  set yN : ↥(Subgroup.normalizer (fsuU T V : Set G)) :=
    ⟨y, L14332.l32nH_le_normalizer_fsuU T V hyH⟩ with hyN
  have hinj : Function.Injective (fun w : D.V => D.ρ yN w - w) := by
    intro w₁ w₂ h12
    have h0 : D.ρ yN (w₁ - w₂) = w₁ - w₂ := by
      have h12' : D.ρ yN w₁ - w₁ = D.ρ yN w₂ - w₂ := h12
      rw [map_sub]
      calc D.ρ yN w₁ - D.ρ yN w₂ = (D.ρ yN w₁ - w₁) - (D.ρ yN w₂ - w₂) + (w₁ - w₂) := by abel
        _ = w₁ - w₂ := by rw [h12', sub_self, zero_add]
    exact sub_eq_zero.mp (S.rho_y_fpf hyL hyH hy3 hy1 _ h0)
  intro u hu
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hinj) (D.π u)
  obtain ⟨u', hu', rfl⟩ := D.π_surj w
  have hyu' : y * u' * y⁻¹ ∈ fsuU T V := L128A.HatU.conj_mem yN.2 hu'
  have hc : y * u' * y⁻¹ * u'⁻¹ ∈ fsuU T V := (fsuU T V).mul_mem hyu' ((fsuU T V).inv_mem hu')
  have hπ : D.π (y * u' * y⁻¹ * u'⁻¹) = D.π u := by
    rw [D.π_mul _ hyu' _ ((fsuU T V).inv_mem hu'), L128A.HatU.π_inv D hu', ← D.ρ_π yN u' hu']
    rw [← sub_eq_add_neg]
    exact hw
  have hz := (D.π_eq_iff _ hc u hu).mp hπ
  rw [S.zU] at hz
  have hu'T : u' ∈ T := S.QT (S.U_le_Q hu')
  have hcL : y * u' * y⁻¹ * u'⁻¹ ∈ L := by
    have h1 : u' * y⁻¹ * u'⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (S.TL hu'T) _).mp (L.inv_mem hyL)
    rw [show y * u' * y⁻¹ * u'⁻¹ = y * (u' * y⁻¹ * u'⁻¹) by group]
    exact L.mul_mem hyL h1
  have e : u = (y * u' * y⁻¹ * u'⁻¹) * ((y * u' * y⁻¹ * u'⁻¹)⁻¹ * u) := by group
  rw [e]
  exact L.mul_mem hcL (S.V_le_L (S.plane.1.1 (S.plane.2 hz)))

theorem Wg_le_L : CFSG.conjugate (l32nW T V V₂) g ≤ L := by
  rintro _ ⟨w, hw, rfl⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem S.g_normL) w).mp
    (S.U_le_L hw.1)
  simpa [MulAut.conj_apply] using h1

theorem TL_le_L : fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g ≤ L := sup_le S.U_le_L S.Wg_le_L

theorem relIndex_TL : (fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g).relIndex L = 21 := by
  have h := Subgroup.relIndex_mul_card (H := fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g) (K := L)
  rw [inf_eq_left.mpr S.TL_le_L, S.card_UWg, S.cardL] at h
  omega

end Setup4

end L1444

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Vol2.Ch11SecD557N
public import CFSG.Quasithin.Background.G2SL3Setting
public import CFSG.Quasithin.Vol2.Ch11SecD557F
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {n : ℕ} {V V₁ L T : Subgroup G}
  (St : L3Setting n V V₁ L T (Subgroup.normalizer (V₁ : Set G)))

include St

omit [Finite G] in
theorem le_centralizer_V₁ :
    conjClosure V (Subgroup.normalizer (V₁ : Set G)) ≤ Subgroup.centralizer (V₁ : Set G) := by
  obtain ⟨hVc, -⟩ := St.hyp.base.elemAbelian
  refine conjClosure_le fun g hg v hv => Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
  have hw' : g⁻¹ * w * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp hw
    exact St.hyp.base.le_V (by simpa using this)
  have hc : (g⁻¹ * w * g) * v = v * (g⁻¹ * w * g) := by
    have := congrArg Subtype.val (hVc.is_comm.comm (⟨_, hw'⟩ : ↥V) ⟨v, hv⟩)
    simpa using this
  calc w * (g * v * g⁻¹) = g * ((g⁻¹ * w * g) * v) * g⁻¹ := by group
    _ = g * (v * (g⁻¹ * w * g)) * g⁻¹ := by rw [hc]
    _ = g * v * g⁻¹ * w := by group

theorem inf_centralizer_U_le :
    V ⊓ Subgroup.centralizer (conjClosure V (Subgroup.normalizer (V₁ : Set G)) : Set G) ≤ V₁ := by
  rintro v ⟨hvV, hvC⟩
  set w := Multiplicative.toAdd (St.D.ψ ⟨v, hvV⟩) with hw
  have hfix : ∀ u : ↥(conjClosure V (Subgroup.normalizer (V₁ : Set G))), St.betaU u • w = w := by
    intro u
    have hu : (u : G) ∈ L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G)) :=
      (le_sup_right : conjClosure V _ ≤ L ⊔ conjClosure V _) u.2
    have h1 := St.D.alpha_psi ⟨u, St.LU_le_normV hu⟩ ⟨v, hvV⟩
    rw [← St.natAct3_Phi ⟨u, hu⟩] at h1
    have h2 : conjAct V ⟨u, St.LU_le_normV hu⟩ ⟨v, hvV⟩ = ⟨v, hvV⟩ := by
      apply Subtype.ext
      rw [conjAct_coe_apply]
      show (u : G) * v * (u : G)⁻¹ = v
      rw [Subgroup.mem_centralizer_iff.mp hvC u u.2, mul_inv_cancel_right]
    rw [h2, natAct3_apply] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd] at h3
    exact h3
  have hQ : ∀ b c : GaloisField 2 n,
      ∃ u : ↥(conjClosure V (Subgroup.normalizer (V₁ : Set G))), St.betaU u = tq b c := by
    intro b c
    have h1 : tq b c ∈ St.Ubar := by rw [St.Ubar_eq_Qv]; exact tq_mem_Qv b c
    obtain ⟨u, hu⟩ := h1
    exact ⟨u, hu⟩
  obtain ⟨u₁, hu₁⟩ := hQ 1 0
  obtain ⟨u₂, hu₂⟩ := hQ 0 1
  have h1 := congrFun (hfix u₁) 0
  have h2 := congrFun (hfix u₂) 0
  rw [hu₁, tq_smul] at h1
  rw [hu₂, tq_smul] at h2
  simp only [Matrix.cons_val_zero, one_mul, zero_mul, add_zero, add_eq_left] at h1 h2
  refine (St.D.line ⟨v, hvV⟩).mpr ⟨w 0, ?_⟩
  rw [← hw]
  funext i
  fin_cases i
  · simp [vE]
  · simp [vE, h1]
  · simp [vE, h2]

theorem center_le
    (hSc : ∀ a ∈ pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))),
      ∀ b ∈ pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))), a * b = b * a)
    (hSV : pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))) ≤
      V ⊔ (pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))) ⊓
        Subgroup.centralizer (L : Set G)))
    (hUL : conjClosure V (Subgroup.normalizer (V₁ : Set G)) ≤
      (conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ L) ⊔
        (conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ Subgroup.centralizer (L : Set G)))
    (hCS : conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ Subgroup.centralizer (L : Set G) ≤
      pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G)))) :
    conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓
        Subgroup.centralizer (conjClosure V (Subgroup.normalizer (V₁ : Set G)) : Set G) ≤
      V₁ ⊔ (conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓
        Subgroup.centralizer (L : Set G)) := by
  set U := conjClosure V (Subgroup.normalizer (V₁ : Set G)) with hUdef
  set S := pCoreOf 2 (L ⊔ U) with hSdef
  have hcomm₁ : ∀ a ∈ U ⊓ L, ∀ b ∈ U ⊓ Subgroup.centralizer (L : Set G), a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp hb.2 a ha.2)
  have hcomm₂ : ∀ a ∈ V, ∀ b ∈ S ⊓ Subgroup.centralizer (L : Set G), a * b = b * a :=
    fun a ha b hb => hSc a (St.hyp.base.V_le_T ha |> fun _ =>
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((le_conjClosure _ _).trans le_sup_right) St.LU_le_normV St.isPGroup_V ha) b hb.1
  rintro z ⟨hzU, hzC⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm₁ (hUL hzU)
  have hbC : b ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup hcomm₁ (hUL hu)
    have h1 : a' * b = b * a' := Subgroup.mem_centralizer_iff.mp hb.2 a' ha'.2
    have h2 : b' * b = b * b' := hSc b' (hCS hb') b (hCS hb)
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have haC : a ∈ Subgroup.centralizer (U : Set G) := by
    have h1 := Subgroup.mul_mem _ hzC (Subgroup.inv_mem _ hbC)
    simpa using h1
  have haK : a ∈ pCoreOf 2 (L ⊔ T) := by
    have hθ : St.D.θ ⟨a, ha.2⟩ = 1 := by
      apply natAct3_injective
      rw [← St.D.alpha_of_mem, map_one]
      refine (St.D.alpha_eq_one_iff _).mpr fun v => ?_
      exact (Subgroup.mem_centralizer_iff.mp haC v ((le_conjClosure _ _) v.2)).symm ▸
        mul_inv_cancel_right _ _
    have h1 : (⟨a, ha.2⟩ : ↥L) ∈ (pCoreOf 2 (L ⊔ T)).subgroupOf L := by
      rw [← St.D.ker_eq]
      exact hθ
    exact h1
  have haS : a ∈ S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left))
      (fun x hx => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
        ((sup_le Subgroup.le_normalizer fun u hu => St.U_le_normL hu) hx))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      (inf_le_pCoreOf_of_normalizer (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
        (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))
        ⟨ha.2, haK⟩)
  obtain ⟨v, hv, c, hc, rfl⟩ := exists_mul_of_mem_sup hcomm₂ (hSV haS)
  have hcC : c ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup hcomm₁ (hUL hu)
    have h1 : a' * c = c * a' := Subgroup.mem_centralizer_iff.mp hc.2 a' ha'.2
    have h2 : b' * c = c * b' := hSc b' (hCS hb') c hc.1
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hvV₁ : v ∈ V₁ := by
    refine inf_centralizer_U_le St ⟨hv, ?_⟩
    have h1 := Subgroup.mul_mem _ haC (Subgroup.inv_mem _ hcC)
    simpa using h1
  have hcU : c ∈ U ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨?_, hc.2⟩
    have h1 : c = v⁻¹ * (v * c) := by group
    rw [h1]
    exact U.mul_mem (U.inv_mem ((le_conjClosure _ _) hv)) ha.1
  rw [mul_assoc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hvV₁)
    (Subgroup.mem_sup_right ((U ⊓ Subgroup.centralizer (L : Set G)).mul_mem hcU hb))

end CFSG.Quasithin.Vol2.Ch11.SecD

module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZC
public import CFSG.Quasithin.Background.C1PackSolvBasic
public import CFSG.Quasithin.Vol2.Ch10SecECase1b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}

omit [Finite G] in
theorem le_normalizer_E (T : Subgroup G) :
    T ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
  (B6.le_normalizer_thompsonJ T).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

omit [Finite G] in
theorem E_le_T (T : Subgroup G) : omegaOneCenterOf (thompsonJ T) ≤ T :=
  (A4.omegaOneCenterOf_le _).trans (B6.thompsonJ_le T)

namespace Ctx

variable (c : Ctx T L I H K n k b hel I' K₀)
include c

theorem exists_SL_two : ∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ), 2 ≤ n ∧
    Nat.card F = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨hn, ⟨F, _, _, hF, he⟩, -⟩ := c.h1
  exact ⟨F, inferInstance, inferInstance, n, hn, hF, he⟩

theorem e23Concl_L0T :
    E2.E23Concl (fsuL0 T L ⊔ T) T (fsuVM T L I) (SecA.isElemAbelian_fsuVM c.hyp) :=
  c.he23 G (fsuL0 T L ⊔ T) T ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (T0 T L : Set G))
    (fsuVM T L I) (SecA.isElemAbelian_fsuVM c.hyp)
    (SecA.minParabolic_L0T c.h37 c.h38 c.hyp c.exists_SL_two) (SecA.sqtkGroup_L0T c.hyp)
    (SecA.charTwo_L0T c.hyp)
    (SecA.isTwoReducedIn_L0T c.h3228 c.hyp (SecA.fsuV_eq_of_cases12 c.h37 c.h38 c.hyp
      (Or.inl ⟨n, c.h1⟩))) c.not_thompsonJ_le

theorem e23Two_L0T :
    IsSylowTwoOf (autI (SecA.isElemAbelian_fsuVM c.hyp) (thompsonJ T))
        (autI (SecA.isElemAbelian_fsuVM c.hyp) (fsuL0 T L)) ∧
      conjClosure (omegaOneCenterOf (thompsonJ T)) (fsuL0 T L) =
        ⁅fsuVM T L I, fsuL0 T L⁆ ⊔
          (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) := by
  obtain ⟨hKJ, I'', hcard, hJeq, hcomm, hind, htrans, htype, -, -, h2, -⟩ := c.e23Concl_L0T
  have hL2 := SecE.isL2Natural_of_case1 c.h37 c.h38 c.h322 c.hyp c.h1 hKJ hcard hJeq hcomm hind
    htrans htype
  have hJH := SecE.autI_thompsonJ_eq_case1 c.h37 c.h38 c.h322 c.hyp c.h1 hKJ hcard hJeq hcomm
    hind htrans htype
  obtain ⟨-, hsyl, -, hcc⟩ := h2 hL2
  rw [SecE.twoResidual_fsuL0_sup c.h37 c.h38 c.hyp] at hcc
  exact ⟨hJH ▸ hsyl, hcc⟩

theorem thompsonJ_le_T0 :
    thompsonJ T ≤ T0 T L ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) :=
  SecE.le_T0_sup_of_autI_le c.h37 c.h38 c.hyp (iSup₂_le fun _ hA => hA.1) c.e23Two_L0T.1.1

theorem exists_mem_Z {P : Subgroup G} (hPE : P ≤ omegaOneCenterOf (thompsonJ T))
    (hPN : T ≤ Subgroup.normalizer (P : Set G)) (hP : P ≠ ⊥) :
    ∃ z ∈ P, z ≠ 1 ∧ z ∈ quasithinOmegaOneCenter T := by
  obtain ⟨z, hz, hz1, hzT⟩ := SecA.exists_ne_one_mem_centralizer c.hyp.fsu.sylow.1
    (hPE.trans (E_le_T T)) hPN hP
  exact ⟨z, hz, hz1, Subgroup.subset_closure ⟨⟨E_le_T T (hPE hz), hzT⟩,
    A4.sq_eq_one_of_mem_omegaOneCenterOf (hPE hz)⟩⟩

theorem inf_centralizer_L0_eq_bot :
    omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
  by_contra hne
  have hN : T ≤ Subgroup.normalizer ((omegaOneCenterOf (thompsonJ T) ⊓
      Subgroup.centralizer (fsuL0 T L : Set G) : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_E T hx,
      SecA.le_normalizer_centralizer le_rfl (SecA.le_fsuM T L hx)⟩
  obtain ⟨z, hz, hz1, hzZ⟩ := c.exists_mem_Z inf_le_left hN hne
  exact hz1 (c.eq_one_of_mem_centralizer_L0 hzZ hz.2)

theorem E_le_V : omegaOneCenterOf (thompsonJ T) ≤ fsuVM T L I := by
  have h := c.e23Two_L0T.2
  rw [c.inf_centralizer_L0_eq_bot, sup_bot_eq, ← SecA.fsuVM_eq_commutator c.hyp.fsu] at h
  exact h ▸ le_conjClosure _ _

theorem Z_le_V : quasithinOmegaOneCenter T ≤ fsuVM T L I :=
  (C1Pack.omegaOneCenterOf_le_omegaOneCenterOf_thompsonJ T).trans c.E_le_V

theorem eq_one_of_mem_centralizer_H {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hzH : z ∈ Subgroup.centralizer (H : Set G)) :
    z = 1 := by
  by_contra hz1
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact c.hyp.not_normal h
  have hloc := c.hyp.fsu.maximal.1
  have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
  have hC0 := c.fsuCVM_eq_bot
  have hzT := quasithinOmegaOneCenter_le_center T hz
  obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ :=
    SecA.exists_mul_of_mem_fsuVM c.h37 c.h38 c.hyp ht htn (c.Z_le_V hz)
  have h12 : ∀ v, v ∈ fsuUL T L I → v ∈ CFSG.conjugate (fsuUL T L I) t → v = 1 := by
    intro v hv1 hv2
    have := SecA.inf_conjugate_le_fsuCVM c.hyp ht htn ⟨hv1, hv2⟩
    rwa [hC0, Subgroup.mem_bot] at this
  have hzt : t * z * t⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hzT.2 t ht, mul_inv_cancel_right]
  have hz12 : z ∈ fsuUL T L I ↔ z ∈ CFSG.conjugate (fsuUL T L I) t := by
    rw [SecA.mem_conjugate_iff, hzt]
  have hw₁1 : w₁ ≠ 1 := by
    rintro rfl
    rw [one_mul] at hw
    subst hw
    exact hz1 (h12 _ (hz12.mpr hw₂) hw₂)
  have hw₂1 : w₂ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hw
    subst hw
    exact hz1 (h12 _ hw₁ (hz12.mp hw₁))
  obtain ⟨_, -, -, ha, -⟩ := c.hyp.three
  have hV₁ : fsuUL T L I ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G) := (ha t ht htn).2.2
  have hV₂ := SecA.conjugate_fsuUL_le_centralizer c.h37 c.h38 c.hyp ht htn
  have hfix : ∀ s : G, s * z * s⁻¹ = z → ∀ {u u' : G}, u * u' = z → s * u' * s⁻¹ = u' →
      s * u * s⁻¹ = u := by
    intro s hs u u' huu' hsu'
    have e : s * u * s⁻¹ * u' = u * u' := by
      calc s * u * s⁻¹ * u' = s * u * s⁻¹ * (s * u' * s⁻¹) := by rw [hsu']
        _ = s * (u * u') * s⁻¹ := by group
        _ = u * u' := by rw [huu', hs]
    exact mul_right_cancel e
  have hcz : ∀ s ∈ T, s * z * s⁻¹ = z := fun s hs => by
    rw [Subgroup.mem_centralizer_iff.mp hzT.2 s hs, mul_inv_cancel_right]
  have hS₁ : ∀ s ∈ T ⊓ L, s * w₁ * s⁻¹ = w₁ := fun s hs =>
    hfix s (hcz s hs.1) hw (by rw [Subgroup.mem_centralizer_iff.mp (hV₂ hw₂) s hs.2,
      mul_inv_cancel_right])
  have hS₂ : ∀ s ∈ T ⊓ CFSG.conjugate L t, s * w₂ * s⁻¹ = w₂ := by
    intro s hs
    have h1 : s * w₁ * s⁻¹ = w₁ := by
      rw [Subgroup.mem_centralizer_iff.mp (hV₁ hw₁) s hs.2, mul_inv_cancel_right]
    have e : w₁ * (s * w₂ * s⁻¹) = w₁ * w₂ := by
      calc w₁ * (s * w₂ * s⁻¹) = s * w₁ * s⁻¹ * (s * w₂ * s⁻¹) := by rw [h1]
        _ = s * (w₁ * w₂) * s⁻¹ := by group
        _ = w₁ * w₂ := by rw [hw, hcz s hs.1]
    exact mul_left_cancel e
  have hbL0 : b ∈ fsuL0 T L := (oTwoUpper_le _ c.hbB0).1
  have hbN : b ∈ Subgroup.normalizer (T0 T L : Set G) := (oTwoUpper_le _ c.hbB0).2
  have hbz : b * z * b⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hzH b c.hbHM.1, mul_inv_cancel_right]
  have hN₁ : fsuL0 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator (SecA.fsuL0_le_normalizer_fsuVM T L I)
      (SecA.fsuL0_le_normalizer hloc)
  have hN₂ : fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate (fsuUL T L I) t : Set G) := by
    rw [SecA.conjugate_commutator_fsuVM htM]
    exact SecA.le_normalizer_commutator (SecA.fsuL0_le_normalizer_fsuVM T L I)
      (SecA.fsuL0_le_normalizer_conjugate hloc htM)
  have hbw₁ : b * w₁ * b⁻¹ ∈ fsuUL T L I := (Subgroup.mem_normalizer_iff.mp (hN₁ hbL0) _).mp hw₁
  have hbw₂ : b * w₂ * b⁻¹ ∈ CFSG.conjugate (fsuUL T L I) t :=
    (Subgroup.mem_normalizer_iff.mp (hN₂ hbL0) _).mp hw₂
  have hkey : w₁⁻¹ * (b * w₁ * b⁻¹) = w₂ * (b * w₂ * b⁻¹)⁻¹ := by
    have e : b * w₁ * b⁻¹ * (b * w₂ * b⁻¹) = w₁ * w₂ := by
      calc b * w₁ * b⁻¹ * (b * w₂ * b⁻¹) = b * (w₁ * w₂) * b⁻¹ := by group
        _ = w₁ * w₂ := by rw [hw, hbz]
    rw [eq_mul_inv_of_mul_eq e]
    group
  have ha1 := h12 _ ((fsuUL T L I).mul_mem ((fsuUL T L I).inv_mem hw₁) hbw₁)
    (hkey ▸ (CFSG.conjugate (fsuUL T L I) t).mul_mem hw₂
      ((CFSG.conjugate (fsuUL T L I) t).inv_mem hbw₂))
  have hbf₁ : b * w₁ * b⁻¹ = w₁ := by
    rw [inv_mul_eq_one] at ha1
    exact ha1.symm
  have hbf₂ : b * w₂ * b⁻¹ = w₂ := by
    rw [hkey, mul_inv_eq_one] at ha1
    exact ha1.symm
  have hC : ∀ {x : G}, x = 1 → x ∈ fsuCVM T L I := fun h => h ▸ Subgroup.one_mem _
  have hb1 := SecA.eq_one_of_centralizes c.h37 c.h38 c.hyp
    (fun y hyL0 hyodd hyN w hwU hwC hwS hwy =>
      SecA.centralizes_of_case_one c.h37 c.h38 c.hyp c.h1 hyL0 hyodd hyN hwU hwC hwS hwy)
    ht htn hbL0 hbN c.hbo hw₁ (by rw [hC0, Subgroup.mem_bot]; exact hw₁1)
    (fun s hs => hC (by rw [hS₁ s hs, mul_inv_cancel])) (hC (by rw [hbf₁, mul_inv_cancel]))
    hw₂ (by rw [hC0, Subgroup.mem_bot]; exact hw₂1)
    (fun s hs => hC (by rw [hS₂ s hs, mul_inv_cancel])) (hC (by rw [hbf₂, mul_inv_cancel]))
  exact c.hbZ (hb1 ▸ Subgroup.one_mem _)

end Ctx

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB

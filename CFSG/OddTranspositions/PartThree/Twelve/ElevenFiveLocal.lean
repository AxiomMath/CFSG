module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveAdjoin
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelBridge

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 Matrix

variable {k : ℕ} {ε π : Bool}

@[expose] noncomputable def adjoinLinearMap (A : FiveAdjoin k ε π) :
    ((Fin (k + 1) → ZMod 5) × ZMod 5) →ₗ[ZMod 5] (Fin (k + 2) → ZMod 5) where
  toFun p := A.j p.1 + p.2 • A.a
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, smul_smul]
    rfl

theorem adjoinLinearMap_injective (A : FiveAdjoin k ε π) :
    Function.Injective (adjoinLinearMap A) := by
  intro p q h
  have h1 : A.j p.1 + p.2 • A.a = A.j q.1 + q.2 • A.a := h
  have h2 : fiveForm (k + 1) (ε == π) (A.j p.1 + p.2 • A.a) A.a =
      fiveForm (k + 1) (ε == π) (A.j q.1 + q.2 • A.a) A.a := by rw [h1]
  simp only [fiveForm_add_left, fiveForm_smul_left, A.perp p.1, A.perp q.1, zero_add] at h2
  have hQ : fiveForm (k + 1) (ε == π) A.a A.a ≠ 0 := A.sign_a.1
  have hc : p.2 = q.2 := mul_right_cancel₀ hQ h2
  have hj : A.j p.1 = A.j q.1 := by
    rw [hc] at h1
    exact add_right_cancel h1
  exact Prod.ext (A.inj hj) hc

@[expose] noncomputable def adjoinLinearEquiv (A : FiveAdjoin k ε π) :
    ((Fin (k + 1) → ZMod 5) × ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 2) → ZMod 5) :=
  LinearEquiv.ofBijective (adjoinLinearMap A)
    ⟨adjoinLinearMap_injective A,
      (Finite.injective_iff_surjective_of_equiv
        ((Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (k + 2) => ZMod 5)))).mp
        (adjoinLinearMap_injective A)⟩

@[simp]
theorem adjoinLinearEquiv_apply (A : FiveAdjoin k ε π) (v : Fin (k + 1) → ZMod 5)
    (c : ZMod 5) : adjoinLinearEquiv A (v, c) = A.j v + c • A.a :=
  rfl

@[expose] noncomputable def prodLinearEquiv {k : ℕ} (g : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5]
    (Fin (k + 1) → ZMod 5)) :
    ((Fin (k + 1) → ZMod 5) × ZMod 5) ≃ₗ[ZMod 5] ((Fin (k + 1) → ZMod 5) × ZMod 5) where
  toFun p := (g p.1, p.2)
  invFun p := (g.symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp [map_add]
  map_smul' c p := by simp [map_smul]

@[simp]
theorem prodLinearEquiv_apply (g : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5]
    (Fin (k + 1) → ZMod 5)) (v : Fin (k + 1) → ZMod 5) (c : ZMod 5) :
    prodLinearEquiv g (v, c) = (g v, c) :=
  rfl

@[simp]
theorem prodLinearEquiv_one :
    prodLinearEquiv (1 : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5]
      (Fin (k + 1) → ZMod 5)) = 1 := by
  apply LinearEquiv.ext
  rintro ⟨v, c⟩
  simp

theorem prodLinearEquiv_mul (f g : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5]
    (Fin (k + 1) → ZMod 5)) :
    prodLinearEquiv (f * g) = prodLinearEquiv f * prodLinearEquiv g := by
  apply LinearEquiv.ext
  rintro ⟨v, c⟩
  simp [LinearEquiv.mul_apply]

@[expose] noncomputable def adjoinIotaLinearEquiv (A : FiveAdjoin k ε π) :
    ((Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5)) →*
      ((Fin (k + 2) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 2) → ZMod 5)) where
  toFun g := (adjoinLinearEquiv A).symm.trans
    ((prodLinearEquiv g).trans (adjoinLinearEquiv A))
  map_one' := by
    rw [prodLinearEquiv_one]
    apply LinearEquiv.ext
    intro x
    simp [LinearEquiv.trans_apply]
  map_mul' f g := by
    rw [prodLinearEquiv_mul]
    apply LinearEquiv.ext
    intro x
    simp [LinearEquiv.trans_apply, LinearEquiv.mul_eq_trans]

@[simp]
theorem adjoinIotaLinearEquiv_apply_adjoin (A : FiveAdjoin k ε π)
    (g : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5))
    (v : Fin (k + 1) → ZMod 5) (c : ZMod 5) :
    adjoinIotaLinearEquiv A g (adjoinLinearEquiv A (v, c)) = adjoinLinearEquiv A (g v, c) := by
  show (adjoinLinearEquiv A).symm.trans ((prodLinearEquiv g).trans (adjoinLinearEquiv A))
      (adjoinLinearEquiv A (v, c)) = adjoinLinearEquiv A (g v, c)
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    prodLinearEquiv_apply]

noncomputable def adjoinIota (A : FiveAdjoin k ε π) :
    GL (Fin (k + 1)) (ZMod 5) →* GL (Fin (k + 2)) (ZMod 5) :=
  (fiveGLIso (k + 1)).symm.toMonoidHom.comp
    ((adjoinIotaLinearEquiv A).comp (fiveGLIso k).toMonoidHom)

theorem fiveGLIso_adjoinIota (A : FiveAdjoin k ε π) (g : GL (Fin (k + 1)) (ZMod 5)) :
    fiveGLIso (k + 1) (adjoinIota A g) = adjoinIotaLinearEquiv A (fiveGLIso k g) := by
  simp [adjoinIota]

theorem fiveReflO_apply (n : ℕ) (ε : Bool) (v x : Fin (n + 1) → ZMod 5) :
    fiveReflO n ε v x = x - (2 * fiveForm n ε x v * (fiveForm n ε v v)⁻¹) • v := by
  rw [← fiveGLIso_fiveReflOf, fiveGLIso_apply, fiveReflOf_mulVec]

theorem adjoinLinearEquiv_fiveReflO (A : FiveAdjoin k ε π)
    (y v : Fin (k + 1) → ZMod 5) (c : ZMod 5) :
    adjoinLinearEquiv A (fiveReflO k ε y v, c) =
      fiveReflO (k + 1) (ε == π) (A.j y) (adjoinLinearEquiv A (v, c)) := by
  rw [adjoinLinearEquiv_apply, adjoinLinearEquiv_apply, fiveReflO_apply, fiveReflO_apply]
  rw [map_sub, map_smul, fiveForm_add_left, fiveForm_smul_left, A.isom v y,
    fiveForm_comm (k + 1) (ε == π) A.a (A.j y), A.perp y, mul_zero, add_zero, A.isom y y]
  module

theorem adjoinIota_fiveReflOf (A : FiveAdjoin k ε π) (y : Fin (k + 1) → ZMod 5) :
    adjoinIota A (fiveReflOf k ε y) = fiveReflOf (k + 1) (ε == π) (A.j y) := by
  apply (fiveGLIso (k + 1)).injective
  rw [fiveGLIso_adjoinIota, fiveGLIso_fiveReflOf, fiveGLIso_fiveReflOf]
  apply LinearEquiv.ext
  intro x
  obtain ⟨v, c, hvc⟩ : ∃ v c, adjoinLinearEquiv A (v, c) = x :=
    ⟨((adjoinLinearEquiv A).symm x).1, ((adjoinLinearEquiv A).symm x).2,
      (adjoinLinearEquiv A).apply_symm_apply x⟩
  rw [← hvc, adjoinIotaLinearEquiv_apply_adjoin, adjoinLinearEquiv_fiveReflO]

theorem adjoinIota_injective (A : FiveAdjoin k ε π) :
    Function.Injective (adjoinIota A) := by
  intro g h hgh
  have h' : adjoinIotaLinearEquiv A (fiveGLIso k g) =
      adjoinIotaLinearEquiv A (fiveGLIso k h) := by
    simpa [fiveGLIso_adjoinIota] using congrArg (fiveGLIso (k + 1)) hgh
  have h'' : fiveGLIso k g = fiveGLIso k h := by
    apply LinearEquiv.ext
    intro v
    have hv := congrArg (fun e => e (adjoinLinearEquiv A (v, 0))) h'
    simp only [adjoinIotaLinearEquiv_apply_adjoin] at hv
    exact congrArg Prod.fst ((adjoinLinearEquiv A).injective hv)
  exact (fiveGLIso k).injective h''

theorem adjoinIota_apply_a (A : FiveAdjoin k ε π) (g : GL (Fin (k + 1)) (ZMod 5)) :
    (fiveGLIso (k + 1) (adjoinIota A g)) A.a = A.a := by
  have h : (adjoinLinearEquiv A).symm A.a = (0, 1) := by
    apply (adjoinLinearEquiv A).injective
    rw [LinearEquiv.apply_symm_apply, adjoinLinearEquiv_apply]
    simp
  rw [fiveGLIso_adjoinIota]
  simp [adjoinIotaLinearEquiv, LinearEquiv.trans_apply, prodLinearEquiv, adjoinLinearEquiv_apply, h]

theorem adjoinIota_apply_adjoin (A : FiveAdjoin k ε π) (g : GL (Fin (k + 1)) (ZMod 5))
    (v : Fin (k + 1) → ZMod 5) (c : ZMod 5) :
    (adjoinIota A g : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ
        (A.j v + c • A.a) =
      A.j (((g : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v) + c • A.a := by
  rw [← fiveGLIso_apply (k + 1) (adjoinIota A g) (A.j v + c • A.a), fiveGLIso_adjoinIota]
  rw [show A.j v + c • A.a = adjoinLinearEquiv A (v, c) from
    (adjoinLinearEquiv_apply A v c).symm]
  rw [adjoinIotaLinearEquiv_apply_adjoin, adjoinLinearEquiv_apply, fiveGLIso_apply]

theorem adjoinIota_mem_fiveReflectionGroup (A : FiveAdjoin k ε π)
    {g : GL (Fin (k + 1)) (ZMod 5)} (hg : g ∈ fiveReflectionGroup k ε π) :
    adjoinIota A g ∈ fiveReflectionGroup (k + 1) (ε == π) π := by
  refine Subgroup.closure_induction (k := fiveReflections k ε π)
    (p := fun g _ => adjoinIota A g ∈ fiveReflectionGroup (k + 1) (ε == π) π)
    ?_ ?_ ?_ ?_ hg
  · intro z hz
    obtain ⟨x, hx, hxπ, rfl⟩ := exists_eq_fiveReflOf hz
    rw [adjoinIota_fiveReflOf]
    exact Subgroup.subset_closure
      (fiveReflOf_mem (by rwa [A.isom x x]) (by rw [A.isom x x]; exact hxπ))
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro z w hz hw ihz ihw
    rw [map_mul]
    exact mul_mem ihz ihw
  · intro z hz ihz
    rw [map_inv]
    exact inv_mem ihz

noncomputable def adjoinIotaSub (A : FiveAdjoin k ε π) :
    fiveReflectionGroup k ε π →* fiveReflectionGroup (k + 1) (ε == π) π :=
  ((adjoinIota A).comp (fiveReflectionGroup k ε π).subtype).codRestrict
    (fiveReflectionGroup (k + 1) (ε == π) π)
    fun g => adjoinIota_mem_fiveReflectionGroup A g.2

@[simp]
theorem coe_adjoinIotaSub (A : FiveAdjoin k ε π) (g : fiveReflectionGroup k ε π) :
    (adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5)) = adjoinIota A g := by
  rfl

noncomputable def adjoinRa (A : FiveAdjoin k ε π) :
    fiveReflectionGroup (k + 1) (ε == π) π :=
  ⟨fiveReflOf (k + 1) (ε == π) A.a,
    Subgroup.subset_closure (fiveReflOf_mem A.sign_a.1 A.sign_a.2)⟩

@[simp]
theorem coe_adjoinRa (A : FiveAdjoin k ε π) :
    (adjoinRa A : GL (Fin (k + 2)) (ZMod 5)) = fiveReflOf (k + 1) (ε == π) A.a := by
  rfl

@[expose] noncomputable def adjoinPhi (A : FiveAdjoin k ε π) :
    fiveReflectionGroup k ε π →* fiveProjective (k + 1) (ε == π) π :=
  (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup (k + 1) (ε == π) π))).comp
    (adjoinIotaSub A)

@[simp]
theorem adjoinPhi_apply (A : FiveAdjoin k ε π) (g : fiveReflectionGroup k ε π) :
    adjoinPhi A g = QuotientGroup.mk (adjoinIotaSub A g) := by
  simp [adjoinPhi]

private theorem fiveAdjoin_a_ne_zero (A : FiveAdjoin k ε π) : A.a ≠ 0 := by
  intro h
  apply A.sign_a.1
  rw [h]
  simp [fiveForm]

private theorem fiveAdjoin_a_ne_neg (A : FiveAdjoin k ε π) (h : A.a = -A.a) : False := by
  have h2 : (2 : ZMod 5) • A.a = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    rw [add_neg_cancel]
  have hzero : A.a = 0 := by
    calc A.a = (2 : ZMod 5)⁻¹ • ((2 : ZMod 5) • A.a) := by
          rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), one_smul]
      _ = 0 := by rw [h2, smul_zero]
  exact fiveAdjoin_a_ne_zero A hzero

private theorem coe_adjoinIotaSub_eq_fiveReflOf (A : FiveAdjoin k ε π)
    {g : fiveReflectionGroup k ε π} {y : Fin (k + 1) → ZMod 5}
    (hgy : (g : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε y) :
    (adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5)) =
      fiveReflOf (k + 1) (ε == π) (A.j y) := by
  rw [coe_adjoinIotaSub]
  rw [hgy, adjoinIota_fiveReflOf]

private theorem adjoinIotaSub_mem_fiveReflections (A : FiveAdjoin k ε π)
    {g : fiveReflectionGroup k ε π}
    (hg : (g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π) :
    (adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5)) ∈
      fiveReflections (k + 1) (ε == π) π := by
  obtain ⟨y, hy, hyπ, hgy⟩ := exists_eq_fiveReflOf hg
  rw [coe_adjoinIotaSub_eq_fiveReflOf A hgy]
  exact fiveReflOf_mem (by rw [A.isom]; exact hy) (by rw [A.isom]; exact hyπ)

private theorem adjoinPhi_mem_fiveProjClass (A : FiveAdjoin k ε π)
    {g : fiveReflectionGroup k ε π}
    (hg : (g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π) :
    adjoinPhi A g ∈ fiveProjClass (k + 1) (ε == π) π := by
  refine ⟨adjoinIotaSub A g, adjoinIotaSub_mem_fiveReflections A hg, ?_⟩
  rw [adjoinPhi_apply]

private theorem adjoinPhi_commute_adjoinRa (A : FiveAdjoin k ε π) (hk : 4 ≤ k)
    {g : fiveReflectionGroup k ε π}
    (hg : (g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π) :
    Commute (adjoinPhi A g) (QuotientGroup.mk (adjoinRa A) :
      fiveProjective (k + 1) (ε == π) π) := by
  have hn : 4 ≤ k + 1 := by omega
  have hra : (adjoinRa A : GL (Fin (k + 2)) (ZMod 5)) ∈
      fiveReflections (k + 1) (ε == π) π := by
    rw [coe_adjoinRa]; exact fiveReflOf_mem A.sign_a.1 A.sign_a.2
  obtain ⟨y, hy, hyπ, hgy⟩ := exists_eq_fiveReflOf hg
  have hcomm_gl : Commute ((adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5)))
      ((adjoinRa A : GL (Fin (k + 2)) (ZMod 5))) := by
    rw [coe_adjoinIotaSub_eq_fiveReflOf A hgy, coe_adjoinRa]
    exact fiveReflOf_commute_of_orthogonal (by rw [A.isom]; exact hy)
      (by rw [A.isom]; exact hyπ) (A.perp y)
  have hcomm_sub : Commute (adjoinIotaSub A g) (adjoinRa A) := by
    rw [commute_iff_eq] at hcomm_gl ⊢
    exact Subtype.ext hcomm_gl
  rw [adjoinPhi_apply]
  exact (commute_mk_iff_commute hn (ε := ε == π) (π := π)
    hra).mpr hcomm_sub

private theorem adjoinPhi_ne_adjoinRa (A : FiveAdjoin k ε π) (hk : 4 ≤ k)
    {g : fiveReflectionGroup k ε π}
    (hg : (g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π) :
    adjoinPhi A g ≠ (QuotientGroup.mk (adjoinRa A) : fiveProjective (k + 1) (ε == π) π) := by
  intro hEq
  have hn : 4 ≤ k + 1 := by omega
  have hra : (adjoinRa A : GL (Fin (k + 2)) (ZMod 5)) ∈
      fiveReflections (k + 1) (ε == π) π := by
    rw [coe_adjoinRa]; exact fiveReflOf_mem A.sign_a.1 A.sign_a.2
  have hcen : (adjoinIotaSub A g)⁻¹ * (adjoinRa A) ∈
      Subgroup.center (fiveReflectionGroup (k + 1) (ε == π) π) := by
    rw [adjoinPhi_apply] at hEq
    exact QuotientGroup.eq.mp hEq
  rcases (mem_center_fiveReflectionGroup_iff hn (ε == π) π _).mp hcen with h1 | h1
  · have hc1 : (adjoinIotaSub A g)⁻¹ * (adjoinRa A) = 1 := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] using h1
    have hab : adjoinIotaSub A g = adjoinRa A := inv_mul_eq_one.mp hc1
    have happ := congrArg (fun h : GL (Fin (k + 2)) (ZMod 5) =>
      (h : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ A.a) (congrArg Subtype.val hab)
    simp only [coe_adjoinIotaSub, coe_adjoinRa] at happ
    have hL : (adjoinIota A g : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ A.a =
        A.a := by
      rw [← fiveGLIso_apply]
      exact adjoinIota_apply_a A g
    have hR : (fiveReflOf (k + 1) (ε == π) A.a :
        Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ A.a = -A.a :=
      fiveReflOf_mulVec_self A.sign_a.1
    rw [hL, hR] at happ
    exact fiveAdjoin_a_ne_neg A happ
  · have hcgl : (adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5))⁻¹ *
        (adjoinRa A : GL (Fin (k + 2)) (ZMod 5)) = -1 := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
    have hb : (adjoinRa A : GL (Fin (k + 2)) (ZMod 5)) =
        -(adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5)) := by
      calc (adjoinRa A : GL (Fin (k + 2)) (ZMod 5))
          = (adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5)) *
              ((adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5))⁻¹ *
                (adjoinRa A : GL (Fin (k + 2)) (ZMod 5))) := by group
        _ = (adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5)) * (-1) := by rw [hcgl]
        _ = -(adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5)) := by rw [mul_neg, mul_one]
    have hneg : (adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5)) =
        -(adjoinRa A : GL (Fin (k + 2)) (ZMod 5)) := by
      rw [hb, neg_neg]
    have hmem := adjoinIotaSub_mem_fiveReflections A hg
    rw [hneg] at hmem
    exact (neg_notMem_fiveReflections (n := k + 1) (by omega : 2 ≤ k + 1) (ε == π) π hra) hmem

theorem commSet_fiveProjClass_eq_image (A : FiveAdjoin k ε π) (hk : 4 ≤ k) :
    commSet (fiveProjClass (k + 1) (ε == π) π) (QuotientGroup.mk (adjoinRa A)) =
      adjoinPhi A '' {g : fiveReflectionGroup k ε π |
        (g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π} := by
  have hn : 4 ≤ k + 1 := by omega
  have hra : (adjoinRa A : GL (Fin (k + 2)) (ZMod 5)) ∈
      fiveReflections (k + 1) (ε == π) π := by
    rw [coe_adjoinRa]; exact fiveReflOf_mem A.sign_a.1 A.sign_a.2
  ext x
  constructor
  · intro hx
    simp only [commSet, Set.mem_setOf_eq] at hx
    obtain ⟨hxclass, hxcomm, hxne⟩ := hx
    obtain ⟨r, hr, hrmk⟩ := hxclass
    have hxcomm' : Commute (QuotientGroup.mk r) (QuotientGroup.mk (adjoinRa A) :
        fiveProjective (k + 1) (ε == π) π) := by
      rw [hrmk]; exact hxcomm
    have hcomm_sub : Commute r (adjoinRa A) :=
      (commute_mk_iff_commute hn (ε := ε == π) (π := π) hra).mp hxcomm'
    obtain ⟨b, hbQ, hbπ, hrb⟩ := exists_eq_fiveReflOf hr
    have hcomm_gl : Commute (fiveReflOf (k + 1) (ε == π) b)
        (fiveReflOf (k + 1) (ε == π) A.a) := by
      rw [commute_iff_eq]
      have h := congrArg Subtype.val hcomm_sub.eq
      simpa only [Subgroup.coe_mul, hrb, coe_adjoinRa] using h
    rcases (commute_fiveReflOf_iff (k + 1) (ε == π) hbQ A.sign_a.1).mp hcomm_gl with
      horth | ⟨μ, hμ⟩
    · obtain ⟨⟨v, c⟩, hvc⟩ := (adjoinLinearEquiv A).surjective b
      have hb_decomp : b = A.j v + c • A.a := by
        rw [← hvc, adjoinLinearEquiv_apply]
      have hc : c = 0 := by
        have h := horth
        rw [hb_decomp, fiveForm_add_left, fiveForm_smul_left, A.perp v, zero_add] at h
        exact (mul_eq_zero.mp h).resolve_right A.sign_a.1
      have hb_j : b = A.j v := by rw [hb_decomp, hc, zero_smul, add_zero]
      have hv : fiveForm k ε v v ≠ 0 := by rw [← A.isom v v, ← hb_j]; exact hbQ
      have hvπ : IsSquare (fiveForm k ε v v) ↔ π = true := by
        rw [← A.isom v v, ← hb_j]; exact hbπ
      let g : fiveReflectionGroup k ε π :=
        ⟨fiveReflOf k ε v, Subgroup.subset_closure (fiveReflOf_mem hv hvπ)⟩
      refine ⟨g, ?_, ?_⟩
      · show (g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π
        exact fiveReflOf_mem hv hvπ
      · rw [adjoinPhi_apply]
        have hga : (adjoinIotaSub A g : GL (Fin (k + 2)) (ZMod 5)) =
            fiveReflOf (k + 1) (ε == π) (A.j v) :=
          coe_adjoinIotaSub_eq_fiveReflOf A (g := g) (y := v) rfl
        have hg_eq : adjoinIotaSub A g = r := by
          apply Subtype.ext
          rw [hga, hrb, hb_j]
        rw [hg_eq]
        exact hrmk
    · exfalso
      have hμ0 : μ ≠ 0 := by
        intro h0
        exact fiveAdjoin_a_ne_zero A (by rw [hμ, h0, zero_smul])
      have hb_eq : b = μ⁻¹ • A.a := by
        rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      have hr_eq : r = adjoinRa A := by
        apply Subtype.ext
        rw [hrb, coe_adjoinRa, hb_eq,
          fiveReflOf_smul (k + 1) (ε == π) A.a (inv_ne_zero hμ0)]
      exact hxne (hrmk.symm.trans (congrArg QuotientGroup.mk hr_eq))
  · rintro ⟨g, hg, rfl⟩
    simp only [commSet, Set.mem_setOf_eq]
    exact ⟨adjoinPhi_mem_fiveProjClass A hg, adjoinPhi_commute_adjoinRa A hk hg,
      adjoinPhi_ne_adjoinRa A hk hg⟩

theorem adjoinIotaSub_mk_injective (A : FiveAdjoin k ε π) (hk : 4 ≤ k) :
    Function.Injective (fun g : fiveReflectionGroup k ε π =>
      (QuotientGroup.mk (adjoinIotaSub A g) : fiveProjective (k + 1) (ε == π) π)) := by
  intro g h hgh
  have hn : 4 ≤ k + 1 := by omega
  have hcen : adjoinIotaSub A (g⁻¹ * h) ∈
      Subgroup.center (fiveReflectionGroup (k + 1) (ε == π) π) := by
    rw [map_mul, map_inv]
    exact QuotientGroup.eq.mp hgh
  rcases (mem_center_fiveReflectionGroup_iff hn (ε == π) π _).mp hcen with h1 | h1
  · have hgl : (adjoinIota A) ((↑g : GL (Fin (k + 1)) (ZMod 5))⁻¹ * ↑h) = 1 := by
      simpa only [coe_adjoinIotaSub, Subgroup.coe_mul, Subgroup.coe_inv] using h1
    exact Subtype.ext (inv_mul_eq_one.mp (adjoinIota_injective A (by rw [hgl, map_one])))
  · exfalso
    have hgl : (adjoinIota A) ((↑g : GL (Fin (k + 1)) (ZMod 5))⁻¹ * ↑h) = -1 := by
      simpa only [coe_adjoinIotaSub, Subgroup.coe_mul, Subgroup.coe_inv] using h1
    have hgl' : (adjoinIota A) (↑(g⁻¹ : fiveReflectionGroup k ε π) * ↑h) = -1 := by
      simpa only [← Subgroup.coe_inv] using hgl
    have happ := adjoinIota_apply_a A (g⁻¹ * h)
    rw [hgl'] at happ
    have hnegapp : fiveGLIso (k + 1) (-1 : GL (Fin (k + 2)) (ZMod 5)) A.a = -A.a := by
      rw [fiveGLIso_apply]
      simp only [Units.val_neg, Matrix.GeneralLinearGroup.coe_one, Matrix.neg_mulVec,
        Matrix.one_mulVec]
    rw [hnegapp] at happ
    exact fiveAdjoin_a_ne_neg A happ.symm

theorem adjoinPhi_injective (A : FiveAdjoin k ε π) (hk : 4 ≤ k) :
    Function.Injective (adjoinPhi A) := by
  intro g h hgh
  have := adjoinIotaSub_mk_injective A hk hgh
  exact this

theorem adjoinPhi_range (A : FiveAdjoin k ε π) (hk : 4 ≤ k) :
    (adjoinPhi A).range = Subgroup.closure (commSet (fiveProjClass (k + 1) (ε == π) π)
      (QuotientGroup.mk (adjoinRa A))) := by
  have hs : Subgroup.closure
      ((fiveReflectionGroup k ε π).subtype ⁻¹' fiveReflections k ε π) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have h := MonoidHom.map_closure (adjoinPhi A)
    ((fiveReflectionGroup k ε π).subtype ⁻¹' fiveReflections k ε π)
  rw [hs] at h
  rw [MonoidHom.range_eq_map, h, commSet_fiveProjClass_eq_image A hk]
  rfl

@[expose] noncomputable def adjoinPhiEquiv (A : FiveAdjoin k ε π) (hk : 4 ≤ k) :
    fiveReflectionGroup k ε π ≃* Subgroup.closure (commSet (fiveProjClass (k + 1) (ε == π) π)
      (QuotientGroup.mk (adjoinRa A))) :=
  (MonoidHom.ofInjective (adjoinPhi_injective A hk)).trans
    (MulEquiv.subgroupCongr (adjoinPhi_range A hk))

@[simp]
theorem coe_adjoinPhiEquiv (A : FiveAdjoin k ε π) (hk : 4 ≤ k) (g : fiveReflectionGroup k ε π) :
    (adjoinPhiEquiv A hk g : fiveProjective (k + 1) (ε == π) π) = adjoinPhi A g :=
  rfl

@[expose] noncomputable def adjoinLocalModel (A : FiveAdjoin k ε π) (hk : 4 ≤ k) :
    FiveLocalModel (fiveProjClass (k + 1) (ε == π) π)
      (QuotientGroup.mk (adjoinRa A) : fiveProjective (k + 1) (ε == π) π) k ε π where
  toMulEquiv := (adjoinPhiEquiv A hk).symm
  mem_iff y := by
    obtain ⟨g, rfl⟩ := (adjoinPhiEquiv A hk).surjective y
    rw [MulEquiv.symm_apply_apply, coe_adjoinPhiEquiv, commSet_fiveProjClass_eq_image A hk]
    exact (adjoinPhi_injective A hk).mem_set_image

@[simp]
theorem adjoinLocalModel_toMulEquiv (A : FiveAdjoin k ε π) (hk : 4 ≤ k) :
    (adjoinLocalModel A hk).toMulEquiv = (adjoinPhiEquiv A hk).symm :=
  rfl

theorem adjoinLocalModel_eq_iff (A : FiveAdjoin k ε π) (hk : 4 ≤ k)
    (y : Subgroup.closure (commSet (fiveProjClass (k + 1) (ε == π) π)
      (QuotientGroup.mk (adjoinRa A))))
    (g : fiveReflectionGroup k ε π) :
    (adjoinLocalModel A hk).toMulEquiv y = g ↔
      (y : fiveProjective (k + 1) (ε == π) π) = adjoinPhi A g := by
  rw [adjoinLocalModel_toMulEquiv, MulEquiv.symm_apply_eq, Subtype.ext_iff, coe_adjoinPhiEquiv]

end CFSG.OddTranspositions.PartThree

end

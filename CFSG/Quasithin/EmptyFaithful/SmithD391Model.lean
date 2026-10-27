module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Rank
public import CFSG.Quasithin.Background.FFC4Zmod

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391 CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {X : Type*} [CommGroup X] {n : ℕ}

theorem center_statedSL_two_eq_bot (hn : 0 < n) :
    Subgroup.center ↥(StatedSL n (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  set e := specialLinearGroupEquivStatedSL n (ZMod 2) with he
  obtain ⟨A, rfl⟩ := e.surjective g
  have hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff] at hg ⊢
    intro B
    apply e.injective
    rw [map_mul, map_mul]
    exact hg (e B)
  obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr1 : r = 1 := by
    rw [Fintype.card_fin] at hr
    have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases key r with rfl | rfl
    · exfalso
      rw [zero_pow hn.ne'] at hr
      exact zero_ne_one hr
    · rfl
  have hA1 : A = 1 := by
    apply Subtype.ext
    rw [← hAr, hr1, map_one]
    rfl
  rw [hA1, map_one]
  exact Subgroup.one_mem _

section Equiv

variable {H : Subgroup (MulAut X)} {U : Subgroup X} {π : ↥(StatedSL n (ZMod 2)) →* ↥H}

theorem exists_natEquiv (hR : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U ⊥ π) :
    ∃ e : ↥U ≃* Multiplicative (Fin n → ZMod 2), ∀ (g : ↥(StatedSL n (ZMod 2))) (u : ↥U)
      (hu : ((π g : ↥H) : MulAut X) (u : X) ∈ U),
      e ⟨_, hu⟩ = natAct (StatedSL n (ZMod 2)) g (e u) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.RealizesVia.secMap rfl hR
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hfk u).1 hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  let e : ↥U ≃* Multiplicative (Fin n → ZMod 2) :=
    (MulEquiv.ofBijective f ⟨hinj, hfs⟩).trans
      (Subgroup.topEquiv (G := Multiplicative (Fin n → ZMod 2)))
  exact ⟨e, fun g u hu => hfe g u hu⟩

theorem exists_dualEquiv (hR : (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia H U ⊥ π) :
    ∃ e : ↥U ≃* Multiplicative (Fin n → ZMod 2), ∀ (g : ↥(StatedSL n (ZMod 2))) (u : ↥U)
      (hu : ((π g : ↥H) : MulAut X) (u : X) ∈ U),
      e ⟨_, hu⟩ = dualNatAct (StatedSL n (ZMod 2)) g (e u) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.RealizesVia.secMap rfl hR
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hfk u).1 hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  let e : ↥U ≃* Multiplicative (Fin n → ZMod 2) :=
    (MulEquiv.ofBijective f ⟨hinj, hfs⟩).trans
      (Subgroup.topEquiv (G := Multiplicative (Fin n → ZMod 2)))
  exact ⟨e, fun g u hu => hfe g u hu⟩

theorem rk_eq_of_equiv (e : ↥U ≃* Multiplicative (Fin n → ZMod 2)) : rk ↥U = n := by
  unfold rk
  rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, Nat.card_eq_fintype_card (α := ZMod 2),
    ZMod.card, padicValNat.prime_pow]

end Equiv

@[expose] noncomputable def autLin
    (ψ : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun v := Multiplicative.toAdd (ψ (Multiplicative.ofAdd v))
  map_add' v w := by rw [ofAdd_add, map_mul, toAdd_mul]
  map_smul' c v := by
    have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases key c with rfl | rfl
    · simp
    · simp

@[expose] noncomputable def autMatrix
    (ψ : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  LinearMap.toMatrix' (autLin ψ)

theorem autMatrix_mulVec (ψ : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) :
    (autMatrix ψ) *ᵥ v = Multiplicative.toAdd (ψ (Multiplicative.ofAdd v)) := by
  unfold autMatrix
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem autMatrix_mul_symm
    (ψ : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2)) :
    autMatrix ψ * autMatrix ψ.symm = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
    autMatrix_mulVec, autMatrix_mulVec, Matrix.toLin'_one, LinearMap.id_apply]
  simp

theorem det_autMatrix (ψ : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2)) :
    (autMatrix ψ).det = 1 := by
  have h := congrArg Matrix.det (autMatrix_mul_symm ψ)
  rw [Matrix.det_mul, Matrix.det_one] at h
  have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide
  exact key _ _ h

@[expose] noncomputable def autSL
    (ψ : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2)) :
    ↥(StatedSL n (ZMod 2)) :=
  ⟨⟨autMatrix ψ, autMatrix ψ.symm, autMatrix_mul_symm ψ, by
      simpa using autMatrix_mul_symm ψ.symm⟩,
    Subgroup.subset_closure (show (autMatrix ψ).det = 1 from det_autMatrix ψ)⟩

theorem natAct_autSL (ψ : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2))
    (x : Multiplicative (Fin n → ZMod 2)) : natAct (StatedSL n (ZMod 2)) (autSL ψ) x = ψ x := by
  show Multiplicative.ofAdd ((autMatrix ψ) *ᵥ Multiplicative.toAdd x) = ψ x
  rw [autMatrix_mulVec]
  rfl

@[expose] noncomputable def autSLDual
    (ψ : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2)) :
    ↥(StatedSL n (ZMod 2)) :=
  ⟨⟨(autMatrix ψ.symm)ᵀ, (autMatrix ψ)ᵀ, by
      rw [← Matrix.transpose_mul, show autMatrix ψ * autMatrix ψ.symm = 1 from
        autMatrix_mul_symm ψ, Matrix.transpose_one], by
      rw [← Matrix.transpose_mul]
      have := autMatrix_mul_symm ψ.symm
      rw [MulEquiv.symm_symm] at this
      rw [this, Matrix.transpose_one]⟩,
    Subgroup.subset_closure (show ((autMatrix ψ.symm)ᵀ).det = 1 by
      rw [Matrix.det_transpose]; exact det_autMatrix ψ.symm)⟩

theorem dualNatAct_autSLDual
    (ψ : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2))
    (x : Multiplicative (Fin n → ZMod 2)) :
    dualNatAct (StatedSL n (ZMod 2)) (autSLDual ψ) x = ψ x := by
  show Multiplicative.ofAdd (((autMatrix ψ)ᵀ)ᵀ *ᵥ Multiplicative.toAdd x) = ψ x
  rw [Matrix.transpose_transpose, autMatrix_mulVec]
  rfl

section Aut

variable {H : Subgroup (MulAut X)} {U : Subgroup X} {π : ↥(StatedSL n (ZMod 2)) →* ↥H}

theorem exists_eq_of_mulAut_nat
    (hR : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U ⊥ π) (ψ : ↥U ≃* ↥U) :
    ∃ g : ↥(StatedSL n (ZMod 2)), ∀ u : ↥U, ((π g : ↥H) : MulAut X) (u : X) = ((ψ u : ↥U) : X) := by
  obtain ⟨e, he⟩ := exists_natEquiv hR
  refine ⟨autSL (e.symm.trans (ψ.trans e)), fun u => ?_⟩
  have hu : ((π (autSL (e.symm.trans (ψ.trans e))) : ↥H) : MulAut X) (u : X) ∈ U :=
    hR.2.2.2.1 _ u u.2
  have h1 := he _ u hu
  rw [natAct_autSL] at h1
  have h2 : e ⟨_, hu⟩ = e (ψ u) := by
    rw [h1]
    simp
  exact congrArg Subtype.val (e.injective h2)

theorem exists_eq_of_mulAut_dual
    (hR : (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia H U ⊥ π) (ψ : ↥U ≃* ↥U) :
    ∃ g : ↥(StatedSL n (ZMod 2)), ∀ u : ↥U, ((π g : ↥H) : MulAut X) (u : X) = ((ψ u : ↥U) : X) := by
  obtain ⟨e, he⟩ := exists_dualEquiv hR
  refine ⟨autSLDual (e.symm.trans (ψ.trans e)), fun u => ?_⟩
  have hu : ((π (autSLDual (e.symm.trans (ψ.trans e))) : ↥H) : MulAut X) (u : X) ∈ U :=
    hR.2.2.2.1 _ u u.2
  have h1 := he _ u hu
  rw [dualNatAct_autSLDual] at h1
  have h2 : e ⟨_, hu⟩ = e (ψ u) := by
    rw [h1]
    simp
  exact congrArg Subtype.val (e.injective h2)

end Aut

theorem dot_toAdd_inv (v : Fin n → ZMod 2) (x : Multiplicative (Fin n → ZMod 2)) :
    v ⬝ᵥ Multiplicative.toAdd x⁻¹ = -(v ⬝ᵥ Multiplicative.toAdd x) := by
  simp only [toAdd_inv]
  exact dotProduct_neg v _

theorem dot_toAdd_mul_inv (x y : Multiplicative (Fin n → ZMod 2)) (c : Fin n → ZMod 2) :
    Multiplicative.toAdd (x * y⁻¹) ⬝ᵥ c =
      Multiplicative.toAdd x ⬝ᵥ c - Multiplicative.toAdd y ⬝ᵥ c := by
  rw [toAdd_mul, add_dotProduct]
  simp only [toAdd_inv]
  rw [sub_eq_add_neg]
  congr 1
  exact neg_dotProduct _ _

@[expose] def annSub (U : Subgroup X) (e : ↥U ≃* Multiplicative (Fin n → ZMod 2))
    (w : Fin n → ZMod 2) : Subgroup X where
  carrier := {u | ∃ hu : u ∈ U, w ⬝ᵥ Multiplicative.toAdd (e ⟨u, hu⟩) = 0}
  one_mem' := ⟨U.one_mem, by
    show w ⬝ᵥ Multiplicative.toAdd (e 1) = 0
    rw [map_one, toAdd_one, dotProduct_zero]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha0⟩ ⟨hb, hb0⟩
    refine ⟨U.mul_mem ha hb, ?_⟩
    show w ⬝ᵥ Multiplicative.toAdd (e (⟨a, ha⟩ * ⟨b, hb⟩)) = 0
    rw [map_mul, toAdd_mul, dotProduct_add, ha0, hb0, add_zero]
  inv_mem' := by
    rintro a ⟨ha, ha0⟩
    refine ⟨U.inv_mem ha, ?_⟩
    show w ⬝ᵥ Multiplicative.toAdd (e (⟨a, ha⟩)⁻¹) = 0
    rw [map_inv, dot_toAdd_inv, ha0]
    exact neg_zero

section Dual

variable [Finite X] {H : Subgroup (MulAut X)} {U₁ U₂ : Subgroup X}
  {π : ↥(StatedSL n (ZMod 2)) →* ↥H}

theorem rk_fixV_dual_add_rk_commSub_le (hX : ∀ x : X, x ^ 2 = 1)
    (hR₁ : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U₁ ⊥ π)
    (hR₂ : (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia H U₂ ⊥ π)
    {F : Subgroup (MulAut X)} (hFH : F ≤ H) :
    rk ↥(U₂ ⊓ fixV F) + rk ↥(commSub U₁ F) ≤ n := by
  classical
  obtain ⟨e₁, he₁⟩ := exists_natEquiv hR₁
  obtain ⟨e₂, he₂⟩ := exists_dualEquiv hR₂
  have hrk₁ : rk ↥U₁ = n := rk_eq_of_equiv e₁
  set D := commSub U₁ F with hD
  have hDU : D ≤ U₁ := by
    rw [hD, commSub, Subgroup.closure_le]
    rintro _ ⟨f, hf, u, hu, rfl⟩
    exact U₁.mul_mem (hR₁.2.2.2.1 ⟨f, hFH hf⟩ u hu) (U₁.inv_mem hu)
  set γ := rk ↥U₁ - rk ↥D with hγ
  have hrkD : rk ↥U₁ = rk ↥D + γ := by
    have := rk_mono hDU
    omega
  obtain ⟨x, hxU, hgen⟩ := exists_gen_mod hX γ D hDU hrkD
  have hfixdual : ∀ z : ↥U₂, (z : X) ∈ fixV F → ∀ f ∈ F, ∀ g : ↥(StatedSL n (ZMod 2)),
      ((π g : ↥H) : MulAut X) = f →
        ((((g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ) *ᵥ
          Multiplicative.toAdd (e₂ z) = Multiplicative.toAdd (e₂ z) := by
    intro z hz f hf g hg
    have hfi : f⁻¹ ∈ F := F.inv_mem hf
    have hgi : ((π g⁻¹ : ↥H) : MulAut X) = f⁻¹ := by rw [map_inv, ← hg]; rfl
    have hz' : ((π g⁻¹ : ↥H) : MulAut X) (z : X) = z := by
      rw [hgi]
      exact (mem_fixV.1 hz) _ hfi
    have hu : ((π g⁻¹ : ↥H) : MulAut X) (z : X) ∈ U₂ := hR₂.2.2.2.1 _ z z.2
    have h1 := he₂ g⁻¹ z hu
    have h2 : (⟨_, hu⟩ : ↥U₂) = z := Subtype.ext hz'
    rw [h2] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    rw [show dualNatAct (StatedSL n (ZMod 2)) g⁻¹ (e₂ z) =
      Multiplicative.ofAdd (((((g⁻¹)⁻¹ : ↥(StatedSL n (ZMod 2))) : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ Multiplicative.toAdd (e₂ z)) from rfl, inv_inv,
      toAdd_ofAdd] at h3
    exact h3.symm
  have hDann : ∀ z : ↥U₂, (z : X) ∈ fixV F → D ≤ annSub U₁ e₁ (Multiplicative.toAdd (e₂ z)) := by
    intro z hz
    rw [hD, commSub, Subgroup.closure_le]
    rintro _ ⟨f, hf, w, hw, rfl⟩
    obtain ⟨g₀, hg₀⟩ := hR₁.1 ⟨f, hFH hf⟩
    set g : ↥(StatedSL n (ZMod 2)) := g₀ with hgdef
    have hg' : ((π g : ↥H) : MulAut X) = f := congrArg Subtype.val hg₀
    have hfw : f w ∈ U₁ := hR₁.2.2.2.1 ⟨f, hFH hf⟩ w hw
    refine ⟨U₁.mul_mem hfw (U₁.inv_mem hw), ?_⟩
    have hw' : ((π g : ↥H) : MulAut X) ((⟨w, hw⟩ : ↥U₁) : X) ∈ U₁ := by rw [hg']; exact hfw
    have h1 := he₁ g ⟨w, hw⟩ hw'
    have h2 : (⟨f w * w⁻¹, U₁.mul_mem hfw (U₁.inv_mem hw)⟩ : ↥U₁) =
        ⟨_, hw'⟩ * (⟨w, hw⟩ : ↥U₁)⁻¹ := by
      apply Subtype.ext
      show f w * w⁻¹ = ((π g : ↥H) : MulAut X) w * w⁻¹
      rw [hg']
    rw [h2, map_mul, map_inv, h1, toAdd_mul, dotProduct_add, dot_toAdd_inv]
    show Multiplicative.toAdd (e₂ z) ⬝ᵥ
        ((((g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ
          Multiplicative.toAdd (e₁ ⟨w, hw⟩)) + _ = 0
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hfixdual z hz f hf g hg']
    exact add_neg_cancel _
  let Ψ : ↥(U₂ ⊓ fixV F) → (Fin γ → ZMod 2) := fun y i =>
    Multiplicative.toAdd (e₂ ⟨y, y.2.1⟩) ⬝ᵥ Multiplicative.toAdd (e₁ ⟨x i, hxU i⟩)
  have hΨ : Function.Injective Ψ := by
    intro y y' hyy'
    set z : ↥U₂ := ⟨y, y.2.1⟩ * (⟨y', y'.2.1⟩ : ↥U₂)⁻¹ with hz
    have hzfix : (z : X) ∈ fixV F := by
      show (y : X) * (y' : X)⁻¹ ∈ fixV F
      exact (fixV F).mul_mem y.2.2 ((fixV F).inv_mem y'.2.2)
    have hzx : ∀ i, x i ∈ annSub U₁ e₁ (Multiplicative.toAdd (e₂ z)) := by
      intro i
      refine ⟨hxU i, ?_⟩
      have := congrFun hyy' i
      simp only [Ψ] at this
      rw [hz, map_mul, map_inv, dot_toAdd_mul_inv, this, sub_self]
    have hle : U₁ ≤ annSub U₁ e₁ (Multiplicative.toAdd (e₂ z)) := by
      have h2 : D ⊔ Subgroup.closure (Set.range x) ≤
          annSub U₁ e₁ (Multiplicative.toAdd (e₂ z)) := by
        refine sup_le (hDann z hzfix) ?_
        rw [Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        exact hzx i
      intro u hu
      rw [← hgen] at hu
      exact h2 hu
    have hzero : Multiplicative.toAdd (e₂ z) = 0 := by
      funext j
      obtain ⟨u, hu⟩ := e₁.surjective (Multiplicative.ofAdd (Pi.single j 1))
      obtain ⟨_, h1⟩ := hle u.2
      rw [show (⟨(u : X), u.2⟩ : ↥U₁) = u from rfl, hu, toAdd_ofAdd, dotProduct_single_one] at h1
      exact h1
    have hz1 : z = 1 := by
      apply e₂.injective
      rw [map_one]
      exact hzero
    rw [hz, mul_inv_eq_one] at hz1
    exact Subtype.ext (congrArg (fun w : ↥U₂ => (w : X)) hz1)
  have hcard := Nat.card_le_card_of_injective Ψ hΨ
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin γ), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card] at hcard
  rw [card_eq_two_pow hX] at hcard
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  omega

end Dual

end CFSG.Quasithin.SmithD391

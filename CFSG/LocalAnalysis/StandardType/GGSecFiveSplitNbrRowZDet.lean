module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoBridge
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] noncomputable def ggDetLin {p : ℕ} [Fact p.Prime] {H : Type} [CommGroup H]
    [Module (ZMod p) (Additive H)] : MulAut H →* (ZMod p)ˣ :=
  (LinearEquiv.det : (Additive H ≃ₗ[ZMod p] Additive H) →* (ZMod p)ˣ).comp
    (ggLinAut (p := p) (H := H))

@[expose] noncomputable def ggDetAut (p : ℕ) (hP : p.Prime) {H : Type} [Group H]
    (hc : ∀ a b : H, a * b = b * a) (hp : ∀ a : H, a ^ p = 1) : MulAut H →* (ZMod p)ˣ :=
  haveI : Fact p.Prime := ⟨hP⟩
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hc }
  letI : Module (ZMod p) (Additive H) := AddCommGroup.zmodModule (n := p) fun a => by
    have h : (Additive.toMul a) ^ p = 1 := hp _
    rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  ggDetLin (p := p) (H := H)

private theorem ggDetLin_congr {p : ℕ} [Fact p.Prime] {H H' : Type} [CommGroup H] [CommGroup H']
    [Module (ZMod p) (Additive H)] [Module (ZMod p) (Additive H')] (Θ : H ≃* H')
    (s : MulAut H) : ggDetLin (p := p) (MulAut.congr Θ s) = ggDetLin (p := p) s := by
  let e : Additive H ≃ₗ[ZMod p] Additive H' :=
    (MulEquiv.toAdditive Θ).toLinearEquiv fun c v => ZMod.map_smul (MulEquiv.toAdditive Θ) c v
  have h : ggLinAut (p := p) (MulAut.congr Θ s) =
      (e.symm.trans (ggLinAut (p := p) s)).trans e := by
    ext v
    rfl
  rw [ggDetLin, MonoidHom.comp_apply, h, LinearEquiv.det_conj]
  rfl

theorem ggDetAut_congr (p : ℕ) (hP : p.Prime) {H H' : Type} [Group H] [Group H']
    (hc : ∀ a b : H, a * b = b * a) (hp : ∀ a : H, a ^ p = 1)
    (hc' : ∀ a b : H', a * b = b * a) (hp' : ∀ a : H', a ^ p = 1) (Θ : H ≃* H')
    (s : MulAut H) :
    ggDetAut p hP hc' hp' (MulAut.congr Θ s) = ggDetAut p hP hc hp s := by
  haveI : Fact p.Prime := ⟨hP⟩
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hc }
  letI : CommGroup H' := { (inferInstance : Group H') with mul_comm := hc' }
  letI : Module (ZMod p) (Additive H) := AddCommGroup.zmodModule (n := p) fun a => by
    have h : (Additive.toMul a) ^ p = 1 := hp _
    rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  letI : Module (ZMod p) (Additive H') := AddCommGroup.zmodModule (n := p) fun a => by
    have h : (Additive.toMul a) ^ p = 1 := hp' _
    rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  show ggDetLin (p := p) (H := H') (MulAut.congr Θ s) = ggDetLin (p := p) (H := H) s
  exact ggDetLin_congr (p := p) Θ s

theorem ggDet_sq_eq_one_of_reflGen {G : Type} [Group G] {p : ℕ} (hP : p.Prime)
    {Bs : Subgroup G} (hc : ∀ a b : ↥Bs, a * b = b * a) (hp : ∀ a : ↥Bs, a ^ p = 1)
    {A : Subgroup (MulAut ↥Bs)} (hA : GGReflGenerated p A) {φ : MulAut ↥Bs} (hφ : φ ∈ A) :
    ((ggDetAut p hP hc hp φ : (ZMod p)ˣ)) ^ 2 = 1 := by
  have hker : A ≤ ((powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).comp
      (ggDetAut p hP hc hp)).ker := by
    rw [hA]
    refine (Subgroup.closure_le _).mpr ?_
    rintro r ⟨-, hr⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, powMonoidHom_apply,
      ← map_pow, hr.1, map_one]
  have h := hker hφ
  rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, powMonoidHom_apply] at h

theorem ggDetAut_eq_det_ggLin {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive Bs ≃+ V) (φ : MulAut Bs) :
    ggDetAut p (Fact.out : p.Prime) (fun a b : Bs => hBs.1.is_comm.comm a b)
      (fun b : Bs => Subtype.ext (by simpa using hBs.2 b b.2)) φ =
        (ggLin (p := p) ι φ).det := by
  let : CommGroup Bs := { (inferInstance : Group Bs) with mul_comm := fun a b => hBs.1.is_comm.comm a b }
  let : Module (ZMod p) (Additive Bs) := AddCommGroup.zmodModule (n := p) fun b => by
    have hb : (Additive.toMul b) ^ p = 1 := Subtype.ext (by simpa using hBs.2 (Additive.toMul b : Bs) (Additive.toMul b : Bs).2)
    rw [← ofMul_toMul b, ← ofMul_pow, hb, ofMul_one]
  let e : Additive Bs ≃ₗ[ZMod p] V := ι.toLinearEquiv fun c v => ZMod.map_smul ι c v
  have he : ggLin (p := p) ι φ = (e.symm.trans (ggLinAut (p := p) φ)).trans e := by
    ext v
    rfl
  rw [he,LinearEquiv.det_conj]
  rfl

theorem ggLin_det_sq_eq_one_of_reflGen {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive Bs ≃+ V) {A : Subgroup (MulAut Bs)} (hA : GGReflGenerated p A)
    {g : MulAut Bs} (hg : g ∈ A) : (ggLin (p := p) ι g).det ^ 2 = 1 := by
  rw [← ggDetAut_eq_det_ggLin hBs ι g]
  exact ggDet_sq_eq_one_of_reflGen Fact.out (fun a b => hBs.1.is_comm.comm a b)
    (fun b => Subtype.ext (by simpa using hBs.2 b b.2)) hA hg


theorem ggLin_det_sq_eq_one_of_mem_closure_refl {p : ℕ} [Fact p.Prime] {E : Type*} [Group E]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type*} (ι : Additive E ≃+ V)
    (φ : Λ → MulAut E) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hα : ∀ i, α i (h i) = 2) (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {g : MulAut E} (hg : g ∈ Subgroup.closure (Set.range φ)) :
    (ggLin (p := p) ι g).det ^ 2 = 1 := by
  have hker : Subgroup.closure (Set.range φ) ≤ ((powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).comp
      ((LinearEquiv.det : (V ≃ₗ[ZMod p] V) →* (ZMod p)ˣ).comp (ggLin (p := p) ι))).ker := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have hr : ∀ w, ggLin (p := p) ι (φ i) (ggLin (p := p) ι (φ i) w) = w := by
      have he : ∀ w, ggLin (p := p) ι (φ i) w = Module.reflection (hα i) w := fun w => by
        rw [hφ i w, Module.reflection_apply]
      intro w
      rw [he, he]
      exact Module.involutive_reflection (hα i) w
    have hinv : ggLin (p := p) ι (φ i) * ggLin (p := p) ι (φ i) = 1 :=
      LinearEquiv.ext fun w => hr w
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
      powMonoidHom_apply, pow_two, ← map_mul, hinv, map_one]
  have h := hker hg
  rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, powMonoidHom_apply] at h

theorem ggLin_det_of_pow {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) {φ : MulAut E} {k : ℕ}
    (hk : ∀ b, φ b = b ^ k) :
    ((ggLin (p := p) ι φ).det : ZMod p) = (k : ZMod p) ^ Module.finrank (ZMod p) V := by
  have h : (ggLin (p := p) ι φ : V →ₗ[ZMod p] V) = (k : ZMod p) • LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.coe_coe, ggLin_apply, hk, LinearMap.smul_apply, LinearMap.id_apply, ofMul_pow,
      ofMul_toMul, map_nsmul, AddEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
  rw [LinearEquiv.coe_det, h, LinearMap.det_smul, LinearMap.det_id, mul_one]

end CFSG.StandardType

end

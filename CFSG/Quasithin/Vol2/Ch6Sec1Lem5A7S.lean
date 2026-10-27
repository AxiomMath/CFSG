module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Quasithin.Background.SmithB45Alt7Sym
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt

public section

namespace CFSG.Quasithin.H13.A7S

open Equiv

section Schur

variable {V : Type} [CommGroup V] {F : Subgroup (MulAut V)}

@[expose] noncomputable def conjF_ch615 (x : ↥(Subgroup.normalizer (F : Set (MulAut V)))) :
    MulAut ↥F where
  toFun f := ⟨(x : MulAut V) * f * (x : MulAut V)⁻¹,
    (Subgroup.mem_normalizer_iff.mp x.2 f).mp f.2⟩
  invFun f := ⟨(x : MulAut V)⁻¹ * f * (x : MulAut V), by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ x.2) f).mp f.2
    rwa [inv_inv] at h⟩
  left_inv f := Subtype.ext (by simp [mul_assoc])
  right_inv f := Subtype.ext (by simp [mul_assoc])
  map_mul' f g := Subtype.ext (by simp [mul_assoc])

theorem conjF_apply_ch615 (x : ↥(Subgroup.normalizer (F : Set (MulAut V)))) (f : ↥F) :
    ((conjF_ch615 x f : ↥F) : MulAut V) = (x : MulAut V) * f * (x : MulAut V)⁻¹ := rfl

variable (ι : ↥F ≃* ↥(alternatingGroup (Fin 7)))

@[expose] noncomputable def alpha_ch615 (x : ↥(Subgroup.normalizer (F : Set (MulAut V)))) :
    MulAut ↥(alternatingGroup (Fin 7)) :=
  (ι.symm.trans (conjF_ch615 x)).trans ι

theorem alpha_mul_ch615 (x y : ↥(Subgroup.normalizer (F : Set (MulAut V)))) :
    alpha_ch615 ι (x * y) = alpha_ch615 ι x * alpha_ch615 ι y := by
  ext a
  simp only [alpha_ch615, MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.symm_apply_apply]
  congr 2

theorem alpha_one_ch615 : alpha_ch615 ι (1 : ↥(Subgroup.normalizer (F : Set (MulAut V)))) = 1 := by
  ext a
  simp only [alpha_ch615, MulEquiv.trans_apply, MulAut.one_apply]
  have : conjF_ch615 (1 : ↥(Subgroup.normalizer (F : Set (MulAut V)))) (ι.symm a) = ι.symm a :=
    Subtype.ext (by simp [conjF_apply_ch615])
  rw [this, MulEquiv.apply_symm_apply]

theorem conjNormal_bij_ch615 :
    Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)) :
      Perm (Fin 7) →* MulAut ↥(alternatingGroup (Fin 7))) :=
  CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)

@[expose] noncomputable def sig_ch615 :
    ↥(Subgroup.normalizer (F : Set (MulAut V))) →* Perm (Fin 7) where
  toFun x := Function.surjInv conjNormal_bij_ch615.2 (alpha_ch615 ι x)
  map_one' := conjNormal_bij_ch615.1 (by
    rw [Function.surjInv_eq conjNormal_bij_ch615.2, alpha_one_ch615, map_one])
  map_mul' x y := conjNormal_bij_ch615.1 (by
    rw [map_mul, Function.surjInv_eq conjNormal_bij_ch615.2,
      Function.surjInv_eq conjNormal_bij_ch615.2, Function.surjInv_eq conjNormal_bij_ch615.2,
      alpha_mul_ch615])

theorem conjNormal_sig_ch615 (x : ↥(Subgroup.normalizer (F : Set (MulAut V)))) :
    MulAut.conjNormal (H := alternatingGroup (Fin 7)) (sig_ch615 ι x) = alpha_ch615 ι x :=
  Function.surjInv_eq conjNormal_bij_ch615.2 _

theorem sig_conj_ch615 (x : ↥(Subgroup.normalizer (F : Set (MulAut V))))
    (a : ↥(alternatingGroup (Fin 7))) :
    sig_ch615 ι x * (a : Perm (Fin 7)) * (sig_ch615 ι x)⁻¹ =
      (ι (conjF_ch615 x (ι.symm a)) : Perm (Fin 7)) := by
  have h := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin 7)) => (φ a : Perm (Fin 7)))
    (conjNormal_sig_ch615 ι x)
  simpa only [MulAut.conjNormal_apply, alpha_ch615, MulEquiv.trans_apply] using h

variable (β : V ≃* ↥(G6.coreMod 7))
  (hβ : ∀ (f : ↥F) (v : V), (β ((f : MulAut V) v) : G6.PermMod 7) = G6.permAct 7 (ι f) (β v))
include hβ

theorem sig_spec_ch615 (x : ↥(Subgroup.normalizer (F : Set (MulAut V)))) (v : V) :
    (β ((x : MulAut V) v) : G6.PermMod 7) = G6.permAct 7 (sig_ch615 ι x) (β v) := by
  set σ := sig_ch615 ι x with hσ
  let E : ↥(G6.coreMod 7) →* ↥(G6.coreMod 7) :=
    { toFun := fun m => ⟨G6.permAct 7 σ⁻¹ (β ((x : MulAut V) (β.symm m))),
        G6.permAct_mem_coreMod _ (β ((x : MulAut V) (β.symm m))).2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun m n => Subtype.ext (by simp) }
  have hEi : Function.Injective E := by
    intro m n h
    have h1 := congrArg Subtype.val h
    simp only [E, MonoidHom.coe_mk, OneHom.coe_mk] at h1
    have h2 := (G6.permAct 7 σ⁻¹).injective h1
    have h3 := β.injective (Subtype.ext h2)
    exact β.symm.injective ((x : MulAut V).injective h3)
  have hE : ∀ τ ∈ alternatingGroup (Fin 7), ∀ m : ↥(G6.coreMod 7),
      (E ⟨G6.permAct 7 τ m, G6.permAct_mem_coreMod τ m.2⟩ : G6.PermMod 7) =
        G6.permAct 7 τ (E m) := by
    intro τ hτ m
    set a : ↥(alternatingGroup (Fin 7)) := ⟨τ, hτ⟩ with ha
    have h1 : β.symm ⟨G6.permAct 7 τ m, G6.permAct_mem_coreMod τ m.2⟩ =
        ((ι.symm a : ↥F) : MulAut V) (β.symm m) := by
      apply β.injective
      apply Subtype.ext
      rw [MulEquiv.apply_symm_apply, hβ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have h2 : (x : MulAut V) (((ι.symm a : ↥F) : MulAut V) (β.symm m)) =
        ((conjF_ch615 x (ι.symm a) : ↥F) : MulAut V) ((x : MulAut V) (β.symm m)) := by
      rw [conjF_apply_ch615]
      simp [MulAut.mul_apply]
    have h3 : (β (((conjF_ch615 x (ι.symm a) : ↥F) : MulAut V) ((x : MulAut V) (β.symm m))) :
        G6.PermMod 7) = G6.permAct 7 (σ * τ * σ⁻¹) (β ((x : MulAut V) (β.symm m))) := by
      rw [hβ]
      congr 2
      rw [hσ]
      exact (sig_conj_ch615 ι x a).symm
    show G6.permAct 7 σ⁻¹ (β ((x : MulAut V) (β.symm ⟨G6.permAct 7 τ m, _⟩))) =
      G6.permAct 7 τ (G6.permAct 7 σ⁻¹ (β ((x : MulAut V) (β.symm m))))
    rw [h1, h2, h3, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
    congr 1
    group
  have hS := B45Alt7.schur_coreMod E hEi hE (β v)
  have h4 := congrArg Subtype.val hS
  simp only [E, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.symm_apply_apply] at h4
  rw [← h4, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

omit hβ in
theorem sig_of_mem_ch615 (f : ↥F) :
    sig_ch615 ι ⟨f, Subgroup.le_normalizer f.2⟩ = (ι f : Perm (Fin 7)) := by
  apply conjNormal_bij_ch615.1
  rw [conjNormal_sig_ch615]
  ext a
  simp only [alpha_ch615, MulEquiv.trans_apply, MulAut.conjNormal_apply]
  have : conjF_ch615 ⟨(f : MulAut V), Subgroup.le_normalizer f.2⟩ (ι.symm a) = f * ι.symm a * f⁻¹ :=
    Subtype.ext (by simp [conjF_apply_ch615])
  rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem sig_injective_ch615 : Function.Injective (sig_ch615 ι :
    ↥(Subgroup.normalizer (F : Set (MulAut V))) →* Perm (Fin 7)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply Subtype.ext
  ext v
  have h := sig_spec_ch615 ι β hβ x v
  rw [hx, map_one, MulAut.one_apply] at h
  exact β.injective (Subtype.ext h)


omit hβ in
@[expose] noncomputable def imgS_ch615 (A : Subgroup (MulAut V)) : Subgroup (Perm (Fin 7)) :=
  (A.subgroupOf (Subgroup.normalizer (F : Set (MulAut V)))).map (sig_ch615 ι)

omit hβ in
theorem mem_imgS_ch615 {A : Subgroup (MulAut V)} {σ : Perm (Fin 7)} :
    σ ∈ imgS_ch615 ι A ↔ ∃ x : ↥(Subgroup.normalizer (F : Set (MulAut V))),
      (x : MulAut V) ∈ A ∧ sig_ch615 ι x = σ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem card_imgS_ch615 {A : Subgroup (MulAut V)}
    (hA : A ≤ Subgroup.normalizer (F : Set (MulAut V))) :
    Nat.card ↥(imgS_ch615 ι A) = Nat.card ↥A := by
  rw [imgS_ch615, Subgroup.card_map_of_injective (sig_injective_ch615 ι β hβ)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

open CFSG.QuasithinUnique.Setup.SL2Modules in
theorem card_fixV_imgS_ch615 {A : Subgroup (MulAut V)}
    (hA : A ≤ Subgroup.normalizer (F : Set (MulAut V))) :
    Nat.card ↥(fixV A) = Nat.card ↥(evenWeight (Fin 7) ⊓ fixedVectors (imgS_ch615 ι A)) := by
  classical
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd (β v : G6.PermMod 7), (β v).2, ?_⟩
      invFun := fun x => ⟨β.symm ⟨Multiplicative.ofAdd x.1, x.2.1⟩, ?_⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  · intro σ hσ
    obtain ⟨a, ha, rfl⟩ := (mem_imgS_ch615 ι).1 hσ
    have h1 := sig_spec_ch615 ι β hβ a v
    rw [v.2 _ ha] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    funext i
    have h3 := (congrFun h2 i).symm
    rwa [G6.permAct_apply] at h3
  · intro a ha
    have h1 := sig_spec_ch615 ι β hβ ⟨a, hA ha⟩ (β.symm ⟨Multiplicative.ofAdd x.1, x.2.1⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    have hfix := x.2.2 _ ((mem_imgS_ch615 ι).2 ⟨⟨a, hA ha⟩, ha, rfl⟩)
    apply β.injective
    apply Subtype.ext
    rw [h1, MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    funext i
    rw [G6.permAct_apply]
    exact congrFun hfix i

end Schur

section Coords

variable {V : Type} [CommGroup V] {F : Subgroup (MulAut V)}

@[expose] noncomputable def coreAut_ch615 (σ : Perm (Fin 7)) :
    ↥(G6.coreMod 7) ≃* ↥(G6.coreMod 7) where
  toFun m := ⟨G6.permAct 7 σ m, G6.permAct_mem_coreMod σ m.2⟩
  invFun m := ⟨G6.permAct 7 σ⁻¹ m, G6.permAct_mem_coreMod σ⁻¹ m.2⟩
  left_inv m := Subtype.ext (by
    show G6.permAct 7 σ⁻¹ (G6.permAct 7 σ m) = m
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
  right_inv m := Subtype.ext (by
    show G6.permAct 7 σ (G6.permAct 7 σ⁻¹ m) = m
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
  map_mul' m n := Subtype.ext (map_mul (G6.permAct 7 σ) (m : G6.PermMod 7) n)

theorem hβ_conj_ch615 (ι : ↥F ≃* ↥(alternatingGroup (Fin 7))) (β : V ≃* ↥(G6.coreMod 7))
    (hβ : ∀ (f : ↥F) (v : V), (β ((f : MulAut V) v) : G6.PermMod 7) = G6.permAct 7 (ι f) (β v))
    (h : Perm (Fin 7)) (f : ↥F) (v : V) :
    ((β.trans (coreAut_ch615 h⁻¹)) ((f : MulAut V) v) : G6.PermMod 7) =
      G6.permAct 7 ((ι.trans (MulAut.conjNormal (H := alternatingGroup (Fin 7)) h⁻¹)) f)
        ((β.trans (coreAut_ch615 h⁻¹)) v) := by
  show G6.permAct 7 h⁻¹ (β ((f : MulAut V) v)) = G6.permAct 7 (h⁻¹ * ι f * h⁻¹⁻¹)
    (G6.permAct 7 h⁻¹ (β v))
  rw [hβ, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

end Coords

end CFSG.Quasithin.H13.A7S

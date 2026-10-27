module

public import CFSG.Quasithin.H13.L32NLem14325i
public import CFSG.Quasithin.Vol2.Ch10SecQ4H4
public import CFSG.Quasithin.H13.L32NLem14325e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.Vol2.Ch10.SecF

namespace L14325

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

omit [Finite G] in
theorem H_le_normalizer_vP (c : G) : l32nH T V ≤ Subgroup.normalizer (vP T V c : Set G) :=
  le_normalizer_conjClosure _ _

namespace CtxI

variable (C : CtxI G T L V V₂ g D)
include C

theorem sqtk : CFSG.SectionRank.IsSQTKCat ↥(l32nH T V) := by
  have := C.ctx.hyp.fsu.simple
  exact (QuasithinUnique.qtkeCore_of_cat C.ctx.hyp.fsu.nonabelian C.ctx.hyp.fsu.qtke).1 _
    C.ctx.pCoreOf_ne_bot

@[expose] noncomputable def rhoK : ↥(kI T V g) →* ↥(D.img (kI T V g)) :=
  (D.ρ.comp (Subgroup.inclusion (C.kI_le.trans (L14332.l32nH_le_normalizer_fsuU T V)))).codRestrict
    _ fun k => L128A.HatU.rho_mem_img D k.2 _

theorem rhoK_coe (k : ↥(kI T V g)) :
    ((C.rhoK k : ↥(D.img (kI T V g))) : D.V ≃ₗ[ZMod 2] D.V) =
      D.ρ ⟨k, L14332.l32nH_le_normalizer_fsuU T V (C.kI_le k.2)⟩ := rfl

theorem rhoK_surjective : Function.Surjective C.rhoK := by
  rintro ⟨γ, hγ⟩
  obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  exact ⟨⟨k, hk⟩, rfl⟩

namespace TransData

variable {C} {x c : G} (X : TransData C x c)
include X

theorem tr : ∀ w ∈ vH T L V, x * w * x⁻¹ = w ∨ x * w * x⁻¹ = w * c := by
  intro w hw
  rcases X.comm w (C.ctx.vH_le hw) with h | h
  · left
    calc x * w * x⁻¹ = x * w * x⁻¹ * w⁻¹ * w := by group
      _ = w := by rw [h, one_mul]
  · right
    calc x * w * x⁻¹ = x * w * x⁻¹ * w⁻¹ * w := by group
      _ = c * w := by rw [h]
      _ = w * c := C.vH_comm X.c_mem hw

theorem not_cent : x ∉ Subgroup.centralizer (vH T L V : Set G) := fun hxc =>
  X.x_ne (L14332.l32nH_le_normalizer_fsuU T V X.x_H) ((L14332.rho_eq_one_iff_mem X.x_H _).mpr
    (C.mem_cHat_of_mem_centralizer (zUg_le_kI X.x_mem) hxc))

theorem elem : IsElemAbelian 2 (vP T V c) :=
  C10E4.isElemAbelian_two_of_le C.ctx.red.2.2.1 X.vP_le

theorem hyp61 : G64.Hyp61 (autI X.elem (l32nH T V)) (C10E4.transvI X.elem X.x_H) :=
  C10E4.hyp61_autI X.elem C.sqtk C.ctx.red X.x_H X.c_mem X.c_ne X.tr X.not_cent

theorem card_comm : Nat.card ↥(commV (Subgroup.zpowers (C10E4.transvI X.elem X.x_H))) = 2 :=
  C10E4.card_commV_transvI X.elem C.ctx.red X.x_H X.c_mem X.c_ne X.tr X.not_cent

theorem concl (h64 : G64.LemmaG64) :
    G64.Conclusion (autI X.elem (l32nH T V)) (C10E4.transvI X.elem X.x_H) :=
  h64 _ IntMod.sq_eq_one _ _ X.hyp61 X.card_comm

theorem transvI_sq : C10E4.transvI X.elem X.x_H ^ 2 = 1 :=
  C10E4.transvI_sq X.elem C.ctx.red.2.1 X.c_mem X.c_ne X.tr X.x_H

theorem cent_vH {k : G} (hk : k ∈ kI T V g)
    (hkc : k ∈ Subgroup.centralizer (vP T V c : Set G)) :
    k ∈ Subgroup.centralizer (vH T L V : Set G) := by
  have hU2 : ∀ u ∈ vP T V c, u * u = 1 := fun u hu => C.vH_sq (X.vP_le hu)
  refine C.ctx.red.2.2.2 (kI T V g ⊓ Subgroup.centralizer (vP T V c : Set G))
    (inf_le_left.trans C.kI_le)
    (fun h hh => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_kI hh, le_normalizer_centralizer (H_le_normalizer_vP c hh)⟩)
    (fun d hd => ⟨1, by
      have := C10E4.sq_mem_centralizer (V := vH T L V) hU2
        (fun w hw => X.comm_mem_vP hd.1 (C.ctx.vH_le hw)) hd.2
      simpa using this⟩) ⟨hk, hkc⟩

theorem convI_zg {z : G} (hz : z ∈ CFSG.conjugate (centerOf (fsuU T V)) g)
    (hzN : z ∈ Subgroup.normalizer (vP T V c : Set G)) :
    convI X.elem ⟨z, hzN⟩ = 1 ∨ convI X.elem ⟨z, hzN⟩ = C10E4.transvI X.elem X.x_H := by
  rcases X.zg_cases hz with h | h
  · left
    ext m
    apply IntMod.val_injective
    rw [convI_apply_val, MulAut.one_apply]
    exact h _ (C.ctx.vH_le (X.vP_le m.val_mem))
  · right
    ext m
    apply IntMod.val_injective
    rw [convI_apply_val, C10E4.transvI_apply_val]
    exact h _ (C.ctx.vH_le (X.vP_le m.val_mem))

theorem autI_kI : autI X.elem (kI T V g) =
    conjClosure (Subgroup.zpowers (C10E4.transvI X.elem X.x_H)) (autI X.elem (l32nH T V)) := by
  apply le_antisymm
  · set S : Subgroup G := ((conjClosure (Subgroup.zpowers (C10E4.transvI X.elem X.x_H))
      (autI X.elem (l32nH T V))).comap (convI X.elem)).map
      (Subgroup.normalizer (vP T V c : Set G)).subtype with hS
    have hKS : kI T V g ≤ S := conjClosure_le fun h hh z hz => by
      have hzH := C.ctx.zUg_le hz
      have hN := H_le_normalizer_vP c
        ((l32nH T V).mul_mem ((l32nH T V).mul_mem hh hzH) ((l32nH T V).inv_mem hh))
      refine ⟨⟨h * z * h⁻¹, hN⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (⟨h * z * h⁻¹, hN⟩ : ↥(Subgroup.normalizer (vP T V c : Set G))) =
          ⟨h, H_le_normalizer_vP c hh⟩ * ⟨z, H_le_normalizer_vP c hzH⟩ *
            (⟨h, H_le_normalizer_vP c hh⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      refine mem_conjClosure (convI_mem_autI X.elem hh _) ?_
      rcases X.convI_zg hz (H_le_normalizer_vP c hzH) with h1 | h1 <;> rw [h1]
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
    intro φ hφ
    obtain ⟨k, hk, rfl⟩ := (mem_autI X.elem).mp hφ
    obtain ⟨k', hk', hk'k⟩ := hKS hk
    have : k' = k := Subtype.ext hk'k
    rw [← this]
    exact hk'
  · refine conjClosure_le fun φ hφ ζ hζ => ?_
    obtain ⟨h, hh, rfl⟩ := (mem_autI X.elem).mp hφ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hζ
    have hxN := H_le_normalizer_vP c X.x_H
    refine (mem_autI X.elem).mpr ⟨h * (⟨x, hxN⟩ ^ n) * h⁻¹, ?_, ?_⟩
    · show (h : G) * x ^ n * (h : G)⁻¹ ∈ kI T V g
      exact mem_conjClosure hh (Subgroup.zpow_mem _ X.x_mem n)
    · rw [map_mul, map_mul, map_inv, map_zpow]
      rfl

noncomputable abbrev kStar : Subgroup (MulAut (IntMod (vP T V c) X.elem)) :=
  conjClosure (Subgroup.zpowers (C10E4.transvI X.elem X.x_H)) (autI X.elem (l32nH T V))

@[expose] noncomputable def phi : ↥(kI T V g) →* ↥X.kStar :=
  (convHom X.elem (kI T V g) (C.kI_le.trans (H_le_normalizer_vP c))).codRestrict X.kStar
    fun k => by
      rw [kStar, ← X.autI_kI, ← range_convHom X.elem _ (C.kI_le.trans (H_le_normalizer_vP c))]
      exact ⟨k, rfl⟩

theorem phi_coe (k : ↥(kI T V g)) :
    ((X.phi k : ↥X.kStar) : MulAut (IntMod (vP T V c) X.elem)) =
      convI X.elem ⟨k, H_le_normalizer_vP c (C.kI_le k.2)⟩ := rfl

theorem phi_surjective : Function.Surjective X.phi := by
  rintro ⟨φ, hφ⟩
  rw [kStar, ← X.autI_kI, ← range_convHom X.elem _ (C.kI_le.trans (H_le_normalizer_vP c))] at hφ
  obtain ⟨k, hk⟩ := hφ
  exact ⟨k, Subtype.ext hk⟩

theorem ker_phi_le : X.phi.ker ≤ C.rhoK.ker := by
  intro k hk
  rw [MonoidHom.mem_ker] at hk ⊢
  have h1 : convI X.elem ⟨k, H_le_normalizer_vP c (C.kI_le k.2)⟩ = 1 := by
    rw [← X.phi_coe]
    exact congrArg Subtype.val hk
  have hkc := (convI_eq_one_iff X.elem _).mp h1
  have hkE := C.mem_cHat_of_mem_centralizer k.2 (X.cent_vH k.2 hkc)
  apply Subtype.ext
  rw [C.rhoK_coe]
  exact (L14332.rho_eq_one_iff_mem (C.kI_le k.2) _).mpr hkE

theorem exists_psi (e : ↥(D.img (kI T V g)) ≃* Equiv.Perm (Fin 3)) :
    ∃ ψ : ↥X.kStar →* Equiv.Perm (Fin 3), Function.Surjective ψ ∧
      ∀ k : ↥(kI T V g), ψ (X.phi k) = e (C.rhoK k) := by
  set f : ↥(kI T V g) →* Equiv.Perm (Fin 3) := (e : ↥(D.img (kI T V g)) →* _).comp C.rhoK
    with hf
  have hker : X.phi.ker ≤ f.ker := fun k hk => by
    have := X.ker_phi_le hk
    rw [MonoidHom.mem_ker] at this ⊢
    rw [hf, MonoidHom.comp_apply, this, map_one]
  set ψ := X.phi.liftOfRightInverseAux (Function.surjInv X.phi_surjective)
    (Function.rightInverse_surjInv X.phi_surjective) f hker with hψ
  have hψk : ∀ k, ψ (X.phi k) = e (C.rhoK k) := fun k =>
    MonoidHom.liftOfRightInverseAux_comp_apply _ _ _ _ _ k
  refine ⟨ψ, fun σ => ?_, hψk⟩
  obtain ⟨γ, rfl⟩ := e.surjective σ
  obtain ⟨k, rfl⟩ := C.rhoK_surjective γ
  exact ⟨X.phi k, hψk k⟩

end TransData

end CtxI

end L14325

end CFSG.Quasithin.H13

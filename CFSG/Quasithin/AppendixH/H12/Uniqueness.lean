module

public import CFSG.Quasithin.AppendixH.H12.GLAction
public import CFSG.Quasithin.Background.HM22Recog
public import CFSG.Milestones.ASVolI.H6
public import CFSG.Quasithin.AppendixH.H12.Vocab
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section


open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH
open CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin.H.Mathieu.H12Cert
open CFSG.Quasithin.H.Mathieu.M22Link
open CFSG.Quasithin.AppendixH.H12.Model (Vec12 glHom toAdd_glHom glHom_injective)

namespace CFSG.Quasithin.AppendixH.H12

private theorem isIrredOn_of_isIrrSec {V : Type} [CommGroup V] (L : Subgroup (MulAut V))
    (h : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) : IsIrredOn L ⊤ := by
  obtain ⟨hlt, hsec⟩ := h
  refine ⟨hlt.ne', fun U _ hU => hsec U ?_ bot_le le_top⟩
  intro a u hu
  rw [Subgroup.smul_def, MulAut.smul_def]
  exact hU a.1 a.2 u hu

private theorem normalizerMonoidHom_surjective :
    Function.Surjective (H12Cert.G.normalizerMonoidHom) := by
  have hker : Nat.card ↥(H12Cert.G.normalizerMonoidHom.ker) = 3 := by
    have hmap : (H12Cert.G.normalizerMonoidHom.ker).map (Subgroup.subtype M22Link.normG) =
        Subgroup.zpowers H12Cert.zU := by
      apply le_antisymm
      · rintro x ⟨y, hy, rfl⟩
        have hy' := MonoidHom.mem_ker.mp hy
        apply M22Link.mem_zpowers_of_comm
        intro g hg
        have h1 := congrArg Subtype.val (congrArg (fun f : MulAut ↥H12Cert.G => f ⟨g, hg⟩) hy')
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
        simp only [MulAut.one_apply] at h1
        have h2 : (y : GL (Fin 12) (ZMod 2)) * g = g * (y : GL (Fin 12) (ZMod 2)) := by
          calc (y : GL (Fin 12) (ZMod 2)) * g
              = ((y : GL (Fin 12) (ZMod 2)) * g * (y : GL (Fin 12) (ZMod 2))⁻¹) *
                  (y : GL (Fin 12) (ZMod 2)) := by group
            _ = g * (y : GL (Fin 12) (ZMod 2)) := by rw [h1]
        exact h2.symm
      · apply Subgroup.zpowers_le.mpr
        refine ⟨⟨H12Cert.zU, Subgroup.le_normalizer H12Cert.zU_mem⟩, ?_, rfl⟩
        refine MonoidHom.mem_ker.mpr ?_
        apply MulEquiv.ext
        intro g
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        simp only [MulAut.one_apply]
        rw [← H12Cert.zU_comm g.2, mul_assoc, mul_inv_cancel, mul_one]
    have hcard : Nat.card ↥((H12Cert.G.normalizerMonoidHom.ker).map
          (Subgroup.subtype M22Link.normG)) =
        Nat.card ↥(H12Cert.G.normalizerMonoidHom.ker) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective M22Link.normG)
    rw [hmap] at hcard
    rw [← hcard, Nat.card_zpowers, H12Cert.orderOf_zU]
  have hcardrange : Nat.card ↥(H12Cert.G.normalizerMonoidHom.range) = 887040 := by
    have hnorm : Nat.card ↥M22Link.normG = 2661120 := by
      rw [M22Link.normG_eq, M22Link.card_m22P]
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (H12Cert.G.normalizerMonoidHom.ker)
    have hquot : Nat.card (↥M22Link.normG ⧸ H12Cert.G.normalizerMonoidHom.ker) =
        Nat.card ↥(H12Cert.G.normalizerMonoidHom.range) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange H12Cert.G.normalizerMonoidHom).toEquiv
    have hq' : Nat.card ↥(H12Cert.G.normalizerMonoidHom.range) *
        Nat.card ↥(H12Cert.G.normalizerMonoidHom.ker) = 2661120 := by
      rw [← hnorm, hq, hquot]
    rw [hker] at hq'
    omega
  haveI : Finite ↥H12Cert.G :=
    (Nat.card_ne_zero.mp (by rw [H12Cert.card_G]; norm_num)).2
  have htop : H12Cert.G.normalizerMonoidHom.range = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [hcardrange, Subgroup.card_top]
    exact M22Link.card_mulAut_G_le.trans (by norm_num)
  exact MonoidHom.range_eq_top.mp htop

theorem exists_faithIrr12
    {Λ : Type} [Group Λ]
    (hΛ : IsHat Λ ↥CFSG.Blueprint.NativeSporadic.M22) :
    ∃ (V₀ : Type) (_ : CommGroup V₀) (ρ₀ : Λ →* MulAut V₀), IsFaithIrr12 ρ₀ := by
  obtain ⟨e⟩ := CFSG.Quasithin.HM22.nonempty_mulEquiv_hatM22Γ₀ hΛ
  let f : Λ ≃* ↥H12Cert.G := e.symm.trans H12Pf.hatEquivG
  let ρ₀ : Λ →* MulAut Vec12 := glHom.comp (H12Cert.G.subtype.comp f.toMonoidHom)
  have hsq : ∀ v : Vec12, v ^ 2 = 1 := by
    intro v
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    show (2 : ℕ) • Multiplicative.toAdd v i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hcard : Nat.card Vec12 = 2 ^ 12 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  have hinj : Function.Injective ρ₀ := by
    intro a b hab
    exact f.injective (Subtype.ext (glHom_injective hab))
  refine ⟨Vec12, inferInstance, ρ₀, hsq, hcard, hinj, ?_⟩
  have hL : IsHat ↥ρ₀.range ↥CFSG.Blueprint.NativeSporadic.M22 :=
    isHat_of_mulEquiv' (MonoidHom.ofInjective hinj) hΛ
  have hW : Nat.card Vec12 = 4096 := by rw [hcard]; norm_num
  exact isIrredOn_of_isIrrSec ρ₀.range (isIrrSec_of_isHat hsq hW hL)

theorem modIso_of_faithIrr12
    {Λ : Type} [Group Λ]
    (hΛ : IsHat Λ ↥CFSG.Blueprint.NativeSporadic.M22) {V₁ V₂ : Type} [CommGroup V₁]
    [CommGroup V₂] {ρ₁ : Λ →* MulAut V₁} {ρ₂ : Λ →* MulAut V₂} (h₁ : IsFaithIrr12 ρ₁)
    (h₂ : IsFaithIrr12 ρ₂) : ModIso ρ₁ ρ₂ := by
  haveI hfin₁ : Finite V₁ := (Nat.card_ne_zero.mp (by rw [h₁.2.1]; norm_num)).2
  haveI hfin₂ : Finite V₂ := (Nat.card_ne_zero.mp (by rw [h₂.2.1]; norm_num)).2
  let L₁ : Subgroup (MulAut V₁) := ρ₁.range
  let L₂ : Subgroup (MulAut V₂) := ρ₂.range
  let ι₁ : Λ ≃* ↥L₁ := MonoidHom.ofInjective h₁.2.2.1
  let ι₂ : Λ ≃* ↥L₂ := MonoidHom.ofInjective h₂.2.2.1
  have hL₁ : IsHat ↥L₁ ↥CFSG.Blueprint.NativeSporadic.M22 := isHat_of_mulEquiv' ι₁ hΛ
  have hL₂ : IsHat ↥L₂ ↥CFSG.Blueprint.NativeSporadic.M22 := isHat_of_mulEquiv' ι₂ hΛ
  have hW₁ : Nat.card V₁ = 4096 := by rw [h₁.2.1]; norm_num
  have hW₂ : Nat.card V₂ = 4096 := by rw [h₂.2.1]; norm_num
  obtain ⟨ψ₁, θ₁, hθ₁⟩ := exists_model_of_isHat h₁.1 hW₁ hL₁
  obtain ⟨ψ₂, θ₂, hθ₂⟩ := exists_model_of_isHat h₂.1 hW₂ hL₂
  let α : ↥H12Cert.G ≃* ↥H12Cert.G := (ψ₁.trans ι₁.symm).trans (ι₂.trans ψ₂.symm)
  obtain ⟨n, hn⟩ := normalizerMonoidHom_surjective α
  have hn' : ∀ x : ↥H12Cert.G, ((α x : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) =
      (n : GL (Fin 12) (ZMod 2)) * (x : GL (Fin 12) (ZMod 2)) *
        (n : GL (Fin 12) (ZMod 2))⁻¹ := by
    intro x
    have h := Subgroup.normalizerMonoidHom_apply_apply_coe H12Cert.G n x
    rw [hn] at h
    exact h
  let e : V₁ →* V₂ := (θ₂.symm.toMonoidHom).comp
    ((glHom (n : GL (Fin 12) (ZMod 2))).toMonoidHom.comp θ₁.toMonoidHom)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : glHom (n : GL (Fin 12) (ZMod 2)) (θ₁ a) =
        glHom (n : GL (Fin 12) (ZMod 2)) (θ₁ b) := by
      have h2 := congrArg θ₂ hab
      simpa [e] using h2
    exact θ₁.injective ((glHom (n : GL (Fin 12) (ZMod 2))).injective h1)
  · rw [MonoidHom.range_eq_top]
    intro y
    refine ⟨θ₁.symm ((glHom (n : GL (Fin 12) (ZMod 2))).symm (θ₂ y)), ?_⟩
    simp [e]
  · intro g₀ v
    set x : ↥H12Cert.G := ψ₁.symm (ι₁ g₀) with hx
    have hρ₁ : ((ψ₁ x : ↥L₁) : MulAut V₁) = ρ₁ g₀ := by
      rw [hx, MulEquiv.apply_symm_apply]
      rfl
    have hαx : α x = ψ₂.symm (ι₂ g₀) := by
      simp only [α, MulEquiv.trans_apply, hx, MulEquiv.symm_apply_apply,
        MulEquiv.apply_symm_apply]
    have hρ₂ : ((ψ₂ (α x) : ↥L₂) : MulAut V₂) = ρ₂ g₀ := by
      rw [hαx, MulEquiv.apply_symm_apply]
      rfl
    have he : ∀ w : V₁, Multiplicative.toAdd (θ₂ (e w)) =
        ((n : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
          (Multiplicative.toAdd (θ₁ w)) := by
      intro w
      show Multiplicative.toAdd (θ₂ (θ₂.symm (glHom (n : GL (Fin 12) (ZMod 2))
        (θ₁ w)))) = ((n : GL (Fin 12) (ZMod 2)) :
          Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (Multiplicative.toAdd (θ₁ w))
      rw [θ₂.apply_symm_apply, toAdd_glHom]
    have hm₁ := hθ₁ x v
    have hm₂ := hθ₂ (α x) (e v)
    rw [← hρ₁, ← hρ₂]
    apply θ₂.injective
    apply Multiplicative.toAdd.injective
    have hmat : (((α x : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) :
          Matrix (Fin 12) (Fin 12) (ZMod 2)) *
        ((n : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        ((n : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
        (((x : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
      have hGL : ((α x : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) *
          (n : GL (Fin 12) (ZMod 2)) =
          (n : GL (Fin 12) (ZMod 2)) * ((x : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) := by
        rw [hn' x]; group
      have hmat' := congrArg (fun u : GL (Fin 12) (ZMod 2) =>
        (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) hGL
      simpa only [Units.val_mul] using hmat'
    rw [he, hm₁, hm₂, he, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]

end CFSG.Quasithin.AppendixH.H12

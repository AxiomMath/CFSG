module

public import CFSG.Quasithin.H13.A6S13824g
public import CFSG.Quasithin.Background.SmithB45Alt7Sym
public import CFSG.Quasithin.H13.A6S13824b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped IsMulCommutative

namespace A7F

theorem act_eq_perm {E : Type*} [CommGroup E] {Λ : Subgroup (MulAut E)} {U Z : Subgroup E}
    {π : (FFModel.altDn 7).Gam →* ↥Λ}
    {β : ↥U →* ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 7) Λ U Z π β) {g : MulAut E}
    {σ : Perm (Fin 7)} (hgU : ∀ u ∈ U, g u ∈ U) (hgZ : ∀ u ∈ U, g u ∈ Z ↔ u ∈ Z)
    (hc : ∀ γ γ' : ↥(alternatingGroup (Fin 7)), (γ' : Perm (Fin 7)) = σ * γ * σ⁻¹ →
      ∀ e, g ((π γ : MulAut E) e) = (π γ' : MulAut E) (g e))
    (u : ↥U) (m : ↥(G6.coreMod 7)) (hm : β u = QuotientGroup.mk m) :
    β ⟨g u, hgU u u.2⟩ =
      QuotientGroup.mk ⟨G6.permAct 7 σ m, G6.permAct_mem_coreMod σ m.2⟩ := by
  classical
  obtain ⟨-, -, -, hΛU, -, -, -, hβs, hβk, hβe⟩ := hR
  set N := (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec with hN
  have hNb : N = ⊥ := by
    rw [hN, QuasithinUnique.B42A57.altDn7_ker, Subgroup.bot_subgroupOf]
  let mk7 : ↥(G6.coreMod 7) →* ↥(FFModel.altDn 7).sec ⧸ N := QuotientGroup.mk' N
  have hmk7 : Function.Bijective mk7 := by
    refine ⟨fun a b h => ?_, QuotientGroup.mk'_surjective N⟩
    have h1 : a⁻¹ * b ∈ N := QuotientGroup.eq.1 h
    rw [hNb] at h1
    exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 h1)
  let e := MulEquiv.ofBijective mk7 hmk7
  have he : ∀ x, e x = mk7 x := fun _ => rfl
  let gU : ↥U →* ↥U := (g.toMonoidHom.comp U.subtype).codRestrict U fun u => hgU u u.2
  have hker : β.ker ≤ (β.comp gU).ker := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv ⊢
    rw [MonoidHom.comp_apply, hβk]
    exact (hgZ v v.2).2 ((hβk v).1 hv)
  let F'' := β.liftOfSurjective hβs ⟨β.comp gU, hker⟩
  have hF'' : ∀ v : ↥U, F'' (β v) = β (gU v) := fun v =>
    MonoidHom.liftOfRightInverse_comp_apply β _ _ ⟨β.comp gU, hker⟩ v
  let ψ : ↥(G6.coreMod 7) →* ↥(G6.coreMod 7) :=
    ((G6.permAct 7 σ⁻¹).toMonoidHom.comp (G6.coreMod 7).subtype).codRestrict _
      fun x => G6.permAct_mem_coreMod σ⁻¹ x.2
  have hψ : ∀ x, (ψ x : G6.PermMod 7) = G6.permAct 7 σ⁻¹ x := fun _ => rfl
  let F' : ↥(G6.coreMod 7) →* ↥(G6.coreMod 7) := ψ.comp (e.symm.toMonoidHom.comp (F''.comp mk7))
  have hF' : ∀ (x : ↥(G6.coreMod 7)) (v : ↥U), β v = mk7 x → F' x = ψ (e.symm (β (gU v))) := by
    intro x v hv
    show ψ (e.symm (F'' (mk7 x))) = _
    rw [← hv, hF'']
  have hinj : Function.Injective F' := by
    refine (injective_iff_map_eq_one F').2 fun x hx => ?_
    obtain ⟨v, hv⟩ := hβs (mk7 x)
    rw [hF' x v hv] at hx
    have h1 : e.symm (β (gU v)) = 1 := by
      have h0 : ψ (e.symm (β (gU v))) = 1 := hx
      apply Subtype.ext
      exact (G6.permAct 7 σ⁻¹).map_eq_one_iff.1 (congrArg Subtype.val h0)
    rw [MulEquiv.map_eq_one_iff, hβk] at h1
    have h2 : (v : E) ∈ Z := (hgZ v v.2).1 h1
    rw [← hβk] at h2
    rw [h2] at hv
    exact hmk7.1 (hv.symm.trans (map_one mk7).symm)
  have hequiv : ∀ τ ∈ alternatingGroup (Fin 7), ∀ x : ↥(G6.coreMod 7),
      (F' ⟨G6.permAct 7 τ x, G6.permAct_mem_coreMod τ x.2⟩ : G6.PermMod 7) =
        G6.permAct 7 τ (F' x) := by
    intro τ hτ x
    obtain ⟨v, hv⟩ := hβs (mk7 x)
    let γ : ↥(alternatingGroup (Fin 7)) := ⟨τ, hτ⟩
    let γ' : ↥(alternatingGroup (Fin 7)) :=
      ⟨σ * τ * σ⁻¹, (alternatingGroup.normal).conj_mem τ hτ σ⟩
    have h1 : β ⟨((π γ : ↥Λ) : MulAut E) v, hΛU (π γ) v v.2⟩ =
        mk7 ⟨G6.permAct 7 τ x, G6.permAct_mem_coreMod τ x.2⟩ :=
      hβe γ v x (hΛU (π γ) v v.2) (G6.permAct_mem_coreMod τ x.2) hv
    set m' := e.symm (β (gU v)) with hm'
    have hm'' : β (gU v) = QuotientGroup.mk m' := (e.apply_symm_apply _).symm
    have h2 : β ⟨((π γ' : ↥Λ) : MulAut E) (gU v), hΛU (π γ') _ (gU v).2⟩ =
        mk7 ⟨G6.permAct 7 (σ * τ * σ⁻¹) m', G6.permAct_mem_coreMod (σ * τ * σ⁻¹) m'.2⟩ :=
      hβe γ' (gU v) m' (hΛU (π γ') _ (gU v).2)
        (G6.permAct_mem_coreMod (σ * τ * σ⁻¹) m'.2) hm''
    have h3 : gU ⟨((π γ : ↥Λ) : MulAut E) v, hΛU (π γ) v v.2⟩ =
        ⟨((π γ' : ↥Λ) : MulAut E) (gU v), hΛU (π γ') _ (gU v).2⟩ :=
      Subtype.ext (hc γ γ' rfl v)
    rw [hF' _ ⟨((π γ : ↥Λ) : MulAut E) v, hΛU (π γ) v v.2⟩ h1, hF' x v hv, h3, h2]
    have h4 : e.symm (mk7 ⟨G6.permAct 7 (σ * τ * σ⁻¹) m',
        G6.permAct_mem_coreMod (σ * τ * σ⁻¹) m'.2⟩) =
        ⟨G6.permAct 7 (σ * τ * σ⁻¹) m', G6.permAct_mem_coreMod (σ * τ * σ⁻¹) m'.2⟩ :=
      e.symm_apply_apply _
    rw [h4, hψ, hψ, ← hm', ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  have hS := B45Alt7.schur_coreMod F' hinj hequiv m
  rw [hF' m u hm] at hS
  have h5 : (e.symm (β (gU u)) : G6.PermMod 7) = G6.permAct 7 σ m := by
    rw [← hS, hψ, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have h6 : e.symm (β (gU u)) = ⟨G6.permAct 7 σ m, G6.permAct_mem_coreMod σ m.2⟩ :=
    Subtype.ext h5
  show β (gU u) = _
  rw [← e.apply_symm_apply (β (gU u)), h6]
  rfl

end A7F

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem exists_perm7 [IsMulCommutative ↥(conjClosure S.V3 H)]
    (hs : S.SecHyp H K (conjClosure S.V3 H) (fsuV1 T V))
    {π : (FFModel.altDn 7).Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    {β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →*
      ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 7)
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β) :
    ∃ ρ : ↥H →* Perm (Fin 7), (∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) ∧
      ∀ (h : ↥H) (u : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))))
        (m : ↥(G6.coreMod 7)) (hu : hs.act h u ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))),
        β u = QuotientGroup.mk m →
        β ⟨hs.act h u, hu⟩ =
          QuotientGroup.mk ⟨G6.permAct 7 (ρ h) m, G6.permAct_mem_coreMod (ρ h) m.2⟩ := by
  classical
  have hcomm : commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊤ := hd.commV_autSec_eq_top
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num))
      ((CFSG.Quasithin.H.Mathieu.realizesVia_iff _ _ _ _ _).2 ⟨β, hR⟩)
  let πe : (FFModel.altDn 7).Gam ≃* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    MulEquiv.ofBijective π ⟨hinj, hR.1⟩
  let rV : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    (hs.act.comp (Subgroup.inclusion hd.hKH)).codRestrict _ fun k =>
      (hs.mem_autSec_iff hd.hKH).2 ⟨_, k.2, rfl⟩
  let α : ↥K →* alternatingGroup (Fin 7) := πe.symm.toMonoidHom.comp rV
  have hrVs : Function.Surjective rV := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hd.hKH).1 hψ
    exact ⟨⟨f, hf⟩, rfl⟩
  have hαs : Function.Surjective α := πe.symm.surjective.comp hrVs
  have hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H := fun k => by
    show πe.symm (rV k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← Subtype.coe_inj]
    exact hs.act_eq_one_iff _
  have hπα : ∀ k : ↥K, ((π (α k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) =
      hs.act ⟨k, hd.hKH k.2⟩ := fun k => by
    have : π (α k) = rV k := πe.apply_symm_apply (rV k)
    rw [this]
    rfl
  obtain ⟨ρ, hρc, -, hρ1⟩ := hd.exists_rho7 hαs hαk
  refine ⟨ρ, hρ1, fun h u m hu hm => ?_⟩
  have hgU : ∀ v ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))),
      hs.act h v ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := fun v _ => hcomm ▸ Subgroup.mem_top _
  have hfix : ∀ v, hs.act h v ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ↔
      v ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
    intro v
    simp only [mem_fixV]
    constructor
    · intro hv ψ hψ
      obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hd.hKH).1 hψ
      have hf' : ((h * f * h⁻¹ : ↥H) : G) ∈ K := hd.conj_mem h ⟨f, hf⟩
      have h1 := hv _ ((hs.mem_autSec_iff hd.hKH).2 ⟨h * f * h⁻¹, hf', rfl⟩)
      simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self] at h1
      exact (hs.act h).injective h1
    · intro hv ψ hψ
      obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hd.hKH).1 hψ
      have hf' : ((h⁻¹ * f * h : ↥H) : G) ∈ K := by
        have := hd.conj_mem h⁻¹ ⟨f, hf⟩
        simpa using this
      have h1 := hv _ ((hs.mem_autSec_iff hd.hKH).2 ⟨h⁻¹ * f * h, hf', rfl⟩)
      simp only [map_mul, map_inv, MulAut.mul_apply] at h1
      have h2 := congrArg (hs.act h) h1
      rwa [MulAut.apply_inv_self] at h2
  have hgZ : ∀ v ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))),
      hs.act h v ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
      commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ↔
        v ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
      commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
    intro v hv
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hfix]
    exact and_congr_right fun _ => ⟨fun _ => hv, fun _ => hgU v hv⟩
  have hc : ∀ γ γ' : ↥(alternatingGroup (Fin 7)), (γ' : Perm (Fin 7)) = ρ h * γ * (ρ h)⁻¹ →
      ∀ e, hs.act h ((π γ : MulAut _) e) = (π γ' : MulAut _) (hs.act h e) := by
    intro γ γ' hγ' e
    obtain ⟨k, rfl⟩ := hαs γ
    have h1 : γ' = α ⟨(h : G) * k * (h : G)⁻¹, hd.conj_mem h k⟩ :=
      Subtype.ext (by rw [hγ', hρc])
    rw [h1, hπα, hπα]
    have h2 : (⟨(h : G) * k * (h : G)⁻¹, hd.hKH (hd.conj_mem h k)⟩ : ↥H) =
        h * ⟨k, hd.hKH k.2⟩ * h⁻¹ := rfl
    rw [h2]
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self]
  exact A7F.act_eq_perm hR hgU hgZ hc u m hm

end DK

end Setting4

end CFSG.Quasithin.H13.A6

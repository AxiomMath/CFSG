module

public import CFSG.Quasithin.H13.AS91Sec4SevenN

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_conj_smul {g x : G} {Y : Subgroup G} : x ∈ MulAut.conj g • Y ↔ g⁻¹ * x * g ∈ Y := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
    inv_inv]

theorem card_conj_smul (g : G) (Y : Subgroup G) : Nat.card ↥(MulAut.conj g • Y) = Nat.card Y :=
  (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) Y).toEquiv).symm

theorem conj_smul_eq_of_le {g : G} {Y Y' : Subgroup G} (hle : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y')
    (hc : Nat.card Y = Nat.card Y') : MulAut.conj g • Y = Y' := by
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_conj_smul, hc])
  have := hle _ (mem_conj_smul.mp hx)
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this

namespace Data41

variable {z : G} {h : HypJ4 G z} (D : Data41 h)

section Y

@[expose] noncomputable def Ysub (i : Fin 3) : Subgroup G :=
  D.E ⊓ pre h.setting ((Two.fGrp i).comap D.Φo)

theorem Ysub_le_E (i : Fin 3) : D.Ysub i ≤ D.E := inf_le_left

theorem mem_Ysub_iff {i : Fin 3} {x : G} (hx : x ∈ D.E) :
    x ∈ D.Ysub i ↔ D.Φo (h.setting.ρ ⟨x, D.E_le_M hx⟩) ∈ Two.fGrp i :=
  ⟨fun h1 => rho_mem_of_mem_pre h1.2 _, fun h1 => ⟨hx, mem_pre_of_rho ⟨x, D.E_le_M hx⟩ h1⟩⟩

end Y

section YModel

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem card_Ysub (i : Fin 3) : Nat.card (D.Ysub i) = 2 ^ 10 := by
  have h1 := D.card_of_image (X := D.Ysub i) (Y := Two.fGrp i) (D.Ysub_le_E i)
    (fun x hx => ⟨D.E1_le_E hx, QG_le_pre _ (D.E1_le_QG hx)⟩)
    (fun x hx => rho_mem_of_mem_pre hx.2 _)
    (fun U hU => by
      obtain ⟨s, hsE, hsU⟩ := D.exists_mem_E hOut hTw (Two.fGrp_le_eb i hU)
      refine ⟨s, (D.mem_Ysub_iff hsE).mpr ?_, hsU⟩
      show D.Φo (h.setting.ρ s) ∈ Two.fGrp i
      rw [hsU]
      exact hU)
  rw [h1, Two.card_fGrp]
  norm_num

theorem Ysub_injective : Function.Injective D.Ysub := by
  intro i j hij
  by_contra hne
  obtain ⟨s, hsE, hsU⟩ := D.exists_mem_E hOut hTw (Two.fGrp_le_eb i (Two.fElt_mem i))
  have hs : (s : G) ∈ D.Ysub i := (D.mem_Ysub_iff hsE).mpr (by
    show D.Φo (h.setting.ρ s) ∈ _
    rw [hsU]
    exact Two.fElt_mem i)
  rw [hij] at hs
  have h1 := (D.mem_Ysub_iff hsE).mp hs
  rw [show D.Φo (h.setting.ρ ⟨(s : G), D.E_le_M hsE⟩) = D.Φo (h.setting.ρ s) from rfl, hsU] at h1
  exact Two.fElt_not_mem hne h1

end YModel

section SevenC

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3)
  {s₀ : h.setting.M} (hs₀ : D.Φo (h.setting.ρ s₀) = Two.tE) (hHat : HatM22SmallModules)

include hOut hTw hg₁ hs₀ hHat

theorem conj_mem_Ysub_of_K {k : G} (hk : k ∈ Kgrp (h := h) g₁ s₀) {i : Fin 3} {y : G}
    (hy : y ∈ D.Ysub i) : k * y * k⁻¹ ∈ D.Ysub i := by
  have hyE := D.Ysub_le_E i hy
  have hkyE := D.conj_mem_E_of_K hOut hTw hg₁ hs₀ hHat hk hyE
  have hc := D.commutator_mem_Bgrp hOut hTw hg₁ hs₀ hk (D.E_le_S hOut hTw hg₁ hs₀ hyE)
  have hcE : k * y * k⁻¹ * y⁻¹ ∈ D.E := mul_mem hkyE (inv_mem hyE)
  have hcF : D.Φo (h.setting.ρ ⟨_, D.E_le_M hcE⟩) ∈ Two.fGrp i := by
    refine Two.iGrp_le_fGrp i ?_
    rw [← Two.eb_inf_p2]
    exact ⟨D.Φo_mem_eb hOut hTw hcE _, rho_mem_of_mem_pre hc.2 _⟩
  refine (D.mem_Ysub_iff hkyE).mpr ?_
  have e : (⟨k * y * k⁻¹, D.E_le_M hkyE⟩ : h.setting.M) =
      ⟨_, D.E_le_M hcE⟩ * ⟨y, D.E_le_M hyE⟩ :=
    Subtype.ext (show k * y * k⁻¹ = k * y * k⁻¹ * y⁻¹ * y by group)
  rw [e, map_mul, map_mul]
  exact mul_mem hcF ((D.mem_Ysub_iff hyE).mp hy)

omit hHat in
theorem exists_conj_Ysub_of_S {s : G}
    (hs : s ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13) (i : Fin 3) :
    ∃ j : Fin 3, ∀ y ∈ D.Ysub i, s * y * s⁻¹ ∈ D.Ysub j := by
  have hsM := D.hSM hOut hTw hg₁ hs₀ hs.1
  have hU : D.Φo (h.setting.ρ ⟨s, hsM⟩) ∈ Two.gZGrp := by
    rw [Two.gZGrp_eq_gammaZ (D.stabIn_three hOut hTw)]
    exact D.Φo_mem_gammaZ hOut hTw hg₁ hs₀ hs.1 hsM
  have hW : ⇑(D.Φo (h.setting.ρ ⟨s, hsM⟩)) '' Two.W1 = Two.W1 :=
    (Two.mem_g13Grp.mp (rho_mem_of_mem_pre hs.2 hsM)).2
  obtain ⟨j, hj⟩ := (Two.conj_fGrp hU hW).1 i
  refine ⟨j, fun y hy => ?_⟩
  have hyE := D.Ysub_le_E i hy
  have hsyE := D.conj_mem_E hs.2 hyE
  refine (D.mem_Ysub_iff hsyE).mpr ?_
  have e : (⟨s * y * s⁻¹, D.E_le_M hsyE⟩ : h.setting.M) =
      ⟨s, hsM⟩ * ⟨y, D.E_le_M hyE⟩ * (⟨s, hsM⟩ : h.setting.M)⁻¹ := Subtype.ext rfl
  rw [e]
  simp only [map_mul, map_inv]
  exact hj _ ((D.mem_Ysub_iff hyE).mp hy)

theorem exists_conj_Ysub {g : G}
    (hg : g ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G)) (i : Fin 3) :
    ∃ j : Fin 3, MulAut.conj g • D.Ysub i = D.Ysub j := by
  obtain ⟨k, hk, s, hs, rfl⟩ := D.exists_mul_of_mem_G12 hOut hTw hg₁ hs₀ hHat hg
  obtain ⟨j, hj⟩ := D.exists_conj_Ysub_of_S hOut hTw hg₁ hs₀ hs i
  refine ⟨j, conj_smul_eq_of_le (fun y hy => ?_)
    (by rw [D.card_Ysub hOut hTw, D.card_Ysub hOut hTw])⟩
  have := D.conj_mem_Ysub_of_K hOut hTw hg₁ hs₀ hHat hk (hj y hy)
  rwa [show k * (s * y * s⁻¹) * k⁻¹ = k * s * y * (k * s)⁻¹ by group] at this

@[expose] noncomputable def yAction : SubMulAction
    ↥((normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G)).map MulAut.conj)
    (Subgroup G) where
  carrier := Set.range D.Ysub
  smul_mem' c Y hY := by
    obtain ⟨i, rfl⟩ := hY
    obtain ⟨g, hg, hgc⟩ := Subgroup.mem_map.mp c.2
    obtain ⟨j, hj⟩ := D.exists_conj_Ysub hOut hTw hg₁ hs₀ hHat hg i
    refine ⟨j, ?_⟩
    show D.Ysub j = (c : MulAut G) • D.Ysub i
    rw [← hgc, hj]

instance : Finite ↥(D.yAction hOut hTw hg₁ hs₀ hHat) :=
  (Set.finite_range D.Ysub).to_subtype

theorem card_yAction : Nat.card ↥(D.yAction hOut hTw hg₁ hs₀ hHat) = 3 := by
  have h1 : Nat.card (Set.range D.Ysub) = 3 := by
    rw [Nat.card_range_of_injective (D.Ysub_injective hOut hTw), Nat.card_fin]
  exact h1

@[expose] noncomputable def psiY :
    ↥(normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G)) →*
      Equiv.Perm (Fin 3) :=
  ((Finite.equivFinOfCardEq (D.card_yAction hOut hTw hg₁ hs₀ hHat)).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom _ ↥(D.yAction hOut hTw hg₁ hs₀ hHat))).comp
      (MulAut.conj.subgroupMap _)

theorem psiY_eq_one_iff
    (g : ↥(normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G))) :
    D.psiY hOut hTw hg₁ hs₀ hHat g = 1 ↔ ∀ i, MulAut.conj (g : G) • D.Ysub i = D.Ysub i := by
  rw [psiY, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]
  constructor
  · intro h1 i
    have := congrArg (fun σ : Equiv.Perm ↥(D.yAction hOut hTw hg₁ hs₀ hHat) =>
      ((σ ⟨D.Ysub i, i, rfl⟩ : ↥(D.yAction hOut hTw hg₁ hs₀ hHat)) : Subgroup G)) h1
    exact this
  · intro h1
    ext ⟨Y, i, rfl⟩ : 1
    exact Subtype.ext (h1 i)

theorem psiY_K {g : ↥(normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G))}
    (hg : (g : G) ∈ Kgrp (h := h) g₁ s₀) : D.psiY hOut hTw hg₁ hs₀ hHat g = 1 :=
  (D.psiY_eq_one_iff hOut hTw hg₁ hs₀ hHat g).mpr fun _ =>
    conj_smul_eq_of_le (fun _ hy => D.conj_mem_Ysub_of_K hOut hTw hg₁ hs₀ hHat hg hy) rfl

theorem mem_RE_of {g : G}
    (hg : g ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G))
    (hgS : g ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G))
    (hY : ∀ i, MulAut.conj g • D.Ysub i = D.Ysub i) : g ∈ D.Bgrp g₁ s₀ ⊔ D.E := by
  have hgM := D.hSM hOut hTw hg₁ hs₀ hgS
  have hgG := (D.mem_normalizer_E_iff hOut hTw hgM).mp hg.2
  have hU : D.Φo (h.setting.ρ ⟨g, hgM⟩) ∈ Two.gZGrp := by
    rw [Two.gZGrp_eq_gammaZ (D.stabIn_three hOut hTw)]
    exact D.Φo_mem_gammaZ hOut hTw hg₁ hs₀ hgS hgM
  have hW : ⇑(D.Φo (h.setting.ρ ⟨g, hgM⟩)) '' Two.W1 = Two.W1 :=
    (Two.mem_g13Grp.mp (rho_mem_of_mem_pre hgG hgM)).2
  have hn : ∀ i : Fin 3, ∀ f ∈ Two.fGrp i,
      D.Φo (h.setting.ρ ⟨g, hgM⟩) * f * (D.Φo (h.setting.ρ ⟨g, hgM⟩))⁻¹ ∈ Two.fGrp i := by
    intro i f hf
    obtain ⟨s, hsE, hsU⟩ := D.exists_mem_E hOut hTw (Two.fGrp_le_eb i hf)
    have hsF : D.Φo (h.setting.ρ ⟨(s : G), D.E_le_M hsE⟩) ∈ Two.fGrp i := by
      have e0 : (⟨(s : G), D.E_le_M hsE⟩ : h.setting.M) = s := rfl
      rw [e0, hsU]
      exact hf
    have hsY : (s : G) ∈ D.Ysub i := (D.mem_Ysub_iff hsE).mpr hsF
    have hgsE := D.conj_mem_E hgG hsE
    have hgsY : g * s * g⁻¹ ∈ D.Ysub i := by
      have h2 : g * s * g⁻¹ ∈ MulAut.conj g • D.Ysub i := by
        rw [mem_conj_smul, show g⁻¹ * (g * s * g⁻¹) * g = s by group]
        exact hsY
      rwa [hY i] at h2
    have h1 := (D.mem_Ysub_iff hgsE).mp hgsY
    have e : (⟨g * s * g⁻¹, D.E_le_M hgsE⟩ : h.setting.M) =
        ⟨g, hgM⟩ * s * (⟨g, hgM⟩ : h.setting.M)⁻¹ := Subtype.ext rfl
    rw [e] at h1
    simp only [map_mul, map_inv] at h1
    rwa [hsU] at h1
  obtain ⟨p, hp, ε, hε, hpε⟩ := (Two.conj_fGrp hU hW).2 hn
  obtain ⟨e, heE, heε⟩ := D.exists_mem_E hOut hTw hε
  have heS := D.E_le_S hOut hTw hg₁ hs₀ heE
  have hρp : D.Φo (h.setting.ρ (⟨g, hgM⟩ * e⁻¹)) ∈ Two.p2Grp := by
    simp only [map_mul, map_inv]
    rw [heε, hpε, mul_inv_cancel_right]
    exact hp
  have hgeR : ((⟨g, hgM⟩ * e⁻¹ : h.setting.M) : G) ∈ D.Bgrp g₁ s₀ := by
    refine Subgroup.mem_inf.mpr ⟨?_, mem_pre_of_rho (⟨g, hgM⟩ * e⁻¹) hρp⟩
    show g * (e : G)⁻¹ ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G)
    exact mul_mem hgS (inv_mem heS)
  have hmem := mul_mem (mem_sup_left hgeR : _ ∈ D.Bgrp g₁ s₀ ⊔ D.E) (mem_sup_right heE)
  have e1 : ((⟨g, hgM⟩ * e⁻¹ : h.setting.M) : G) * (e : G) = g := by
    show g * (e : G)⁻¹ * e = g
    group
  rwa [e1] at hmem

theorem of_mem_RE {g : G} (hg : g ∈ D.Bgrp g₁ s₀ ⊔ D.E) :
    g ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) ∧ ∀ i, MulAut.conj g • D.Ysub i = D.Ysub i := by
  let H₀ : Subgroup G := centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓
    ⨅ i : Fin 3, (MulAction.stabilizer (MulAut G) (D.Ysub i)).comap MulAut.conj
  have hmem : ∀ x, x ∈ H₀ ↔ x ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) ∧
      ∀ i, MulAut.conj x • D.Ysub i = D.Ysub i := by
    intro x
    simp only [H₀, mem_inf, mem_iInf, mem_comap, MulAction.mem_stabilizer_iff]
  have hB : D.Bgrp g₁ s₀ ≤ H₀ := fun b hb => (hmem b).mpr
    ⟨D.Bgrp_le_centralizer hOut hTw hg₁ hs₀ hb, fun _ => conj_smul_eq_of_le (fun _ hy =>
      D.conj_mem_Ysub_of_K hOut hTw hg₁ hs₀ hHat (D.Bgrp_le_Kgrp hOut hTw hg₁ hs₀ hb) hy) rfl⟩
  have hE : D.E ≤ H₀ := by
    intro e he
    refine (hmem e).mpr ⟨D.E_le_S hOut hTw hg₁ hs₀ he, fun i => conj_smul_eq_of_le
      (fun y hy => ?_) rfl⟩
    rw [D.E_comm hOut hTw hHat he (D.Ysub_le_E i hy), mul_inv_cancel_right]
    exact hy
  exact (hmem g).mp (sup_le hB hE hg)

theorem mem_RE_iff {g : G}
    (hg : g ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G)) :
    (g ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) ∧
      ∀ i, MulAut.conj g • D.Ysub i = D.Ysub i) ↔ g ∈ D.Bgrp g₁ s₀ ⊔ D.E :=
  ⟨fun h1 => D.mem_RE_of hOut hTw hg₁ hs₀ hHat hg h1.1 h1.2,
    D.of_mem_RE hOut hTw hg₁ hs₀ hHat⟩

theorem psiY_surjective (σ : Equiv.Perm (Fin 3)) :
    ∃ s ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13,
      ∃ hs : s ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G),
        D.psiY hOut hTw hg₁ hs₀ hHat ⟨s, hs⟩ = σ := by
  have hle : centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13 ≤
      normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G) :=
    le_inf (inf_le_left.trans (centralizer_le_normalizer _)) fun g hg =>
      (D.mem_normalizer_E_iff hOut hTw (pre_le_M _ hg.2)).mpr hg.2
  let f := (D.psiY hOut hTw hg₁ hs₀ hHat).comp (Subgroup.inclusion hle)
  have hRE : D.Bgrp g₁ s₀ ⊔ D.E ≤ centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13 :=
    sup_le (le_inf (D.Bgrp_le_centralizer hOut hTw hg₁ hs₀) D.Bgrp_le_G13)
      (le_inf (D.E_le_S hOut hTw hg₁ hs₀) (D.E_le_G13 hOut hTw))
  have hker : f.ker = (D.Bgrp g₁ s₀ ⊔ D.E).subgroupOf
      (centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.comp_apply, D.psiY_eq_one_iff,
      ← D.mem_RE_iff hOut hTw hg₁ hs₀ hHat (hle x.2)]
    exact ⟨fun h1 => ⟨x.2.1, h1⟩, fun h1 => h1.2⟩
  have hcS : Nat.card ↥(centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13) = 2 ^ 11 * 384 := by
    have c3 := Subgroup.card_mul_index
      (D.G13.subgroupOf (centralizer (Zinf (h := h) g₁ s₀ : Set G)))
    rw [D.index_G13_S hOut hTw hg₁ hs₀, card_subgroupOf_eq,
      D.card_centralizer_Zinf hOut hTw hg₁ hs₀] at c3
    norm_num at c3 ⊢
    omega
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker, card_subgroupOf_eq, inf_of_le_right hRE,
    D.card_R_sup_E hOut hTw hg₁ hs₀, hcS] at h1
  have h6 : Nat.card f.range = Nat.card (Equiv.Perm (Fin 3)) := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num at h1 ⊢
    omega
  obtain ⟨x, hx⟩ := (MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ h6)) σ
  exact ⟨x, x.2, hle x.2, hx⟩

theorem G12_quot : ∃ φ : ↥(normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G)) →*
    GL (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3), Function.Surjective φ ∧
      φ.ker = (Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊔ D.E).subgroupOf
        (normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G)) := by
  obtain ⟨θ, hθs, hθk⟩ := D.exists_theta hOut hTw hg₁ hs₀
  have hθ1 : ∀ n : ↥(normalizer (Zinf (h := h) g₁ s₀ : Set G)),
      θ n = 1 ↔ (n : G) ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) := fun n => by
    rw [← MonoidHom.mem_ker, hθk, mem_subgroupOf]
  let θ' := θ.comp (Subgroup.inclusion (inf_le_left :
    normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G) ≤
      normalizer (Zinf (h := h) g₁ s₀ : Set G)))
  refine ⟨θ'.prod (D.psiY hOut hTw hg₁ hs₀ hHat), ?_, ?_⟩
  · rintro ⟨a, σ⟩
    obtain ⟨n, hn⟩ := hθs a
    have hSK : centralizer (Zinf (h := h) g₁ s₀ : Set G) ≤
        normalizer (Kgrp (h := h) g₁ s₀ : Set G) := fun _ hs =>
      mem_normalizer_fintype fun _ hk =>
        conj_mem_Kgrp (h := h) (centralizer_le_normalizer _ hs) hk
    have hnN : (n : G) ∈ Kgrp (h := h) g₁ s₀ ⊔ centralizer (Zinf (h := h) g₁ s₀ : Set G) := by
      rw [← (D.K_facts hOut hTw hg₁ hs₀).1]
      exact n.2
    obtain ⟨k, hk, s', hs', hks'⟩ := exists_mul_of_mem_sup hSK hnN
    have hkN := D.Kgrp_le_normalizer hOut hTw hg₁ hs₀ hk
    have hkG : k ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G) :=
      ⟨hkN, D.K_le_normalizer_E hOut hTw hg₁ hs₀ hHat hk⟩
    have hθk' : θ ⟨k, hkN⟩ = a := by
      have e : n = ⟨k, hkN⟩ * ⟨s', centralizer_le_normalizer _ hs'⟩ := Subtype.ext hks'.symm
      rw [← hn, e, map_mul, (hθ1 ⟨s', centralizer_le_normalizer _ hs'⟩).mpr hs', mul_one]
    obtain ⟨s, hsSG, hsG, hsσ⟩ := D.psiY_surjective hOut hTw hg₁ hs₀ hHat σ
    refine ⟨⟨k, hkG⟩ * ⟨s, hsG⟩, ?_⟩
    rw [MonoidHom.prod_apply, map_mul, map_mul,
      D.psiY_K hOut hTw hg₁ hs₀ hHat (g := ⟨k, hkG⟩) hk, one_mul, hsσ]
    congr 1
    show θ ⟨k, hkN⟩ * θ ⟨s, hsG.1⟩ = a
    rw [(hθ1 ⟨s, hsG.1⟩).mpr hsSG.1, mul_one, hθk']
  · ext g
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one, mem_subgroupOf,
      D.Kgrp_inf_eq_Bgrp hOut hTw hg₁ hs₀, D.psiY_eq_one_iff,
      ← D.mem_RE_iff hOut hTw hg₁ hs₀ hHat g.2]
    have : θ' g = 1 ↔ (g : G) ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) := hθ1 _
    rw [this]

end SevenC

@[expose] noncomputable def toLoc47
    (hHat : HatM22SmallModules) (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) : Loc47 G z where
  toLoc46 := D.toLoc46 hHat hOut hTw
  G12 := normalizer (Zinf (h := h) (D.exists_g₁ hOut hTw).choose (D.exists_s₀ hOut hTw).choose :
    Set G) ⊓ normalizer (D.E : Set G)
  G12_eq := rfl
  K_le := le_inf (D.Kgrp_le_normalizer hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec) (D.K_le_normalizer_E hOut hTw
      (D.exists_g₁ hOut hTw).choose_spec (D.exists_s₀ hOut hTw).choose_spec hHat)
  relIndex_G12 := D.relIndex_G12 hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec hHat
  card_RE := by
    show Nat.card ↥(Kgrp (h := h) (D.exists_g₁ hOut hTw).choose (D.exists_s₀ hOut hTw).choose ⊓
      centralizer (Zinf (h := h) (D.exists_g₁ hOut hTw).choose (D.exists_s₀ hOut hTw).choose :
        Set G) ⊔ D.E) = 2 ^ 17
    rw [D.Kgrp_inf_eq_Bgrp hOut hTw (D.exists_g₁ hOut hTw).choose_spec
      (D.exists_s₀ hOut hTw).choose_spec]
    exact D.card_R_sup_E hOut hTw (D.exists_g₁ hOut hTw).choose_spec
      (D.exists_s₀ hOut hTw).choose_spec
  G12_quot := D.G12_quot hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec hHat

end Data41

end CFSG.Quasithin.H13.AS91

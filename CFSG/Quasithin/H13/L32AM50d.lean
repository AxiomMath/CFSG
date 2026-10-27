module

public import CFSG.Quasithin.H13.L32AM50c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open Equiv Equiv.Perm
open scoped IsMulCommutative

@[expose] def Core7.v01 : G6.PermMod 7 := Multiplicative.ofAdd (Pi.single 0 1 + Pi.single 1 1)

theorem Core7.fixed_facts : ∀ w : G6.PermMod 7, ∑ i, Multiplicative.toAdd w i = 0 →
    G6.permAct 7 (swap 2 4 * swap 2 3) w = w →
    G6.permAct 7 (swap 2 6 * swap 2 5 * swap 2 4 * swap 2 3) w = w →
    G6.permAct 7 (swap 0 1 * swap 2 3) w = w → w = 1 ∨ w = Core7.v01 := by
  decide +kernel

theorem Core7.v01_facts :
    (swap (2 : Fin 7) 4 * swap 2 3) ∈ alternatingGroup (Fin 7) ∧
    (swap (2 : Fin 7) 6 * swap 2 5 * swap 2 4 * swap 2 3) ∈ alternatingGroup (Fin 7) ∧
    (swap (0 : Fin 7) 1 * swap 2 3) ∈ alternatingGroup (Fin 7) ∧
    G6.permAct 7 (swap 2 4 * swap 2 3) Core7.v01 = Core7.v01 ∧
    G6.permAct 7 (swap 2 6 * swap 2 5 * swap 2 4 * swap 2 3) Core7.v01 = Core7.v01 ∧
    G6.permAct 7 (swap 0 1 * swap 2 3) Core7.v01 = Core7.v01 ∧
    ∑ i, Multiplicative.toAdd Core7.v01 i = 0 ∧ Core7.v01 ≠ 1 := by
  simp only [mem_alternatingGroup]
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top50

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 7)} (C : Top50 T L V H W K π)
  [IsMulCommutative ↥(conjClosure V H)]
include C

theorem iota_symm_eq {h : ↥H} (hh : π h ∈ alternatingGroup (Fin 7)) :
    ((C.iota.symm ⟨π h, hh⟩ : ↥C.autK) : MulAut (Hat V H W)) = C.act h := by
  have : C.iota ⟨C.act h, (C.act_mem_autK_iff h).2 hh⟩ = ⟨π h, hh⟩ :=
    Subtype.ext (C.emb_act h)
  rw [← this, MulEquiv.symm_apply_apply]

variable {β : Hat V H W ≃* ↥(G6.coreMod 7)}
  (hβ : ∀ (γ : B45Alt7.A7) (s : Hat V H W),
    (β ((C.iota.symm γ : MulAut (Hat V H W)) s) : G6.PermMod 7) =
      G6.permAct 7 (γ : Perm (Fin 7)) (β s))
include hβ

theorem beta_act_of_mem {h : ↥H} (hh : π h ∈ alternatingGroup (Fin 7)) (s : Hat V H W) :
    β (C.act h s) = G6.coreAct 7 (π h) (β s) := by
  apply Subtype.ext
  rw [G6.coreAct_coe, ← C.iota_symm_eq hh]
  exact hβ ⟨π h, hh⟩ s

theorem beta_act (hirr : C.IrrK) (h : ↥H) (s : Hat V H W) :
    β (C.act h s) = G6.coreAct 7 (π h) (β s) := by
  classical
  set σ := π h with hσ
  set φ : ↥(G6.coreMod 7) →* ↥(G6.coreMod 7) := β.toMonoidHom.comp ((C.act h).toMonoidHom.comp
    (β.symm.toMonoidHom.comp (G6.coreAct 7 σ⁻¹).toMonoidHom)) with hφdef
  have hφx : ∀ x, φ x = β (C.act h (β.symm (G6.coreAct 7 σ⁻¹ x))) := fun x => rfl
  have hφ : ∀ γ ∈ alternatingGroup (Fin 7), ∀ x,
      φ (G6.coreAct 7 γ x) = G6.coreAct 7 γ (φ x) := by
    intro γ hγ x
    have hγ' : σ⁻¹ * γ * σ ∈ alternatingGroup (Fin 7) := by
      have := (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem γ hγ σ⁻¹
      simpa using this
    obtain ⟨k, hk, hkγ⟩ := C.exists_pi_eq hγ'
    set k' : ↥H := ⟨k, C.hKH hk⟩ with hk'
    have hk'mem : π k' ∈ alternatingGroup (Fin 7) := hkγ ▸ hγ'
    have hhk : π (h * k' * h⁻¹) = γ := by
      rw [map_mul, map_mul, map_inv, hkγ, ← hσ]
      group
    have hhkm : π (h * k' * h⁻¹) ∈ alternatingGroup (Fin 7) := hhk ▸ hγ
    have e1 : G6.coreAct 7 σ⁻¹ (G6.coreAct 7 γ x) =
        G6.coreAct 7 (π k') (G6.coreAct 7 σ⁻¹ x) := by
      rw [hkγ, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    have e2 : ∀ y, β.symm (G6.coreAct 7 (π k') y) = C.act k' (β.symm y) := by
      intro y
      rw [MulEquiv.symm_apply_eq, C.beta_act_of_mem hβ hk'mem, MulEquiv.apply_symm_apply]
    have e3 : ∀ z, C.act h (C.act k' z) = C.act (h * k' * h⁻¹) (C.act h z) := by
      intro z
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [hφx, hφx, e1, e2, e3, C.beta_act_of_mem hβ hhkm, hhk]
  set F : Subgroup (Hat V H W) := MonoidHom.eqLocus (φ.comp β.toMonoidHom) β.toMonoidHom with hF
  have hmemF : ∀ s, s ∈ F ↔ φ (β s) = β s := fun s => Iff.rfl
  have hFinv : ∀ l ∈ C.autK, ∀ v ∈ F, l v ∈ F := by
    intro l hl v hv
    rw [hmemF] at hv ⊢
    set γ := C.iota ⟨l, hl⟩ with hγ
    have hl' : ((C.iota.symm γ : ↥C.autK) : MulAut (Hat V H W)) = l := by
      rw [hγ, MulEquiv.symm_apply_apply]
    have hb : β (l v) = G6.coreAct 7 (γ : Perm (Fin 7)) (β v) := by
      apply Subtype.ext
      rw [G6.coreAct_coe, ← hl']
      exact hβ γ v
    rw [hb, hφ _ γ.2, hv]
  obtain ⟨hg1, hg2, hg3, hf1, hf2, hf3, hv0, hv1⟩ := Core7.v01_facts
  set v0 : ↥(G6.coreMod 7) := ⟨Core7.v01, hv0⟩ with hv0def
  have hfix : ∀ g ∈ alternatingGroup (Fin 7), G6.permAct 7 g Core7.v01 = Core7.v01 →
      G6.permAct 7 g (φ v0 : G6.PermMod 7) = (φ v0 : G6.PermMod 7) := by
    intro g hg hgv
    have h1 : G6.coreAct 7 g v0 = v0 := Subtype.ext (by rw [G6.coreAct_coe]; exact hgv)
    rw [← G6.coreAct_coe, ← hφ g hg, h1]
  have hφv : φ v0 = v0 := by
    rcases Core7.fixed_facts _ (φ v0).2 (hfix _ hg1 hf1) (hfix _ hg2 hf2) (hfix _ hg3 hf3) with
      h0 | h0
    · exfalso
      have h1 : φ v0 = 1 := Subtype.ext h0
      have hinj : Function.Injective φ := by
        intro a b hab
        rw [hφx, hφx] at hab
        have := β.injective hab
        have := (C.act h).injective this
        have := β.symm.injective this
        exact (G6.coreAct 7 σ⁻¹).injective this
      have h2 : v0 = 1 := hinj (h1.trans (map_one φ).symm)
      exact hv1 (congrArg Subtype.val h2)
    · exact Subtype.ext h0
  have hFtop : F = ⊤ := by
    rcases hirr F hFinv with h0 | h0
    · exfalso
      have h1 : β.symm v0 ∈ F := by
        rw [hmemF, MulEquiv.apply_symm_apply]
        exact hφv
      rw [h0, Subgroup.mem_bot, MulEquiv.symm_apply_eq, map_one] at h1
      exact hv1 (congrArg Subtype.val h1)
    · exact h0
  have h1 : β.symm (G6.coreAct 7 σ (β s)) ∈ F := by rw [hFtop]; trivial
  rw [hmemF, MulEquiv.apply_symm_apply, hφx] at h1
  rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply,
    MulEquiv.symm_apply_apply] at h1

theorem case_six (hirr : C.IrrK) :
    ∃ β' : ↥(conjClosure V H) →* ↥(G6.coreMod 7), Function.Surjective β' ∧
      β'.ker = W.subgroupOf (conjClosure V H) ∧
      ∀ (h : ↥H) (x x' : ↥(conjClosure V H)), (x' : G) = h * x * (h : G)⁻¹ →
        β' x' = G6.coreAct 7 (π h) (β' x) := by
  refine ⟨β.toMonoidHom.comp (InternalSec.secMk (W.subgroupOf (conjClosure V H))), ?_, ?_, ?_⟩
  · exact β.surjective.comp (InternalSec.secMk_surjective _)
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, A6.A6Mod.secMk_eq_one_iff, Subgroup.mem_subgroupOf]
  · intro h x x' hx'
    have : InternalSec.secMk (W.subgroupOf (conjClosure V H)) x' =
        C.act h (InternalSec.secMk (W.subgroupOf (conjClosure V H)) x) := by
      rw [C.act_secMk]
      congr 1
      exact Subtype.ext (by rw [Setup.rho_apply_coe, hx'])
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this,
      C.beta_act hβ hirr]

end Top50

end CFSG.Quasithin.H13.L32A.C

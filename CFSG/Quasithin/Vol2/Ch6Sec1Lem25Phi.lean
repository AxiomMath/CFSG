module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

section General

variable (X : Type*) [Group X]

@[expose] noncomputable def autQuotHom (N : Subgroup X) [N.Normal] [N.Characteristic] :
    MulAut X →* MulAut (X ⧸ N) where
  toFun α := QuotientGroup.congr N N α (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rfl
  map_mul' α β := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rfl

variable {X}

@[simp] theorem autQuotHom_mk (N : Subgroup X) [N.Normal] [N.Characteristic] (α : MulAut X)
    (x : X) : autQuotHom X N α (x : X ⧸ N) = ((α x : X) : X ⧸ N) := rfl

theorem commutatorElement_mul_center {Q : Type*} [Group Q] {z₁ z₂ : Q}
    (h₁ : z₁ ∈ Subgroup.center Q) (h₂ : z₂ ∈ Subgroup.center Q) (a b : Q) :
    ⁅z₁ * a, z₂ * b⁆ = ⁅a, b⁆ := by
  have c₁ : ∀ w : Q, z₁ * w * z₁⁻¹ = w := fun w => by
    rw [(Subgroup.mem_center_iff.mp h₁ w).symm]
    group
  have c₂ : ∀ w : Q, z₂ * w * z₂⁻¹ = w := fun w => by
    rw [(Subgroup.mem_center_iff.mp h₂ w).symm]
    group
  rw [commutatorElement_def, commutatorElement_def]
  calc z₁ * a * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹ =
      (z₁ * (a * (z₂ * b) * a⁻¹) * z₁⁻¹) * (z₂ * b)⁻¹ := by group
    _ = z₂ * (a * (z₂⁻¹ * (z₂ * b)) * a⁻¹ * b⁻¹) * z₂⁻¹ := by
        rw [c₁]
        have e : a * (z₂ * b) * a⁻¹ = z₂ * (a * b * a⁻¹) := by
          rw [← mul_assoc a z₂ b, Subgroup.mem_center_iff.mp h₂ a]
          group
        rw [e]
        group
    _ = a * b * a⁻¹ * b⁻¹ := by
        rw [c₂]
        group

theorem eq_one_of_mul_inv_mem_center {Q : Type*} [Group Q] (hQ : Group.IsPerfect Q)
    (β : MulAut Q) (hβ : ∀ q : Q, β q * q⁻¹ ∈ Subgroup.center Q) : β = 1 := by
  let F : Subgroup Q :=
    { carrier := {q | β q = q}
      mul_mem' := fun {a b} ha hb => by
        show β (a * b) = a * b
        rw [map_mul, show β a = a from ha, show β b = b from hb]
      one_mem' := map_one β
      inv_mem' := fun {a} ha => by
        show β a⁻¹ = a⁻¹
        rw [map_inv, show β a = a from ha] }
  have hF : (⊤ : Subgroup Q) ≤ F := by
    rw [← hQ.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show β ⁅a, b⁆ = ⁅a, b⁆
    have ea : β a = (β a * a⁻¹) * a := by group
    have eb : β b = (β b * b⁻¹) * b := by group
    rw [map_commutatorElement, ea, eb]
    exact commutatorElement_mul_center (hβ a) (hβ b) a b
  ext q
  exact hF (Subgroup.mem_top q)

end General

section KBar

variable {G : Type} [Group G]

abbrev KQ (K : Subgroup G) : Type := ↥K ⧸ CFSG.pCore 2 ↥K

abbrev KBar (K : Subgroup G) : Type := KQ K ⧸ Subgroup.center (KQ K)

@[expose] noncomputable def piK (K : Subgroup G) : ↥K →* KBar K :=
  (QuotientGroup.mk' (Subgroup.center (KQ K))).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))

theorem piK_surjective (K : Subgroup G) : Function.Surjective (piK K) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

@[expose] noncomputable def phiK (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (KBar K) :=
  (autQuotHom (KQ K) (Subgroup.center (KQ K))).comp
    ((autQuotHom ↥K (CFSG.pCore 2 ↥K)).comp K.normalizerMonoidHom)

theorem phiK_piK (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    phiK K g (piK K k) = piK K (K.normalizerMonoidHom g k) := rfl

theorem normalizerMonoidHom_coe (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G)))
    (k : ↥K) : ((K.normalizerMonoidHom g k : ↥K) : G) = g * k * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe K g k

theorem phiK_of_mem (K : Subgroup G) (k : ↥K) :
    phiK K ⟨k, Subgroup.le_normalizer k.2⟩ = MulAut.conj (piK K k) := by
  ext x
  obtain ⟨y, rfl⟩ := piK_surjective K x
  rw [phiK_piK, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem pCoreOf_two_eq_map_ch625 (K : Subgroup G) :
    pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype := CFSG.openPCoreOf_eq_map_pCore 2 K

theorem phiK_eq_one_iff {K : Subgroup G} (hQ : CFSG.IsQuasisimple (KQ K))
    (g : ↥(Subgroup.normalizer (K : Set G))) :
    phiK K g = 1 ↔ ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  set β := autQuotHom ↥K (CFSG.pCore 2 ↥K) (K.normalizerMonoidHom g) with hβ
  have hmk : ∀ k : ↥K, β (k : KQ K) = ((K.normalizerMonoidHom g k : ↥K) : KQ K) := fun k => rfl
  have key : β = 1 ↔ ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    rw [pCoreOf_two_eq_map_ch625]
    constructor
    · intro h1 k hk
      have h2 := congrArg (fun α : MulAut (KQ K) => α ((⟨k, hk⟩ : ↥K) : KQ K)) h1
      simp only [MulAut.one_apply] at h2
      rw [hmk, QuotientGroup.eq_iff_div_mem] at h2
      refine ⟨_, h2, ?_⟩
      simp [div_eq_mul_inv]
    · intro h1
      ext q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAut.one_apply, hmk, QuotientGroup.eq_iff_div_mem]
      obtain ⟨x, hx, hxk⟩ := h1 k k.2
      have : (K.normalizerMonoidHom g k : ↥K) / k = x := by
        apply Subtype.ext
        change _ = K.subtype x
        rw [hxk]
        simp [div_eq_mul_inv]
      rw [this]
      exact hx
  rw [← key]
  constructor
  · intro h1
    refine eq_one_of_mul_inv_mem_center hQ.1 β fun q => ?_
    have h2 := congrArg (fun α : MulAut (KBar K) => α (q : KBar K)) h1
    simp only [MulAut.one_apply] at h2
    change ((β q : KQ K) : KBar K) = (q : KBar K) at h2
    rw [QuotientGroup.eq_iff_div_mem] at h2
    simpa [div_eq_mul_inv] using h2
  · intro h1
    show autQuotHom (KQ K) (Subgroup.center (KQ K)) β = 1
    rw [h1, map_one]

theorem isSimpleGroup_KBar {K : Subgroup G} (hQ : CFSG.IsQuasisimple (KQ K)) :
    IsSimpleGroup (KBar K) ∧ ∃ a b : KBar K, a * b ≠ b * a :=
  ⟨hQ.2.1, hQ.2.2⟩

end KBar

end CFSG.Quasithin.H13

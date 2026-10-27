
module

public import CFSG.Monster.B.TwoA.Base.RankThreeBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.Lifts CFSG.Monster.VisCert

open CFSG.Monster.B.Co2 (v0)

theorem actD_alpha_31 : ∀ i : Fin 24, i.val < 23 →
    Co2.Native.actD 22 (Co2.genQuotMatrix i) 31 = 31 := by
  decide +kernel

theorem alphaN_mem_of {T : Subgroup OLq} (hT : ∀ i, Co2.alpha i ∈ T) (j : ℕ) :
    Co2.alphaN j ∈ T := by
  unfold Co2.alphaN
  split_ifs
  · exact hT _
  · exact T.one_mem

theorem alphaWord_mem_of {T : Subgroup OLq} (hT : ∀ i, Co2.alpha i ∈ T) (w : List ℤ) :
    Co2.alphaWord w ∈ T := by
  induction w with
  | nil => exact T.one_mem
  | cons l w ih =>
    rw [Co2.alphaWord]
    refine T.mul_mem ?_ ih
    split_ifs
    · exact alphaN_mem_of hT _
    · exact T.inv_mem (alphaN_mem_of hT _)

theorem mk_PO_mem_sup {D : Submodule (ZMod 2) (Fin 24 → ZMod 2)} {Q₁ Q₂ : Subgroup AutPerm}
    (h₁ : MonoHyp D Q₁) (h₂ : MonoHyp D Q₂) {q : AutPerm} (hq : q ∈ Q₁ ⊔ Q₂) :
    (QuotientGroup.mk (PO q) : OLq) ∈ monoSub h₁ ⊔ monoSub h₂ := by
  rw [Subgroup.sup_eq_closure] at hq
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · refine Subgroup.mem_sup_left ?_
      have h := mk_mem_monoSub h₁ (a := 0) D.zero_mem hx
      rwa [gO_zero, one_mul] at h
    · refine Subgroup.mem_sup_right ?_
      have h := mk_mem_monoSub h₂ (a := 0) D.zero_mem hx
      rwa [gO_zero, one_mul] at h
  | one =>
    rw [PO_one]
    exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    rw [PO_mul, QuotientGroup.mk_mul]
    exact Subgroup.mul_mem _ hy hx
  | inv x _ hx =>
    rw [PO_inv, QuotientGroup.mk_inv]
    exact Subgroup.inv_mem _ hx

theorem monoSub_le_sup {D : Submodule (ZMod 2) (Fin 24 → ZMod 2)} {Q Q₁ Q₂ : Subgroup AutPerm}
    (h : MonoHyp D Q) (h₁ : MonoHyp D Q₁) (h₂ : MonoHyp D Q₂) (hQ : Q ≤ Q₁ ⊔ Q₂) :
    monoSub h ≤ monoSub h₁ ⊔ monoSub h₂ := by
  intro x hx
  obtain ⟨a, ha, p, hp, rfl⟩ := (mem_monoSub_iff h).1 hx
  rw [QuotientGroup.mk_mul]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (mk_PO_mem_sup h₁ h₂ (hQ hp))
  have h1 := mk_mem_monoSub h₁ ha Q₁.one_mem
  rwa [PO_one, mul_one] at h1

theorem sup_subgroupOf_eq_comap {G K : Type*} [Group G] [Group K] {J A B : Subgroup G}
    (hA : A ≤ J) (hB : B ≤ J) {f : J →* K} (hf : Function.Surjective f) {A' B' : Subgroup K}
    (hA' : A.subgroupOf J = A'.comap f) (hB' : B.subgroupOf J = B'.comap f) :
    (A ⊔ B).subgroupOf J = (A' ⊔ B').comap f := by
  rw [Subgroup.subgroupOf_sup hA hB, hA', hB', Subgroup.comap_sup_eq f A' B' hf]

theorem Ptwo_subgroupOf_eq_Mfr :
    Ptwo.subgroupOf Jhat = Mfr.comap jhatToKv0 := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, ← mem_Ntwo_iff_Mfr]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem Ptwo_inf_K3_subgroupOf :
    (Ptwo ⊓ K3).subgroupOf Jhat = (NU ⊓ Mfr).comap jhatToKv0 := by
  rw [show Ptwo ⊓ K3 = H3 ⊓ Ntwo from inf_right_comm _ _ _, H3_inf_Ntwo_subgroupOf]

theorem Shat_eq_sup : Shat = Jhat ⊔ Ntwo := by
  refine le_antisymm ?_ (sup_le Jhat_le_Shat Ntwo_le_Shat)
  rintro _ ⟨c, rfl⟩
  obtain ⟨g, rfl⟩ := kappa_surjective c
  have hg : g ∈ Subgroup.closure (((↑) : Cgen → _) ⁻¹'
      (insert tauB (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB)))) :=
    (Subgroup.closure_closure_coe_preimage (k := insert tauB
      (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB)))).ge (Subgroup.mem_top g)
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · refine Subgroup.mem_sup_right ?_
      have hxt : x = tauC := Subtype.ext hx
      rw [hxt]
      exact tauhat_mem_Ntwo
    · refine Subgroup.mem_sup_left ?_
      rw [Jhat_eq_map]
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  | one => rw [map_one, map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv, map_inv]; exact Subgroup.inv_mem _ hx

end CFSG.Monster.B.TwoA

module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

private theorem xof_le_pPrimeCore_of_eq
    (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G) :
    Xof G ≤ CFSG.pPrimeCore 3 G :=
  le_sup_left.trans (le_of_eq hH.symm)

private theorem center_le_pPrimeCore_of_eq
    (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G) :
    Subgroup.center G ≤ CFSG.pPrimeCore 3 G :=
  le_sup_right.trans (le_of_eq hH.symm)

private noncomputable def uc45J (hXH : Xof G ≤ CFSG.pPrimeCore 3 G) :
    ↥(Xof G) →* ↥(CFSG.pPrimeCore 3 G) ⧸
      (Subgroup.center G).subgroupOf (CFSG.pPrimeCore 3 G) :=
  (QuotientGroup.mk' ((Subgroup.center G).subgroupOf (CFSG.pPrimeCore 3 G))).comp
    (Subgroup.inclusion hXH)

private theorem uc45J_surjective
    (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G) :
    Function.Surjective (uc45J (xof_le_pPrimeCore_of_eq hH)) := by
  intro q
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  have hmem : (h : G) ∈ Xof G ⊔ Subgroup.center G := hH ▸ h.2
  obtain ⟨x, hx, c, hc, hxc⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  refine ⟨⟨x, hx⟩, ?_⟩
  change QuotientGroup.mk (Subgroup.inclusion (xof_le_pPrimeCore_of_eq hH) ⟨x, hx⟩) =
    QuotientGroup.mk h
  rw [QuotientGroup.eq]
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion, Subgroup.coe_mul,
    Subgroup.coe_inv]
  rw [← hxc, inv_mul_cancel_left]
  exact hc

private theorem uc45J_ker (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G)
    (c : Ctx45 p G D) :
    (uc45J (xof_le_pPrimeCore_of_eq hH)).ker = Subgroup.center ↥(Xof G) := by
  ext x
  rw [MonoidHom.mem_ker]
  simp only [uc45J, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    have hxZ : (x : G) ∈ Subgroup.center G := by
      simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] using hx
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxZ (y : G)
  · intro hx
    have hxZ : (x : G) ∈ ZXof G := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxZ' : (x : G) ∈ Subgroup.center G := c.ZX_le hxZ
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] using hxZ'

private theorem quotientKerEquivOfSurjective_mk {M N : Type*} [Group M] [Group N]
    (f : M →* N) (hf : Function.Surjective f) (x : M) :
    QuotientGroup.quotientKerEquivOfSurjective f hf (QuotientGroup.mk x) = f x := rfl

private theorem quotientKerEquivOfSurjective_symm_apply {M N : Type*} [Group M] [Group N]
    (f : M →* N) (hf : Function.Surjective f) (x : M) :
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x) = QuotientGroup.mk x :=
  (MulEquiv.symm_apply_eq _).2 (quotientKerEquivOfSurjective_mk f hf x).symm

private noncomputable def uc45Theta
    (j : ↥(Xof G) →* ↥(CFSG.pPrimeCore 3 G) ⧸
      (Subgroup.center G).subgroupOf (CFSG.pPrimeCore 3 G))
    (hj : Function.Surjective j)
    (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5))
    (hjk : j.ker = ψ.ker) (hψs : Function.Surjective ψ) :
    ↥(CFSG.pPrimeCore 3 G) ⧸ (Subgroup.center G).subgroupOf (CFSG.pPrimeCore 3 G) ≃*
      ↥(CFSG.Quasithin.G6.coreMod 5) :=
  (QuotientGroup.quotientKerEquivOfSurjective j hj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hjk).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs))

private theorem uc45Theta_apply_j
    (j : ↥(Xof G) →* ↥(CFSG.pPrimeCore 3 G) ⧸
      (Subgroup.center G).subgroupOf (CFSG.pPrimeCore 3 G))
    (hj : Function.Surjective j)
    (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5))
    (hjk : j.ker = ψ.ker) (hψs : Function.Surjective ψ) (x : ↥(Xof G)) :
    uc45Theta j hj ψ hjk hψs (j x) = ψ x := by
  simp only [uc45Theta, MulEquiv.trans_apply, quotientKerEquivOfSurjective_symm_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, quotientKerEquivOfSurjective_mk]

private theorem uc45Theta_equivariant
    (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G)
    (η : G →* Equiv.Perm (Fin 5))
    (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5))
    (hψs : Function.Surjective ψ)
    (hψe : ∀ (g : G) (x : ↥(Xof G)),
      ψ (MulAut.conjNormal g x) = CFSG.Quasithin.G6.coreAct 5 (η g) (ψ x))
    (hj : Function.Surjective (uc45J (xof_le_pPrimeCore_of_eq hH)))
    (hjk : (uc45J (xof_le_pPrimeCore_of_eq hH)).ker = ψ.ker) :
    ∀ (g : G) (h : ↥(CFSG.pPrimeCore 3 G)),
      uc45Theta (uc45J (xof_le_pPrimeCore_of_eq hH)) hj ψ hjk hψs
          (QuotientGroup.mk (MulAut.conjNormal g h)) =
        CFSG.Quasithin.G6.coreAct 5 (η g)
          (uc45Theta (uc45J (xof_le_pPrimeCore_of_eq hH)) hj ψ hjk hψs
            (QuotientGroup.mk h)) := by
  intro g h
  let j := uc45J (xof_le_pPrimeCore_of_eq hH)
  let θ := uc45Theta j hj ψ hjk hψs
  change θ (QuotientGroup.mk (MulAut.conjNormal g h)) =
    CFSG.Quasithin.G6.coreAct 5 (η g) (θ (QuotientGroup.mk h))
  obtain ⟨x, hx⟩ := hj (QuotientGroup.mk h)
  have hxmk : QuotientGroup.mk (Subgroup.inclusion (xof_le_pPrimeCore_of_eq hH) x) =
      QuotientGroup.mk h := hx
  have hxj : j x = QuotientGroup.mk h := hx
  have hmem : h⁻¹ * Subgroup.inclusion (xof_le_pPrimeCore_of_eq hH) x ∈
      (Subgroup.center G).subgroupOf (CFSG.pPrimeCore 3 G) := by
    simpa only [mul_inv_rev, inv_inv] using inv_mem (QuotientGroup.eq.mp hxmk)
  have hconjmem : (MulAut.conjNormal g h)⁻¹ *
      MulAut.conjNormal g (Subgroup.inclusion (xof_le_pPrimeCore_of_eq hH) x) ∈
      (Subgroup.center G).subgroupOf (CFSG.pPrimeCore 3 G) := by
    rw [← map_inv, ← map_mul, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] using
      (inferInstance : (Subgroup.center G).Normal).conj_mem
        (h⁻¹ * Subgroup.inclusion (xof_le_pPrimeCore_of_eq hH) x) hmem g
  have hmk : QuotientGroup.mk (MulAut.conjNormal g h) =
      QuotientGroup.mk (MulAut.conjNormal g
        (Subgroup.inclusion (xof_le_pPrimeCore_of_eq hH) x)) :=
    QuotientGroup.eq.mpr hconjmem
  have hconjincl : MulAut.conjNormal g
        (Subgroup.inclusion (xof_le_pPrimeCore_of_eq hH) x) =
      Subgroup.inclusion (xof_le_pPrimeCore_of_eq hH) (MulAut.conjNormal g x) :=
    Subtype.ext (by simp)
  have hjconj : j (MulAut.conjNormal g x) =
      QuotientGroup.mk (MulAut.conjNormal g h) := by
    change QuotientGroup.mk (Subgroup.inclusion (xof_le_pPrimeCore_of_eq hH)
      (MulAut.conjNormal g x)) = QuotientGroup.mk (MulAut.conjNormal g h)
    rw [← hconjincl, ← hmk]
  have hθj : ∀ y : ↥(Xof G), θ (j y) = ψ y :=
    fun y => uc45Theta_apply_j j hj ψ hjk hψs y
  calc
    θ (QuotientGroup.mk (MulAut.conjNormal g h))
        = θ (j (MulAut.conjNormal g x)) := by rw [hjconj]
    _ = ψ (MulAut.conjNormal g x) := hθj (MulAut.conjNormal g x)
    _ = CFSG.Quasithin.G6.coreAct 5 (η g) (ψ x) := hψe g x
    _ = CFSG.Quasithin.G6.coreAct 5 (η g) (θ (j x)) := by rw [hθj x]
    _ = CFSG.Quasithin.G6.coreAct 5 (η g) (θ (QuotientGroup.mk h)) := by rw [hxj]

theorem uc45_complement (hSplit : SplitDelta5) (c : Ctx45 p G D)
    (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G) (hD5 : XDelta5 G) :
    ∃ S : Subgroup G, Subgroup.center G ≤ S ∧ S ⊓ CFSG.pPrimeCore 3 G = Subgroup.center G ∧
      S ⊔ CFSG.pPrimeCore 3 G = ⊤ := by
  obtain ⟨η, ψ, hηk, hηr, hψs, hψk, hψe⟩ := hD5
  have hZH : Subgroup.center G ≤ CFSG.pPrimeCore 3 G := center_le_pPrimeCore_of_eq hH
  have hj : Function.Surjective (uc45J (xof_le_pPrimeCore_of_eq hH)) := uc45J_surjective hH
  have hjk : (uc45J (xof_le_pPrimeCore_of_eq hH)).ker = ψ.ker := by
    rw [uc45J_ker hH c, hψk]
  refine hSplit G (CFSG.pPrimeCore 3 G) (Subgroup.center G) hZH η hηk hηr
    (uc45Theta (uc45J (xof_le_pPrimeCore_of_eq hH)) hj ψ hjk hψs) ?_
  exact uc45Theta_equivariant hH η ψ hψs hψe hj hjk

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

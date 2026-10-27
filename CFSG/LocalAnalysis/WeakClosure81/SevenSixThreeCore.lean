module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeBridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeKerAbs
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.Goldschmidt.Steps.G2Grp
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.Foundations
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Goldschmidt.G2
open scoped CFSG.Goldschmidt.G2 commutatorElement

variable {G : Type} [Group G] [Finite G]

section Bar

variable {I Y₀ : Subgroup G} {u : G} [(I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)).Normal]

@[expose] noncomputable def conjRepBar [hI : Fact (IsElemAbelian 2 I)]
    (hLN : Y₀ ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (I : Set G)) :
    Representation (ZMod 2) (↥(Y₀ ⊔ Subgroup.zpowers u) ⧸ I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u))
      (Additive ↥I) :=
  QuotientGroup.lift (I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u))
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (conjRep hLN)) (by
      intro x hx
      have hx' : x ∈ (conjRep hLN).ker := by
        rw [ker_conjRep]
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact congrArg Subtype.val
          (hI.out.1.is_comm.comm (⟨a, ha⟩ : ↥I) (⟨(x : G), hx⟩ : ↥I))
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx', map_one])

theorem conjRepBar_apply [hI : Fact (IsElemAbelian 2 I)]
    (hLN : Y₀ ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (I : Set G))
    (l : ↥(Y₀ ⊔ Subgroup.zpowers u)) (v : Additive ↥I) :
    ((Additive.toMul (conjRepBar hLN (QuotientGroup.mk l) v) : ↥I) : G) =
      (l : G) * (Additive.toMul v : ↥I) * (l : G)⁻¹ :=
  rfl

theorem traceSpace_conjRepBar_ne_bot [hI : Fact (IsElemAbelian 2 I)]
    (hLN : Y₀ ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (I : Set G))
    (hcomm : ⁅I, Subgroup.zpowers u⁆ ≠ ⊥) :
    traceSpace (conjRepBar hLN) (quotU I Y₀ u) ≠ ⊥ := by
  intro hbot
  apply hcomm
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro w hw
  have hmem : (conjRepBar hLN (quotU I Y₀ u) (Additive.ofMul ⟨w, hw⟩) -
      Additive.ofMul ⟨w, hw⟩) ∈ traceSpace (conjRepBar hLN) (quotU I Y₀ u) :=
    mem_traceSpace.mpr ⟨_, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  have h2 := congrArg (fun t : Additive ↥I => ((Additive.toMul t : ↥I) : G)) hmem
  simp only [toMul_sub, Subgroup.coe_div, toMul_zero, Subgroup.coe_one] at h2
  have h3 := conjRepBar_apply hLN (uMem Y₀ u) (Additive.ofMul ⟨w, hw⟩)
  rw [toMul_ofMul] at h2 h3
  have h4 : u * w * u⁻¹ = w := by
    rw [div_eq_one] at h2
    exact h3.symm.trans h2
  calc w * u = (u * w * u⁻¹) * u := by rw [h4]
    _ = u * w := by group

theorem toMul_mem_commutator_of_mem_traceSpace [hI : Fact (IsElemAbelian 2 I)]
    (hLN : Y₀ ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (I : Set G))
    {t : Additive ↥I} (ht : t ∈ traceSpace (conjRepBar hLN) (quotU I Y₀ u)) :
    ((Additive.toMul t : ↥I) : G) ∈ ⁅I, Subgroup.zpowers u⁆ := by
  obtain ⟨v, rfl⟩ := mem_traceSpace.mp ht
  have h1 : ((Additive.toMul (conjRepBar hLN (quotU I Y₀ u) v - v) : ↥I) : G) =
      u * (Additive.toMul v : ↥I) * u⁻¹ * ((Additive.toMul v : ↥I) : G)⁻¹ := by
    rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
    exact congrArg (fun x => x * ((Additive.toMul v : ↥I) : G)⁻¹)
      (conjRepBar_apply hLN (uMem Y₀ u) v)
  rw [h1, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers u) (Additive.toMul v : ↥I).2

theorem mem_normalizer_of_isTI_of_conj_mem {U : Subgroup G}
    (hTI : CFSG.CGT.Timmesfeld75.IsTI U) {w y : G} (hwU : w ∈ U) (hw1 : w ≠ 1)
    (hy : y * w * y⁻¹ ∈ U) : y ∈ Subgroup.normalizer (U : Set G) := by
  have hne : U ⊓ conjSubgroup U y ≠ ⊥ := by
    intro hbot
    have hmem : w ∈ U ⊓ conjSubgroup U y := ⟨hwU, mem_conjSubgroup_iff.mpr hy⟩
    rw [hbot] at hmem
    exact hw1 (by simpa using hmem)
  exact conjSubgroup_eq_iff_mem_normalizer.mp (conjSubgroup_eq_of_isTI hTI hne)

theorem conjRepBar_ti [hI : Fact (IsElemAbelian 2 I)]
    (hLN : Y₀ ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (I : Set G)) {U : Subgroup G}
    (hUTI : CFSG.CGT.Timmesfeld75.IsTI U) (huU : u ∈ U) (hcommU : ⁅I, Subgroup.zpowers u⁆ ≤ U)
    (huY : u ∈ Subgroup.normalizer (Y₀ : Set G)) (hUY : ∀ w ∈ U, w ∈ Y₀ → w ∈ I) :
    ∀ y ∈ quotY I Y₀ u,
      traceSpace (conjRepBar hLN) (quotU I Y₀ u) ⊓
          (traceSpace (conjRepBar hLN) (quotU I Y₀ u)).map (conjRepBar hLN y) ≠ ⊥ →
        y * quotU I Y₀ u = quotU I Y₀ u * y := by
  intro y hy hne
  obtain ⟨y₀, hyL, hy₀, rfl⟩ := (mem_quotY_iff).mp hy
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨htT, htT'⟩ := Submodule.mem_inf.mp ht
  obtain ⟨t', ht'T, rfl⟩ := Submodule.mem_map.mp htT'
  have hwU : ((Additive.toMul (conjRepBar hLN (QuotientGroup.mk ⟨y₀, hyL⟩) t') : ↥I) : G) ∈ U :=
    hcommU (toMul_mem_commutator_of_mem_traceSpace hLN htT)
  have hw'U : ((Additive.toMul t' : ↥I) : G) ∈ U :=
    hcommU (toMul_mem_commutator_of_mem_traceSpace hLN ht'T)
  have hconj := conjRepBar_apply hLN ⟨y₀, hyL⟩ t'
  have hw1 : ((Additive.toMul t' : ↥I) : G) ≠ 1 := by
    intro h1
    apply ht0
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hconj, h1]
    simp
  have hy₀N : y₀ ∈ Subgroup.normalizer (U : Set G) :=
    mem_normalizer_of_isTI_of_conj_mem hUTI hw'U hw1 (by rw [← hconj]; exact hwU)
  have h1 : y₀ * u * y₀⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hy₀N u).mp huU
  have h2 : y₀ * u * y₀⁻¹ * u⁻¹ ∈ U := U.mul_mem h1 (U.inv_mem huU)
  have h3 : y₀ * u * y₀⁻¹ * u⁻¹ ∈ Y₀ := by
    have h4 : u * y₀⁻¹ * u⁻¹ ∈ Y₀ :=
      (Subgroup.mem_normalizer_iff.mp huY y₀⁻¹).mp (Y₀.inv_mem hy₀)
    have h5 := Y₀.mul_mem hy₀ h4
    rwa [show y₀ * (u * y₀⁻¹ * u⁻¹) = y₀ * u * y₀⁻¹ * u⁻¹ by group] at h5
  exact mk_mul_quotU_comm hyL (hUY _ h2 h3)

end Bar

theorem seven_six_three_core {I Y₀ U : Subgroup G} {u : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hIab : IsElemAbelian 2 I) (hIY : I ≤ Y₀) (hYI : Y₀ ≤ Subgroup.normalizer (I : Set G))
    (huI : u ∈ Subgroup.normalizer (I : Set G)) (hu2 : u * u = 1)
    (huY : u ∈ Subgroup.normalizer (Y₀ : Set G)) (hexp : ∀ y ∈ Y₀, y ^ p ∈ I)
    (hcl : ∀ x ∈ Y₀, ∀ y ∈ Y₀, ∀ z ∈ Y₀, ⁅⁅x, y⁆, z⁆ ∈ I)
    (hgen : Y₀ ≤ ⁅Y₀, Subgroup.zpowers u⁆ ⊔ I) (hne : I ≠ Y₀)
    (hUTI : CFSG.CGT.Timmesfeld75.IsTI U) (huU : u ∈ U) (hcommU : ⁅I, Subgroup.zpowers u⁆ ≤ U)
    (hcommne : ⁅I, Subgroup.zpowers u⁆ ≠ ⊥) (hUY : ∀ w ∈ U, w ∈ Y₀ → w ∈ I) :
    I.relIndex Y₀ = p ∨ (I.relIndex Y₀ = p ^ 3 ∧ ∃ x ∈ Y₀, ∃ y ∈ Y₀, ⁅x, y⁆ ∉ I) := by
  haveI : Fact (IsElemAbelian 2 I) := ⟨hIab⟩
  haveI := normal_subgroupOf_sup_zpowers hIY hYI huI (u := u)
  have hLN : Y₀ ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (I : Set G) :=
    sup_le hYI (Subgroup.zpowers_le.mpr huI)
  have hQ : quotY I Y₀ u ≠ ⊥ := by
    intro hbot
    have h1 := card_quotY (I := I) (Y₀ := Y₀) (u := u) hIY
    rw [hbot, Subgroup.card_bot] at h1
    have h2 : Y₀ ≤ I := Subgroup.relIndex_eq_one.mp h1.symm
    exact hne (le_antisymm hIY h2)
  have hmain := PInvol.card_main_of_rep (conjRepBar hLN)
    (pInvol_quotY hp hp2 hIY hexp hcl hu2 huY hgen)
    quotY_sup_zpowers_quotU_eq_top hQ (traceSpace_conjRepBar_ne_bot hLN hcommne)
    (conjRepBar_ti hLN hUTI huU hcommU huY hUY)
  rw [card_quotY hIY] at hmain
  rcases hmain with h | ⟨h, hxy⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, exists_commutator_notMem_of_quotY hxy⟩

end CFSG.LocalAnalysis.WeakClosure81

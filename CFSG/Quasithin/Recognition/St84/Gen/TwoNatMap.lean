module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalDefs

import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G H : Type*} [Group G] [Group H]

private theorem isTwoNatType_block_map {L : Subgroup G} {N : Subgroup H} (e : ↥L ≃* ↥N) :
    ∃ g : ↥L →* H, Function.Injective g ∧
      (∀ x : ↥L, g x = (e x : H)) ∧
      blockU N = (blockU (⊤ : Subgroup ↥L)).map g ∧
      blockZ N = (blockZ (⊤ : Subgroup ↥L)).map g := by
  classical
  let g : ↥L →* H := N.subtype.comp e.toMonoidHom
  have hg : Function.Injective g := N.subtype_injective.comp e.injective
  have hN : (⊤ : Subgroup ↥L).map g = N := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine ⟨g, hg, fun _ => rfl, ?_, ?_⟩
  · rw [← hN,
      CFSG.QuasithinUnique.Setup.Wreath.blockU_map_injective g hg (⊤ : Subgroup ↥L)]
  · rw [← hN,
      CFSG.QuasithinUnique.Setup.Wreath.blockZ_map_injective g hg (⊤ : Subgroup ↥L)]

private theorem isTwoNatType_exists_blockU_equiv {L : Subgroup G} {N : Subgroup H}
    (g : ↥L →* H) (hg : Function.Injective g)
    (hU : blockU N = (blockU (⊤ : Subgroup ↥L)).map g)
    (hZ : blockZ N = (blockZ (⊤ : Subgroup ↥L)).map g)
    (hBL : blockU L ≤ L) :
    ∃ eU : ↥(blockU L) ≃* ↥(blockU N),
      (∀ u : ↥(blockU L),
        ((eU u : ↥(blockU N)) : H) = g ⟨(u : G), hBL u.2⟩) ∧
      (∀ u : ↥(blockU L),
        ((eU u : ↥(blockU N)) : H) ∈ blockZ N ↔ (u : G) ∈ blockZ L) := by
  have hL : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hUL : blockU L = (blockU (⊤ : Subgroup ↥L)).map L.subtype := by
    conv_lhs => rw [← hL]
    exact CFSG.QuasithinUnique.Setup.Wreath.blockU_map_injective L.subtype
      L.subtype_injective (⊤ : Subgroup ↥L)
  have hZL : blockZ L = (blockZ (⊤ : Subgroup ↥L)).map L.subtype := by
    conv_lhs => rw [← hL]
    exact CFSG.QuasithinUnique.Setup.Wreath.blockZ_map_injective L.subtype
      L.subtype_injective (⊤ : Subgroup ↥L)
  let eLtop : ↥(blockU L) ≃* ↥(blockU (⊤ : Subgroup ↥L)) :=
    (MulEquiv.subgroupCongr hUL).trans
      (((blockU (⊤ : Subgroup ↥L)).equivMapOfInjective L.subtype
        L.subtype_injective).symm)
  let eU : ↥(blockU L) ≃* ↥(blockU N) :=
    eLtop.trans (((blockU (⊤ : Subgroup ↥L)).equivMapOfInjective g hg).trans
      (MulEquiv.subgroupCongr hU.symm))
  have heU : ∀ u : ↥(blockU L),
      ((eU u : ↥(blockU N)) : H) = g ⟨(u : G), hBL u.2⟩ := by
    intro u
    simp only [eU, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom, eLtop,
      MulEquiv.subgroupCongr_apply, MulEquiv.symm_apply_apply]
    change g (((blockU (⊤ : Subgroup ↥L)).equivMapOfInjective L.subtype
      L.subtype_injective).symm ((MulEquiv.subgroupCongr hUL) u)) = g ⟨(u : G), hBL u.2⟩
    congr 1
    obtain ⟨x, hxmem, hxu⟩ := Subgroup.mem_map.mp (show (u : G) ∈
      (blockU (⊤ : Subgroup ↥L)).map L.subtype from hUL ▸ u.2)
    have hx2 : ((blockU (⊤ : Subgroup ↥L)).equivMapOfInjective L.subtype
        L.subtype_injective) ⟨x, hxmem⟩ = (MulEquiv.subgroupCongr hUL) u := by
      apply Subtype.ext
      exact hxu
    rw [← hx2, MulEquiv.symm_apply_apply]
    exact Subtype.ext hxu
  have hZmem : ∀ u : ↥(blockU L),
      ((eU u : ↥(blockU N)) : H) ∈ blockZ N ↔ (u : G) ∈ blockZ L := by
    intro u
    rw [hZ, hZL, heU]
    exact (Subgroup.mem_map_iff_mem hg).trans
      (Subgroup.mem_map_iff_mem L.subtype_injective).symm
  exact ⟨eU, heU, hZmem⟩

theorem IsTwoNatType.of_mulEquiv {L : Subgroup G} {N : Subgroup H} {m : ℕ} (e : ↥L ≃* ↥N)
    (h : IsTwoNatType N m) : IsTwoNatType L m := by
  classical
  obtain ⟨F, _, _, hF, α, hαs, hαk, β, hβs, hβk, hβe⟩ := h
  obtain ⟨g, hg, hgapp, hU, hZ⟩ := isTwoNatType_block_map e
  have hBL : blockU L ≤ L := by
    rw [blockU, Subgroup.commutator_le]
    intro a ha b hb
    have haL : a ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L ha
    have hbL : b ∈ L := hb
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem haL hbL) (L.inv_mem haL)) (L.inv_mem hbL)
  obtain ⟨eU, heU, hZmem⟩ := isTwoNatType_exists_blockU_equiv g hg hU hZ hBL
  refine ⟨F, inferInstance, inferInstance, hF, α.comp e.toMonoidHom,
    hαs.comp e.surjective, ?_, β.comp eU.toMonoidHom, hβs.comp eU.surjective, ?_, ?_⟩
  · ext x
    change α (e x) = 1 ↔ x ∈ CFSG.pCore 2 ↥L
    constructor
    · intro hx
      have h1 : e x ∈ α.ker := MonoidHom.mem_ker.2 hx
      rw [hαk, ← CFSG.pCore_map_iso 2 e] at h1
      exact (Subgroup.mem_map_iff_mem e.injective).mp h1
    · intro hx
      have h1 : e x ∈ CFSG.pCore 2 ↥N := by
        rw [← CFSG.pCore_map_iso 2 e]
        exact Subgroup.mem_map_of_mem _ hx
      exact MonoidHom.mem_ker.1 (hαk ▸ h1)
  · ext u
    change β (eU u) = 1 ↔ u ∈ (blockZ L).subgroupOf (blockU L)
    rw [show β (eU u) = 1 ↔ eU u ∈ β.ker from MonoidHom.mem_ker, hβk,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hZmem u
  · intro ℓ u v huv
    have hrel : ((eU v : ↥(blockU N)) : H) = (e ℓ : H) *
        ((eU u : ↥(blockU N)) : H) * (e ℓ : H)⁻¹ := by
      rw [heU, heU, ← hgapp ⟨(ℓ : G), ℓ.2⟩]
      have h1 : (⟨(v : G), hBL v.2⟩ : ↥L) = ℓ * ⟨(u : G), hBL u.2⟩ * ℓ⁻¹ := by
        apply Subtype.ext
        simpa using huv
      rw [h1, map_mul, map_mul, map_inv]
    have := hβe (e ℓ) (eU u) (eU v) hrel
    simpa [MonoidHom.comp_apply] using this

theorem le_centralizer_centerOf_pCoreOf_of_mulEquiv {L : Subgroup G} {N : Subgroup H} {p : ℕ}
    (e : ↥L ≃* ↥N) (h : N ≤ Subgroup.centralizer (centerOf (pCoreOf p N) : Set H)) :
    L ≤ Subgroup.centralizer (centerOf (pCoreOf p L) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzL : z ∈ L := CFSG.LieType.BorelTits.pCoreOf_le p L (Subgroup.mem_inf.mp hz).1
  have hzQN : ((e ⟨z, hzL⟩ : ↥N) : H) ∈ pCoreOf p N :=
    (mem_pCoreOf_iff_of_mulEquiv e p ⟨z, hzL⟩).mp (Subgroup.mem_inf.mp hz).1
  have hzZ : ((e ⟨z, hzL⟩ : ↥N) : H) ∈ centerOf (pCoreOf p N) := by
    rw [centerOf, Subgroup.mem_inf]
    refine ⟨hzQN, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨w, hw⟩ := e.surjective ⟨y, CFSG.LieType.BorelTits.pCoreOf_le p N hy⟩
    have hw' : ((e w : ↥N) : H) = y := congrArg Subtype.val hw
    have hwp : (w : G) ∈ pCoreOf p L :=
      (mem_pCoreOf_iff_of_mulEquiv e p w).mpr (hw' ▸ hy)
    have hzw : (w : G) * z = z * w :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 w hwp
    have h1 : e w * e ⟨z, hzL⟩ = e ⟨z, hzL⟩ * e w := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hzw
    rw [← hw']
    exact congrArg Subtype.val h1
  have hcommL : (⟨z, hzL⟩ : ↥L) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨z, hzL⟩ := by
    apply e.injective
    rw [map_mul, map_mul]
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (h (e ⟨x, hx⟩).2) (e ⟨z, hzL⟩) hzZ)
  simpa using congrArg Subtype.val hcommL

end CFSG.Quasithin.F112R.St84

end

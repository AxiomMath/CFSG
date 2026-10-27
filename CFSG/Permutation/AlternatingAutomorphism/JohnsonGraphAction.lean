module

public import CFSG.Permutation.AlternatingAutomorphism.JohnsonGraph
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.Permutation.AlternatingAutomorphism.ThreeCycle

public section

namespace CFSG

namespace AlternatingAutomorphism

open Equiv Equiv.Perm Finset johnsonGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_alternatingGroup_isThreeCycle_support_eq {s : Finset α} (hs : #s = 3) :
    ∃ g : alternatingGroup α, (g : Perm α).IsThreeCycle ∧ (g : Perm α).support = s := by
  obtain ⟨c, hc, hcs⟩ := exists_isThreeCycle_support_eq hs
  exact ⟨⟨c, hc.mem_alternatingGroup⟩, hc, hcs⟩

private theorem support_map_eq (f : MulAut (alternatingGroup α)) {g h : alternatingGroup α}
    (hg : (g : Perm α).IsThreeCycle) (hh : (h : Perm α).IsThreeCycle)
    (hgh : (g : Perm α).support = (h : Perm α).support) :
    (f g : Perm α).support = (f h : Perm α).support := by
  obtain e | e := eq_or_eq_inv_of_support_eq hg hh hgh
  · rw [Subtype.ext e]
  · rw [show h = g⁻¹ from Subtype.ext e, map_inv, Subgroup.coe_inv, support_inv]

private noncomputable def supportMap (f : MulAut (alternatingGroup α))
    (hf : ∀ g, (f g : Perm α).IsThreeCycle ↔ (g : Perm α).IsThreeCycle)
    (s : {s : Finset α // #s = 3}) : {s : Finset α // #s = 3} :=
  ⟨(f (exists_alternatingGroup_isThreeCycle_support_eq s.2).choose : Perm α).support,
    ((hf _).mpr (exists_alternatingGroup_isThreeCycle_support_eq s.2).choose_spec.1).card_support⟩

variable {f : MulAut (alternatingGroup α)}
  (hf : ∀ g, (f g : Perm α).IsThreeCycle ↔ (g : Perm α).IsThreeCycle)
include hf

private theorem supportMap_apply {g : alternatingGroup α} (hg : (g : Perm α).IsThreeCycle) :
    (supportMap f hf ⟨(g : Perm α).support, hg.card_support⟩).1 = (f g : Perm α).support :=
  have h := (exists_alternatingGroup_isThreeCycle_support_eq hg.card_support).choose_spec
  support_map_eq f h.1 hg h.2

private theorem supportMap_supportMap {f' : MulAut (alternatingGroup α)}
    (hf' : ∀ g, (f' g : Perm α).IsThreeCycle ↔ (g : Perm α).IsThreeCycle)
    (hff' : ∀ g, f' (f g) = g) (s : {s : Finset α // #s = 3}) :
    supportMap f' hf' (supportMap f hf s) = s := by
  obtain ⟨g, hg, hgs⟩ := exists_alternatingGroup_isThreeCycle_support_eq s.2
  obtain rfl : s = ⟨_, hg.card_support⟩ := Subtype.ext hgs.symm
  have : supportMap f hf ⟨_, hg.card_support⟩ = ⟨_, ((hf g).mpr hg).card_support⟩ :=
    Subtype.ext (supportMap_apply hf hg)
  rw [this]
  exact Subtype.ext ((supportMap_apply hf' ((hf g).mpr hg)).trans (by rw [hff']))

private theorem isThreeCycle_symm_iff :
    ∀ g, (f.symm g : Perm α).IsThreeCycle ↔ (g : Perm α).IsThreeCycle := fun g => by
  rw [← hf, MulEquiv.apply_symm_apply]

private noncomputable def supportEquiv : {s : Finset α // #s = 3} ≃ {s : Finset α // #s = 3} where
  toFun := supportMap f hf
  invFun := supportMap f.symm (isThreeCycle_symm_iff hf)
  left_inv := supportMap_supportMap hf _ f.symm_apply_apply
  right_inv := supportMap_supportMap _ hf f.apply_symm_apply

private theorem supportEquiv_apply {g : alternatingGroup α} (hg : (g : Perm α).IsThreeCycle) :
    (supportEquiv hf ⟨(g : Perm α).support, hg.card_support⟩).1 = (f g : Perm α).support :=
  supportMap_apply hf hg

private theorem supportEquiv_adj {s t : {s : Finset α // #s = 3}}
    (h : (johnsonGraph α 3).Adj s t) :
    (johnsonGraph α 3).Adj (supportEquiv hf s) (supportEquiv hf t) := by
  obtain ⟨c, d, hcs, hdt, hc, hd, hcd⟩ :=
    exists_isThreeCycle_mul_inv s.2 t.2 (by simp only [adj_iff] at h; omega)
  let g₁ : alternatingGroup α := ⟨c, hc.mem_alternatingGroup⟩
  let g₂ : alternatingGroup α := ⟨d, hd.mem_alternatingGroup⟩
  have hne := card_inter_lt ((supportEquiv hf).injective.ne h.ne)
  obtain rfl : s = ⟨(g₁ : Perm α).support, hc.card_support⟩ := Subtype.ext hcs.symm
  obtain rfl : t = ⟨(g₂ : Perm α).support, hd.card_support⟩ := Subtype.ext hdt.symm
  have h3 : ((f g₁ : Perm α) * (f g₂ : Perm α)⁻¹).IsThreeCycle := by
    simpa using (hf (g₁ * g₂⁻¹)).mpr hcd
  have := two_le_card_support_inter ((hf g₁).mpr hc) ((hf g₂).mpr hd).inv h3
  rw [support_inv] at this
  rw [adj_iff, supportEquiv_apply hf hc, supportEquiv_apply hf hd]
  rw [supportEquiv_apply hf hc, supportEquiv_apply hf hd] at hne
  omega

theorem exists_johnsonGraph_iso : ∃ F : johnsonGraph α 3 ≃g johnsonGraph α 3,
    ∀ (g : alternatingGroup α) (hg : (g : Perm α).IsThreeCycle),
      (F ⟨(g : Perm α).support, hg.card_support⟩).1 = (f g : Perm α).support := by
  refine ⟨⟨supportEquiv hf, fun {s t} => ⟨fun h => ?_, supportEquiv_adj hf⟩⟩,
    fun _ => supportEquiv_apply hf⟩
  have hinv (x) : supportEquiv (isThreeCycle_symm_iff hf) (supportEquiv hf x) = x :=
    (supportEquiv hf).left_inv x
  simpa only [hinv] using supportEquiv_adj (isThreeCycle_symm_iff hf) h

end AlternatingAutomorphism

end CFSG

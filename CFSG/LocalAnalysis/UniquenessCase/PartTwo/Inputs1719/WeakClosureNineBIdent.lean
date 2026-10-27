module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBImage
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open Subgroup CFSG.Quasithin

theorem map_equiv_eq_subgroupOf {X : Type} [Group X] {G : Subgroup P16} (e : X ≃* G)
    (f : X →* P16) (hf : ∀ x, (e x : P16) = f x) {H : Subgroup X} {K : Subgroup P16}
    (hH : H.map f = K) : H.map e.toMonoidHom = K.subgroupOf G := by
  ext ⟨g, hg⟩
  rw [mem_subgroupOf, ← hH]
  constructor
  · rintro ⟨x, hx, hxe⟩
    exact ⟨x, hx, by rw [← hf]; exact congrArg Subtype.val hxe⟩
  · rintro ⟨x, hx, hxf⟩
    exact ⟨x, hx, Subtype.ext (by rw [MulEquiv.coe_toMonoidHom, hf]; exact hxf)⟩

theorem isSylowIn_inf_L {X : Type} [Group X] [Finite X] {L L' Tb : Subgroup X} {t₀ : X}
    (hS : Setting L L' Tb t₀) (hsyl : IsSylowIn 2 Tb ⊤) : IsSylowIn 2 (Tb ⊓ L) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsSylowIn 2 (Tb ⊓ (L ⊔ L')) (L ⊔ L') := hsyl.inf_normal le_top (hS.normal.subgroupOf ⊤)
  have h2 := h1.inf_normal le_sup_left
    ((normal_subgroupOf_iff_le_normalizer le_sup_left).2 hS.sup_le_normalizer)
  rwa [inf_assoc, inf_eq_right.2 (le_sup_left : L ≤ L ⊔ L')] at h2

theorem nGIdent_holds : NGIdent := by
  intro X _ _ L1b L2b Tb hL ⟨t₀, ht₀, hL2⟩ hne hperm hcomm hnorm hcent htop hsyl
  have hS : Setting L1b L2b Tb t₀ := ⟨ht₀, hL2, hne, hperm, hcomm, hnorm, hcent, htop⟩
  obtain ⟨β, hβ⟩ := exists_isBeta hL (isSylowIn_inf_L hS hsyl)
  have h3 : Tb.map (hS.phi β) ≤ TB 3 := map_le_iff_le_comap.2 fun t ht => hS.phi_mem_TB3 hβ ht
  obtain ⟨i, hi⟩ := eq_TB_of h3 (hS.TD_le_map_phi hβ) (hS.sig_or_d1sig hβ)
  have hinj := hS.phi_injective hβ.inj
  have hrange : (hS.phi β).range = GB i := by
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, Subgroup.map_sup, hS.map_phi_L hβ,
      hS.map_phi_L' hβ, hi, sup_TB_eq_GB]
  let e : X ≃* GB i := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ x, ((e x : GB i) : P16) = hS.phi β x := fun x => rfl
  exact ⟨i, e, map_equiv_eq_subgroupOf e _ he (hS.map_phi_L hβ),
    map_equiv_eq_subgroupOf e _ he (hS.map_phi_L' hβ), map_equiv_eq_subgroupOf e _ he hi⟩

end CFSG.LocalAnalysis.WeakClosure81.NGM

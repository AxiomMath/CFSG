module

public import CFSG.Quasithin.Background.C124BlkBasic
public import CFSG.Quasithin.Background.B4Models

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {V L : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] noncomputable def commEquiv (hL : L ≤ Subgroup.normalizer (V : Set G)) :
    ↥(commV (autI hV L)) ≃* ↥(⁅V, L⁆ : Subgroup G) :=
  (Subgroup.equivMapOfInjective _ (blkVal hV) (blkVal_injective hV)).trans
    (MulEquiv.subgroupCongr (map_blkVal_commV hV hL))

theorem commEquiv_apply (hL : L ≤ Subgroup.normalizer (V : Set G))
    (x : ↥(commV (autI hV L))) : ((commEquiv hV hL x : ↥(⁅V, L⁆ : Subgroup G)) : G) =
      (x : IntMod V hV).val := rfl

theorem commEquiv_symm_val (hL : L ≤ Subgroup.normalizer (V : Set G))
    (a : ↥(⁅V, L⁆ : Subgroup G)) : (((commEquiv hV hL).symm a : ↥(commV (autI hV L))) :
      IntMod V hV).val = a := by
  have := commEquiv_apply hV hL ((commEquiv hV hL).symm a)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem comm_blockZ (hVL : ⁅V, L⁆ ≤ blockU L) {a b : G} (ha : a ∈ ⁅V, L⁆) (hb : b ∈ blockZ L) :
    a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp hb.2 a (blockU_le L (hVL ha))

theorem exists_mul_of_blockU (hVL : ⁅V, L⁆ ≤ blockU L) (hU : blockU L = ⁅V, L⁆ ⊔ blockZ L)
    {u : G} (hu : u ∈ blockU L) : ∃ a ∈ (⁅V, L⁆ : Subgroup G), ∃ b ∈ blockZ L, u = a * b := by
  let P : Subgroup G :=
    { carrier := {u | ∃ a ∈ (⁅V, L⁆ : Subgroup G), ∃ b ∈ blockZ L, u = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', Subgroup.mul_mem _ ha ha', b * b', Subgroup.mul_mem _ hb hb', ?_⟩
        have hbc : b * a' = a' * b := (comm_blockZ hVL ha' hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * a' * (b * b') := by rw [hbc]; group
      one_mem' := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, Subgroup.inv_mem _ ha, b⁻¹, Subgroup.inv_mem _ hb, ?_⟩
        have hbc : a * b = b * a := comm_blockZ hVL ha hb
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := by
            rw [show a⁻¹ * b⁻¹ = (b * a)⁻¹ by group, ← hbc]
            group }
  have hle : (⁅V, L⁆ ⊔ blockZ L : Subgroup G) ≤ P :=
    sup_le (fun a ha => ⟨a, ha, 1, Subgroup.one_mem _, by simp⟩)
      (fun b hb => ⟨1, Subgroup.one_mem _, b, hb, by simp⟩)
  exact hle (hU ▸ hu)

theorem exists_blockHom (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hVL : ⁅V, L⁆ ≤ blockU L) (hU : blockU L = ⁅V, L⁆ ⊔ blockZ L) (D : FFModel)
    (π : D.Gam →* ↥(autI hV L))
    (hπ : D.RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π) :
    ∃ β : ↥(blockU L) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec,
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      ∀ (ℓ : ↥L) (γ : D.Gam), π γ = starHom hV L hL ℓ →
        ∀ (u v : ↥(blockU L)) (m : ↥D.sec) (hm : D.act γ (m : D.Amb) ∈ D.sec),
          (v : G) = ℓ * u * ℓ⁻¹ → β u = QuotientGroup.mk m →
          β v = QuotientGroup.mk ⟨D.act γ m, hm⟩ := by
  obtain ⟨-, -, -, hUinv, -, -, -, β', hβ's, hβ'k, hβ'e⟩ := hπ
  have hWL : ∀ a ∈ (⁅V, L⁆ : Subgroup G), a ∈ L := fun a ha => blockU_le L (hVL ha)
  let f : ↥(⁅V, L⁆ : Subgroup G) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    β'.comp (commEquiv hV hL).symm.toMonoidHom
  have hfix : ∀ (a : G) (ha : a ∈ (⁅V, L⁆ : Subgroup G)),
      (((commEquiv hV hL).symm ⟨a, ha⟩ : ↥(commV (autI hV L))) : IntMod V hV) ∈
          fixV (autI hV L) ↔ a ∈ Subgroup.centralizer (L : Set G) := by
    intro a ha
    rw [mem_fixV_autI hV hL, commEquiv_symm_val hV hL]
  have hf0 : ∀ (a : G) (ha : a ∈ (⁅V, L⁆ : Subgroup G)), a ∈ blockZ L → f ⟨a, ha⟩ = 1 := by
    intro a ha hb
    refine (hβ'k _).2 ?_
    exact ⟨(hfix a ha).2 hb.2, ((commEquiv hV hL).symm ⟨a, ha⟩).2⟩
  have hf1 : ∀ (a : G) (ha : a ∈ (⁅V, L⁆ : Subgroup G)), f ⟨a, ha⟩ = 1 → a ∈ blockZ L := by
    intro a ha h
    exact ⟨hVL ha, (hfix a ha).1 ((hβ'k _).1 h).1⟩
  obtain ⟨g, hg, hgk⟩ := exists_extend_hom (U := blockU L) (A := ⁅V, L⁆) (B := blockZ L)
    (fun u hu => exists_mul_of_blockU hVL hU hu) (fun a ha b hb => comm_blockZ hVL ha hb)
    f hf0 hf1
  refine ⟨g, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨x, hx⟩ := hβ's q
    set a : ↥(⁅V, L⁆ : Subgroup G) := commEquiv hV hL x with ha
    refine ⟨⟨a, hVL a.2⟩, ?_⟩
    rw [hg ⟨a, hVL a.2⟩ a 1 a.2 (Subgroup.one_mem _) (by simp)]
    show β' ((commEquiv hV hL).symm a) = q
    rw [ha, MulEquiv.symm_apply_apply, hx]
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hgk u
  · intro ℓ γ hγ u v m hm hv hu
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_blockU hVL hU u.2
    have hℓ : (ℓ : G) ∈ L := ℓ.2
    have hb' : (ℓ : G) * b * (ℓ : G)⁻¹ = b := by
      rw [Subgroup.mem_centralizer_iff.mp hb.2 ℓ hℓ]
      group
    rw [Subgroup.coe_inv] at hv
    have ha' : (ℓ : G) * a * (ℓ : G)⁻¹ ∈ (⁅V, L⁆ : Subgroup G) :=
      conj_mem_commutator hL hℓ ha
    have hvab : (v : G) = ((ℓ : G) * a * (ℓ : G)⁻¹) * b := by
      calc (v : G) = (ℓ : G) * (a * b) * (ℓ : G)⁻¹ := by rw [hv, hab]
        _ = ((ℓ : G) * a * (ℓ : G)⁻¹) * ((ℓ : G) * b * (ℓ : G)⁻¹) := by group
        _ = _ := by rw [hb']
    rw [hg v _ b ha' hb hvab]
    rw [hg u a b ha hb hab] at hu
    set x : ↥(commV (autI hV L)) := (commEquiv hV hL).symm ⟨a, ha⟩ with hx
    have hxu : β' x = QuotientGroup.mk m := hu
    have hux := hUinv (π γ) x x.2
    have h1 := hβ'e γ x m hux hm hxu
    have hval : ((π γ : ↥(autI hV L)) : MulAut (IntMod V hV)) (x : IntMod V hV) =
        (((commEquiv hV hL).symm ⟨_, ha'⟩ : ↥(commV (autI hV L))) : IntMod V hV) := by
      apply IntMod.val_injective
      rw [commEquiv_symm_val, hγ, starHom_apply, convI_apply_val, hx, commEquiv_symm_val]
    have h2 : (⟨((π γ : ↥(autI hV L)) : MulAut (IntMod V hV)) (x : IntMod V hV), hux⟩ :
        ↥(commV (autI hV L))) = (commEquiv hV hL).symm ⟨_, ha'⟩ := Subtype.ext hval
    show β' ((commEquiv hV hL).symm ⟨_, ha'⟩) = _
    rw [← h2]
    exact h1

theorem exists_blockHomOfEquiv (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hVL : ⁅V, L⁆ ≤ blockU L) (hU : blockU L = ⁅V, L⁆ ⊔ blockZ L) (D : FFModel)
    (π : D.Gam →* ↥(autI hV L))
    (hπ : D.RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π)
    {T : Type*} [Group T] (eQ : (↥D.sec ⧸ D.ker.subgroupOf D.sec) ≃* T) :
    ∃ β : ↥(blockU L) →* T,
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      ∀ (ℓ : ↥L) (γ : D.Gam), π γ = starHom hV L hL ℓ →
        ∀ (u v : ↥(blockU L)) (m : ↥D.sec) (hm : D.act γ (m : D.Amb) ∈ D.sec),
          (v : G) = ℓ * u * ℓ⁻¹ → β u = eQ (QuotientGroup.mk m) →
          β v = eQ (QuotientGroup.mk ⟨D.act γ m, hm⟩) := by
  obtain ⟨β₀, hs, hk, he⟩ := exists_blockHom hV hL hVL hU D π hπ
  refine ⟨eQ.toMonoidHom.comp β₀, eQ.surjective.comp hs, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective β₀ _ eQ.injective]
    exact hk
  · intro ℓ γ hγ u v m hm hv hu
    have hu' : β₀ u = QuotientGroup.mk m := eQ.injective hu
    show eQ (β₀ v) = _
    rw [he ℓ γ hγ u v m hm hv hu']

end CFSG.Quasithin.C124

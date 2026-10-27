module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Iso
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Split

public section

namespace CFSG.Quasithin.H13

open Equiv MulAction CFSG.A7Fano CFSG.M23Heptad CFSG.Blueprint CFSG.Open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.L246.C123 (A7)
open CFSG.Quasithin.Asc94 (heptad₀)
open scoped Pointwise

theorem isComplement'_Ubar_Abar :
    (Ubar : Subgroup ↥M2bar).IsComplement' Abar := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [card_ker_πbar, card_Abar, card_M2bar]
  · rw [Subgroup.disjoint_def]
    intro k hU hA
    exact injOn_Abar hA (MonoidHom.mem_ker.mp hU)

variable {G : Type} [Group G] [Finite G]

theorem exists_permEquiv_of_setting
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    ∃ (ι : Fin 7 → Fin 23) (ζ : ↥M2 ≃* ↥(stabilizer ↥NativeSporadic.M23 heptad₀)),
      Function.Injective ι ∧ (∀ i, ι i ∈ heptad₀) ∧ IsPermEquiv M2 π ι ζ := by
  obtain ⟨π', -, -, hker, -, -, hU16, -, -, -, hπ'⟩ := exists_rho_of_setting hQ hyp hM23 hS
  obtain ⟨τ, -, φ, hφ⟩ := exists_mulEquiv_Ubar_of_setting hQ hyp hM23 hS
  obtain ⟨A, hA⟩ := exists_isComplement_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hUM2 : pCoreOf 2 M2 ≤ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2
  set Y := (pCoreOf 2 M2).subgroupOf M2 with hY
  have hYn : Y.Normal := hker ▸ π'.normal_ker
  set θ : ↥A →* A7 := (MulAut.conjNormal (H := alternatingGroup (Fin 7)) τ).toMonoidHom.comp
    (π'.comp A.subtype) with hθ
  have hθapp : ∀ a : ↥A, ((θ a : A7) : Perm (Fin 7)) = τ * π a * τ⁻¹ := fun a => by
    have h := MulAut.conjNormal_apply (H := alternatingGroup (Fin 7)) τ (π' a)
    rw [hπ'] at h
    exact h
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have h0 : (MulAut.conjNormal (H := alternatingGroup (Fin 7)) τ) (π' a) = 1 :=
      MonoidHom.mem_ker.mp ha
    have h1 : π' (a : ↥M2) = 1 :=
      (map_eq_one_iff _ (MulAut.conjNormal (H := alternatingGroup (Fin 7)) τ).injective).mp h0
    have hY' : (a : ↥M2) ∈ Y := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr h1
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.disjoint_def.mp hA.disjoint hY' a.2))
  have hcardA : Nat.card A = 2520 := by
    have h := hA.card_mul_card
    have hY16 : Nat.card Y = 16 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM2).toEquiv).trans hU16
    have hM2 : Nat.card M2 = 40320 := by
      have h1 := card_map_mul_card_inf hS.ker_eq (le_refl M2)
      rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, hS.range_eq,
        CFSG.Quasithin.H13.card_alternatingGroup_seven, inf_of_le_right hUM2, hU16] at h1
      exact h1.symm
    rw [hY16, hM2] at h
    omega
  set θe : ↥A ≃* A7 := MulEquiv.ofBijective θ (hθinj.bijective_of_nat_card_le (by
    rw [hcardA, CFSG.QuasithinUnique.L246.C123.card_A7])) with hθe
  set fg : ↥A ≃* ↥Abar := θe.trans AbarEquiv.symm with hfgdef
  set fn : ↥Y ≃* ↥Ubar := (Subgroup.subgroupOfEquivOfLe hUM2).trans φ with hfndef
  have hfg : ∀ a : ↥A, πbar ((fg a : ↥Abar) : ↥M2bar) = θ a := fun a => πbar_sbar (θ a)
  have hAle : A ≤ Subgroup.normalizer (Y : Set ↥M2) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hAbarle : Abar ≤ Subgroup.normalizer ((Ubar : Subgroup ↥M2bar) : Set ↥M2bar) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcompat : ∀ a : ↥A, ((Y.normalizerMonoidHom.comp (Subgroup.inclusion hAle)) a).trans fn =
      fn.trans (((Ubar : Subgroup ↥M2bar).normalizerMonoidHom.comp
        (Subgroup.inclusion hAbarle)) (fg a)) := by
    intro a
    refine MulEquiv.ext fun y => ?_
    have hmu : ((a : ↥M2) : G) * ((Subgroup.subgroupOfEquivOfLe hUM2 y : ↥(pCoreOf 2 M2)) : G) *
        ((a : ↥M2) : G)⁻¹ ∈ pCoreOf 2 M2 :=
      Subgroup.mem_subgroupOf.mp ((Y.normalizerMonoidHom.comp (Subgroup.inclusion hAle)) a y).2
    have e1 : Subgroup.subgroupOfEquivOfLe hUM2
        ((Y.normalizerMonoidHom.comp (Subgroup.inclusion hAle)) a y) = ⟨_, hmu⟩ := Subtype.ext rfl
    have e3 : fn ((Y.normalizerMonoidHom.comp (Subgroup.inclusion hAle)) a y) =
        ρbar (θ a) (fn y) := by
      rw [hfndef, MulEquiv.trans_apply, MulEquiv.trans_apply, e1]
      exact hφ (a : ↥M2) (Subgroup.subgroupOfEquivOfLe hUM2 y) hmu (θ a) (hθapp a)
    change fn ((Y.normalizerMonoidHom.comp (Subgroup.inclusion hAle)) a y) = _
    rw [e3]
    apply Subtype.ext
    rw [ρbar_apply_of_πbar (hfg a)]
    rfl
  set ζ : ↥M2 ≃* ↥M2bar := (SemidirectProduct.mulEquivSubgroup hA).symm.trans
    ((SemidirectProduct.congr fn fg hcompat).trans
      (SemidirectProduct.mulEquivSubgroup isComplement'_Ubar_Abar)) with hζdef
  refine ⟨fun i => ιbar (τ i), ζ, ιbar_injective.comp τ.injective, fun i => ιbar_mem _, ?_⟩
  intro g i
  set x := (SemidirectProduct.mulEquivSubgroup hA).symm g with hx
  have hgx : g = (x.left : ↥M2) * (x.right : ↥M2) := by
    rw [← SemidirectProduct.mulEquivSubgroup_apply hA x, hx, MulEquiv.apply_symm_apply]
  have hζ : ζ g = (fn x.left : ↥M2bar) * (fg x.right : ↥M2bar) := by
    rw [hζdef, MulEquiv.trans_apply, MulEquiv.trans_apply, ← hx,
      SemidirectProduct.mulEquivSubgroup_apply]
    rfl
  have hπg : π g = π (x.right : ↥M2) := by
    have h1 : π (x.left : ↥M2) = 1 := by
      rw [← MonoidHom.mem_ker, hS.ker_eq]
      exact x.left.2
    rw [hgx, map_mul, h1, one_mul]
  have hl : ∀ j, (((fn x.left : ↥M2bar) : ↥NativeSporadic.M23) : Perm (Fin 23)) (ιbar j) =
      ιbar j := by
    intro j
    rw [← πbar_apply, MonoidHom.mem_ker.mp (fn x.left).2, Perm.one_apply]
  have hr : (((fg x.right : ↥M2bar) : ↥NativeSporadic.M23) : Perm (Fin 23)) (ιbar (τ i)) =
      ιbar (τ (π x.right i)) := by
    rw [← πbar_apply, hfg, hθapp]
    simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply]
  show (((ζ g : ↥M2bar) : ↥NativeSporadic.M23) : Perm (Fin 23)) (ιbar (τ i)) = ιbar (τ (π g i))
  rw [hζ, Subgroup.coe_mul, Subgroup.coe_mul, Perm.mul_apply, hr, hl, hπg]

end CFSG.Quasithin.H13

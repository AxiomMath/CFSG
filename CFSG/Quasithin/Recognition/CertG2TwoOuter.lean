module

public import CFSG.Quasithin.Recognition.CertG2Two
public import CFSG.Quasithin.Recognition.CertTwoLocalIndexTwo
public import CFSG.Quasithin.Recognition.CertU33Phi

public section

namespace CFSG.Quasithin

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree

section Rho

variable {k : Type} [Field k]

@[expose] noncomputable def g2Rho
    (h2 : (2 : k) = 0) : ModGL Tag.G2 k :=
  (g2Hom h2 (u33El "asy"))⁻¹ * g2L 1

theorem g2Rho_conj_gen
    (h2 : (2 : k) = 0) (j : Fin 5) :
    g2Rho h2 * g2Img j * (g2Rho h2)⁻¹ = g2Hom h2 (u33El (u33PiConjW.getD j "")) := by
  have hb := g2L_one_conj h2 j.2
  rw [← g2Hom_mk h2 (u33Word (g2ConjStrings.getD (5 * 1 + (j : ℕ)) "")),
    ← u33El_eq_mk] at hb
  have hb' : g2L 1 * g2Img j * (g2L 1)⁻¹ =
      g2Hom h2 (u33El (g2ConjStrings.getD (5 * 1 + (j : ℕ)) "")) := hb
  have e : g2Rho h2 * g2Img j * (g2Rho h2)⁻¹ =
      (g2Hom h2 (u33El "asy"))⁻¹ * (g2L 1 * g2Img j * (g2L 1)⁻¹) * g2Hom h2 (u33El "asy") := by
    simp only [g2Rho, mul_inv_rev, inv_inv, mul_assoc]
  rw [e, hb', ← map_inv, ← map_mul, ← map_mul, u33_conjB_G j j.2]

theorem g2Rho_conj
    (h2 : (2 : k) = 0) (x : U33G) :
    g2Rho h2 * g2Hom h2 x * (g2Rho h2)⁻¹ = g2Hom h2 (u33Phi' x) := by
  have h : (MulAut.conj (g2Rho h2)).toMonoidHom.comp (g2Hom h2) =
      (g2Hom h2).comp u33Phi'.toMonoidHom := by
    refine PresentedGroup.ext fun j => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, g2Hom_of, MulAut.conj_apply,
      u33Phi'_gen]
    exact g2Rho_conj_gen h2 j
  simpa [MulAut.conj_apply] using DFunLike.congr_fun h x

theorem g2Rho_sq
    (h2 : (2 : k) = 0) : g2Rho h2 * g2Rho h2 = 1 := by
  have hbb : g2L 1 * g2L 1 = (1 : ModGL Tag.G2 k) := g2L_mul_self h2 (by norm_num)
  have hR : g2Rho h2 = (g2Hom h2 (u33El "asy"))⁻¹ * g2L 1 := rfl
  have h1 : g2Rho h2 * (g2Hom h2 (u33El "asy"))⁻¹ * (g2Rho h2)⁻¹ =
      g2Hom h2 (u33Phi' (u33El "asy")⁻¹) := by
    rw [← map_inv, g2Rho_conj h2]
  have e : u33Phi' (u33El "asy")⁻¹ * (u33El "asy")⁻¹ = 1 := by
    rw [map_inv, ← mul_inv_rev, u33_asy_phi, inv_one]
  calc g2Rho h2 * g2Rho h2 = g2Rho h2 * ((g2Hom h2 (u33El "asy"))⁻¹ * g2L 1) := by rw [← hR]
    _ = (g2Rho h2 * (g2Hom h2 (u33El "asy"))⁻¹ * (g2Rho h2)⁻¹) * g2Rho h2 * g2L 1 := by group
    _ = g2Hom h2 (u33Phi' (u33El "asy")⁻¹) * ((g2Hom h2 (u33El "asy"))⁻¹ * g2L 1) * g2L 1 := by
        rw [h1, ← hR]
    _ = g2Hom h2 (u33Phi' (u33El "asy")⁻¹ * (u33El "asy")⁻¹) * (g2L 1 * g2L 1) := by
        simp only [map_mul, map_inv, mul_assoc]
    _ = 1 := by rw [e, hbb, map_one, mul_one]

theorem g2Rho_core
    (h2 : (2 : k) = 0) : IndexTwoCore (g2Hom h2) (g2Rho h2) u33Phi' :=
  ⟨g2Rho_sq h2, fun x => g2Rho_conj h2 x⟩

theorem g2L_one_eq
    (h2 : (2 : k) = 0) :
    (g2L 1 : ModGL Tag.G2 k) = g2Hom h2 (u33El "asy") * g2Rho h2 := by
  show _ = g2Hom h2 (u33El "asy") * ((g2Hom h2 (u33El "asy"))⁻¹ * g2L 1)
  rw [mul_inv_cancel_left]

end Rho

section Cover

variable {k : Type} [Field k]

theorem range_g2Hom_le
    (h2 : (2 : k) = 0) : (g2Hom h2).range ≤ adjointGroup Tag.G2 k := by
  rw [range_g2Hom]
  exact (Subgroup.closure_le _).2 (by
    rintro _ ⟨j, rfl⟩
    exact constPinned_mem_adjointGroup _)

theorem g2Rho_mem
    (h2 : (2 : k) = 0) : g2Rho h2 ∈ adjointGroup Tag.G2 k :=
  Subgroup.mul_mem _ (Subgroup.inv_mem _ (range_g2Hom_le h2 ⟨_, rfl⟩)) (g2L_mem_adjointGroup 1)

theorem g2_cover_mod
    (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1) {g : ModGL Tag.G2 k}
    (hg : g ∈ adjointGroup Tag.G2 k) : g ∈ (g2Hom h2).range ∨ g * g2Rho h2 ∈ (g2Hom h2).range := by
  have C := g2Rho_core h2
  have hext : ∀ g : ModGL Tag.G2 k, g ∈ C.ext ⊤ (fun _ _ => Subgroup.mem_top _) ↔
      g ∈ (g2Hom h2).range ∨ g * g2Rho h2 ∈ (g2Hom h2).range := by
    intro g
    rw [C.mem_ext, ← MonoidHom.range_eq_map]
  have hle : adjointGroup Tag.G2 k ≤ C.ext ⊤ (fun _ _ => Subgroup.mem_top _) := by
    rw [adjointGroup_G2_eq hk2]
    refine (Subgroup.closure_le _).2 ?_
    rintro x (rfl | ⟨⟨t, ht⟩, rfl⟩)
    · exact Subgroup.one_mem _
    · rw [SetLike.mem_coe, hext]
      have h0 : (g2L 0 : ModGL Tag.G2 k) ∈ (g2Hom h2).range := by
        rw [g2L_zero_eq_img]; exact g2Img_mem_range h2 2
      have hb : g2L 1 * g2Rho h2 = (g2Hom h2 (u33El "asy") : ModGL Tag.G2 k) := by
        calc g2L 1 * g2Rho h2 = g2Hom h2 (u33El "asy") * g2Rho h2 * g2Rho h2 := by
              rw [← g2L_one_eq h2]
          _ = g2Hom h2 (u33El "asy") := by rw [mul_assoc, g2Rho_sq, mul_one]
      have hd : g2L 3 * g2Rho h2 = g2Hom h2 (u33El "asy") * g2Hom h2 (u33Phi' (u33GenPG 4)) := by
        have e1 : (g2L 3 : ModGL Tag.G2 k) = g2L 1 * g2Img 4 := g2L_three_eq h2
        have e2 : g2Img 4 = g2Hom h2 (u33GenPG 4) := by
          have : u33GenPG 4 = PresentedGroup.of (4 : Fin 5) := u33GenPG_of 4
          rw [this, g2Hom_of]
        calc g2L 3 * g2Rho h2 = g2Hom h2 (u33El "asy") * g2Rho h2 * g2Hom h2 (u33GenPG 4) *
              g2Rho h2 := by rw [e1, e2, ← g2L_one_eq h2]
          _ = g2Hom h2 (u33El "asy") * (g2Rho h2 * g2Hom h2 (u33GenPG 4) * g2Rho h2) := by
              simp only [mul_assoc]
          _ = _ := by rw [C.conj']
      interval_cases t
      · exact Or.inl h0
      · exact Or.inr (hb ▸ ⟨_, rfl⟩)
      · exact Or.inl (g2L_two_mem_range h2)
      · refine Or.inr ?_
        show g2L 3 * g2Rho h2 ∈ _
        rw [hd]
        exact (g2Hom h2).range.mul_mem ⟨_, rfl⟩ ⟨_, rfl⟩
  exact (hext g).1 (hle hg)

end Cover

section Group

variable {k : Type} [Field k]

abbrev G2Group (k : Type) [Field k] : Type := ↥(adjointGroup Tag.G2 k)

@[expose] noncomputable def g2HomC
    (h2 : (2 : k) = 0) : U33G →* G2Group k :=
  (g2Hom h2).codRestrict (adjointGroup Tag.G2 k) fun x => range_g2Hom_le h2 ⟨x, rfl⟩

@[expose] noncomputable def g2RhoC
    (h2 : (2 : k) = 0) : G2Group k := ⟨g2Rho h2, g2Rho_mem h2⟩

theorem g2HomC_injective
    (h2 : (2 : k) = 0) : Function.Injective (g2HomC h2) :=
  fun _ _ h => g2Hom_injective h2 (congrArg Subtype.val h)

theorem finite_g2Group [Finite k] : Finite (G2Group k) := by
  have : Finite (Module.End k (RootModule Tag.G2 k)) := Module.finite_of_finite k
  have : Finite (ModGL Tag.G2 k) := by infer_instance
  infer_instance

theorem g2IndexTwoData
    (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1) :
    IndexTwoData (g2HomC h2) (g2RhoC h2) u33Phi' where
  sq := Subtype.ext (g2Rho_sq h2)
  conj x := Subtype.ext (g2Rho_conj h2 x)
  inj := g2HomC_injective h2
  cover g := by
    rcases g2_cover_mod h2 hk2 g.2 with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact Or.inl ⟨x, Subtype.ext hx⟩
    · exact Or.inr ⟨x, Subtype.ext hx⟩
  outer := u33Phi'_not_inner

theorem g2_twoLocalPairProp
    (k : Type) [Field k] [Finite k] (hk : Nat.card k = 2) :
    TwoLocalPairProp (G2Group k) := by
  have h2 := two_eq_zero_of_card_two hk
  have hk2 := eq_zero_or_eq_one_of_card_two hk
  have : Finite (G2Group k) := finite_g2Group
  exact (g2IndexTwoData h2 hk2).twoLocalPairProp u33Extra u33Phi'_T u33Phi'_A u33Phi'_B
    u33Phi'_PA u33Phi'_PB

end Group

end CFSG.Quasithin

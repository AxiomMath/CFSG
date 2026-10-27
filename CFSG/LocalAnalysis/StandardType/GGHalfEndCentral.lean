module

public import CFSG.LocalAnalysis.StandardType.GGHalfZpowers
public import CFSG.LocalAnalysis.StandardType.GGHalfAutLevi
public import CFSG.LocalAnalysis.StandardType.GGHalfAux
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem centralizer_zpowers_eq' {G : Type} [Group G] (c : G) :
    Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    exact (hx c (Subgroup.mem_zpowers c)).symm
  · intro hx g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left (show Commute c x from hx.symm) k)).eq

private theorem centralizer_singleton_eq_of_zpowers_eq' {G : Type} [Group G] {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  rw [← centralizer_zpowers_eq' a, ← centralizer_zpowers_eq' b, h]

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

include h

theorem endT₂_conj_wElt : endT₂ φ₂ * wElt φ₂ * (endT₂ φ₂)⁻¹ = (wElt φ₂)⁻¹ := by
  have hW : (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩)⁻¹ =
      weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ :=
    inv_eq_of_mul_eq_one_right
      (weylRep_mul_self (F := F2) (m := m + 1 + 1) gf2_two ⟨m + 1, by omega⟩)
  have hmain : weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ *
        omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ *
        (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩)⁻¹ =
      (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ := by
    rw [hW, weylRep_mul_omegaBlock_mul_weylRep]
  calc endT₂ φ₂ * wElt φ₂ * (endT₂ φ₂)⁻¹
      = φ₂ (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩) *
          φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) *
          (φ₂ (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩))⁻¹ := by
        rw [endT₂, wElt]
    _ = φ₂ (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ *
          omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ *
          (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩)⁻¹) := by
        rw [map_mul, map_mul, map_inv]
    _ = φ₂ ((omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹) := by rw [hmain]
    _ = (φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩))⁻¹ := by rw [map_inv]
    _ = (wElt φ₂)⁻¹ := by rw [wElt]

theorem zpowers_conj_endT₂_x :
    Subgroup.zpowers (endT₂ φ₂ * x * (endT₂ φ₂)⁻¹) = Subgroup.zpowers x := by
  have hxw : Subgroup.zpowers x = Subgroup.zpowers (wElt φ₂) := by
    simpa only [wElt] using h.zpowers_x
  have hf : (MulAut.conj (endT₂ φ₂)).toMonoidHom (wElt φ₂) = (wElt φ₂)⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact endT₂_conj_wElt h
  calc Subgroup.zpowers (endT₂ φ₂ * x * (endT₂ φ₂)⁻¹)
      = (Subgroup.zpowers x).map (MulAut.conj (endT₂ φ₂)).toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    _ = (Subgroup.zpowers (wElt φ₂)).map (MulAut.conj (endT₂ φ₂)).toMonoidHom := by rw [hxw]
    _ = Subgroup.zpowers ((MulAut.conj (endT₂ φ₂)).toMonoidHom (wElt φ₂)) := by
        rw [MonoidHom.map_zpowers]
    _ = Subgroup.zpowers ((wElt φ₂)⁻¹) := by rw [hf]
    _ = Subgroup.zpowers (wElt φ₂) := by rw [Subgroup.zpowers_inv]
    _ = Subgroup.zpowers x := hxw.symm

theorem endT₂_comm_J : ∀ j ∈ J, endT₂ φ₂ * j = j * endT₂ φ₂ := by
  intro j hj
  have hJ : J = (φ₂.comp (slUpper2Hom m)).range := by
    rw [← h.coords.rangeJ, h.coords.agree]
  rw [hJ] at hj
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hj
  have hfix : ∀ i ∈ ({i : Fin (m + 1 + 1 + 1) | i.val ≤ m} : Set (Fin (m + 1 + 1 + 1))),
      (Equiv.swap ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc)
        ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ)) i = i := by
    intro i hi
    simp only [Set.mem_setOf_eq] at hi
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;>
      (intro hh
       have hv := congrArg Fin.val hh
       simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk] at hv
       omega)
  have hmem : slUpper2Hom m s ∈
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val ≤ m} := by
    rw [← range_slUpper2Hom m]
    exact ⟨s, rfl⟩
  have hcomm := commute_slPerm_slOn (N := m + 1 + 1 + 1)
    (π := Equiv.swap ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc)
      ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ))
    (S := {i : Fin (m + 1 + 1 + 1) | i.val ≤ m}) hfix hmem
  rw [endT₂, weylRep_eq_slPerm, MonoidHom.comp_apply, ← map_mul, ← map_mul, hcomm]

theorem endT₂_normalizes_L : L.map (MulAut.conj (endT₂ φ₂)).toMonoidHom = L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm3 : 3 ≤ m := by have := h.nbr.2.2.1; omega
  have hJ₂ : J = (φ₂.comp (slUpper2Hom m)).range := by
    rw [← h.coords.rangeJ, h.coords.agree]
  have hJL : J ≤ L := by
    calc J = (φ₁.comp (slLower2Hom m)).range := h.coords.rangeJ.symm
      _ = (slLower2Hom m).range.map φ₁ := MonoidHom.range_comp φ₁ (slLower2Hom m)
      _ ≤ (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)).map φ₁ :=
            Subgroup.map_mono le_top
      _ = φ₁.range := (MonoidHom.range_eq_map φ₁).symm
      _ = L := h.coords.range₁
  have hc : Subgroup.centralizer ({endT₂ φ₂ * x * (endT₂ φ₂)⁻¹} : Set G) =
      Subgroup.centralizer ({x} : Set G) :=
    centralizer_singleton_eq_of_zpowers_eq' h.zpowers_conj_endT₂_x
  have hA : LargeEvenPComponent 3
      (Subgroup.centralizer ({endT₂ φ₂ * x * (endT₂ φ₂)⁻¹} : Set G))
      (L.map (MulAut.conj (endT₂ φ₂)).toMonoidHom) :=
    largeEvenPComponent_conj_centralizer_singleton h.pComponent_L (endT₂ φ₂)
  rw [hc] at hA
  have hperf : J ≤ ⁅J, J⁆ := by
    have hJeq : J = (slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val}).map φ₁ := by
      rw [← h.coords.rangeJ, MonoidHom.range_comp, range_slLower2Hom]
    rw [hJeq, ← Subgroup.map_commutator]
    apply Subgroup.map_mono
    apply slOn_perfect
    refine ⟨⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Fin.val_mk]; omega
    · simp only [Set.mem_setOf_eq, Fin.val_mk]; omega
    · simp only [Set.mem_setOf_eq, Fin.val_mk]; omega
    · exact Fin.ne_of_val_ne (by norm_num)
    · exact Fin.ne_of_val_ne (by norm_num)
    · exact Fin.ne_of_val_ne (by norm_num)
  have hgJ : uElt φ₂ ∈ J := by
    rw [hJ₂]
    exact MonoidHom.mem_range.mpr ⟨omegaBlock m ⟨0, by omega⟩, by
      rw [MonoidHom.comp_apply, slUpper2Hom_omegaBlock, uElt]⟩
  have hg1 : uElt φ₂ ≠ 1 := by
    rw [uElt]
    intro hh
    exact omegaBlock_ne_one (m + 1 + 1) ⟨0, by omega⟩
      (h.coords.inj₂ (by simpa using hh))
  have hg3 : (uElt φ₂) ^ 3 = 1 := by
    rw [uElt, ← map_pow, omegaBlock_pow_three, map_one]
  have hPA : J ≤ L.map (MulAut.conj (endT₂ φ₂)).toMonoidHom := by
    intro j hj
    refine ⟨j, hJL hj, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h.endT₂_comm_J j hj, mul_assoc, mul_inv_cancel, mul_one]
  exact eq_of_pComponents_of_perfect_common hA h.pComponent_L hPA hJL hperf hgJ hg1 hg3

theorem endT₂_central : ∀ l ∈ L, endT₂ φ₂ * l = l * endT₂ φ₂ := by
  have hm : 2 ≤ m := by have := h.nbr.2.2.1; omega
  have hnorm := h.endT₂_normalizes_L
  have hrange : ((MulAut.conj (endT₂ φ₂)).toMonoidHom.comp φ₁).range = φ₁.range := by
    rw [MonoidHom.range_comp, h.coords.range₁, hnorm]
  obtain ⟨β, hβ⟩ := exists_mulAut_of_range_eq
    (ψ := (MulAut.conj (endT₂ φ₂)).toMonoidHom.comp φ₁) (ψ' := φ₁)
    ((MulAut.conj (endT₂ φ₂)).injective.comp h.coords.inj₁) h.coords.inj₁ hrange
  have hTT : endT₂ φ₂ * endT₂ φ₂ = 1 := by
    rw [endT₂, ← map_mul,
      weylRep_mul_self (F := F2) (m := m + 1 + 1) gf2_two (⟨m + 1, by omega⟩), map_one]
  have h1 : ∀ s, β (slLower2Hom m s) = slLower2Hom m s := by
    intro s
    apply h.coords.inj₁
    rw [hβ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hmem : φ₁ (slLower2Hom m s) ∈ J := by
      rw [← h.coords.rangeJ]
      exact MonoidHom.mem_range.mpr ⟨s, rfl⟩
    rw [h.endT₂_comm_J (φ₁ (slLower2Hom m s)) hmem, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : β (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) =
      omegaBlock (m + 1 + 1) ⟨0, by omega⟩ := by
    apply h.coords.inj₁
    rw [hβ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨-, -, -, -, -, -, -, hyK, -, -⟩ := h.basic
    have hv : φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ∈ Subgroup.zpowers y := by
      rw [h.zpowers_y]; exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hTK : endT₂ φ₂ ∈ K := by
      rw [← h.coords.range₂]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hyT : y * endT₂ φ₂ = endT₂ φ₂ * y := hyK (endT₂ φ₂) hTK
    have hcomm : endT₂ φ₂ * φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) =
        φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) * endT₂ φ₂ := by
      rw [← hk]
      exact (Commute.zpow_left (show Commute y (endT₂ φ₂) from hyT) k).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have h3 : β * β = 1 := by
    apply MulEquiv.ext
    intro s
    apply h.coords.inj₁
    change φ₁ (β (β s)) = φ₁ s
    rw [hβ, MonoidHom.comp_apply, hβ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hTinv : (endT₂ φ₂)⁻¹ = endT₂ φ₂ := inv_eq_of_mul_eq_one_right hTT
    rw [hTinv]
    calc endT₂ φ₂ * (endT₂ φ₂ * φ₁ s * endT₂ φ₂) * endT₂ φ₂
        = (endT₂ φ₂ * endT₂ φ₂) * φ₁ s * (endT₂ φ₂ * endT₂ φ₂) := by group
      _ = φ₁ s := by rw [hTT]; group
  have hβeq : β = 1 := mulAut_eq_one_of_levi hm β h1 h2 h3
  intro l hl
  rw [← h.coords.range₁] at hl
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hl
  have hfix : endT₂ φ₂ * φ₁ s * (endT₂ φ₂)⁻¹ = φ₁ s := by
    have hthis := hβ s
    rw [hβeq] at hthis
    simpa using hthis.symm
  rw [← mul_inv_eq_iff_eq_mul]
  exact hfix

end GGHalfCtx

end CFSG.StandardType

end

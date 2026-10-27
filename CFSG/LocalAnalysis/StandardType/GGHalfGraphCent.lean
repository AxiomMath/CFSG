module

public import CFSG.LocalAnalysis.StandardType.GGHalfEndNodes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

@[expose] noncomputable def slE (c d : Fin 6) : SpecialLinearGroup (Fin 6) F2 :=
  if h : c = d then 1 else SpecialLinearGroup.transvection h 1

@[expose] def ggHalfSLoc : Fin 6 → Fin 6 := ![1, 0, 5, 4, 3, 2]

namespace GGHalfCtx

private theorem ggHalfGraphCent_centralizer_singleton_eq_of_zpowers_eq {G : Type} [Group G]
    {a b : G} (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have key : ∀ c : G, Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    intro c
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx
      exact (hx c (Subgroup.mem_zpowers c)).symm
    · intro hx g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact ((Commute.zpow_left (show Commute c x from hx.symm) k)).eq
  rw [← key a, ← key b, h]

private theorem ggHalfGraphCent_sZero_comm_J {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) :
    ∀ j ∈ J, sZero φ₁ * j = j * sZero φ₁ := by
  intro j hj
  have hJ : J = (φ₁.comp (slLower2Hom m)).range := h.coords.rangeJ.symm
  rw [hJ] at hj
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hj
  have hfix : ∀ i ∈ ({i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} : Set (Fin (m + 1 + 1 + 1))),
      (Equiv.swap ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc)
        ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ)) i = i := by
    intro i hi
    simp only [Set.mem_setOf_eq] at hi
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;>
      (intro hh
       have hv := congrArg Fin.val hh
       simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk] at hv
       omega)
  have hmem : slLower2Hom m s ∈
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} := by
    rw [← range_slLower2Hom m]
    exact ⟨s, rfl⟩
  have hcomm := commute_slPerm_slOn (N := m + 1 + 1 + 1)
    (π := Equiv.swap ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc)
      ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ))
    (S := {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val}) hfix hmem
  rw [sZero, weylRep_eq_slPerm, MonoidHom.comp_apply, ← map_mul, ← map_mul, hcomm]

private theorem ggHalfGraphCent_zpowers_conj_sZero_y {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) :
    Subgroup.zpowers (sZero φ₁ * y * (sZero φ₁)⁻¹) = Subgroup.zpowers y := by
  have hyv : Subgroup.zpowers y = Subgroup.zpowers (vElt φ₁) := by
    simpa only [vElt] using h.zpowers_y
  have hf : (MulAut.conj (sZero φ₁)).toMonoidHom (vElt φ₁) = (vElt φ₁)⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h.s0_v
  calc Subgroup.zpowers (sZero φ₁ * y * (sZero φ₁)⁻¹)
      = (Subgroup.zpowers y).map (MulAut.conj (sZero φ₁)).toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    _ = (Subgroup.zpowers (vElt φ₁)).map (MulAut.conj (sZero φ₁)).toMonoidHom := by rw [hyv]
    _ = Subgroup.zpowers ((MulAut.conj (sZero φ₁)).toMonoidHom (vElt φ₁)) := by
        rw [MonoidHom.map_zpowers]
    _ = Subgroup.zpowers ((vElt φ₁)⁻¹) := by rw [hf]
    _ = Subgroup.zpowers (vElt φ₁) := by rw [Subgroup.zpowers_inv]
    _ = Subgroup.zpowers y := hyv.symm

private theorem ggHalfGraphCent_mulAut_eq_one_of_levi_upper {m : ℕ} (hm : 2 ≤ m)
    (β : MulAut (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))
    (h1 : ∀ s, β (slUpper2Hom m s) = slUpper2Hom m s)
    (h2 : β (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) =
      omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)
    (h3 : β * β = 1) : β = 1 := by
  let ρ : Equiv.Perm (Fin (m + 1 + 1 + 1)) := Fin.revPerm
  let P : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := slPerm gf2_two ρ
  let conjP : MulAut (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) := MulAut.conj P
  have hρρ : ρ * ρ = 1 := by
    ext i
    rw [Equiv.Perm.mul_apply, Fin.revPerm_apply, Fin.revPerm_apply, Fin.rev_rev]
    rfl
  have hPP : P * P = 1 := by
    have h := congrArg (slPerm gf2_two) hρρ
    simpa only [map_mul, map_one] using h
  have hconj2 : conjP * conjP = 1 := by
    have h := map_mul MulAut.conj P P
    rw [hPP, map_one] at h
    exact h.symm
  have h1' : ∀ s, (conjP * β * conjP) (slLower2Hom m s) = slLower2Hom m s := by
    intro s
    have hmemLower : slLower2Hom m s ∈
        slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} := by
      rw [← range_slLower2Hom m]
      exact ⟨s, rfl⟩
    have hsub : ρ '' {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} ⊆
        {i : Fin (m + 1 + 1 + 1) | i.val ≤ m} := by
      rintro i ⟨j, hj, rfl⟩
      simp only [Set.mem_setOf_eq] at hj ⊢
      rw [Fin.revPerm_apply, Fin.val_rev]
      omega
    have hmemMap : conjP (slLower2Hom m s) ∈
        (slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val}).map
          conjP.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨_, hmemLower, rfl⟩
    rw [slOn_map_conj_slPerm ρ {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val}] at hmemMap
    have hmemUp : conjP (slLower2Hom m s) ∈
        slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val ≤ m} :=
      slOn_mono hsub hmemMap
    rw [← range_slUpper2Hom m] at hmemUp
    obtain ⟨s', hs'⟩ := MonoidHom.mem_range.mp hmemUp
    show conjP (β (conjP (slLower2Hom m s))) = slLower2Hom m s
    rw [← hs', h1 s', hs']
    rw [← MulAut.mul_apply, hconj2, MulAut.one_apply]
  have hρ0 : ρ (0 : Fin (m + 1 + 1 + 1)) =
      (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ := by
    rw [Fin.revPerm_apply, Fin.rev_zero]
    rfl
  have hρ1 : ρ (1 : Fin (m + 1 + 1 + 1)) =
      (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc := by
    apply Fin.ext
    rw [Fin.revPerm_apply, Fin.val_rev, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    simp only [Fin.val_castSucc, Fin.val_mk]
    omega
  have hρlastC : ρ ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc) =
      (0 : Fin (m + 1 + 1)).succ := by
    apply Fin.ext
    rw [Fin.revPerm_apply, Fin.val_rev]
    simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_succ, Fin.val_zero]
    omega
  have hρlastS : ρ ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ) =
      (0 : Fin (m + 1 + 1)).castSucc := by
    apply Fin.ext
    rw [Fin.revPerm_apply, Fin.val_rev]
    simp only [Fin.val_succ, Fin.val_mk, Fin.val_castSucc, Fin.val_zero]
    omega
  have hconj0 : conjP (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) =
      (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)⁻¹ := by
    show MulAut.conj P (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) = _
    rw [MulAut.conj_apply]
    exact slPerm_conj_omegaBlock_inv ρ hρ0 hρ1
  have hconjLast : conjP (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) =
      (omegaBlock (m + 1 + 1) ⟨0, by omega⟩)⁻¹ := by
    show MulAut.conj P (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) = _
    rw [MulAut.conj_apply]
    exact slPerm_conj_omegaBlock_inv ρ hρlastC hρlastS
  have h2' : (conjP * β * conjP) (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) =
      omegaBlock (m + 1 + 1) ⟨0, by omega⟩ := by
    show conjP (β (conjP (omegaBlock (m + 1 + 1) ⟨0, by omega⟩))) =
      omegaBlock (m + 1 + 1) ⟨0, by omega⟩
    rw [hconj0, map_inv, h2, map_inv, hconjLast]
    exact inv_inv _
  have h3' : (conjP * β * conjP) * (conjP * β * conjP) = 1 := by
    calc (conjP * β * conjP) * (conjP * β * conjP)
        = conjP * β * (conjP * conjP) * β * conjP := by group
      _ = conjP * β * 1 * β * conjP := by rw [hconj2]
      _ = conjP * (β * β) * conjP := by group
      _ = conjP * 1 * conjP := by rw [h3]
      _ = conjP * conjP := by group
      _ = 1 := hconj2
  have hβ' : conjP * β * conjP = 1 :=
    mulAut_eq_one_of_levi hm (conjP * β * conjP) h1' h2' h3'
  have hfin : conjP * (conjP * β * conjP) * conjP = β := by
    calc conjP * (conjP * β * conjP) * conjP
        = (conjP * conjP) * β * (conjP * conjP) := by group
      _ = 1 * β * 1 := by rw [hconj2]
      _ = β := by group
  calc β = conjP * (conjP * β * conjP) * conjP := hfin.symm
    _ = conjP * 1 * conjP := by rw [hβ']
    _ = conjP * conjP := by group
    _ = 1 := hconj2

private theorem ggHalfGraphCent_sZero_normalizes_K {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) :
    K.map (MulAut.conj (sZero φ₁)).toMonoidHom = K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm3 : 3 ≤ m := by have := h.nbr.2.2.1; omega
  have hJ₂ : J = (φ₂.comp (slUpper2Hom m)).range := by
    rw [← h.coords.rangeJ, h.coords.agree]
  have hJK : J ≤ K := by
    calc J = (φ₂.comp (slUpper2Hom m)).range := hJ₂
      _ = (slUpper2Hom m).range.map φ₂ := MonoidHom.range_comp φ₂ (slUpper2Hom m)
      _ ≤ (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)).map φ₂ :=
            Subgroup.map_mono le_top
      _ = φ₂.range := (MonoidHom.range_eq_map φ₂).symm
      _ = K := h.coords.range₂
  have hc : Subgroup.centralizer ({sZero φ₁ * y * (sZero φ₁)⁻¹} : Set G) =
      Subgroup.centralizer ({y} : Set G) :=
    ggHalfGraphCent_centralizer_singleton_eq_of_zpowers_eq
      (h := ggHalfGraphCent_zpowers_conj_sZero_y (h := h))
  have hA : LargeEvenPComponent 3
      (Subgroup.centralizer ({sZero φ₁ * y * (sZero φ₁)⁻¹} : Set G))
      (K.map (MulAut.conj (sZero φ₁)).toMonoidHom) :=
    largeEvenPComponent_conj_centralizer_singleton (h := h.pComponent_K) (sZero φ₁)
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
  have hPA : J ≤ K.map (MulAut.conj (sZero φ₁)).toMonoidHom := by
    intro j hj
    refine ⟨j, hJK hj, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [ggHalfGraphCent_sZero_comm_J h j hj, mul_assoc, mul_inv_cancel, mul_one]
  exact eq_of_pComponents_of_perfect_common hA h.pComponent_K hPA hJK hperf hgJ hg1 hg3

theorem sZero_central {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) : ∀ k ∈ K, sZero φ₁ * k = k * sZero φ₁ := by
  have hm : 2 ≤ m := by have := h.nbr.2.2.1; omega
  have hnorm := ggHalfGraphCent_sZero_normalizes_K (h := h)
  have hrange : ((MulAut.conj (sZero φ₁)).toMonoidHom.comp φ₂).range = φ₂.range := by
    rw [MonoidHom.range_comp, h.coords.range₂, hnorm]
  obtain ⟨β, hβ⟩ := exists_mulAut_of_range_eq
    (ψ := (MulAut.conj (sZero φ₁)).toMonoidHom.comp φ₂) (ψ' := φ₂)
    ((MulAut.conj (sZero φ₁)).injective.comp h.coords.inj₂) h.coords.inj₂ hrange
  have hsZero2 : sZero φ₁ * sZero φ₁ = 1 := by
    rw [sZero, ← map_mul,
      weylRep_mul_self (F := F2) (m := m + 1 + 1) gf2_two (⟨0, by omega⟩), map_one]
  have h1 : ∀ s, β (slUpper2Hom m s) = slUpper2Hom m s := by
    intro s
    apply h.coords.inj₂
    rw [hβ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hmem : φ₂ (slUpper2Hom m s) ∈ J := by
      rw [← h.coords.rangeJ, h.coords.agree]
      exact MonoidHom.mem_range.mpr ⟨s, rfl⟩
    rw [ggHalfGraphCent_sZero_comm_J (h := h) (φ₂ (slUpper2Hom m s)) hmem,
      mul_assoc, mul_inv_cancel, mul_one]
  have h2 : β (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) =
      omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ := by
    apply h.coords.inj₂
    rw [hβ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨-, -, -, -, -, -, hxL, -, -, -⟩ := h.basic
    have hw : φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) ∈ Subgroup.zpowers x := by
      rw [h.zpowers_x]; exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hsL : sZero φ₁ ∈ L := by
      rw [sZero, ← h.coords.range₁]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hxs : x * sZero φ₁ = sZero φ₁ * x := hxL (sZero φ₁) hsL
    have hcomm : sZero φ₁ * φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) =
        φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) * sZero φ₁ := by
      rw [← hk]
      exact (Commute.zpow_left (show Commute x (sZero φ₁) from hxs) k).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have h3 : β * β = 1 := by
    apply MulEquiv.ext
    intro s
    apply h.coords.inj₂
    change φ₂ (β (β s)) = φ₂ s
    rw [hβ, MonoidHom.comp_apply, hβ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hSinv : (sZero φ₁)⁻¹ = sZero φ₁ := inv_eq_of_mul_eq_one_right hsZero2
    rw [hSinv]
    calc sZero φ₁ * (sZero φ₁ * φ₂ s * sZero φ₁) * sZero φ₁
        = (sZero φ₁ * sZero φ₁) * φ₂ s * (sZero φ₁ * sZero φ₁) := by group
      _ = φ₂ s := by rw [hsZero2]; group
  have hβeq : β = 1 :=
    ggHalfGraphCent_mulAut_eq_one_of_levi_upper hm β h1 h2 h3
  intro k hk
  rw [← h.coords.range₂] at hk
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hk
  have hfix : sZero φ₁ * φ₂ s * (sZero φ₁)⁻¹ = φ₂ s := by
    have hthis := hβ s
    rw [hβeq] at hthis
    simpa using hthis.symm
  rw [← mul_inv_eq_iff_eq_mul]
  exact hfix

end GGHalfCtx

end CFSG.StandardType

end

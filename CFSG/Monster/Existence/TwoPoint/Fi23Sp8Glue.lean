module

public import CFSG.Monster.Existence.TwoPoint.Fi23Sp8Group
public import CFSG.Monster.Existence.TwoPoint.Fi22Iso
public import CFSG.Monster.Existence.TwoPoint.Fi23S4

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.Existence.Fi23Sp8 (mem_gIdx_iff spL eq_spL_of_le)
open CFSG.Sporadic.Bridge.Fi23 (img)

@[expose] noncomputable def fiLK : Subgroup MGriess :=
  Subgroup.closure {x | ∃ i, i < 10 ∧ i ≠ 8 ∧ x = fiE i}

theorem fiE_mem_fiLK {i : ℕ} (hi : i < 10) (hi8 : i ≠ 8) : fiE i ∈ fiLK :=
  Subgroup.subset_closure ⟨i, hi, hi8, rfl⟩

theorem fiLK_le_fiK :
    fiLK ≤ fiK :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨i, hi, -, rfl⟩
    exact fiE_mem_fiK hi)

section Glue

variable {γ₀ : MGriess}

theorem fiE_mem_inter
    (hc : ∀ i, i < 10 → i ≠ 8 → fiE i * γ₀ = γ₀ * fiE i) {i : ℕ} (hi : i < 10)
    (hi8 : i ≠ 8) : fiE i ∈ cent2 fiAlpha fiBeta ⊓ cent γ₀ :=
  Subgroup.mem_inf.2
    ⟨fiK_le (fiE_mem_fiK hi), Subgroup.mem_centralizer_singleton_iff.2 (hc i hi hi8)⟩

theorem inter_le_fiK
    (hKeq : fiK = cent2 fiAlpha fiBeta) :
    cent2 fiAlpha fiBeta ⊓ cent γ₀ ≤ fiK := by
  rw [hKeq]
  exact inf_le_left

theorem map_inter_eq_spL
    (hc : ∀ i, i < 10 → i ≠ 8 → fiE i * γ₀ = γ₀ * fiE i)
    (hn : fiE 8 * γ₀ ≠ γ₀ * fiE 8) :
    ((cent2 fiAlpha fiBeta ⊓ cent γ₀).subgroupOf fiK).map (fiPhi : fiK →* CFSG.Sporadic.Fi23.J) =
      spL := by
  refine eq_spL_of_le ?_ ?_
  · rw [spL, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨hk10, hk8⟩ := mem_gIdx_iff.1 hk
    exact ⟨⟨fiE k, fiE_mem_fiK hk10⟩, Subgroup.mem_subgroupOf.2 (fiE_mem_inter hc hk10 hk8),
      fiPhi_fiE hk10⟩
  · rintro ⟨y, hy, hy8⟩
    have h1 : y = ⟨fiE 8, fiE_mem_fiK (by norm_num)⟩ :=
      fiPhi.injective (hy8.trans (fiPhi_fiE (by norm_num)).symm)
    have h2 : fiE 8 ∈ cent2 fiAlpha fiBeta ⊓ cent γ₀ := by
      have := Subgroup.mem_subgroupOf.1 hy
      rw [h1] at this
      exact this
    exact hn (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h2).2)

theorem fiPhi_mem_spL
    (hKeq : fiK = cent2 fiAlpha fiBeta)
    (hc : ∀ i, i < 10 → i ≠ 8 → fiE i * γ₀ = γ₀ * fiE i) (hn : fiE 8 * γ₀ ≠ γ₀ * fiE 8)
    {x : MGriess} (hx : x ∈ cent2 fiAlpha fiBeta ⊓ cent γ₀) :
    fiPhi ⟨x, inter_le_fiK hKeq hx⟩ ∈ spL := by
  rw [← map_inter_eq_spL hc hn]
  exact ⟨⟨x, inter_le_fiK hKeq hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩

theorem fiPhi_symm_mem_fiLK
    {j : CFSG.Sporadic.Fi23.J} (hj : j ∈ spL) :
    ((fiPhi.symm j : fiK) : MGriess) ∈ fiLK := by
  induction hj using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨hk10, hk8⟩ := mem_gIdx_iff.1 hk
    have e : fiPhi.symm (img k) = ⟨fiE k, fiE_mem_fiK hk10⟩ := by
      rw [MulEquiv.symm_apply_eq, fiPhi_fiE hk10]
    rw [e]
    exact fiE_mem_fiLK hk10 hk8
  | one =>
    rw [map_one]
    exact fiLK.one_mem
  | mul y z _ _ hy hz =>
    rw [map_mul]
    exact fiLK.mul_mem hy hz
  | inv y _ hy =>
    rw [map_inv]
    exact fiLK.inv_mem hy

theorem cent2_inf_cent_eq
    (hKeq : fiK = cent2 fiAlpha fiBeta)
    (hc : ∀ i, i < 10 → i ≠ 8 → fiE i * γ₀ = γ₀ * fiE i) (hn : fiE 8 * γ₀ ≠ γ₀ * fiE 8) :
    cent2 fiAlpha fiBeta ⊓ cent γ₀ = fiLK := by
  apply le_antisymm
  · intro x hx
    have h := fiPhi_symm_mem_fiLK (fiPhi_mem_spL hKeq hc hn hx)
    rw [MulEquiv.symm_apply_apply] at h
    exact h
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, hi8, rfl⟩
    exact fiE_mem_inter hc hi hi8

noncomputable def interEquivSpL
    (hKeq : fiK = cent2 fiAlpha fiBeta)
    (hc : ∀ i, i < 10 → i ≠ 8 → fiE i * γ₀ = γ₀ * fiE i) (hn : fiE 8 * γ₀ ≠ γ₀ * fiE 8) :
    ↥(cent2 fiAlpha fiBeta ⊓ cent γ₀) ≃* ↥spL where
  toFun s := ⟨fiPhi ⟨s.1, inter_le_fiK hKeq s.2⟩, fiPhi_mem_spL hKeq hc hn s.2⟩
  invFun l := ⟨((fiPhi.symm l.1 : fiK) : MGriess), by
    rw [cent2_inf_cent_eq hKeq hc hn]
    exact fiPhi_symm_mem_fiLK l.2⟩
  left_inv s := Subtype.ext (by
    show ((fiPhi.symm (fiPhi ⟨s.1, inter_le_fiK hKeq s.2⟩) : fiK) : MGriess) = s.1
    rw [MulEquiv.symm_apply_apply])
  right_inv l := Subtype.ext (by
    show fiPhi (fiPhi.symm l.1) = l.1
    exact MulEquiv.apply_symm_apply fiPhi l.1)
  map_mul' a b := Subtype.ext (by
    show fiPhi ⟨(a.1 * b.1 : MGriess), _⟩ =
      fiPhi ⟨a.1, inter_le_fiK hKeq a.2⟩ * fiPhi ⟨b.1, inter_le_fiK hKeq b.2⟩
    rw [← map_mul]
    rfl)

theorem lieModel_cent2_inf_cent
    (hKeq : fiK = cent2 fiAlpha fiBeta)
    (hc : ∀ i, i < 10 → i ≠ 8 → fiE i * γ₀ = γ₀ * fiE i) (hn : fiE 8 * γ₀ ≠ γ₀ * fiE 8) :
    CFSG.Blueprint.LieModel ↥(cent2 fiAlpha fiBeta ⊓ cent γ₀) .PSp 4 2 1 :=
  Fi23Sp8.lieModel_of_mulEquiv ((interEquivSpL hKeq hc hn).trans Fi23Sp8.spEquivStated)

end Glue

theorem cent2_inf_cent_gammaZero
    (hKeq : fiK = cent2 fiAlpha fiBeta) :
    cent2 fiAlpha fiBeta ⊓ cent gammaZero = fiLK :=
  cent2_inf_cent_eq hKeq (fun _ hi hi8 => fiE_commute_gammaZero hi hi8)
    fiE_eight_not_commute_gammaZero

theorem lieModel_cent2_inf_cent_gammaZero
    (hKeq : fiK = cent2 fiAlpha fiBeta) :
    CFSG.Blueprint.LieModel ↥(cent2 fiAlpha fiBeta ⊓ cent gammaZero) .PSp 4 2 1 :=
  lieModel_cent2_inf_cent hKeq (fun _ hi hi8 => fiE_commute_gammaZero hi hi8)
    fiE_eight_not_commute_gammaZero

end CFSG.Monster.Existence

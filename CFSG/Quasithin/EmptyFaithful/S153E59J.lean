module

public import CFSG.Quasithin.EmptyFaithful.S153E59I
public import CFSG.Quasithin.EmptyFaithful.S153EInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section Orders

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
  {y t₁ : G}

theorem card_U (c : Chain15358 cx N₁ N₂ g s y t₁) : Nat.card ↥(UH153 T M V₁ Mc) = 2 ^ 7 := by
  have := c.h58.two_U.2.1
  norm_num at this
  exact this

theorem klein_autOn_U (c : Chain15358 cx N₁ N₂ g s y t₁) :
    IsKleinFour153 (autOn (UH153 T M V₁ Mc) (VZ T M)) := by
  rcases c.h51.two with h | h
  · exact h.2.1
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := c.h52
    exact hab (B2F.isElemAbelian_comm h.1 ha hb)

theorem Pgp_eq (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Pgp153 T M V₁ Mc g = pCoreOf 2 (IYU T Mc M V₁) := by
  unfold Pgp153
  rw [c.h54.one]

theorem P_eq_centralizer (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    pCoreOf 2 (IYU T Mc M V₁) = IYU T Mc M V₁ ⊓ Subgroup.centralizer (VZ T M : Set G) :=
  pCoreOf_IYU_eq h113 cx (by rw [← Pgp_eq cx c]; exact c.h54.two_center)

theorem W_eq (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Wgp153 T M V₁ Mc g = UH153 T M V₁ Mc ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  show UH153 T M V₁ Mc ⊓ Pgp153 T M V₁ Mc g = _
  rw [Pgp_eq cx c, P_eq_centralizer cx h113 c, ← inf_assoc, inf_eq_left.mpr U_le_IYU]

theorem card_W (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(Wgp153 T M V₁ Mc g) = 2 ^ 5 := by
  have hV := cx.c.hyp.elemAbelian
  have h1 := card_autI_mul_card_inf hV (S153E.U_le_N cx)
  have hk : Nat.card ↥(autI hV (UH153 T M V₁ Mc)) = 4 := (klein_autOn_U cx c).1
  rw [hk, card_U cx c] at h1
  rw [W_eq cx h113 c]
  omega

theorem card_W_inf (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(conjSubgroup (Wgp153 T M V₁ Mc g) g ⊓ Wgp153 T M V₁ Mc g) = 4 := by
  rw [inf_comm, ← c.h54.three_eq]
  exact c.h54.three_klein.1

theorem conj_W_le_normalizer (c : Chain15358 cx N₁ N₂ g s y t₁) :
    conjSubgroup (Wgp153 T M V₁ Mc g) g ≤ Subgroup.normalizer (Wgp153 T M V₁ Mc g : Set G) := by
  intro x hx
  have key : ∀ x ∈ conjSubgroup (Wgp153 T M V₁ Mc g) g, ∀ w ∈ Wgp153 T M V₁ Mc g,
      x * w * x⁻¹ ∈ Wgp153 T M V₁ Mc g := by
    intro x hx w hw
    have hc : x * w * x⁻¹ * w⁻¹ ∈ ⁅conjSubgroup (Wgp153 T M V₁ Mc g) g, UH153 T M V₁ Mc⁆ :=
      Subgroup.commutator_mem_commutator hx hw.1
    have hc' := c.h54.five_comm hc
    have e : x * w * x⁻¹ = (x * w * x⁻¹ * w⁻¹) * w := by group
    rw [e]
    exact (Wgp153 T M V₁ Mc g).mul_mem hc' hw
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => key x hx w hw, fun hw => ?_⟩
  have := key x⁻¹ ((conjSubgroup (Wgp153 T M V₁ Mc g) g).inv_mem hx) _ hw
  simpa [mul_assoc] using this

theorem conj_W_sup_eq (c : Chain15358 cx N₁ N₂ g s y t₁) :
    conjSubgroup (Wgp153 T M V₁ Mc g) g ⊔ Wgp153 T M V₁ Mc g = Pgp153 T M V₁ Mc g := by
  apply le_antisymm
  · refine sup_le (fun x hx => ?_) inf_le_right
    have : x ∈ ((Wgp153 T M V₁ Mc g : Subgroup G) : Set G) *
        ((conjSubgroup (Wgp153 T M V₁ Mc g) g : Subgroup G) : Set G) :=
      ⟨1, (Wgp153 T M V₁ Mc g).one_mem, x, hx, one_mul x⟩
    rw [← c.h54.two_prod] at this
    exact this
  · intro x hx
    have : x ∈ ((Wgp153 T M V₁ Mc g : Subgroup G) : Set G) *
        ((conjSubgroup (Wgp153 T M V₁ Mc g) g : Subgroup G) : Set G) := by
      rw [← c.h54.two_prod]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hb)
theorem card_P (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(Pgp153 T M V₁ Mc g) = 2 ^ 8 := by
  have h := card_sup_mul_card_inf_of_normalizes (conj_W_le_normalizer cx c)
  rw [conj_W_sup_eq cx c, card_W_inf cx c, card_conjSubgroup', card_W cx h113 c] at h
  omega

theorem card_autOn_IYU (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(autOn (IYU T Mc M V₁) (VZ T M)) = 36 := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨Ω, -, hsup, hN⟩ := c.h53one.omega
  have h1 : autOn (IYU T Mc M V₁) (VZ T M) = N₁ ⊔ N₂ := by
    show autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) = _
    rw [autI_sup hV (cx.c.hyp.le_normalizer.trans' (Y153_le Mc M))
      (S153E.U_le_N cx), sup_comm]
    exact hsup.trans hN.symm
  have hc1 : Nat.card ↥N₁ = 6 := by
    obtain ⟨e⟩ := c.h53one.iso₁
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hc2 : Nat.card ↥N₂ = 6 := by
    obtain ⟨e⟩ := c.h53one.iso₂
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have h2 := B2F.card_sup_mul_card_inf_of_commute c.h53one.comm
  rw [c.h53one.inf, Subgroup.card_bot, hc1, hc2] at h2
  rw [h1]
  omega

theorem card_IYU (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(IYU T Mc M V₁) = 9216 := by
  have hV := cx.c.hyp.elemAbelian
  have h1 := card_autI_mul_card_inf hV
    (cx.c.hyp.le_normalizer.trans' (IYU_le_M cx) : IYU T Mc M V₁ ≤ _)
  have h36 : Nat.card ↥(autI hV (IYU T Mc M V₁)) = 36 := card_autOn_IYU cx c
  rw [← P_eq_centralizer cx h113 c, ← Pgp_eq cx c, card_P cx h113 c, h36] at h1
  omega

end Orders

end S153E59

end CFSG.Quasithin

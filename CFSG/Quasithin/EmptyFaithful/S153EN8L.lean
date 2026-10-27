module

public import CFSG.Quasithin.EmptyFaithful.S153EN8J
public import CFSG.Quasithin.EmptyFaithful.S153EN8K

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t} {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

section TJ

variable (h113 : StageLemma14113) (c : Chain15359 cx N₁ N₂ g s y t₁) (B : BarModel cx)
  {d : G} (hdM : d ∈ M) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hbd : barM cx hdM ∈ B.L₂)

theorem mem_T_iff_barM (c' : Chain15358 cx N₁ N₂ g s y t₁) {x : G} (hx : x ∈ M) :
    x ∈ T ↔ barM cx hx ∈ autI cx.c.hyp.elemAbelian T := by
  constructor
  · intro hxT
    exact convI_mem_autI _ hxT _
  · intro h
    obtain ⟨y', hyT, hy⟩ := (mem_autI _).1 h
    have hyM : (y' : G) ∈ M := S153E.T_le_M cx hyT
    have h1 : barM cx hyM = barM cx hx := hy
    have h2 := (barM_eq_iff hyM hx).1 h1
    have h3 : (y' : G)⁻¹ * x ∈ T := Q_le_T c' ⟨M.mul_mem (M.inv_mem hyM) hx, h2⟩
    have e : x = (y' : G) * ((y' : G)⁻¹ * x) := by group
    rw [e]
    exact T.mul_mem hyT h3

include c B hdM hd3 hd1 hbd in
theorem autI_TJ :
    autI cx.c.hyp.elemAbelian (T ⊓ Jgp M V₂ d) = autI cx.c.hyp.elemAbelian T ⊓ B.L₁ := by
  apply le_antisymm
  · refine le_inf (autI_mono _ inf_le_left) ?_
    rw [← autI_Jgp c B hdM hd3 hd1 hbd]
    exact autI_mono _ inf_le_right
  · intro φ hφ
    obtain ⟨x, hxM, hxJ, hxφ⟩ := exists_lift_J c B hdM hd3 hd1 hbd hφ.2
    have hxT : x ∈ T := (mem_T_iff_barM c.toChain15358 hxM).2 (by rw [hxφ]; exact hφ.1)
    rw [← hxφ]
    exact convI_mem_autI _ (Subgroup.mem_inf.2 ⟨hxT, hxJ⟩) _

include B in
theorem inf_L₁_eq_zpowers :
    autI cx.c.hyp.elemAbelian T ⊓ B.L₁ = Subgroup.zpowers B.s₁ := by
  apply le_antisymm
  · intro x hx
    have hxS : x ∈ autI cx.c.hyp.elemAbelian T ⊓ (B.L₁ ⊔ B.L₂) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, Subgroup.mem_sup_left (Subgroup.mem_inf.1 hx).2⟩
    rcases B.hF.sylow.inf₁ x hxS (Subgroup.mem_inf.1 hx).2 with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 B.hF.sylow.s₁_mem_S).1, B.hF.sylow.s₁_mem_L⟩

include B in
theorem card_zpowers_s₁ : Nat.card (Subgroup.zpowers B.s₁) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact B.hF.s₁_sq) B.hF.sylow.s₁_ne

include h113 c B hdM hd3 hd1 hbd in
theorem card_TJ : Nat.card ↥(T ⊓ Jgp M V₂ d) = 8 := by
  have hV := cx.c.hyp.elemAbelian
  have hRN : T ⊓ Jgp M V₂ d ≤ Subgroup.normalizer (VZ T M : Set G) := fun x hx =>
    cx.c.hyp.le_normalizer ((mem_Jgp.1 (Subgroup.mem_inf.1 hx).2).1.1)
  have hRC : (T ⊓ Jgp M V₂ d) ⊓ Subgroup.centralizer (VZ T M : Set G) = V₁ := by
    apply le_antisymm
    · intro x hx
      rw [← inf_centralizer_Jgp h113 c B hdM hd3 hd1 hbd]
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2,
        (Subgroup.mem_inf.1 hx).2⟩
    · intro x hx
      have hVJ := V₁_le_Jgp h113 c B hdM hd3 hd1 hbd hx
      have hxV : x ∈ VZ T M := cx.c.decomp.le₁ hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨cx.c.hyp.VZ_le_T hxV, hVJ⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact B2F.isElemAbelian_comm hV hv hxV
  have h := card_autI_mul_card_inf hV hRN
  rw [autI_TJ c B hdM hd3 hd1 hbd, inf_L₁_eq_zpowers B, card_zpowers_s₁ B, hRC,
    cx.c.decomp.card₁] at h
  omega

include h113 c B hdM hd3 hd1 hbd in
theorem isSylowTwoOf_TJ : IsSylowTwoOf (T ⊓ Jgp M V₂ d) (Jgp M V₂ d) := by
  refine ⟨inf_le_right, (cx.hF.sylow_H.2.1 : IsPGroup 2 T).to_le inf_le_left, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (T ⊓ Jgp M V₂ d) (Jgp M V₂ d)
  rw [inf_eq_left.2 (inf_le_right : T ⊓ Jgp M V₂ d ≤ Jgp M V₂ d), card_TJ h113 c B hdM hd3 hd1 hbd,
    card_Jgp h113 c B hdM hd3 hd1 hbd] at h1
  have h2 : (T ⊓ Jgp M V₂ d).relIndex (Jgp M V₂ d) = 3 := by omega
  show ¬ 2 ∣ (T ⊓ Jgp M V₂ d).relIndex (Jgp M V₂ d)
  rw [h2]
  decide

include h113 c B hdM hd3 hd1 hbd in
theorem nonempty_dihedral_TJ : Nonempty (↥(T ⊓ Jgp M V₂ d) ≃* DihedralGroup 4) := by
  obtain ⟨ψ⟩ := nonempty_equiv_perm_four_Jgp h113 c B hdM hd3 hd1 hbd
  exact nonempty_dihedral_of_perm_four
    ((cx.hF.sylow_H.2.1 : IsPGroup 2 T).to_le inf_le_left : IsPGroup 2 ↥(T ⊓ Jgp M V₂ d))
    (card_TJ h113 c B hdM hd3 hd1 hbd)
    (ψ.toMonoidHom.comp (Subgroup.inclusion inf_le_right))
    (ψ.injective.comp (Subgroup.inclusion_injective _))

end TJ

end S153EN8

end CFSG.Quasithin

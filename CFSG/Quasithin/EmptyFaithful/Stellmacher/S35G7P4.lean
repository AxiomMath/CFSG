module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChCent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7.P

open S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem exists_lift {γ : Geo H M} {c : Ch.Chart γ} {K : Subgroup G} {l₀ : Geo H M}
    (wm : WModule c K l₀) (f0 : ↥(Wb γ) →* orth.W)
    (hker : ∀ w : ↥(Wb γ), wm.proj w = 1 → f0 w = 1) :
    ∃ f : wm.mod.W →* orth.W, ∀ w, f (wm.proj w) = f0 w := by
  have hle : wm.proj.ker ≤ f0.ker := fun w hw => hker w (MonoidHom.mem_ker.mp hw)
  exact ⟨wm.proj.liftOfSurjective wm.proj_surj ⟨f0, hle⟩, fun w =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨f0, hle⟩ w⟩

omit [Finite G] in
theorem card_map_U {γ : Geo H M} {c : Ch.Chart γ} {K : Subgroup G} {l₀ : Geo H M}
    (wm : WModule c K l₀) : Nat.card (wm.U.map wm.π) = 4 := by
  rw [← wm.card_U]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun u : ↥wm.U => (⟨wm.π u, Subgroup.mem_map_of_mem wm.π u.2⟩ : ↥(wm.U.map wm.π)))
    ⟨?_, ?_⟩)).symm
  · intro a b hab
    have h1 : wm.π (a : wm.mod.W) = wm.π (b : wm.mod.W) := congrArg Subtype.val hab
    have h2 : wm.π ((a : wm.mod.W) * (b : wm.mod.W)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := wm.π_inj _ (wm.U.mul_mem a.2 (wm.U.inv_mem b.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  · rintro ⟨_, u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩

omit [Finite G] in
theorem isInvSub_map_U {γ : Geo H M} {c : Ch.Chart γ} {K : Subgroup G} {l₀ : Geo H M}
    (wm : WModule c K l₀) : IsInvSub orth S5Syl (wm.U.map wm.π) := by
  rintro b hb _ ⟨u, hu, rfl⟩
  exact ⟨wm.mod.act b u, wm.inv b hb u hu, (wm.π_act b u)⟩

theorem img_Rl_eq_map (hC : Ch.Ctx H M S) {γ : Geo H M} (hγ : vtype γ = false)
    {c : Ch.Chart γ} {K : Subgroup G} {l₀ : Geo H M} (hl₀ : l₀ ∈ nbrs γ)
    (hD : c.Dl l₀ = S5Syl) (wm : WModule c K l₀) :
    c.img (Ch.Rl γ l₀) = wm.U.map wm.π := by
  have hz : IsCentInv S5Syl (zc S5Syl) := isCentInv_zc card_S5Syl
  rw [c.img_Rl hC hγ hl₀, hD]
  exact (eq_commW_z_of_card_four card_S5Syl hz (isInvSub_map_U wm) (card_map_U wm)).symm

end S35.G7.P

end F53.Stellmacher

end CFSG.Quasithin

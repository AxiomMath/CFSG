module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord

namespace TypeBDatum

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem sign_of_sq_one {p : ℕ} [Fact p.Prime] {x : ZMod p} (hx : x * x = 1) :
    x = 1 ∨ x = -1 := by
  have h : (x - 1) * (x + 1) = 0 := by
    have : (x - 1) * (x + 1) = x * x - 1 := by ring
    rw [this, hx, sub_self]
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (by linear_combination h1)

@[expose] def permAutHom (m p : ℕ) :
    Equiv.Perm (Fin m) →* MulAut (Fin m → Multiplicative (ZMod p)) where
  toFun σ := permAut (p := p) σ
  map_one' := by ext f i; rfl
  map_mul' σ τ := by
    ext f i
    simp only [MulAut.mul_apply, permAut_apply, Function.comp_apply, mul_inv_rev,
      Equiv.Perm.mul_apply]

theorem permAut_mul_swap {m p : ℕ} (τ : Equiv.Perm (Fin m)) (a b : Fin m) :
    permAut (p := p) τ * permAut (p := p) (Equiv.swap a b) * (permAut (p := p) τ)⁻¹ =
      permAut (p := p) (Equiv.swap (τ a) (τ b)) := by
  change permAutHom m p τ * permAutHom m p (Equiv.swap a b) *
      (permAutHom m p τ)⁻¹ = permAut (p := p) (Equiv.swap (τ a) (τ b))
  rw [← (permAutHom m p).map_mul, ← (permAutHom m p).map_inv,
    ← (permAutHom m p).map_mul, Equiv.swap_apply_apply]
  rfl

theorem permSupportedAut_map_conj {m p : ℕ} (τ : Equiv.Perm (Fin m))
    (S : Finset (Fin m)) :
    (permSupportedAut m p S).map (MulAut.conj (permAut (p := p) τ)).toMonoidHom =
      permSupportedAut m p (S.image τ) := by
  classical
  rw [permSupportedAut, permSupportedAut, MonoidHom.map_closure]
  congr 1
  ext σ
  constructor
  · rintro ⟨y, ⟨a, ha, b, hb, hab, rfl⟩, rfl⟩
    refine ⟨τ a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, τ b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      fun h => hab (τ.injective h), permAut_mul_swap τ a b⟩
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    rcases Finset.mem_image.mp ha with ⟨a', ha', rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b', hb', rfl⟩
    exact ⟨permAut (p := p) (Equiv.swap a' b'),
      ⟨a', ha', b', hb', fun h => hab (by rw [h]), rfl⟩, permAut_mul_swap τ a' b'⟩

theorem liftBs_prodCongr {G : Type} [Group G] {Bs : Subgroup G} {W W₀ : Type}
    [Group W] [Group W₀] (Θ : (W × W₀) ≃* ↥Bs) (P : MulAut W) :
    liftBs (Bs := Bs) ((MulEquiv.prodCongr P (MulEquiv.refl W₀)).trans Θ) =
      (liftBs (Bs := Bs) Θ).comp (MulAut.conj P).toMonoidHom := by
  refine MonoidHom.ext fun σ => MulEquiv.ext fun x => ?_
  obtain ⟨⟨w, u⟩, rfl⟩ := Θ.surjective x
  have hx : Θ (w, u) =
      ((MulEquiv.prodCongr P (MulEquiv.refl W₀)).trans Θ) (P⁻¹ w, u) := by
    change Θ (w, u) = Θ (P (P⁻¹ w), u)
    exact (congrArg (fun x => Θ (x, u)) (MulEquiv.apply_symm_apply P w)).symm
  change liftBs (Bs := Bs) ((MulEquiv.prodCongr P (MulEquiv.refl W₀)).trans Θ) σ (Θ (w, u)) =
    liftBs (Bs := Bs) Θ (MulAut.conj P σ) (Θ (w, u))
  rw [liftBs_apply Θ (MulAut.conj P σ) w u]
  conv_lhs => rw [hx]
  rw [liftBs_apply ((MulEquiv.prodCongr P (MulEquiv.refl W₀)).trans Θ) σ (P⁻¹ w) u,
    MulAut.conj_apply]
  rfl

theorem conj_apply_comp {E : Type} [Group E] (a b x : E) :
    MulAut.conj a (MulAut.conj b x) = MulAut.conj (a * b) x := by
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  group

end TypeBDatum

end CFSG.StandardType

end

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S143Aux

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q2

section Norm

variable {W : Type} [CommGroup W]

@[expose] def nrmHom (z : MulAut W) : W →* W :=
  MonoidHom.mk' (fun w => w * z w * z (z w)) (fun a b => by simp only [map_mul]; ac_rfl)

theorem nrmHom_apply (z : MulAut W) (w : W) : nrmHom z w = w * z w * z (z w) := rfl

variable {z : MulAut W}

theorem z_cube_apply (hz3 : z ^ 3 = 1) (w : W) : z (z (z w)) = w := by
  have h : (z * z * z) w = w := by rw [← pow_three', hz3]; rfl
  exact h

theorem nrmHom_of_fixed (hW2 : ∀ w : W, w * w = 1) {c : W} (hc : z c = c) : nrmHom z c = c := by
  rw [nrmHom_apply, hc, hc, hW2, one_mul]

theorem z_nrmHom (hz3 : z ^ 3 = 1) (w : W) : z (nrmHom z w) = nrmHom z w := by
  rw [nrmHom_apply, map_mul, map_mul, z_cube_apply hz3]
  ac_rfl

@[expose] def kerN (z : MulAut W) : Subgroup W := (nrmHom z).ker

theorem mem_kerN {w : W} : w ∈ kerN z ↔ nrmHom z w = 1 := MonoidHom.mem_ker

theorem fixed_of_mem_kerN (hW2 : ∀ w : W, w * w = 1) {c : W} (hc : z c = c) (hk : c ∈ kerN z) :
    c = 1 := by
  rw [← nrmHom_of_fixed hW2 hc]; exact mem_kerN.1 hk

theorem div_nrm_mem_kerN (hW2 : ∀ w : W, w * w = 1) (hz3 : z ^ 3 = 1) (w : W) :
    w * (nrmHom z w)⁻¹ ∈ kerN z := by
  rw [mem_kerN, map_mul, map_inv, nrmHom_of_fixed hW2 (z_nrmHom hz3 w)]
  exact mul_inv_cancel _

theorem nrmHom_comm {g : MulAut W} (hg : g * z = z * g) (w : W) :
    nrmHom z (g w) = g (nrmHom z w) := by
  have h : ∀ x, z (g x) = g (z x) := fun x => (congrArg (fun f : MulAut W => f x) hg).symm
  simp only [nrmHom_apply, map_mul, h]

theorem kerN_invariant {g : MulAut W} (hg : g * z = z * g) {w : W} (hw : w ∈ kerN z) :
    g w ∈ kerN z := by
  rw [mem_kerN, nrmHom_comm hg, mem_kerN.1 hw, map_one]

theorem z_eq_one_of_fix (hW2 : ∀ w : W, w * w = 1) (hz3 : z ^ 3 = 1)
    (hfix : ∀ w ∈ kerN z, z w = w) : z = 1 := by
  ext w
  have h1 := div_nrm_mem_kerN hW2 hz3 w
  have h3 := fixed_of_mem_kerN hW2 (hfix _ h1) h1
  have h4 : w = nrmHom z w := mul_inv_eq_one.1 h3
  rw [MulAut.one_apply]
  have h5 := z_nrmHom hz3 w
  rw [← h4] at h5
  exact h5

end Norm

section Restrict

variable {W : Type} [CommGroup W]

@[expose] def fixK (K : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | ∀ w ∈ K, g w = w}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb w hw => by
    show a (b w) = w
    rw [hb w hw, ha w hw]
  inv_mem' := fun {a} ha w hw => by
    calc a⁻¹ w = a⁻¹ (a w) := by rw [ha w hw]
      _ = w := by simp

@[expose] def restHom (K : Subgroup W) (A : Subgroup (MulAut W))
    (hA : ∀ g ∈ A, ∀ v ∈ K, g v ∈ K ∧ g⁻¹ v ∈ K) : ↥A →* MulAut ↥K where
  toFun g :=
    { toFun := fun x => ⟨g.1 x.1, (hA g.1 g.2 x.1 x.2).1⟩
      invFun := fun x => ⟨g.1⁻¹ x.1, (hA g.1 g.2 x.1 x.2).2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (map_mul g.1 x.1 y.1) }
  map_one' := by ext x; rfl
  map_mul' := fun g h => by ext x; rfl

theorem restHom_apply (K : Subgroup W) (A : Subgroup (MulAut W))
    (hA : ∀ g ∈ A, ∀ v ∈ K, g v ∈ K ∧ g⁻¹ v ∈ K) (g : ↥A) (x : ↥K) :
    ((restHom K A hA g x : ↥K) : W) = g.1 (x : W) := rfl

theorem restHom_injective (K : Subgroup W) (A : Subgroup (MulAut W))
    (hA : ∀ g ∈ A, ∀ v ∈ K, g v ∈ K ∧ g⁻¹ v ∈ K)
    (h : ∀ g ∈ A, g ∈ fixK K → g = 1) : Function.Injective (restHom K A hA) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  refine h g.1 g.2 fun w hw => ?_
  have := congrArg (fun f : MulAut ↥K => ((f ⟨w, hw⟩ : ↥K) : W)) hg
  simpa [restHom_apply] using this

end Restrict

end Q2

end S153Q

end CFSG.Quasithin

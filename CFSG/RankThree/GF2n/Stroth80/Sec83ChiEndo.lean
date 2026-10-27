module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

theorem exists_chi_endo {G : Type} [Group G] {R Q Z V W : Subgroup G} {M : Type}
    [AddCommGroup M] [DistribMulAction ↥R M] {κ : ↥Q →* Multiplicative M}
    (hκ : IsSecMod R Q Z M κ) {t : G} (hchi : IsChiIso Q R W V Z t) (hVQ : V ≤ Q)
    (hZW : Z ≤ W) (hZV : Z ≤ V) (hP : ∀ r ∈ R, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q) :
    ∃ ε : M →+ M,
      (∀ x : ↥Q, ε (Multiplicative.toAdd (κ x)) =
        Multiplicative.toAdd (κ ⟨⁅(x : G), t⁆, hVQ (hchi.1 x x.2)⟩)) ∧
      ε.ker = secSub κ W ∧ ε.range = secSub κ V ∧
      ∀ (z : ↥R) (a : M), ε (z • a) = z • ε a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hchi
  obtain ⟨c, hc⟩ : ∃ c : ↥Q → ↥Q, ∀ x : ↥Q, (c x : G) = ⁅(x : G), t⁆ :=
    ⟨fun x => ⟨⁅(x : G), t⁆, hVQ (h1 x x.2)⟩, fun x => rfl⟩
  have hc' : ∀ x : ↥Q, c x = ⟨⁅(x : G), t⁆, hVQ (h1 x x.2)⟩ := fun x => Subtype.ext (hc x)
  have hc_one : c 1 = 1 := Subtype.ext (by rw [hc]; simp)
  have hc_mul : ∀ x y : ↥Q, κ (c (x * y)) = κ (c x) * κ (c y) := fun x y => by
    rw [← map_mul, hκ.eq_iff, Subgroup.coe_mul, hc, hc, hc]
    exact h3 x x.2 y y.2
  let ε₀ : ↥Q →* Multiplicative M :=
    { toFun := fun x => κ (c x)
      map_one' := by rw [hc_one, map_one]
      map_mul' := hc_mul }
  have hε₀Z : ∀ x : ↥Q, (x : G) ∈ Z → ε₀ x = 1 := fun x hx =>
    (hκ.ker (c x)).mpr (by rw [hc]; exact (h4 x x.2).mpr (hZW hx))
  have hker : κ.ker ≤ ε₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hε₀Z x ((hκ.ker x).mp hx)
  let ε' : Multiplicative M →* Multiplicative M :=
    κ.liftOfRightInverse (Function.surjInv hκ.surj) (Function.rightInverse_surjInv hκ.surj)
      ⟨ε₀, hker⟩
  have hε' : ∀ x : ↥Q, ε' (κ x) = κ (c x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply κ _ _ ⟨ε₀, hker⟩ x
  let ε : M →+ M :=
    { toFun := fun a => Multiplicative.toAdd (ε' (Multiplicative.ofAdd a))
      map_zero' := by simp
      map_add' := fun a b => by simp [ofAdd_add, toAdd_mul] }
  have hεκ : ∀ x : ↥Q, ε (Multiplicative.toAdd (κ x)) = Multiplicative.toAdd (κ (c x)) := by
    intro x
    show Multiplicative.toAdd (ε' (Multiplicative.ofAdd (Multiplicative.toAdd (κ x)))) = _
    rw [ofAdd_toAdd, hε']
  refine ⟨ε, fun x => by rw [hεκ, hc'], ?_, ?_, ?_⟩
  ·
    ext a
    obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd a)
    have hxa : Multiplicative.toAdd (κ x) = a := by rw [hx]; rfl
    subst hxa
    rw [AddMonoidHom.mem_ker, hεκ, toAdd_eq_zero, hκ.ker, hc, h4 x x.2,
      toAdd_mem_secSub_iff hκ hZW x]
  ·
    ext a
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd b)
      have hxb : Multiplicative.toAdd (κ x) = b := by rw [hx]; rfl
      subst hxb
      rw [hεκ, toAdd_mem_secSub_iff hκ hZV (c x), hc]
      exact h1 x x.2
    · intro ha
      obtain ⟨y, hyV, hy⟩ := mem_secSub.mp ha
      obtain ⟨x, hxQ, hxy⟩ := h2 (y : G) hyV
      refine ⟨Multiplicative.toAdd (κ ⟨x, hxQ⟩), ?_⟩
      have hxy' : κ (c ⟨x, hxQ⟩) = κ y := by
        rw [hκ.eq_iff, hc]
        exact hxy
      rw [hεκ, hxy', hy, toAdd_ofAdd]
  ·
    intro z a
    obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd a)
    have hxa : Multiplicative.toAdd (κ x) = a := by rw [hx]; rfl
    subst hxa
    obtain ⟨y, hy⟩ : ∃ y : ↥Q, (y : G) = (z : G) * (x : G) * (z : G)⁻¹ :=
      ⟨⟨_, hP z z.2 x x.2⟩, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : ↥Q, (w : G) = (z : G) * (c x : G) * (z : G)⁻¹ :=
      ⟨⟨_, hP z z.2 (c x) (c x).2⟩, rfl⟩
    have hy1 : κ y = Multiplicative.ofAdd (z • Multiplicative.toAdd (κ x)) :=
      hκ.act z x y hy
    have hw1 : κ w = Multiplicative.ofAdd (z • Multiplicative.toAdd (κ (c x))) :=
      hκ.act z (c x) w hw
    have hyw : κ (c y) = κ w := by
      rw [hκ.eq_iff, hc, hw, hy, hc]
      exact h5 z z.2 x x.2
    have hy2 : Multiplicative.toAdd (κ y) = z • Multiplicative.toAdd (κ x) := by
      rw [hy1, toAdd_ofAdd]
    have hw2 : Multiplicative.toAdd (κ w) = z • Multiplicative.toAdd (κ (c x)) := by
      rw [hw1, toAdd_ofAdd]
    rw [← hy2, hεκ y, hyw, hw2, hεκ x]

end CFSG.RankThree.GF2n.Stroth80

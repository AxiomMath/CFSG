module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkConj
public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockPiece

public section

namespace CFSG.StandardType

namespace WitOmBlk

open QuadraticMap Module OrdPNsOm CFSG.RankThree.OrthogonalInvolutions

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Supp

theorem inv_apply_self (g : V ≃ₗ[K] V) (y : V) : g⁻¹ (g y) = y := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]
  rfl

theorem orthogonalBilin_orthogonalBilin [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    (X : Submodule K V) :
    (X.orthogonalBilin (polarBilin Q)).orthogonalBilin (polarBilin Q) = X :=
  LinearMap.BilinForm.orthogonal_orthogonal hQ (QuadraticMap.isSymm_polarBilin Q).isRefl X

theorem mem_orth_iff {X : Submodule K V} {y : V} :
    y ∈ X.orthogonalBilin (polarBilin Q) ↔ ∀ x ∈ X, polar Q x y = 0 :=
  Submodule.mem_orthogonalBilin

theorem map_mem_of_fix_orth [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {X : Submodule K V}
    (hfix : ∀ y ∈ X.orthogonalBilin (polarBilin Q), g y = y) {x : V} (hx : x ∈ X) : g x ∈ X := by
  rw [← orthogonalBilin_orthogonalBilin hQ X, mem_orth_iff]
  intro y hy
  rw [← hfix y hy, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg, polar_comm]
  exact mem_orth_iff.mp hy x hx

theorem map_mem_orth_of_fix {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {X : Submodule K V} (hfix : ∀ x ∈ X, g x = x) {y : V}
    (hy : y ∈ X.orthogonalBilin (polarBilin Q)) : g y ∈ X.orthogonalBilin (polarBilin Q) := by
  rw [mem_orth_iff] at hy ⊢
  intro x hx
  rw [← hfix x hx, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg]
  exact hy x hx

theorem commute_of_fix [FiniteDimensional K V] {X : Submodule K V}
    (hX : SUTB.NondegOn (polarBilin Q) X) {g h : V ≃ₗ[K] V}
    (hg : ∀ y ∈ X.orthogonalBilin (polarBilin Q), g y = y) (hgX : ∀ x ∈ X, g x ∈ X)
    (hh : ∀ x ∈ X, h x = x)
    (hhY : ∀ y ∈ X.orthogonalBilin (polarBilin Q), h y ∈ X.orthogonalBilin (polarBilin Q)) :
    g * h = h * g := by
  ext v
  obtain ⟨x, hx, y, hy, rfl⟩ := SUTB.exists_add_orth hX v
  simp only [LinearEquiv.mul_apply, map_add, hh x hx, hg y hy, hg _ (hhY y hy),
    hh _ (hgX x hx)]

theorem exists_quad_ne_zero_orth [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    {X : Submodule K V} (hX : SUTB.NondegOn (polarBilin Q) X)
    (hlt : finrank K X < finrank K V) :
    ∃ w ∈ X.orthogonalBilin (polarBilin Q), Q w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hY : X.orthogonalBilin (polarBilin Q) ≤ X := by
    intro y hy
    rw [← orthogonalBilin_orthogonalBilin hQ X, mem_orth_iff]
    intro y' hy'
    rw [polar, hcon _ ((X.orthogonalBilin (polarBilin Q)).add_mem hy' hy), hcon y' hy',
      hcon y hy, sub_zero, sub_zero]
  have h0 : X.orthogonalBilin (polarBilin Q) = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => ?_
    exact hX y (hY hy) fun n hn => mem_orth_iff.mp hy n hn
  have h1 := LinearMap.BilinForm.finrank_orthogonal hQ X
  change finrank K (X.orthogonalBilin (polarBilin Q)) = _ at h1
  rw [h0, finrank_bot] at h1
  have := Submodule.finrank_le X
  omega

end Supp

section Core

variable [CharP K 2]

theorem exists_conj_commute_block [Finite K] [FiniteDimensional K V] [Finite V] {c₀ : K}
    (hc₀ : c₀ ∉ (wp K).range) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p m : ℕ} (hm : 1 ≤ m)
    (hdim : 4 * (2 * m + 2) ≤ finrank K V) {τ₀ : Bool} {U₁ U₂ : Submodule K V}
    (hU₁ : SUTB.NondegOn (polarBilin Q) U₁) (hU₂ : SUTB.NondegOn (polarBilin Q) U₂)
    (hU12 : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0) {e₁ f₁ e₂ f₂ : Fin m → V} {a₁ b₁ a₂ b₂ : V}
    (hF₁ : IsFrame Q c₀ τ₀ e₁ f₁ a₁ b₁) (hF₂ : IsFrame Q c₀ τ₀ e₂ f₂ a₂ b₂)
    (hmem₁ : ∀ x, fvec e₁ f₁ a₁ b₁ x ∈ U₁) (hmem₂ : ∀ x, fvec e₂ f₂ a₂ b₂ x ∈ U₂)
    (hdim₁ : finrank K U₁ = 2 * m + 2) (hdim₂ : finrank K U₂ = 2 * m + 2) {z₁ z₂ : V ≃ₗ[K] V}
    (hz₁ : z₁ ∈ CFSG.RankThree.Classical2.orthDerived Q) (hz₁p : z₁ ^ p = 1) (hz₁1 : z₁ ≠ 1)
    (hz₁off : ∀ y ∈ U₁.orthogonalBilin (polarBilin Q), z₁ y = y) (hz12 : z₁ * z₂ = z₂ * z₁)
    (hF3 : ∀ c ∈ CFSG.RankThree.Classical2.orthDerived Q, c ^ p = 1 → c ≠ 1 →
      (∀ y ∈ U₂.orthogonalBilin (polarBilin Q), c y = y) →
      ∃ h ∈ CFSG.RankThree.Classical2.orthDerived Q,
        (∀ y ∈ U₂.orthogonalBilin (polarBilin Q), h y = y) ∧ ∃ k : ℕ, h * c * h⁻¹ = z₂ ^ k)
    {u : V ≃ₗ[K] V} (hu : u ∈ CFSG.RankThree.Classical2.orthDerived Q) (huu : u * u = 1) :
    ∃ g ∈ CFSG.RankThree.Classical2.orthDerived Q, ∃ k : ℕ,
      g * u * g⁻¹ * (z₁ * z₂ ^ k) = z₁ * z₂ ^ k * (g * u * g⁻¹) := by
  classical
  have hΩO : CFSG.RankThree.Classical2.orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _
  have hz₁O := hΩO hz₁
  have huO := hΩO hu
  have hspan₁ := hF₁.span_eq hmem₁ hdim₁
  have hspan₂ := hF₂.span_eq hmem₂ hdim₂
  have hU : SUTB.NondegOn (polarBilin Q) (U₁ ⊔ U₂) := SUTB.nondegOn_sup hU₁ hU₂ fun y hy x hx =>
    ⟨by rw [polarBilin_apply_apply, polar_comm]; exact hU12 x hx y hy, hU12 x hx y hy⟩
  obtain ⟨w, hw, hw0⟩ := exists_quad_ne_zero_orth hQ hU (by
    have := Submodule.finrank_add_le_finrank_add_finrank U₁ U₂
    omega)
  have hw₁ : ∀ x, polar Q w (fvec e₁ f₁ a₁ b₁ x) = 0 := fun x => by
    rw [polar_comm]
    exact mem_orth_iff.mp hw _ (Submodule.mem_sup_left (hmem₁ x))
  have hw₂ : ∀ x, polar Q w (fvec e₂ f₂ a₂ b₂ x) = 0 := fun x => by
    rw [polar_comm]
    exact mem_orth_iff.mp hw _ (Submodule.mem_sup_right (hmem₂ x))
  have hz₁U₁ : ∀ x ∈ U₁, z₁ x ∈ U₁ := fun x hx => map_mem_of_fix_orth hQ hz₁O hz₁off hx
  have hU₂U₁ : ∀ x ∈ U₂, x ∈ U₁.orthogonalBilin (polarBilin Q) := fun x hx =>
    mem_orth_iff.mpr fun y hy => hU12 y hy x hx
  have hz₁U₂ : ∀ x ∈ U₂, z₁ x = x := fun x hx => hz₁off x (hU₂U₁ x hx)
  obtain ⟨e, f, a, b, hF, hfs⟩ := exists_frame_fix_or_swap hc₀ hQ huO huu hm hdim τ₀
  rcases hfs with hfix | hsw
  ·
    obtain ⟨g, hg, hgF⟩ := exists_orthDerived_frame hQ hT hF hF₁ hw0 hw₁
    refine ⟨g, hg, 0, ?_⟩
    rw [pow_zero, mul_one]
    have hvO : g * u * g⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      mul_mem (mul_mem (hΩO hg) huO) (inv_mem (hΩO hg))
    have hvU : ∀ x ∈ U₁, (g * u * g⁻¹) x = x := by
      have hle : U₁ ≤ fixSpace (g * u * g⁻¹) := by
        rw [← hspan₁, Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        refine mem_fixSpace.mpr ?_
        rw [← hgF x, LinearEquiv.mul_apply, LinearEquiv.mul_apply, inv_apply_self,
          mem_fixSpace.mp (hfix x)]
      exact fun x hx => mem_fixSpace.mp (hle hx)
    exact (commute_of_fix hU₁ hz₁off hz₁U₁ hvU fun y hy => map_mem_orth_of_fix hvO hvU hy).symm
  ·
    have h12 : ∀ x y, polar Q (fvec e₁ f₁ a₁ b₁ x) (fvec e₂ f₂ a₂ b₂ y) = 0 := fun x y =>
      hU12 _ (hmem₁ x) _ (hmem₂ y)
    obtain ⟨g, hg, hgF⟩ := exists_orthDerived_frame_swap hQ hT huO hF hsw hF₁ hF₂ h12 hw0 hw₁ hw₂
    set v := g * u * g⁻¹ with hvdef
    have hvO : v ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      mul_mem (mul_mem (hΩO hg) huO) (inv_mem (hΩO hg))
    have hvΩ : v ∈ CFSG.RankThree.Classical2.orthDerived Q := mul_mem (mul_mem hg hu) (inv_mem hg)
    have hvv : v * v = 1 := by
      rw [hvdef]
      calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by rw [huu]; group
    have hv1 : ∀ x, v (fvec e₁ f₁ a₁ b₁ x) = fvec e₂ f₂ a₂ b₂ x := fun x => by
      rw [← (hgF x).1, hvdef, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        inv_apply_self, (hgF x).2]
    have hv2 : ∀ x, v (fvec e₂ f₂ a₂ b₂ x) = fvec e₁ f₁ a₁ b₁ x := fun x => by
      rw [← hv1 x, ← LinearEquiv.mul_apply, hvv, LinearEquiv.coe_one, id]
    have hvU₁ : ∀ x ∈ U₁, v x ∈ U₂ := by
      have hle : U₁ ≤ U₂.comap (v : V →ₗ[K] V) := by
        rw [← hspan₁, Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        change v _ ∈ U₂
        rw [hv1 x]
        exact hmem₂ x
      exact fun x hx => hle hx
    have hvperp : ∀ y ∈ U₂.orthogonalBilin (polarBilin Q),
        v y ∈ U₁.orthogonalBilin (polarBilin Q) := by
      intro y hy
      refine mem_orth_iff.mpr fun x hx => ?_
      have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hvO x (v y)
      rw [← LinearEquiv.mul_apply v v y, hvv, LinearEquiv.coe_one, id] at h1
      rw [← h1]
      exact mem_orth_iff.mp hy _ (hvU₁ x hx)
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    have hc : v * z₁ * v⁻¹ ∈ CFSG.RankThree.Classical2.orthDerived Q :=
      mul_mem (mul_mem hvΩ hz₁) (inv_mem hvΩ)
    have hcp : (v * z₁ * v⁻¹) ^ p = 1 := by rw [conj_pow, hz₁p, mul_one, mul_inv_cancel]
    have hc1 : v * z₁ * v⁻¹ ≠ 1 := fun h1 => hz₁1 (by
      calc z₁ = v⁻¹ * (v * z₁ * v⁻¹) * v := by group
        _ = 1 := by rw [h1]; group)
    have hcoff : ∀ y ∈ U₂.orthogonalBilin (polarBilin Q), (v * z₁ * v⁻¹) y = y := by
      intro y hy
      rw [hvinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hz₁off _ (hvperp y hy),
        ← LinearEquiv.mul_apply, hvv, LinearEquiv.coe_one, id]
    obtain ⟨h, hh, hhoff, k, hk⟩ := hF3 _ hc hcp hc1 hcoff
    refine ⟨h * g, mul_mem hh hg, k, ?_⟩
    have hhO := hΩO hh
    have hhz : h * z₁ = z₁ * h :=
      commute_of_fix hU₂ hhoff (fun x hx => map_mem_of_fix_orth hQ hhO hhoff hx) hz₁U₂
        fun y hy => map_mem_orth_of_fix hz₁O hz₁U₂ hy
    have e0 : h * g * u * (h * g)⁻¹ = h * v * h⁻¹ := by rw [hvdef]; group
    have e1 : h⁻¹ * z₁ * h = z₁ := by
      rw [mul_assoc, ← hhz, ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : h * v * h⁻¹ * z₁ = z₂ ^ k * (h * v * h⁻¹) := by
      rw [← hk]
      calc h * v * h⁻¹ * z₁ = h * v * (h⁻¹ * z₁ * h) * h⁻¹ := by group
        _ = h * (v * z₁ * v⁻¹) * h⁻¹ * (h * v * h⁻¹) := by rw [e1]; group
    have e3 : h * v * h⁻¹ * (h * v * h⁻¹) = 1 := by
      calc h * v * h⁻¹ * (h * v * h⁻¹) = h * (v * v) * h⁻¹ := by group
        _ = 1 := by rw [hvv]; group
    have e4 : z₂ ^ k = h * v * h⁻¹ * z₁ * (h * v * h⁻¹) := by
      rw [e2, mul_assoc, e3, mul_one]
    have e5 : h * v * h⁻¹ * z₂ ^ k = z₁ * (h * v * h⁻¹) := by
      rw [e4]
      calc h * v * h⁻¹ * (h * v * h⁻¹ * z₁ * (h * v * h⁻¹)) =
          (h * v * h⁻¹ * (h * v * h⁻¹)) * z₁ * (h * v * h⁻¹) := by group
        _ = z₁ * (h * v * h⁻¹) := by rw [e3, one_mul]
    have hzk : z₁ * z₂ ^ k = z₂ ^ k * z₁ := ((Commute.pow_right hz12 k)).eq
    rw [e0]
    calc h * v * h⁻¹ * (z₁ * z₂ ^ k) = (h * v * h⁻¹ * z₁) * z₂ ^ k := by group
      _ = z₂ ^ k * (h * v * h⁻¹ * z₂ ^ k) := by rw [e2]; group
      _ = z₂ ^ k * z₁ * (h * v * h⁻¹) := by rw [e5]; group
      _ = z₁ * z₂ ^ k * (h * v * h⁻¹) := by rw [← hzk]

end Core

end WitOmBlk

end CFSG.StandardType

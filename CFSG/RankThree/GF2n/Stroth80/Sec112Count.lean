module

public import CFSG.RankThree.GF2n.Stroth80.Sec114
public import CFSG.RankThree.OrthogonalInvolutions.Basic
import CFSG.RankThree.GF2n.Stroth80.Sec112Point
import CFSG.RankThree.GF2n.Stroth80.Sec112Model
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoBound
import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveIsometry
import CFSG.RankThree.OrthogonalInvolutions.FixHyperplane
import CFSG.RankThree.GF2n.Stroth80.Sec123Order

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions (commSpace fixSpace mem_fixSpace
  fixSpace_eq_orthogonal_commSpace)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B B' : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
variable {W : Submodule K M₀.E}

private def fixerW (W : Submodule K M₀.E) : Subgroup (M₀.E ≃ₗ[K] M₀.E) where
  carrier := {g | ∀ w ∈ W, g w = w}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {x y} hx hy => by
    show ∀ w ∈ W, (x * y) w = w
    intro w hw
    rw [LinearEquiv.mul_apply, hy w hw, hx w hw]
  inv_mem' := fun {x} hx => by
    show ∀ w ∈ W, (x⁻¹) w = w
    intro w hw
    have h2 : x ((x⁻¹) w) = x w := by
      rw [show x ((x⁻¹) w) = w from LinearEquiv.apply_symm_apply x w, hx w hw]
    exact x.injective h2

private theorem bar_LB_le_bar_H0 [(Q.subgroupOf M).Normal] (hc' : Ctx M Q Z B') :
    bar M Q (LB M Q B') ≤ bar M Q (H0 M Z) :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono M hc'.LB_le_H0)

private noncomputable def liftFOnBar [(Q.subgroupOf M).Normal]
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) (hc' : Ctx M Q Z B') :
    ↥(bar M Q (LB M Q B')) →* (M₀.E ≃ₗ[K] M₀.E) where
  toFun x := liftF φ (x : Mbar M Q)
  map_one' := liftF_one hφker
  map_mul' x y := by
    show liftF φ ((x : Mbar M Q) * (y : Mbar M Q)) =
      liftF φ (x : Mbar M Q) * liftF φ (y : Mbar M Q)
    exact liftF_mul hφker (mem_bar_H0_iff.mp (bar_LB_le_bar_H0 hc' x.2))
      (mem_bar_H0_iff.mp (bar_LB_le_bar_H0 hc' y.2))

private noncomputable def Lzero [(Q.subgroupOf M).Normal]
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) (hc' : Ctx M Q Z B') :
    Subgroup ↥(bar M Q (LB M Q B')) :=
  (fixerW W).comap (liftFOnBar φ hφker hc')

omit [Finite K] in
private theorem mem_Lzero [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    {hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q} {hc' : Ctx M Q Z B'}
    {x : ↥(bar M Q (LB M Q B'))} :
    x ∈ Lzero (W := W) φ hφker hc' ↔
      ∀ w ∈ W, liftF φ (x : Mbar M Q) w = w := Iff.rfl

private theorem exists_rep_of_mem_L [(Q.subgroupOf M).Normal] (hc' : Ctx M Q Z B')
    {x : Mbar M Q} (hx : x ∈ bar M Q (LB M Q B')) :
    ∃ l : G, ∃ hl : l ∈ LB M Q B', mkH M Q Z ⟨l, hc'.LB_le_H0 hl⟩ = x := by
  change x ∈ Subgroup.map (QuotientGroup.mk' (Q.subgroupOf M)) ((LB M Q B').subgroupOf M) at hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨⟨l, hlM⟩, hl, hxl⟩ := hx
  rw [Subgroup.mem_subgroupOf] at hl
  exact ⟨l, hl, by rw [← hxl]; rfl⟩

omit [Finite K] in
private theorem liftF_stabilizes_W_of_mem_HH [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W)
    {x : Mbar M Q} (hx : x ∈ bar M Q (H0 M Z)) {w : M₀.E} (hw : w ∈ W) :
    liftF φ x w ∈ W := by
  obtain ⟨g, rfl⟩ := mem_bar_H0_iff.mp hx
  rw [liftF_mkH hφker]
  exact hWst g w hw

omit [Finite K] in
private theorem liftF_mem_orthogonalGroup_of_mem_HH [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e)
    {x : Mbar M Q} (hx : x ∈ bar M Q (H0 M Z)) :
    liftF φ x ∈ TauCeti.QuadraticMap.orthogonalGroup M₀.toQuadraticForm := by
  obtain ⟨g, rfl⟩ := mem_bar_H0_iff.mp hx
  rw [liftF_mkH hφker]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hφiso g)

omit [Finite K] in
private theorem liftF_preserves_B_of_mem_HH [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e)
    {x : Mbar M Q} (hx : x ∈ bar M Q (H0 M Z)) (a b : M₀.E) :
    M₀.B (liftF φ x a) (liftF φ x b) = M₀.B a b := by
  have hO := liftF_mem_orthogonalGroup_of_mem_HH hφker hφiso hx
  have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO a b
  rwa [Tim79.QuadModel.polar_toQuadraticForm, Tim79.QuadModel.polar_toQuadraticForm] at h

private theorem liftF_fixes_perp_of_mem_L [(Q.subgroupOf M).Normal]
    (hc' : Ctx M Q Z B') (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B' ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B' : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W) (hbW : b ∉ W)
    {x : Mbar M Q} (hx : x ∈ bar M Q (LB M Q B')) {y : M₀.E} (hyW : y ∈ W)
    (hyb : M₀.B y b = 0) : liftF φ x y = y := by
  obtain ⟨l, hl, hxl⟩ := exists_rep_of_mem_L hc' hx
  have hfix := Ctx.LB_fixes_of_perp (B := B') hc' h hφπ hB hcent hWst hbW hl hyW hyb
  rw [← hxl, liftF_mkH hφker]
  exact hfix

omit [Finite G] in
omit [Finite K] in
private theorem le_sup_ker_of_dual_eq_one {μ : Module.Dual K M₀.E} {v₁ : M₀.E}
    (hv₁ : v₁ ∈ W) (hμ : μ v₁ = 1) :
    W ≤ (W ⊓ LinearMap.ker μ) ⊔ Submodule.span K ({v₁} : Set M₀.E) := by
  intro w hw
  have hmem : w - μ w • v₁ ∈ W ⊓ LinearMap.ker μ := by
    refine ⟨W.sub_mem hw (W.smul_mem _ hv₁), ?_⟩
    show μ (w - μ w • v₁) = 0
    simp [LinearMap.map_sub, hμ]
  have hspan : μ w • v₁ ∈ Submodule.span K ({v₁} : Set M₀.E) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v₁))
  have hw' : w = (w - μ w • v₁) + μ w • v₁ := by abel
  rw [hw']
  exact Submodule.add_mem _ (Submodule.mem_sup_left hmem) (Submodule.mem_sup_right hspan)

omit [Finite G] in
omit [Finite K] in
private theorem exists_dual_eq_one_of_not_le_perp {b : M₀.E}
    (h : ¬ ∀ w ∈ W, M₀.B w b = 0) :
    ∃ v₁ ∈ W, (M₀.B.flip b) v₁ = 1 := by
  push Not at h
  obtain ⟨v₀, hv₀W, hv₀b⟩ := h
  refine ⟨(M₀.B v₀ b)⁻¹ • v₀, W.smul_mem _ hv₀W, ?_⟩
  rw [LinearMap.BilinForm.flip_apply, map_smul]
  show ((M₀.B v₀) b)⁻¹ * ((M₀.B v₀) b) = 1
  exact inv_mul_cancel₀ hv₀b

private theorem liftF_fixes_hyperplane_of_mem_L [(Q.subgroupOf M).Normal]
    (hc' : Ctx M Q Z B') (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B' ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B' : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W) (hbW : b ∉ W)
    {x : Mbar M Q} (hx : x ∈ bar M Q (LB M Q B')) :
    ∀ z ∈ W, (M₀.B.flip b) z = 0 → liftF φ x z = z := by
  intro z hz hzμ
  refine liftF_fixes_perp_of_mem_L hc' h hφπ hφker hB hcent hWst hbW hx hz ?_
  rwa [LinearMap.BilinForm.flip_apply] at hzμ

private theorem liftF_moves_of_not_mem_Lzero [(Q.subgroupOf M).Normal]
    (hc' : Ctx M Q Z B') (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B' ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B' : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W) (hbW : b ∉ W)
    {x : ↥(bar M Q (LB M Q B'))} (hx : x ∉ Lzero (W := W) φ hφker hc')
    {v₁ : M₀.E} (hv₁W : v₁ ∈ W) (hμ : (M₀.B.flip b) v₁ = 1) :
    liftF φ (x : Mbar M Q) v₁ ≠ v₁ := by
  intro hfix
  apply hx
  rw [mem_Lzero]
  intro w hw
  have hdecomp := le_sup_ker_of_dual_eq_one (W := W) (μ := M₀.B.flip b) hv₁W hμ
  obtain ⟨z₀, hz₀, u, hu, hzu⟩ := Submodule.mem_sup.mp (hdecomp hw)
  rw [← hzu]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hu
  rw [← ha]
  have hzb : M₀.B z₀ b = 0 := by
    rw [← LinearMap.BilinForm.flip_apply]
    exact LinearMap.mem_ker.mp hz₀.2
  have hfixH : liftF φ (x : Mbar M Q) z₀ = z₀ :=
    liftF_fixes_perp_of_mem_L hc' h hφπ hφker hB hcent hWst hbW x.2 hz₀.1 hzb
  rw [map_add, map_smul, hfixH, hfix]

private theorem liftF_eqOn_W_of_not_mem_Lzero [(Q.subgroupOf M).Normal]
    (hc' : Ctx M Q Z B') (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B' ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B' : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (hWnd : ∀ x ∈ W, (∀ y ∈ W, M₀.B x y = 0) → x = 0)
    (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W) (hbW : b ∉ W)
    (hWperp : ¬ ∀ w ∈ W, M₀.B w b = 0)
    {x y : ↥(bar M Q (LB M Q B'))}
    (hx : x ∉ Lzero (W := W) φ hφker hc') (hy : y ∉ Lzero (W := W) φ hφker hc') :
    ∀ w ∈ W, liftF φ (x : Mbar M Q) w = liftF φ (y : Mbar M Q) w := by
  obtain ⟨v₁, hv₁W, hμ⟩ := exists_dual_eq_one_of_not_le_perp hWperp
  have hWnd' : ∀ z ∈ W, (∀ w ∈ W, QuadraticMap.polar M₀.toQuadraticForm z w = 0) → z = 0 := by
    intro z hz hp
    refine hWnd z hz fun w hw => ?_
    rw [← Tim79.QuadModel.polar_toQuadraticForm]
    exact hp w hw
  have hxH : (x : Mbar M Q) ∈ bar M Q (H0 M Z) := bar_LB_le_bar_H0 hc' x.2
  have hyH : (y : Mbar M Q) ∈ bar M Q (H0 M Z) := bar_LB_le_bar_H0 hc' y.2
  exact CFSG.RankThree.OrthogonalInvolutions.eqOn_of_fix_ker hWnd' (M₀.B.flip b) hv₁W hμ
    (liftF_mem_orthogonalGroup_of_mem_HH hφker hφiso hxH)
    (liftF_mem_orthogonalGroup_of_mem_HH hφker hφiso hyH)
    (fun w hw => liftF_stabilizes_W_of_mem_HH hφker hWst hxH hw)
    (fun w hw => liftF_stabilizes_W_of_mem_HH hφker hWst hyH hw)
    (liftF_fixes_hyperplane_of_mem_L hc' h hφπ hφker hB hcent hWst hbW x.2)
    (liftF_fixes_hyperplane_of_mem_L hc' h hφπ hφker hB hcent hWst hbW y.2)
    (liftF_moves_of_not_mem_Lzero hc' h hφπ hφker hB hcent hWst hbW hx hv₁W hμ)
    (liftF_moves_of_not_mem_Lzero hc' h hφπ hφker hB hcent hWst hbW hy hv₁W hμ)

private theorem Lzero_eq_top_of_le_perp [(Q.subgroupOf M).Normal]
    (hc' : Ctx M Q Z B') (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B' ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B' : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W) (hbW : b ∉ W)
    (hWperp : ∀ w ∈ W, M₀.B w b = 0) :
    Lzero (W := W) φ hφker hc' = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_Lzero]
  intro w hw
  exact liftF_fixes_perp_of_mem_L hc' h hφπ hφker hB hcent hWst hbW x.2 hw (hWperp w hw)

private theorem mul_mem_Lzero_of_not_mem [(Q.subgroupOf M).Normal]
    (hc' : Ctx M Q Z B') (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B' ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B' : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (hWnd : ∀ x ∈ W, (∀ y ∈ W, M₀.B x y = 0) → x = 0)
    (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W) (hbW : b ∉ W)
    (hWperp : ¬ ∀ w ∈ W, M₀.B w b = 0)
    {a c : ↥(bar M Q (LB M Q B'))} (ha : a ∉ Lzero (W := W) φ hφker hc')
    (hc : c ∉ Lzero (W := W) φ hφker hc') :
    c * a ∈ Lzero (W := W) φ hφker hc' := by
  rw [mem_Lzero]
  intro w hw
  have hac := liftF_eqOn_W_of_not_mem_Lzero hc' h hφπ hφker hφiso hB hcent hWnd hWst
    hbW hWperp ha hc
  have haH : (a : Mbar M Q) ∈ bar M Q (H0 M Z) := bar_LB_le_bar_H0 hc' a.2
  have hcH : (c : Mbar M Q) ∈ bar M Q (H0 M Z) := bar_LB_le_bar_H0 hc' c.2
  have haE : ∃ g : ↥(H0 M Z), mkH M Q Z g = (a : Mbar M Q) := mem_bar_H0_iff.mp haH
  have hcE : ∃ g : ↥(H0 M Z), mkH M Q Z g = (c : Mbar M Q) := mem_bar_H0_iff.mp hcH
  have hsq : liftF φ (a : Mbar M Q) * liftF φ (a : Mbar M Q) = 1 := by
    have ha2 : (a : Mbar M Q) ^ 2 = 1 := by
      simpa using (hc'.isElemAbelian_bar_LB).2 (a : Mbar M Q) a.2
    rw [← liftF_mul hφker haE haE, ← pow_two, ha2, liftF_one hφker]
  change liftF φ ((c : Mbar M Q) * (a : Mbar M Q)) w = w
  rw [liftF_mul hφker hcE haE, LinearEquiv.mul_apply]
  calc liftF φ (c : Mbar M Q) (liftF φ (a : Mbar M Q) w)
      = liftF φ (a : Mbar M Q) (liftF φ (a : Mbar M Q) w) :=
          (hac _ (liftF_stabilizes_W_of_mem_HH hφker hWst haH hw)).symm
    _ = w := by rw [← LinearEquiv.mul_apply, hsq]; rfl

private theorem index_Lzero_dvd_two [(Q.subgroupOf M).Normal]
    (hc' : Ctx M Q Z B') (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B' ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B' : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (hWnd : ∀ x ∈ W, (∀ y ∈ W, M₀.B x y = 0) → x = 0)
    (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W) (hbW : b ∉ W) :
    (Lzero (W := W) φ hφker hc').index ∣ 2 := by
  by_cases htop : Lzero (W := W) φ hφker hc' = ⊤
  · simp [htop]
  · obtain ⟨a, ha⟩ : ∃ a : ↥(bar M Q (LB M Q B')), a ∉ Lzero (W := W) φ hφker hc' := by
      by_contra hcon
      push Not at hcon
      exact htop (eq_top_iff.mpr fun x _ => hcon x)
    have hWperp : ¬ ∀ w ∈ W, M₀.B w b = 0 := by
      intro hperp
      exact htop (Lzero_eq_top_of_le_perp hc' h hφπ hφker hB hcent hWst hbW hperp)
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨a, fun c => ?_⟩
    by_cases hc : c ∈ Lzero (W := W) φ hφker hc'
    · exact Or.inr hc
    · exact Or.inl (mul_mem_Lzero_of_not_mem hc' h hφπ hφker hφiso hB hcent hWnd hWst
        hbW hWperp ha hc)

private theorem card_bar_LB_le_two_mul_card_Lzero [(Q.subgroupOf M).Normal]
    (hc' : Ctx M Q Z B') (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B' ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B' : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (hWnd : ∀ x ∈ W, (∀ y ∈ W, M₀.B x y = 0) → x = 0)
    (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W) (hbW : b ∉ W) :
    Nat.card ↥(bar M Q (LB M Q B')) ≤ 2 * Nat.card ↥(Lzero (W := W) φ hφker hc') := by
  have hdvd := index_Lzero_dvd_two hc' h hφπ hφker hφiso hB hcent hWnd hWst hbW
  have hmul := Subgroup.card_mul_index (Lzero (W := W) φ hφker hc')
  have hle : (Lzero (W := W) φ hφker hc').index ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  calc Nat.card ↥(bar M Q (LB M Q B'))
      = Nat.card ↥(Lzero (W := W) φ hφker hc') *
          (Lzero (W := W) φ hφker hc').index := hmul.symm
    _ ≤ Nat.card ↥(Lzero (W := W) φ hφker hc') * 2 := Nat.mul_le_mul_left _ hle
    _ = 2 * Nat.card ↥(Lzero (W := W) φ hφker hc') := Nat.mul_comm _ _

private noncomputable def LzeroBar [(Q.subgroupOf M).Normal]
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) (hc' : Ctx M Q Z B') :
    Subgroup (Mbar M Q) :=
  (Lzero (W := W) φ hφker hc').map (bar M Q (LB M Q B')).subtype

omit [Finite K] in
private theorem card_LzeroBar [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    {hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q} {hc' : Ctx M Q Z B'} :
    Nat.card ↥(LzeroBar (W := W) φ hφker hc') =
      Nat.card ↥(Lzero (W := W) φ hφker hc') := by
  change Nat.card ↥(Subgroup.map (bar M Q (LB M Q B')).subtype
    (Lzero (W := W) φ hφker hc')) = Nat.card ↥(Lzero (W := W) φ hφker hc')
  exact Subgroup.card_map_of_injective (bar M Q (LB M Q B')).subtype_injective

omit [Finite K] in
private theorem LzeroBar_le_centralizer [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    {hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q} {hc' : Ctx M Q Z B'}
    (hL0C : ∀ x ∈ Lzero (W := W) φ hφker hc',
      (x : Mbar M Q) ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) :
    LzeroBar (W := W) φ hφker hc' ≤
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact hL0C x hx

omit [Finite K] in
private theorem LzeroBar_le_H0 [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    {hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q} (hc' : Ctx M Q Z B') :
    LzeroBar (W := W) φ hφker hc' ≤ bar M Q (H0 M Z) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact bar_LB_le_bar_H0 hc' x.2

omit [Finite K] in
private theorem isPGroup_LzeroBar [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    {hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q} (hc' : Ctx M Q Z B') :
    IsPGroup 2 ↥(LzeroBar (W := W) φ hφker hc') :=
  ((hc'.isPGroup_bar_LB).to_subgroup (Lzero (W := W) φ hφker hc')).of_equiv
    (Subgroup.equivMapOfInjective (Lzero (W := W) φ hφker hc')
      (bar M Q (LB M Q B')).subtype (bar M Q (LB M Q B')).subtype_injective)

private theorem orthogonal_le_ker_opm_of_mem_Ebar [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hWE : ∀ e ∈ Ebar M Q Z B, commSpace (liftF φ e) ≤ W)
    {e : Mbar M Q} (he : e ∈ Ebar M Q Z B) :
    M₀.B.orthogonal W ≤ (opm (liftF φ e)).ker := by
  have hBeq : QuadraticMap.polarBilin M₀.toQuadraticForm = M₀.B := by
    ext a b
    rw [QuadraticMap.polarBilin_apply_apply, Tim79.QuadModel.polar_toQuadraticForm]
  intro y hy
  rw [LinearMap.mem_ker, opm_apply, sub_eq_zero]
  have hyW : y ∈ M₀.B.orthogonal (commSpace (liftF φ e)) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy ⊢
    intro z hz
    exact hy z (hWE e he hz)
  have heOrth := Ctx.isOrthA2_liftF_of_mem_Ebar hc h hφπ hφker he
  have hfixeq := fixSpace_eq_orthogonal_commSpace
    (polarBilin_toQuadraticForm_nondegenerate M₀) heOrth.mem heOrth.mul_self
  rw [hBeq] at hfixeq
  rw [← hfixeq, mem_fixSpace] at hyW
  exact hyW

omit [Finite K] in
private theorem eq_of_liftF_eq_on_HH [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    {a b : Mbar M Q} (ha : a ∈ bar M Q (H0 M Z)) (hb : b ∈ bar M Q (H0 M Z))
    (hab : liftF φ a = liftF φ b) : a = b := by
  have h1 : (⟨a, ha⟩ : ↥(bar M Q (H0 M Z))) = ⟨b, hb⟩ := by
    apply barH0Act_injective hφker
    rw [barH0Act_apply, barH0Act_apply]
    exact hab
  exact congrArg Subtype.val h1

private theorem liftF_commute_of_mem_Lzero_of_mem_Ebar [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (hc' : Ctx M Q Z B') (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e)
    (hWE : ∀ e ∈ Ebar M Q Z B, commSpace (liftF φ e) ≤ W)
    {x : ↥(bar M Q (LB M Q B'))} (hx : x ∈ Lzero (W := W) φ hφker hc')
    {e : Mbar M Q} (he : e ∈ Ebar M Q Z B) :
    e * (x : Mbar M Q) = (x : Mbar M Q) * e := by
  have heH : e ∈ bar M Q (H0 M Z) := hc.Ebar_subset_H he
  have hxH : (x : Mbar M Q) ∈ bar M Q (H0 M Z) := bar_LB_le_bar_H0 hc' x.2
  have hxA := liftF_mem_orthogonalGroup_of_mem_HH hφker hφiso hxH
  have hu := liftF_preserves_B_of_mem_HH hφker hφiso hxH
  have hr : (opm (liftF φ e)).range ≤ W := by
    change LinearMap.range ((liftF φ e : M₀.E →ₗ[K] M₀.E) - 1) ≤ W
    exact hWE e he
  have hcomm := mul_comm_of_fixes (M₀.B) (liftF φ (x : Mbar M Q)) (liftF φ e) hu W
    (mem_Lzero.mp hx) hr (orthogonal_le_ker_opm_of_mem_Ebar hc h hφπ hφker hWE he)
  have hmul1 : liftF φ ((x : Mbar M Q) * e) = liftF φ (e * (x : Mbar M Q)) := by
    have hxE : ∃ g : ↥(H0 M Z), mkH M Q Z g = (x : Mbar M Q) := mem_bar_H0_iff.mp hxH
    have heE : ∃ g : ↥(H0 M Z), mkH M Q Z g = e := mem_bar_H0_iff.mp heH
    rw [liftF_mul hφker hxE heE, liftF_mul hφker heE hxE]
    exact hcomm
  exact (eq_of_liftF_eq_on_HH hφker ((bar M Q (H0 M Z)).mul_mem hxH heH)
    ((bar M Q (H0 M Z)).mul_mem heH hxH) hmul1).symm

private theorem Lzero_le_centralizer_Xbar [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (hc' : Ctx M Q Z B') (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e)
    (hWE : ∀ e ∈ Ebar M Q Z B, commSpace (liftF φ e) ≤ W) :
    ∀ x ∈ Lzero (W := W) φ hφker hc',
      (x : Mbar M Q) ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem e he => exact liftF_commute_of_mem_Lzero_of_mem_Ebar hc hc' h hφπ hφker hφiso hWE hx he
  | one => rw [one_mul, mul_one]
  | mul a b ha hb hax hbx => rw [mul_assoc, hbx, ← mul_assoc, hax, mul_assoc]
  | inv a ha hax =>
    have h1 : a * (a⁻¹ * (x : Mbar M Q)) = a * ((x : Mbar M Q) * a⁻¹) := by
      calc a * (a⁻¹ * (x : Mbar M Q)) = (a * a⁻¹) * (x : Mbar M Q) := by rw [mul_assoc]
        _ = (x : Mbar M Q) := by rw [mul_inv_cancel, one_mul]
        _ = ((x : Mbar M Q) * a) * a⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = (a * (x : Mbar M Q)) * a⁻¹ := by rw [hax]
        _ = a * ((x : Mbar M Q) * a⁻¹) := by rw [mul_assoc]
    exact mul_left_cancel h1

omit [Finite K] in
private theorem card_Lzero_dvd_of_embedding [(Q.subgroupOf M).Normal] {K' : Type}
    [Field K'] [Finite K']
    (hc' : Ctx M Q Z B') {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hL0C : ∀ x ∈ Lzero (W := W) φ hφker hc',
      (x : Mbar M Q) ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    (f : ↥(Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z)) →*
      GL (Fin 2) K') (hf : Function.Injective f) {q : ℕ}
    (hK' : Nat.card K' = 2 ^ q) (hq : 1 ≤ q) :
    Nat.card ↥(Lzero (W := W) φ hφker hc') ∣ Nat.card K' := by
  have hΛ : LzeroBar (W := W) φ hφker hc' ≤
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z) :=
    le_inf (LzeroBar_le_centralizer hL0C) (LzeroBar_le_H0 hc')
  let f' : ↥(LzeroBar (W := W) φ hφker hc') →* GL (Fin 2) K' :=
    f.comp (Subgroup.inclusion hΛ)
  have hf' : Function.Injective f' := hf.comp (Subgroup.inclusion_injective hΛ)
  let A : Subgroup (GL (Fin 2) K') := Subgroup.map f' ⊤
  have hpTop : IsPGroup 2 ↥(⊤ : Subgroup ↥(LzeroBar (W := W) φ hφker hc')) :=
    (isPGroup_LzeroBar (W := W) hc').of_equiv (Subgroup.topEquiv).symm
  have hpA : IsPGroup 2 ↥A := hpTop.of_equiv (Subgroup.equivMapOfInjective ⊤ f' hf')
  have hcardA : Nat.card ↥A = Nat.card ↥(Lzero (W := W) φ hφker hc') := by
    have h1 : Nat.card ↥A = Nat.card ↥(LzeroBar (W := W) φ hφker hc') := by
      rw [show A = Subgroup.map f' ⊤ from rfl]
      rw [Subgroup.card_map_of_injective hf', Subgroup.card_top]
    rw [h1, card_LzeroBar (W := W) (φ := φ) (hφker := hφker) (hc' := hc')]
  have hdvd := card_dvd_of_isPGroup_subgroup_GL_two hq hK' A hpA
  rwa [hcardA] at hdvd

omit [Finite K] in
private theorem card_Lzero_dvd_card_Z [(Q.subgroupOf M).Normal] [CharP K 2]
    (hc : Ctx M Q Z B) (hc' : Ctx M Q Z B') {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hA : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hL0C : ∀ x ∈ Lzero (W := W) φ hφker hc',
      (x : Mbar M Q) ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) :
    Nat.card ↥(Lzero (W := W) φ hφker hc') ∣ Nat.card Z := by
  obtain ⟨K', hK'f, hK'fin, hK'card, f, hf⟩ :=
    stroth114_holds (G := G) (M := M) (Q := Q) (Z := Z) (B := B) (n := n) hc hw hn hA
  let := hK'f
  let := hK'fin
  obtain ⟨q, k, hqZ, -⟩ := hc.hyp.cp
  have hK'x : Nat.card K' = 2 ^ q := by rw [hK'card, hqZ]
  have hq : 1 ≤ q := by
    apply Nat.pos_of_ne_zero
    intro h0
    have h1 : Nat.card Z = 1 := by simpa [h0] using hqZ
    have h4 : 4 ≤ Nat.card Z := hc.hyp.q4
    rw [h1] at h4
    omega
  have h := card_Lzero_dvd_of_embedding (W := W) hc' hφker hL0C f hf hK'x hq
  rwa [hK'card] at h

theorem Ctx.img_le_of_planes_le [(Q.subgroupOf M).Normal] [CharP K 2] (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hA : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {W : Submodule K M₀.E}
    (hWnd : ∀ x ∈ W, (∀ y ∈ W, M₀.B x y = 0) → x = 0)
    (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W)
    (hWE : ∀ e ∈ Ebar M Q Z B, commSpace (liftF φ e) ≤ W) {B' : Subgroup G}
    (hc' : Ctx M Q Z B') : ∀ v ∈ M₀.img B', v ∈ W := by
  intro v hv
  obtain ⟨b, hb0, hbQf, hB, hcent, hcard⟩ := Ctx.dictB hc' h
  have hbW : b ∈ W := by
    by_contra hbW
    have hcardL := card_bar_LB_le_two_mul_card_Lzero hc' h hφπ hφker hφiso hB hcent hWnd hWst hbW
    have hL0C := Lzero_le_centralizer_Xbar hc hc' h hφπ hφker hφiso hWE
    have hdvd := card_Lzero_dvd_card_Z hc hc' hw hn hA (φ := φ) hφker hL0C
    have hqpos : 0 < Nat.card Z := Nat.card_pos
    have hL0le : Nat.card ↥(Lzero (W := W) φ hφker hc') ≤ Nat.card Z :=
      Nat.le_of_dvd hqpos hdvd
    have hq2 := hc'.card_bar_LB_ge_two hw hn
    have h2q : 2 * Nat.card Z < Nat.card Z ^ 2 := by
      have h4 : 4 ≤ Nat.card Z := hc'.hyp.q4
      nlinarith
    have hle : Nat.card Z ^ 2 ≤ 2 * Nat.card Z :=
      le_trans hq2 (le_trans hcardL (Nat.mul_le_mul_left 2 hL0le))
    exact absurd hle (not_le.mpr h2q)
  obtain ⟨s, hs⟩ := (hB v).mp hv
  rw [hs]
  exact W.smul_mem s hbW


end CFSG.RankThree.GF2n.Stroth80

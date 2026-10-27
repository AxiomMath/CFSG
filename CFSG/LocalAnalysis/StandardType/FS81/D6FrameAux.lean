module

public import CFSG.LocalAnalysis.StandardType.FS81.D6HostsAux
public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelOm
public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelRoot
public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelPerp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalInvolution.WeakCT
open CFSG.SeitzReduction.OmegaPilot (plusNodeSet)

section Transport

variable {G : Type} [Group G] {K : Subgroup G}

noncomputable abbrev trElt (e : ↥K ≃* ↥Om12) (x : ↥Om12) : G := ((e.symm x : ↥K) : G)

theorem trElt_mem_tr (e : ↥K ≃* ↥Om12) {x : ↥Om12} {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hx : (x : V12 ≃ₗ[ZMod 2] V12) ∈ X) : trElt e x ∈ tr e X :=
  mem_tr.mpr ⟨x, hx, rfl⟩

theorem trElt_mul (e : ↥K ≃* ↥Om12) (x y : ↥Om12) :
    trElt e (x * y) = trElt e x * trElt e y := by
  simp only [trElt, map_mul, Subgroup.coe_mul]

theorem trElt_conj_mem (e : ↥K ≃* ↥Om12) {x : ↥Om12} {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hX : ∀ z ∈ X, (x : V12 ≃ₗ[ZMod 2] V12) * z * (x : V12 ≃ₗ[ZMod 2] V12)⁻¹ ∈ X) :
    ∀ g ∈ tr e X, trElt e x * g * (trElt e x)⁻¹ ∈ tr e X := by
  intro g hg
  obtain ⟨y, hyX, rfl⟩ := mem_tr.mp hg
  refine mem_tr.mpr ⟨x * y * x⁻¹, ?_, ?_⟩
  · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hX _ hyX
  · simp only [trElt, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem mem_pull {e : ↥K ≃* ↥Om12} {H : Subgroup G} {z : V12 ≃ₗ[ZMod 2] V12} :
    z ∈ pull e H ↔ ∃ y : ↥Om12, ((e.symm y : ↥K) : G) ∈ H ∧ (y : V12 ≃ₗ[ZMod 2] V12) = z := by
  simp only [pull, Subgroup.mem_map, Subgroup.mem_comap, MonoidHom.coe_comp,
    Function.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]

theorem pull_conj_mem (e : ↥K ≃* ↥Om12) {H : Subgroup G} {h : G} (hK : h ∈ K)
    (hH : ∀ k ∈ H, h * k * h⁻¹ ∈ H) :
    ∀ z ∈ pull e H, ((e ⟨h, hK⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) * z *
      ((e ⟨h, hK⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12)⁻¹ ∈ pull e H := by
  intro z hz
  obtain ⟨y, hyH, rfl⟩ := mem_pull.mp hz
  refine mem_pull.mpr ⟨e ⟨h, hK⟩ * y * (e ⟨h, hK⟩)⁻¹, ?_, by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]⟩
  have hy : ((e.symm (e ⟨h, hK⟩ * y * (e ⟨h, hK⟩)⁻¹) : ↥K) : G) =
      h * ((e.symm y : ↥K) : G) * h⁻¹ := by
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hy]
  exact hH _ hyH

theorem tr_map_conj (e : ↥K ≃* ↥Om12) (x : ↥Om12) {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hX : X ≤ Om12) :
    tr e (X.map (MulAut.conj (x : V12 ≃ₗ[ZMod 2] V12)).toMonoidHom) =
      (tr e X).map (MulAut.conj (trElt e x)).toMonoidHom := by
  ext g
  constructor
  · intro hg
    obtain ⟨y, ⟨z, hz, hzy⟩, rfl⟩ := mem_tr.mp hg
    have hzO : z ∈ Om12 := hX hz
    refine ⟨trElt e ⟨z, hzO⟩, mem_tr.mpr ⟨⟨z, hzO⟩, hz, rfl⟩, ?_⟩
    have hy : y = x * ⟨z, hzO⟩ * x⁻¹ := Subtype.ext (by simpa using hzy.symm)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hy, trElt, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_inv]
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨z, hz, rfl⟩ := mem_tr.mp hg'
    refine mem_tr.mpr ⟨x * z * x⁻¹, ⟨z, hz, ?_⟩, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, trElt, map_mul, map_inv,
        Subgroup.coe_mul, Subgroup.coe_inv]

end Transport

section Conj

variable {H : Type} [Group H]

theorem map_conj_eq_of_commute {X : Subgroup H} {g : H} (h : ∀ x ∈ X, g * x = x * g) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  have key : ∀ x ∈ X, g * x * g⁻¹ = x := fun x hx => by rw [h x hx, mul_inv_cancel_right]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    show g * x * g⁻¹ ∈ X
    rw [key x hx]
    exact hx
  · intro hz
    exact ⟨z, hz, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, key z hz]⟩

theorem map_conj_mul_eq {X : Subgroup H} {m c : H} (hm : m ∈ X) (hc : ∀ x ∈ X, c * x = x * c) :
    X.map (MulAut.conj (m * c)).toMonoidHom = X := by
  have key : ∀ x ∈ X, (m * c) * x * (m * c)⁻¹ = m * x * m⁻¹ := fun x hx => by
    rw [mul_inv_rev, mul_assoc m c x, hc x hx]
    group
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    show (m * c) * x * (m * c)⁻¹ ∈ X
    rw [key x hx]
    exact X.mul_mem (X.mul_mem hm hx) (X.inv_mem hm)
  · intro z hz
    have hz' : m⁻¹ * z * m ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hm) hz) hm
    refine ⟨m⁻¹ * z * m, hz', ?_⟩
    show (m * c) * (m⁻¹ * z * m) * (m * c)⁻¹ = z
    rw [key _ hz']
    group

theorem commute_map_conj {X Y : Subgroup H} {g : H} (hXY : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a)
    (hg : ∀ b ∈ Y, g * b = b * g) :
    ∀ a ∈ X.map (MulAut.conj g).toMonoidHom, ∀ b ∈ Y, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ b hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have h1 : g⁻¹ * b = b * g⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hg b hb, mul_assoc, mul_inv_cancel, mul_one]
  calc g * a * g⁻¹ * b = g * (a * b) * g⁻¹ := by rw [mul_assoc, h1]; group
    _ = g * (b * a) * g⁻¹ := by rw [hXY a ha b hb]
    _ = b * (g * a * g⁻¹) := by rw [← mul_assoc g b a, hg b hb]; group

theorem pair_map_conj {W X Y : Subgroup H} (h : LinearBlockStandardPair (ZMod 2) W X Y) (g : H) :
    LinearBlockStandardPair (ZMod 2) (W.map (MulAut.conj g).toMonoidHom)
      (X.map (MulAut.conj g).toMonoidHom) (Y.map (MulAut.conj g).toMonoidHom) :=
  CFSG.ClassicalInvolution.Models.linearBlockStandardPair_map h _ (MulAut.conj g).injective

theorem pair_symm {W X Y : Subgroup H} (h : LinearBlockStandardPair (ZMod 2) W X Y) :
    LinearBlockStandardPair (ZMod 2) W Y X := by
  obtain ⟨θ, c, h1, h2, h3⟩ := h
  exact ⟨θ, c, h1, h2, h3.symm⟩

end Conj

theorem Om12_le_O12 : Om12 ≤ TauCeti.QuadraticMap.orthogonalGroup Q12 :=
  Subgroup.commutator_le_self _

theorem apply_mem_subCommSpace {Z : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {g : V12 ≃ₗ[ZMod 2] V12}
    (hg : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) {v : V12} (hv : v ∈ subCommSpace Z) :
    g v ∈ subCommSpace Z := by
  have hle : Z.map (MulAut.conj g).toMonoidHom ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    exact hg z hz
  have h1 : (subCommSpace Z).map (g : V12 →ₗ[ZMod 2] V12) ≤ subCommSpace Z := by
    rw [← subCommSpace_map_conj]
    exact iSup₂_le fun z hz => le_iSup₂_of_le z (hle hz) le_rfl
  exact h1 ⟨v, hv, rfl⟩

theorem subCommSpace_node2 : subCommSpace (node 2) = Y2 := by
  rw [subCommSpace_node, plusNodeSet_six.2.2.1]
  rfl

theorem subCommSpace_node_zero : subCommSpace (node 0) = planeSpan {0, 1} := by
  rw [subCommSpace_node, plusNodeSet_six.1]

theorem subCommSpace_node_one : subCommSpace (node 1) = planeSpan {1, 2} := by
  rw [subCommSpace_node, plusNodeSet_six.2.1]

theorem subCommSpace_node_four : subCommSpace (node 4) = planeSpan {4, 5} := by
  rw [subCommSpace_node, plusNodeSet_six.2.2.2.2.1]

theorem Y2_le_compl {P : Finset (Fin 6)} (h : Disjoint ({2, 3} : Finset (Fin 6)) P) :
    Y2 ≤ planeSpan Pᶜ :=
  planeSpan_mono fun _ hx => Finset.mem_compl.mpr fun hxP => Finset.disjoint_left.mp h hx hxP

theorem fixY2_node (j : Fin 6) (hj : Disjoint ({2, 3} : Finset (Fin 6)) (plusNodeSet 6 j))
    {z : V12 ≃ₗ[ZMod 2] V12} (hz : z ∈ node j) : ∀ v ∈ Y2, z v = v :=
  fun _ hv => node_apply_eq_self j hz (Y2_le_compl hj hv)

theorem fixY2_node0 {z : V12 ≃ₗ[ZMod 2] V12} (hz : z ∈ node 0) : ∀ v ∈ Y2, z v = v :=
  fixY2_node 0 (by rw [plusNodeSet_six.1]; decide) hz

theorem fixY2_node4 {z : V12 ≃ₗ[ZMod 2] V12} (hz : z ∈ node 4) : ∀ v ∈ Y2, z v = v :=
  fixY2_node 4 (by rw [plusNodeSet_six.2.2.2.2.1]; decide) hz

theorem fixY2_node5 {z : V12 ≃ₗ[ZMod 2] V12} (hz : z ∈ node 5) : ∀ v ∈ Y2, z v = v :=
  fixY2_node 5 (by rw [plusNodeSet_six.2.2.2.2.2]; decide) hz

theorem fixY2_flip0 {z : V12 ≃ₗ[ZMod 2] V12} (hz : z ∈ flip0) : ∀ v ∈ Y2, z v = v :=
  fun _ hv => rootL_apply_eq_self (by decide : (0 : Fin 6) ≠ 1) hz (Y2_le_compl (by decide) hv)

theorem mapsY2_node2 {z : V12 ≃ₗ[ZMod 2] V12} (hz : z ∈ node 2) {v : V12} (hv : v ∈ Y2) :
    z v ∈ Y2 :=
  node_apply_mem 2 (by rw [plusNodeSet_six.2.2.1]) hz hv

theorem mapsY2_flip2 {z : V12 ≃ₗ[ZMod 2] V12} (hz : z ∈ flip2) {v : V12} (hv : v ∈ Y2) :
    z v ∈ Y2 :=
  rootL_apply_mem (by decide : (2 : Fin 6) ≠ 3) subset_rfl hz hv

theorem apply_Y2_of_factors {a n b c : V12 ≃ₗ[ZMod 2] V12} (ha : ∀ v ∈ Y2, a v = v)
    (hn : n ∈ node 2) (hb : ∀ v ∈ Y2, b v = v) (hc : c ∈ flip2) :
    ∀ v ∈ Y2, (a * n * b * c) v = (n * c) v := by
  intro v hv
  have hcv := mapsY2_flip2 hc hv
  simp only [LinearEquiv.mul_apply]
  rw [hb _ hcv, ha _ (mapsY2_node2 hn hcv)]

theorem sigOf_of_normalizes {Z : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {g n c : V12 ≃ₗ[ZMod 2] V12}
    (hg : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) (hn : n ∈ node 2) (hc : c ∈ flip2) (hc1 : c ≠ 1)
    (hgv : ∀ v ∈ Y2, g v = (n * c) v) : SigOf (subCommSpace Z ⊓ Y2) c := by
  refine ⟨hc, hc1, n, hn, fun v hv => ?_⟩
  obtain ⟨hvZ, hvY⟩ := Submodule.mem_inf.mp hv
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [← hgv v hvY]
    exact apply_mem_subCommSpace hg hvZ
  · rw [LinearEquiv.mul_apply]
    exact mapsY2_node2 hn (mapsY2_flip2 hc hvY)

theorem polar_eq_zero_of_le_sup {A A₁ A₂ B B₁ B₂ : Submodule (ZMod 2) V12}
    (hA : A ≤ A₁ ⊔ A₂) (hB : B ≤ B₁ ⊔ B₂)
    (h11 : ∀ a ∈ A₁, ∀ b ∈ B₁, QuadraticMap.polar Q12 a b = 0)
    (h12 : ∀ a ∈ A₁, ∀ b ∈ B₂, QuadraticMap.polar Q12 a b = 0)
    (h21 : ∀ a ∈ A₂, ∀ b ∈ B₁, QuadraticMap.polar Q12 a b = 0)
    (h22 : ∀ a ∈ A₂, ∀ b ∈ B₂, QuadraticMap.polar Q12 a b = 0) :
    ∀ a ∈ A, ∀ b ∈ B, QuadraticMap.polar Q12 a b = 0 := by
  intro a ha b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp (hA ha)
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp (hB hb)
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
    h11 _ ha₁ _ hb₁, h12 _ ha₁ _ hb₂, h21 _ ha₂ _ hb₁, h22 _ ha₂ _ hb₂, add_zero, add_zero]

theorem perpY2_le_Y2 (P : Submodule (ZMod 2) V12) : perpY2 P ≤ Y2 := inf_le_left

theorem polar_perpY2 {P : Submodule (ZMod 2) V12} :
    ∀ w ∈ perpY2 P, ∀ b ∈ P, QuadraticMap.polar Q12 w b = 0 := by
  intro w hw b hb
  have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp (Submodule.mem_inf.mp hw).2) b hb
  change QuadraticMap.polarBilin Q12 b w = 0 at h
  rw [QuadraticMap.polarBilin_apply_apply] at h
  rw [QuadraticMap.polar_comm]
  exact h

theorem polar_Y2_disjoint {P : Finset (Fin 6)} (h : Disjoint ({2, 3} : Finset (Fin 6)) P) :
    ∀ a ∈ Y2, ∀ b ∈ planeSpan P, QuadraticMap.polar Q12 a b = 0 :=
  polar_eq_zero_of_disjoint h

theorem polar_disjoint_Y2 {P : Finset (Fin 6)} (h : Disjoint P ({2, 3} : Finset (Fin 6))) :
    ∀ a ∈ planeSpan P, ∀ b ∈ Y2, QuadraticMap.polar Q12 a b = 0 :=
  polar_eq_zero_of_disjoint h

end CFSG.StandardType.FrameRoute.FS81.D6M

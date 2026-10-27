module

public import CFSG.GH74.QTGen4.Recog.G23.MLettersD
public import CFSG.GH74.QTGen4.Recog.G23.MSylowC
public import CFSG.Quasithin.EmptyFaithful.S14113bFStar
public import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.Quasithin.G23Type.Ctx

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23
open scoped MatrixGroups IsMulCommutative

variable {G : Type} [Group G]

theorem fitting_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.ComponentClassification.Fitting.subgroup A).map e.toMonoidHom =
      CFSG.ComponentClassification.Fitting.subgroup B :=
  CFSG.WholeGroup.fittingSubgroup_map_mulEquiv e

theorem generalizedFitting_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.ComponentClassification.GeneralizedFitting.subgroup A).map e.toMonoidHom =
      CFSG.ComponentClassification.GeneralizedFitting.subgroup B := by
  simp only [CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup]
  rw [Subgroup.map_sup, fitting_map_equiv e, CFSG.ComponentClassification.Layer.equiv_invariant e]

theorem quasithinGenFitting_map_mulEquiv (σ : G ≃* G) (Y : Subgroup G) :
    quasithinGenFitting (Y.map σ.toMonoidHom) = (quasithinGenFitting Y).map σ.toMonoidHom := by
  rw [CFSG.Quasithin.quasithinGenFitting_eq_map_subtype,
    CFSG.Quasithin.quasithinGenFitting_eq_map_subtype]
  set e := Y.equivMapOfInjective σ.toMonoidHom σ.injective
  rw [← generalizedFitting_map_equiv e, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem g23Two_map {M : Subgroup G} (hM : G23Two M) (σ : G ≃* G) :
    G23Two (M.map σ.toMonoidHom) := by
  have hF : quasithinGenFitting (M.map σ.toMonoidHom) =
      (quasithinGenFitting M).map σ.toMonoidHom :=
    quasithinGenFitting_map_mulEquiv σ M
  obtain ⟨hcomm, hexp⟩ := hM.elem
  obtain ⟨θ0, hθs, hθk⟩ := hM.quot
  let e : ↥M ≃* ↥(M.map σ.toMonoidHom) :=
    Subgroup.equivMapOfInjective M σ.toMonoidHom σ.injective
  let eF : ↥(quasithinGenFitting M) ≃* ↥((quasithinGenFitting M).map σ.toMonoidHom) :=
    Subgroup.equivMapOfInjective (quasithinGenFitting M) σ.toMonoidHom σ.injective
  have key : ∀ x : ↥(M.map σ.toMonoidHom), ((e.symm x : ↥M) : G) = σ.symm (x : G) := by
    intro x
    have h1 : σ ((e.symm x : ↥M) : G) = (x : G) := by
      have h0 := congrArg Subtype.val (e.apply_symm_apply x)
      exact h0
    rw [← h1, MulEquiv.symm_apply_apply]
  have hk : ∀ m : ↥M, θ0 m = 1 ↔ (m : G) ∈ quasithinGenFitting M := fun m => by
    rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf]
  refine ⟨?_, ?_, ?_⟩
  · rw [hF]
    unfold IsElemAbelian
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · show a * b = b * a
      have h1 : eF.symm a * eF.symm b = eF.symm b * eF.symm a := hcomm.is_comm.comm _ _
      have h2 := congrArg (fun z => eF z) h1
      simpa only [map_mul, MulEquiv.apply_symm_apply] using h2
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hexp y hy, map_one]
  · rw [hF]
    exact (Nat.card_congr eF.toEquiv).symm.trans hM.card
  · refine ⟨θ0.comp e.symm.toMonoidHom, ?_, ?_⟩
    · intro s
      obtain ⟨m, hm⟩ := hθs s
      refine ⟨e m, ?_⟩
      show θ0 (e.symm (e m)) = s
      rw [MulEquiv.symm_apply_apply]
      exact hm
    · ext x
      rw [Subgroup.mem_subgroupOf, hF, Subgroup.mem_map_equiv]
      show θ0 (e.symm x) = 1 ↔ _
      rw [hk, key]

theorem exists_matrix_action [Finite G] {M : Subgroup G} (hM : G23Two M) :
    ∃ (κ : G → (Fin 3 → ZMod 2)) (Φ : ↥M →* Matrix (Fin 3) (Fin 3) (ZMod 2)),
      (∀ v ∈ quasithinGenFitting M, ∀ w ∈ quasithinGenFitting M, κ (v * w) = κ v + κ w) ∧
      (∀ x ∈ quasithinGenFitting M, ∀ y ∈ quasithinGenFitting M, κ x = κ y → x = y) ∧
      (∀ c : Fin 3 → ZMod 2, ∃ v ∈ quasithinGenFitting M, κ v = c) ∧
      (∀ g : ↥M, ∀ v ∈ quasithinGenFitting M,
        κ ((g : G) * v * (g : G)⁻¹) = Matrix.mulVec (Φ g) (κ v)) ∧
      (∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.det ≠ 0 → ∃ g : ↥M, Φ g = B) := by
  have hVM : quasithinGenFitting M ≤ M := CFSG.Quasithin.quasithinGenFitting_le M
  have hcomm : IsMulCommutative ↥(quasithinGenFitting M) := hM.elem.1
  have hexp : ∀ x : ↥(quasithinGenFitting M), x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa using hM.elem.2 _ x.2)
  let hmod : Module (ZMod 2) (Additive ↥(quasithinGenFitting M)) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by
      show 2 • x = 0
      apply Additive.toMul.injective
      simp only [toMul_nsmul, toMul_zero]
      exact hexp x.toMul)
  have hcard : Nat.card (Additive ↥(quasithinGenFitting M)) = 8 :=
    (Nat.card_congr Additive.toMul).trans hM.card
  have hfin : Finite (Additive ↥(quasithinGenFitting M)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Module.Finite (ZMod 2) (Additive ↥(quasithinGenFitting M)) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) (Additive ↥(quasithinGenFitting M)) = 3 := by
    have hfc := Fintype.ofFinite (Additive ↥(quasithinGenFitting M))
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive ↥(quasithinGenFitting M))
    rw [← Nat.card_eq_fintype_card, hcard, ZMod.card] at h
    have h' : 2 ^ Module.finrank (ZMod 2) (Additive ↥(quasithinGenFitting M)) = 2 ^ 3 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h'
  let b : Module.Basis (Fin 3) (ZMod 2) (Additive ↥(quasithinGenFitting M)) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive ↥(quasithinGenFitting M)) hrank
  let T : M →* Module.End (ZMod 2) (Additive ↥(quasithinGenFitting M)) :=
    { toFun := fun g => AddMonoidHom.toZModLinearMap 2
        (AddMonoidHom.mk'
          (fun x : Additive ↥(quasithinGenFitting M) =>
            Additive.ofMul (⟨(g : G) * x.toMul * (g : G)⁻¹,
              G23Two.conj_mem_fitting hM g.2 x.toMul.2⟩ : ↥(quasithinGenFitting M)))
          (fun x y => by
            apply Additive.toMul.injective
            apply Subtype.ext
            simp [mul_assoc]))
      map_one' := by
        ext x
        simp [AddMonoidHom.toZModLinearMap]
      map_mul' := fun a c => by
        ext x
        simp [AddMonoidHom.toZModLinearMap, mul_assoc] }
  let Φ0 : M →* Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toMonoidHom.comp T
  let Φ : M →* (Matrix (Fin 3) (Fin 3) (ZMod 2))ˣ := Φ0.toHomUnits
  have hker : Φ.ker = (quasithinGenFitting M).subgroupOf M := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have h0 : Φ0 g = 1 := by
        have := congrArg Units.val hg
        exact this
      have hT : T g = 1 := by
        apply (LinearMap.toMatrixAlgEquiv b).injective
        rw [map_one]
        exact h0
      have hconj : ∀ x : Additive ↥(quasithinGenFitting M),
          (g : G) * x.toMul * (g : G)⁻¹ = x.toMul := by
        intro x
        have h2 : T g x = x := LinearMap.congr_fun hT x
        have h3 := congrArg (fun y : Additive ↥(quasithinGenFitting M) => ((Additive.toMul y : ↥(quasithinGenFitting M)) : G)) h2
        exact h3
      have hcen : (g : G) ∈ Subgroup.centralizer (quasithinGenFitting M : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have h4 : (g : G) * h * (g : G)⁻¹ = h := hconj (Additive.ofMul ⟨h, hh⟩)
        exact (mul_inv_eq_iff_eq_mul.mp h4).symm
      have hmemM : (g : G) ∈ M ⊓ Subgroup.centralizer (quasithinGenFitting M : Set G) :=
        ⟨g.2, hcen⟩
      rwa [G23Two.inf_centralizer_fitting hM] at hmemM
    · intro hg
      have hT : T g = 1 := by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        apply Subtype.ext
        show (g : G) * x.toMul * (g : G)⁻¹ = x.toMul
        rw [G23Two.fitting_comm hM hg x.toMul.2, mul_inv_cancel_right]
      apply Units.ext
      show (LinearMap.toMatrixAlgEquiv b) (T g) = 1
      rw [hT, map_one]
  have hkerCard : Nat.card Φ.ker = 8 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVM).toEquiv, hM.card]
  have hrange : Nat.card Φ.range = 168 := by
    have h := Subgroup.card_ker_mul_card_range Φ
    rw [hkerCard, G23Two.card_group hM] at h
    omega
  set R : Set (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    (fun u : (Matrix (Fin 3) (Fin 3) (ZMod 2))ˣ => (u : Matrix (Fin 3) (Fin 3) (ZMod 2))) ''
      (Φ.range : Set (Matrix (Fin 3) (Fin 3) (ZMod 2))ˣ) with hR
  have hRcard : R.ncard = 168 := by
    rw [hR, Set.ncard_image_of_injective _ (fun _ _ h => Units.ext h), ← Nat.card_coe_set_eq]
    exact hrange
  have hsub : R ⊆ {B : Matrix (Fin 3) (Fin 3) (ZMod 2) | B.det ≠ 0} := by
    rintro _ ⟨u, _, rfl⟩
    show (u : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0
    exact ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero
  have hRS : R = {B : Matrix (Fin 3) (Fin 3) (ZMod 2) | B.det ≠ 0} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hRcard, card_invertible_fin3]) (Set.toFinite _)
  classical
  let κ : G → (Fin 3 → ZMod 2) := fun g =>
    if h : g ∈ quasithinGenFitting M then ⇑(b.repr (Additive.ofMul (⟨g, h⟩ : ↥(quasithinGenFitting M))))
    else 0
  have hκ : ∀ (v : G) (hv : v ∈ quasithinGenFitting M),
      κ v = ⇑(b.repr (Additive.ofMul (⟨v, hv⟩ : ↥(quasithinGenFitting M)))) := by
    intro v hv
    simp only [κ, hv, dite_true]
  refine ⟨κ, Φ0, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv w hw
    rw [hκ v hv, hκ w hw, hκ (v * w) ((quasithinGenFitting M).mul_mem hv hw)]
    have : Additive.ofMul (⟨v * w, (quasithinGenFitting M).mul_mem hv hw⟩ : ↥(quasithinGenFitting M)) =
        Additive.ofMul (⟨v, hv⟩ : ↥(quasithinGenFitting M)) +
          Additive.ofMul (⟨w, hw⟩ : ↥(quasithinGenFitting M)) := rfl
    rw [this, map_add]
    rfl
  · intro x hx y hy hxy
    rw [hκ x hx, hκ y hy] at hxy
    have h1 := b.repr.injective (DFunLike.coe_injective hxy)
    have h2 := congrArg (fun y : Additive ↥(quasithinGenFitting M) =>
      ((Additive.toMul y : ↥(quasithinGenFitting M)) : G)) h1
    exact h2
  · intro c
    refine ⟨((Additive.toMul (b.repr.symm (Finsupp.equivFunOnFinite.symm c)) :
      ↥(quasithinGenFitting M)) : G), (Additive.toMul (b.repr.symm
        (Finsupp.equivFunOnFinite.symm c)) : ↥(quasithinGenFitting M)).2, ?_⟩
    rw [hκ _ (Additive.toMul (b.repr.symm (Finsupp.equivFunOnFinite.symm c)) :
      ↥(quasithinGenFitting M)).2]
    simp
  · intro g v hv
    have hgv : (g : G) * v * (g : G)⁻¹ ∈ quasithinGenFitting M :=
      G23Two.conj_mem_fitting hM g.2 hv
    rw [hκ v hv, hκ _ hgv]
    have hrep : ∀ y : Additive ↥(quasithinGenFitting M),
        (⇑(b.repr (T g y)) : Fin 3 → ZMod 2) = Matrix.mulVec (Φ0 g) ⇑(b.repr y) := by
      intro y
      show _ = Matrix.mulVec (LinearMap.toMatrix b b (T g)) ⇑(b.repr y)
      exact (LinearMap.toMatrix_mulVec_repr b b (T g) y).symm
    exact hrep (Additive.ofMul ⟨v, hv⟩)
  · intro B hB
    have hBR : B ∈ R := by
      rw [hRS]
      exact hB
    obtain ⟨u, hu, hue⟩ := hBR
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hu : u ∈ Φ.range)
    refine ⟨g, ?_⟩
    rw [← hue, ← hg]
    rfl

private def e0 : Fin 3 → ZMod 2 := ![1, 0, 0]
private def e1 : Fin 3 → ZMod 2 := ![0, 1, 0]
private def e2 : Fin 3 → ZMod 2 := ![0, 0, 1]

private def stdBy : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

private def stdBh : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

private theorem ff_cols : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.det ≠ 0 →
    (Matrix.mulVec B e1 ≠ 0 ∧ Matrix.mulVec B e1 ≠ Matrix.mulVec B e0 ∧
      Matrix.mulVec B e2 ≠ 0 ∧ Matrix.mulVec B e2 ≠ Matrix.mulVec B e0 ∧
      Matrix.mulVec B e1 + Matrix.mulVec B e2 ≠ 0 ∧
      Matrix.mulVec B e1 + Matrix.mulVec B e2 ≠ Matrix.mulVec B e0) := by
  unfold e0 e1 e2
  decide +kernel

private theorem ff_gen : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.det ≠ 0 →
    ∀ w : Fin 3 → ZMod 2,
      w = 0 ∨ w = Matrix.mulVec B e0 ∨ w = Matrix.mulVec B e1 ∨
      w = Matrix.mulVec B e0 + Matrix.mulVec B e1 ∨ w = Matrix.mulVec B e2 ∨
      w = Matrix.mulVec B e0 + Matrix.mulVec B e2 ∨
      w = Matrix.mulVec B e1 + Matrix.mulVec B e2 ∨
      w = Matrix.mulVec B e0 + Matrix.mulVec B e1 + Matrix.mulVec B e2 := by
  unfold e0 e1 e2
  decide +kernel

private theorem ff_std : stdBy ^ 3 = 1 ∧ stdBy.det ≠ 0 ∧ stdBh.det ≠ 0 ∧
    Matrix.mulVec stdBy e0 = e0 ∧ Matrix.mulVec stdBy e1 = e2 ∧
    Matrix.mulVec stdBy e2 = e1 + e2 ∧ Matrix.mulVec stdBh e0 = e0 ∧
    Matrix.mulVec stdBh e1 = e2 ∧ Matrix.mulVec stdBh e2 = e1 := by
  unfold stdBy stdBh e0 e1 e2
  decide +kernel

private theorem zmod2_ne_zero (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  revert x; decide

theorem exists_basis_act [Finite G] {M : Subgroup G} (hM : G23Two M) {z : G}
    (hz : z ∈ quasithinGenFitting M) (hz1 : z ≠ 1) :
    ∃ a b y h : G, a ∈ quasithinGenFitting M ∧ b ∈ quasithinGenFitting M ∧
      a ≠ 1 ∧ a ≠ z ∧ b ≠ 1 ∧ b ≠ z ∧ a * b ≠ 1 ∧ a * b ≠ z ∧
      (∀ v ∈ quasithinGenFitting M, v ∈ Subgroup.closure ({z, a, b} : Set G)) ∧
      y ∈ M ∧ y ^ 3 = 1 ∧ y * z * y⁻¹ = z ∧ y * a * y⁻¹ = b ∧ y * b * y⁻¹ = a * b ∧
      h ∈ M ∧ h * z * h⁻¹ = z ∧ h * a * h⁻¹ = b ∧ h * b * h⁻¹ = a := by
  obtain ⟨κ, Φ, hadd, hinj, hsurj, hact, hΦ⟩ := exists_matrix_action hM
  have hV1 : (1 : G) ∈ quasithinGenFitting M := (quasithinGenFitting M).one_mem
  have hκ1 : κ 1 = 0 := by
    have h := hadd 1 hV1 1 hV1
    rw [mul_one] at h
    simpa using h
  have hκz : κ z ≠ 0 := by
    intro h
    exact hz1 (hinj z hz 1 hV1 (h.trans hκ1.symm))
  have he0 : e0 ≠ 0 := by unfold e0; decide
  obtain ⟨B, hBdet, hB⟩ := GL3_two_transitive e0 (κ z) he0 hκz
  set B₀ : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of B with hB₀
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := ff_cols B₀ hBdet
  obtain ⟨a, haV, haκ⟩ := hsurj (Matrix.mulVec B₀ e1)
  obtain ⟨b, hbV, hbκ⟩ := hsurj (Matrix.mulVec B₀ e2)
  have hzκ : κ z = Matrix.mulVec B₀ e0 := hB.symm
  have habV : a * b ∈ quasithinGenFitting M := (quasithinGenFitting M).mul_mem haV hbV
  have habκ : κ (a * b) = Matrix.mulVec B₀ e1 + Matrix.mulVec B₀ e2 := by
    rw [hadd a haV b hbV, haκ, hbκ]
  have hna1 : a ≠ 1 := by
    intro h; apply hc1; rw [← haκ, h, hκ1]
  have hnaz : a ≠ z := by
    intro h; apply hc2; rw [← haκ, h, hzκ]
  have hnb1 : b ≠ 1 := by
    intro h; apply hc3; rw [← hbκ, h, hκ1]
  have hnbz : b ≠ z := by
    intro h; apply hc4; rw [← hbκ, h, hzκ]
  have hnab1 : a * b ≠ 1 := by
    intro h; apply hc5; rw [← habκ, h, hκ1]
  have hnabz : a * b ≠ z := by
    intro h; apply hc6; rw [← habκ, h, hzκ]
  have hgen : ∀ v ∈ quasithinGenFitting M, v ∈ Subgroup.closure ({z, a, b} : Set G) := by
    intro v hv
    have hzc : z ∈ Subgroup.closure ({z, a, b} : Set G) := Subgroup.subset_closure (by simp)
    have hac : a ∈ Subgroup.closure ({z, a, b} : Set G) := Subgroup.subset_closure (by simp)
    have hbc : b ∈ Subgroup.closure ({z, a, b} : Set G) := Subgroup.subset_closure (by simp)
    have key : ∀ p : G, p ∈ Subgroup.closure ({z, a, b} : Set G) → p ∈ quasithinGenFitting M →
        κ p = κ v → v ∈ Subgroup.closure ({z, a, b} : Set G) := by
      intro p hp hpV hpκ
      rw [← hinj p hpV v hv hpκ]
      exact hp
    have hmul : ∀ {x y : G}, x ∈ Subgroup.closure ({z, a, b} : Set G) →
        y ∈ Subgroup.closure ({z, a, b} : Set G) → x * y ∈ Subgroup.closure ({z, a, b} : Set G) :=
      fun hx hy => Subgroup.mul_mem _ hx hy
    rcases ff_gen B₀ hBdet (κ v) with h | h | h | h | h | h | h | h
    · exact key 1 (Subgroup.one_mem _) hV1 (by rw [hκ1, h])
    · exact key z hzc hz (by rw [hzκ, h])
    · exact key a hac haV (by rw [haκ, h])
    · exact key (z * a) (hmul hzc hac) ((quasithinGenFitting M).mul_mem hz haV)
        (by rw [hadd z hz a haV, hzκ, haκ, h])
    · exact key b hbc hbV (by rw [hbκ, h])
    · exact key (z * b) (hmul hzc hbc) ((quasithinGenFitting M).mul_mem hz hbV)
        (by rw [hadd z hz b hbV, hzκ, hbκ, h])
    · exact key (a * b) (hmul hac hbc) habV (by rw [habκ, h])
    · exact key (z * (a * b)) (hmul hzc (hmul hac hbc)) ((quasithinGenFitting M).mul_mem hz habV)
        (by rw [hadd z hz (a * b) habV, hzκ, habκ, ← add_assoc, h])
  have hu : IsUnit B₀.det := isUnit_iff_ne_zero.mpr hBdet
  have hBinv : B₀⁻¹ * B₀ = 1 := Matrix.nonsing_inv_mul B₀ hu
  have hconj : ∀ (C : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2),
      Matrix.mulVec (B₀ * C * B₀⁻¹) (Matrix.mulVec B₀ x) =
        Matrix.mulVec B₀ (Matrix.mulVec C x) := by
    intro C x
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, mul_assoc, hBinv, mul_one]
  have hdetconj : ∀ C : Matrix (Fin 3) (Fin 3) (ZMod 2), C.det ≠ 0 →
      (B₀ * C * B₀⁻¹).det ≠ 0 := by
    intro C hC
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, zmod2_ne_zero _ hBdet,
      zmod2_ne_zero _ hC, Ring.inverse_one]
    decide
  obtain ⟨hy3, hdy, hdh, hy0, hy1, hy2, hh0, hh1, hh2⟩ := ff_std
  obtain ⟨m, hm⟩ := hΦ (B₀ * stdBy * B₀⁻¹) (hdetconj _ hdy)
  obtain ⟨g, hg⟩ := hΦ (B₀ * stdBh * B₀⁻¹) (hdetconj _ hdh)
  have hVz : ∀ x ∈ quasithinGenFitting M, ∀ c : G, c ∈ quasithinGenFitting M → κ x = κ c → x = c :=
    fun x hx c hc h => hinj x hx c hc h
  have hmV : ∀ v ∈ quasithinGenFitting M, (m : G) * v * (m : G)⁻¹ ∈ quasithinGenFitting M :=
    fun v hv => G23Two.conj_mem_fitting hM m.2 hv
  have hmz : (m : G) * z * (m : G)⁻¹ = z := by
    apply hinj _ (hmV z hz) z hz
    rw [hact m z hz, hm, hzκ, hconj, hy0]
  have hma : (m : G) * a * (m : G)⁻¹ = b := by
    apply hinj _ (hmV a haV) b hbV
    rw [hact m a haV, hm, haκ, hconj, hy1, hbκ]
  have hmb : (m : G) * b * (m : G)⁻¹ = a * b := by
    apply hinj _ (hmV b hbV) (a * b) habV
    rw [hact m b hbV, hm, hbκ, hconj, hy2, Matrix.mulVec_add, habκ]
  have hgV : ∀ v ∈ quasithinGenFitting M, (g : G) * v * (g : G)⁻¹ ∈ quasithinGenFitting M :=
    fun v hv => G23Two.conj_mem_fitting hM g.2 hv
  have hgz : (g : G) * z * (g : G)⁻¹ = z := by
    apply hinj _ (hgV z hz) z hz
    rw [hact g z hz, hg, hzκ, hconj, hh0]
  have hga : (g : G) * a * (g : G)⁻¹ = b := by
    apply hinj _ (hgV a haV) b hbV
    rw [hact g a haV, hg, haκ, hconj, hh1, hbκ]
  have hgb : (g : G) * b * (g : G)⁻¹ = a := by
    apply hinj _ (hgV b hbV) a haV
    rw [hact g b hbV, hg, hbκ, hconj, hh2, haκ]
  have hcomm : b * a = a * b := G23Two.fitting_comm hM hbV haV
  have hbb : b * b = 1 := G23Two.sq_fitting hM hbV
  have hmab : (m : G) * (a * b) * (m : G)⁻¹ = a := by
    have e : (m : G) * (a * b) * (m : G)⁻¹ =
        ((m : G) * a * (m : G)⁻¹) * ((m : G) * b * (m : G)⁻¹) := by group
    rw [e, hma, hmb]
    calc b * (a * b) = (b * a) * b := by rw [mul_assoc]
      _ = (a * b) * b := by rw [hcomm]
      _ = a * (b * b) := by rw [mul_assoc]
      _ = a := by rw [hbb, mul_one]
  have h3z : (m : G) ^ 3 * z = z * (m : G) ^ 3 := by
    have e : (m : G) ^ 3 * z * ((m : G) ^ 3)⁻¹ =
        (m : G) * ((m : G) * ((m : G) * z * (m : G)⁻¹) * (m : G)⁻¹) * (m : G)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc, inv_one, mul_one]
    rw [hmz, hmz, hmz] at e
    exact (mul_inv_eq_iff_eq_mul.mp e)
  have h3a : (m : G) ^ 3 * a = a * (m : G) ^ 3 := by
    have e : (m : G) ^ 3 * a * ((m : G) ^ 3)⁻¹ =
        (m : G) * ((m : G) * ((m : G) * a * (m : G)⁻¹) * (m : G)⁻¹) * (m : G)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc, inv_one, mul_one]
    rw [hma, hmb, hmab] at e
    exact (mul_inv_eq_iff_eq_mul.mp e)
  have h3b : (m : G) ^ 3 * b = b * (m : G) ^ 3 := by
    have e : (m : G) ^ 3 * b * ((m : G) ^ 3)⁻¹ =
        (m : G) * ((m : G) * ((m : G) * b * (m : G)⁻¹) * (m : G)⁻¹) * (m : G)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc, inv_one, mul_one]
    rw [hmb, hmab, hma] at e
    exact (mul_inv_eq_iff_eq_mul.mp e)
  have hcen : (m : G) ^ 3 ∈ Subgroup.centralizer (quasithinGenFitting M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hle : Subgroup.closure ({z, a, b} : Set G) ≤ Subgroup.centralizer {(m : G) ^ 3} := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hx with rfl | rfl | rfl
      · exact h3z.symm
      · exact h3a.symm
      · exact h3b.symm
    have := hle (hgen v hv)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hm3V : (m : G) ^ 3 ∈ quasithinGenFitting M := by
    have : (m : G) ^ 3 ∈ M ⊓ Subgroup.centralizer (quasithinGenFitting M : Set G) :=
      ⟨pow_mem m.2 3, hcen⟩
    rwa [G23Two.inf_centralizer_fitting hM] at this
  have hm33 : (m : G) ^ 3 * (m : G) ^ 3 = 1 := G23Two.sq_fitting hM hm3V
  have e4z : (m : G) ^ 4 * z * ((m : G) ^ 4)⁻¹ = z := by
    have e : (m : G) ^ 4 * z * ((m : G) ^ 4)⁻¹ =
        (m : G) * ((m : G) * ((m : G) * ((m : G) * z * (m : G)⁻¹) * (m : G)⁻¹) * (m : G)⁻¹) *
          (m : G)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc, inv_one, mul_one]
    rw [e, hmz, hmz, hmz, hmz]
  have e4a : (m : G) ^ 4 * a * ((m : G) ^ 4)⁻¹ = b := by
    have e : (m : G) ^ 4 * a * ((m : G) ^ 4)⁻¹ =
        (m : G) * ((m : G) * ((m : G) * ((m : G) * a * (m : G)⁻¹) * (m : G)⁻¹) * (m : G)⁻¹) *
          (m : G)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc, inv_one, mul_one]
    rw [e, hma, hmb, hmab, hma]
  have e4b : (m : G) ^ 4 * b * ((m : G) ^ 4)⁻¹ = a * b := by
    have e : (m : G) ^ 4 * b * ((m : G) ^ 4)⁻¹ =
        (m : G) * ((m : G) * ((m : G) * ((m : G) * b * (m : G)⁻¹) * (m : G)⁻¹) * (m : G)⁻¹) *
          (m : G)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc, inv_one, mul_one]
    rw [e, hmb, hmab, hma, hmb]
  have hy3 : ((m : G) ^ 4) ^ 3 = 1 := by
    have e : ((m : G) ^ 4) ^ 3 = ((m : G) ^ 3 * (m : G) ^ 3) * ((m : G) ^ 3 * (m : G) ^ 3) := by
      simp only [← pow_mul, ← pow_add]
    rw [e, hm33, mul_one]
  exact ⟨a, b, (m : G) ^ 4, (g : G), haV, hbV, hna1, hnaz, hnb1, hnbz, hnab1, hnabz, hgen,
    pow_mem m.2 4, hy3, e4z, e4a, e4b, g.2, hgz, hga, hgb⟩

end CFSG.Quasithin.G23Type.Ctx

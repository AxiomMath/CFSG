module

public import CFSG.RankThree.GF2n.Stroth80.Sec118I4Coords
public import CFSG.LieType.D4Small.SpinSeven
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action
public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Form

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic CFSG.LieType.D4Small
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open QuadraticMap
open scoped Matrix commutatorElement

noncomputable abbrev spinSevenGL (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (GL (Fin (2 * 4)) K) :=
  (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype

section MulVec

variable {K : Type} [Field K]

theorem eq_of_mulVec_eq_fin {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using h v)

theorem gl_eq_of_mulVec_eq_fin {n : ℕ} {A B : GL (Fin n) K}
    (h : ∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ v = (B : Matrix (Fin n) (Fin n) K) *ᵥ v) :
    A = B :=
  Units.ext (eq_of_mulVec_eq_fin h)

end MulVec

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

omit [CharP K 2] in
theorem cmCommGL_isometry (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφQ : ∀ (g : ↥(H0 M Z)) e', M₀.Qf (φ g e') = M₀.Qf e')
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K))
    (heQ : ∀ v, coordinateQuadPlus 4 K (e v) = cmCommQf B φ v) (ℓ : ↥(H0 M Z))
    (w : Fin (2 * 4) → K) :
    coordinateQuadPlus 4 K
        (((cmCommGL hc hD φ hφπ e ℓ : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w) =
      coordinateQuadPlus 4 K w := by
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [cmCommGL_mulVec, heQ, heQ]
  exact hφQ ℓ (v : M₀.E)

theorem Ctx.cmCommGL_mem_spinSevenGL (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K))
    (hXS1 : ∀ s : ↥(XbarH M Q Z B), cmCommGL hc hD φ hφπ e (s : ↥(H0 M Z)) ∈ spinSevenGL K)
    (hXS2 : ∀ M' ∈ spinSeven K, ∃ s : ↥(XbarH M Q Z B),
      cmCommGL hc hD φ hφπ e (s : ↥(H0 M Z)) = (M' : GL (Fin (2 * 4)) K))
    (hiso : ∀ (ℓ : ↥(H0 M Z)) (w : Fin (2 * 4) → K), coordinateQuadPlus 4 K
        (((cmCommGL hc hD φ hφπ e ℓ : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w) = coordinateQuadPlus 4 K w)
    (hN : ∀ g : GL (Fin (2 * 4)) K,
      (∀ w, coordinateQuadPlus 4 K ((g : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w) =
        coordinateQuadPlus 4 K w) →
      (∀ M' ∈ spinSeven K, g * (M' : GL (Fin (2 * 4)) K) * g⁻¹ ∈ spinSevenGL K) → g ∈ spinSevenGL K)
    (ℓ : ↥(H0 M Z)) : cmCommGL hc hD φ hφπ e ℓ ∈ spinSevenGL K := by
  refine hN _ (hiso ℓ) fun M' hM' => ?_
  obtain ⟨s, hs⟩ := hXS2 M' hM'
  rw [← hs]
  have : cmCommGL hc hD φ hφπ e ℓ * cmCommGL hc hD φ hφπ e (s : ↥(H0 M Z)) *
      (cmCommGL hc hD φ hφπ e ℓ)⁻¹ =
      cmCommGL hc hD φ hφπ e (ℓ * (s : ↥(H0 M Z)) * ℓ⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [this]
  exact hXS1 ⟨ℓ * (s : ↥(H0 M Z)) * ℓ⁻¹, hc.conj_mem_XbarH s.2⟩

theorem Ctx.cmCommGL_XbarH_mem_spinSevenGL (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K))
    (ψ : StatedSp 3 K →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)))
    (Θ : ↥(XbarH M Q Z B) →* StatedSp 3 K) (hψΘ : ∀ s, ψ (Θ s) = cmCommAct hc φ s)
    (hef : ∀ g, ∃ M' ∈ spinSeven K, ∀ v,
      ((M' : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v = e (ψ g v))
    (s : ↥(XbarH M Q Z B)) : cmCommGL hc hD φ hφπ e (s : ↥(H0 M Z)) ∈ spinSevenGL K := by
  obtain ⟨M', hM', hM'v⟩ := hef (Θ s)
  refine Subgroup.mem_map.mpr ⟨M', hM', ?_⟩
  refine gl_eq_of_mulVec_eq_fin fun w => ?_
  obtain ⟨v, rfl⟩ := e.surjective w
  show ((M' : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v = _
  rw [hM'v, cmCommGL_mulVec, hψΘ s]
  rfl

theorem Ctx.exists_XbarH_cmCommGL_eq (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K))
    (ψ : StatedSp 3 K →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)))
    (Θ : ↥(XbarH M Q Z B) →* StatedSp 3 K) (hΘ : Function.Surjective Θ)
    (hψΘ : ∀ s, ψ (Θ s) = cmCommAct hc φ s)
    (heb : ∀ M' ∈ spinSeven K, ∃ g, ∀ v,
      ((M' : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v = e (ψ g v))
    (M' : Om8 K) (hM' : M' ∈ spinSeven K) :
    ∃ s : ↥(XbarH M Q Z B),
      cmCommGL hc hD φ hφπ e (s : ↥(H0 M Z)) = (M' : GL (Fin (2 * 4)) K) := by
  obtain ⟨g, hg⟩ := heb M' hM'
  obtain ⟨s, rfl⟩ := hΘ g
  refine ⟨s, gl_eq_of_mulVec_eq_fin fun w => ?_⟩
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [cmCommGL_mulVec, hg, hψΘ s]
  rfl

omit [CharP K 2] in
theorem Ctx.mem_Q_of_cmCommGL_eq_one (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K)) {t : ↥(H0 M Z)}
    (htC : ∀ z ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ), φ t z = z)
    (ht : cmCommGL hc hD φ hφπ e t = 1) : (t : G) ∈ Q := by
  refine (hφk t).mp (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    exists_mem_add_eq_of_isCompl (hc.isCompl_cmComm_orthogonal hD φ hφπ) v
  have h1 : φ t x = x := by
    have h2 := cmCommGL_mulVec hc hD φ hφπ e t ⟨x, hx⟩
    rw [ht, Units.val_one, Matrix.one_mulVec] at h2
    have h3 := e.injective h2
    exact congrArg Subtype.val h3.symm
  change φ t (x + y) = x + y
  rw [map_add, h1, htC y hy]

omit [CharP K 2] in
theorem Ctx.exists_XbarH_oddLift (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) (hQ2 : IsPGroup 2 Q)
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K))
    (M' : Om8 K)
    (hXS : ∃ s : ↥(XbarH M Q Z B),
      cmCommGL hc hD φ hφπ e (s : ↥(H0 M Z)) = (M' : GL (Fin (2 * 4)) K))
    (hodd : Odd (orderOf M')) :
    ∃ s' : ↥(XbarH M Q Z B), Odd (orderOf (((s' : ↥(H0 M Z)) : H0 M Z) : G)) ∧
      cmCommGL hc hD φ hφπ e (s' : ↥(H0 M Z)) = (M' : GL (Fin (2 * 4)) K) := by
  obtain ⟨s, hs⟩ := hXS
  set m := orderOf (M' : GL (Fin (2 * 4)) K) with hmdef
  have hm : Odd m := by
    rw [hmdef, Subgroup.orderOf_coe]
    exact hodd
  have hMm : (M' : GL (Fin (2 * 4)) K) ^ m = 1 := pow_orderOf_eq_one _
  have hsm : cmCommGL hc hD φ hφπ e ((s ^ m : ↥(XbarH M Q Z B)) : ↥(H0 M Z)) = 1 := by
    rw [Subgroup.coe_pow, map_pow, hs, hMm]
  have hsmQ : ((((s ^ m : ↥(XbarH M Q Z B)) : ↥(H0 M Z))) : G) ∈ Q :=
    hc.mem_Q_of_cmCommGL_eq_one hD φ hφπ hφk e
      (fun z hz => hc.action_fixes_orthogonal_of_mem_XbarH hD φ hφπ (s ^ m) hz) hsm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨_, hsmQ⟩
  have hk' : orderOf ((s : ↥(H0 M Z)) ^ m) = 2 ^ k := by
    have h1 : orderOf ((((s ^ m : ↥(XbarH M Q Z B)) : ↥(H0 M Z))) : G) = 2 ^ k := by
      rw [← hk]
      exact Subgroup.orderOf_coe (⟨_, hsmQ⟩ : ↥Q)
    rwa [Subgroup.orderOf_coe, Subgroup.coe_pow] at h1
  obtain ⟨r, hr1, hr2⟩ := exists_pow_odd_of_pow_orderOf (s : ↥(H0 M Z)) hm hk'
  refine ⟨s ^ r, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.coe_pow]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hr2)
  · rw [Subgroup.coe_pow, map_pow, hs]
    have h3 : (M' : GL (Fin (2 * 4)) K) ^ r = (M' : GL (Fin (2 * 4)) K) := by
      rw [← pow_mod_orderOf, ← hmdef, hr1, hmdef, pow_mod_orderOf, pow_one]
    exact h3

omit [Finite G] [Finite K] [CharP K 2] in
theorem polar_coordinateQuadPlus_e (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K))
    (heQ : ∀ v, coordinateQuadPlus 4 K (e v) = cmCommQf B φ v)
    (u v : ↥(cmComm M Q Z B K γ M₀ φ)) :
    polar (coordinateQuadPlus 4 K) (e u) (e v) = M₀.B (u : M₀.E) (v : M₀.E) := by
  rw [polar, ← map_add, heQ, heQ, heQ]
  have := M₀.Qf_add (u : M₀.E) (v : M₀.E)
  show M₀.Qf ((u + v : ↥(cmComm M Q Z B K γ M₀ φ)) : M₀.E) - M₀.Qf (u : M₀.E) -
    M₀.Qf (v : M₀.E) = _
  rw [Submodule.coe_add, this]
  ring

omit [(Q.subgroupOf M).Normal] in
private theorem Ctx.Q_le_H0_aux (hc : Ctx M Q Z B) : Q ≤ H0 M Z := fun _q hq =>
  ⟨hc.hyp.Q_normal.1 hq, Subgroup.mem_centralizer_iff.mpr fun _z hz =>
    (hc.hyp.toHyp79.V_central hz hq)⟩

omit [CharP K 2] in
theorem cmCommGL_eq_one_of_phi_eq_one (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K)) {t : ↥(H0 M Z)} (ht : φ t = 1) :
    cmCommGL hc hD φ hφπ e t = 1 := by
  refine gl_eq_of_mulVec_eq_fin fun w => ?_
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [cmCommGL_mulVec, Units.val_one, Matrix.one_mulVec]
  congr 1
  exact Subtype.ext (by rw [coe_cmCommActH, ht]; rfl)

omit [CharP K 2] in
theorem Ctx.card_cmCommGL_range_mul (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K)) :
    Nat.card ((cmCommGL hc hD φ hφπ e).comp ((LB M Q B).subgroupOf (H0 M Z)).subtype).range *
      Nat.card Q = Nat.card (LB M Q B) := by
  set LBH := (LB M Q B).subgroupOf (H0 M Z) with hLBH
  set f := (cmCommGL hc hD φ hφπ e).comp LBH.subtype with hf
  have h1 := Subgroup.card_ker_mul_card_range f
  have h3 : Nat.card LBH = Nat.card (LB M Q B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.LB_le_H0).toEquiv
  have h2 : Nat.card f.ker = Nat.card Q := by
    refine Nat.card_congr
      { toFun := fun ℓ => ⟨((ℓ.1 : ↥LBH) : ↥(H0 M Z)).1, ?_⟩
        invFun := fun q => ⟨⟨⟨q, hc.Q_le_H0_aux q.2⟩,
          Subgroup.mem_subgroupOf.mpr (le_sup_left (a := Q) q.2)⟩, ?_⟩
        left_inv := fun ℓ => rfl
        right_inv := fun q => rfl }
    · have hℓ : cmCommGL hc hD φ hφπ e ((ℓ.1 : ↥LBH) : ↥(H0 M Z)) = 1 := ℓ.2
      exact hc.mem_Q_of_cmCommGL_eq_one hD φ hφπ hφk e
        (fun z hz => hc.action_fixes_orthogonal hD φ hφπ ha2
          (Subgroup.mem_subgroupOf.mp (ℓ.1 : ↥LBH).2) ((ℓ.1 : ↥LBH) : ↥(H0 M Z)).2 hz) hℓ
    · exact cmCommGL_eq_one_of_phi_eq_one hc hD φ hφπ e ((hφk ⟨q, hc.Q_le_H0_aux q.2⟩).mpr q.2)
  rw [← h3, ← h1, h2, mul_comm]

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec118CommBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Tensor
public import CFSG.RankThree.GF2n.Stroth80.Sec11A2Line

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix commutatorElement

@[expose] noncomputable def glEquivLin (n : ℕ) (K : Type) [Field K] :
    ((Fin n → K) ≃ₗ[K] (Fin n → K)) ≃* GL (Fin n) K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

theorem glEquivLin_mulVec (n : ℕ) (K : Type) [Field K] (f : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (v : Fin n → K) :
    ((glEquivLin n K f : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = f v := by
  have h1 := Matrix.GeneralLinearGroup.coe_toLin (glEquivLin n K f)
  have h2 : Matrix.GeneralLinearGroup.toLin (glEquivLin n K f) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).symm f := by
    rw [glEquivLin]
    exact MulEquiv.apply_symm_apply _ _
  rw [h2] at h1
  have h3 := LinearMap.congr_fun h1 v
  rw [Matrix.mulVecLin_apply] at h3
  rw [← h3]
  rfl

section Split

variable {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E] {S C : Submodule K E}
  {N₁ N₂ : Type} [AddCommGroup N₁] [Module K N₁] [AddCommGroup N₂] [Module K N₂]

@[expose] noncomputable def complProdEquiv (hSC : IsCompl S C) (e : S ≃ₗ[K] N₁) (c : C ≃ₗ[K] N₂) :
    E ≃ₗ[K] N₁ × N₂ :=
  (Submodule.prodEquivOfIsCompl S C hSC).symm.trans (e.prodCongr c)

theorem complProdEquiv_add (hSC : IsCompl S C) (e : S ≃ₗ[K] N₁) (c : C ≃ₗ[K] N₂) {x y : E}
    (hx : x ∈ S) (hy : y ∈ C) :
    complProdEquiv hSC e c (x + y) = (e ⟨x, hx⟩, c ⟨y, hy⟩) := by
  have h1 : (Submodule.prodEquivOfIsCompl S C hSC) (⟨x, hx⟩, ⟨y, hy⟩) = x + y := rfl
  rw [complProdEquiv, LinearEquiv.trans_apply, ← h1, LinearEquiv.symm_apply_apply]
  rfl

theorem exists_mem_add_eq_of_isCompl (hSC : IsCompl S C) (v : E) :
    ∃ x ∈ S, ∃ y ∈ C, v = x + y := by
  have : v ∈ S ⊔ C := by rw [hSC.sup_eq_top]; trivial
  obtain ⟨x, hx, y, hy, h⟩ := Submodule.mem_sup.mp this
  exact ⟨x, hx, y, hy, h.symm⟩

end Split
theorem exists_pow_odd_of_pow_orderOf {H : Type*} [Group H] (s : H) {m : ℕ} (hm : Odd m) {k : ℕ}
    (hk : orderOf (s ^ m) = 2 ^ k) : ∃ r : ℕ, r ≡ 1 [MOD m] ∧ (s ^ r) ^ m = 1 := by
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Odd.coprime_two_right hm)
  obtain ⟨r, hr1, hr2⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨r, hr1, ?_⟩
  have hdvd : 2 ^ k ∣ r := (Nat.modEq_zero_iff_dvd).mp hr2
  rw [← pow_mul, mul_comm, pow_mul]
  exact orderOf_dvd_iff_pow_eq_one.mp (hk ▸ hdvd)

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.conj_mem_XbarH (hc : Ctx M Q Z B) {l s : ↥(H0 M Z)} (hs : s ∈ XbarH M Q Z B) :
    l * s * l⁻¹ ∈ XbarH M Q Z B := by
  unfold XbarH at hs ⊢
  rw [Subgroup.mem_comap] at hs ⊢
  simp only [map_mul, map_inv]
  exact hc.Xbar_normal.conj_mem _ hs _

theorem Ctx.cmComm_map_eq_self_of_mem_H0 (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) (g : ↥(H0 M Z)) :
    Submodule.map ((φ g : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
      (cmComm M Q Z B K γ M₀ φ) = cmComm M Q Z B K γ M₀ φ := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hc.mem_cmComm_of_act hD φ hφπ g.2 hy
  · intro y hy
    refine ⟨φ (g⁻¹) y, hc.mem_cmComm_of_act hD φ hφπ (g⁻¹).2 hy, ?_⟩
    show φ g (φ (g⁻¹) y) = y
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

@[expose] noncomputable def cmCommActH (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) :
    ↥(H0 M Z) →*
      (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)) where
  toFun g := LinearEquiv.ofSubmodules (φ g) _ _ (hc.cmComm_map_eq_self_of_mem_H0 hD φ hφπ g)
  map_one' := by
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    simp [LinearEquiv.ofSubmodules_apply]
  map_mul' s t := by
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    simp [LinearEquiv.ofSubmodules_apply]

theorem coe_cmCommActH (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) (g : ↥(H0 M Z))
    (v : ↥(cmComm M Q Z B K γ M₀ φ)) :
    ((cmCommActH hc hD φ hφπ g v : ↥(cmComm M Q Z B K γ M₀ φ)) : M₀.E) = φ g (v : M₀.E) := rfl

@[expose] noncomputable def cmCommGL (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K)) :
    ↥(H0 M Z) →* GL (Fin (2 * 4)) K where
  toFun g := glEquivLin (2 * 4) K ((e.symm.trans (cmCommActH hc hD φ hφπ g)).trans e)
  map_one' := by
    rw [← map_one (glEquivLin (2 * 4) K)]
    congr 1
    refine LinearEquiv.ext fun v => ?_
    simp
  map_mul' g h := by
    rw [← map_mul (glEquivLin (2 * 4) K)]
    congr 1
    refine LinearEquiv.ext fun v => ?_
    simp

theorem cmCommGL_mulVec (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K)) (g : ↥(H0 M Z))
    (v : ↥(cmComm M Q Z B K γ M₀ φ)) :
    ((cmCommGL hc hD φ hφπ e g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        e v = e (cmCommActH hc hD φ hφπ g v) := by
  rw [cmCommGL]
  show ((glEquivLin (2 * 4) K _ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
    e v = _
  rw [glEquivLin_mulVec]
  simp



theorem Ctx.complProdEquiv_act (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (e : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] (Fin (2 * 4) → K)) {s : ℕ}
    (c : ↥(M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)) ≃ₗ[K] (Fin (2 * s) → K))
    {g : ↥(H0 M Z)} (hg : ∀ z ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ), φ g z = z)
    (v : M₀.E) :
    complProdEquiv (hc.isCompl_cmComm_orthogonal hD φ hφπ) e c (φ g v) =
      (((cmCommGL hc hD φ hφπ e g : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          (complProdEquiv (hc.isCompl_cmComm_orthogonal hD φ hφπ) e c v).1,
        (complProdEquiv (hc.isCompl_cmComm_orthogonal hD φ hφπ) e c v).2) := by
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    exists_mem_add_eq_of_isCompl (hc.isCompl_cmComm_orthogonal hD φ hφπ) v
  have hgx : φ g x ∈ cmComm M Q Z B K γ M₀ φ := hc.mem_cmComm_of_act hD φ hφπ g.2 hx
  have h1 : φ g (x + y) = φ g x + y := by rw [map_add, hg y hy]
  rw [h1, complProdEquiv_add _ e c hgx hy, complProdEquiv_add _ e c hx hy]
  show (e ⟨φ g x, hgx⟩, c ⟨y, hy⟩) = (_, _)
  rw [cmCommGL_mulVec]
  rfl

theorem Ctx.mem_cmComm_of_mem_img_B (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {b₀ : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b₀) :
    b₀ ∈ cmComm M Q Z B K γ M₀ φ := by
  obtain ⟨a, haL, hA⟩ := ha2
  have haH : a ∈ H0 M Z := hc.LB_le_H0 haL
  obtain ⟨y, hyB, hyQ, hyb⟩ := (hB b₀).mpr ⟨1, (one_smul K b₀).symm⟩
  have hyD : y ∈ (⁅Q, Subgroup.zpowers a⁆ ⊔ Z : Subgroup G) :=
    hc.B_le_commutator_of_a2 haL hA hyB
  have hrange0 : b₀ ∈ LinearMap.range
      (((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) :=
    (hc.mem_img_zpowers_sup_iff φ hφπ haH hA.2.2.1 b₀).mp ⟨y, hyD, hyQ, hyb⟩
  rw [hc.range_sub_one_eq_map_cmComm hD φ hφπ ⟨a, haL, hA⟩ haL haH] at hrange0
  obtain ⟨x, hx, hxb⟩ := hrange0
  have hax : φ ⟨a, haH⟩ x ∈ cmComm M Q Z B K γ M₀ φ := hc.mem_cmComm_of_act hD φ hφπ haH hx
  rw [← hxb]
  have : φ ⟨a, haH⟩ x - x ∈ cmComm M Q Z B K γ M₀ φ := Submodule.sub_mem _ hax hx
  simpa using this

omit [(Q.subgroupOf M).Normal] [Finite K] in
theorem Ctx.img_inf_QB_orthogonal (hc : Ctx M Q Z B)
    {b₀ : M₀.E} (hperp : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔
      M₀.B (M₀.π x) b₀ = 0) {v : M₀.E} (hv : v ∈ M₀.img (Q ⊓ QB B)) : M₀.B v b₀ = 0 := by
  obtain ⟨x, hxS, hxQ, rfl⟩ := hv
  refine (hperp x hxQ).mp ?_
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbS : b ∈ Q ⊓ QB B := Subgroup.mem_inf.mpr ⟨hc.le hb, Ctx.B_le_QB hc hb⟩
  exact (congrArg Subtype.val
    ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨b, hbS⟩ ⟨x, hxS⟩)).symm.symm

end CFSG.RankThree.GF2n.Stroth80

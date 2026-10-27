module

public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Tensor
public import CFSG.RankThree.GF2n.Stroth80.Sec118CommBridge
import CFSG.RankThree.GF2n.Stroth80.CarterSec11CMIsometry
import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
import CFSG.RankThree.GF2n.Smith81.LinTLCentralizer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix
open CFSG.ClassicalGroups.Symplectic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

omit [(Q.subgroupOf M).Normal] [Finite K] in
theorem Ctx.map_sub_one_mem_img_inf_QB (hc : Ctx M Q Z B) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {b₀ : M₀.E} (hperp : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔
      M₀.B (M₀.π x) b₀ = 0)
    {l₀ : G} (hl₀ : l₀ ∈ LB M Q B) (hl₀H : l₀ ∈ H0 M Z) {y : M₀.E} (hy : M₀.B y b₀ = 0) :
    φ ⟨l₀, hl₀H⟩ y - y ∈ M₀.img (Q ⊓ QB B) := by
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj y
  have hxC : x ∈ Subgroup.centralizer (B : Set G) := (hperp x hxQ).mpr hy
  have hz₀ : ⁅l₀, x⁆ ∈ Q ⊓ QB B := hc.comm_mem_inf_of_mem_LB hl₀ ⟨hxQ, hxC⟩
  have hlxQ : l₀ * x * l₀⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hl₀H.1) x).mp hxQ
  have hπz₀ : M₀.π ⁅l₀, x⁆ = φ ⟨l₀, hl₀H⟩ (M₀.π x) - M₀.π x := by
    have e : ⁅l₀, x⁆ = (l₀ * x * l₀⁻¹) * x⁻¹ := by rw [commutatorElement_def]
    rw [e, M₀.π_mul _ hlxQ _ (Q.inv_mem hxQ), pi_inv hxQ, hφπ ⟨l₀, hl₀H⟩ x hxQ, sub_eq_add_neg]
  rw [← hπz₀]
  exact M₀.pi_mem_img hz₀ hz₀.1

omit [(Q.subgroupOf M).Normal] [Finite K] in
theorem Ctx.eq_smul_of_fixed_mem_img_inf_QB (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {b₀ : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b₀)
    {v : M₀.E} (hv : v ∈ M₀.img (Q ⊓ QB B))
    (hfix : ∀ (l : G) (_hl : l ∈ LB M Q B) (hlH : l ∈ H0 M Z), φ ⟨l, hlH⟩ v = v) :
    ∃ s : K, v = s • b₀ := by
  classical
  obtain ⟨x, hxS, hxQ, rfl⟩ := hv
  have hcomm : ∀ l ∈ LB M Q B, ⁅x, l⁆ ∈ Z := by
    intro l hl
    have hlH : l ∈ H0 M Z := hc.LB_le_H0 hl
    have hlxQ : l * x * l⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlH.1) x).mp hxQ
    have h1 : ⁅l, x⁆ ∈ Z := by
      refine (M₀.comm_mem_iff hxQ hlxQ).mpr ?_
      rw [hφπ ⟨l, hlH⟩ x hxQ]
      exact hfix l hl hlH
    have := Z.inv_mem h1
    rwa [commutatorElement_inv] at this
  have hBZ : x ∈ (B ⊔ Z : Subgroup G) := hc.mem_sup_of_comm_LB_mem_Z' hxS hcomm
  let S : Subgroup G :=
    { carrier := {w | w ∈ Q ∧ ∃ c ∈ B, M₀.π w = M₀.π c}
      one_mem' := ⟨Q.one_mem, 1, B.one_mem, rfl⟩
      mul_mem' := by
        rintro w w' ⟨hwQ, c, hcB, hwc⟩ ⟨hw'Q, c', hc'B, hw'c'⟩
        refine ⟨Q.mul_mem hwQ hw'Q, c * c', B.mul_mem hcB hc'B, ?_⟩
        rw [M₀.π_mul w hwQ w' hw'Q, M₀.π_mul c (hc.le hcB) c' (hc.le hc'B), hwc, hw'c']
      inv_mem' := by
        rintro w ⟨hwQ, c, hcB, hwc⟩
        refine ⟨Q.inv_mem hwQ, c⁻¹, B.inv_mem hcB, ?_⟩
        rw [pi_inv hwQ, pi_inv (hc.le hcB), hwc] }
  have hBS : B ≤ S := fun c hcB => ⟨hc.le hcB, c, hcB, rfl⟩
  have hZS : Z ≤ S := fun z hz =>
    ⟨hc.Z_le_Q hz, 1, B.one_mem, by
      rw [pi_one, (M₀.π_ker z (hc.Z_le_Q hz)).mpr hz]⟩
  obtain ⟨-, c, hcB, hzc⟩ := (sup_le hBS hZS) hBZ
  obtain ⟨s, hs⟩ := (hB _).mp (M₀.pi_mem_img hcB (hc.le hcB))
  exact ⟨s, by rw [hzc, hs]⟩


omit [Finite G] [Finite K] in
theorem polar_eq_zero_of_Qf_eq_zero {W : Submodule K M₀.E} (hW : ∀ w ∈ W, M₀.Qf w = 0)
    {x y : M₀.E} (hx : x ∈ W) (hy : y ∈ W) : M₀.B x y = 0 := by
  have h1 := M₀.Qf_add x y
  rw [hW _ (W.add_mem hx hy), hW x hx, hW y hy] at h1
  linear_combination -h1

theorem Ctx.exists_form_const [CharP K 2] (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {m : ℕ} (hm : 1 ≤ m) {W₁ W₂ : Submodule K M₀.E}
    (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (hW₁ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁)
    (hW₂ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂)
    (hs₁ : ∀ w ∈ W₁, M₀.Qf w = 0)
    (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K) (hρr : ρ.range = StatedSp m K)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (he₁ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₁),
      e₁ ⟨φ s w, hW₁ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₁ w)
    (he₂ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₂),
      e₂ ⟨φ s w, hW₂ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₂ w) :
    ∃ c : K, c ≠ 0 ∧ ∀ x y : Fin m ⊕ Fin m → K,
      M₀.B ((e₁.symm x : W₁) : M₀.E) ((e₂.symm y : W₂) : M₀.E) = c * spForm m K x y := by
  classical
  have hΦB : ∀ (t : ↥(XbarH M Q Z B)) (u v : M₀.E), M₀.B (φ t u) (φ t v) = M₀.B u v :=
    fun t u v => (isometry_of_π h (t : ↥(H0 M Z)) (hφπ t)).2 u v
  have hcoord₁ : ∀ (s : ↥(XbarH M Q Z B)) (x : Fin m ⊕ Fin m → K),
      φ s ((e₁.symm x : W₁) : M₀.E) =
        ((e₁.symm ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) : W₁) : M₀.E) := by
    intro s x
    have h1 := he₁ s (e₁.symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : (⟨φ s (e₁.symm x : W₁), hW₁ s _ (e₁.symm x).2⟩ : W₁) =
        e₁.symm ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
      apply e₁.injective
      rw [h1, LinearEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  have hcoord₂ : ∀ (s : ↥(XbarH M Q Z B)) (x : Fin m ⊕ Fin m → K),
      φ s ((e₂.symm x : W₂) : M₀.E) =
        ((e₂.symm ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) : W₂) : M₀.E) := by
    intro s x
    have h1 := he₂ s (e₂.symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : (⟨φ s (e₂.symm x : W₂), hW₂ s _ (e₂.symm x).2⟩ : W₂) =
        e₂.symm ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
      apply e₂.injective
      rw [h1, LinearEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  let β : LinearMap.BilinForm K (Fin m ⊕ Fin m → K) :=
    M₀.B.compl₁₂ (W₁.subtype ∘ₗ e₁.symm.toLinearMap) (W₂.subtype ∘ₗ e₂.symm.toLinearMap)
  have hβ : ∀ x y, β x y = M₀.B ((e₁.symm x : W₁) : M₀.E) ((e₂.symm y : W₂) : M₀.E) :=
    fun x y => rfl
  have hβinv : ∀ A ∈ StatedSp m K, ∀ x y : Fin m ⊕ Fin m → K,
      β ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)
        ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = β x y := by
    intro A hA x y
    rw [← hρr] at hA
    obtain ⟨s, rfl⟩ := hA
    rw [hβ, hβ, ← hcoord₁ s x, ← hcoord₂ s y, hΦB]
  obtain ⟨c, hc'⟩ := exists_eq_smul_spForm_of_invariant hm β hβinv
  refine ⟨c, ?_, fun x y => by rw [← hβ]; exact hc' x y⟩
  rintro rfl
  let x₀ : Fin m ⊕ Fin m → K := Pi.single (Sum.inl ⟨0, hm⟩) 1
  have hx₀ : x₀ ≠ 0 := by
    intro hx
    have := congrFun hx (Sum.inl ⟨0, hm⟩)
    simp [x₀] at this
  have hw : ((e₁.symm x₀ : W₁) : M₀.E) = 0 := by
    refine hc.eq_zero_of_mem_cmComm_of_orthogonal h φ hφπ ?_ ?_
    · rw [← hsup]; exact Submodule.mem_sup_left (e₁.symm x₀).2
    · intro z hz
      rw [← hsup] at hz
      obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
      have h1 : M₀.B ((e₁.symm x₀ : W₁) : M₀.E) z₁ = 0 :=
        polar_eq_zero_of_Qf_eq_zero hs₁ (e₁.symm x₀).2 hz₁
      have h2 : M₀.B ((e₁.symm x₀ : W₁) : M₀.E) z₂ = 0 := by
        have := hc' x₀ (e₂ ⟨z₂, hz₂⟩)
        rw [hβ, LinearEquiv.symm_apply_apply] at this
        rw [this]
        simp
      rw [map_add, h1, h2, add_zero]
  exact hx₀ (by
    have : e₁.symm x₀ = 0 := Subtype.ext hw
    simpa using this)

theorem Ctx.action_fixes_orthogonal_of_mem_XbarH (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (s : ↥(XbarH M Q Z B)) {z : M₀.E} (hz : z ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)) :
    φ s z = z := by
  have hcompl := hc.isCompl_cmComm_orthogonal h φ hφπ
  have hmem1 : φ s z - z ∈ cmComm M Q Z B K γ M₀ φ := by
    have h1 : φ s z - z ∈ LinearMap.range
        (((φ s : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) := ⟨z, by simp⟩
    exact (le_iSup (fun t : ↥(XbarH M Q Z B) => LinearMap.range
      (((φ t : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)) s) h1
  have hmem2 : φ s z - z ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) := by
    intro y hy
    have hinv : φ ((s : ↥(H0 M Z))⁻¹) y ∈ cmComm M Q Z B K γ M₀ φ :=
      hc.mem_cmComm_of_act h φ hφπ ((s : ↥(H0 M Z))⁻¹).2 hy
    have hiso := (isometry_of_π h (s : ↥(H0 M Z)) (hφπ s)).2
    have e1 : φ (s : ↥(H0 M Z)) (φ ((s : ↥(H0 M Z))⁻¹) y) = y := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    have e2 := hiso (φ ((s : ↥(H0 M Z))⁻¹) y) z
    rw [e1] at e2
    have e3 : M₀.B (φ ((s : ↥(H0 M Z))⁻¹) y) z = 0 := hz _ hinv
    show M₀.B y (φ s z - z) = 0
    rw [map_sub, hz y hy, e2, e3, sub_zero]
  have hbot := hcompl.disjoint
  have := Submodule.disjoint_def.mp hbot _ hmem1 hmem2
  exact sub_eq_zero.mp this

end CFSG.RankThree.GF2n.Stroth80

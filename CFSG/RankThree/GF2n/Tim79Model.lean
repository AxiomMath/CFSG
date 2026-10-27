module

public import CFSG.RankThree.GF2n.Tim79Class
public import CFSG.RankThree.GF2n.Tim79Heis

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G]

structure ModelCtx (V Q : Subgroup G) {K : Type} [Field K] (γ : G → K) : Prop where
  V_le : V ≤ Q
  comm_mem : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ V
  sq_mem : ∀ x ∈ Q, x ^ 2 ∈ V
  central : ∀ v ∈ V, ∀ y ∈ Q, v * y = y * v
  center_le : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x ∈ V
  γ_add : ∀ a ∈ V, ∀ b ∈ V, γ (a * b) = γ a + γ b
  γ_inj : ∀ a ∈ V, γ a = 0 → a = 1

theorem Hyp79.modelCtx [Finite G] {M V Q U₀ : Subgroup G}
    {K : Type} [Field K] (H : Hyp79 M V Q) (D₀ : MulData V U₀ Q K) : ModelCtx V Q D₀.γ where
  V_le := H.V_le_Q
  comm_mem := fun _ hx _ hy => H.comm_mem_V hx hy
  sq_mem := fun _ hx => H.sq_mem_V hx
  central := fun _ hv _ hy => H.V_central hv hy
  center_le := fun x hx hc => by
    have : x ∈ Q ⊓ Subgroup.centralizer (Q : Set G) :=
      ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm⟩
    rwa [H.special.2.1] at this
  γ_add := D₀.γ_add
  γ_inj := D₀.γ_inj

namespace ModelCtx

variable {V Q : Subgroup G} {K : Type} [Field K] {γ : G → K} (C : ModelCtx V Q γ)

include C

theorem γ_one : γ 1 = 0 := by
  have h := C.γ_add 1 V.one_mem 1 V.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

variable [CharP K 2]

theorem γ_inv {v : G} (hv : v ∈ V) : γ v⁻¹ = γ v := by
  have h := C.γ_add v hv v⁻¹ (V.inv_mem hv)
  rw [mul_inv_cancel, C.γ_one] at h
  exact (CharTwo.add_eq_zero.mp h.symm).symm

theorem mul_self_eq_one {v : G} (hv : v ∈ V) : v * v = 1 :=
  C.γ_inj _ (V.mul_mem hv hv) (by rw [C.γ_add v hv v hv, CharTwo.add_self_eq_zero])

theorem γ_sq_eq_zero {v : G} (hv : v ∈ V) : γ (v ^ 2) = 0 := by
  rw [pow_two, C.mul_self_eq_one hv, C.γ_one]

theorem comm_eq_one_left {v y : G} (hv : v ∈ V) (hy : y ∈ Q) : ⁅v, y⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (C.central v hv y hy)

theorem comm_eq_one_right {v y : G} (hv : v ∈ V) (hy : y ∈ Q) : ⁅y, v⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (C.central v hv y hy).symm

theorem comm_mul_left {x y z : G} (hx : x ∈ Q) (hy : y ∈ Q) (hz : z ∈ Q) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hyz : ⁅y, z⁆ ∈ V := C.comm_mem y hy z hz
  have hxz : ⁅x, z⁆ ∈ V := C.comm_mem x hx z hz
  have h1 : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
    rw [← C.central _ hyz x hx, mul_inv_cancel_right]
  have h2 : ⁅x, z⁆ * ⁅y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ := (C.central _ hyz _ (C.V_le hxz)).symm
  calc ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [h1]
    _ = ⁅x, z⁆ * ⁅y, z⁆ := h2.symm

theorem γ_comm_mul_left {x y z : G} (hx : x ∈ Q) (hy : y ∈ Q) (hz : z ∈ Q) :
    γ ⁅x * y, z⁆ = γ ⁅x, z⁆ + γ ⁅y, z⁆ := by
  rw [C.comm_mul_left hx hy hz]
  exact C.γ_add _ (C.comm_mem x hx z hz) _ (C.comm_mem y hy z hz)

theorem γ_comm_symm {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : γ ⁅y, x⁆ = γ ⁅x, y⁆ := by
  rw [← commutatorElement_inv, C.γ_inv (C.comm_mem x hx y hy)]

theorem γ_comm_inv_left {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : γ ⁅x⁻¹, y⁆ = γ ⁅x, y⁆ := by
  have h := C.γ_comm_mul_left (Q.inv_mem hx) hx hy
  rw [inv_mul_cancel, commutatorElement_one_left, C.γ_one] at h
  exact CharTwo.add_eq_zero.mp h.symm

theorem γ_sq_mul {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    γ ((x * y) ^ 2) = γ (x ^ 2) + γ (y ^ 2) + γ ⁅x, y⁆ := by
  have hyx : ⁅y, x⁆ ∈ V := C.comm_mem y hy x hx
  have h1 : x * ⁅y, x⁆ * x⁻¹ = ⁅y, x⁆ := by
    rw [← C.central _ hyx x hx, mul_inv_cancel_right]
  have e : (x * y) ^ 2 = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
    calc (x * y) ^ 2 = x * ⁅y, x⁆ * x⁻¹ * (x ^ 2 * y ^ 2) := by
          simp only [commutatorElement_def, pow_two]; group
      _ = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by rw [h1]
  rw [e, C.γ_add _ hyx _ (V.mul_mem (C.sq_mem x hx) (C.sq_mem y hy)),
    C.γ_add _ (C.sq_mem x hx) _ (C.sq_mem y hy), C.γ_comm_symm hx hy]
  ring

theorem γ_sq_inv {x : G} (hx : x ∈ Q) : γ (x⁻¹ ^ 2) = γ (x ^ 2) := by
  rw [inv_pow, C.γ_inv (C.sq_mem x hx)]

private theorem exists_smul_of_datum {U : Subgroup G} (hUQ : U ≤ Q) (D : MulData V U Q K)
    {c : K} (hc : c ≠ 0) {σ : K ≃+* K} (hcσ : ∀ v ∈ V, D.γ v = c * σ (γ v)) {u : G} (hu : u ∈ U)
    (lam : K) :
    ∃ u' ∈ U, (∀ y ∈ Q, γ ⁅u', y⁆ = lam * γ ⁅u, y⁆) ∧ u' * u' = 1 ∧ u * u = 1 := by
  have hsq : ∀ w ∈ U, w * w = 1 := fun w hw =>
    D.ψ_inj _ (U.mul_mem hw hw) (by rw [D.ψ_add w hw w hw, CharTwo.add_self_eq_zero])
  have key : ∀ w ∈ U, ∀ y ∈ Q, γ ⁅w, y⁆ = σ.symm (c⁻¹ * D.ψ w) * σ.symm (D.t y) := by
    intro w hw y hy
    obtain ⟨hV, hγ⟩ := D.comm y hy w hw
    have h1 : c * σ (γ ⁅y, w⁆) = D.t y * D.ψ w := by rw [← hcσ _ hV, hγ]
    have h2 : γ ⁅y, w⁆ = σ.symm (c⁻¹ * (D.t y * D.ψ w)) := by
      rw [← h1, ← mul_assoc, inv_mul_cancel₀ hc, one_mul, RingEquiv.symm_apply_apply]
    rw [← C.γ_comm_symm (hUQ hw) hy, h2, ← map_mul]
    congr 1
    ring
  refine ⟨D.uinv (c * σ (lam * σ.symm (c⁻¹ * D.ψ u))), D.uinv_mem _, fun y hy => ?_,
    hsq _ (D.uinv_mem _), hsq u hu⟩
  rw [key _ (D.uinv_mem _) y hy, key u hu y hy, D.ψ_uinv, ← mul_assoc c⁻¹, inv_mul_cancel₀ hc,
    one_mul, RingEquiv.symm_apply_apply, mul_assoc]

theorem exists_smul_of_mem_classGroup {x : G} (hx : x ∈ classGroup V Q γ) (lam : K) :
    ∃ x' ∈ classGroup V Q γ, (∀ y ∈ Q, γ ⁅x', y⁆ = lam * γ ⁅x, y⁆) ∧
      γ (x' ^ 2) = lam ^ 2 * γ (x ^ 2) := by
  induction hx using Subgroup.closure_induction generalizing lam with
  | mem x hx =>
    rcases hx with hxV | hxU
    · refine ⟨1, one_mem _, fun y hy => ?_, ?_⟩
      · rw [commutatorElement_one_left, C.γ_one, C.comm_eq_one_left hxV hy, C.γ_one, mul_zero]
      · rw [one_pow, C.γ_one, C.γ_sq_eq_zero hxV, mul_zero]
    · obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp hxU
      obtain ⟨-, hUQ, -, D, c, σ, hc, hcσ⟩ := id hU
      obtain ⟨u', hu', h1, h2, h3⟩ := C.exists_smul_of_datum hUQ D hc hcσ hxU lam
      refine ⟨u', le_classGroup_of_mem hU hu', h1, ?_⟩
      have e1 : u' ^ 2 = 1 := by rw [pow_two]; exact h2
      have e2 : x ^ 2 = 1 := by rw [pow_two]; exact h3
      rw [e1, e2, C.γ_one, mul_zero]
  | one =>
    refine ⟨1, one_mem _, fun y hy => ?_, ?_⟩
    · rw [commutatorElement_one_left, C.γ_one, mul_zero]
    · rw [one_pow, C.γ_one, mul_zero]
  | mul x y hx hy ihx ihy =>
    obtain ⟨x₁, hx₁, hx₁c, hx₁s⟩ := ihx lam
    obtain ⟨y₁, hy₁, hy₁c, hy₁s⟩ := ihy lam
    have hxQ : x ∈ Q := classGroup_le C.V_le hx
    have hyQ : y ∈ Q := classGroup_le C.V_le hy
    have hx₁Q : x₁ ∈ Q := classGroup_le C.V_le hx₁
    have hy₁Q : y₁ ∈ Q := classGroup_le C.V_le hy₁
    refine ⟨x₁ * y₁, Subgroup.mul_mem _ hx₁ hy₁, fun z hz => ?_, ?_⟩
    · rw [C.γ_comm_mul_left hx₁Q hy₁Q hz, C.γ_comm_mul_left hxQ hyQ hz, hx₁c z hz, hy₁c z hz]
      ring
    · have hB : γ ⁅x₁, y₁⁆ = lam ^ 2 * γ ⁅x, y⁆ := by
        rw [hx₁c y₁ hy₁Q, ← C.γ_comm_symm hxQ hy₁Q, hy₁c x hxQ, C.γ_comm_symm hxQ hyQ]
        ring
      rw [C.γ_sq_mul hx₁Q hy₁Q, C.γ_sq_mul hxQ hyQ, hx₁s, hy₁s, hB]
      ring
  | inv x hx ih =>
    obtain ⟨x₁, hx₁, hx₁c, hx₁s⟩ := ih lam
    have hxQ : x ∈ Q := classGroup_le C.V_le hx
    have hx₁Q : x₁ ∈ Q := classGroup_le C.V_le hx₁
    refine ⟨x₁⁻¹, Subgroup.inv_mem _ hx₁, fun z hz => ?_, ?_⟩
    · rw [C.γ_comm_inv_left hx₁Q hz, C.γ_comm_inv_left hxQ hz, hx₁c z hz]
    · rw [C.γ_sq_inv hx₁Q, C.γ_sq_inv hxQ, hx₁s]

end ModelCtx

section Model

variable {V Q : Subgroup G} {K : Type} [Field K] [CharP K 2] {γ : G → K}

private def jh (Q : Subgroup G) (γ : G → K) (x : G) : ↥Q → K := fun y => γ ⁅x, (y : G)⁆

private def Esub (C : ModelCtx V Q γ) : Submodule K (↥Q → K) where
  carrier := {φ | ∃ x ∈ classGroup V Q γ, jh Q γ x = φ}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x * y, Subgroup.mul_mem _ hx hy, funext fun z => ?_⟩
    exact C.γ_comm_mul_left (classGroup_le C.V_le hx) (classGroup_le C.V_le hy) z.2
  zero_mem' := ⟨1, one_mem _, funext fun z => by
    show γ ⁅1, (z : G)⁆ = 0
    rw [commutatorElement_one_left, C.γ_one]⟩
  smul_mem' := by
    rintro lam _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', h1, -⟩ := C.exists_smul_of_mem_classGroup hx lam
    exact ⟨x', hx', funext fun z => h1 z z.2⟩

private theorem mem_Esub (C : ModelCtx V Q γ) {φ : ↥Q → K} :
    φ ∈ Esub C ↔ ∃ x ∈ classGroup V Q γ, jh Q γ x = φ := Iff.rfl

private noncomputable def liftE (C : ModelCtx V Q γ) (e : Esub C) : G :=
  Classical.choose ((mem_Esub C).mp e.2)

private theorem liftE_mem (C : ModelCtx V Q γ) (e : Esub C) : liftE C e ∈ classGroup V Q γ :=
  (Classical.choose_spec ((mem_Esub C).mp e.2)).1

private theorem jh_liftE (C : ModelCtx V Q γ) (e : Esub C) : jh Q γ (liftE C e) = e.1 :=
  (Classical.choose_spec ((mem_Esub C).mp e.2)).2

private noncomputable def Bval (C : ModelCtx V Q γ) (φ ψ : Esub C) : K :=
  ψ.1 ⟨liftE C φ, classGroup_le C.V_le (liftE_mem C φ)⟩

private theorem Bval_eq (C : ModelCtx V Q γ) (φ ψ : Esub C) :
    Bval C φ ψ = γ ⁅liftE C ψ, liftE C φ⁆ :=
  (congrFun (jh_liftE C ψ) ⟨liftE C φ, classGroup_le C.V_le (liftE_mem C φ)⟩).symm

private theorem Bval_symm (C : ModelCtx V Q γ) (φ ψ : Esub C) : Bval C φ ψ = Bval C ψ φ := by
  rw [Bval_eq, Bval_eq]
  exact C.γ_comm_symm (classGroup_le C.V_le (liftE_mem C φ))
    (classGroup_le C.V_le (liftE_mem C ψ))

private noncomputable def Bform (C : ModelCtx V Q γ) : LinearMap.BilinForm K (Esub C) :=
  LinearMap.mk₂ K (Bval C)
    (fun φ₁ φ₂ ψ => by
      rw [Bval_symm C (φ₁ + φ₂) ψ, Bval_symm C φ₁ ψ, Bval_symm C φ₂ ψ]
      rfl)
    (fun c φ ψ => by
      rw [Bval_symm C (c • φ) ψ, Bval_symm C φ ψ]
      rfl)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

open scoped _root_.Classical in
private noncomputable def piE (C : ModelCtx V Q γ) (x : G) : Esub C :=
  if hx : x ∈ classGroup V Q γ then ⟨jh Q γ x, x, hx, rfl⟩ else 0

private theorem piE_val (C : ModelCtx V Q γ) {x : G} (hx : x ∈ classGroup V Q γ) :
    (piE C x).1 = jh Q γ x := by
  simp only [piE, dif_pos hx]

private theorem piE_mul (C : ModelCtx V Q γ) {x y : G} (hx : x ∈ classGroup V Q γ)
    (hy : y ∈ classGroup V Q γ) : piE C (x * y) = piE C x + piE C y := by
  apply Subtype.ext
  rw [piE_val C (Subgroup.mul_mem _ hx hy), Submodule.coe_add, piE_val C hx, piE_val C hy]
  funext z
  exact C.γ_comm_mul_left (classGroup_le C.V_le hx) (classGroup_le C.V_le hy) z.2

private theorem piE_surj (C : ModelCtx V Q γ) (e : Esub C) :
    ∃ x ∈ classGroup V Q γ, piE C x = e := by
  obtain ⟨x, hx, hxe⟩ := (mem_Esub C).mp e.2
  exact ⟨x, hx, Subtype.ext (by rw [piE_val C hx]; exact hxe)⟩

private theorem piE_eq_zero_iff (C : ModelCtx V Q γ) {x : G} (hx : x ∈ classGroup V Q γ) :
    piE C x = 0 ↔ x ∈ V := by
  have hxQ := classGroup_le C.V_le hx
  constructor
  · intro h
    refine C.center_le x hxQ fun y hy => ?_
    have h1 : γ ⁅x, y⁆ = 0 := by
      have := congrFun (congrArg Subtype.val h) ⟨y, hy⟩
      rw [piE_val C hx] at this
      exact this
    exact commutatorElement_eq_one_iff_mul_comm.mp (C.γ_inj _ (C.comm_mem x hxQ y hy) h1)
  · intro h
    apply Subtype.ext
    rw [piE_val C hx]
    funext z
    show γ ⁅x, (z : G)⁆ = 0
    rw [C.comm_eq_one_left h z.2, C.γ_one]

private theorem Bval_piE (C : ModelCtx V Q γ) {x y : G} (hx : x ∈ classGroup V Q γ)
    (hy : y ∈ classGroup V Q γ) : Bval C (piE C x) (piE C y) = γ ⁅x, y⁆ := by
  have hyQ := classGroup_le C.V_le hy
  have hl := classGroup_le C.V_le (liftE_mem C (piE C x))
  have h1 : Bval C (piE C x) (piE C y) = γ ⁅y, liftE C (piE C x)⁆ := by
    unfold Bval
    rw [piE_val C hy]
    rfl
  rw [h1, C.γ_comm_symm hl hyQ]
  have h2 := congrFun (jh_liftE C (piE C x)) ⟨y, hyQ⟩
  rw [piE_val C hx] at h2
  exact h2

private theorem sq_eq_of_jh_eq (C : ModelCtx V Q γ) {x x' : G} (hx : x ∈ classGroup V Q γ)
    (hx' : x' ∈ classGroup V Q γ) (h : ∀ z ∈ Q, γ ⁅x', z⁆ = γ ⁅x, z⁆) :
    γ (x' ^ 2) = γ (x ^ 2) := by
  have hxQ := classGroup_le C.V_le hx
  have hx'Q := classGroup_le C.V_le hx'
  have hvQ : x⁻¹ * x' ∈ Q := Q.mul_mem (Q.inv_mem hxQ) hx'Q
  have hv : x⁻¹ * x' ∈ V := by
    refine C.center_le _ hvQ fun z hz => ?_
    have h0 : γ ⁅x⁻¹ * x', z⁆ = 0 := by
      rw [C.γ_comm_mul_left (Q.inv_mem hxQ) hx'Q hz, C.γ_comm_inv_left hxQ hz, h z hz,
        CharTwo.add_self_eq_zero]
    exact commutatorElement_eq_one_iff_mul_comm.mp (C.γ_inj _ (C.comm_mem _ hvQ z hz) h0)
  have e : γ (x' ^ 2) = γ ((x * (x⁻¹ * x')) ^ 2) := by rw [mul_inv_cancel_left]
  rw [e, C.γ_sq_mul hxQ hvQ, C.γ_sq_eq_zero hv, C.comm_eq_one_right hv hxQ, C.γ_one, add_zero,
    add_zero]

private noncomputable def Qform (C : ModelCtx V Q γ) (e : Esub C) : K := γ ((liftE C e) ^ 2)

private theorem Qform_piE (C : ModelCtx V Q γ) {x : G} (hx : x ∈ classGroup V Q γ) :
    Qform C (piE C x) = γ (x ^ 2) := by
  refine sq_eq_of_jh_eq C hx (liftE_mem C (piE C x)) fun z hz => ?_
  have h2 := congrFun (jh_liftE C (piE C x)) ⟨z, hz⟩
  rw [piE_val C hx] at h2
  exact h2

private theorem comm_of_comm_classGroup {x : G}
    (hcl : Q = classGroup V Q γ ⊔ (Q ⊓ Subgroup.centralizer (classGroup V Q γ : Set G)))
    (hx : x ∈ classGroup V Q γ) (h : ∀ y ∈ classGroup V Q γ, x * y = y * x) :
    ∀ z ∈ Q, x * z = z * x := by
  have hle : Q ≤ Subgroup.centralizer ({x} : Set G) := by
    refine hcl.le.trans (sup_le (fun y hy => ?_) (fun z hz => ?_))
    · refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      rw [Set.mem_singleton_iff.mp ha]
      exact h y hy
    · refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      rw [Set.mem_singleton_iff.mp ha]
      exact Subgroup.mem_centralizer_iff.mp hz.2 x hx
  intro z hz
  exact Subgroup.mem_centralizer_iff.mp (hle hz) x rfl

theorem exists_quadModel_of_ctx [Finite G] (C : ModelCtx V Q γ)
    (hcl : Q = classGroup V Q γ ⊔ (Q ⊓ Subgroup.centralizer (classGroup V Q γ : Set G))) :
    Nonempty (QuadModel (classGroup V Q γ) V K γ) := by
  refine ⟨{
    E := Esub C
    π := piE C
    B := Bform C
    Qf := Qform C
    π_mul := fun x hx y hy => piE_mul C hx hy
    π_surj := piE_surj C
    π_ker := fun x hx => piE_eq_zero_iff C hx
    comm_mem := fun x hx y hy =>
      C.comm_mem x (classGroup_le C.V_le hx) y (classGroup_le C.V_le hy)
    sq_mem := fun x hx => C.sq_mem x (classGroup_le C.V_le hx)
    comm_eq := fun x hx y hy => (Bval_piE C hx hy).symm
    sq_eq := fun x hx => (Qform_piE C hx).symm
    alt := ?_
    nondeg := ?_
    Qf_smul := ?_
    Qf_add := ?_ }⟩
  · intro e
    obtain ⟨x, hx, rfl⟩ := piE_surj C e
    show Bval C (piE C x) (piE C x) = 0
    rw [Bval_piE C hx hx, commutatorElement_self, C.γ_one]
  · intro e he
    obtain ⟨x, hx, rfl⟩ := piE_surj C e
    have hxQ := classGroup_le C.V_le hx
    have hcomm : ∀ y ∈ classGroup V Q γ, x * y = y * x := by
      intro y hy
      have h1 : γ ⁅x, y⁆ = 0 := by
        have := he (piE C y)
        rw [show Bform C (piE C x) (piE C y) = Bval C (piE C x) (piE C y) from rfl,
          Bval_piE C hx hy] at this
        exact this
      exact commutatorElement_eq_one_iff_mul_comm.mp
        (C.γ_inj _ (C.comm_mem x hxQ y (classGroup_le C.V_le hy)) h1)
    have hall := comm_of_comm_classGroup hcl hx hcomm
    apply Subtype.ext
    rw [piE_val C hx]
    funext z
    show γ ⁅x, (z : G)⁆ = 0
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hall z z.2), C.γ_one]
  · intro c e
    obtain ⟨x, hx, rfl⟩ := piE_surj C e
    obtain ⟨x', hx', h1, h2⟩ := C.exists_smul_of_mem_classGroup hx c
    have h3 : c • piE C x = piE C x' := by
      apply Subtype.ext
      rw [Submodule.coe_smul, piE_val C hx, piE_val C hx']
      funext z
      exact (h1 z z.2).symm
    show Qform C (c • piE C x) = c ^ 2 * Qform C (piE C x)
    rw [h3, Qform_piE C hx', Qform_piE C hx, h2]
  · intro e f
    obtain ⟨x, hx, rfl⟩ := piE_surj C e
    obtain ⟨y, hy, rfl⟩ := piE_surj C f
    show Qform C (piE C x + piE C y) = Qform C (piE C x) + Qform C (piE C y) +
      Bval C (piE C x) (piE C y)
    rw [← piE_mul C hx hy, Qform_piE C (Subgroup.mul_mem _ hx hy), Qform_piE C hx,
      Qform_piE C hy, Bval_piE C hx hy]
    exact C.γ_sq_mul (classGroup_le C.V_le hx) (classGroup_le C.V_le hy)

end Model

theorem QuadModel.exists_similitude {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : QuadModel QF V K γ) (hVQF : V ≤ QF) {τ : G} {a : K}
    (hτV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQF : ∀ x ∈ QF, τ * x * τ⁻¹ ∈ QF) (hQF' : ∀ x ∈ QF, τ⁻¹ * x * τ ∈ QF)
    (hγ : ∀ v ∈ V, γ (τ * v * τ⁻¹) = a * γ v) :
    ∃ τE : M₀.E ≃ₗ[K] M₀.E, (∀ x ∈ QF, M₀.π (τ * x * τ⁻¹) = τE (M₀.π x)) ∧
      (∀ e f, M₀.B (τE e) (τE f) = a * M₀.B e f) ∧ ∀ e, M₀.Qf (τE e) = a * M₀.Qf e := by
  have hVn : ∀ v, v ∈ V ↔ τ * v * τ⁻¹ ∈ V := Subgroup.mem_normalizer_iff.mp hτV
  have pi_one : M₀.π 1 = 0 := by
    have h := M₀.π_mul 1 QF.one_mem 1 QF.one_mem
    rw [mul_one] at h
    exact left_eq_add.mp h
  have pi_inv : ∀ x ∈ QF, M₀.π x⁻¹ = - M₀.π x := by
    intro x hx
    have h := M₀.π_mul x hx x⁻¹ (QF.inv_mem hx)
    rw [mul_inv_cancel, pi_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have pi_eq : ∀ x ∈ QF, ∀ y ∈ QF, M₀.π x = M₀.π y → x⁻¹ * y ∈ V := by
    intro x hx y hy h
    refine (M₀.π_ker _ (QF.mul_mem (QF.inv_mem hx) hy)).mp ?_
    rw [M₀.π_mul _ (QF.inv_mem hx) _ hy, pi_inv x hx, h, neg_add_cancel]
  choose lift hlift_mem hlift using M₀.π_surj
  let f₀ : M₀.E → M₀.E := fun e => M₀.π (τ * lift e * τ⁻¹)
  have hf₀ : ∀ x ∈ QF, f₀ (M₀.π x) = M₀.π (τ * x * τ⁻¹) := by
    intro x hx
    have h1 : x⁻¹ * lift (M₀.π x) ∈ V := pi_eq x hx _ (hlift_mem _) (hlift _).symm
    have hv : τ * (x⁻¹ * lift (M₀.π x)) * τ⁻¹ ∈ V := (hVn _).mp h1
    have e : τ * lift (M₀.π x) * τ⁻¹ =
        τ * x * τ⁻¹ * (τ * (x⁻¹ * lift (M₀.π x)) * τ⁻¹) := by group
    show M₀.π (τ * lift (M₀.π x) * τ⁻¹) = _
    rw [e, M₀.π_mul _ (hQF x hx) _ (hVQF hv), (M₀.π_ker _ (hVQF hv)).mpr hv, add_zero]
  have hadd : ∀ e e' : M₀.E, f₀ (e + e') = f₀ e + f₀ e' := by
    intro e e'
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj e'
    rw [← M₀.π_mul x hx y hy, hf₀ _ (QF.mul_mem hx hy), hf₀ x hx, hf₀ y hy,
      show τ * (x * y) * τ⁻¹ = τ * x * τ⁻¹ * (τ * y * τ⁻¹) by group,
      M₀.π_mul _ (hQF x hx) _ (hQF y hy)]
  have hB : ∀ e f : M₀.E, M₀.B (f₀ e) (f₀ f) = a * M₀.B e f := by
    intro e f
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj f
    rw [hf₀ x hx, hf₀ y hy, ← M₀.comm_eq _ (hQF x hx) _ (hQF y hy), ← M₀.comm_eq x hx y hy,
      show ⁅τ * x * τ⁻¹, τ * y * τ⁻¹⁆ = τ * ⁅x, y⁆ * τ⁻¹ by
        simp only [commutatorElement_def]; group]
    exact hγ _ (M₀.comm_mem x hx y hy)
  have hQ : ∀ e : M₀.E, M₀.Qf (f₀ e) = a * M₀.Qf e := by
    intro e
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    rw [hf₀ x hx, ← M₀.sq_eq _ (hQF x hx), ← M₀.sq_eq x hx,
      show (τ * x * τ⁻¹) ^ 2 = τ * x ^ 2 * τ⁻¹ by rw [pow_two, pow_two]; group]
    exact hγ _ (M₀.sq_mem x hx)
  have hsurj : Function.Surjective f₀ := by
    intro g
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj g
    refine ⟨M₀.π (τ⁻¹ * y * τ), ?_⟩
    rw [hf₀ _ (hQF' y hy), show τ * (τ⁻¹ * y * τ) * τ⁻¹ = y by group]
  have hsmul : ∀ (c : K) (e : M₀.E), f₀ (c • e) = c • f₀ e := by
    intro c e
    refine sub_eq_zero.mp (M₀.nondeg _ fun g => ?_)
    obtain ⟨g', rfl⟩ := hsurj g
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hB]
    ring
  have hinj : ∀ e : M₀.E, f₀ e = 0 → e = 0 := by
    intro e he
    have hx := hlift_mem e
    have h1 : τ * lift e * τ⁻¹ ∈ V := (M₀.π_ker _ (hQF _ hx)).mp he
    have h2 : lift e ∈ V := (hVn _).mpr h1
    rw [← hlift e]
    exact (M₀.π_ker _ hx).mpr h2
  let Tm : M₀.E →ₗ[K] M₀.E := { toFun := f₀, map_add' := hadd, map_smul' := hsmul }
  have hTinj : Function.Injective Tm := (injective_iff_map_eq_zero Tm).mpr hinj
  exact ⟨LinearEquiv.ofBijective Tm ⟨hTinj, hsurj⟩, fun x hx => (hf₀ x hx).symm, hB, hQ⟩

theorem Hyp79.exists_quadModel [Finite G] {M V Q : Subgroup G}
    (H : Hyp79 M V Q) {n : ℕ} {U₀ : Subgroup G} (hU₀ : ∃ g : G, U₀ = conjSubgroup g V)
    (hU₀Q : U₀ ≤ Q) (hU₀V : U₀ ≠ V) (D₀ : MulData V U₀ Q (GaloisField 2 n)) :
    ∃ M₀ : QuadModel (classGroup V Q D₀.γ) V (GaloisField 2 n) D₀.γ,
      (∃ (e₀ : M₀.E) (ℓ : M₀.E →ₗ[GaloisField 2 n] GaloisField 2 n),
        (∀ u ∈ U₀, M₀.π u = D₀.ψ u • e₀) ∧ (∀ y ∈ classGroup V Q D₀.γ, D₀.t y = ℓ (M₀.π y)) ∧
          ∀ f, M₀.B e₀ f = ℓ f) ∧
      (∀ τ ∈ M, ∀ a : GaloisField 2 n, (∀ v ∈ V, D₀.γ (τ * v * τ⁻¹) = a * D₀.γ v) →
        ∃ τE : M₀.E ≃ₗ[GaloisField 2 n] M₀.E,
          (∀ x ∈ classGroup V Q D₀.γ, τ * x * τ⁻¹ ∈ classGroup V Q D₀.γ ∧
            M₀.π (τ * x * τ⁻¹) = τE (M₀.π x)) ∧
          (∀ e f, M₀.B (τE e) (τE f) = a * M₀.B e f) ∧ ∀ e, M₀.Qf (τE e) = a * M₀.Qf e) := by
  have C := H.modelCtx D₀
  obtain ⟨M₀⟩ := exists_quadModel_of_ctx C (H.eq_classGroup_sup_centralizer D₀ hU₀ hU₀Q hU₀V)
  have hU₀cl : U₀ ≤ classGroup V Q D₀.γ :=
    le_classGroup_of_mem (mem_classOf_self D₀ hU₀ hU₀Q hU₀V)
  have hBU : ∀ u ∈ U₀, ∀ y ∈ classGroup V Q D₀.γ,
      M₀.B (M₀.π u) (M₀.π y) = D₀.t y * D₀.ψ u := by
    intro u hu y hy
    rw [← M₀.comm_eq u (hU₀cl hu) y hy, ← C.γ_comm_symm (hU₀Q hu) (classGroup_le C.V_le hy)]
    exact (D₀.comm y (classGroup_le C.V_le hy) u hu).2
  refine ⟨M₀, ⟨M₀.π (D₀.uinv 1), M₀.B (M₀.π (D₀.uinv 1)), ?_, ?_, fun f => rfl⟩, ?_⟩
  · intro u hu
    refine sub_eq_zero.mp (M₀.nondeg _ fun f => ?_)
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj f
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hBU u hu y hy, hBU _ (D₀.uinv_mem 1) y hy, D₀.ψ_uinv, mul_one]
    ring
  · intro y hy
    show D₀.t y = M₀.B (M₀.π (D₀.uinv 1)) (M₀.π y)
    rw [hBU _ (D₀.uinv_mem 1) y hy, D₀.ψ_uinv, mul_one]
  · intro τ hτ a hγ
    obtain ⟨g, hgV, hgQ⟩ := H.exists_opposite
    have h218 := H.toHyp218 hgV hgQ
    have hV : τ ∈ Subgroup.normalizer (V : Set G) := h218.M_le_normalizer hτ
    have hQ : τ ∈ Subgroup.normalizer (Q : Set G) := h218.M_le_normalizer_Q hτ
    have hVn : ∀ v, v ∈ V ↔ τ * v * τ⁻¹ ∈ V := Subgroup.mem_normalizer_iff.mp hV
    have ha : a ≠ 0 := by
      rintro rfl
      have hV1 : V = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall V).mpr fun v hv => ?_
        have h0 := hγ v hv
        rw [zero_mul] at h0
        have h1 : τ * v * τ⁻¹ = 1 := D₀.γ_inj _ ((hVn v).mp hv) h0
        calc v = τ⁻¹ * (τ * v * τ⁻¹) * τ := by group
          _ = 1 := by rw [h1]; group
      have h4 := H.q4
      rw [hV1, Subgroup.card_bot] at h4
      omega
    have hQF : ∀ x ∈ classGroup V Q D₀.γ, τ * x * τ⁻¹ ∈ classGroup V Q D₀.γ :=
      fun x hx => conj_mem_classGroup hV hQ ha hγ hx
    have hγ' : ∀ v ∈ V, D₀.γ (τ⁻¹ * v * τ⁻¹⁻¹) = a⁻¹ * D₀.γ v := fun v hv => by
      simpa using gamma_conj_inv hV ha hγ hv
    have hQF' : ∀ x ∈ classGroup V Q D₀.γ, τ⁻¹ * x * τ ∈ classGroup V Q D₀.γ := fun x hx => by
      simpa using conj_mem_classGroup (inv_mem hV) (inv_mem hQ) (inv_ne_zero ha) hγ' hx
    obtain ⟨τE, h1, h2, h3⟩ := M₀.exists_similitude V_le_classGroup hV hQF hQF' hγ
    exact ⟨τE, fun x hx => ⟨hQF x hx, h1 x hx⟩, h2, h3⟩

end CFSG.RankThree.GF2n.Tim79

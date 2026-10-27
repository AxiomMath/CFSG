module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110Pairing
public import CFSG.RankThree.GF2n.Stroth80.Sec1110Core
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatField
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
public import CFSG.RankThree.GF2n.Stroth80.Sec5SLDual

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.SpecialLinear
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
variable {n : ℕ} {X₁ X₂ X₃ X₄ : Subgroup G}

private noncomputable def piHom₂ (hXQ : X₂ ≤ Q) : ↥X₂ →* Multiplicative M₀.E where
  toFun x := Multiplicative.ofAdd (M₀.π (x : G))
  map_one' := by
    rw [Subgroup.coe_one, Tim79.QuadModel.pi_one]
    rfl
  map_mul' x y := by
    rw [Subgroup.coe_mul, M₀.π_mul (x : G) (hXQ x.2) (y : G) (hXQ y.2)]
    rfl

private theorem piHom₂_apply (hXQ : X₂ ≤ Q) (x : ↥X₂) :
    piHom₂ (M₀ := M₀) (X₂ := X₂) hXQ x =
      Multiplicative.ofAdd (M₀.π (x : G)) := rfl

private theorem le_ker_piHom₂ (hX₁ : X₁ = Z) (hXQ : X₂ ≤ Q) :
    X₁.subgroupOf X₂ ≤ (piHom₂ (M₀ := M₀) (X₂ := X₂) hXQ).ker := by
  intro z hz
  rw [Subgroup.mem_subgroupOf] at hz
  have hzZ : (z : G) ∈ Z := by rw [← hX₁]; exact hz
  rw [MonoidHom.mem_ker, piHom₂_apply, (M₀.π_ker (z : G) (hXQ z.2)).mpr hzZ]
  rfl

private noncomputable def piQuot₂ [(X₁.subgroupOf X₂).Normal] (hX₁ : X₁ = Z) (hXQ : X₂ ≤ Q) :
    (↥X₂ ⧸ X₁.subgroupOf X₂) →* Multiplicative M₀.E :=
  QuotientGroup.lift _ (piHom₂ (M₀ := M₀) (X₂ := X₂) hXQ)
    (le_ker_piHom₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ)

private theorem piQuot₂_mk [(X₁.subgroupOf X₂).Normal] (hX₁ : X₁ = Z) (hXQ : X₂ ≤ Q)
    (x : ↥X₂) :
    piQuot₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ (QuotientGroup.mk x) =
      Multiplicative.ofAdd (M₀.π (x : G)) := rfl

private noncomputable def coord₂ [(X₁.subgroupOf X₂).Normal] (hX₁ : X₁ = Z) (hXQ : X₂ ≤ Q)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) : (Fin n → K) →+ M₀.E where
  toFun u := Multiplicative.toAdd
    (piQuot₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ (ψ.symm (Multiplicative.ofAdd u)))
  map_zero' := by
    rw [show piQuot₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ
        (ψ.symm (Multiplicative.ofAdd (0 : Fin n → K))) =
        piQuot₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ 1 from by
      rw [show Multiplicative.ofAdd (0 : Fin n → K) = 1 from rfl, map_one]]
    rw [map_one, toAdd_one]
  map_add' u v := by
    rw [ofAdd_add, map_mul, map_mul, toAdd_mul]

private theorem coord₂_mk [(X₁.subgroupOf X₂).Normal] (hX₁ : X₁ = Z) (hXQ : X₂ ≤ Q)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) (x : ↥X₂) :
    coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ ψ
        (Multiplicative.toAdd (ψ (QuotientGroup.mk x))) = M₀.π (x : G) := by
  show Multiplicative.toAdd
    (piQuot₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ
      (ψ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (ψ (QuotientGroup.mk x)))))) = _
  rw [ofAdd_toAdd, ψ.symm_apply_apply, piQuot₂_mk, toAdd_ofAdd]

private theorem coord₂_theta_smul [(X₁.subgroupOf X₂).Normal]
    (hX₁ : X₁ = Z) (hXQ : X₂ ≤ Q) (hstable : PiImageStable M₀ X₂)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) (θ : K ≃+* K)
    (hθ : ∀ (c : K) (v w : ↥X₂), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (c : K) (u : Fin n → K) :
    coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ ψ (θ c • u) =
      c • coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ ψ u := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
    (ψ.symm (Multiplicative.ofAdd u) : ↥X₂ ⧸ X₁.subgroupOf X₂)
  have hu : u = Multiplicative.toAdd (ψ (QuotientGroup.mk x)) := by
    rw [hx, ψ.apply_symm_apply, toAdd_ofAdd]
  obtain ⟨w, hwX₂, hwQ, hwπ⟩ := (M₀.mem_img (S := X₂)).mp
    (hstable c (M₀.π (x : G)) (M₀.pi_mem_img (S := X₂) x.2 (hXQ x.2)))
  have hwψ := hθ c x ⟨w, hwX₂⟩ hwπ
  have hcoord : coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ ψ u = M₀.π (x : G) := by
    rw [hu, coord₂_mk]
  have hcoord' : coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hXQ ψ (θ c • u) = M₀.π w := by
    have hu' : θ c • u =
        Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨w, hwX₂⟩)) := by
      rw [hu, ← hwψ]
    rw [hu', coord₂_mk]
  rw [hcoord', hcoord, hwπ]

theorem B_vanishes_on_X₂_of_naturalRep {n : ℕ} (hn : 3 ≤ n) {X₁ X₂ N : Subgroup G}
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q)
    (nat2 : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁ N)
    (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀) :
    ∀ x ∈ X₂, ∀ y ∈ X₂, M₀.B (M₀.π x) (M₀.π y) = 0 := by
  obtain ⟨φ, hrange, -, hNorm, hN, ψ, hψ⟩ := nat2
  haveI := hN
  let F : (Fin n → K) →+ (Fin n → K) →+ K :=
    { toFun := fun u =>
        (M₀.B (coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ u)).toAddMonoidHom.comp
          (coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ)
      map_zero' := by
        ext v
        simp
      map_add' := by
        intro u w
        ext v
        simp [map_add] }
  have hinv : ∀ g : GL (Fin n) K, g ∈ StatedSL n K → ∀ u v : Fin n → K,
      F (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u)
        (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = F u v := by
    intro g hg u v
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hg)
    obtain ⟨T, hTπ, -, hTB⟩ := exists_isometry_of_mem_XbarPre hc hD s.2
    have hmk : ∀ u : Fin n → K,
        coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ
          (((φ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) =
        T (coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ u) := by
      intro u
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
        (ψ.symm (Multiplicative.ofAdd u) : ↥X₂ ⧸ X₁.subgroupOf X₂)
      have hu : u = Multiplicative.toAdd (ψ (QuotientGroup.mk x)) := by
        rw [hx, ψ.apply_symm_apply, toAdd_ofAdd]
      rw [hu, coord₂_mk (M₀ := M₀) hX₁ hX₂Q ψ x]
      have hmem : (s : G) * (x : G) * (s : G)⁻¹ ∈ X₂ :=
        (Subgroup.mem_normalizer_iff.mp (hNorm s.2) (x : G)).mp x.2
      have hsec := hψ s x ⟨(s : G) * (x : G) * (s : G)⁻¹, hmem⟩ rfl
      rw [← hsec, coord₂_mk (M₀ := M₀) hX₁ hX₂Q ψ ⟨_, hmem⟩]
      exact hTπ (x : G) (hX₂Q x.2)
    change M₀.B (coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ
        (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u))
      (coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ
        (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) =
      M₀.B (coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ u)
        (coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ v)
    rw [show (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      ((φ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) from by rw [hs]]
    rw [hmk, hmk]
    exact hTB _ _
  have hzero : ∀ u v : Fin n → K, F u v = 0 :=
    fun u v => biadd_eq_zero_of_SL hn F hinv u v
  intro x hx y hy
  have hxy : F (Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨x, hx⟩)))
      (Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨y, hy⟩))) =
      M₀.B (M₀.π x) (M₀.π y) := by
    change M₀.B (coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ
        (Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨x, hx⟩))))
      (coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ
        (Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨y, hy⟩)))) =
      M₀.B (M₀.π x) (M₀.π y)
    rw [coord₂_mk (M₀ := M₀) hX₁ hX₂Q ψ ⟨x, hx⟩,
      coord₂_mk (M₀ := M₀) hX₁ hX₂Q ψ ⟨y, hy⟩]
  rw [hzero] at hxy
  exact hxy.symm

private theorem commutatorElement_mul_right_of_class_two
    (hc : Ctx M Q Z B) {x a b : G} (hx : x ∈ Q) (ha : a ∈ Q) (hb : b ∈ Q) :
    ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
  have hQQ : ⁅Q,Q⁆ = Z := (hc.hyp.toHyp79.special).1
  have hbZ : ⁅x, b⁆ ∈ Z := by
    rw [← hQQ]
    exact Subgroup.commutator_mem_commutator hx hb
  have hZc : Z ≤ Subgroup.centralizer (Q : Set G) := by
    rw [hc.hyp.hZ, cen_eq]
    exact inf_le_right
  have hconj : a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
    have hcomm : a * ⁅x, b⁆ = ⁅x, b⁆ * a :=
      Subgroup.mem_centralizer_iff.mp (hZc hbZ) a ha
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  calc
    ⁅x, a * b⁆ = ⁅x, a⁆ * a * ⁅x, b⁆ * a⁻¹ := by
      rw [commutatorElement_mul_right_eq_mul_conj]
    _ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by group
    _ = ⁅x, a⁆ * ⁅x, b⁆ := by rw [hconj]

private theorem commutatorElement_inv_right_eq_inv
    (hc : Ctx M Q Z B) {x q : G} (hx : x ∈ Q) (hq : q ∈ Q) :
    ⁅x, q⁻¹⁆ = ⁅x, q⁆⁻¹ := by
  have hQQ : ⁅Q,Q⁆ = Z := (hc.hyp.toHyp79.special).1
  have hxqZ : ⁅x, q⁆ ∈ Z := by
    rw [← hQQ]
    exact Subgroup.commutator_mem_commutator hx hq
  have hZc : Z ≤ Subgroup.centralizer (Q : Set G) := by
    rw [hc.hyp.hZ, cen_eq]
    exact inf_le_right
  have hconj : q⁻¹ * ⁅x, q⁆⁻¹ * q = ⁅x, q⁆⁻¹ := by
    have hcomm : q⁻¹ * ⁅x, q⁆⁻¹ = ⁅x, q⁆⁻¹ * q⁻¹ := by
      have h : q * ⁅x, q⁆ = ⁅x, q⁆ * q :=
        Subgroup.mem_centralizer_iff.mp (hZc hxqZ) q hq
      calc
        q⁻¹ * ⁅x, q⁆⁻¹ = (⁅x, q⁆ * q)⁻¹ := by group
        _ = (q * ⁅x, q⁆)⁻¹ := by rw [h]
        _ = ⁅x, q⁆⁻¹ * q⁻¹ := by group
    calc
      q⁻¹ * ⁅x, q⁆⁻¹ * q = (⁅x, q⁆⁻¹ * q⁻¹) * q := by rw [hcomm]
      _ = ⁅x, q⁆⁻¹ := by group
  rw [commutatorElement_inv_right, ← commutatorElement_inv, hconj]

private theorem commutatorElement_conj_mul_right_of_class_two
    (hc : Ctx M Q Z B) {x c q : G} (hx : x ∈ Q) (hcQ : c ∈ Q) (hq : q ∈ Q) :
    ⁅x, q * c * q⁻¹⁆ = ⁅x, c⁆ := by
  haveI : IsMulCommutative ↥Z := hc.hyp.maxAb.prop.2.2
  have hmul₁ : ⁅x, q * c⁆ = ⁅x, q⁆ * ⁅x, c⁆ :=
    commutatorElement_mul_right_of_class_two hc hx hq hcQ
  have hmul₂ : ⁅x, (q * c) * q⁻¹⁆ = ⁅x, q * c⁆ * ⁅x, q⁻¹⁆ :=
    commutatorElement_mul_right_of_class_two hc hx (Q.mul_mem hq hcQ) (Q.inv_mem hq)
  have hqinv : ⁅x, q⁻¹⁆ = ⁅x, q⁆⁻¹ := commutatorElement_inv_right_eq_inv hc hx hq
  have hQQ : ⁅Q,Q⁆ = Z := (hc.hyp.toHyp79.special).1
  have hxqZ : ⁅x, q⁆ ∈ Z := by
    rw [← hQQ]
    exact Subgroup.commutator_mem_commutator hx hq
  have hxcZ : ⁅x, c⁆ ∈ Z := by
    rw [← hQQ]
    exact Subgroup.commutator_mem_commutator hx hcQ
  have hcomm : ⁅x, q⁆ * ⁅x, c⁆ = ⁅x, c⁆ * ⁅x, q⁆ := setLike_mul_comm hxqZ hxcZ
  calc
    ⁅x, q * c * q⁻¹⁆ = ⁅x, (q * c) * q⁻¹⁆ := rfl
    _ = ⁅x, q * c⁆ * ⁅x, q⁻¹⁆ := hmul₂
    _ = (⁅x, q⁆ * ⁅x, c⁆) * ⁅x, q⁆⁻¹ := by rw [hmul₁, hqinv]
    _ = ⁅x, c⁆ := by rw [hcomm]; group

private theorem commutator_commutator_eq_of_class_two
    (hc : Ctx M Q Z B) {x q s : G} (hx : x ∈ Q) (hq : q ∈ Q)
    (hs : s ∈ XbarPre M Q Z B) :
    ⁅x, ⁅s, q⁆⁆ = ⁅⁅s⁻¹, x⁆, q⁆ := by
  have hQQ : ⁅Q,Q⁆ = Z := (hc.hyp.toHyp79.special).1
  have hQQle : ⁅Q,Q⁆ ≤ Z := by rw [hQQ]
  have hsM : s ∈ M := XbarPre_le_M hc hs
  have hsNormQ : (s : G) ∈ Subgroup.normalizer (Q : Set G) :=
    hc.hyp.Q_normal.2 hsM
  have hsInvNormQ : s⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).inv_mem hsNormQ
  have hsqQ : ⁅s, q⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hsNormQ q).mp hq) (Q.inv_mem hq)
  have hsinvxQ : ⁅s⁻¹, x⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hsInvNormQ x).mp hx) (Q.inv_mem hx)
  have hinvq_sQ : ⁅q⁻¹, s⁆ ∈ Q := by
    rw [commutatorElement_inv_left]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hsqQ) hq
  have hxinvqQ : ⁅x⁻¹, q⁆ ∈ ⁅Q,Q⁆ :=
    Subgroup.commutator_mem_commutator (Q.inv_mem hx) hq
  set T₁ : G := ⁅x, ⁅q⁻¹, s⁆⁆ with hT₁
  set T₂ : G := ⁅q, ⁅s⁻¹, x⁆⁆ with hT₂
  set T₃ : G := ⁅s, ⁅x⁻¹, q⁆⁆ with hT₃
  have hT₁Z : T₁ ∈ Z := hQQle (Subgroup.commutator_mem_commutator hx hinvq_sQ)
  have hT₂Z : T₂ ∈ Z := hQQle (Subgroup.commutator_mem_commutator hq hsinvxQ)
  have hT₃Z : ⁅x⁻¹, q⁆ ∈ Z := hQQle hxinvqQ
  have hsZ : s ∈ Subgroup.centralizer (Z : Set G) := (XbarPre_le_H0 hc hs).2
  have hsZcomm : ∀ z ∈ Z, s * z * s⁻¹ = z := by
    intro z hz
    have h : s * z = z * s := (Subgroup.mem_centralizer_iff.mp hsZ z hz).symm
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hqZ : q ∈ Subgroup.centralizer (Z : Set G) := by
    have hZc : Z ≤ Subgroup.centralizer (Q : Set G) := by
      rw [hc.hyp.hZ, cen_eq]
      exact inf_le_right
    exact (Subgroup.le_centralizer_iff.mp hZc) hq
  have hqZcomm : ∀ z ∈ Z, q * z * q⁻¹ = z := by
    intro z hz
    have h : q * z = z * q := (Subgroup.mem_centralizer_iff.mp hqZ z hz).symm
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hT₃one : T₃ = 1 := by
    rw [hT₃]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hsZ _ hT₃Z).symm
  have hHW := conj_commutatorElement_right_commutatorElement_mul x q s
  have hAB : T₁ * T₂ = 1 := by
    have h := hHW
    rw [← hT₁, ← hT₂, ← hT₃] at h
    rw [hT₃one, mul_one] at h
    have h1 := hqZcomm T₁ hT₁Z
    have h2 := hsZcomm T₂ hT₂Z
    have h' : q * T₁ * q⁻¹ * s * T₂ * s⁻¹ = 1 := by
      simpa using h
    rw [h1] at h'
    rw [show T₁ * s * T₂ * s⁻¹ = T₁ * (s * T₂ * s⁻¹) by group] at h'
    rw [h2] at h'
    exact h'
  have hT₁T₂ : T₁ = T₂⁻¹ := by
    rw [eq_inv_of_mul_eq_one_right hAB, inv_inv]
  have hT₂inv : T₂⁻¹ = ⁅⁅s⁻¹, x⁆, q⁆ := by
    rw [hT₂, commutatorElement_inv]
  have hT₁rewrite : T₁ = ⁅x, ⁅s, q⁆⁆ := by
    rw [hT₁, commutatorElement_inv_left]
    simpa using commutatorElement_conj_mul_right_of_class_two hc hx hsqQ (Q.inv_mem hq)
  rw [← hT₁rewrite, hT₁T₂, hT₂inv]

private theorem exists_B_pairing_ne_zero {n : ℕ} (hn : 3 ≤ n)
    (hX₁ : X₁ = Z) (hX₂ : X₂ = Z ⊔ ⁅X₃, XbarPre M Q Z B⁆)
    (hX₃ : X₃ = X₂) (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆)
    (h₁₂ : X₁ ≤ X₂) (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄) (h₄Q : X₄ ≤ Q)
    (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (nat2 : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁
      (Q)) :
    ∃ x ∈ X₂, ∃ y ∈ X₄, M₀.B (M₀.π x) (M₀.π y) ≠ 0 := by
  have hX₂Q : X₂ ≤ Q := fun x hx => h₄Q (h₃₄ (h₂₃ hx))
  have hX₄Q : X₄ ≤ Q := h₄Q
  have hX₂ne : X₂ ≠ Z := by
    intro hEq
    have hcard := card_quotient_X₂_X₁ (K := K) (m := n) nat2
    have htop : X₁.subgroupOf X₂ = ⊤ := by
      rw [hEq, hX₁]
      exact Subgroup.subgroupOf_self Z
    have hq1 : Nat.card (↥X₂ ⧸ X₁.subgroupOf X₂) = 1 := by
      rw [htop]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
    rw [hq1] at hcard
    have hK2 : 1 < Nat.card K := Finite.one_lt_card
    have hpow : 1 < Nat.card K ^ n := one_lt_pow' hK2 (by omega)
    omega
  have hex : ∃ a ∈ X₂, ∃ s ∈ XbarPre M Q Z B, M₀.π ⁅a, s⁆ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hcommZ : ⁅X₂, XbarPre M Q Z B⁆ ≤ Z := by
      rw [Subgroup.commutator_le]
      intro a ha s hs
      have hsNormQ : (s : G) ∈ Subgroup.normalizer (Q : Set G) :=
        hc.hyp.Q_normal.2 (XbarPre_le_M hc hs)
      have hasQ : ⁅a, s⁆ ∈ Q := by
        rw [commutatorElement_def]
        have hsasQ : s * a * s⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hsNormQ a).mp (hX₂Q ha)
        rw [show a * s * a⁻¹ * s⁻¹ = a * (s * a * s⁻¹)⁻¹ by group]
        exact Q.mul_mem (hX₂Q ha) (Q.inv_mem hsasQ)
      exact (M₀.π_ker _ hasQ).mp (hcon a ha s hs)
    have hX₂Z : X₂ ≤ Z := by
      rw [hX₂, hX₃]
      exact sup_le le_rfl hcommZ
    exact hX₂ne (le_antisymm hX₂Z (by rw [← hX₁]; exact h₁₂))
  obtain ⟨a, haX₂, s, hs, hπas⟩ := hex
  have hsNormQ : (s : G) ∈ Subgroup.normalizer (Q : Set G) :=
    hc.hyp.Q_normal.2 (XbarPre_le_M hc hs)
  have hsInvNormQ : s⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).inv_mem hsNormQ
  have hasQ : ⁅a, s⁆ ∈ Q := by
    rw [commutatorElement_def]
    have hsasQ : s * a * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hsNormQ a).mp (hX₂Q haX₂)
    rw [show a * s * a⁻¹ * s⁻¹ = a * (s * a * s⁻¹)⁻¹ by group]
    exact Q.mul_mem (hX₂Q haX₂) (Q.inv_mem hsasQ)
  have hcQ : ⁅s⁻¹, a⁆ ∈ Q := by
    rw [commutatorElement_inv_left]
    simpa using (Subgroup.mem_normalizer_iff.mp hsInvNormQ ⁅a, s⁆).mp hasQ
  have hπc : M₀.π ⁅s⁻¹, a⁆ ≠ 0 := by
    intro h0
    have hcZ : ⁅s⁻¹, a⁆ ∈ Z := (M₀.π_ker _ hcQ).mp h0
    have hsZ : s * ⁅s⁻¹, a⁆ * s⁻¹ ∈ Z :=
      ((hc.hyp.Z_normal.2 (XbarPre_le_M hc hs)) ⁅s⁻¹, a⁆).mp hcZ
    have hconj : ⁅a, s⁆ = s * ⁅s⁻¹, a⁆ * s⁻¹ := by
      rw [commutatorElement_inv_left]
      group
    exact hπas ((M₀.π_ker _ hasQ).mpr (hconj ▸ hsZ))
  obtain ⟨q, hq, hqpair⟩ : ∃ q ∈ Q, M₀.B (M₀.π ⁅s⁻¹, a⁆) (M₀.π q) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hπc (M₀.nondeg _ fun f => by
      obtain ⟨q, hq, rfl⟩ := M₀.π_surj f
      exact hcon q hq)
  have hyX₄ : ⁅s, q⁆ ∈ X₄ := by
    rw [hX₄]
    refine Subgroup.mem_sup_right ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hs hq
  have hqyQ : ⁅s, q⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem
      ((Subgroup.mem_normalizer_iff.mp hsNormQ q).mp hq) (Q.inv_mem hq)
  refine ⟨a, haX₂, ⁅s, q⁆, hyX₄, ?_⟩
  have hident := commutator_commutator_eq_of_class_two hc (hX₂Q haX₂) hq hs
  have hB : M₀.B (M₀.π a) (M₀.π ⁅s, q⁆) =
      M₀.B (M₀.π ⁅s⁻¹, a⁆) (M₀.π q) := by
    calc
      M₀.B (M₀.π a) (M₀.π ⁅s, q⁆) = γ ⁅a, ⁅s, q⁆⁆ :=
        (M₀.comm_eq a (hX₂Q haX₂) ⁅s, q⁆ hqyQ).symm
      _ = γ ⁅⁅s⁻¹, a⁆, q⁆ := by rw [hident]
      _ = M₀.B (M₀.π ⁅s⁻¹, a⁆) (M₀.π q) :=
        M₀.comm_eq ⁅s⁻¹, a⁆ hcQ q hq
  rw [hB]
  exact hqpair

theorem B_pairing_kernel {n : ℕ} (hn : 3 ≤ n)
    {X₁ X₂ X₃ X₄ : Subgroup G}
    (hX₁ : X₁ = Z) (hX₂ : X₂ = Z ⊔ ⁅X₃, XbarPre M Q Z B⁆)
    (hX₃ : X₃ = X₂) (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆)
    (h₁₂ : X₁ ≤ X₂) (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄) (h₄Q : X₄ ≤ Q)
    (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (nat2 : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁
      (Q))
    (nat4 : NaturalDualRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₄ X₃
      (Q))
    {y : G} (hy : y ∈ X₄)
    (hpair : ∀ x ∈ X₂, M₀.B (M₀.π x) (M₀.π y) = 0) :
    y ∈ X₃ := by
  have hX₂Q : X₂ ≤ Q := fun x hx => h₄Q (h₃₄ (h₂₃ hx))
  have hX₃Q : X₃ ≤ Q := hX₃ ▸ hX₂Q
  have hX₄Q : X₄ ≤ Q := h₄Q
  have hZ₂ : Z ≤ X₂ := by rw [← hX₁]; exact h₁₂
  have hZ₄ : Z ≤ X₄ := hZ₂.trans (h₂₃.trans h₃₄)
  have hne := exists_B_pairing_ne_zero (n := n) hn hX₁ hX₂ hX₃ hX₄ h₁₂ h₂₃ h₃₄ h₄Q hc hD nat2
  obtain ⟨x₀, hx₀X₂, y₀, hy₀X₄, hBne⟩ := hne
  have hBvan : ∀ x ∈ X₂, ∀ y ∈ X₂, M₀.B (M₀.π x) (M₀.π y) = 0 :=
    B_vanishes_on_X₂_of_naturalRep hn hX₁ hX₂Q nat2 hc hD
  let φ₂ : ↥(XbarPre M Q Z B) →* GL (Fin n) K := Classical.choose nat2
  have hrange₂ : φ₂.range = StatedSL n K := (Classical.choose_spec nat2).1
  obtain ⟨hnorm₂, hN₂, ψ₂, hψ₂⟩ := (Classical.choose_spec nat2).2.2
  obtain ⟨φ₄, hrange₄, hker₄, hnorm₄, hN₄, ψ₄, hψ₄⟩ := nat4
  haveI := hN₂
  haveI := hN₄
  let S : AddSubgroup (Fin n → K) :=
    { carrier := { v | ∃ y : ↥X₄,
        Multiplicative.toAdd (ψ₄ (QuotientGroup.mk y)) = v ∧
          ∀ x ∈ X₂, M₀.B (M₀.π x) (M₀.π (y : G)) = 0 },
      add_mem' := by
        rintro v w ⟨y, hyv, hyp⟩ ⟨z, hzv, hzp⟩
        refine ⟨y * z, ?_, ?_⟩
        · rw [QuotientGroup.mk_mul, map_mul, toAdd_mul, hyv, hzv]
        · intro x hx
          rw [Subgroup.coe_mul, M₀.π_mul (y : G) (hX₄Q y.2) (z : G) (hX₄Q z.2),
            map_add, hyp x hx, hzp x hx, add_zero]
      zero_mem' := by
        refine ⟨1, ?_, ?_⟩
        · rw [QuotientGroup.mk_one, map_one, toAdd_one]
        · intro x hx
          rw [Subgroup.coe_one, Tim79.QuadModel.pi_one, map_zero]
      neg_mem' := by
        rintro v ⟨y, hyv, hyp⟩
        refine ⟨y⁻¹, ?_, ?_⟩
        · rw [QuotientGroup.mk_inv, map_inv, toAdd_inv, hyv]
        · intro x hx
          rw [Subgroup.coe_inv, M₀.pi_inv (x := (y : G)) (hX₄Q y.2), map_neg, hyp x hx, neg_zero] }
  let W : AddSubgroup ((Fin n → K) × (Fin n → K)) :=
    S.map (AddMonoidHom.inr (Fin n → K) (Fin n → K))
  have hWinv : ∀ g ∈ StatedSL n K, ∀ p ∈ W,
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ p.1,
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ p.2) ∈ W := by
    intro g hg p hp
    obtain ⟨v, hvS, rfl⟩ := AddSubgroup.mem_map.mp hp
    obtain ⟨y, hyv, hyp⟩ := hvS
    have hyX₄ : (y : G) ∈ X₄ := y.2
    obtain ⟨s, hsφ⟩ := MonoidHom.mem_range.mp (by rw [hrange₄]; exact hg)
    have hsH : (s : G) ∈ XbarPre M Q Z B := s.2
    have hy'X₄ : (s : G) * (y : G) * (s : G)⁻¹ ∈ X₄ :=
      (Subgroup.mem_normalizer_iff.mp (hnorm₄ hsH) (y : G)).mp hyX₄
    have hpair' : ∀ x ∈ X₂,
        M₀.B (M₀.π x) (M₀.π ((s : G) * (y : G) * (s : G)⁻¹)) = 0 := by
      intro x hx
      have hxsQ : (s : G)⁻¹ * x * (s : G) ∈ Q := by
        have hsNormQ : (s : G) ∈ Subgroup.normalizer (Q : Set G) :=
          hc.hyp.Q_normal.2 (XbarPre_le_M hc hsH)
        have hxQ : x ∈ Q := hX₂Q hx
        have h1 : (s : G)⁻¹ * x * (s : G) ∈ Q := by
          have h := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (Q : Set G)).inv_mem hsNormQ) x).mp hxQ
          simpa using h
        exact h1
      have hx'X₂ : (s : G)⁻¹ * x * (s : G) ∈ X₂ := by
        have hsNorm : (s : G) ∈ Subgroup.normalizer (X₂ : Set G) := hnorm₂ hsH
        have h := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (X₂ : Set G)).inv_mem hsNorm) x).mp hx
        simpa using h
      obtain ⟨T, hTπ, -, hTB⟩ := exists_isometry_of_mem_XbarPre hc hD hsH
      obtain ⟨T', hT'π, -, -⟩ :=
        exists_isometry_of_mem_XbarPre hc hD ((XbarPre M Q Z B).inv_mem hsH)
      have hT'π' : ∀ y ∈ Q, M₀.π ((s : G)⁻¹ * y * (s : G)) = T' (M₀.π y) := by
        intro y hy
        simpa using hT'π y hy
      have hTT' : T (T' (M₀.π x)) = M₀.π x := by
        rw [← hT'π' x (hX₂Q hx), ← hTπ _ hxsQ]
        rw [show (s : G) * ((s : G)⁻¹ * x * (s : G)) * (s : G)⁻¹ = x by group]
      calc
        M₀.B (M₀.π x) (M₀.π ((s : G) * (y : G) * (s : G)⁻¹))
            = M₀.B (M₀.π x) (T (M₀.π (y : G))) := by rw [hTπ (y : G) (hX₄Q y.2)]
        _ = M₀.B (T (T' (M₀.π x))) (T (M₀.π (y : G))) := by rw [hTT']
        _ = M₀.B (T' (M₀.π x)) (M₀.π (y : G)) := hTB (T' (M₀.π x)) (M₀.π (y : G))
        _ = M₀.B (M₀.π ((s : G)⁻¹ * x * (s : G))) (M₀.π (y : G)) := by
          rw [← hT'π' x (hX₂Q hx)]
        _ = 0 := hyp _ hx'X₂
    have hv' : Multiplicative.toAdd
        (ψ₄ (QuotientGroup.mk ⟨(s : G) * (y : G) * (s : G)⁻¹, hy'X₄⟩)) =
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ v := by
      rw [hψ₄ s y ⟨(s : G) * (y : G) * (s : G)⁻¹, hy'X₄⟩ rfl, hyv]
      rw [← hsφ]
    refine AddSubgroup.mem_map.mpr
      ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ v,
        ⟨⟨(s : G) * (y : G) * (s : G)⁻¹, hy'X₄⟩, hv', hpair'⟩, ?_⟩
    ext <;> simp [AddMonoidHom.inr]
  have hcl := natDual_invariant_addSubgroup (K := K) (n := n) hn W hWinv
  have hmap_prod : ∀ (H K' : AddSubgroup (Fin n → K)),
      (H.prod K').map (AddMonoidHom.snd (Fin n → K) (Fin n → K)) = K' := by
    intro H K'
    ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (AddSubgroup.mem_prod.mp hp).2
    · intro hv
      exact AddSubgroup.mem_map.mpr
        ⟨(0, v), AddSubgroup.mem_prod.mpr ⟨H.zero_mem, hv⟩, rfl⟩
  have hW_eq : W = (⊥ : AddSubgroup (Fin n → K)).prod S := by
    ext p
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact AddSubgroup.mem_prod.mpr ⟨(⊥ : AddSubgroup (Fin n → K)).zero_mem, hv⟩
    · intro hp
      obtain ⟨hp1, hp2⟩ := AddSubgroup.mem_prod.mp hp
      have hp1' : p.1 = 0 := by simpa using hp1
      exact AddSubgroup.mem_map.mpr
        ⟨p.2, hp2, by ext <;> simp [AddMonoidHom.inr, hp1']⟩
  have hmapW : W.map (AddMonoidHom.snd (Fin n → K) (Fin n → K)) = S := by
    rw [hW_eq, hmap_prod]
  have hmap_top : (⊤ : AddSubgroup ((Fin n → K) × (Fin n → K))).map
      (AddMonoidHom.snd (Fin n → K) (Fin n → K)) = ⊤ := by
    ext v
    exact ⟨fun _ => AddSubgroup.mem_top v,
      fun _ => AddSubgroup.mem_map.mpr ⟨(0, v), AddSubgroup.mem_top _, rfl⟩⟩
  have hS : S = ⊥ ∨ S = ⊤ := by
    rcases hcl with h | h | h | h
    · left
      rw [← hmapW, h, AddSubgroup.map_bot]
    · left
      rw [← hmapW, h, hmap_prod]
    · right
      rw [← hmapW, h, hmap_prod]
    · right
      rw [← hmapW, h, hmap_top]
  have hSneTop : S ≠ ⊤ := by
    intro htop
    have hv₀S : Multiplicative.toAdd (ψ₄ (QuotientGroup.mk ⟨y₀, hy₀X₄⟩)) ∈ S :=
      htop ▸ AddSubgroup.mem_top _
    obtain ⟨y', hy'v, hy'pair⟩ := hv₀S
    have hψeq : ψ₄ (QuotientGroup.mk y') = ψ₄ (QuotientGroup.mk ⟨y₀, hy₀X₄⟩) := by
      apply Multiplicative.toAdd.injective
      exact hy'v
    have hmk : QuotientGroup.mk y' = QuotientGroup.mk ⟨y₀, hy₀X₄⟩ :=
      ψ₄.injective hψeq
    have hmem : y'⁻¹ * ⟨y₀, hy₀X₄⟩ ∈ X₃.subgroupOf X₄ := by
      refine (QuotientGroup.eq_one_iff (N := X₃.subgroupOf X₄)
        (y'⁻¹ * ⟨y₀, hy₀X₄⟩)).mp ?_
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk, inv_mul_cancel]
    have hzX₃ : ((y'⁻¹ * ⟨y₀, hy₀X₄⟩ : ↥X₄) : G) ∈ X₃ :=
      Subgroup.mem_subgroupOf.mp hmem
    have hzX₂ : ((y'⁻¹ * ⟨y₀, hy₀X₄⟩ : ↥X₄) : G) ∈ X₂ := by
      rw [← hX₃]
      exact hzX₃
    have hy₀eq : (y₀ : G) = (y' : G) * ((y'⁻¹ * ⟨y₀, hy₀X₄⟩ : ↥X₄) : G) := by
      have h : ((y'⁻¹ * ⟨y₀, hy₀X₄⟩ : ↥X₄) : G) = (y' : G)⁻¹ * y₀ := rfl
      rw [h]
      group
    have hzero : M₀.B (M₀.π x₀) (M₀.π y₀) = 0 := by
      rw [hy₀eq]
      have hy'Q : (y' : G) ∈ Q := hX₄Q y'.2
      have hzQ : ((y'⁻¹ * ⟨y₀, hy₀X₄⟩ : ↥X₄) : G) ∈ Q := hX₃Q hzX₃
      rw [M₀.π_mul (y' : G) hy'Q _ hzQ, map_add, hy'pair x₀ hx₀X₂,
        hBvan x₀ hx₀X₂ _ hzX₂, add_zero]
    exact hBne hzero
  rcases hS with hbot | htop
  ·
    have hyS : Multiplicative.toAdd (ψ₄ (QuotientGroup.mk ⟨y, hy⟩)) ∈ S :=
      ⟨⟨y, hy⟩, rfl, hpair⟩
    rw [hbot] at hyS
    have hv0 : Multiplicative.toAdd (ψ₄ (QuotientGroup.mk ⟨y, hy⟩)) = 0 := by
      simpa using hyS
    have hψ1 : ψ₄ (QuotientGroup.mk ⟨y, hy⟩) = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hv0
    have hmk1 : QuotientGroup.mk (⟨y, hy⟩ : ↥X₄) = 1 :=
      ψ₄.injective (by simpa using hψ1)
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (N := X₃.subgroupOf X₄) (⟨y, hy⟩ : ↥X₄)).mp hmk1)
  · exact absurd htop hSneTop

private noncomputable def thetaVec (θ : K ≃+* K) (u : Fin n → K) : Fin n → K :=
  fun i => θ (u i)

private theorem thetaVec_smul (θ : K ≃+* K) (c : K) (u : Fin n → K) :
    thetaVec (K := K) θ (c • u) = θ c • thetaVec (K := K) θ u := by
  ext i
  simp [thetaVec]

private theorem thetaVec_add (θ : K ≃+* K) (u v : Fin n → K) :
    thetaVec (K := K) θ (u + v) = thetaVec (K := K) θ u + thetaVec (K := K) θ v := by
  ext i
  simp [thetaVec]

private theorem thetaVec_mulVec (θ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K)
    (u : Fin n → K) :
    thetaVec (K := K) θ (A *ᵥ u) = (A.map θ) *ᵥ thetaVec (K := K) θ u := by
  ext i
  simp [thetaVec, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, mul_comm]

private noncomputable def rieszVec (L : (Fin n → K) →ₗ[K] K) : Fin n → K :=
  fun i => L (Pi.single i 1)

private theorem rieszVec_spec (L : (Fin n → K) →ₗ[K] K) (u : Fin n → K) :
    L u = ∑ i, u i * rieszVec (K := K) L i := by
  have hu : u = ∑ i, u i • Pi.single i 1 := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    L u = L (∑ i, u i • Pi.single i 1) := by
      conv_lhs => rw [hu]
    _ = ∑ i, L (u i • Pi.single i 1) := by rw [map_sum]
    _ = ∑ i, u i * L (Pi.single i 1) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul, smul_eq_mul]
    _ = ∑ i, u i * rieszVec (K := K) L i := rfl

private theorem rieszVec_add (L M : (Fin n → K) →ₗ[K] K) :
    rieszVec (K := K) (L + M) = rieszVec (K := K) L + rieszVec (K := K) M := by
  ext i
  simp [rieszVec]

private theorem rieszVec_comp_mulVecLin (L : (Fin n → K) →ₗ[K] K)
    (A : Matrix (Fin n) (Fin n) K) :
    rieszVec (K := K) (L.comp (Matrix.mulVecLin A)) =
      Aᵀ *ᵥ rieszVec (K := K) L := by
  ext i
  rw [rieszVec, LinearMap.comp_apply, Matrix.mulVecLin_apply,
    rieszVec_spec (K := K) L (A *ᵥ Pi.single i 1)]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.transpose_apply]

private noncomputable def dualFun [(X₁.subgroupOf X₂).Normal]
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q) (hstable : PiImageStable M₀ X₂)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) (θ : K ≃+* K)
    (hθ : ∀ (c : K) (v w : ↥X₂), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (y : G) : (Fin n → K) →ₗ[K] K where
  toFun u := M₀.B (coord₂ (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q ψ (thetaVec (K := K) θ u))
    (M₀.π y)
  map_add' u v := by
    rw [thetaVec_add, map_add, map_add]
    rfl
  map_smul' c u := by
    rw [thetaVec_smul (K := K) θ c u,
      coord₂_theta_smul (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ c (thetaVec (K := K) θ u),
      map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp

private noncomputable def dualCoord [(X₁.subgroupOf X₂).Normal]
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q) (hstable : PiImageStable M₀ X₂)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) (θ : K ≃+* K)
    (hθ : ∀ (c : K) (v w : ↥X₂), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (y : G) : Fin n → K :=
  fun i => θ (rieszVec (K := K) (dualFun (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ y) i)

private theorem dualFun_mul [(X₁.subgroupOf X₂).Normal]
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q) (hstable : PiImageStable M₀ X₂)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) (θ : K ≃+* K)
    (hθ : ∀ (c : K) (v w : ↥X₂), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hX₄Q : X₄ ≤ Q) {y z : G} (hy : y ∈ X₄) (hz : z ∈ X₄) :
    dualFun (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q hstable ψ θ hθ (y * z) =
      dualFun (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q hstable ψ θ hθ y +
        dualFun (M₀ := M₀) (X₁ := X₁) hX₁ hX₂Q hstable ψ θ hθ z := by
  apply LinearMap.ext
  intro u
  change M₀.B (coord₂ (M₀ := M₀) hX₁ hX₂Q ψ (thetaVec (K := K) θ u))
      (M₀.π (y * z)) =
    M₀.B (coord₂ (M₀ := M₀) hX₁ hX₂Q ψ (thetaVec (K := K) θ u)) (M₀.π y) +
      M₀.B (coord₂ (M₀ := M₀) hX₁ hX₂Q ψ (thetaVec (K := K) θ u)) (M₀.π z)
  rw [M₀.π_mul y (hX₄Q hy) z (hX₄Q hz), map_add]

private theorem dualCoord_mul [(X₁.subgroupOf X₂).Normal]
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q) (hstable : PiImageStable M₀ X₂)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) (θ : K ≃+* K)
    (hθ : ∀ (c : K) (v w : ↥X₂), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hX₄Q : X₄ ≤ Q) {y z : G} (hy : y ∈ X₄) (hz : z ∈ X₄) :
    dualCoord (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ (y * z) =
      dualCoord (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ y +
        dualCoord (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ z := by
  funext i
  change θ (rieszVec (K := K) (dualFun (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ (y * z)) i) =
    θ (rieszVec (K := K) (dualFun (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ y) i) +
      θ (rieszVec (K := K) (dualFun (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ z) i)
  rw [dualFun_mul (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ hX₄Q hy hz, rieszVec_add]
  simp [map_add]

private theorem dualCoord_one [(X₁.subgroupOf X₂).Normal]
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q) (hstable : PiImageStable M₀ X₂)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) (θ : K ≃+* K)
    (hθ : ∀ (c : K) (v w : ↥X₂), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    dualCoord (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ 1 = 0 := by
  funext i
  change θ (rieszVec (K := K) (dualFun (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ 1) i) = 0
  simp [dualFun, rieszVec, Tim79.QuadModel.pi_one]

private theorem dualCoord_eq_zero_of_mem_X₂ [(X₁.subgroupOf X₂).Normal]
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q) (hstable : PiImageStable M₀ X₂)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) (θ : K ≃+* K)
    (hθ : ∀ (c : K) (v w : ↥X₂), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hBvan : ∀ x ∈ X₂, ∀ y ∈ X₂, M₀.B (M₀.π x) (M₀.π y) = 0)
    {y : G} (hy : y ∈ X₂) :
    dualCoord (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ y = 0 := by
  have hcoord : ∀ u : Fin n → K,
      ∃ x ∈ X₂, coord₂ (M₀ := M₀) hX₁ hX₂Q ψ (thetaVec (K := K) θ u) = M₀.π x := by
    intro u
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
      (ψ.symm (Multiplicative.ofAdd (thetaVec (K := K) θ u)) :
        ↥X₂ ⧸ X₁.subgroupOf X₂)
    refine ⟨x, x.2, ?_⟩
    have hu : thetaVec (K := K) θ u = Multiplicative.toAdd (ψ (QuotientGroup.mk x)) := by
      rw [hx, ψ.apply_symm_apply, toAdd_ofAdd]
    rw [hu, coord₂_mk]
  funext i
  have hz : M₀.B (coord₂ (M₀ := M₀) hX₁ hX₂Q ψ
      (thetaVec (K := K) θ (Pi.single i 1))) (M₀.π y) = 0 := by
    obtain ⟨x, hxX₂, hxπ⟩ := hcoord (Pi.single i 1)
    rw [hxπ]
    exact hBvan x hxX₂ y hy
  change θ (rieszVec (K := K) (dualFun (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ y) i) = 0
  simp only [rieszVec, dualFun, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hz, map_zero]

private noncomputable def dualHom [(X₁.subgroupOf X₂).Normal]
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q) (hstable : PiImageStable M₀ X₂)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) (θ : K ≃+* K)
    (hθ : ∀ (c : K) (v w : ↥X₂), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hX₄Q : X₄ ≤ Q) : ↥X₄ →* Multiplicative (Fin n → K) where
  toFun y := Multiplicative.ofAdd
    (dualCoord (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ (y : G))
  map_one' := by
    rw [Subgroup.coe_one, dualCoord_one, ofAdd_zero]
  map_mul' y z := by
    rw [Subgroup.coe_mul, dualCoord_mul (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ hX₄Q y.2 z.2,
      ofAdd_add]

private noncomputable def dualQuot [(X₁.subgroupOf X₂).Normal]
    (hX₁ : X₁ = Z) (hX₂Q : X₂ ≤ Q) (hstable : PiImageStable M₀ X₂)
    (ψ : ↥X₂ ⧸ X₁.subgroupOf X₂ ≃* Multiplicative (Fin n → K)) (θ : K ≃+* K)
    (hθ : ∀ (c : K) (v w : ↥X₂), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hX₄Q : X₄ ≤ Q)
    (hBvan : ∀ x ∈ X₂, ∀ y ∈ X₂, M₀.B (M₀.π x) (M₀.π y) = 0)
    [(X₂.subgroupOf X₄).Normal] :
    (↥X₄ ⧸ X₂.subgroupOf X₄) →* Multiplicative (Fin n → K) :=
  QuotientGroup.lift (X₂.subgroupOf X₄)
    (dualHom (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ hX₄Q) (by
      intro z hz
      rw [MonoidHom.mem_ker]
      have hzX₂ : (z : G) ∈ X₂ := Subgroup.mem_subgroupOf.mp hz
      show Multiplicative.ofAdd
        (dualCoord (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ (z : G)) = 1
      rw [dualCoord_eq_zero_of_mem_X₂ (M₀ := M₀) hX₁ hX₂Q hstable ψ θ hθ hBvan hzX₂,
        ofAdd_zero])

theorem sectionAct_dual_on_quotient {n : ℕ} (hn : 3 ≤ n)
    {X₁ X₂ X₃ X₄ : Subgroup G}
    (hX₁ : X₁ = Z) (hX₂ : X₂ = Z ⊔ ⁅X₃, XbarPre M Q Z B⁆)
    (hX₃ : X₃ = X₂) (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆)
    (h₁₂ : X₁ ≤ X₂) (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄) (h₄Q : X₄ ≤ Q)
    (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (nat2 : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁
      (Q))
    (nat4 : NaturalDualRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₄ X₃
      (Q))
    (hstable : PiImageStable M₀ X₂) :
    SectionAct K (XbarPre M Q Z B) X₄ X₂ (Classical.choose nat2)
      (fun g => (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ) := by
  subst X₁
  subst X₃
  have nat2c := nat2
  have nat4c := nat4
  have hX₂Q : X₂ ≤ Q := fun x hx => h₄Q (h₃₄ (h₂₃ hx))
  have hBvan : ∀ x ∈ X₂, ∀ y ∈ X₂, M₀.B (M₀.π x) (M₀.π y) = 0 :=
    B_vanishes_on_X₂_of_naturalRep hn rfl hX₂Q nat2 hc hD
  let φ₂ : ↥(XbarPre M Q Z B) →* GL (Fin n) K := Classical.choose nat2
  have hrange₂ : φ₂.range = StatedSL n K := (Classical.choose_spec nat2).1
  obtain ⟨hnorm₂, hN₂, ψ₂, hψ₂⟩ := (Classical.choose_spec nat2).2.2
  obtain ⟨φ₄, hrange₄, hker₄, hnorm₄, hN₄, ψ₄, hψ₄⟩ := nat4
  haveI := hN₂
  haveI := hN₄
  have hlin : ∀ r ∈ XbarPre M Q Z B, ∃ T : M₀.E →ₗ[K] M₀.E,
      ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x) := by
    intro r hr
    obtain ⟨T, hT, -, -⟩ := hD.linear_of_centralizes (XbarPre_le_M hc hr) (by
      intro z hz
      have h := Subgroup.mem_centralizer_iff.mp (XbarPre_le_H0 hc hr).2 z hz
      rw [← h]; group)
    exact ⟨T, hT⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_natural (K' := K) (Q := Q) (V := X₂) (Z := Z)
    (R := XbarPre M Q Z B) (X := StatedSL n K) (γ := γ) rfl M₀ hX₂Q
    (addCommutantScalar_statedSL (by omega)) hstable hlin φ₂ hrange₂ hnorm₂ ψ₂ hψ₂
  let ψd : (↥X₄ ⧸ X₂.subgroupOf X₄) →* Multiplicative (Fin n → K) :=
    dualQuot (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ h₄Q hBvan
  have hker : ∀ y : ↥X₄, ψd (QuotientGroup.mk y) = 1 → y ∈ X₂.subgroupOf X₄ := by
    intro y hy1
    have hcoord : dualCoord (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (y : G) = 0 := by
      have h := congrArg Multiplicative.toAdd hy1
      simpa [ψd, dualQuot, dualHom] using h
    have hriesz : rieszVec (K := K)
        (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (y : G)) = 0 := by
      funext i
      have hi := congrFun hcoord i
      change θ (rieszVec (K := K)
        (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (y : G)) i) = 0 at hi
      exact θ.injective (by simpa using hi)
    have hL0 : dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (y : G) = 0 := by
      apply LinearMap.ext
      intro u
      rw [rieszVec_spec, hriesz]
      simp
    have hpair : ∀ x ∈ X₂, M₀.B (M₀.π x) (M₀.π (y : G)) = 0 := by
      intro x hx
      obtain ⟨u, hu⟩ : ∃ u : Fin n → K,
          coord₂ (M₀ := M₀) rfl hX₂Q ψ₂ (thetaVec (K := K) θ u) = M₀.π x := by
        refine ⟨thetaVec (K := K) θ.symm
          (Multiplicative.toAdd (ψ₂ (QuotientGroup.mk ⟨x, hx⟩))), ?_⟩
        have h : thetaVec (K := K) θ (thetaVec (K := K) θ.symm
            (Multiplicative.toAdd (ψ₂ (QuotientGroup.mk ⟨x, hx⟩)))) =
            Multiplicative.toAdd (ψ₂ (QuotientGroup.mk ⟨x, hx⟩)) := by
          ext i
          simp [thetaVec]
        rw [h, coord₂_mk]
      rw [← hu]
      exact LinearMap.congr_fun hL0 u
    refine Subgroup.mem_subgroupOf.mpr ?_
    exact B_pairing_kernel hn rfl hX₂ rfl hX₄ h₁₂ h₂₃ h₃₄ h₄Q hc hD nat2c nat4c y.2 hpair
  have hinj : Function.Injective ψd := by
    intro a b hab
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective b
    have h1 : ψd (QuotientGroup.mk (y⁻¹ * z)) = 1 := by
      rw [QuotientGroup.mk_mul, map_mul, QuotientGroup.mk_inv, map_inv, hab,
        inv_mul_cancel]
    have hmem := hker (y⁻¹ * z) h1
    have hmem' : ((y⁻¹ * z : ↥X₄) : G) ∈ X₂ := Subgroup.mem_subgroupOf.mp hmem
    have hz1 : QuotientGroup.mk (y⁻¹ * z) = (1 : ↥X₄ ⧸ X₂.subgroupOf X₄) :=
      (QuotientGroup.eq_one_iff (N := X₂.subgroupOf X₄) (y⁻¹ * z)).mpr hmem
    have h2 : ((QuotientGroup.mk y : ↥X₄ ⧸ X₂.subgroupOf X₄))⁻¹ *
        (QuotientGroup.mk z : ↥X₄ ⧸ X₂.subgroupOf X₄) = 1 := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      exact hz1
    calc
      QuotientGroup.mk y = QuotientGroup.mk y *
          ((QuotientGroup.mk y)⁻¹ * QuotientGroup.mk z) := by
        rw [h2, mul_one]
      _ = QuotientGroup.mk z := by group
  haveI : Finite (↥X₄ ⧸ X₂.subgroupOf X₄) :=
    Finite.of_surjective (QuotientGroup.mk' (X₂.subgroupOf X₄))
      (QuotientGroup.mk'_surjective (X₂.subgroupOf X₄))
  haveI : Finite (Multiplicative (Fin n → K)) := by infer_instance
  haveI : Fintype (↥X₄ ⧸ X₂.subgroupOf X₄) := Fintype.ofFinite _
  haveI : Fintype (Multiplicative (Fin n → K)) := Fintype.ofFinite _
  have hcarddom : Nat.card (↥X₄ ⧸ X₂.subgroupOf X₄) = Nat.card K ^ n := by
    exact card_quotient_of_naturalDualRep (K := K) (m := n) nat4c
  have hcardcod : Nat.card (Multiplicative (Fin n → K)) = Nat.card K ^ n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]
  have hcard : Fintype.card (↥X₄ ⧸ X₂.subgroupOf X₄) =
      Fintype.card (Multiplicative (Fin n → K)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcarddom, hcardcod]
  have hsurj : Function.Surjective ψd :=
    Function.Injective.surjective_of_finite (Fintype.equivOfCardEq hcard) hinj
  let ψe : (↥X₄ ⧸ X₂.subgroupOf X₄) ≃* Multiplicative (Fin n → K) :=
    MulEquiv.ofBijective ψd ⟨hinj, hsurj⟩
  refine ⟨hnorm₄, ⟨inferInstance, ψe, ?_⟩⟩
  intro s v w hw
  set A : GL (Fin n) K := φ₂ s with hA
  set Ainv : Matrix (Fin n) (Fin n) K :=
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAinv
  set Bmat : Matrix (Fin n) (Fin n) K := Ainv.map θ.symm with hBmat
  obtain ⟨T, hTπ, -, hTB⟩ := exists_isometry_of_mem_XbarPre hc hD s.2
  have hTcoord : ∀ z : Fin n → K,
      T (coord₂ (M₀ := M₀) rfl hX₂Q ψ₂ z) =
        coord₂ (M₀ := M₀) rfl hX₂Q ψ₂ (A *ᵥ z) := by
    intro z
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
      (ψ₂.symm (Multiplicative.ofAdd z) : ↥X₂ ⧸ Z.subgroupOf X₂)
    have hz : z = Multiplicative.toAdd (ψ₂ (QuotientGroup.mk x)) := by
      rw [hx, ψ₂.apply_symm_apply, toAdd_ofAdd]
    have hmem : (s : G) * (x : G) * (s : G)⁻¹ ∈ X₂ :=
      (Subgroup.mem_normalizer_iff.mp (hnorm₂ s.2) (x : G)).mp x.2
    have hψ := hψ₂ s x ⟨(s : G) * (x : G) * (s : G)⁻¹, hmem⟩ rfl
    rw [hz, coord₂_mk, ← hTπ (x : G) (hX₂Q x.2), ← hψ, coord₂_mk]
  have hTcoord_symm : ∀ z : Fin n → K,
      T.symm (coord₂ (M₀ := M₀) rfl hX₂Q ψ₂ z) =
        coord₂ (M₀ := M₀) rfl hX₂Q ψ₂ (A⁻¹ *ᵥ z) := by
    intro z
    apply T.injective
    have hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv A, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [LinearEquiv.apply_symm_apply, hTcoord, Matrix.mulVec_mulVec, hAA,
      Matrix.one_mulVec]
  have hdualFun : dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (w : G) =
      (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (v : G)).comp
        (Matrix.mulVecLin Bmat) := by
    apply LinearMap.ext
    intro u
    change M₀.B (coord₂ (M₀ := M₀) rfl hX₂Q ψ₂ (thetaVec (K := K) θ u))
        (M₀.π (w : G)) =
      M₀.B (coord₂ (M₀ := M₀) rfl hX₂Q ψ₂ (thetaVec (K := K) θ (Bmat *ᵥ u)))
        (M₀.π (v : G))
    rw [hw, hTπ (v : G) (h₄Q v.2)]
    have htheta : ((((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹) *ᵥ
        thetaVec (K := K) θ u = thetaVec (K := K) θ (Bmat *ᵥ u) := by
      rw [← Matrix.GeneralLinearGroup.coe_inv A, thetaVec_mulVec]
      congr 1
      ext i j
      simp [Bmat, Ainv, Matrix.map_apply]
    calc
      M₀.B (coord₂ (M₀ := M₀) rfl hX₂Q ψ₂ (thetaVec (K := K) θ u))
          (T (M₀.π (v : G))) =
          M₀.B (T (T.symm (coord₂ (M₀ := M₀) rfl hX₂Q ψ₂
            (thetaVec (K := K) θ u)))) (T (M₀.π (v : G))) := by
        rw [LinearEquiv.apply_symm_apply]
      _ = M₀.B (T.symm (coord₂ (M₀ := M₀) rfl hX₂Q ψ₂
            (thetaVec (K := K) θ u))) (M₀.π (v : G)) :=
        hTB _ _
      _ = M₀.B (coord₂ (M₀ := M₀) rfl hX₂Q ψ₂ (A⁻¹ *ᵥ thetaVec (K := K) θ u))
            (M₀.π (v : G)) := by
        rw [hTcoord_symm]
      _ = M₀.B (coord₂ (M₀ := M₀) rfl hX₂Q ψ₂
            (thetaVec (K := K) θ (Bmat *ᵥ u))) (M₀.π (v : G)) := by
        rw [htheta]
  have hriesz : rieszVec (K := K)
      (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (w : G)) =
      Bmatᵀ *ᵥ rieszVec (K := K)
        (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (v : G)) := by
    rw [hdualFun, rieszVec_comp_mulVecLin]
  have hcoord : dualCoord (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (w : G) =
      Ainvᵀ *ᵥ dualCoord (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (v : G) := by
    funext i
    change θ (rieszVec (K := K)
      (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (w : G)) i) =
      (Ainvᵀ *ᵥ fun i => θ (rieszVec (K := K)
        (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (v : G)) i)) i
    rw [hriesz]
    have htheta : thetaVec (K := K) θ
        (Bmatᵀ *ᵥ rieszVec (K := K)
          (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (v : G))) =
        Ainvᵀ *ᵥ thetaVec (K := K) θ (rieszVec (K := K)
          (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (v : G))) := by
      rw [thetaVec_mulVec]
      congr 1
      ext j k
      simp [Bmat, Ainv, Matrix.map_apply, Matrix.transpose_apply]
    change θ ((Bmatᵀ *ᵥ rieszVec (K := K)
      (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (v : G))) i) =
      (Ainvᵀ *ᵥ thetaVec (K := K) θ (rieszVec (K := K)
        (dualFun (M₀ := M₀) rfl hX₂Q hstable ψ₂ θ hθ (v : G)))) i
    exact congrFun htheta i
  have hψe : Multiplicative.toAdd (ψe (QuotientGroup.mk w)) =
      (((φ₂ s : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ
        Multiplicative.toAdd (ψe (QuotientGroup.mk v)) := by
    simpa [ψe, ψd, dualQuot, dualHom, hA, hAinv] using hcoord
  simpa using hψe

theorem caseVICore_of_chain_with_complement {n : ℕ}
    {X₁ X₂ X₃ X₄ W : Subgroup G}
    (hK : Nat.card K = Nat.card Z)
    (hX₁ : X₁ = Z)
    (h₁₂ : X₁ ≤ X₂) (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄) (h₄Q : X₄ ≤ Q)
    (hZW : Z ≤ W) (hWQ : W ≤ Q)
    (hinf : W ⊓ X₂ = Z) (hsup : W ⊔ X₂ = Q)
    (nat2 : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁
      (Q))
    (hactW : SectionAct K (XbarPre M Q Z B) W Z (Classical.choose nat2)
      (fun g => (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ))
    (hswap : ∃ x ∈ M, conjSubgroup x X₂ = W) :
    CaseVICore M Q Z (XbarPre M Q Z B) n := by
  have hX₂Q : X₂ ≤ Q := fun x hx => h₄Q (h₃₄ (h₂₃ hx))
  have hZV₁ : Z ≤ X₂ := by rw [← hX₁]; exact h₁₂
  have hrange : (Classical.choose nat2).range = StatedSL n K :=
    (Classical.choose_spec nat2).1
  have hker : (Classical.choose nat2).ker = Q.subgroupOf (XbarPre M Q Z B) :=
    (Classical.choose_spec nat2).2.1
  have hact₁ : SectionAct K (XbarPre M Q Z B) X₂ Z (Classical.choose nat2)
      (fun g => (g : Matrix (Fin n) (Fin n) K)) := by
    simpa [hX₁] using (Classical.choose_spec nat2).2.2
  exact caseVICore_of_data (S := XbarPre M Q Z B) hK hrange hker hZV₁ hX₂Q
    hZW hWQ (by rw [inf_comm]; exact hinf) (by rw [sup_comm]; exact hsup)
    hact₁ hactW hswap

end CFSG.RankThree.GF2n.Stroth80

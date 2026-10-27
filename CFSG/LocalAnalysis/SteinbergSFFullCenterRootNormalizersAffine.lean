module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterRootNormalizersOrbit

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenter

open Subgroup GomiFusion RootAxisTwoCore
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Act

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V]

structure ActHyp (ψ : G → V) (t : G) (A U H : Subgroup G) : Prop where
  U_le : U ≤ A
  add : ∀ a ∈ A, ∀ b ∈ A, ψ (a * b) = ψ a + ψ b
  ker : ∀ a ∈ A, ψ a = 0 ↔ a ∈ U
  surj : ∀ v : V, ∃ a ∈ A, ψ a = v
  conj_A : ∀ g ∈ H, ∀ a ∈ A, g * a * g⁻¹ ∈ A
  conj_U : ∀ g ∈ H, ∀ u ∈ U, g * u * g⁻¹ ∈ U
  conj_t : ∀ g ∈ H, t⁻¹ * (g * t * g⁻¹) ∈ A

namespace ActHyp

variable {ψ : G → V} {t : G} {A U H : Subgroup G}

theorem psi_one (hA : ActHyp ψ t A U H) : ψ 1 = 0 :=
  (hA.ker 1 (one_mem A)).mpr (one_mem U)

theorem psi_inv (hA : ActHyp ψ t A U H) {a : G} (ha : a ∈ A) : ψ a⁻¹ = -ψ a := by
  have h1 := hA.add a ha a⁻¹ (inv_mem ha)
  rw [mul_inv_cancel, hA.psi_one] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

theorem psi_eq_iff (hA : ActHyp ψ t A U H) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    ψ a = ψ b ↔ a⁻¹ * b ∈ U := by
  rw [← hA.ker _ (mul_mem (inv_mem ha) hb), hA.add _ (inv_mem ha) _ hb, hA.psi_inv ha,
    neg_add_eq_zero]

theorem psi_mul_U (hA : ActHyp ψ t A U H) {x y : G} (hx : x ∈ A) (hy : y ∈ U) :
    ψ (x * y) = ψ x := by
  rw [hA.add x hx y (hA.U_le hy), (hA.ker y (hA.U_le hy)).mpr hy, add_zero]

@[expose] noncomputable def sec (hA : ActHyp ψ t A U H) (v : V) : G :=
  Classical.choose (hA.surj v)

theorem sec_mem (hA : ActHyp ψ t A U H) (v : V) : hA.sec v ∈ A :=
  (Classical.choose_spec (hA.surj v)).1

theorem psi_sec (hA : ActHyp ψ t A U H) (v : V) : ψ (hA.sec v) = v :=
  (Classical.choose_spec (hA.surj v)).2

theorem inv_mul_sec_mem (hA : ActHyp ψ t A U H) {a : G} (ha : a ∈ A) :
    a⁻¹ * hA.sec (ψ a) ∈ U :=
  (hA.psi_eq_iff ha (hA.sec_mem _)).mp (hA.psi_sec _).symm

@[expose] noncomputable def linFun (hA : ActHyp ψ t A U H) (g : G) (v : V) : V :=
  ψ (g * hA.sec v * g⁻¹)

theorem linFun_psi (hA : ActHyp ψ t A U H) {g : G} (hg : g ∈ H) {a : G} (ha : a ∈ A) :
    hA.linFun g (ψ a) = ψ (g * a * g⁻¹) := by
  have e : g * hA.sec (ψ a) * g⁻¹ = (g * a * g⁻¹) * (g * (a⁻¹ * hA.sec (ψ a)) * g⁻¹) := by group
  rw [linFun, e, hA.psi_mul_U (hA.conj_A g hg a ha) (hA.conj_U g hg _ (hA.inv_mul_sec_mem ha))]

theorem linFun_mul (hA : ActHyp ψ t A U H) {g g' : G} (hg : g ∈ H) (hg' : g' ∈ H) (v : V) :
    hA.linFun (g * g') v = hA.linFun g (hA.linFun g' v) := by
  obtain ⟨a, ha, rfl⟩ := hA.surj v
  rw [hA.linFun_psi (mul_mem hg hg') ha, hA.linFun_psi hg' ha,
    hA.linFun_psi hg (hA.conj_A g' hg' a ha)]
  congr 1
  group

theorem linFun_one (hA : ActHyp ψ t A U H) (v : V) : hA.linFun 1 v = v := by
  obtain ⟨a, ha, rfl⟩ := hA.surj v
  rw [hA.linFun_psi (one_mem H) ha]
  congr 1
  group

theorem linFun_add (hA : ActHyp ψ t A U H) {g : G} (hg : g ∈ H) (v w : V) :
    hA.linFun g (v + w) = hA.linFun g v + hA.linFun g w := by
  obtain ⟨a, ha, rfl⟩ := hA.surj v
  obtain ⟨b, hb, rfl⟩ := hA.surj w
  rw [← hA.add a ha b hb, hA.linFun_psi hg (mul_mem ha hb), hA.linFun_psi hg ha,
    hA.linFun_psi hg hb, ← hA.add _ (hA.conj_A g hg a ha) _ (hA.conj_A g hg b hb)]
  congr 1
  group

@[expose] noncomputable def lin (hA : ActHyp ψ t A U H) : H →* Equiv.Perm V where
  toFun g :=
    { toFun := hA.linFun g
      invFun := hA.linFun (g : G)⁻¹
      left_inv := fun v => by
        rw [← hA.linFun_mul (inv_mem g.2) g.2, inv_mul_cancel, hA.linFun_one]
      right_inv := fun v => by
        rw [← hA.linFun_mul g.2 (inv_mem g.2), mul_inv_cancel, hA.linFun_one] }
  map_one' := Equiv.ext fun v => hA.linFun_one v
  map_mul' g g' := Equiv.ext fun v => hA.linFun_mul g.2 g'.2 v

theorem lin_psi (hA : ActHyp ψ t A U H) (g : H) {a : G} (ha : a ∈ A) :
    hA.lin g (ψ a) = ψ ((g : G) * a * (g : G)⁻¹) :=
  hA.linFun_psi g.2 ha

theorem lin_add (hA : ActHyp ψ t A U H) (g : H) (v w : V) :
    hA.lin g (v + w) = hA.lin g v + hA.lin g w :=
  hA.linFun_add g.2 v w

@[expose] noncomputable def linAdd (hA : ActHyp ψ t A U H) (g : H) : V ≃+ V :=
  { hA.lin g with map_add' := hA.lin_add g }

theorem lin_eq_one_iff (hA : ActHyp ψ t A U H) (g : H) :
    hA.lin g = 1 ↔ ∀ a ∈ A, ψ ((g : G) * a * (g : G)⁻¹) = ψ a := by
  constructor
  · intro h a ha
    rw [← hA.lin_psi g ha, h]
    rfl
  · intro h
    refine Equiv.ext fun v => ?_
    obtain ⟨a, ha, rfl⟩ := hA.surj v
    rw [hA.lin_psi g ha, h a ha]
    rfl

theorem mem_A_aff (hA : ActHyp ψ t A U H) {g : G} (hg : g ∈ H) {a : G} (ha : a ∈ A) :
    t⁻¹ * (g * (t * a) * g⁻¹) ∈ A := by
  have e : t⁻¹ * (g * (t * a) * g⁻¹) = (t⁻¹ * (g * t * g⁻¹)) * (g * a * g⁻¹) := by group
  rw [e]
  exact mul_mem (hA.conj_t g hg) (hA.conj_A g hg a ha)

@[expose] noncomputable def affFun (hA : ActHyp ψ t A U H) (g : G) (v : V) : V :=
  ψ (t⁻¹ * (g * (t * hA.sec v) * g⁻¹))

theorem affFun_psi (hA : ActHyp ψ t A U H) {g : G} (hg : g ∈ H) {a : G} (ha : a ∈ A) :
    hA.affFun g (ψ a) = ψ (t⁻¹ * (g * (t * a) * g⁻¹)) := by
  have e : t⁻¹ * (g * (t * hA.sec (ψ a)) * g⁻¹) =
      (t⁻¹ * (g * (t * a) * g⁻¹)) * (g * (a⁻¹ * hA.sec (ψ a)) * g⁻¹) := by group
  rw [affFun, e, hA.psi_mul_U (hA.mem_A_aff hg ha) (hA.conj_U g hg _ (hA.inv_mul_sec_mem ha))]

theorem affFun_eq (hA : ActHyp ψ t A U H) {g : G} (hg : g ∈ H) (v : V) :
    hA.affFun g v = hA.linFun g v + ψ (t⁻¹ * (g * t * g⁻¹)) := by
  obtain ⟨a, ha, rfl⟩ := hA.surj v
  rw [hA.affFun_psi hg ha, hA.linFun_psi hg ha, add_comm,
    ← hA.add _ (hA.conj_t g hg) _ (hA.conj_A g hg a ha)]
  congr 1
  group

theorem affFun_mul (hA : ActHyp ψ t A U H) {g g' : G} (hg : g ∈ H) (hg' : g' ∈ H) (v : V) :
    hA.affFun (g * g') v = hA.affFun g (hA.affFun g' v) := by
  obtain ⟨a, ha, rfl⟩ := hA.surj v
  rw [hA.affFun_psi (mul_mem hg hg') ha, hA.affFun_psi hg' ha,
    hA.affFun_psi hg (hA.mem_A_aff hg' ha)]
  congr 1
  group

theorem affFun_one (hA : ActHyp ψ t A U H) (v : V) : hA.affFun 1 v = v := by
  obtain ⟨a, ha, rfl⟩ := hA.surj v
  rw [hA.affFun_psi (one_mem H) ha]
  congr 1
  group

@[expose] noncomputable def aff (hA : ActHyp ψ t A U H) : H →* Equiv.Perm V where
  toFun g :=
    { toFun := hA.affFun g
      invFun := hA.affFun (g : G)⁻¹
      left_inv := fun v => by
        rw [← hA.affFun_mul (inv_mem g.2) g.2, inv_mul_cancel, hA.affFun_one]
      right_inv := fun v => by
        rw [← hA.affFun_mul g.2 (inv_mem g.2), mul_inv_cancel, hA.affFun_one] }
  map_one' := Equiv.ext fun v => hA.affFun_one v
  map_mul' g g' := Equiv.ext fun v => hA.affFun_mul g.2 g'.2 v

theorem aff_psi (hA : ActHyp ψ t A U H) (g : H) {a : G} (ha : a ∈ A) :
    hA.aff g (ψ a) = ψ (t⁻¹ * ((g : G) * (t * a) * (g : G)⁻¹)) :=
  hA.affFun_psi g.2 ha

theorem aff_eq (hA : ActHyp ψ t A U H) (g : H) (v : V) :
    hA.aff g v = hA.lin g v + ψ (t⁻¹ * ((g : G) * t * (g : G)⁻¹)) :=
  hA.affFun_eq g.2 v

theorem aff_zero (hA : ActHyp ψ t A U H) (g : H) :
    hA.aff g 0 = ψ (t⁻¹ * ((g : G) * t * (g : G)⁻¹)) := by
  rw [← hA.psi_one, hA.aff_psi g (one_mem A), mul_one]

theorem lin_zero (hA : ActHyp ψ t A U H) (g : H) : hA.lin g 0 = 0 := by
  rw [← hA.psi_one, hA.lin_psi g (one_mem A), mul_one, mul_inv_cancel]

theorem aff_eq_one_iff (hA : ActHyp ψ t A U H) (g : H) :
    hA.aff g = 1 ↔ ∀ a ∈ A, ψ (t⁻¹ * ((g : G) * (t * a) * (g : G)⁻¹)) = ψ a := by
  constructor
  · intro h a ha
    rw [← hA.aff_psi g ha, h]
    rfl
  · intro h
    refine Equiv.ext fun v => ?_
    obtain ⟨a, ha, rfl⟩ := hA.surj v
    rw [hA.aff_psi g ha, h a ha]
    rfl

theorem linFun_eq_of_normal [Finite V] (hA : ActHyp ψ t A U H) {H₀ R : Subgroup G}
    (hH₀ : H₀ ≤ H) (hRH₀ : R ≤ H₀) (hRn : ∀ g ∈ H₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hR : IsPGroup 2 R) (h2 : 2 ∣ Nat.card V)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ g ∈ H₀, hA.linFun g v = w)
    {r : G} (hr : r ∈ R) (v : V) : hA.linFun r v = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : R →* Equiv.Perm V := hA.lin.comp (inclusion (hRH₀.trans hH₀))
  let _ : MulAction R V := MulAction.compHom V f
  have hsmul : ∀ (r' : R) (w : V), r' • w = hA.linFun r' w := fun _ _ => rfl
  have h0 : (0 : V) ∈ MulAction.fixedPoints R V := fun r' => by
    rw [hsmul]
    exact hA.lin_zero ⟨r', hRH₀.trans hH₀ r'.2⟩
  obtain ⟨w, hw, hw0⟩ := hR.exists_fixed_point_of_prime_dvd_card_of_fixed_point V h2 h0
  by_cases hv : v = 0
  · rw [hv]
    exact hA.lin_zero ⟨r, hRH₀.trans hH₀ hr⟩
  obtain ⟨g, hg, hgw⟩ := htrans w v (Ne.symm hw0) hv
  have hgH := hH₀ hg
  have hrH := hRH₀.trans hH₀ hr
  have hconj : g⁻¹ * r * g ∈ R := by simpa using hRn g⁻¹ (inv_mem hg) r hr
  have hfix : hA.linFun (g⁻¹ * r * g) w = w := by
    have := hw ⟨_, hconj⟩
    rwa [hsmul] at this
  rw [← hgw, ← hA.linFun_mul hrH hgH]
  have e : r * g = g * (g⁻¹ * r * g) := by group
  rw [e, hA.linFun_mul hgH (hH₀ (hRH₀ hconj)), hfix]

end ActHyp

end Act

theorem pCore_quotient_eq {p : ℕ} {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hNp : IsPGroup p N) :
    CFSG.pCore p (H ⧸ N) = (CFSG.pCore p H).map (QuotientGroup.mk' N) := by
  have hcomap : (CFSG.pCore p (H ⧸ N)).comap (QuotientGroup.mk' N) = CFSG.pCore p H := by
    apply le_antisymm
    · refine le_sSup ⟨(CFSG.pCore_normal (G := H ⧸ N) (p := p)).comap (QuotientGroup.mk' N), ?_⟩
      refine (CFSG.pCore_isPGroup (G := H ⧸ N) (p := p)).comap_of_ker_isPGroup _ ?_
      rwa [QuotientGroup.ker_mk']
    · rw [← map_le_iff_le_comap]
      exact le_sSup ⟨(CFSG.pCore_normal (G := H) (p := p)).map _ (QuotientGroup.mk'_surjective N),
        (CFSG.pCore_isPGroup (G := H) (p := p)).map _⟩
  rw [← hcomap, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)]

theorem pCore_map_subgroupOf {G : Type*} [Group G] {p : ℕ} (H : Subgroup G) :
    ((CFSG.pCore p H).map H.subtype).subgroupOf H = CFSG.pCore p H :=
  comap_map_eq_self_of_injective H.subtype_injective _

section Vec

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem vecOf_conj_d (i : Axis) (l : Kˣ) {z : antiSp K} (hz : z ∈ rootA K i) :
    vecOf K i (dHom K i l * z * (dHom K i l)⁻¹) = (l : K) • vecOf K i z := by
  have two : ∀ {w : antiSp K}, w ∈ radA2 K →
      vecOf₂ (dElt l * w * (dElt l)⁻¹) = (l : K) • vecOf₂ w := by
    intro w hw
    obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp hw
    rw [dElt_mul_aElt, mul_inv_cancel_right, vecOf₂_aElt, vecOf₂_aElt]
  cases i
  · change z ∈ radA1 K at hz
    rw [radA1_eq_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    show vecOf₂ ((minorAut K).symm (minorAut K (dElt l) * minorAut K w *
      (minorAut K (dElt l))⁻¹)) = (l : K) • vecOf₂ ((minorAut K).symm (minorAut K w))
    rw [← map_inv, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact two hw
  · exact two hz

theorem vecOf_frob (i : Axis) {z : antiSp K} (hz : z ∈ rootA K i) :
    vecOf K i (frobAut K z) = fun j => vecOf K i z j ^ 2 := by
  have two : ∀ {w : antiSp K}, w ∈ radA2 K → vecOf₂ (frobAut K w) = fun j => vecOf₂ w j ^ 2 := by
    intro w hw
    obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp hw
    rw [frobAut_aElt, vecOf₂_aElt, vecOf₂_aElt]
  cases i
  · change z ∈ radA1 K at hz
    rw [radA1_eq_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    show vecOf₂ ((minorAut K).symm (frobAut K (minorAut K w))) =
      fun j => vecOf₂ ((minorAut K).symm (minorAut K w)) j ^ 2
    rw [frobAut_minorAut, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact two hw
  · exact two hz

theorem vecOf_frob_pow (i : Axis) (k : ℕ) {z : antiSp K} (hz : z ∈ rootA K i) :
    vecOf K i ((frobAut K ^ k) z) = fun j => vecOf K i z j ^ 2 ^ k := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih ((frobAut_mem_rootA_iff i z).mpr hz), vecOf_frob i hz]
    funext j
    rw [← pow_mul, ← pow_succ']

theorem vecOf_aut (i : Axis)
    (hst : RootAxisStructure (rootU K i) (rootA K i) (sHom K i) (dHom K i) (rootCoord K i)
      (vecOf K i)) {a : antiSp K} (ha : a ∈ rootA K i) (l : Kˣ) (M : SL₂ K) (k : ℕ)
    {z : antiSp K} (hz : z ∈ rootA K i) :
    vecOf K i ((MulAut.conj (a * (dHom K i l * sHom K i M)) * frobAut K ^ k) z) =
      (l : K) • ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => vecOf K i z j ^ 2 ^ k) := by
  have hw : (frobAut K ^ k) z ∈ rootA K i :=
    (frobAut_pow_mem_iff (frobAut_mem_rootA_iff i) k z).mpr hz
  set w := (frobAut K ^ k) z with hwdef
  have hsw : sHom K i M * w * (sHom K i M)⁻¹ ∈ rootA K i :=
    hst.A_normal_C _ (hst.s_mem_C M) w hw
  have hdsw : dHom K i l * (sHom K i M * w * (sHom K i M)⁻¹) * (dHom K i l)⁻¹ ∈ rootA K i :=
    hst.A_normal_N _ (d_mem_N hst l) _ hsw
  have e : (a * (dHom K i l * sHom K i M)) * w * (a * (dHom K i l * sHom K i M))⁻¹ =
      a * (dHom K i l * (sHom K i M * w * (sHom K i M)⁻¹) * (dHom K i l)⁻¹) * a⁻¹ := by group
  rw [MulAut.mul_apply, MulAut.conj_apply, ← hwdef, e, rootA_comm i ha hdsw,
    mul_inv_cancel_right, vecOf_conj_d i l hsw, hst.vec_conj M w hw, hwdef,
    vecOf_frob_pow i k hz]

end Vec

theorem conj_mem_pCore_map {G : Type*} [Group G] {p : ℕ} {H : Subgroup G} {g : G} (hg : g ∈ H)
    {x : G} (hx : x ∈ (CFSG.pCore p H).map H.subtype) :
    g * x * g⁻¹ ∈ (CFSG.pCore p H).map H.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem y hy ⟨g, hg⟩, rfl⟩

namespace FCHyp

section Act

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐕[" i "]" => (zpowers t ⊔ pull φ (rootU K i) : Subgroup G)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

theorem actHyp (h : FCHyp L K n φ t) (i : Axis) :
    ActHyp (psiG φ i) t 𝐀[i] 𝐔[i] 𝐍[i] where
  U_le := pull_mono φ (rootU_le_rootA i)
  add := fun _ ha _ hb => psiG_mul h.twoCore φ i ha hb
  ker := fun _ ha => psiG_eq_zero_iff h.twoCore φ i ha
  surj := exists_psiG_eq h.twoCore φ i
  conj_A := fun g hg a ha => (mem_normalizer_iff.mp (h.N_le_normalizer_A i hg) a).mp ha
  conj_U := fun g hg u hu => (mem_normalizer_iff.mp (h.N_le_normalizer_U i hg) u).mp hu
  conj_t := fun g hg => by
    have hxB : g⁻¹⁻¹ * t * g⁻¹ ∈ 𝐁[i] :=
      (mem_normalizer_iff''.mp (inv_mem hg) t).mp (mem_sup_left (mem_zpowers t))
    have h1 := h.conj_t_mem_tA i hxB ⟨g⁻¹, rfl⟩
    rw [inv_inv] at h1
    rw [h.twoCore.t_inv]
    exact h1

theorem exists_aut (h : FCHyp L K n φ t) (i : Axis) {g : G} (hgC : g ∈ 𝐂) (hgN : g ∈ 𝐍[i]) :
    ∃ a ∈ rootA K i, ∃ (l : Kˣ) (M : SL₂ K) (k : ℕ), k < n ∧
      normAct φ ⟨g, h.setup.cent_le hgC⟩ =
        MulAut.conj (a * (dHom K i l * sHom K i M)) * frobAut K ^ k := by
  have hαA : normAct φ ⟨g, h.setup.cent_le hgC⟩ ∈ autStab (rootA K i) :=
    (mem_normalizer_pull_iff φ _ ⟨g, h.setup.cent_le hgC⟩).mp (h.N_le_normalizer_A i hgN)
  rw [← (h.twoCore.axisAut i).stab_eq] at hαA
  exact ((h.twoCore.axisAut i).mem_iff _).mp hαA

theorem exists_semilinear (h : FCHyp L K n φ t) (i : Axis) {g : G} (hgC : g ∈ 𝐂)
    (hgN : g ∈ 𝐍[i]) :
    ∃ (l : Kˣ) (M : SL₂ K) (k : ℕ), k < n ∧ ∀ a ∈ 𝐀[i],
      psiG φ i (g * a * g⁻¹) =
        (l : K) • ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => psiG φ i a j ^ 2 ^ k) := by
  obtain ⟨a₀, ha₀, l, M, k, hk, hα⟩ := h.exists_aut i hgC hgN
  refine ⟨l, M, k, hk, fun a ha => ?_⟩
  obtain ⟨z, hz, rfl⟩ := exists_eq_symm_of_mem_pull ha
  rw [← normAct_symm_apply φ ⟨g, h.setup.cent_le hgC⟩ z, psiG_symm, psiG_symm, hα]
  exact vecOf_aut i (h.twoCore.axisStr i) ha₀ l M k hz

theorem mem_B_of_lin_eq_one (h : FCHyp L K n φ t) (i : Axis) {g : G} (hgC : g ∈ 𝐂)
    (hgN : g ∈ 𝐍[i]) (hlin : ∀ a ∈ 𝐀[i], psiG φ i (g * a * g⁻¹) = psiG φ i a) : g ∈ 𝐁[i] := by
  obtain ⟨a₀, ha₀, l, M, k, hk, hα⟩ := h.exists_aut i hgC hgN
  have hst := h.twoCore.axisStr i
  have hv : ∀ v : Fin 2 → K,
      (l : K) • ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => v j ^ 2 ^ k) = v := by
    intro v
    obtain ⟨z, hz, rfl⟩ := hst.vec_surj v
    have h1 := hlin _ (symm_mem_pull.mpr hz)
    rw [← normAct_symm_apply φ ⟨g, h.setup.cent_le hgC⟩ z, psiG_symm, psiG_symm, hα,
      vecOf_aut i hst ha₀ l M k hz] at h1
    exact h1
  have hpow0 : (0 : K) ^ 2 ^ k = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have e1 : (fun j => (![1, 0] : Fin 2 → K) j ^ 2 ^ k) = ![1, 0] := by
    funext j
    fin_cases j <;> simp [hpow0]
  have h1 := hv ![1, 0]
  rw [e1] at h1
  have hfix : ∀ x : K, x ^ 2 ^ k = x := by
    intro x
    have ex : (fun j => (![x, 0] : Fin 2 → K) j ^ 2 ^ k) = (x ^ 2 ^ k) • ![1, 0] := by
      funext j
      fin_cases j <;> simp [hpow0]
    have h2 := hv ![x, 0]
    rw [ex, Matrix.mulVec_smul, smul_comm, h1] at h2
    have := congrFun h2 0
    simpa using this
  have hk0 : k = 0 := eq_zero_of_frobRingEquiv_pow_eq_one (by have := h.setup.two_le; omega)
    h.setup.card_K hk (RingEquiv.ext fun x => by rw [frobRingEquiv_pow_apply, hfix x]; rfl)
  subst hk0
  have hlM : (l : K) • (M : Matrix (Fin 2) (Fin 2) K) = 1 := matrix_eq_one_of_mulVec fun v => by
    rw [Matrix.smul_mulVec]
    simpa using hv v
  have hl : l = 1 := by
    have hdet := congrArg Matrix.det hlM
    rw [Matrix.det_smul, M.det_coe, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h5 : ((l : K) - 1) ^ 2 = 0 := by linear_combination hdet + (1 - (l : K)) * h2
    exact Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5))
  have hM : M = 1 := by
    apply Subtype.ext
    rw [hl, Units.val_one, one_smul] at hlM
    exact hlM
  rw [hl, hM, map_one, map_one, mul_one, mul_one, pow_zero, mul_one] at hα
  have hα' : normAct φ ⟨g, h.setup.cent_le hgC⟩ = MulAut.conj (φ (φ.symm a₀)) := by
    rw [MulEquiv.apply_symm_apply]
    exact hα
  have h0 := inv_mul_mem_centralizer φ _ _ hα'
  have hτ : ((φ.symm a₀ : L) : G)⁻¹ * g ∈ zpowers t :=
    h.twoCore.mem_zpowers_of_mem h0 (mul_mem (inv_mem (h.setup.L_le (φ.symm a₀).2)) hgC)
  have e : g = ((φ.symm a₀ : L) : G) * (((φ.symm a₀ : L) : G)⁻¹ * g) := by group
  rw [e]
  exact mul_mem (mem_sup_right (symm_mem_pull.mpr ha₀)) (mem_sup_left hτ)

theorem exists_linear (h : FCHyp L K n φ t) (i : Axis) (A₀ : GL (Fin 2) K) :
    ∃ g ∈ 𝐂 ⊓ 𝐍[i], ∀ a ∈ 𝐀[i],
      psiG φ i (g * a * g⁻¹) = (A₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ psiG φ i a := by
  have hst := h.twoCore.axisStr i
  have hdet : (A₀ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A₀) |>.ne_zero
  obtain ⟨l₀, hl₀⟩ := exists_sq_eq (A₀ : Matrix (Fin 2) (Fin 2) K).det
  have hl₀0 : l₀ ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hl₀]; ring)
  set l : Kˣ := Units.mk0 l₀ hl₀0
  have hMdet : (l₀⁻¹ • (A₀ : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hl₀]
    field_simp
  set M : SL₂ K := ⟨l₀⁻¹ • (A₀ : Matrix (Fin 2) (Fin 2) K), hMdet⟩
  set g : G := ((φ.symm (dHom K i l * sHom K i M) : L) : G)
  have hgC : g ∈ 𝐂 := h.setup.L_le (φ.symm _).2
  have hds : dHom K i l * sHom K i M ∈
      normalizer ((rootU K i : Subgroup (antiSp K)) : Set (antiSp K)) := hst.ds_mem_N l M
  have hgA : g ∈ normalizer (𝐀[i] : Set G) := by
    refine RootAxisTwoCore.mem_normalizer_of_conj_le fun a ha => ?_
    obtain ⟨z, hz, rfl⟩ := exists_eq_symm_of_mem_pull ha
    rw [symm_conj_eq]
    exact symm_mem_pull.mpr (hst.A_normal_N _ hds z hz)
  refine ⟨g, mem_inf.mpr ⟨hgC, (h.twoCore.mem_normalizer_zpowers_sup_iff hgC
    (pull_le φ _)).mpr hgA⟩, fun a ha => ?_⟩
  obtain ⟨z, hz, rfl⟩ := exists_eq_symm_of_mem_pull ha
  rw [symm_conj_eq, psiG_symm, psiG_symm]
  have hsz : sHom K i M * z * (sHom K i M)⁻¹ ∈ rootA K i :=
    hst.A_normal_C _ (hst.s_mem_C M) z hz
  have e : (dHom K i l * sHom K i M) * z * (dHom K i l * sHom K i M)⁻¹ =
      dHom K i l * (sHom K i M * z * (sHom K i M)⁻¹) * (dHom K i l)⁻¹ := by group
  rw [e, vecOf_conj_d i l hsz, hst.vec_conj M z hz, ← Matrix.smul_mulVec]
  congr 1
  show l₀ • (l₀⁻¹ • (A₀ : Matrix (Fin 2) (Fin 2) K)) = A₀
  rw [smul_smul, mul_inv_cancel₀ hl₀0, one_smul]

end Act

section Kernel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

theorem symm_s_mem_M (h : FCHyp L K n φ t) (i : Axis) (M : SL₂ K) :
    ((φ.symm (sHom K i M) : L) : G) ∈ 𝐌[i] := by
  obtain ⟨hcC, -, hcU, -⟩ := h.symm_s_mem i M
  exact (h.twoCore.mem_normalizer_zpowers_sup_iff hcC (pull_le φ _)).mpr hcU

omit [Finite G] [Finite K] in
theorem two_dvd_card (h : FCHyp L K n φ t) : 2 ∣ Nat.card (Fin 2 → K) := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, h.setup.card_K]
  exact dvd_pow (dvd_pow_self 2 (by have := h.setup.two_le; omega)) two_ne_zero

theorem lin_trans (h : FCHyp L K n φ t) (i : Axis) {H₀ : Subgroup G}
    (hH₀ : ∀ M : SL₂ K, ((φ.symm (sHom K i M) : L) : G) ∈ H₀) :
    ∀ v w : Fin 2 → K, v ≠ 0 → w ≠ 0 → ∃ g ∈ H₀, (h.actHyp i).linFun g v = w := by
  intro v w hv hw
  obtain ⟨M, hM⟩ := exists_sl2_mulVec_eq hv hw
  refine ⟨_, hH₀ M, ?_⟩
  obtain ⟨a, ha, rfl⟩ := exists_psiG_eq h.twoCore φ i v
  rw [(h.actHyp i).linFun_psi (h.symm_s_mem i M).2.2.2 ha, (psiG_conj_s h.twoCore φ i M ha).2, hM]

theorem psiG_conj_eq_of_normal (h : FCHyp L K n φ t) (i : Axis) {H₀ R : Subgroup G}
    (hH₀ : H₀ ≤ 𝐍[i]) (hsH₀ : ∀ M : SL₂ K, ((φ.symm (sHom K i M) : L) : G) ∈ H₀)
    (hRH₀ : R ≤ H₀) (hRn : ∀ g ∈ H₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hR : IsPGroup 2 R) {r : G}
    (hr : r ∈ R) {a : G} (ha : a ∈ 𝐀[i]) : psiG φ i (r * a * r⁻¹) = psiG φ i a := by
  rw [← (h.actHyp i).linFun_psi (hH₀ (hRH₀ hr)) ha]
  exact (h.actHyp i).linFun_eq_of_normal hH₀ hRH₀ hRn hR h.two_dvd_card (h.lin_trans i hsH₀) hr _

theorem D_lin (h : FCHyp L K n φ t) (i : Axis) {d : G} (hd : d ∈ 𝐃[i]) {a : G}
    (ha : a ∈ 𝐀[i]) : psiG φ i (d * a * d⁻¹) = psiG φ i a :=
  h.psiG_conj_eq_of_normal i (h.twoCore.M_le_normalizer_B φ i) (h.symm_s_mem_M i)
    (map_subtype_le _) (fun _ hg _ hr => conj_mem_pCore_map hg hr) (CFSG.pCore_isPGroup.map _) hd
    ha

theorem E_lin (h : FCHyp L K n φ t) (i : Axis) {e : G} (he : e ∈ 𝐄[i]) {a : G}
    (ha : a ∈ 𝐀[i]) : psiG φ i (e * a * e⁻¹) = psiG φ i a :=
  h.psiG_conj_eq_of_normal i le_rfl (fun M => (h.symm_s_mem i M).2.2.2) (map_subtype_le _)
    (fun _ hg _ hr => conj_mem_pCore_map hg hr) (CFSG.pCore_isPGroup.map _) he ha

theorem aff_zero_eq_zero_iff (h : FCHyp L K n φ t) (i : Axis) (g : 𝐍[i]) :
    (h.actHyp i).aff g 0 = 0 ↔ (g : G) ∈ 𝐌[i] := by
  rw [(h.actHyp i).aff_zero, psiG_eq_zero_iff h.twoCore φ i ((h.actHyp i).conj_t g g.2)]
  constructor
  · intro hu
    have hgU := h.N_le_normalizer_U i g.2
    rw [← inv_mem_iff]
    exact mem_M_of (inv_mem hgU) hu (by group)
  · intro hgM
    have h1 := h.twoCore.conj_t_mem φ i (inv_mem hgM)
    rw [inv_inv] at h1
    rw [h.twoCore.t_inv]
    exact h1

theorem aff_D (h : FCHyp L K n φ t) (i : Axis) (g : 𝐍[i]) (hg : (g : G) ∈ 𝐃[i]) :
    (h.actHyp i).aff g = 1 := by
  have hlin : (h.actHyp i).lin g = 1 :=
    ((h.actHyp i).lin_eq_one_iff g).mpr fun a ha => h.D_lin i hg ha
  have h0 : (h.actHyp i).aff g 0 = 0 :=
    (h.aff_zero_eq_zero_iff i g).mpr (map_subtype_le _ hg)
  refine Equiv.ext fun v => ?_
  rw [(h.actHyp i).aff_eq, hlin, ← (h.actHyp i).aff_zero, h0, add_zero]

theorem aff_eq_one_iff_mem_D (h : FCHyp L K n φ t) (i : Axis) (g : 𝐍[i]) :
    (h.actHyp i).aff g = 1 ↔ (g : G) ∈ 𝐃[i] := by
  refine ⟨fun h1 => ?_, h.aff_D i g⟩
  have hgM : (g : G) ∈ 𝐌[i] := (h.aff_zero_eq_zero_iff i g).mp (by rw [h1]; rfl)
  obtain ⟨h₁, -, -, -⟩ := h.twoCore.cond φ i (h.M_not_le_C i)
  obtain ⟨d, hd, c, hc, hdc⟩ := h₁ g hgM
  have hMN := h.twoCore.M_le_normalizer_B φ i
  have hcN : c ∈ 𝐍[i] := hMN (mem_inf.mp hc).2
  have hdN : d ∈ 𝐍[i] := hMN (map_subtype_le _ hd)
  have hc1 : (h.actHyp i).aff ⟨c, hcN⟩ = 1 := by
    have e : (⟨c, hcN⟩ : 𝐍[i]) = ⟨d, hdN⟩⁻¹ * g := Subtype.ext (by
      show c = d⁻¹ * (g : G)
      rw [← hdc]
      group)
    rw [e, map_mul, map_inv, h.aff_D i _ hd, h1, inv_one, one_mul]
  have hcC : c ∈ 𝐂 := (mem_inf.mp hc).1
  have hlin : ∀ a ∈ 𝐀[i], psiG φ i (c * a * c⁻¹) = psiG φ i a := by
    intro a ha
    have h2 := ((h.actHyp i).aff_eq_one_iff _).mp hc1 a ha
    have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hcC
    have e : t⁻¹ * (c * (t * a) * c⁻¹) = c * a * c⁻¹ := by
      rw [← mul_assoc c t a, hct]
      group
    rwa [e] at h2
  have hcB := h.mem_B_of_lin_eq_one i hcC hcN hlin
  rw [← hdc]
  exact mul_mem hd (h.B_le_D i hcB)

theorem kernel_B (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐍[i]) :
    (∀ b ∈ 𝐁[i], b⁻¹ * (g * b * g⁻¹) ∈ 𝐔[i]) ↔ g ∈ 𝐃[i] := by
  have hA := h.actHyp i
  rw [← h.aff_eq_one_iff_mem_D i ⟨g, hg⟩, hA.aff_eq_one_iff]
  constructor
  · intro hB a ha
    have htaB : t * a ∈ 𝐁[i] := mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right ha)
    have h1 := hB _ htaB
    refine ((hA.psi_eq_iff ha (hA.mem_A_aff hg ha)).mpr ?_).symm
    rwa [show a⁻¹ * (t⁻¹ * (g * (t * a) * g⁻¹)) = (t * a)⁻¹ * (g * (t * a) * g⁻¹) by group]
  · intro hA' b hb
    rcases (mem_zpowers_sup_iff h.setup.t_mul_t (TwoCoreSetup.comm_pull φ h.twoCore)).mp hb with
      hbA | hbA
    · have h1 := hA' b hbA
      have h0 := hA' 1 (one_mem _)
      rw [mul_one, hA.psi_one] at h0
      rw [show t⁻¹ * (g * (t * b) * g⁻¹) = (t⁻¹ * (g * t * g⁻¹)) * (g * b * g⁻¹) by group,
        hA.add _ (hA.conj_t g hg) _ (hA.conj_A g hg b hbA), h0, zero_add] at h1
      exact (hA.psi_eq_iff hbA (hA.conj_A g hg b hbA)).mp h1.symm
    · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ 𝐀[i], b = t * a :=
        ⟨t * b, hbA, by rw [← mul_assoc, h.setup.t_mul_t, one_mul]⟩
      have h1 := hA' a ha
      have h2 := (hA.psi_eq_iff ha (hA.mem_A_aff hg ha)).mp h1.symm
      rwa [show a⁻¹ * (t⁻¹ * (g * (t * a) * g⁻¹)) = (t * a)⁻¹ * (g * (t * a) * g⁻¹) by group]
        at h2

theorem conj_mem_D (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐍[i]) {d : G}
    (hd : d ∈ 𝐃[i]) : g * d * g⁻¹ ∈ 𝐃[i] := by
  have hdN : d ∈ 𝐍[i] := h.twoCore.M_le_normalizer_B φ i (map_subtype_le _ hd)
  have := (h.aff_eq_one_iff_mem_D i (⟨g, hg⟩ * ⟨d, hdN⟩ * ⟨g, hg⟩⁻¹)).mp (by
    rw [map_mul, map_mul, map_inv, h.aff_D i ⟨d, hdN⟩ hd, mul_one, mul_inv_cancel])
  exact this

theorem D_le_E (h : FCHyp L K n φ t) (i : Axis) : 𝐃[i] ≤ 𝐄[i] := by
  have hDN : 𝐃[i] ≤ 𝐍[i] := (map_subtype_le _).trans (h.twoCore.M_le_normalizer_B φ i)
  have hn : ((𝐃[i]).subgroupOf 𝐍[i]).Normal :=
    ⟨fun d hd g => mem_subgroupOf.mpr (h.conj_mem_D i g.2 (mem_subgroupOf.mp hd))⟩
  have hp : IsPGroup 2 ((𝐃[i]).subgroupOf 𝐍[i]) :=
    (CFSG.pCore_isPGroup.map _).of_equiv (subgroupOfEquivOfLe hDN).symm
  have hle : (𝐃[i]).subgroupOf 𝐍[i] ≤ CFSG.pCore 2 𝐍[i] := le_sSup ⟨hn, hp⟩
  intro d hd
  exact ⟨⟨d, hDN hd⟩, hle (mem_subgroupOf.mpr hd), rfl⟩

theorem aff_trans (h : FCHyp L K n φ t) (i : Axis) (v w : Fin 2 → K) :
    ∃ g : 𝐍[i], (h.actHyp i).aff g v = w := by
  have hfrom0 : ∀ v, ∃ g : 𝐍[i], (h.actHyp i).aff g 0 = v := by
    intro v
    obtain ⟨a, ha, rfl⟩ := exists_psiG_eq h.twoCore φ i v
    obtain ⟨x, hx, hxt⟩ := h.exists_conj_eq_t_mul i ha
    refine ⟨⟨x, hx.1⟩⁻¹, ?_⟩
    rw [(h.actHyp i).aff_zero]
    show psiG φ i (t⁻¹ * (x⁻¹ * t * x⁻¹⁻¹)) = psiG φ i a
    rw [inv_inv, hxt, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨g₁, hg₁⟩ := hfrom0 v
  obtain ⟨g₂, hg₂⟩ := hfrom0 w
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← hg₁,
    show ((h.actHyp i).aff g₁)⁻¹ ((h.actHyp i).aff g₁ 0) = 0 from
      Equiv.Perm.inv_eq_iff_eq.mpr rfl, hg₂]

theorem aff_semilinear (h : FCHyp L K n φ t) (i : Axis) (g : 𝐍[i]) (hgM : (g : G) ∈ 𝐌[i]) :
    ∃ (A₀ : GL (Fin 2) K) (k : ℕ), k < n ∧ ∀ x : Fin 2 → K,
      (h.actHyp i).aff g x = (A₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => x j ^ 2 ^ k := by
  obtain ⟨h₁, -, -, -⟩ := h.twoCore.cond φ i (h.M_not_le_C i)
  obtain ⟨d, hd, c, hc, hdc⟩ := h₁ g hgM
  have hMN := h.twoCore.M_le_normalizer_B φ i
  have hcN : c ∈ 𝐍[i] := hMN (mem_inf.mp hc).2
  have hdN : d ∈ 𝐍[i] := hMN (map_subtype_le _ hd)
  have hcC : c ∈ 𝐂 := (mem_inf.mp hc).1
  have e : g = ⟨d, hdN⟩ * ⟨c, hcN⟩ := Subtype.ext hdc.symm
  obtain ⟨l, M, k, hk, hform⟩ := h.exists_semilinear i hcC hcN
  have hdet : ((l : K) • (M : Matrix (Fin 2) (Fin 2) K)).det ≠ 0 := by
    rw [Matrix.det_smul, M.det_coe, mul_one]
    exact pow_ne_zero _ l.ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, k, hk, fun x => ?_⟩
  have hval : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = (l : K) • (M : Matrix (Fin 2) (Fin 2) K) := rfl
  rw [hval, Matrix.smul_mulVec, e, map_mul, h.aff_D i _ hd, one_mul]
  obtain ⟨a, ha, rfl⟩ := exists_psiG_eq h.twoCore φ i x
  rw [(h.actHyp i).aff_psi _ ha, ← hform a ha]
  have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hcC
  congr 1
  show t⁻¹ * (c * (t * a) * c⁻¹) = c * a * c⁻¹
  rw [← mul_assoc c t a, hct]
  group

theorem aff_linear (h : FCHyp L K n φ t) (i : Axis) (A₀ : GL (Fin 2) K) :
    ∃ g : 𝐍[i], (g : G) ∈ 𝐂 ∧ ∀ x : Fin 2 → K,
      (h.actHyp i).aff g x = (A₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ x := by
  obtain ⟨g, hg, hform⟩ := h.exists_linear i A₀
  refine ⟨⟨g, (mem_inf.mp hg).2⟩, (mem_inf.mp hg).1, fun x => ?_⟩
  obtain ⟨a, ha, rfl⟩ := exists_psiG_eq h.twoCore φ i x
  rw [(h.actHyp i).aff_psi _ ha, ← hform a ha]
  have hct : g * t = t * g := mem_centralizer_singleton_iff.mp (mem_inf.mp hg).1
  congr 1
  show t⁻¹ * (g * (t * a) * g⁻¹) = g * a * g⁻¹
  rw [← mul_assoc g t a, hct]
  group

theorem quotient_stab (h : FCHyp L K n φ t) (i : Axis) :
    ∃ _ : ((𝐁[i]).subgroupOf (𝐂 ⊓ 𝐍[i])).Normal, ∃ _ : ((𝐃[i]).subgroupOf 𝐌[i]).Normal,
      ∃ e : (↥(𝐂 ⊓ 𝐍[i]) ⧸ (𝐁[i]).subgroupOf (𝐂 ⊓ 𝐍[i])) ≃* (↥𝐌[i] ⧸ (𝐃[i]).subgroupOf 𝐌[i]),
        ∀ (x : ↥(𝐂 ⊓ 𝐍[i])) (m : ↥𝐌[i]), (x : G) = m →
          e (QuotientGroup.mk x) = QuotientGroup.mk m := by
  have hBn : ((𝐁[i]).subgroupOf (𝐂 ⊓ 𝐍[i])).Normal := ⟨fun b hb c => mem_subgroupOf.mpr
    ((mem_normalizer_iff.mp (mem_inf.mp c.2).2 b).mp (mem_subgroupOf.mp hb))⟩
  have hDn : ((𝐃[i]).subgroupOf 𝐌[i]).Normal :=
    ⟨fun d hd m => mem_subgroupOf.mpr (conj_mem_pCore_map m.2 (mem_subgroupOf.mp hd))⟩
  have hCN : 𝐂 ⊓ 𝐍[i] ≤ 𝐌[i] := by
    rw [← h.twoCore.inf_normalizer_eq φ i]
    exact inf_le_right
  set f : ↥(𝐂 ⊓ 𝐍[i]) →* ↥𝐌[i] ⧸ (𝐃[i]).subgroupOf 𝐌[i] :=
    (QuotientGroup.mk' _).comp (inclusion hCN) with hf
  have hker : (𝐁[i]).subgroupOf (𝐂 ⊓ 𝐍[i]) = f.ker := by
    ext x
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
    show (x : G) ∈ 𝐁[i] ↔ (x : G) ∈ 𝐃[i]
    constructor
    · intro hx
      exact h.B_le_D i hx
    · intro hx
      have h1 : (x : G) ∈ 𝐃[i] ⊓ 𝐂 := mem_inf.mpr ⟨hx, (mem_inf.mp x.2).1⟩
      rwa [h.D_inf_C i] at h1
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨h₁, -, -, -⟩ := h.twoCore.cond φ i (h.M_not_le_C i)
    obtain ⟨d, hd, c, hc, hdc⟩ := h₁ m m.2
    have hc' : c ∈ 𝐂 ⊓ 𝐍[i] := by
      rw [← h.twoCore.inf_normalizer_eq φ i]
      exact hc
    refine ⟨⟨c, hc'⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [mem_subgroupOf]
    show c⁻¹ * (m : G) ∈ 𝐃[i]
    rw [← hdc, show c⁻¹ * (d * c) = c⁻¹ * d * c⁻¹⁻¹ by group]
    exact conj_mem_pCore_map (inv_mem (mem_inf.mp hc).2) hd
  refine ⟨hBn, hDn, (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj), fun x m hxm => ?_⟩
  change f x = QuotientGroup.mk m
  rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  congr 1
  exact Subtype.ext hxm

theorem quotient_aff (h : FCHyp L K n φ t) (i : Axis) :
    ∃ _ : ((𝐃[i]).subgroupOf 𝐍[i]).Normal,
      ∃ ρ : (↥𝐍[i] ⧸ (𝐃[i]).subgroupOf 𝐍[i]) →* Equiv.Perm (Fin 2 → K),
        Function.Injective ρ ∧ ∀ g : 𝐍[i], ρ (QuotientGroup.mk g) = (h.actHyp i).aff g := by
  have hker : (𝐃[i]).subgroupOf 𝐍[i] = (h.actHyp i).aff.ker := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf, h.aff_eq_one_iff_mem_D]
  have hn : ((𝐃[i]).subgroupOf 𝐍[i]).Normal :=
    ⟨fun d hd g => mem_subgroupOf.mpr (h.conj_mem_D i g.2 (mem_subgroupOf.mp hd))⟩
  refine ⟨hn, QuotientGroup.lift _ (h.actHyp i).aff (fun g hg => hker ▸ hg), ?_,
    fun g => QuotientGroup.lift_mk _ _ _⟩
  refine (injective_iff_map_eq_one _).mpr fun q hq => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [QuotientGroup.lift_mk, ← MonoidHom.mem_ker, ← hker] at hq
  exact (QuotientGroup.eq_one_iff g).mpr hq

theorem aff_E (h : FCHyp L K n φ t) (i : Axis) (e : 𝐍[i]) (he : (e : G) ∈ 𝐄[i])
    (v : Fin 2 → K) : (h.actHyp i).aff e v = v + (h.actHyp i).aff e 0 := by
  have hlin : (h.actHyp i).lin e = 1 :=
    ((h.actHyp i).lin_eq_one_iff e).mpr fun a ha => h.E_lin i he ha
  rw [(h.actHyp i).aff_eq, hlin, (h.actHyp i).aff_zero]
  rfl

theorem E_alternative (h : FCHyp L K n φ t) (i : Axis) :
    𝐄[i] = 𝐃[i] ∨ ∀ b : Fin 2 → K, ∃ e : 𝐍[i], (e : G) ∈ 𝐄[i] ∧
      ∀ x, (h.actHyp i).aff e x = x + b := by
  by_cases hall : ∀ e : 𝐍[i], (e : G) ∈ 𝐄[i] → (h.actHyp i).aff e 0 = 0
  · left
    refine le_antisymm (fun e he => ?_) (h.D_le_E i)
    have heN : e ∈ 𝐍[i] := map_subtype_le _ he
    refine (h.aff_eq_one_iff_mem_D i ⟨e, heN⟩).mp (Equiv.ext fun v => ?_)
    rw [h.aff_E i ⟨e, heN⟩ he, hall ⟨e, heN⟩ he, add_zero]
    rfl
  · right
    push Not at hall
    obtain ⟨e₀, he₀, hb₀⟩ := hall
    intro b
    by_cases hb : b = 0
    · refine ⟨1, one_mem _, fun x => ?_⟩
      rw [map_one, hb, add_zero]
      rfl
    obtain ⟨M, hM⟩ := exists_sl2_mulVec_eq hb₀ hb
    obtain ⟨hcC, -, -, hcN⟩ := h.symm_s_mem i M
    set c : G := ((φ.symm (sHom K i M) : L) : G) with hc
    have hcN' : c ∈ 𝐍[i] := hcN
    have he₁ : c * e₀ * c⁻¹ ∈ 𝐄[i] := conj_mem_pCore_map hcN' he₀
    have he₁N : c * e₀ * c⁻¹ ∈ 𝐍[i] := map_subtype_le _ he₁
    refine ⟨⟨_, he₁N⟩, he₁, fun x => ?_⟩
    rw [h.aff_E i ⟨_, he₁N⟩ he₁, (h.actHyp i).aff_zero]
    congr 1
    have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hcC
    have hw := (h.actHyp i).conj_t _ e₀.2
    have e : t⁻¹ * ((⟨_, he₁N⟩ : 𝐍[i]) * t * ((⟨_, he₁N⟩ : 𝐍[i]) : G)⁻¹) =
        c * (t⁻¹ * ((e₀ : G) * t * (e₀ : G)⁻¹)) * c⁻¹ := by
      show t⁻¹ * (c * e₀ * c⁻¹ * t * (c * e₀ * c⁻¹)⁻¹) = _
      have hct' : c⁻¹ * t = t * c⁻¹ := by
        calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
          _ = t * c⁻¹ := by group
      have hct'' : t⁻¹ * c = c * t⁻¹ := by
        calc t⁻¹ * c = t⁻¹ * (c * t) * t⁻¹ := by group
          _ = t⁻¹ * (t * c) * t⁻¹ := by rw [hct]
          _ = c * t⁻¹ := by group
      have hctc : c⁻¹ * t * c = t := by
        rw [hct', mul_assoc, inv_mul_cancel, mul_one]
      calc t⁻¹ * (c * e₀ * c⁻¹ * t * (c * e₀ * c⁻¹)⁻¹)
          = (t⁻¹ * c) * e₀ * (c⁻¹ * t * c) * (e₀ : G)⁻¹ * c⁻¹ := by group
        _ = (c * t⁻¹) * e₀ * t * (e₀ : G)⁻¹ * c⁻¹ := by rw [hct'', hctc]
        _ = c * (t⁻¹ * ((e₀ : G) * t * (e₀ : G)⁻¹)) * c⁻¹ := by group
    rw [e, (psiG_conj_s h.twoCore φ i M hw).2, ← (h.actHyp i).aff_zero, hM]

theorem E_mul_M (h : FCHyp L K n φ t) (i : Axis)
    (htr : ∀ b : Fin 2 → K, ∃ e : 𝐍[i], (e : G) ∈ 𝐄[i] ∧ ∀ x, (h.actHyp i).aff e x = x + b) :
    (𝐄[i] : Set G) * (𝐌[i] : Set G) = (𝐍[i] : Set G) ∧ 𝐄[i] ⊓ 𝐌[i] = 𝐃[i] := by
  have hMN := h.twoCore.M_le_normalizer_B φ i
  constructor
  · ext g
    simp only [Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨e, he, m, hm, rfl⟩
      exact mul_mem (map_subtype_le _ he) (hMN hm)
    · intro hg
      obtain ⟨e, he, hetr⟩ := htr ((h.actHyp i).aff ⟨g, hg⟩ 0)
      refine ⟨e, he, (e : G)⁻¹ * g, ?_, by group⟩
      have h1 : (h.actHyp i).aff (e⁻¹ * ⟨g, hg⟩) 0 = 0 := by
        rw [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, hetr, zero_add]
      exact (h.aff_zero_eq_zero_iff i _).mp h1
  · refine le_antisymm (fun x hx => ?_) (le_inf (h.D_le_E i) (map_subtype_le _))
    obtain ⟨hxE, hxM⟩ := mem_inf.mp hx
    have hxN : x ∈ 𝐍[i] := hMN hxM
    have h0 := (h.aff_zero_eq_zero_iff i ⟨x, hxN⟩).mpr hxM
    refine (h.aff_eq_one_iff_mem_D i ⟨x, hxN⟩).mp (Equiv.ext fun v => ?_)
    rw [h.aff_E i ⟨x, hxN⟩ hxE, h0, add_zero]
    rfl

theorem quotient_E (h : FCHyp L K n φ t) (i : Axis)
    (htr : ∀ b : Fin 2 → K, ∃ e : 𝐍[i], (e : G) ∈ 𝐄[i] ∧ ∀ x, (h.actHyp i).aff e x = x + b) :
    ∃ _ : ((𝐃[i]).subgroupOf 𝐄[i]).Normal, ∃ _ : ((𝐔[i]).subgroupOf 𝐀[i]).Normal,
      ∃ e : (↥𝐄[i] ⧸ (𝐃[i]).subgroupOf 𝐄[i]) ≃* (↥𝐀[i] ⧸ (𝐔[i]).subgroupOf 𝐀[i]),
        (∀ x : 𝐄[i], ∃ a : 𝐀[i], (a : G) = t⁻¹ * ((x : G)⁻¹ * t * x) ∧
          e (QuotientGroup.mk x) = QuotientGroup.mk a) ∧
        (∀ h' ∈ 𝐂 ⊓ 𝐍[i], ∀ x : 𝐄[i], ∃ x' : 𝐄[i], (x' : G) = h'⁻¹ * x * h' ∧
          ∀ a a' : 𝐀[i], (a' : G) = h'⁻¹ * a * h' →
            e (QuotientGroup.mk x) = QuotientGroup.mk a →
            e (QuotientGroup.mk x') = QuotientGroup.mk a') ∧
        Nat.card (↥𝐄[i] ⧸ (𝐃[i]).subgroupOf 𝐄[i]) = Nat.card K ^ 2 := by
  have hA := h.actHyp i
  have hEN : 𝐄[i] ≤ 𝐍[i] := map_subtype_le _
  have hDE : ((𝐃[i]).subgroupOf 𝐄[i]).Normal := ⟨fun d hd x => mem_subgroupOf.mpr
    (h.conj_mem_D i (hEN x.2) (mem_subgroupOf.mp hd))⟩
  have hAU : 𝐀[i] ≤ normalizer (𝐔[i] : Set G) :=
    (le_sup_right.trans le_normalizer).trans (h.N_le_normalizer_U i)
  have hUA : ((𝐔[i]).subgroupOf 𝐀[i]).Normal := ⟨fun u hu a => mem_subgroupOf.mpr
    ((mem_normalizer_iff.mp (hAU a.2) u).mp (mem_subgroupOf.mp hu))⟩
  have hmem : ∀ x : 𝐄[i], t⁻¹ * ((x : G)⁻¹ * t * x) ∈ 𝐀[i] := fun x => by
    have := hA.conj_t _ (inv_mem (hEN x.2))
    rwa [inv_inv] at this
  have hψθ : ∀ x : 𝐄[i], psiG φ i (t⁻¹ * ((x : G)⁻¹ * t * x)) =
      hA.aff ⟨x, hEN x.2⟩⁻¹ 0 := fun x => by
    rw [hA.aff_zero]
    show _ = psiG φ i (t⁻¹ * ((x : G)⁻¹ * t * (x : G)⁻¹⁻¹))
    rw [inv_inv]
  have hmk : ∀ a b : 𝐀[i], (QuotientGroup.mk a : ↥𝐀[i] ⧸ (𝐔[i]).subgroupOf 𝐀[i]) =
      QuotientGroup.mk b ↔ psiG φ i a = psiG φ i b := fun a b => by
    rw [QuotientGroup.eq, mem_subgroupOf, hA.psi_eq_iff a.2 b.2]
    rfl
  have hψθ' : ∀ x : 𝐄[i], psiG φ i ((⟨_, hmem x⟩ : 𝐀[i]) : G) =
      hA.aff ⟨x, hEN x.2⟩⁻¹ 0 := hψθ
  let θ : 𝐄[i] →* ↥𝐀[i] ⧸ (𝐔[i]).subgroupOf 𝐀[i] :=
    { toFun := fun x => QuotientGroup.mk ⟨_, hmem x⟩
      map_one' := by
        rw [← QuotientGroup.mk_one]
        congr 1
        exact Subtype.ext (by simp)
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, hmk]
        change psiG φ i ((⟨_, hmem (x * y)⟩ : 𝐀[i]) : G) =
          psiG φ i ((t⁻¹ * ((x : G)⁻¹ * t * x)) * (t⁻¹ * ((y : G)⁻¹ * t * y)))
        rw [psiG_mul h.twoCore φ i (hmem x) (hmem y), hψθ' (x * y), hψθ x, hψθ y]
        have e2 : (⟨((x * y : 𝐄[i]) : G), hEN (x * y).2⟩ : 𝐍[i])⁻¹ =
            (⟨y, hEN y.2⟩ : 𝐍[i])⁻¹ * (⟨x, hEN x.2⟩ : 𝐍[i])⁻¹ :=
          Subtype.ext (by simp [mul_inv_rev])
        rw [e2, map_mul, Equiv.Perm.mul_apply, h.aff_E i _ (inv_mem y.2)] }
  have hθ : ∀ x : 𝐄[i], θ x = QuotientGroup.mk ⟨_, hmem x⟩ := fun _ => rfl
  have hDEM := (h.E_mul_M i htr).2
  have hker : (𝐃[i]).subgroupOf 𝐄[i] = θ.ker := by
    ext x
    rw [MonoidHom.mem_ker, hθ, QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
    change (x : G) ∈ 𝐃[i] ↔ t⁻¹ * ((x : G)⁻¹ * t * x) ∈ 𝐔[i]
    rw [← psiG_eq_zero_iff h.twoCore φ i (hmem x), hψθ x, h.aff_zero_eq_zero_iff]
    change (x : G) ∈ 𝐃[i] ↔ (x : G)⁻¹ ∈ 𝐌[i]
    rw [inv_mem_iff]
    constructor
    · intro hx
      rw [← hDEM] at hx
      exact (mem_inf.mp hx).2
    · intro hx
      rw [← hDEM]
      exact mem_inf.mpr ⟨x.2, hx⟩
  have hsurj : Function.Surjective θ := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he, hetr⟩ := htr (psiG φ i a)
    refine ⟨⟨(e : G)⁻¹, inv_mem he⟩, ?_⟩
    rw [hθ, hmk, hψθ']
    have : (⟨((⟨(e : G)⁻¹, inv_mem he⟩ : 𝐄[i]) : G), hEN (inv_mem he)⟩ : 𝐍[i])⁻¹ = e :=
      Subtype.ext (inv_inv _)
    rw [this, hetr, zero_add]
  have hcardA : Nat.card (↥𝐀[i] ⧸ (𝐔[i]).subgroupOf 𝐀[i]) = Nat.card K ^ 2 := by
    have h1 := card_eq_card_quotient_mul_card_subgroup ((𝐔[i]).subgroupOf 𝐀[i])
    rw [Nat.card_congr (subgroupOfEquivOfLe (pull_mono φ (rootU_le_rootA i))).toEquiv,
      card_U, card_pull, card_rootA] at h1
    have hq : 0 < Nat.card K := Nat.card_pos
    have h2 : Nat.card (↥𝐀[i] ⧸ (𝐔[i]).subgroupOf 𝐀[i]) * Nat.card K =
        Nat.card K ^ 2 * Nat.card K := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hq h2
  set e := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hsurj) with he
  have he_mk : ∀ x : 𝐄[i], e (QuotientGroup.mk x) = θ x := fun _ => rfl
  refine ⟨hDE, hUA, e, fun x => ⟨⟨_, hmem x⟩, rfl, he_mk x⟩, fun h' hh' x => ?_, ?_⟩
  · have hx' : h'⁻¹ * x * h' ∈ 𝐄[i] := by
      have := conj_mem_pCore_map (inv_mem (mem_inf.mp hh').2) x.2
      rwa [inv_inv] at this
    refine ⟨⟨_, hx'⟩, rfl, fun a a' ha' hxa => ?_⟩
    rw [he_mk, hθ, hmk] at hxa ⊢
    have hhC : h' * t = t * h' := mem_centralizer_singleton_iff.mp (mem_inf.mp hh').1
    have hhN := inv_mem (mem_inf.mp hh').2
    have e3 : t⁻¹ * ((h'⁻¹ * x * h')⁻¹ * t * (h'⁻¹ * x * h')) =
        h'⁻¹ * (t⁻¹ * ((x : G)⁻¹ * t * x)) * h'⁻¹⁻¹ := by
      have h1 : h'⁻¹ * t⁻¹ = t⁻¹ * h'⁻¹ := by
        calc h'⁻¹ * t⁻¹ = (t * h')⁻¹ := by group
          _ = (h' * t)⁻¹ := by rw [hhC]
          _ = t⁻¹ * h'⁻¹ := by group
      have h2 : h' * t * h'⁻¹ = t := by rw [hhC, mul_inv_cancel_right]
      calc t⁻¹ * ((h'⁻¹ * x * h')⁻¹ * t * (h'⁻¹ * x * h'))
          = t⁻¹ * h'⁻¹ * (x : G)⁻¹ * (h' * t * h'⁻¹) * x * h' := by group
        _ = h'⁻¹ * t⁻¹ * (x : G)⁻¹ * t * x * h' := by rw [h2, ← h1]
        _ = h'⁻¹ * (t⁻¹ * ((x : G)⁻¹ * t * x)) * h'⁻¹⁻¹ := by group
    change psiG φ i (t⁻¹ * ((h'⁻¹ * x * h')⁻¹ * t * (h'⁻¹ * x * h'))) = psiG φ i a'
    have k1 := hA.linFun_psi hhN (hmem x)
    have k2 := hA.linFun_psi hhN a.2
    rw [inv_inv] at k2
    rw [e3, ha', ← k1, ← k2]
    exact congrArg _ hxa
  · rw [Nat.card_congr e.toEquiv, hcardA]

theorem pCore_quotient_N (h : FCHyp L K n φ t) (i : Axis) :
    ∃ _ : ((𝐃[i]).subgroupOf 𝐍[i]).Normal,
      CFSG.pCore 2 (↥𝐍[i] ⧸ (𝐃[i]).subgroupOf 𝐍[i]) =
        ((𝐄[i]).subgroupOf 𝐍[i]).map (QuotientGroup.mk' _) := by
  have hDN : 𝐃[i] ≤ 𝐍[i] := (map_subtype_le _).trans (h.twoCore.M_le_normalizer_B φ i)
  have hn : ((𝐃[i]).subgroupOf 𝐍[i]).Normal :=
    ⟨fun d hd g => mem_subgroupOf.mpr (h.conj_mem_D i g.2 (mem_subgroupOf.mp hd))⟩
  refine ⟨hn, ?_⟩
  rw [pCore_map_subgroupOf]
  exact pCore_quotient_eq _ ((CFSG.pCore_isPGroup.map _).of_equiv (subgroupOfEquivOfLe hDN).symm)

end Kernel

end FCHyp

end FullCenter

end CFSG.LocalAnalysis.SymplecticFourStandard

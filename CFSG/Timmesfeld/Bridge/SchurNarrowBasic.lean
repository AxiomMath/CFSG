module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Timmesfeld.Bridge

open scoped commutatorElement

@[expose] def CentralIn {X : Type*} [Group X] (S : Subgroup X) (w : X) : Prop :=
  w ∈ S ∧ ∀ q ∈ S, Commute q w

structure SylowBorelData (X : Type*) [Group X] (S : Subgroup X) : Prop where
  commutator_central : ∀ a ∈ S, ∀ b ∈ S, CentralIn S (a * b * a⁻¹ * b⁻¹)
  sq_central : ∀ a ∈ S, CentralIn S (a * a)
  center_sq : ∀ w, CentralIn S w → w * w = 1
  noncomm : ∃ a ∈ S, ¬ CentralIn S a
  torus : ∃ D : Subgroup X, Odd (Nat.card D) ∧ D ≤ Subgroup.normalizer (S : Set X) ∧
    (∀ w w' : X, CentralIn S w → w ≠ 1 → CentralIn S w' → w' ≠ 1 →
      ∃ d ∈ D, d⁻¹ * w * d = w') ∧
    (∀ β : X → X → ZMod 2,
      (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, β (a * b) c = β a c + β b c) →
      (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, β a (b * c) = β a b + β a c) →
      (∀ a ∈ S, β a a = 0) →
      (∀ a ∈ S, ∀ b : X, CentralIn S b → β a b = 0) →
      (∀ d ∈ D, ∀ a ∈ S, ∀ b ∈ S, β (d⁻¹ * a * d) (d⁻¹ * b * d) = β a b) →
      ∀ a ∈ S, ∀ b ∈ S, β a b = 0)
  center_card : 4 ≤ Nat.card {w : X // CentralIn S w}

theorem mem_commutator_sylow_of_mem_commutator {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (P : Sylow p G) {z : G} (hz : z ∈ Subgroup.center G)
    (hzP : z ∈ (P : Subgroup G)) (hzc : z ∈ commutator G) :
    z ∈ ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
  classical
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center G := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff.mp hzk g₀⁻¹, inv_mul_cancel_right]
  let φ : (P : Subgroup G) →* Abelianization (P : Subgroup G) := Abelianization.of
  have htr := MonoidHom.transfer_eq_pow φ z key
  have htriv : φ.transfer z = 1 :=
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker (φ.transfer) hzc)
  rw [htriv] at htr
  have hpow : (⟨z, hzP⟩ : (P : Subgroup G)) ^ (P : Subgroup G).index ∈
      commutator (P : Subgroup G) := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    have heq : (⟨z, hzP⟩ : (P : Subgroup G)) ^ (P : Subgroup G).index =
        ⟨z ^ (P : Subgroup G).index, MonoidHom.transfer_eq_pow_aux z key⟩ :=
      Subtype.ext (by simp)
    rw [heq]
    exact htr.symm
  have hcop : Nat.Coprime p (P : Subgroup G).index :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).mpr P.not_dvd_index
  have hgcd : ((P : Subgroup G).index).gcd (orderOf (⟨z, hzP⟩ : (P : Subgroup G))) = 1 :=
    (P.isPGroup'.orderOf_coprime hcop _).symm
  have h := (Subgroup.zpowers_le.mpr hpow) (mem_zpowers_pow_iff.mpr hgcd)
  have hmap := Subgroup.mem_map_of_mem (P : Subgroup G).subtype h
  rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hmap

theorem exists_ker_mul_mem_normalizer {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    [Fact p.Prime] (φ : G →* H) (P : Sylow p G) {g : G}
    (hg : φ g ∈ Subgroup.normalizer (((P : Subgroup G).map φ : Subgroup H) : Set H)) :
    ∃ k ∈ φ.ker, k * g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
  set L : Subgroup G := (P : Subgroup G) ⊔ φ.ker with hL
  have hPL : (P : Subgroup G) ≤ L := le_sup_left
  have hgPL : ((g • P : Sylow p G) : Subgroup G) ≤ L := by
    intro y hy
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have hy' : g⁻¹ * y * g ∈ (P : Subgroup G) := by
      simpa [MulAut.conj_apply] using hy
    have hφy : φ y ∈ (P : Subgroup G).map φ := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hg (φ (g⁻¹ * y * g))).mp
        (Subgroup.mem_map_of_mem φ hy')
      simpa [map_mul, map_inv, mul_assoc] using h1
    obtain ⟨s, hs, hsy⟩ := hφy
    have hk : s⁻¹ * y ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsy, inv_mul_cancel]
    have hy_eq : y = s * (s⁻¹ * y) := by group
    rw [hy_eq]
    exact Subgroup.mul_mem_sup hs hk
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L ((g • P).subtype hgPL) (P.subtype hPL)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hl
  have hlg : (l : G) * g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hl)
  obtain ⟨s, hs, k, hk, hsk⟩ := Subgroup.mem_sup_of_normal_right.mp l.2
  refine ⟨k, hk, ?_⟩
  have heq : k * g = s⁻¹ * ((l : G) * g) := by rw [← hsk]; group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer (Subgroup.inv_mem _ hs)) hlg

section Lift

variable {K : Type*} [Group K] {Z : Subgroup K}

theorem conj_eq_of_mk_eq_central (hZ : Z ≤ Subgroup.center K) {g g' : K}
    (h : (g : K ⧸ Z) = g') (x : K) : g' * x * g'⁻¹ = g * x * g⁻¹ := by
  rw [QuotientGroup.eq] at h
  have hc := Subgroup.mem_center_iff.mp (hZ h) x
  calc g' * x * g'⁻¹ = g * ((g⁻¹ * g') * x * (g⁻¹ * g')⁻¹) * g⁻¹ := by group
    _ = g * x * g⁻¹ := by rw [← hc, mul_inv_cancel_right]

theorem commutatorElement_mul_central_left {a b u : K} (hu : u ∈ Subgroup.center K) :
    ⁅a * u, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hu b
  rw [commutatorElement_def, commutatorElement_def]
  calc a * u * b * (a * u)⁻¹ * b⁻¹ = a * (u * b) * u⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * u) * u⁻¹ * a⁻¹ * b⁻¹ := by rw [← h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central_right {a b v : K} (hv : v ∈ Subgroup.center K) :
    ⁅a, b * v⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hv a⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * v) * a⁻¹ * (b * v)⁻¹ = a * b * (v * a⁻¹) * v⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * v) * v⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_eq_of_mk_eq_central (hZ : Z ≤ Subgroup.center K) {a a' b b' : K}
    (ha : (a : K ⧸ Z) = a') (hb : (b : K ⧸ Z) = b') : ⁅a', b'⁆ = ⁅a, b⁆ := by
  rw [QuotientGroup.eq] at ha hb
  have ha' : a' = a * (a⁻¹ * a') := by group
  have hb' : b' = b * (b⁻¹ * b') := by group
  rw [ha', hb', commutatorElement_mul_central_left (hZ ha),
    commutatorElement_mul_central_right (hZ hb)]

variable (Z) in
@[expose] noncomputable def quotConj (d : K ⧸ Z) (x : K) : K :=
  Quotient.out d * x * (Quotient.out d)⁻¹

theorem quotConj_eq (hZ : Z ≤ Subgroup.center K) {g : K} {d : K ⧸ Z}
    (h : (g : K ⧸ Z) = d) (x : K) : quotConj Z d x = g * x * g⁻¹ :=
  conj_eq_of_mk_eq_central hZ (h.trans (QuotientGroup.out_eq' d).symm) x

theorem quotConj_one [Z.Normal] (hZ : Z ≤ Subgroup.center K) (x : K) : quotConj Z 1 x = x := by
  rw [quotConj_eq hZ (g := 1) (d := 1) (QuotientGroup.mk_one _), one_mul, inv_one, mul_one]

theorem quotConj_mul [Z.Normal] (hZ : Z ≤ Subgroup.center K) (d₁ d₂ : K ⧸ Z) (x : K) :
    quotConj Z (d₁ * d₂) x = quotConj Z d₁ (quotConj Z d₂ x) := by
  have h : ((Quotient.out d₁ * Quotient.out d₂ : K) : K ⧸ Z) = d₁ * d₂ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
  rw [quotConj_eq hZ h, quotConj, quotConj]
  group

theorem quotConj_mul_left (d : K ⧸ Z) (x y : K) :
    quotConj Z d (x * y) = quotConj Z d x * quotConj Z d y := by
  simp only [quotConj]
  group

theorem quotConj_commutatorElement (d : K ⧸ Z) (x y : K) :
    quotConj Z d ⁅x, y⁆ = ⁅quotConj Z d x, quotConj Z d y⁆ := by
  simp only [quotConj, commutatorElement_def]
  group

theorem quotConj_of_mem_center (d : K ⧸ Z) {x : K} (hx : x ∈ Subgroup.center K) :
    quotConj Z d x = x := by
  rw [quotConj, Subgroup.mem_center_iff.mp hx, mul_inv_cancel_right]

theorem mk_quotConj [Z.Normal] (d : K ⧸ Z) (x : K) :
    ((quotConj Z d x : K) : K ⧸ Z) = d * (x : K ⧸ Z) * d⁻¹ := by
  rw [quotConj, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.out_eq']

@[expose, instance_reducible] noncomputable def quotConjAction [Z.Normal]
    (hZ : Z ≤ Subgroup.center K) (D : Subgroup (K ⧸ Z)) (W : Subgroup K)
    (hDW : ∀ d ∈ D, ∀ w ∈ W, quotConj Z d w ∈ W) : MulDistribMulAction D W where
  smul d w := ⟨quotConj Z d w, hDW d d.2 w w.2⟩
  one_smul w := Subtype.ext (quotConj_one hZ (w : K))
  mul_smul d₁ d₂ w := Subtype.ext (quotConj_mul hZ (d₁ : K ⧸ Z) d₂ (w : K))
  smul_mul d w₁ w₂ := Subtype.ext (quotConj_mul_left (d : K ⧸ Z) w₁ w₂)
  smul_one d := Subtype.ext (by
    change quotConj Z (d : K ⧸ Z) 1 = 1
    rw [quotConj, mul_one, mul_inv_cancel])

end Lift

section Norm

variable {D W : Type*} [Group D] [Fintype D] [CommGroup W] [MulDistribMulAction D W]

variable (D W) in
@[expose] noncomputable def orbitNorm : W →* W where
  toFun w := ∏ d : D, d • w
  map_one' := by simp only [smul_one, Finset.prod_const_one]
  map_mul' w w' := by simp only [smul_mul', Finset.prod_mul_distrib]

theorem orbitNorm_apply (w : W) : orbitNorm D W w = ∏ d : D, d • w := rfl

theorem smul_orbitNorm (d₀ : D) (w : W) : d₀ • orbitNorm D W w = orbitNorm D W w := by
  rw [orbitNorm_apply, Finset.smul_prod']
  exact Fintype.prod_equiv (Equiv.mulLeft d₀) _ _ fun d => (mul_smul d₀ d w).symm

theorem orbitNorm_smul (d₀ : D) (w : W) : orbitNorm D W (d₀ • w) = orbitNorm D W w := by
  simp only [orbitNorm_apply, ← mul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight d₀) _ _ fun d => rfl

theorem orbitNorm_of_forall_smul_eq {w : W} (hw : ∀ d : D, d • w = w) :
    orbitNorm D W w = w ^ Fintype.card D := by
  simp only [orbitNorm_apply, hw, Finset.prod_const, Finset.card_univ]

end Norm

section Indicator

variable {G : Type*} [Group G]

@[expose] noncomputable def neOneInd (s : G) : ZMod 2 := by
  classical
  exact if s = 1 then 0 else 1

theorem neOneInd_one : neOneInd (1 : G) = 0 := by
  simp [neOneInd]

theorem eq_one_of_neOneInd_eq_zero {s : G} (h : neOneInd s = 0) : s = 1 := by
  by_contra hs
  simp [neOneInd, hs] at h

theorem neOneInd_mul {s t : G} (h : s = 1 ∨ t = 1 ∨ s = t) (hs : s * s = 1) :
    neOneInd (s * t) = neOneInd s + neOneInd t := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  rcases h with rfl | rfl | rfl
  · rw [one_mul, neOneInd_one, zero_add]
  · rw [mul_one, neOneInd_one, add_zero]
  · rw [hs, neOneInd_one, h2]

end Indicator

end CFSG.Timmesfeld.Bridge

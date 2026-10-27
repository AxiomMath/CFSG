module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Head
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Tensor

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

section Coord

variable {G : Type} [Group G] {V Z : Subgroup G} {K : Type} [Field K] [(Z.subgroupOf V).Normal]

@[expose] def cmat (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K)) (v : ↥V) :
    Matrix (Fin 2) (Fin 2) K :=
  toMat K (secVec ψ v)

theorem cmat_mul (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K)) (v w : ↥V) :
    cmat ψ (v * w) = cmat ψ v + cmat ψ w := by
  unfold cmat
  rw [secVec_mul, map_add]

theorem cmat_inv (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K)) (v : ↥V) :
    cmat ψ v⁻¹ = -cmat ψ v := by
  unfold cmat
  rw [secVec_inv, map_neg]

theorem cmat_eq_zero_iff (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (v : ↥V) : cmat ψ v = 0 ↔ (v : G) ∈ Z := by
  unfold cmat
  rw [← secVec_eq_zero_iff ψ v]
  constructor
  · intro h
    exact (toMat K).injective (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

theorem cmat_eq_iff (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (v w : ↥V) : cmat ψ v = cmat ψ w ↔ (v : G) * (w : G)⁻¹ ∈ Z := by
  rw [← secVec_eq_iff ψ v w]
  unfold cmat
  exact (toMat K).injective.eq_iff

theorem cmat_conj {R : Subgroup G}
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (s : ↥R) (v w : ↥V) (hw : (w : G) = (s : G) * v * (s : G)⁻¹) :
    cmat ψ w = Ψ K (φ s) (cmat ψ v) := by
  unfold cmat
  rw [Ψ_apply, LinearEquiv.symm_apply_apply]
  exact congrArg (toMat K) (hψ s v w hw)

@[expose] def coordSub (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (T : Submodule K (Matrix (Fin 2) (Fin 2) K)) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ V, cmat ψ ⟨x, hx⟩ ∈ T}
  mul_mem' := by
    rintro a b ⟨ha, haT⟩ ⟨hb, hbT⟩
    refine ⟨V.mul_mem ha hb, ?_⟩
    have h : cmat ψ (⟨a, ha⟩ * ⟨b, hb⟩ : ↥V) = cmat ψ ⟨a, ha⟩ + cmat ψ ⟨b, hb⟩ :=
      cmat_mul ψ _ _
    exact h ▸ T.add_mem haT hbT
  one_mem' := ⟨V.one_mem, by
    have h : cmat ψ (1 : ↥V) = 0 := (cmat_eq_zero_iff ψ 1).mpr Z.one_mem
    exact h ▸ T.zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, haT⟩
    refine ⟨V.inv_mem ha, ?_⟩
    have h : cmat ψ (⟨a, ha⟩⁻¹ : ↥V) = -cmat ψ ⟨a, ha⟩ := cmat_inv ψ _
    exact h ▸ T.neg_mem haT

theorem conjSubgroup_le_Uline {B Y : Subgroup G} {y x : G} (hy : y ∈ Y)
    (hx : x ∈ conjSubgroup y B) : x ∈ Uline Z B Y :=
  Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem y (Subgroup.mem_iSup_of_mem hy hx))

theorem exists_mem_conjSubgroup_sup_of_cmat_mem_range {R : Subgroup G}
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G)) {Y B : Subgroup G} (hYR : Y ≤ R)
    (hBV : B ≤ V) (u : Fin 2 ⊕ Fin 2 → K)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    (hH : ∀ h, h ∈ H ↔ ∃ s : ↥R, (s : G) ∈ Y ∧ Ψ K (φ s) = h)
    [Finite K] [CharP K 2]
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} {w₀ : Fin 2 → K} (hA : ActsNat H Φ)
    (hw₀ : w₀ ≠ 0) (hu : toMat K u = Φ w₀) {x : G} (hxV : x ∈ V)
    (hxΦ : cmat ψ ⟨x, hxV⟩ ∈ Set.range Φ) :
    ∃ y ∈ Y, x ∈ (conjSubgroup y B ⊔ Z : Subgroup G) := by
  obtain ⟨w, hw⟩ := hxΦ
  by_cases hw0 : w = 0
  · refine ⟨1, Y.one_mem, Subgroup.mem_sup_right ?_⟩
    have h : cmat ψ ⟨x, hxV⟩ = 0 := by rw [← hw, hw0, map_zero]
    exact (cmat_eq_zero_iff ψ _).mp h
  · obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hw₀ hw0
    obtain ⟨h, hh, hact⟩ := hA.lift g
    obtain ⟨s, hsY, hsh⟩ := (hH h).mp hh
    obtain ⟨b, hbB, hbu⟩ := (hBiff u).mpr ⟨1, (one_smul K u).symm⟩
    have hsR : (s : G) ∈ R := hYR hsY
    have hbV : (b : G) ∈ V := hBV hbB
    have hx'V : (s : G) * b * (s : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hsR) (b : G)).mp hbV
    have hcb : cmat ψ b = Φ w₀ := by
      unfold cmat
      rw [hbu, hu]
    have hcm : cmat ψ ⟨(s : G) * b * (s : G)⁻¹, hx'V⟩ = cmat ψ ⟨x, hxV⟩ := by
      rw [cmat_conj ψ φ hψ s b ⟨(s : G) * b * (s : G)⁻¹, hx'V⟩ rfl, hcb, hsh,
        hact w₀, hg, hw]
    have hz : x * ((s : G) * b * (s : G)⁻¹)⁻¹ ∈ Z :=
      (cmat_eq_iff ψ ⟨x, hxV⟩ ⟨(s : G) * b * (s : G)⁻¹, hx'V⟩).mp hcm.symm
    have hx'B : (s : G) * b * (s : G)⁻¹ ∈ conjSubgroup (s : G) B := by
      rw [mem_conjSubgroup]
      have e : (s : G)⁻¹ * ((s : G) * b * (s : G)⁻¹) * (s : G) = b := by group
      rw [e]
      exact hbB
    have e : x = (x * ((s : G) * b * (s : G)⁻¹)⁻¹) * ((s : G) * b * (s : G)⁻¹) := by group
    refine ⟨(s : G), hsY, ?_⟩
    rw [sup_comm, e]
    exact Subgroup.mul_mem_sup hz hx'B

theorem uline_mem_iff {R : Subgroup G}
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G)) {Y B : Subgroup G} (hYR : Y ≤ R)
    (hZV : Z ≤ V) (hBV : B ≤ V) (u : Fin 2 ⊕ Fin 2 → K)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    (hH : ∀ h, h ∈ H ↔ ∃ s : ↥R, (s : G) ∈ Y ∧ Ψ K (φ s) = h)
    [Finite K] [CharP K 2]
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} {w₀ : Fin 2 → K} (hA : ActsNat H Φ)
    (hw₀ : w₀ ≠ 0) (hu : toMat K u = Φ w₀) (x : G) :
    x ∈ Uline Z B Y ↔ ∃ hx : x ∈ V, cmat ψ ⟨x, hx⟩ ∈ Set.range Φ := by
  have hle : Uline Z B Y ≤ coordSub ψ (LinearMap.range Φ) := by
    refine sup_le ?_ (iSup₂_le fun y hy => ?_)
    · intro z hz
      refine ⟨hZV hz, ?_⟩
      have h : cmat ψ ⟨z, hZV hz⟩ = 0 := (cmat_eq_zero_iff ψ _).mpr hz
      rw [h]
      exact (LinearMap.range Φ).zero_mem
    · intro x hx
      rw [mem_conjSubgroup] at hx
      have hyR : y ∈ R := hYR hy
      have hbV : y⁻¹ * x * y ∈ V := hBV hx
      have hxe : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      have hxV : x ∈ V := by
        rw [hxe]
        exact (Subgroup.mem_normalizer_iff.mp (hnorm hyR) _).mp hbV
      refine ⟨hxV, ?_⟩
      have h1 := cmat_conj ψ φ hψ ⟨y, hyR⟩ ⟨y⁻¹ * x * y, hbV⟩ ⟨x, hxV⟩ hxe
      rw [h1]
      obtain ⟨c, hc⟩ := (hBiff (secVec ψ ⟨y⁻¹ * x * y, hbV⟩)).mp ⟨⟨y⁻¹ * x * y, hbV⟩, hx, rfl⟩
      have h2 : cmat ψ ⟨y⁻¹ * x * y, hbV⟩ = Φ (c • w₀) := by
        unfold cmat
        rw [hc, map_smul, hu, map_smul]
      rw [h2]
      obtain ⟨g, hg⟩ := hA.act (Ψ K (φ ⟨y, hyR⟩)) ((hH _).mpr ⟨⟨y, hyR⟩, hy, rfl⟩)
      rw [hg]
      exact ⟨_, rfl⟩
  constructor
  · intro hx
    obtain ⟨hxV, hxT⟩ := hle hx
    exact ⟨hxV, hxT⟩
  · rintro ⟨hxV, w, hw⟩
    obtain ⟨y, hy, hxy⟩ := exists_mem_conjSubgroup_sup_of_cmat_mem_range
      ψ φ hψ hnorm hYR hBV u hBiff hH hA hw₀ hu hxV ⟨w, hw⟩
    exact (sup_le (fun c hc => conjSubgroup_le_Uline hy hc)
      (le_sup_left : Z ≤ Uline Z B Y)) hxy

theorem uline_cover {R : Subgroup G}
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G)) {Y B : Subgroup G} (hYR : Y ≤ R)
    (hZV : Z ≤ V) (hBV : B ≤ V) (u : Fin 2 ⊕ Fin 2 → K)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    (hH : ∀ h, h ∈ H ↔ ∃ s : ↥R, (s : G) ∈ Y ∧ Ψ K (φ s) = h)
    [Finite K] [CharP K 2]
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} {w₀ : Fin 2 → K} (hA : ActsNat H Φ)
    (hw₀ : w₀ ≠ 0) (hu : toMat K u = Φ w₀) :
    ∀ x ∈ Uline Z B Y, ∃ y ∈ Y, x ∈ (conjSubgroup y B ⊔ Z : Subgroup G) := by
  intro x hx
  obtain ⟨hxV, hxΦ⟩ := (uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hH hA hw₀ hu x).mp hx
  exact exists_mem_conjSubgroup_sup_of_cmat_mem_range ψ φ hψ hnorm hYR hBV u hBiff hH hA
    hw₀ hu hxV hxΦ

theorem uline_card [Finite G] {R : Subgroup G}
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G)) {Y B : Subgroup G} (hYR : Y ≤ R)
    (hZV : Z ≤ V) (hBV : B ≤ V) (u : Fin 2 ⊕ Fin 2 → K)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    (hH : ∀ h, h ∈ H ↔ ∃ s : ↥R, (s : G) ∈ Y ∧ Ψ K (φ s) = h)
    [Finite K] [CharP K 2]
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} {w₀ : Fin 2 → K} (hA : ActsNat H Φ)
    (hw₀ : w₀ ≠ 0) (hu : toMat K u = Φ w₀) :
    Nat.card ↥(Uline Z B Y) = Nat.card Z * Nat.card K ^ 2 := by
  have hmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hH hA hw₀ hu
  have hUV : Uline Z B Y ≤ V := fun x hx => ((hmem x).mp hx).1
  have hinj : Function.Injective (fun w : Fin 2 → K => (toMat K).symm (Φ w)) :=
    (toMat K).symm.injective.comp hA.inj
  have hS : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ w : ↥V, (w : G) ∈ Uline Z B Y ∧ secVec ψ w = x) ↔
        x ∈ Set.range (fun w : Fin 2 → K => (toMat K).symm (Φ w)) := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwV, w', hw'⟩ := (hmem w).mp hw
      refine ⟨w', ?_⟩
      show (toMat K).symm (Φ w') = secVec ψ w
      rw [hw']
      exact (toMat K).symm_apply_apply _
    · rintro ⟨w', rfl⟩
      obtain ⟨v, hv⟩ := exists_secVec_eq ψ ((toMat K).symm (Φ w'))
      refine ⟨v, (hmem v).mpr ⟨v.2, w', ?_⟩, hv⟩
      show Φ w' = cmat ψ ⟨v, v.2⟩
      unfold cmat
      rw [hv, LinearEquiv.apply_symm_apply]
  refine (card_eq_of_secVec (W := Uline Z B Y) ψ le_sup_left hUV _ hS).trans ?_
  rw [Nat.card_range_of_injective hinj, Nat.card_fun, Nat.card_fin]

theorem comm_mem_Z_of_secVec
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K)) (x y : ↥V) :
    ⁅(x : G), (y : G)⁆ ∈ Z := by
  have h : secVec ψ (x * y * x⁻¹ * y⁻¹) = 0 := by
    simp only [secVec_mul, secVec_inv]
    abel
  have := (secVec_eq_zero_iff ψ _).mp h
  simpa [commutatorElement_def] using this

theorem sq_mem_Z_of_secVec [CharP K 2]
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K)) (x : ↥V) :
    (x : G) ^ 2 ∈ Z := by
  have h : secVec ψ (x * x) = 0 := by
    rw [secVec_mul]
    ext i
    simp [CharTwo.add_self_eq_zero]
  have := (secVec_eq_zero_iff ψ _).mp h
  simpa [pow_two] using this

theorem uline_irred [Finite G] {R : Subgroup G}
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G)) {Y B : Subgroup G} (hYR : Y ≤ R)
    (hZV : Z ≤ V) (hBV : B ≤ V) (u : Fin 2 ⊕ Fin 2 → K)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    (hH : ∀ h, h ∈ H ↔ ∃ s : ↥R, (s : G) ∈ Y ∧ Ψ K (φ s) = h)
    [Finite K] [CharP K 2]
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} {w₀ : Fin 2 → K} (hA : ActsNat H Φ)
    (hw₀ : w₀ ≠ 0) (hu : toMat K u = Φ w₀)
    (hbnz : ∃ b ∈ B, b ∉ Z) : IsIrredModule Y (Uline Z B Y) Z := by
  have hmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hH hA hw₀ hu
  have hUV : Uline Z B Y ≤ V := fun x hx => ((hmem x).mp hx).1
  refine ⟨fun x hx y hy => comm_mem_Z_of_secVec ψ ⟨x, hUV hx⟩ ⟨y, hUV hy⟩,
    fun x hx => sq_mem_Z_of_secVec ψ ⟨x, hUV hx⟩, ?_, ?_⟩
  · refine lt_of_le_of_ne le_sup_left fun h => ?_
    obtain ⟨b, hbB, hbZ⟩ := hbnz
    apply hbZ
    have hbU : b ∈ Uline Z B Y := conjSubgroup_le_Uline Y.one_mem (by
      rw [mem_conjSubgroup]
      simpa using hbB)
    rw [← h] at hbU
    exact hbU
  · intro A hZA hAU hAinv
    have hcoord : ∀ a : ↥V, (a : G) ∈ A → ∃ w, cmat ψ a = Φ w := by
      intro a haA
      obtain ⟨hV', w, hw⟩ := (hmem a).mp (hAU haA)
      exact ⟨w, hw.symm⟩
    rcases hA.irred {z | ∃ a : ↥V, (a : G) ∈ A ∧ cmat ψ a = z}
      (by
        rintro _ ⟨a, haA, rfl⟩
        exact hcoord a haA)
      (by
        rintro h hh _ ⟨a, haA, rfl⟩
        obtain ⟨s, hsY, rfl⟩ := (hH h).mp hh
        have hsR : (s : G) ∈ R := s.2
        have haV : (s : G) * a * (s : G)⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (hnorm hsR) a).mp a.2
        refine ⟨⟨(s : G) * a * (s : G)⁻¹, haV⟩, ?_, ?_⟩
        · have h1 : (s : G) * a * (s : G)⁻¹ ∈ conjSubgroup (s : G) A := by
            rw [mem_conjSubgroup]
            have e : (s : G)⁻¹ * ((s : G) * a * (s : G)⁻¹) * (s : G) = a := by group
            rw [e]
            exact haA
          rw [hAinv (s : G) hsY] at h1
          exact h1
        · exact cmat_conj ψ φ hψ s a ⟨(s : G) * a * (s : G)⁻¹, haV⟩ rfl) with h0 | hall
    · left
      refine le_antisymm (fun a haA => ?_) hZA
      have haV : a ∈ V := ((hmem a).mp (hAU haA)).1
      exact (cmat_eq_zero_iff ψ ⟨a, haV⟩).mp (h0 _ ⟨⟨a, haV⟩, haA, rfl⟩)
    · right
      refine le_antisymm hAU (fun x hx => ?_)
      obtain ⟨hxV, w, hw⟩ := (hmem x).mp hx
      by_cases hw0 : w = 0
      · have h : cmat ψ ⟨x, hxV⟩ = 0 := by rw [← hw, hw0, map_zero]
        exact hZA ((cmat_eq_zero_iff ψ _).mp h)
      · obtain ⟨a, haA, hcm⟩ := hall w hw0
        have hz : (a : G) * x⁻¹ ∈ Z := (cmat_eq_iff ψ a ⟨x, hxV⟩).mp (hcm.trans hw)
        have e : x = ((a : G) * x⁻¹)⁻¹ * a := by group
        rw [e]
        exact A.mul_mem (A.inv_mem (hZA hz)) haA

theorem exists_stabSub {Y : Subgroup G} (S : Set G)
    (hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y * z * y⁻¹ ∈ Z) :
    ∃ Y₀ : Subgroup G, Y₀ ≤ Y ∧ ∀ y, y ∈ Y₀ ↔ y ∈ Y ∧ ∀ b ∈ S, ⁅y, b⁆ ∈ Z := by
  refine ⟨{ carrier := {y | y ∈ Y ∧ ∀ b ∈ S, ⁅y, b⁆ ∈ Z}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun y hy => hy.1, fun y => Iff.rfl⟩
  · rintro y y' ⟨hy, hyS⟩ ⟨hy', hy'S⟩
    refine ⟨Y.mul_mem hy hy', fun b hb => ?_⟩
    have e : ⁅y * y', b⁆ = y * ⁅y', b⁆ * y⁻¹ * ⁅y, b⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Z.mul_mem (hYZ y hy _ (hy'S b hb)) (hyS b hb)
  · refine ⟨Y.one_mem, fun b _ => ?_⟩
    rw [show ⁅(1 : G), b⁆ = 1 by simp [commutatorElement_def]]
    exact Z.one_mem
  · rintro y ⟨hy, hyS⟩
    refine ⟨Y.inv_mem hy, fun b hb => ?_⟩
    have h1 : ⁅y⁻¹, b⁆ = (y⁻¹ * ⁅y, b⁆ * y)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    refine Z.inv_mem ?_
    have := hYZ y⁻¹ (Y.inv_mem hy) _ (hyS b hb)
    simpa using this

theorem uline_fixed [Finite G] {R : Subgroup G}
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G)) {Y B : Subgroup G} (hYR : Y ≤ R)
    (hZV : Z ≤ V) (hBV : B ≤ V) (u : Fin 2 ⊕ Fin 2 → K)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    (hH : ∀ h, h ∈ H ↔ ∃ s : ↥R, (s : G) ∈ Y ∧ Ψ K (φ s) = h)
    [Finite K] [CharP K 2]
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} {w₀ : Fin 2 → K} (hA : ActsNat H Φ)
    (hw₀ : w₀ ≠ 0) (hu : toMat K u = Φ w₀)
    (hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y * z * y⁻¹ ∈ Z) :
    ∃ Y₀ : Subgroup G, Y₀ ≤ Y ∧ (∀ b ∈ B, ∀ y ∈ Y₀, ⁅y, b⁆ ∈ Z) ∧
      ∀ x ∈ Uline Z B Y, (∀ y ∈ Y₀, ⁅y, x⁆ ∈ Z) → x ∈ (B ⊔ Z : Subgroup G) := by
  obtain ⟨Y₀, hY₀Y, hY₀⟩ := exists_stabSub (Y := Y) (Z := Z) (B : Set G) hYZ
  refine ⟨Y₀, hY₀Y, fun b hb y hy => ((hY₀ y).mp hy).2 b hb, ?_⟩
  intro x hx hfixx
  have hmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hH hA hw₀ hu
  obtain ⟨hxV, w, hw⟩ := (hmem x).mp hx
  have hcomm := secVec_comm φ ψ hψ hnorm
  have hfix : ∀ h ∈ H, h (Φ w₀) = Φ w₀ → h (Φ w) = Φ w := by
    intro h hh hfixh
    obtain ⟨s, hsY, rfl⟩ := (hH h).mp hh
    have hφu : (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u = u := by
      rw [← hu] at hfixh
      rw [Ψ_apply, LinearEquiv.symm_apply_apply] at hfixh
      exact (toMat K).injective hfixh
    have hsY₀ : (s : G) ∈ Y₀ := by
      refine (hY₀ _).mpr ⟨hsY, fun b hb => ?_⟩
      have hbV := hBV hb
      obtain ⟨c, hc⟩ := (hBiff (secVec ψ ⟨b, hbV⟩)).mp ⟨⟨b, hbV⟩, hb, rfl⟩
      refine (secVec_eq_zero_iff ψ ⟨⁅(s : G), b⁆, comm_mem_of_le_normalizer hnorm s ⟨b, hbV⟩⟩).mp ?_
      rw [hcomm s ⟨b, hbV⟩, hc, Matrix.mulVec_smul, hφu, sub_self]
    have h2 := hfixx (s : G) hsY₀
    have h3 := (secVec_eq_zero_iff ψ
      ⟨⁅(s : G), x⁆, comm_mem_of_le_normalizer hnorm s ⟨x, hxV⟩⟩).mpr h2
    rw [hcomm s ⟨x, hxV⟩, sub_eq_zero] at h3
    rw [hw]
    unfold cmat
    rw [Ψ_apply, LinearEquiv.symm_apply_apply, h3]
  obtain ⟨c, hc⟩ := hA.fixed hw₀ hfix
  have hcm : cmat ψ ⟨x, hxV⟩ = toMat K (c • u) := by
    rw [← hw, hc, map_smul, map_smul, hu]
  have hsx : secVec ψ ⟨x, hxV⟩ = c • u := (toMat K).injective hcm
  obtain ⟨b, hbB, hbv⟩ := (hBiff (c • u)).mpr ⟨c, rfl⟩
  have hz : x * (b : G)⁻¹ ∈ Z := (secVec_eq_iff ψ ⟨x, hxV⟩ b).mp (hsx.trans hbv.symm)
  have e : x = (x * (b : G)⁻¹) * (b : G) := by group
  rw [sup_comm, e]
  exact Subgroup.mul_mem_sup hz hbB

end Coord

end HS9

open HS9

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec9_coord (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (_ : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K)
      (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (Fin 2 ⊕ Fin 2 → K))
      (u : Fin 2 ⊕ Fin 2 → K),
      Nat.card K = Nat.card Z ∧
      ((Ψ K).toMonoidHom.comp φ).range = (rho' K).range ∧
      φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
      Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) ∧
      (∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
        (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            Multiplicative.toAdd (ψ (QuotientGroup.mk v))) ∧
      (∀ x : Fin 2 ⊕ Fin 2 → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
          ∃ c : K, x = c • u) ∧
      (∀ x : Fin 2 ⊕ Fin 2 → K, (∃ w : ↥(Vt M (LB M Q B) B Z t),
        (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔
        polar (quadPlus 2 K) u x = 0) ∧
      (toMat K u).det = 0 ∧ toMat K u ≠ 0 := by
  classical
  have hs5 := hs.toSec5
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B := sec9_notQB h34 hs
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hs.plus4
  haveI := hn
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four hq4
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have h3 : 3 ≤ Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  obtain ⟨u, hQu, hu0, hBiff, hW, -⟩ := hc.omega_points_flag h34 hs5 hnotQB hK
    (ElemMatrixIso.ofStated (coe_quadPlus 2 K)
      (Classify.commutator_orthogonalGroup_quadPlus_two K hc0 hc1)) hQ h3
    (addCommutantScalar_statedOmegaPlus_two ⟨c0, hc0, hc1⟩) φ hφ hker ψ hψ
  have hdet : (toMat K u).det = 0 := by
    rw [det_toMat]
    exact (congrFun (coe_quadPlus 2 K) u).symm.trans hQu
  have hu0' : toMat K u ≠ 0 := fun h => hu0 ((toMat K).injective (by rw [h, map_zero]))
  have hrange : ((Ψ K).toMonoidHom.comp φ).range = (rho' K).range := by
    have h1 : ((Ψ K).toMonoidHom.comp φ).range = φ.range.map (Ψ K).toMonoidHom :=
      MonoidHom.range_comp _ _
    rw [h1, hφ, map_statedOmega, commutator_eq_range hq4]
  exact ⟨K, fK, finK, ‹CharP K 2›, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, hW,
    hdet, hu0'⟩

theorem sec97_HY_ne_bot {R X Y CN : Subgroup G} {K : Type} [Field K]
    (φ'' : ↥R →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K))
    (hYR : Y ≤ R) (hhead : CN ≤ X) (hXYQ : X ⊓ Y = Q)
    (hQY_idx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1))
    (hq4 : 4 ≤ Nat.card Z)
    (hφ''1 : ∀ s : ↥R, φ'' s = 1 ↔ (s : G) ∈ CN) :
    (Y.subgroupOf R).map φ'' ≠ ⊥ := by
  intro hbot
  have hYN : Y ≤ CN := by
    intro y hy
    have hyR : y ∈ R := hYR hy
    have h1 : φ'' ⟨y, hyR⟩ = 1 := by
      have hmem : φ'' ⟨y, hyR⟩ ∈ (Y.subgroupOf R).map φ'' :=
        Subgroup.mem_map.mpr ⟨⟨y, hyR⟩, hy, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact (hφ''1 _).mp h1
  have hYQ : Y ≤ Q := by
    intro y hy
    rw [← hXYQ]
    exact ⟨hhead (hYN hy), hy⟩
  have h1 : Q.relIndex Y = 1 := Subgroup.relIndex_eq_one.mpr hYQ
  rw [hQY_idx] at h1
  have hq4' : 4 ≤ Nat.card Z := hq4
  have := Nat.eq_one_of_mul_eq_one_right h1
  omega

theorem sec97_HY_card_le {R Y Q CN : Subgroup G} {K : Type} [Field K] [Finite K]
    (φ'' : ↥R →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K))
    (hYR : Y ≤ R) (hQCN : Q ≤ CN)
    (hφ''1 : ∀ s : ↥R, φ'' s = 1 ↔ (s : G) ∈ CN)
    (hQY_idx : Q.relIndex Y = Nat.card K * (Nat.card K ^ 2 - 1)) :
    Nat.card ↥((Y.subgroupOf R).map φ'') ≤ Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  haveI : Finite (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    Finite.of_injective (fun f => (f : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K))
      (fun f g h => LinearEquiv.ext (congrFun h))
  let f : ↥Y →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    φ''.comp (Subgroup.inclusion hYR)
  have hrangef : f.range = (Y.subgroupOf R).map φ'' := by
    ext h
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨y, hYR y.2⟩, y.2, rfl⟩
    · intro hh
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hh
      exact ⟨⟨s, hs⟩, rfl⟩
  have hQker : Q.subgroupOf Y ≤ f.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    show φ'' ⟨(y : G), hYR y.2⟩ = 1
    exact (hφ''1 _).mpr (hQCN (Subgroup.mem_subgroupOf.mp hy))
  rw [← hrangef, ← Subgroup.index_ker f]
  have hdvd := Subgroup.index_dvd_of_le hQker
  have hpos : 0 < (Q.subgroupOf Y).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  calc f.ker.index ≤ (Q.subgroupOf Y).index := Nat.le_of_dvd hpos hdvd
    _ = Nat.card K * (Nat.card K ^ 2 - 1) := hQY_idx

theorem sec97_HX_ne_bot {R X Y : Subgroup G} {K : Type} [Field K] [Finite K]
    (φ'' : ↥R →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K))
    (hrange : φ''.range = (rho' K).range)
    (hdec : ∀ r ∈ R, ∃ x ∈ X, ∃ y ∈ Y, x * y = r)
    (hXR : X ≤ R) (hYR : Y ≤ R)
    (hcardRange : Nat.card (rho' K).range =
      Nat.card K * (Nat.card K ^ 2 - 1) * (Nat.card K * (Nat.card K ^ 2 - 1)))
    (hcardHY : Nat.card ↥((Y.subgroupOf R).map φ'') ≤ Nat.card K * (Nat.card K ^ 2 - 1))
    (hq4 : 4 ≤ Nat.card K) :
    (X.subgroupOf R).map φ'' ≠ ⊥ := by
  haveI : Finite (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    Finite.of_injective (fun f => (f : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K))
      (fun f g h => LinearEquiv.ext (congrFun h))
  intro hbot
  have hle : (rho' K).range ≤ (Y.subgroupOf R).map φ'' := by
    rw [← hrange]
    rintro _ ⟨r, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hdec r.1 r.2
    have hxR : x ∈ R := hXR hx
    have hyR : y ∈ R := hYR hy
    have hr : r = ⟨x, hxR⟩ * ⟨y, hyR⟩ := Subtype.ext hxy.symm
    have hx1 : φ'' ⟨x, hxR⟩ = 1 := by
      have hmem : φ'' ⟨x, hxR⟩ ∈ (X.subgroupOf R).map φ'' :=
        Subgroup.mem_map.mpr ⟨⟨x, hxR⟩, hx, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [hr, map_mul, hx1, one_mul]
    exact Subgroup.mem_map.mpr ⟨⟨y, hyR⟩, hy, rfl⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [hcardRange] at h1
  have h16 : 16 ≤ Nat.card K ^ 2 := by nlinarith [hq4]
  have hpos : 2 ≤ Nat.card K * (Nat.card K ^ 2 - 1) := by
    have : 1 ≤ Nat.card K ^ 2 - 1 := by omega
    nlinarith
  nlinarith [hcardHY, hq4]

theorem sec97_normal_comm {R X Y Q CN : Subgroup G} {K : Type} [Field K]
    (φ'' : ↥R →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K))
    (hrange : φ''.range = (rho' K).range)
    (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hQCN : Q ≤ CN) (hcomm : ∀ a ∈ X, ∀ y ∈ Y, ⁅a, y⁆ ∈ Q)
    (hφ''1 : ∀ s : ↥R, φ'' s = 1 ↔ (s : G) ∈ CN) :
    (∀ g ∈ (rho' K).range, ∀ h ∈ (Y.subgroupOf R).map φ'',
      g * h * g⁻¹ ∈ (Y.subgroupOf R).map φ'') ∧
    (∀ g ∈ (rho' K).range, ∀ h ∈ (X.subgroupOf R).map φ'',
      g * h * g⁻¹ ∈ (X.subgroupOf R).map φ'') ∧
    (∀ x ∈ (X.subgroupOf R).map φ'', ∀ y ∈ (Y.subgroupOf R).map φ'', x * y = y * x) := by
  have hnY : ∀ g ∈ (rho' K).range, ∀ h ∈ (Y.subgroupOf R).map φ'',
      g * h * g⁻¹ ∈ (Y.subgroupOf R).map φ'' := by
    intro g hg h hh
    rw [← hrange] at hg
    obtain ⟨r, rfl⟩ := hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨r * y * r⁻¹, ?_, by simp [map_mul, map_inv]⟩
    show ((r : G) * (y : G) * (r : G)⁻¹) ∈ Y
    exact (Subgroup.mem_normalizer_iff.mp (hRY r.2) y).mp hy
  have hnX : ∀ g ∈ (rho' K).range, ∀ h ∈ (X.subgroupOf R).map φ'',
      g * h * g⁻¹ ∈ (X.subgroupOf R).map φ'' := by
    intro g hg h hh
    rw [← hrange] at hg
    obtain ⟨r, rfl⟩ := hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨r * y * r⁻¹, ?_, by simp [map_mul, map_inv]⟩
    show ((r : G) * (y : G) * (r : G)⁻¹) ∈ X
    exact (Subgroup.mem_normalizer_iff.mp (hRX r.2) y).mp hy
  have hcXY : ∀ x ∈ (X.subgroupOf R).map φ'', ∀ y ∈ (Y.subgroupOf R).map φ'',
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hq : ((a * b * a⁻¹ * b⁻¹ : ↥R) : G) ∈ CN := by
      have h1 : ((a * b * a⁻¹ * b⁻¹ : ↥R) : G) = ⁅(a : G), (b : G)⁆ := by
        simp [commutatorElement_def]
      rw [h1]
      exact hQCN (hcomm a ha b hb)
    have h2 : φ'' (a * b * a⁻¹ * b⁻¹) = 1 := (hφ''1 _).mpr hq
    simp only [map_mul, map_inv] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp (by rwa [commutatorElement_def])
  exact ⟨hnY, hnX, hcXY⟩

theorem sec97_factor (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z)
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K)
    (hrange : ((Ψ K).toMonoidHom.comp φ).range = (rho' K).range)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)) :
    (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K ∨
    (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  have hhead := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have hq4Z : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  obtain ⟨hYQnorm, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := HS9.isSLModel_two_data hq4Z hq2 hYmod
  have hQY_idx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := HS9.normalizer_of_commutator_le hQX hcomm
  have hXY' : X ≤ Subgroup.normalizer (Y : Set G) :=
    HS9.normalizer_of_commutator_le (X := Y) (Y := X) hQY (fun a ha y hy => by
      have := Q.inv_mem (hcomm y hy a ha)
      rwa [commutatorElement_inv] at this)
  have hRX : Rt M (LB M Q B) t ≤ Subgroup.normalizer (X : Set G) :=
    calc Rt M (LB M Q B) t = X ⊔ Y := hXY.symm
      _ ≤ _ := sup_le Subgroup.le_normalizer hYX
  have hRY : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Y : Set G) :=
    calc Rt M (LB M Q B) t = X ⊔ Y := hXY.symm
      _ ≤ _ := sup_le hXY' Subgroup.le_normalizer
  have hdec : ∀ r ∈ Rt M (LB M Q B) t, ∃ x ∈ X, ∃ y ∈ Y, x * y = r := by
    intro r hr
    have hr' : r ∈ (↑(X ⊔ Y) : Set G) := by rw [hXY]; exact hr
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXY'] at hr'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hr'
    exact ⟨x, hx, y, hy, hxy⟩
  let φ'' : ↥(Rt M (LB M Q B) t) →*
      (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) := (Ψ K).toMonoidHom.comp φ
  have hφ''1 : ∀ s : ↥(Rt M (LB M Q B) t), φ'' s = 1 ↔ (s : G) ∈ hc.CN t := by
    intro s
    show Ψ K (φ s) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    (card_statedSL 2 K).symm.trans (card_statedSL_two K)
  have hcardRange : Nat.card (rho' K).range =
      Nat.card K * (Nat.card K ^ 2 - 1) * (Nat.card K * (Nat.card K ^ 2 - 1)) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (rho'_injective (K := K))).toEquiv,
      Nat.card_prod, hcardSL]
  have hQY_idxK : Q.relIndex Y = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [hQY_idx, hK]
  have hHYne : (Y.subgroupOf (Rt M (LB M Q B) t)).map φ'' ≠ ⊥ :=
    sec97_HY_ne_bot φ'' hYR hhead hXYQ hQY_idx hq4Z hφ''1
  have hcardHY : Nat.card ↥((Y.subgroupOf (Rt M (LB M Q B) t)).map φ'') ≤
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    sec97_HY_card_le φ'' hYR (hc.Q_le_CN ht) hφ''1 hQY_idxK
  have hHXne : (X.subgroupOf (Rt M (LB M Q B) t)).map φ'' ≠ ⊥ :=
    sec97_HX_ne_bot φ'' hrange hdec hXR hYR hcardRange hcardHY hq4
  have hnc := sec97_normal_comm φ'' hrange hRX hRY (hc.Q_le_CN ht) hcomm hφ''1
  have hcls := eq_leftF_or_rightF hq4 hnc.2.1 hnc.1
    (hrange ▸ Subgroup.map_le_range φ'' (X.subgroupOf (Rt M (LB M Q B) t)))
    (hrange ▸ Subgroup.map_le_range φ'' (Y.subgroupOf (Rt M (LB M Q B) t)))
    hHXne hHYne hnc.2.2
  rcases hcls with ⟨-, h2⟩ | ⟨-, h2⟩
  · exact Or.inr h2
  · exact Or.inl h2

theorem sec97_line_data (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (_ : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K)
      (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (Fin 2 ⊕ Fin 2 → K))
      (u : Fin 2 ⊕ Fin 2 → K)
      (H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K))
      (Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K) (w₀ : Fin 2 → K),
      Nat.card K = Nat.card Z ∧
      (∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
        (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            Multiplicative.toAdd (ψ (QuotientGroup.mk v))) ∧
      Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) ∧
      (∀ x : Fin 2 ⊕ Fin 2 → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
          ∃ c : K, x = c • u) ∧
      (∀ h, h ∈ H ↔ ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h) ∧
      ActsNat H Φ ∧ w₀ ≠ 0 ∧ toMat K u = Φ w₀ := by
  classical
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, hW, hdet, hu0⟩ :=
    sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  let φ'' : ↥(Rt M (LB M Q B) t) →*
      (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) := (Ψ K).toMonoidHom.comp φ
  have hfac : (Y.subgroupOf (Rt M (LB M Q B) t)).map φ'' = leftF K ∨
      (Y.subgroupOf (Rt M (LB M Q B) t)).map φ'' = rightF K :=
    sec97_factor h34 h311a hc hs hsplit hK φ hrange hker
  have hHY : ∀ h, h ∈ (Y.subgroupOf (Rt M (LB M Q B) t)).map φ'' ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
    intro h
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  rcases hfac with hleft | hright
  · obtain ⟨Φ, w₀, hA, hw₀, hu⟩ :=
      natural_module_data (H := leftF K) (Or.inl rfl) hdet hu0
    refine ⟨K, fK, finK, chK, hn, φ, ψ, u, leftF K, Φ, w₀, hK, hψ, hnorm, hBiff, ?_,
      hA, hw₀, hu⟩
    intro h
    rw [← hleft]
    exact hHY h
  · obtain ⟨Φ, w₀, hA, hw₀, hu⟩ :=
      natural_module_data (H := rightF K) (Or.inr rfl) hdet hu0
    refine ⟨K, fK, finK, chK, hn, φ, ψ, u, rightF K, Φ, w₀, hK, hψ, hnorm, hBiff, ?_,
      hA, hw₀, hu⟩
    intro h
    rw [← hright]
    exact hHY h

end HS9

theorem sec97LineNat_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y →
        Nat.card ↥(HS9.Uline Z B Y) = Nat.card Z ^ 3 ∧
        IsIrredModule Y (HS9.Uline Z B Y) Z ∧
        ∃ Y₀ : Subgroup G, Y₀ ≤ Y ∧ (∀ b ∈ B, ∀ y ∈ Y₀, ⁅y, b⁆ ∈ Z) ∧
          ∀ u ∈ HS9.Uline Z B Y, (∀ y ∈ Y₀, ⁅y, u⁆ ∈ Z) → u ∈ (B ⊔ Z : Subgroup G) := by
  classical
  intro G _ _ M Q Z B hc n t hs X Y hsplit
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, H, Φ, w₀, hK, hψ, hnorm, hBiff, hH, hA, hw₀, hu⟩ :=
    sec97_line_data h34 h311a hc hs hsplit
  haveI := hn
  haveI : CharP K 2 := chK
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hYM : Y ≤ M := hYR.trans (Rt_le_M hc.LB_le_M t)
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y * z * y⁻¹ ∈ Z := fun y hy z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hYM hy)) z).mp hz
  have hu0 : toMat K u ≠ 0 := by
    rw [hu]
    exact fun h => hw₀ (hA.inj (by rw [h, map_zero]))
  have hbnz : ∃ b ∈ B, b ∉ Z := by
    obtain ⟨b, hbB, hbu⟩ := (hBiff u).mpr ⟨1, (one_smul K u).symm⟩
    refine ⟨(b : G), hbB, fun hbZ => hu0 ?_⟩
    rw [← hbu, (secVec_eq_zero_iff ψ b).mpr hbZ, map_zero]
  refine ⟨?_, uline_irred ψ φ hψ hnorm hYR hZV hBV u hBiff hH hA hw₀ hu hbnz,
    uline_fixed ψ φ hψ hnorm hYR hZV hBV u hBiff hH hA hw₀ hu hYZ⟩
  rw [uline_card ψ φ hψ hnorm hYR hZV hBV u hBiff hH hA hw₀ hu, hK]
  ring

end CFSG.RankThree.GF2n.Stroth80

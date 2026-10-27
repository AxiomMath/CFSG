module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatFlag
public import CFSG.ClassicalGroups.SpecialLinear.Transitive

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.SpecialLinear CFSG.Open
open QuadraticMap Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
  {K : Type} [Field K] [(Z.subgroupOf V).Normal]

@[expose] def secVec (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (v : ↥V) : ι → K :=
  Multiplicative.toAdd (ψ (QuotientGroup.mk v))

theorem secVec_mul (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (v w : ↥V) :
    secVec ψ (v * w) = secVec ψ v + secVec ψ w := by
  unfold secVec
  rw [QuotientGroup.mk_mul, map_mul, toAdd_mul]

theorem secVec_inv (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (v : ↥V) :
    secVec ψ v⁻¹ = -secVec ψ v := by
  unfold secVec
  rw [QuotientGroup.mk_inv, map_inv, toAdd_inv]

theorem secVec_eq_zero_iff (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (v : ↥V) :
    secVec ψ v = 0 ↔ (v : G) ∈ Z := by
  unfold secVec
  rw [toAdd_eq_zero, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem exists_secVec_eq (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (x : ι → K) :
    ∃ v : ↥V, secVec ψ v = x := by
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd x))
  exact ⟨v, by unfold secVec; rw [hv, MulEquiv.apply_symm_apply, toAdd_ofAdd]⟩

theorem secVec_eq_iff (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (v w : ↥V) :
    secVec ψ v = secVec ψ w ↔ (v : G) * (w : G)⁻¹ ∈ Z := by
  have h : secVec ψ (v * w⁻¹) = secVec ψ v - secVec ψ w := by
    rw [secVec_mul, secVec_inv, sub_eq_add_neg]
  rw [← sub_eq_zero, ← h, secVec_eq_zero_iff]
  rfl

theorem mem_of_secVec_eq {S : Subgroup G} (hZS : Z ≤ S)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) {y w : ↥V} (hw : (w : G) ∈ S)
    (h : secVec ψ w = secVec ψ y) : (y : G) ∈ S := by
  have h1 : (y : G) * (w : G)⁻¹ ∈ Z := (secVec_eq_iff ψ y w).mp h.symm
  have h2 : (y : G) = ((y : G) * (w : G)⁻¹) * (w : G) := by group
  rw [h2]
  exact S.mul_mem (hZS h1) hw

section Comm

variable {R : Subgroup G} (φ : ↥R →* GL ι K)

theorem comm_mem_of_le_normalizer (hVR : R ≤ Subgroup.normalizer (V : Set G)) (s : ↥R)
    (v : ↥V) : ⁅(s : G), (v : G)⁆ ∈ V := by
  have h1 : (s : G) * v * (s : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hVR s.2) v).mp v.2
  rw [commutatorElement_def]
  exact V.mul_mem h1 (V.inv_mem v.2)

theorem secVec_comm (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hVR : R ≤ Subgroup.normalizer (V : Set G)) (s : ↥R) (v : ↥V) :
    secVec ψ ⟨⁅(s : G), (v : G)⁆, comm_mem_of_le_normalizer hVR s v⟩ =
      (φ s : Matrix ι ι K) *ᵥ secVec ψ v - secVec ψ v := by
  set w : ↥V := ⟨(s : G) * v * (s : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hVR s.2) v).mp v.2⟩ with hw
  have hc : (⟨⁅(s : G), (v : G)⁆, comm_mem_of_le_normalizer hVR s v⟩ : ↥V) = w * v⁻¹ := by
    apply Subtype.ext
    rfl
  have h := hψ s v w rfl
  change secVec ψ w = (φ s : Matrix ι ι K) *ᵥ secVec ψ v at h
  rw [hc, secVec_mul, secVec_inv, h, sub_eq_add_neg]

end Comm

section Flag

variable {R : Subgroup G} (φ : ↥R →* GL ι K)

theorem commFlag_iff {B W : Subgroup G} (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hVR : R ≤ Subgroup.normalizer (V : Set G)) (hZV : Z ≤ V) (hBV : B ≤ V) (hWV : W ≤ V)
    (hZW : Z ≤ W) (hBZ : ∀ y ∈ B ⊔ Z, ∃ b ∈ B, ∃ z ∈ Z, y = b * z) {u : ι → K}
    {H : (ι → K) → Prop}
    (hB : ∀ x : ι → K, (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    (hW : ∀ x : ι → K, (∃ w : ↥V, (w : G) ∈ W ∧ secVec ψ w = x) ↔ H x) (s : ↥R) :
    ((∀ b ∈ B, ⁅(s : G), b⁆ ∈ Z) ∧ (∀ v ∈ W, ⁅(s : G), v⁆ ∈ B ⊔ Z) ∧
        ∀ v ∈ V, ⁅(s : G), v⁆ ∈ W) ↔
      ((φ s : Matrix ι ι K) *ᵥ u = u ∧
        (∀ x, H x → ∃ c : K, (φ s : Matrix ι ι K) *ᵥ x - x = c • u) ∧
          ∀ x, H ((φ s : Matrix ι ι K) *ᵥ x - x)) := by
  let cm : ↥V → ↥V := fun v => ⟨⁅(s : G), (v : G)⁆, comm_mem_of_le_normalizer hVR s v⟩
  have key : ∀ v : ↥V, secVec ψ (cm v) = (φ s : Matrix ι ι K) *ᵥ secVec ψ v - secVec ψ v :=
    fun v => secVec_comm φ ψ hψ hVR s v
  have c1 : (∀ b ∈ B, ⁅(s : G), b⁆ ∈ Z) ↔ (φ s : Matrix ι ι K) *ᵥ u = u := by
    constructor
    · intro h
      obtain ⟨b, hbB, hbu⟩ := (hB u).mpr ⟨1, (one_smul K u).symm⟩
      have h0 : secVec ψ (cm b) = 0 := (secVec_eq_zero_iff ψ (cm b)).mpr (h b hbB)
      rw [key b, hbu, sub_eq_zero] at h0
      exact h0
    · intro h b hb
      obtain ⟨c, hc⟩ := (hB (secVec ψ ⟨b, hBV hb⟩)).mp ⟨⟨b, hBV hb⟩, hb, rfl⟩
      have h0 : secVec ψ (cm ⟨b, hBV hb⟩) = 0 := by
        rw [key ⟨b, hBV hb⟩, hc, Matrix.mulVec_smul, h, sub_self]
      exact (secVec_eq_zero_iff ψ (cm ⟨b, hBV hb⟩)).mp h0
  have c2 : (∀ v ∈ W, ⁅(s : G), v⁆ ∈ B ⊔ Z) ↔
      ∀ x, H x → ∃ c : K, (φ s : Matrix ι ι K) *ᵥ x - x = c • u := by
    constructor
    · intro h x hx
      obtain ⟨w, hwW, hwx⟩ := (hW x).mpr hx
      obtain ⟨b, hbB, z, hzZ, hbz⟩ := hBZ _ (h w hwW)
      have hbV : b ∈ V := hBV hbB
      have hzV : z ∈ V := hZV hzZ
      have e : cm w = ⟨b, hbV⟩ * ⟨z, hzV⟩ := Subtype.ext hbz
      have hz0 : secVec ψ ⟨z, hzV⟩ = 0 := (secVec_eq_zero_iff ψ _).mpr hzZ
      obtain ⟨c, hc⟩ := (hB (secVec ψ ⟨b, hbV⟩)).mp ⟨⟨b, hbV⟩, hbB, rfl⟩
      refine ⟨c, ?_⟩
      rw [← hwx, ← key w, e, secVec_mul, hz0, add_zero, hc]
    · intro h v hv
      obtain ⟨c, hc⟩ := h (secVec ψ ⟨v, hWV hv⟩) ((hW _).mp ⟨⟨v, hWV hv⟩, hv, rfl⟩)
      obtain ⟨b, hbB, hbc⟩ := (hB (c • u)).mpr ⟨c, rfl⟩
      exact mem_of_secVec_eq (S := B ⊔ Z) le_sup_right ψ (y := cm ⟨v, hWV hv⟩) (w := b)
        (Subgroup.mem_sup_left hbB) (by rw [key ⟨v, hWV hv⟩, hc, hbc])
  have c3 : (∀ v ∈ V, ⁅(s : G), v⁆ ∈ W) ↔
      ∀ x, H ((φ s : Matrix ι ι K) *ᵥ x - x) := by
    constructor
    · intro h x
      obtain ⟨v, rfl⟩ := exists_secVec_eq ψ x
      have := (hW (secVec ψ (cm v))).mp ⟨cm v, h v v.2, rfl⟩
      rwa [key v] at this
    · intro h v hv
      have hH := h (secVec ψ ⟨v, hv⟩)
      rw [← key ⟨v, hv⟩] at hH
      obtain ⟨w, hwW, hwe⟩ := (hW _).mpr hH
      exact mem_of_secVec_eq hZW ψ (y := cm ⟨v, hv⟩) hwW hwe
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨c1.mp h1, c2.mp h2, c3.mp h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨c1.mpr h1, c2.mpr h2, c3.mpr h3⟩⟩

end Flag

theorem exists_mul_of_mem_sup {B Z' : Subgroup G} (hc : ∀ b ∈ B, ∀ z ∈ Z', b * z = z * b) {y : G}
    (hy : y ∈ B ⊔ Z') : ∃ b ∈ B, ∃ z ∈ Z', y = b * z := by
  let S : Subgroup G :=
    { carrier := {y | ∃ b ∈ B, ∃ z ∈ Z', y = b * z}
      mul_mem' := by
        rintro _ _ ⟨b₁, hb₁, z₁, hz₁, rfl⟩ ⟨b₂, hb₂, z₂, hz₂, rfl⟩
        refine ⟨b₁ * b₂, B.mul_mem hb₁ hb₂, z₁ * z₂, Z'.mul_mem hz₁ hz₂, ?_⟩
        have h : z₁ * b₂ = b₂ * z₁ := (hc b₂ hb₂ z₁ hz₁).symm
        calc b₁ * z₁ * (b₂ * z₂) = b₁ * (z₁ * b₂) * z₂ := by group
          _ = b₁ * (b₂ * z₁) * z₂ := by rw [h]
          _ = b₁ * b₂ * (z₁ * z₂) := by group
      one_mem' := ⟨1, B.one_mem, 1, Z'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨b, hb, z, hz, rfl⟩
        refine ⟨b⁻¹, B.inv_mem hb, z⁻¹, Z'.inv_mem hz, ?_⟩
        have h : z⁻¹ * b⁻¹ = b⁻¹ * z⁻¹ := (hc b⁻¹ (B.inv_mem hb) z⁻¹ (Z'.inv_mem hz)).symm
        rw [_root_.mul_inv_rev, h] }
  have hle : B ⊔ Z' ≤ S :=
    sup_le (fun b hb => ⟨b, hb, 1, Z'.one_mem, by simp⟩)
      (fun z hz => ⟨1, B.one_mem, z, hz, by simp⟩)
  exact hle hy

section Corollaries

variable {R : Subgroup G}

theorem map_subgroupOf_eq_LspGL_of_commFlag {m : ℕ} {N L B W : Subgroup G}
    (φ : ↥R →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    (hNφ : φ.ker = N.subgroupOf R) (hN : N ≤ R) (hL : L ≤ R)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hVR : R ≤ Subgroup.normalizer (V : Set G)) (hZV : Z ≤ V) (hBV : B ≤ V) (hWV : W ≤ V)
    (hZW : Z ≤ W) (hBZ : ∀ y ∈ B ⊔ Z, ∃ b ∈ B, ∃ z ∈ Z, y = b * z)
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    (hB : ∀ x : Fin m ⊕ Fin m → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    (hW : ∀ x : Fin m ⊕ Fin m → K,
      (∃ w : ↥V, (w : G) ∈ W ∧ secVec ψ w = x) ↔ spForm m K x u = 0)
    (h : ∀ r : ↥R, (r : G) ∈ L ⊔ N ↔ (∀ b ∈ B, ⁅(r : G), b⁆ ∈ Z) ∧
      (∀ v ∈ W, ⁅(r : G), v⁆ ∈ B ⊔ Z) ∧ ∀ v ∈ V, ⁅(r : G), v⁆ ∈ W) :
    (L.subgroupOf R).map φ = LspGL m K u :=
  map_subgroupOf_eq_LspGL_of_flag φ hφ hNφ hN hL hu fun r =>
    (h r).trans (commFlag_iff φ ψ hψ hVR hZV hBV hWV hZW hBZ hB hW r)

theorem map_subgroupOf_eq_LomGL_of_commFlag {Q : QuadraticForm K (ι → K)}
    {X : Subgroup (GL ι K)} {N L B W : Subgroup G} (E : ElemMatrixIso Q X)
    (hQ : (polarBilin Q).Nondegenerate) (φ : ↥R →* GL ι K) (hφ : φ.range = X)
    (hNφ : φ.ker = N.subgroupOf R) (hN : N ≤ R) (hL : L ≤ R)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hVR : R ≤ Subgroup.normalizer (V : Set G)) (hZV : Z ≤ V) (hBV : B ≤ V) (hWV : W ≤ V)
    (hZW : Z ≤ W) (hBZ : ∀ y ∈ B ⊔ Z, ∃ b ∈ B, ∃ z ∈ Z, y = b * z) {u : ι → K} (hu : Q u = 0)
    (hu0 : u ≠ 0)
    (hB : ∀ x : ι → K, (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    (hW : ∀ x : ι → K, (∃ w : ↥V, (w : G) ∈ W ∧ secVec ψ w = x) ↔ polar Q u x = 0)
    (h : ∀ r : ↥R, (r : G) ∈ L ⊔ N ↔ (∀ b ∈ B, ⁅(r : G), b⁆ ∈ Z) ∧
      (∀ v ∈ W, ⁅(r : G), v⁆ ∈ B ⊔ Z) ∧ ∀ v ∈ V, ⁅(r : G), v⁆ ∈ W) :
    (L.subgroupOf R).map φ = E.LomGL u :=
  map_subgroupOf_eq_LomGL_of_flag E hQ φ hφ hNφ hN hL hu hu0 fun r =>
    (h r).trans (commFlag_iff φ ψ hψ hVR hZV hBV hWV hZW hBZ hB hW r)

end Corollaries

end CFSG.RankThree.GF2n.Stroth80

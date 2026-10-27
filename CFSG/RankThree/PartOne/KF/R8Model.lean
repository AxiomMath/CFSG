module

public import CFSG.RankThree.PartOne.KF.R8Group
public import CFSG.RankThree.PartOne.KF.R1Model

public section

namespace CFSG.RankThree.PartOne.KFQ

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank

section Normalizer

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_subgroupOf_iff' {M T : Subgroup Γ} (hTM : T ≤ M) (m : ↥M) :
    m ∈ Subgroup.normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M) ↔
      (∀ x ∈ T, (m : Γ) * x * (m : Γ)⁻¹ ∈ T) ∧ (∀ x ∈ T, (m : Γ)⁻¹ * x * (m : Γ) ∈ T) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact (h ⟨x, hTM hx⟩).mp hx
    · have h1 : (⟨(m : Γ)⁻¹ * x * (m : Γ), M.mul_mem (M.mul_mem
          (M.inv_mem m.2) (hTM hx)) m.2⟩ : ↥M) ∈ T.subgroupOf M ↔ _ := h _
      have h2 : m * ⟨(m : Γ)⁻¹ * x * (m : Γ), M.mul_mem (M.mul_mem
          (M.inv_mem m.2) (hTM hx)) m.2⟩ * m⁻¹ = ⟨x, hTM hx⟩ := by
        apply Subtype.ext
        show (m : Γ) * ((m : Γ)⁻¹ * x * (m : Γ)) * (m : Γ)⁻¹ = x
        group
      rw [h2] at h1
      exact h1.mpr hx
  · rintro ⟨h1, h2⟩ y
    constructor
    · intro hy
      exact h1 _ hy
    · intro hy
      have h4 := h2 ((m * y * m⁻¹ : ↥M) : Γ) hy
      have h3 : (m : Γ)⁻¹ * ((m * y * m⁻¹ : ↥M) : Γ) * (m : Γ) = (y : Γ) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h3] at h4
      exact h4

end Normalizer

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem realizes_inv {γ : DihedralGroup 4} {g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)}
    (h : Realizes (p := p) γ g) (v : D8Mod p (Qext K)) :
    g⁻¹ * d8Emb v * g = d8Emb (d8Act γ⁻¹ v) := by
  have h1 := h (d8Act γ⁻¹ v)
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h1
  have h2 : g⁻¹ * (g * d8Emb (d8Act γ⁻¹ v) * g⁻¹) * g = d8Emb (d8Act γ⁻¹ v) := by group
  rw [h1] at h2
  exact h2

@[expose] noncomputable def m8Equiv : ↥(M8 K) ≃* ↥(StatedSL 4 K) :=
  ((glEquiv (K := K)).subgroupMap (M8 K)).trans (MulEquiv.subgroupCongr (by
    ext x
    rw [mem_statedSL_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      have h1 := det_glEquiv (K := K) g
      have h2 : LinearEquiv.det g = 1 := (mem_M8_iff g).mp hg
      show ((glEquiv (K := K) g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1
      rw [h1, h2]
      simp
    · intro hx
      refine ⟨(glEquiv (K := K)).symm x, (mem_M8_iff _).mpr ?_, by simp⟩
      apply Units.ext
      have := det_glEquiv (K := K) ((glEquiv (K := K)).symm x)
      rw [MulEquiv.apply_symm_apply] at this
      rw [← this, hx]
      simp))

omit [Finite K] in
theorem scalar_eq_one_of_det {z : GL (Fin 4) K} (hz : z ∈ StatedScalars (Fin 4) K)
    (hdet : (z : Matrix (Fin 4) (Fin 4) K).det = 1) : z = 1 := by
  obtain ⟨c, rfl⟩ := hz
  have h1 : ((c : Kˣ) : K) ^ 4 = 1 := by
    have : ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).det = (c : K) ^ 4 := by
      simp [Matrix.GeneralLinearGroup.scalar]
    rw [← this]
    exact hdet
  have h2 : (((c : Kˣ) : K) - 1) ^ (2 ^ 2) = 0 := by
    rw [sub_pow_char_pow (p := 2) (n := 2)]
    simp [h1]
  have h3 : ((c : Kˣ) : K) = 1 := sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  have : c = 1 := Units.ext (by simpa using h3)
  rw [this, map_one]

theorem isCentralPQuot_m8 (p : ℕ) :
    IsCentralPQuot p ((QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K))).comp
      (m8Equiv (K := K)).toMonoidHom) := by
  have hN : (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    exact scalar_eq_one_of_det hx (mem_statedSL_iff.mp x.2)
  refine SymCtx.isCentralPQuot_of_bijective _ ⟨fun x y hxy => ?_, ?_⟩ p
  · have h1 : (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)))
        (m8Equiv x) = (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf
          (StatedSL 4 K))) (m8Equiv y) := hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact m8Equiv.injective h1
  · exact (QuotientGroup.mk'_surjective _).comp m8Equiv.surjective

theorem exists_d8ctx_r8 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    Nonempty (D8Ctx p (Qext K) (⊤ : Subgroup ↥(M8 K))
      ((d8Emb : D8Mod p (Qext K) →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))).range.subgroupOf
        (M8 K))) := by
  classical
  set T : Subgroup (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) := d8Emb.range with hTdef
  have hTM : T ≤ M8 K := by
    rintro _ ⟨v, rfl⟩
    exact d8Emb_mem_M8 hp hp2 hpq v
  let torh : D8Mod p (Qext K) →* ↥(T.subgroupOf (M8 K)) :=
    { toFun := fun v => ⟨⟨d8Emb v, d8Emb_mem_M8 hp hp2 hpq v⟩, ⟨v, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        exact map_one _
      map_mul' := fun v w => by
        apply Subtype.ext
        apply Subtype.ext
        exact map_mul _ _ _ }
  have hinj : Function.Injective torh := by
    intro v w h
    exact d8Emb_injective (congrArg (fun x : ↥(T.subgroupOf (M8 K)) =>
      ((x : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))) h)
  have hsurj : Function.Surjective torh := by
    rintro ⟨⟨x, hxM⟩, hxT⟩
    obtain ⟨v, hv⟩ := hxT
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hv
  let tor : D8Mod p (Qext K) ≃* ↥(T.subgroupOf (M8 K)) :=
    MulEquiv.ofBijective torh ⟨hinj, hsurj⟩
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }⟩
  · intro γ
    obtain ⟨g, hdet, hr⟩ := exists_realizer (p := p) hpq γ
    set gM : ↥(M8 K) := ⟨g, (mem_M8_iff _).mpr hdet⟩ with hgMdef
    have hg : gM ∈ Subgroup.normalizer
        ((T.subgroupOf (M8 K) : Subgroup ↥(M8 K)) : Set ↥(M8 K)) := by
      rw [mem_normalizer_subgroupOf_iff' hTM]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨v, rfl⟩ := hx
        show g * d8Emb v * g⁻¹ ∈ T
        rw [hr v]
        exact ⟨_, rfl⟩
      · obtain ⟨v, rfl⟩ := hx
        show g⁻¹ * d8Emb v * g ∈ T
        rw [realizes_inv hr v]
        exact ⟨_, rfl⟩
    refine ⟨gM, hg, Subgroup.mem_top _, ?_⟩
    refine MulEquiv.ext fun t => ?_
    obtain ⟨v, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    apply Subtype.ext
    exact hr v
  · intro m hm _
    obtain ⟨h1, -⟩ := (mem_normalizer_subgroupOf_iff' hTM m).mp hm
    have hg : ∀ v : D8Mod p (Qext K), ∃ v' : D8Mod p (Qext K),
        (m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * d8Emb v * (m : QV K (Fin 2) ≃ₗ[K] _)⁻¹ =
          d8Emb v' := fun v => by
      obtain ⟨v', hv'⟩ := h1 _ ⟨v, rfl⟩
      exact ⟨v', hv'.symm⟩
    obtain ⟨w, hw⟩ := exists_dihedral_of_normalizes hp hp2 hpq
      (m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) hg
    refine ⟨w, MulEquiv.ext fun t => ?_⟩
    obtain ⟨v, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    apply Subtype.ext
    exact hw v

end CFSG.RankThree.PartOne.KFQ

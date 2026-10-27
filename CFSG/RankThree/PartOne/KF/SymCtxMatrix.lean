module

public import CFSG.RankThree.PartOne.KF.SymCtx
public import CFSG.RankThree.PartOne.KF.R9Perm

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.RankThree.PartOne

namespace SymCtx

variable {n p : ℕ} {K : Type} [Field K]

theorem ofMatrixGroup (M : Subgroup (GL (Fin n) K)) (hTM : torusSU p n K ≤ M)
    (hperm : ∀ σ : Equiv.Perm (Fin n), (permGL σ : GL (Fin n) K) ∈ M)
    (hdist : ∀ i j : Fin n, i ≠ j → ∃ x ∈ torusSU p n K, ent x i i ≠ ent x j j) :
    Nonempty (SymCtx p n K (⊤ : Subgroup ↥M) ((torusSU p n K).subgroupOf M)) := by
  classical
  let T : Subgroup ↥M := (torusSU p n K).subgroupOf M
  have hdmem : ∀ d : torusVec p n K, (diagU (d : Fin n → Kˣ) : GL (Fin n) K) ∈ torusSU p n K :=
    fun d => mem_torusSU_iff.mpr ⟨d.1, d.2.1, d.2.2, rfl⟩
  let torh : torusVec p n K →* T :=
    { toFun := fun d => ⟨⟨diagU (d : Fin n → Kˣ), hTM (hdmem d)⟩, hdmem d⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        exact diagU_one
      map_mul' := fun d e => by
        apply Subtype.ext
        apply Subtype.ext
        exact (diagU_mul _ _).symm }
  have hinj : Function.Injective torh := fun d e h =>
    Subtype.ext (diagU_injective (congrArg (fun x : T => ((x : ↥M) : GL (Fin n) K)) h))
  have hsurj : Function.Surjective torh := by
    rintro ⟨⟨x, hxM⟩, hxT⟩
    obtain ⟨d, hd1, hd2, hdx⟩ := mem_torusSU_iff.mp hxT
    refine ⟨⟨d, hd1, hd2⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hdx
  let tor : torusVec p n K ≃* T := MulEquiv.ofBijective torh ⟨hinj, hsurj⟩
  have hcoe : ∀ d, (((tor d : T) : ↥M) : GL (Fin n) K) = diagU (d : Fin n → Kˣ) := fun d => rfl
  have hnorm_iff : ∀ m : ↥M, m ∈ Subgroup.normalizer (T : Set ↥M) ↔
      (∀ x ∈ torusSU p n K, (m : GL (Fin n) K) * x * (m : GL (Fin n) K)⁻¹ ∈ torusSU p n K) ∧
      (∀ x ∈ torusSU p n K, (m : GL (Fin n) K)⁻¹ * x * (m : GL (Fin n) K) ∈ torusSU p n K) := by
    intro m
    rw [Subgroup.mem_normalizer_iff]
    constructor
    · intro h
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · exact (h ⟨x, hTM hx⟩).mp hx
      · have h1 : (⟨(m : GL (Fin n) K)⁻¹ * x * (m : GL (Fin n) K), M.mul_mem (M.mul_mem
            (M.inv_mem m.2) (hTM hx)) m.2⟩ : ↥M) ∈ T ↔ _ := h _
        have h2 : m * ⟨(m : GL (Fin n) K)⁻¹ * x * (m : GL (Fin n) K), M.mul_mem (M.mul_mem
            (M.inv_mem m.2) (hTM hx)) m.2⟩ * m⁻¹ = ⟨x, hTM hx⟩ := by
          apply Subtype.ext
          show (m : GL (Fin n) K) * ((m : GL (Fin n) K)⁻¹ * x * (m : GL (Fin n) K)) *
            (m : GL (Fin n) K)⁻¹ = x
          group
        rw [h2] at h1
        exact h1.mpr hx
    · rintro ⟨h1, h2⟩ y
      constructor
      · intro hy
        exact h1 _ hy
      · intro hy
        have h4 := h2 ((m * y * m⁻¹ : ↥M) : GL (Fin n) K) hy
        have h3 : (m : GL (Fin n) K)⁻¹ * ((m * y * m⁻¹ : ↥M) : GL (Fin n) K) *
            (m : GL (Fin n) K) = (y : GL (Fin n) K) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [h3] at h4
        exact h4
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }⟩
  · intro σ
    set g : ↥M := ⟨permGL σ, hperm σ⟩ with hgdef
    have hg : g ∈ Subgroup.normalizer (T : Set ↥M) := by
      rw [hnorm_iff]
      refine ⟨(normPerm_permGL (p := p) σ).1, fun x hx => ?_⟩
      have h1 : (permGL σ : GL (Fin n) K)⁻¹ = permGL σ⁻¹ := (map_inv permGL σ).symm
      show (permGL σ : GL (Fin n) K)⁻¹ * x * (permGL σ : GL (Fin n) K) ∈ torusSU p n K
      have h2 : (permGL σ : GL (Fin n) K) = (permGL σ⁻¹ : GL (Fin n) K)⁻¹ := by
        rw [map_inv, inv_inv]
      rw [h1, h2]
      exact (normPerm_permGL (p := p) σ⁻¹).1 x hx
    refine ⟨g, hg, Subgroup.mem_top _, ?_⟩
    refine MulEquiv.ext fun t => ?_
    obtain ⟨d, rfl⟩ := tor.surjective t
    rw [congr_apply_tor]
    apply Subtype.ext
    apply Subtype.ext
    show (permGL σ : GL (Fin n) K) * diagU (d : Fin n → Kˣ) * (permGL σ : GL (Fin n) K)⁻¹ =
      diagU ((symAct p K σ d : torusVec p n K) : Fin n → Kˣ)
    exact permGL_conj_diagU σ _
  · intro m hm _
    obtain ⟨h1, h2⟩ := (hnorm_iff m).mp hm
    obtain ⟨τ, hτ⟩ := exists_normPerm hdist h1 h2
    refine ⟨τ, MulEquiv.ext fun t => ?_⟩
    obtain ⟨d, rfl⟩ := tor.surjective t
    rw [congr_apply_tor]
    apply Subtype.ext
    apply Subtype.ext
    show (m : GL (Fin n) K) * diagU (d : Fin n → Kˣ) * (m : GL (Fin n) K)⁻¹ =
      diagU ((symAct p K τ d : torusVec p n K) : Fin n → Kˣ)
    exact hτ.conj_diagU d.2

end SymCtx

end CFSG.RankThree.PartOne.KFU

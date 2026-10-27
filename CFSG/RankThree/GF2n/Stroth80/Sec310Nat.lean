module

public import CFSG.RankThree.GF2n.Stroth80.Sec310MatRep
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_natural_data_of_subspace {R V N : Subgroup G} (H : StrothHyp M Q Z) (hVQ : V ≤ Q)
    (hZV : Z ≤ V) (hRH : R ≤ H0 M Z) (hRV : R ≤ Subgroup.normalizer (V : Set G))
    (hN : ∀ r, r ∈ N ↔ r ∈ R ∧ ∀ v ∈ V, ⁅r, v⁆ ∈ Z) {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V) :
    ∃ (m : ℕ) (φ : ↥R →* GL (Fin m) K) (_ : (Z.subgroupOf V).Normal)
      (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin m → K))
      (c : ↥(imgSub M₀ V hS) ≃ₗ[K] (Fin m → K)),
      φ.ker = N.subgroupOf R ∧
      (∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix (Fin m) (Fin m) K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) ∧
      (∀ (c' : K) (v w : ↥V), M₀.π w = c' • M₀.π v →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          c' • Multiplicative.toAdd (ψ (QuotientGroup.mk v))) ∧
      (∀ v : ↥V, Multiplicative.toAdd (ψ (QuotientGroup.mk v)) =
        c ⟨M₀.π (v : G), mem_imgSub.mpr (M₀.pi_mem_img v.2 (hVQ v.2))⟩) ∧
      (∀ (r : ↥R) (S : M₀.E ≃ₗ[K] M₀.E),
        (∀ x ∈ Q, M₀.π ((r : G) * x * (r : G)⁻¹) = S (M₀.π x)) →
        ∀ (w : ↥(imgSub M₀ V hS)) (hw : S (w : M₀.E) ∈ imgSub M₀ V hS),
          c ⟨S (w : M₀.E), hw⟩ = (φ r : Matrix (Fin m) (Fin m) K) *ᵥ c w) := by
  classical
  obtain ⟨φ₀, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 H h
  let W : Submodule K M₀.E := imgSub M₀ V hS
  have hWmem : ∀ e, e ∈ W ↔ e ∈ M₀.img V := fun e => mem_imgSub
  have hπW : ∀ v : ↥V, M₀.π (v : G) ∈ W := fun v =>
    (hWmem _).mpr (M₀.pi_mem_img v.2 (hVQ v.2))
  let φR : ↥R →* (M₀.E ≃ₗ[K] M₀.E) := φ₀.comp (Subgroup.inclusion hRH)
  have hφRπ : ∀ (r : ↥R) (x : G), x ∈ Q →
      M₀.π ((r : G) * x * (r : G)⁻¹) = φR r (M₀.π x) := fun r x hx =>
    hφπ (Subgroup.inclusion hRH r) x hx
  have hinv : ∀ (r : ↥R) (w : M₀.E), w ∈ W → φR r w ∈ W := by
    intro r w hw
    obtain ⟨u, huV, huQ, rfl⟩ := (hWmem w).mp hw
    have hru : (r : G) * u * (r : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hRV r.2) u).mp huV
    rw [← hφRπ r u huQ]
    exact (hWmem _).mpr (M₀.pi_mem_img hru (hVQ hru))
  let ρ : ↥R →* (W ≃ₗ[K] W) := actionOnSubspace φR W hinv
  have hρ : ∀ (r : ↥R) (w : W), ((ρ r w : W) : M₀.E) = φR r (w : M₀.E) := fun r w =>
    actionOnSubspace_apply φR W hinv r w
  obtain ⟨φ, c, hc, hker⟩ := exists_matrixRep_of_linearRep (W := W)
    (hW := (rfl : Module.finrank K W = Module.finrank K W)) ρ
  have hkerρ : ρ.ker = N.subgroupOf R := by
    ext r
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hN]
    constructor
    · intro h1
      refine ⟨r.2, fun v hv => ?_⟩
      have hvQ : v ∈ Q := hVQ hv
      have hrvQ : (r : G) * v * (r : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (hRH r.2).1) v).mp hvQ
      refine (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hvQ hrvQ).mpr ?_
      have h2 := congrArg (fun f : W ≃ₗ[K] W => ((f ⟨M₀.π v, hπW ⟨v, hv⟩⟩ : W) : M₀.E)) h1
      simp only [hρ] at h2
      rw [hφRπ r v hvQ]
      exact h2
    · rintro ⟨-, h1⟩
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      rw [hρ]
      obtain ⟨u, huV, huQ, hu⟩ := (hWmem _).mp w.2
      have hruQ : (r : G) * u * (r : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (hRH r.2).1) u).mp
          (hVQ huV)
      have := (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) huQ hruQ).mp (h1 u huV)
      change φR r (w : M₀.E) = (w : M₀.E)
      rw [← hu, ← hφRπ r u huQ, this]
  let πV : ↥V →* Multiplicative W :=
    { toFun := fun v => Multiplicative.ofAdd (⟨M₀.π (v : G), hπW v⟩ : W)
      map_one' := by
        have h0 : M₀.π (1 : G) = 0 := (M₀.π_ker 1 (Q.one_mem)).mpr Z.one_mem
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        exact h0
      map_mul' := by
        intro v w
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        exact M₀.π_mul _ (hVQ v.2) _ (hVQ w.2) }
  have hker' : πV.ker = Z.subgroupOf V := by
    ext v
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 := congrArg (fun a : Multiplicative W => ((Multiplicative.toAdd a : W) : M₀.E)) h1
      exact (M₀.π_ker _ (hVQ v.2)).mp h2
    · intro h1
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact (M₀.π_ker _ (hVQ v.2)).mpr h1
  have hsurj : Function.Surjective πV := by
    intro w
    obtain ⟨u, huV, huQ, hu⟩ := (hWmem _).mp (Multiplicative.toAdd w).2
    refine ⟨⟨u, huV⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hu
  have hn : (Z.subgroupOf V).Normal := hker' ▸ πV.normal_ker
  haveI := hn
  let e1 : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative W :=
    (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective πV hsurj)
  have he1 : ∀ v : ↥V, e1 (QuotientGroup.mk v) = πV v := fun v => rfl
  let ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin (Module.finrank K W) → K) :=
    e1.trans c.toAddEquiv.toMultiplicative
  have hψ : ∀ v : ↥V, Multiplicative.toAdd (ψ (QuotientGroup.mk v)) =
      c ⟨M₀.π (v : G), hπW v⟩ := fun v => rfl
  refine ⟨Module.finrank K W, φ, hn, ψ, c, hker.trans hkerρ, ?_, ?_, hψ, ?_⟩
  · intro s v w hw
    rw [hψ, hψ]
    have : (⟨M₀.π (w : G), hπW w⟩ : W) = ρ s ⟨M₀.π (v : G), hπW v⟩ := by
      apply Subtype.ext
      rw [hρ]
      show M₀.π (w : G) = φR s (M₀.π (v : G))
      rw [hw]
      exact hφRπ s v (hVQ v.2)
    rw [congrArg c this]
    exact hc s _
  · intro c' v w hw
    rw [hψ, hψ]
    have : (⟨M₀.π (w : G), hπW w⟩ : W) = c' • ⟨M₀.π (v : G), hπW v⟩ := by
      apply Subtype.ext
      exact hw
    rw [congrArg c this, map_smul]
  · intro r S hS' w hw
    have hSφ : ∀ e, S e = φR r e := by
      intro e
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
      rw [← hS' x hxQ, hφRπ r x hxQ]
    have : (⟨S (w : M₀.E), hw⟩ : W) = ρ r w := by
      apply Subtype.ext
      rw [hρ]
      exact hSφ _
    rw [this]
    exact hc r w

end CFSG.RankThree.GF2n.Stroth80

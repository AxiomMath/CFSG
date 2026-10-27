module

public import CFSG.RankThree.GF2n.Stroth80.Sec310Symp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_repr_of_subspace {R V N : Subgroup G} (H : StrothHyp M Q Z) (hVQ : V ≤ Q)
    (hRH : R ≤ H0 M Z) (hRV : R ≤ Subgroup.normalizer (V : Set G))
    (hN : ∀ r, r ∈ N ↔ r ∈ R ∧ ∀ v ∈ V, ⁅r, v⁆ ∈ Z) {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V) :
    ∃ ρ : ↥R →* (↥(imgSub M₀ V hS) ≃ₗ[K] ↥(imgSub M₀ V hS)),
      (∀ (r : ↥R) (S : M₀.E ≃ₗ[K] M₀.E),
        (∀ x ∈ Q, M₀.π ((r : G) * x * (r : G)⁻¹) = S (M₀.π x)) →
        ∀ w : ↥(imgSub M₀ V hS), ∃ hw : S (w : M₀.E) ∈ imgSub M₀ V hS,
          ρ r w = ⟨S (w : M₀.E), hw⟩) ∧
      ρ.ker = N.subgroupOf R ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K ↥(imgSub M₀ V hS)),
        ∃ φ : ↥R →* GL ι K, (∀ r, φ r = b.toGL (ρ r)) ∧ φ.ker = N.subgroupOf R ∧
          SectionAct K R V Z φ (fun g => (g : Matrix ι ι K)) := by
  classical
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 H h
  let W : Submodule K M₀.E := imgSub M₀ V hS
  have hWmem : ∀ e, e ∈ W ↔ e ∈ M₀.img V := fun e => mem_imgSub
  have hπW : ∀ v : ↥V, M₀.π (v : G) ∈ W := fun v =>
    (hWmem _).mpr (M₀.pi_mem_img v.2 (hVQ v.2))
  let φR : ↥R →* (M₀.E ≃ₗ[K] M₀.E) := φ₀.comp (Subgroup.inclusion hRH)
  have hφRπ : ∀ (r : ↥R) (x : G), x ∈ Q →
      M₀.π ((r : G) * x * (r : G)⁻¹) = φR r (M₀.π x) := fun r x hx =>
    hφπ (Subgroup.inclusion hRH r) x hx
  have hinvW : ∀ (r : ↥R) (w : M₀.E), w ∈ W → φR r w ∈ W := by
    intro r w hw
    obtain ⟨u, huV, huQ, rfl⟩ := (hWmem w).mp hw
    have hru : (r : G) * u * (r : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hRV r.2) u).mp huV
    rw [← hφRπ r u huQ]
    exact (hWmem _).mpr (M₀.pi_mem_img hru (hVQ hru))
  let ρ : ↥R →* (W ≃ₗ[K] W) := actionOnSubspace φR W hinvW
  have hρ : ∀ (r : ↥R) (w : W), ((ρ r w : W) : M₀.E) = φR r (w : M₀.E) := fun r w =>
    actionOnSubspace_apply φR W hinvW r w
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
        (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (hRH r.2).1) u).mp (hVQ huV)
      have := (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) huQ hruQ).mp (h1 u huV)
      change φR r (w : M₀.E) = (w : M₀.E)
      rw [← hu, ← hφRπ r u huQ, this]
  refine ⟨ρ, ?_, hkerρ, ?_⟩
  · intro r S hS' w
    have hSφ : ∀ e, S e = φR r e := by
      intro e
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
      rw [← hS' x hxQ, hφRπ r x hxQ]
    have hw : S (w : M₀.E) ∈ W := by
      rw [hSφ]
      exact hinvW r w w.2
    refine ⟨hw, Subtype.ext ?_⟩
    rw [hρ]
    exact (hSφ _).symm
  · intro ι _ _ b
    let φ : ↥R →* GL ι K := (b.toGL : (W ≃ₗ[K] W) ≃* GL ι K).toMonoidHom.comp ρ
    have hφ : ∀ r, φ r = b.toGL (ρ r) := fun r => rfl
    have hker : φ.ker = ρ.ker := by
      ext r
      simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact MulEquiv.map_eq_one_iff _
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
    let ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K) :=
      e1.trans b.equivFun.toAddEquiv.toMultiplicative
    have hψ : ∀ v : ↥V, Multiplicative.toAdd (ψ (QuotientGroup.mk v)) =
        b.equivFun ⟨M₀.π (v : G), hπW v⟩ := fun v => rfl
    have hcompat : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
      intro s v w hw
      rw [hψ, hψ]
      have hρv : (⟨M₀.π (w : G), hπW w⟩ : W) = ρ s ⟨M₀.π (v : G), hπW v⟩ := by
        apply Subtype.ext
        rw [hρ]
        show M₀.π (w : G) = φR s (M₀.π (v : G))
        rw [hw]
        exact hφRπ s v (hVQ v.2)
      rw [hρv, hφ]
      exact (toGL_mulVec_equivFun b (ρ s) _).symm
    exact ⟨φ, hφ, hker.trans hkerρ, hRV, hn, ψ, hcompat⟩

end CFSG.RankThree.GF2n.Stroth80

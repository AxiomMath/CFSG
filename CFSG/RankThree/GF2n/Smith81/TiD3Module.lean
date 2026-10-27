module

public import CFSG.RankThree.GF2n.Smith81.TiD2Module
public import CFSG.RankThree.GF2n.Smith81.TiD3Model

public section

namespace CFSG.RankThree.GF2n.Smith81

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups Matrix

namespace D2

variable {K : Type*} [Field K]

theorem slMap_injective (σ : K ≃+* K) : Function.Injective (slMap σ) := by
  intro A B h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := congrArg (fun C : SL(2, K) => (C : Mat2 K) i j) h
  simp only [coe_slMap] at this
  exact σ.injective this

theorem slMap_surjective (σ : K ≃+* K) : Function.Surjective (slMap σ) :=
  fun t => ⟨slMap σ.symm t, slMap_symm_apply σ t⟩

end D2

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section D3G

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

structure D3Data {S : Subgroup G} (Q Z : Subgroup G) (M₀ : Tim79.QuadModel Q Z K γ)
    (φS : ↥S →* (M₀.E ≃ₗ[K] M₀.E)) (F : Type) [Field F] [Algebra K F] where
  card_F : Nat.card F = Nat.card K ^ 3
  finrank_F : Module.finrank K F = 3
  θ : M₀.E ≃ₗ[K] D3.kForm (FiniteField.frobeniusAlgHom K F)
  p : ↥S →* SL(2, F)
  surj : Function.Surjective p
  ker_iff : ∀ m : ↥S, p m = 1 ↔ (m : G) ∈ Q
  act : ∀ (m : ↥S) e, (θ (φS m e) : D3.Hyp F) =
    D3.act (FiniteField.frobeniusAlgHom K F : F →+* F) ((p m : SL(2, F)) : Mat2 F) (θ e)
  quad_eq : ∀ e, algebraMap K F (M₀.Qf e) = D3.quad (θ e : D3.Hyp F)

theorem exists_d3Data (hMod : D3ModuleStatement)
    (hc : Ctx M Q Z B) (hw : Width Q Z 4)
    (hcase : QuotSat (Lgen M (LB M Q B)) Q (IsSLModel 2 (Nat.card Z ^ 3)))
    (hD : GlobalModelData M Q Z γ M₀)
    (φS : ↥(Lgen M (LB M Q B)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(Lgen M (LB M Q B))) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φS m (M₀.π x))
    (hφker : ∀ m : ↥(Lgen M (LB M Q B)), φS m = 1 ↔ (m : G) ∈ Q)
    (hφQ : ∀ m e, M₀.Qf (φS m e) = M₀.Qf e) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Algebra K F),
      Nat.card F = Nat.card K ^ 3 ∧ Module.finrank K F = 3 ∧
        Nonempty (D3Data Q Z M₀ φS F) := by
  classical
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hcardK : Nat.card K = Nat.card Z := hD.card
  have hK4 : 4 ≤ Nat.card K := by rw [hcardK]; exact hq4
  have hK1 : 1 < Nat.card K := by omega
  have hcardF : Nat.card (FiniteField.Extension K 2 3) = Nat.card K ^ 3 :=
    FiniteField.natCard_extension K 2 3
  have hfinrank : Module.finrank K (FiniteField.Extension K 2 3) = 3 :=
    FiniteField.finrank_extension K 2 3
  obtain ⟨ψ, hψs, hψk⟩ := exists_psi (K := FiniteField.Extension K 2 3) hcase
    (by rw [hcardF, hcardK])
  have hker : ψ.ker ≤ φS.ker := fun m hm =>
    MonoidHom.mem_ker.mpr ((hφker m).mpr ((hψk m).mp (MonoidHom.mem_ker.mp hm)))
  let ρ : SL(2, FiniteField.Extension K 2 3) →* (M₀.E ≃ₗ[K] M₀.E) :=
    ψ.liftOfRightInverse (Function.surjInv hψs) (Function.rightInverse_surjInv hψs) ⟨φS, hker⟩
  have hρψ : ∀ m, ρ (ψ m) = φS m := fun m =>
    ψ.liftOfRightInverse_comp_apply (Function.surjInv hψs) (Function.rightInverse_surjInv hψs)
      ⟨φS, hker⟩ m
  have hρQ : ∀ g e, M₀.Qf (ρ g e) = M₀.Qf e := by
    intro g e
    obtain ⟨m, rfl⟩ := hψs g
    rw [hρψ, hφQ]
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨m, rfl⟩ := hψs g
    rw [hρψ] at hg
    exact (hψk m).mpr ((hφker m).mp hg)
  have hSM : Lgen M (LB M Q B) ≤ M := hc.Lgen_le_M
  have hNorm : M ≤ Subgroup.normalizer ((Lgen M (LB M Q B) : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      exact hc.mem_Lgen_conj hm hs
    · intro hs
      have := hc.mem_Lgen_conj (M.inv_mem hm) hs
      rwa [show m⁻¹ * (m * s * m⁻¹) * m⁻¹⁻¹ = s by group] at this
  have hCQt : ∀ c ∈ Q, (∀ g, ρ g (M₀.π c) = M₀.π c) → c ∈ CQt Q Z (Lgen M (LB M Q B)) := by
    intro c hcQ he
    refine ⟨hcQ, fun t ht => ?_⟩
    have h1 : φS ⟨t, ht⟩ (M₀.π c) = M₀.π c := by rw [← hρψ]; exact he _
    rw [← hφπ ⟨t, ht⟩ c hcQ] at h1
    have hcc := conj_mem_Q hc.hyp (hSM ht) hcQ
    rw [commutatorElement_def]
    refine (M₀.π_ker _ (Q.mul_mem hcc (Q.inv_mem hcQ))).mp ?_
    rw [M₀.π_mul _ hcc _ (Q.inv_mem hcQ), Tim79.QuadModel.pi_inv M₀ hcQ, h1, add_neg_cancel]
  have hfix : (∀ u v : M₀.E, (∀ g, ρ g u = u) → (∀ g, ρ g v = v) → M₀.B u v = 0) →
      ∀ e : M₀.E, (∀ g, ρ g e = e) → e = 0 := by
    intro hiso e he
    have hcomm : ∀ c ∈ CQt Q Z (Lgen M (LB M Q B)), ∀ d ∈ CQt Q Z (Lgen M (LB M Q B)),
        c * d = d * c := by
      intro c hc' d hd'
      have hfc : ∀ g, ρ g (M₀.π c) = M₀.π c := by
        intro g
        obtain ⟨m, rfl⟩ := hψs g
        rw [hρψ, ← hφπ m c hc'.1]
        have hcc := conj_mem_Q hc.hyp (hSM m.2) hc'.1
        have h1 : M₀.π ((m : G) * c * (m : G)⁻¹ * c⁻¹) = 0 :=
          (M₀.π_ker _ (Q.mul_mem hcc (Q.inv_mem hc'.1))).mpr (hc'.2 m m.2)
        rw [M₀.π_mul _ hcc _ (Q.inv_mem hc'.1), Tim79.QuadModel.pi_inv M₀ hc'.1] at h1
        exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h1)
      have hfd : ∀ g, ρ g (M₀.π d) = M₀.π d := by
        intro g
        obtain ⟨m, rfl⟩ := hψs g
        rw [hρψ, ← hφπ m d hd'.1]
        have hcc := conj_mem_Q hc.hyp (hSM m.2) hd'.1
        have h1 : M₀.π ((m : G) * d * (m : G)⁻¹ * d⁻¹) = 0 :=
          (M₀.π_ker _ (Q.mul_mem hcc (Q.inv_mem hd'.1))).mpr (hd'.2 m m.2)
        rw [M₀.π_mul _ hcc _ (Q.inv_mem hd'.1), Tim79.QuadModel.pi_inv M₀ hd'.1] at h1
        exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h1)
      have hB := hiso _ _ hfc hfd
      exact commutatorElement_eq_one_iff_mul_comm.mp
        ((GM.comm_eq_one_iff hD hc'.1 hd'.1).mpr hB)
    have hCZ := cqt_eq_of_commute hc.hyp hSM hNorm hcomm
    obtain ⟨c, hcQ, rfl⟩ := M₀.π_surj e
    have hmem : c ∈ CQt Q Z (Lgen M (LB M Q B)) := hCQt c hcQ he
    rw [hCZ] at hmem
    exact (M₀.π_ker c hcQ).mpr hmem
  have hdim : Module.finrank K M₀.E = 8 := by rw [hD.finrank_E hw (by omega)]
  obtain ⟨σ, θ, hθact, hθQ⟩ := hMod K (FiniteField.Extension K 2 3) hcardF hK4 M₀.E M₀.B M₀.Qf
    M₀.alt M₀.nondeg M₀.Qf_add M₀.Qf_smul hD.hyperbolic hdim ρ hρQ hρinj hfix
  refine ⟨FiniteField.Extension K 2 3, inferInstance, inferInstance, inferInstance, hcardF,
    hfinrank, ⟨⟨hcardF, hfinrank, θ, (D2.slMap σ).comp ψ, ?_, ?_, ?_, hθQ⟩⟩⟩
  · exact (D2.slMap_surjective σ).comp hψs
  · intro m
    show D2.slMap σ (ψ m) = 1 ↔ _
    rw [← hψk m]
    constructor
    · intro h
      exact D2.slMap_injective σ (by rw [h, map_one])
    · intro h
      rw [h, map_one]
  · intro m e
    show _ = D3.act _ ((D2.slMap σ (ψ m) : SL(2, FiniteField.Extension K 2 3)) :
      Mat2 (FiniteField.Extension K 2 3)) _
    rw [← hθact (ψ m) e, hρψ]

end D3G

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section D3Basic

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {S : Subgroup G} {φS : ↥S →* (M₀.E ≃ₗ[K] M₀.E)}
  {F : Type} [Field F] [Finite F] [Algebra K F]

namespace D3Data

variable (D : D3Data Q Z M₀ φS F)

include D in
theorem tau3 (a : F) :
    (FiniteField.frobeniusAlgHom K F) ((FiniteField.frobeniusAlgHom K F)
      ((FiniteField.frobeniusAlgHom K F) a)) = a := by
  haveI : Fintype F := Fintype.ofFinite F
  have h := FiniteField.pow_card a
  have hq : Fintype.card F = Fintype.card K * (Fintype.card K * Fintype.card K) := by
    rw [← Nat.card_eq_fintype_card, D.card_F, ← Nat.card_eq_fintype_card]
    ring
  simp only [FiniteField.coe_frobeniusAlgHom]
  rw [← pow_mul, ← pow_mul, ← hq]
  exact h

noncomputable def ptv (w : Fin 2 → F) : M₀.E :=
  D.θ.symm ⟨D3.pt (FiniteField.frobeniusAlgHom K F : F →+* F) w,
    D3.pt_mem_kForm _ D.tau3 w⟩

theorem θ_ptv (w : Fin 2 → F) :
    (D.θ (D.ptv w) : D3.Hyp F) = D3.pt (FiniteField.frobeniusAlgHom K F : F →+* F) w := by
  simp [ptv]

theorem φS_ptv (m : ↥S) (w : Fin 2 → F) :
    φS m (D.ptv w) = D.ptv ((D.p m : Mat2 F) *ᵥ w) := by
  apply D.θ.injective
  apply Subtype.ext
  rw [D.act, D.θ_ptv, D.θ_ptv, D3.act_pt]

theorem φS_eq_of_p_eq {m m' : ↥S} (h : D.p m = D.p m') : φS m = φS m' := by
  refine LinearEquiv.ext fun e => D.θ.injective (Subtype.ext ?_)
  rw [D.act, D.act, h]

theorem algebraMap_B (e f : M₀.E) :
    algebraMap K F (M₀.B e f) = D3.polar (D.θ e : D3.Hyp F) (D.θ f : D3.Hyp F) := by
  have h2 := congrArg (algebraMap K F) (M₀.Qf_add e f)
  rw [map_add, map_add, D.quad_eq, D.quad_eq, D.quad_eq] at h2
  have h3 : (D.θ (e + f) : D3.Hyp F) = (D.θ e : D3.Hyp F) + (D.θ f : D3.Hyp F) := by
    rw [map_add]
    rfl
  rw [h3, D3.quad_add] at h2
  linear_combination -h2

theorem algebraMap_B_ptv (v w : Fin 2 → F) :
    algebraMap K F (M₀.B (D.ptv v) (D.ptv w)) =
      (v 0 * w 1 + v 1 * w 0) * (FiniteField.frobeniusAlgHom K F) (v 0 * w 1 + v 1 * w 0) *
        (FiniteField.frobeniusAlgHom K F) ((FiniteField.frobeniusAlgHom K F)
          (v 0 * w 1 + v 1 * w 0)) := by
  rw [D.algebraMap_B, D.θ_ptv, D.θ_ptv, D3.polar_pt]
  rfl

theorem ptv_ne_zero {w : Fin 2 → F} (hw : w ≠ 0) : D.ptv w ≠ 0 := by
  intro h
  apply D3.pt_ne_zero (FiniteField.frobeniusAlgHom K F : F →+* F) hw
  rw [← D.θ_ptv, h, map_zero]
  rfl

theorem ptv_smul (s : F) (w : Fin 2 → F) : ∃ κ : K,
    algebraMap K F κ = s * (FiniteField.frobeniusAlgHom K F) s *
      (FiniteField.frobeniusAlgHom K F) ((FiniteField.frobeniusAlgHom K F) s) ∧
    D.ptv (s • w) = κ • D.ptv w := by
  haveI : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = Fintype.card K ^ 3 := by
    rw [← Nat.card_eq_fintype_card, D.card_F, ← Nat.card_eq_fintype_card]
  obtain ⟨κ, hκ⟩ := D3.nrm_mem_range hF s
  have hκ' : algebraMap K F κ = s * (FiniteField.frobeniusAlgHom K F) s *
      (FiniteField.frobeniusAlgHom K F) ((FiniteField.frobeniusAlgHom K F) s) := by
    rw [hκ, FiniteField.coe_frobeniusAlgHom]
    beta_reduce
    ring
  refine ⟨κ, hκ', D.θ.injective (Subtype.ext ?_)⟩
  rw [D.θ_ptv, map_smul, Submodule.coe_smul, D.θ_ptv, D3.pt_smul]
  funext i j k
  simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, hκ', AlgHom.coe_toRingHom]

theorem exists_smul_of_B_eq_zero {v w : Fin 2 → F} (hv : v ≠ 0)
    (h : M₀.B (D.ptv v) (D.ptv w) = 0) : ∃ κ : K, D.ptv w = κ • D.ptv v := by
  have h1 := D.algebraMap_B_ptv v w
  rw [h, map_zero] at h1
  have h2F : (2 : F) = 0 := by
    have := congrArg (algebraMap K F) (CharTwo.two_eq_zero : (2 : K) = 0)
    rwa [map_ofNat, map_zero] at this
  have hω0 : v 0 * w 1 + v 1 * w 0 = 0 := by
    by_contra hne
    have hτ : ∀ x : F, x ≠ 0 → (FiniteField.frobeniusAlgHom K F) x ≠ 0 := fun x hx =>
      (map_ne_zero (FiniteField.frobeniusAlgHom K F)).mpr hx
    exact mul_ne_zero (mul_ne_zero hne (hτ _ hne)) (hτ _ (hτ _ hne)) h1.symm
  have hdet : v 0 * w 1 - v 1 * w 0 = 0 := by
    linear_combination hω0 - (v 1 * w 0) * h2F
  obtain ⟨s, hs⟩ := D2.exists_smul_of_det_zero hv hdet
  rw [hs]
  obtain ⟨κ, -, hκ⟩ := D.ptv_smul s v
  exact ⟨κ, hκ⟩

end D3Data

end D3Basic

end

end CFSG.RankThree.GF2n.Smith81

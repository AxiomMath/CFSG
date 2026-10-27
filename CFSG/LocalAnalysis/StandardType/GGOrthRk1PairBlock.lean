module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1PairTriple
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1PairGrp
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Centralizer
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Iso
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Theta

public section

open Module Multiplicative QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

private theorem q2cO4b_fin3_cover :
    ∀ c a b l : Fin 3, a ≠ c → b ≠ c → a ≠ b → l ≠ c → l = a ∨ l = b := by
  decide

private theorem q2cO4b_orthDerived_le_orthogonalGroup (Q : QuadraticForm K V) :
    orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [orthDerived, Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
    ((TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
      ((TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem h₁ h₂)
      ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem h₁))
    ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem h₂)

private theorem q2cO4b_block_eq_rankOne {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ}
    (Δ : TBJOmData Q p A r) (hr : 3 ≤ r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f : ℕ) (hf : Nat.card K = 2 ^ f) (K' : Type) [Field K'] [Finite K'] [CharP K' 2]
    [Algebra K K'] (hK' : Nat.card K' = (2 ^ f) ^ 2)
    (hσ : IsUnitaryInvolution (unitaryInvolution K' 2 f))
    (T : NormTriple Q (unitaryInvolution K' 2 f)) (ζ : K')
    (idx : Fin 3 → Fin r)
    (hT : ∀ (g : Fin r → Multiplicative (ZMod p)) (z : Fin 3 → K'),
      Δ.τ g (T.incl z) = T.incl (fun l => ζ ^ (toAdd (g (idx l))).val * z l))
    (c a b : Fin 3) (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b) (hne : idx a ≠ idx b) :
    ((embSUid (unitaryInvolution K' 2 f) c).range).map (T.toEmbedding hσ).theta =
      Δ.rankOne (idx a) (idx b) := by
  let B : Subgroup (SUid (unitaryInvolution K' 2 f) 3) :=
    (embSUid (unitaryInvolution K' 2 f) c).range
  let θ : SUid (unitaryInvolution K' 2 f) 3 →* (V ≃ₗ[K] V) := (T.toEmbedding hσ).theta
  have hcenter : ∀ g ∈ B, θ g ∈
      Subgroup.centralizer (Δ.reflFixed (idx a) (idx b) : Set (V ≃ₗ[K] V)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [TBJOmData.reflFixed, Subgroup.mem_map] at hh
    obtain ⟨g₀, hg₀, rfl⟩ := hh
    have hg₀eq : g₀ (idx a) = g₀ (idx b) := by
      have hmem := hg₀
      simp only [reflFixedCoord, MonoidHom.mem_ker, MonoidHom.div_apply] at hmem
      simpa using (div_eq_one.mp hmem)
    simp only [B, MonoidHom.mem_range] at hg
    obtain ⟨A₀, rfl⟩ := hg
    have hmem_range : Δ.τ g₀ ∈ Δ.τ.range := MonoidHom.mem_range.mpr ⟨g₀, rfl⟩
    have hSA : Δ.τ g₀ ∈ A := by
      rwa [Δ.τ_range] at hmem_range
    have hS : ∀ x : V, Q (Δ.τ g₀ x) = Q x :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (q2cO4b_orthDerived_le_orthogonalGroup Q (hAΩ hSA))
    let a' : Fin 3 → K' := fun l => ζ ^ (toAdd (g₀ (idx l))).val
    let a'' : Fin 3 → K' := fun l => ζ ^ (toAdd (g₀⁻¹ (idx l))).val
    have ha'b : a' a = a' b := by
      simp only [a']
      rw [hg₀eq]
    have hac' : ∀ l l' : Fin 3, l ≠ c → l' ≠ c → a' l = a' l' := by
      intro l l' hlc hl'c
      have hl : l = a ∨ l = b := q2cO4b_fin3_cover c a b l hac hbc hab hlc
      have hl' : l' = a ∨ l' = b := q2cO4b_fin3_cover c a b l' hac hbc hab hl'c
      rcases hl with rfl | rfl <;> rcases hl' with rfl | rfl
      · rfl
      · exact ha'b
      · exact ha'b.symm
      · rfl
    have hM : ∀ z : Fin 3 → K', Δ.τ g₀ (T.incl z) = T.incl (diagMap (K := K) a' z) := by
      intro z
      rw [hT g₀ z]
      rfl
    have hM' : ∀ z : Fin 3 → K',
        (Δ.τ g₀)⁻¹ (T.incl z) = T.incl (diagMap (K := K) a'' z) := by
      intro z
      rw [show (Δ.τ g₀)⁻¹ = Δ.τ g₀⁻¹ by rw [← map_inv]]
      rw [hT g₀⁻¹ z]
      rfl
    have hgz : ∀ z : Fin 3 → K',
        diagMap (K := K) a' (embSUid (unitaryInvolution K' 2 f) c A₀ • z) =
          embSUid (unitaryInvolution K' 2 f) c A₀ • diagMap (K := K) a' z :=
      fun z => diagMap_smul_embSUid c a' hac' A₀ z
    exact normTriple_theta_mul_comm hσ T (Δ.τ g₀) hS (diagMap (K := K) a')
      (diagMap (K := K) a'') hM hM' (embSUid (unitaryInvolution K' 2 f) c A₀) hgz
  have homega : ∀ g ∈ B, θ g ∈ orthDerived Q := by
    intro g _
    exact theta_mem_orthDerived hf hK' T hσ g
  have hgen : B.map θ ≤ Δ.rankOne (idx a) (idx b) := by
    rw [TBJOmData.rankOne, CFSG.StandardType.ggOTwoPrime]
    rw [show B = Subgroup.closure {g : SUid (unitaryInvolution K' 2 f) 3 |
        g ∈ B ∧ g ^ 2 = 1} from (embSUid_range_closure hf hK' c).symm]
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro y ⟨g, hg, rfl⟩
    exact ⟨⟨hcenter g hg.1, homega g hg.1⟩,
      ⟨1, by rw [show (2 : ℕ) ^ 1 = 2 by norm_num, ← map_pow, hg.2, map_one]⟩⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  have hcardBmap : Nat.card (B.map θ) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.card_map_of_injective (T.toEmbedding hσ).theta_injective]
    exact embSUid_range_natCard hf hK' c
  obtain ⟨φ, hφinj, hφrange, hφQ, hφτ⟩ :=
    Δ.exists_rk1_isometry hp2 hAΩ (idx a) (idx b) hne
  obtain ⟨θ₁, -, -, hθ₁inj, -, -, hθ₁uniq⟩ :=
    Δ.exists_rk1_theta hfix (idx a) (idx b) hne φ hφinj hφrange hφQ hφτ
  have hRle := Δ.rankOne_le_range hp2 hfix (idx a) (idx b)
    φ hφinj hφrange hφQ hφτ θ₁ hθ₁uniq
  have hcardR : Nat.card (Δ.rankOne (idx a) (idx b)) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    calc
      _ ≤ Nat.card θ₁.range := Subgroup.card_le_of_le hRle
      _ = _ := by
        rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hθ₁inj]
        exact Subgroup.card_top
  exact Subgroup.eq_of_le_of_card_ge hgen (hcardR.trans_eq hcardBmap.symm)

theorem TBJOmData.exists_pair_blocks {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ} (Δ : TBJOmData Q p A r)
    (hr : 3 ≤ r) (hpq : p ∣ Nat.card K + 1)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f : ℕ) (hf : Nat.card K = 2 ^ f) (K' : Type) [Field K'] [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ θ : Su K' 2 f 3 →* (V ≃ₗ[K] V), Function.Injective θ ∧ θ.range ≤ orthDerived Q ∧
      (B12 K' 2 f).map θ = Δ.rankOne i j ∧ (B23 K' 2 f).map θ = Δ.rankOne j k ∧
      θ.range ≤ Subgroup.centralizer
        ((Δ.reflFixed i j ⊓ Δ.reflFixed j k : Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) := by
  obtain ⟨inst, T, ζ, hT⟩ :=
    Δ.exists_normTriple hp2 hAΩ hf hpq K' hK' i j k hij hjk hik
  letI : Algebra K K' := inst
  have hσ : IsUnitaryInvolution (unitaryInvolution K' 2 f) :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK'
  let idx : Fin 3 → Fin r := ![i, j, k]
  refine ⟨(T.toEmbedding hσ).theta, (T.toEmbedding hσ).theta_injective, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact theta_mem_orthDerived hf hK' T hσ g
  · exact q2cO4b_block_eq_rankOne hp2 hAΩ Δ hr hfix f hf K' hK' hσ T ζ idx hT
      2 0 1 (by decide) (by decide) (by decide) hij
  · exact q2cO4b_block_eq_rankOne hp2 hAΩ Δ hr hfix f hf K' hK' hσ T ζ idx hT
      0 1 2 (by decide) (by decide) (by decide) hjk
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hh.1
    obtain ⟨v, hv, huv⟩ := Subgroup.mem_map.mp hh.2
    have huv' : v = u := Δ.τ_inj huv
    subst v
    have huij : u i = u j := by
      have h := hu
      simp only [reflFixedCoord, MonoidHom.mem_ker, MonoidHom.div_apply] at h
      exact div_eq_one.mp h
    have hujk : u j = u k := by
      have h := hv
      simp only [reflFixedCoord, MonoidHom.mem_ker, MonoidHom.div_apply] at h
      exact div_eq_one.mp h
    have hidx : ∀ l : Fin 3, u (idx l) = u i := by
      intro l
      fin_cases l
      · rfl
      · exact huij.symm
      · exact (huij.trans hujk).symm
    let a : Fin 3 → K' := fun l => ζ ^ (toAdd (u (idx l))).val
    let a' : Fin 3 → K' := fun l => ζ ^ (toAdd (u⁻¹ (idx l))).val
    have hS : ∀ x : V, Q (Δ.τ u x) = Q x :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (q2cO4b_orthDerived_le_orthogonalGroup Q
          (hAΩ (by
            have huA : Δ.τ u ∈ Δ.τ.range := ⟨u, rfl⟩
            simpa only [Δ.τ_range] using huA)))
    have hM : ∀ z, Δ.τ u (T.incl z) = T.incl (diagMap (K := K) a z) := by
      intro z
      rw [hT u z]
      rfl
    have hM' : ∀ z, (Δ.τ u)⁻¹ (T.incl z) = T.incl (diagMap (K := K) a' z) := by
      intro z
      rw [← map_inv, hT u⁻¹ z]
      rfl
    apply normTriple_theta_mul_comm hσ T (Δ.τ u) hS
      (diagMap (K := K) a) (diagMap (K := K) a') hM hM' g
    intro z
    funext l
    simp only [smul_def, diagMap_apply, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three]
    simp only [a, hidx]
    ring

end OrthTorus

end CFSG.StandardType

end

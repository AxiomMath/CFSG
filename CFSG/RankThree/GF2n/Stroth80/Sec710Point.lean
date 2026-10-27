module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Q7Moved

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_point_le_of_singular (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (hW : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → Q' x = Q' y →
      ∃ A ∈ X, ((A : GL ι K) : Matrix ι ι K) *ᵥ x = y)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {g : G} (hg : g ∈ M) {u : ι → K} (hu0 : u ≠ 0) (hQu : Q' u = 0)
    (hu : ∃ k : ↥(Vt M (LB M Q B) B Z t),
      (k : G) ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) ∧ secVec ψ k = u) :
    ∃ r ∈ Rt M (LB M Q B) t,
      conjSubgroup r B ⊔ Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hVR := hc.Rt_normalizes_Vt ht
  have hsing := hc.omega_singular h34 hRoot hs hnat hK E hQ h3 hX φ hφ ψ hψ
  obtain ⟨u₀, hQu₀, hu₀0, hBu, -, -, -⟩ :=
    hc.omega_points_core h34 hRoot hs hnat hK E hQ h3 hX φ hφ hker ψ hψ hsing
  obtain ⟨nn, γ, M₀, hglob, θ, hθ⟩ := hc.exists_globalRingEquiv ht hK hX φ hφ ψ hψ
  obtain ⟨A, hAX, hAu⟩ := hW u₀ u hu₀0 hu0 (by rw [hQu₀, hQu])
  obtain ⟨r, hrA⟩ := MonoidHom.mem_range.mp (hφ ▸ hAX)
  obtain ⟨k, hkg, hku⟩ := hu
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  refine ⟨r, r.2, sup_le (fun b' hb' => ?_) (hc.Z_le_conjSubgroup sec39_Z_le_Vt hg)⟩
  rw [mem_conjSubgroup] at hb'
  have hbB : (r : G)⁻¹ * b' * r ∈ B := hb'
  have hbV : (r : G)⁻¹ * b' * r ∈ Vt M (LB M Q B) B Z t := hBV hbB
  have hb'V : b' ∈ Vt M (LB M Q B) B Z t := by
    have := (Subgroup.mem_normalizer_iff.mp (hVR r.2) ((r : G)⁻¹ * b' * r)).mp hbV
    simpa [mul_assoc] using this
  obtain ⟨c, hc'⟩ := (hBu (secVec ψ ⟨(r : G)⁻¹ * b' * r, hbV⟩)).mp ⟨⟨_, hbV⟩, hbB, rfl⟩
  have h1 : secVec ψ ⟨b', hb'V⟩ = c • u := by
    have := hψ r ⟨(r : G)⁻¹ * b' * r, hbV⟩ ⟨b', hb'V⟩ (by
      show b' = (r : G) * ((r : G)⁻¹ * b' * r) * (r : G)⁻¹
      group)
    change secVec ψ ⟨b', hb'V⟩ = (φ r : Matrix ι ι K) *ᵥ secVec ψ ⟨(r : G)⁻¹ * b' * r, hbV⟩ at this
    rw [this, hc', Matrix.mulVec_smul, hrA, hAu]
  obtain ⟨w, hw, hwπ⟩ := hc.exists_smul_mem_inf_conj hglob hg (θ.symm c)
    (Subgroup.mem_inf.mpr ⟨k.2, hkg⟩)
  obtain ⟨hwV, hwg⟩ := Subgroup.mem_inf.mp hw
  have h2 : secVec ψ ⟨w, hwV⟩ = c • u := by
    have := hθ (θ.symm c) k ⟨w, hwV⟩ hwπ
    rw [RingEquiv.apply_symm_apply, hku] at this
    exact this
  have h3' : b' * w⁻¹ ∈ Z := by
    have := (secVec_eq_iff ψ ⟨b', hb'V⟩ ⟨w, hwV⟩).mp (h1.trans h2.symm)
    exact this
  have e : b' = (b' * w⁻¹) * w := by group
  rw [e]
  exact (conjSubgroup g (Vt M (LB M Q B) B Z t)).mul_mem
    (hc.Z_le_conjSubgroup sec39_Z_le_Vt hg h3') hwg

end CFSG.RankThree.GF2n.Stroth80

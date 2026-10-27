module

public import CFSG.RankThree.PartOne.D4RC.Lines

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Center

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem rcz_eq_one (F : RclFrame ℓ f K σ ε p L) {w : ModGL TwistTag.D4.tag L} {i j : Fin 4}
    (hij : i ≠ j)
    (hi : w ∈ subtorusSigma F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) (d4Sigma i))
    (hj : w ∈ subtorusSigma F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) (d4Sigma j)) :
    w = 1 := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hT := twistedTorus_D4_eq_map_of_weylImage (iterateFrobenius L ℓ f) F.hn F.w F.hnw
    (d4T36M ε) F.hw
  obtain ⟨hiT, hiC⟩ := hi
  obtain ⟨-, hjC⟩ := hj
  rw [hT] at hiT
  obtain ⟨b, hb, rfl⟩ := hiT
  have hci := (rootDiagUnit_mem_centralizer_rootSpan_iff b
    (fun α hα => isRoot_of_mem_d4Sigma hα)).1 hiC
  have hcj := (rootDiagUnit_mem_centralizer_rootSpan_iff b
    (fun α hα => isRoot_of_mem_d4Sigma hα)).1 hjC
  have hu : ∀ k : Fin 4, trialityU k ∈ d4Sigma k := fun k => mem_trialitySigma.2 List.mem_cons_self
  by_contra hne
  have hb1 : b ≠ 1 := fun h => hne (by rw [h, map_one])
  rcases d4T36_rootCharKernel_cases F.hε hb hb1 with h0 | ⟨k, hk⟩
  · have hmem : trialityU i ∈ rootCharKernel b := ⟨isRoot_of_mem_d4Sigma (hu i), hci _ (hu i)⟩
    rw [h0] at hmem
    exact hmem
  · have hmi : trialityU i ∈ trialitySigma k := by
      rw [← hk]
      exact ⟨isRoot_of_mem_d4Sigma (hu i), hci _ (hu i)⟩
    have hmj : trialityU j ∈ trialitySigma k := by
      rw [← hk]
      exact ⟨isRoot_of_mem_d4Sigma (hu j), hcj _ (hu j)⟩
    have h1 : i = k := by
      by_contra h
      exact Set.disjoint_left.1 (pairwise_disjoint_trialitySigma h) (hu i) hmi
    have h2 : j = k := by
      by_contra h
      exact Set.disjoint_left.1 (pairwise_disjoint_trialitySigma h) (hu j) hmj
    exact hij (h1.trans h2.symm)

theorem rcz_mem_subtorus (F : RclFrame ℓ f K σ ε p L) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) {z : 𝒞[K, σ]} (hz : z ∈ Subgroup.centralizer ({x} : Set 𝒞[K, σ]))
    (hP : ∀ u ∈ rclPx sp, z * u = u * z) :
    F.g0⁻¹ * triEmb K σ L (sp.c * z * sp.c⁻¹) * F.g0 ∈
      subtorusSigma F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) (d4Sigma i) := by
  obtain ⟨-, -, -, -, -, hQψ, -, hcent⟩ := rcl_psi_props F sp
  have h := hcent ⟨z, hz⟩ fun u hu => by
    obtain ⟨v, hv⟩ := hQψ hu
    have hvP : (v : 𝒞[K, σ]) ∈ rclPx sp := (mem_rclPx_iff sp v.2).2 (by rw [hv]; exact hu)
    have hzv : (⟨z, hz⟩ : Subgroup.centralizer ({x} : Set 𝒞[K, σ])) * v =
        v * ⟨z, hz⟩ := Subtype.ext (hP v hvP)
    rw [← hv, ← map_mul, hzv, map_mul]
  rwa [rclPsi, d4QPsi_apply] at h

variable {F : RclFrame ℓ f K σ ε p L} {S : Sylow p 𝒞[K, σ]} {c : 𝒞[K, σ]}
  {E : Subgroup 𝒞[K, σ]}

theorem rcz_eq_one_of_comm (Ln : RceLines F S c E) {j : Fin 4} (hj : j ≠ 0) {z : 𝒞[K, σ]}
    (hz0 : z ∈ Subgroup.centralizer ({Ln.x 0} : Set 𝒞[K, σ]))
    (hzj : z ∈ Subgroup.centralizer ({Ln.x j} : Set 𝒞[K, σ]))
    (hP0 : ∀ u ∈ rclPx (Ln.sp 0), z * u = u * z) (hPj : ∀ u ∈ rclPx (Ln.sp j), z * u = u * z) :
    z = 1 := by
  have h0 := rcz_mem_subtorus F (Ln.sp 0) hz0 hP0
  have h1 := rcz_mem_subtorus F (Ln.sp j) hzj hPj
  rw [Ln.hspc] at h0 h1
  have hw := rcz_eq_one F hj.symm h0 h1
  have h2 : triEmb K σ L (c * z * c⁻¹) = triEmb K σ L 1 := by
    rw [map_one]
    calc triEmb K σ L (c * z * c⁻¹)
        = F.g0 * (F.g0⁻¹ * triEmb K σ L (c * z * c⁻¹) * F.g0) * F.g0⁻¹ := by group
      _ = 1 := by rw [hw]; group
  have h3 := triEmb_injective h2
  calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
    _ = 1 := by rw [h3]; group

theorem rcz_center (Ln : RceLines F S c E) {j : Fin 4} (hj : j ≠ 0) {Γ : Subgroup 𝒞[K, σ]}
    (hEΓ : E ≤ Γ) (hP0 : rclPx (Ln.sp 0) ≤ Γ) (hPj : rclPx (Ln.sp j) ≤ Γ) :
    Subgroup.center ↥Γ = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  have hc : ∀ g ∈ Γ, (z : 𝒞[K, σ]) * g = g * z := fun g hg =>
    (congrArg Subtype.val (hz ⟨g, hg⟩)).symm
  have hcx : ∀ k, (z : 𝒞[K, σ]) ∈ Subgroup.centralizer ({Ln.x k} : Set 𝒞[K, σ]) := fun k => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc _ (hEΓ (Ln.hx k).1)
  have := rcz_eq_one_of_comm Ln hj (hcx 0) (hcx j) (fun u hu => hc u (hP0 hu))
    (fun u hu => hc u (hPj hu))
  exact Subgroup.mem_bot.2 (Subtype.ext this)

end Center

end CFSG.RankThree.PartOne.D4RC

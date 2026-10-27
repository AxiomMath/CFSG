module

public import CFSG.LocalAnalysis.StandardType.GGTwE6BigLineDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqA1
public import Certificates.Certificate13657
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentrePerm
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreLang
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDAll

public section

namespace CFSG.StandardType

section A4A1Helper

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs

theorem SCFourCover.statedClassicalModel_rationalComponent_a4a1
    {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {q : ℕ} {h : twistedE6InndiagGL K σ} (D : TwE6LineLang K σ q h)
    (h3q : 3 ∣ q + 1) (hdim : twE6MatFixDim K σ h = 28) (hq2 : D.S.D.q = 2)
    (i : KernelComponent (rootCharHom D.a))
    (hqs : CFSG.IsQuasisimple (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) :
    StatedClassicalModel
      (↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
        Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i))
      .PSU 5 (ringChar K) D.e := by
  classical
  have h22 : (kernelRoots (rootCharHom D.a)).ncard = 22 := by
    have hker := D.hker
    omega
  obtain ⟨m, hm, v, ψ₀, σ₀, hψ₀, hn₀, hΨ₀, -, hS1⟩ :=
    KSConn.conn_class_data D.hL3 D.hap (Or.inl h22) i
  have hψ := hψ₀.transport v
  have hnorm : ∀ x y, x ≠ y → iform (v • σ₀ x y) (v • σ₀ x y) = 2 := fun x y hxy => by
    rw [CFSG.LieType.Chevalley.iform_smul]
    exact hn₀ x y hxy
  have hΨ : componentRoots (rootCharHom D.a) i = frameRoots (fun x y => v • σ₀ x y) := by
    rw [hΨ₀, IsSLFrame.frameRoots_smul]
  obtain ⟨t, ht, Fr, hFr, hΦ0⟩ := D.hS
  obtain rfl : t = .E6 := by
    cases t
    · rfl
    · exact absurd ht (by decide)
  have hΦ : D.S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr :=
    MonoidHom.ext fun g => (hΦ0 g).trans rfl
  have h3q' : 3 ∣ D.S.D.q + 1 := by
    rw [D.hSq, ← D.hqe]
    exact h3q
  obtain ⟨u, hu, hρ⟩ := KSConn.exists_rho_neg_weyl_of_conn D.S hFr hΦ D.hT D.hap h3q'
    (by rw [h22]; simp)
  obtain ⟨π, hπ1⟩ := KSConn.exists_unitary_perm_of_rho_eq_neg i hψ hnorm hΨ D.S.ρ hu hρ
  have hstab : ∀ γ ∈ componentRoots (rootCharHom D.a) i,
      D.S.ρ γ ∈ componentRoots (rootCharHom D.a) i := by
    intro γ hγ
    rw [hΨ] at hγ ⊢
    obtain ⟨x, y, hxy, rfl⟩ := hγ
    exact ⟨π y, π x, fun hyx => hxy (π.injective hyx).symm, hπ1 x y hxy⟩
  have hfin : (componentRoots (rootCharHom D.a) i).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  have hs1 := componentOrbitLength_eq_one hfin hstab
  rcases hm with rfl | rfl | rfl
  ·
    obtain ⟨hrank, hncard, -⟩ := hS1 rfl
    have hfix : (D.S.ρ : (Fin Tag.E6.rank → ℤ) → _) ''
        componentRoots (rootCharHom D.a) i = componentRoots (rootCharHom D.a) i := by
      have h := ((hfin.injOn_iff_bijOn_of_mapsTo hstab).1 D.S.ρ.injective.injOn).image_eq
      simpa using h
    have hne := orbit_ne_of_rank_one_quasisimple
      D.S hq2 D.hT i hrank hncard hqs
    exact absurd hfix hne
  ·
    have hπ : ∀ x y, x ≠ y → (D.S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength
        D.S.ρ (componentRoots (rootCharHom D.a) i)] (v • σ₀ x y) = v • σ₀ (π y) (π x) :=
      fun x y hxy => by
        rw [hs1, Function.iterate_one]
        exact hπ1 x y hxy
    have hmodel := KSExact.rationalComponent_suN_model D.S D.hT i (ν := 4 + 1) (by norm_num) hψ
      hΨ π hπ D.hℓ D.hchar D.he D.hSq (by simp)
    rw [hs1, Nat.mul_one] at hmodel
    exact hmodel
  ·
    exfalso
    have hc : (componentRoots (rootCharHom D.a) i).ncard = 30 := by
      rw [hΨ]
      have hframe := CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hψ one_ne_zero
        fun x y hxy => (hnorm x y hxy).trans (mul_one 2).symm
      omega
    have hfinK : (kernelRoots (rootCharHom D.a)).Finite :=
      (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
    have hle : (componentRoots (rootCharHom D.a) i).ncard ≤ 22 := by
      rw [← h22]
      exact Set.ncard_le_ncard (fun γ hγ => hγ.1) hfinK
    omega

end A4A1Helper

open CFSG CFSG.Assembly CFSG.Blueprint TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.SCFourCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

private theorem ggTwE6BigA4A1_eq_twA_of_dict {lab : LargeEvenLabel} {r f : ℕ}
    (ht : markTag lab = .PSU) (hc : markChar lab = 2) (hr : markRank lab = r + 1)
    (hf : markDeg lab = f) (h3 : r ≠ 3) : lab = ⟨.twA, r, f⟩ := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> dsimp only [markTag, markRank, markChar, markDeg] at ht hc hr hf
  case twA =>
    obtain rfl := Nat.add_right_cancel hr
    subst hf
    rfl
  case twD =>
    split_ifs at ht hr <;>
      first | exact absurd ht (by decide) | exact absurd (by omega) h3
  case G2der => exact absurd hc (by decide)
  all_goals ((try split_ifs at ht) <;> exact absurd ht (by decide))

theorem ggTwE6BigA4A1_holds :
    GGTwE6BigA4A1 := by
  intro K _ _ σ hK hσ h hh1 hh3 hdim J hJ
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; decide
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ 2 hK3 hσ hK2 (by norm_num) h hh1 hh3
  have he : D.e = 1 := by
    have h1 := D.hqe
    rw [hchar] at h1
    have h2 : (2 : ℕ) ^ D.e = 2 ^ 1 := by rw [← h1, pow_one]
    exact Nat.pow_right_injective (le_refl 2) h2
  have hdq : D.S.D.q = 2 := by rw [D.hSq, ← D.hqe]
  obtain ⟨i, hqs, hJi⟩ := D.exists_rationalComponent hJ
  let eJ := (J.equivMapOfInjective D.ι D.hinj).trans (MulEquiv.subgroupCongr hJi)
  have hmodel :=
    statedClassicalModel_rationalComponent_a4a1 D (by norm_num) hdim hdq i hqs
  have hlie : LieModel
      (↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
        Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i))
      .PSU 5 2 1 := by
    rw [hchar, he] at hmodel
    exact Or.inl ⟨by decide, hmodel⟩
  have hmark : LargeEvenMarking
      ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)
      fun lab' _ _ _ _ _ => lab' = ⟨.twA, 4, 1⟩ :=
    largeEvenMarking_mono
      (fun lab R _ I F θ h => ggTwE6BigA4A1_eq_twA_of_dict (r := 4) (f := 1)
        h.1 h.2.2.1 h.2.1 h.2.2.2 (by decide))
      (largeEvenMarking_of_lieModel_centerQuot (Group.isPerfect_def.mp hqs.1) hlie)
  exact largeEvenMarking_of_mulEquiv eJ hmark

end CFSG.StandardType

end

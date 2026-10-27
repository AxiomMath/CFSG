module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesFix
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section Steinberg

open TableBExc.E6Three

variable {K : Type} [Field K]

theorem exists_inndiag_conj_eq_on_diag3 [Finite K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    {α : MulAut (adjointGroup .E6 K)} (hα : α ^ 3 = 1) :
    ∃ h ∈ (hatAut .E6 K).range, ∀ x : Fin Tag.E6.rank → ZMod 3,
      α * diag3 ζ hζ (Multiplicative.ofAdd x) * α⁻¹ =
        h * diag3 ζ hζ (Multiplicative.ofAdd x) * h⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero (exactE .E6) := ⟨(exactE_pos .E6).ne'⟩
  obtain ⟨Θ, -, hΘ, -, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hαe⟩ := exists_conj_mul_exactNormalAut (K := K) (Or.inl rfl) α
  have hpt : ∀ h : adjointGroup .E6 K, (α h : ModGL .E6 K) = (g : ModGL .E6 K) *
      rootDiagUnit .E6 a * exactQ .E6 K (ε : ℕ) *
      Units.map (entrywiseHom σ.toRingHom) (h : ModGL .E6 K) *
        (exactQ .E6 K (ε : ℕ))⁻¹ * (rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹ := by
    intro h
    rw [hαe, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  have hΘα : Θ α = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE .E6))) :=
    hΘ α g a σ ε hpt
  have hcube : Θ α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hσ3 : σ ^ 3 = 1 := by
    have h := congrArg (MonoidHom.fst (RingAut K)
      (Multiplicative (ZMod (exactE .E6)))) hcube
    rw [map_pow, hΘα, map_one] at h
    simpa using h
  have hε0 : (ε : ℕ) = 0 := by
    have h := congrArg (MonoidHom.snd (RingAut K)
      (Multiplicative (ZMod (exactE .E6)))) hcube
    rw [map_pow, hΘα, map_one] at h
    have hz : (((ε : ℕ)) : ZMod (exactE .E6)) = 0 := by
      set z : ZMod (exactE .E6) := ((ε : ℕ) : ZMod (exactE .E6)) with hzdef
      change (Multiplicative.ofAdd z) ^ 3 = 1 at h
      have h3 : (3 : ℕ) • z = z := by
        have : ∀ w : ZMod (exactE .E6), (3 : ℕ) • w = w := by decide
        exact this z
      rw [← ofAdd_nsmul, h3] at h
      have hz0 : z = 0 := (ofAdd_eq_one).1 h
      rwa [hzdef] at hz0
    have hlt : (ε : ℕ) < 2 := by simpa [exactE] using ε.2
    have hdvd : 2 ∣ (ε : ℕ) := by
      have := (ZMod.natCast_eq_zero_iff (ε : ℕ) (exactE .E6)).1 hz
      simpa [exactE] using this
    exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
  have hN0 : exactNormalAut .E6 K a σ (ε : ℕ) = exactNormalAut .E6 K a σ 0 := by rw [hε0]
  have hαe0 : α = MulAut.conj g * exactNormalAut .E6 K a σ 0 := by rw [hαe, hN0]
  have hmul_diag : exactNormalAut .E6 K a 1 0 * exactNormalAut .E6 K 1 σ 0 =
      exactNormalAut .E6 K a σ 0 := by
    rw [exactNormalAut_diag_mul (τ := Tag.E6) (K := K) a 1 σ 0, mul_one]
  refine ⟨MulAut.conj g * rootDiagAutHom .E6 K a, ?_, ?_⟩
  · rw [hatAut_range_eq_sup]
    exact Subgroup.mul_mem_sup ⟨g, rfl⟩ ⟨a, rfl⟩
  · intro x
    set b : Fin Tag.E6.rank → Kˣ := zetaVec ζ hζ x with hb
    have ha1 : rootDiagAutHom .E6 K a = exactNormalAut .E6 K a 1 0 :=
      rootDiagAut_eq_exactNormalAut (K := K) a
    have hαh : α =
        (MulAut.conj g * rootDiagAutHom .E6 K a) * exactNormalAut .E6 K 1 σ 0 := by
      rw [hαe0, ← hmul_diag, ← ha1]
      group
    have hb3u : ∀ j : Fin Tag.E6.rank, (b j) ^ 3 = 1 := by
      intro j
      rw [hb]
      rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    have hb3 : ∀ j : Fin Tag.E6.rank, ((b j : K)) ^ 3 = 1 := by
      intro j
      rw [← Units.val_pow_eq_pow_val, hb3u j, Units.val_one]
    have hbfix : ∀ j : Fin Tag.E6.rank,
        Units.map σ.toRingHom.toMonoidHom (b j) = b j := by
      intro j
      refine Units.ext ?_
      rw [Units.coe_map]
      exact CFSG.StandardType.ExcFrames.ringAut_apply_eq_self (L := K) hσ3 (hb3 j)
    have hcomm : exactNormalAut .E6 K 1 σ 0 * exactNormalAut .E6 K b 1 0 =
        exactNormalAut .E6 K b 1 0 * exactNormalAut .E6 K 1 σ 0 := by
      rw [exactNormalAut_mul (τ := Tag.E6) (K := K) 1 b σ 1 0 0,
        exactNormalAut_diag_mul (τ := Tag.E6) (K := K) b 1 σ 0]
      have harg : (fun j : Fin Tag.E6.rank => (1 : Fin Tag.E6.rank → Kˣ) j *
          Units.map σ.toRingHom.toMonoidHom (b ((exactPerm Tag.E6 0).symm j))) = b := by
        funext j
        rw [exactPerm_zero]
        show (1 : Kˣ) * Units.map σ.toRingHom.toMonoidHom (b j) = b j
        rw [one_mul, hbfix j]
      rw [harg]
      simp only [mul_one, add_zero]
    have hconjN1 : exactNormalAut .E6 K 1 σ 0 * exactNormalAut .E6 K b 1 0 *
        (exactNormalAut .E6 K 1 σ 0)⁻¹ = exactNormalAut .E6 K b 1 0 := by
      rw [hcomm]
      group
    have hδN : diag3 ζ hζ (Multiplicative.ofAdd x) = exactNormalAut .E6 K b 1 0 := by
      rw [hb]
      exact (show diag3 ζ hζ (Multiplicative.ofAdd x) =
          rootDiagAut .E6 K (zetaVec ζ hζ x) from rfl).trans
        (rootDiagAut_eq_exactNormalAut (K := K) (zetaVec ζ hζ x))
    have hN1δ : exactNormalAut .E6 K 1 σ 0 * diag3 ζ hζ (Multiplicative.ofAdd x) *
        (exactNormalAut .E6 K 1 σ 0)⁻¹ = diag3 ζ hζ (Multiplicative.ofAdd x) := by
      rw [hδN]
      exact hconjN1
    calc α * diag3 ζ hζ (Multiplicative.ofAdd x) * α⁻¹
        = (MulAut.conj g * rootDiagAutHom .E6 K a) *
            (exactNormalAut .E6 K 1 σ 0 * diag3 ζ hζ (Multiplicative.ofAdd x) *
              (exactNormalAut .E6 K 1 σ 0)⁻¹) *
            (MulAut.conj g * rootDiagAutHom .E6 K a)⁻¹ := by
          rw [hαh, mul_inv_rev]
          group
      _ = (MulAut.conj g * rootDiagAutHom .E6 K a) * diag3 ζ hζ (Multiplicative.ofAdd x) *
            (MulAut.conj g * rootDiagAutHom .E6 K a)⁻¹ := by rw [hN1δ]

end Steinberg

end NoOffE6Three

end CFSG.StandardType

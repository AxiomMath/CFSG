module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamAut
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFNW
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeylEx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFDefs
import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem
open CFSG.StandardType CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

omit [CharP K 2] in
private theorem omfoi_finrank_commSpace_reflect {n : ℕ}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    finrank K (commSpace (CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus n K b c)
      (planeVec n planeOne))) = 1 := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirrQ
  let _ : Invertible (quadMinus n K b c (planeVec n planeOne)) := by
    rw [quadMinus_planeOne]
    exact invertibleOne
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
  exact finrank_commSpace_reflection hQ (planeVec n planeOne)

private theorem omfoi_exists_conj {n : ℕ} (hn : 4 ≤ n) (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {A M : Vm n K ≃ₗ[K] Vm n K}
    (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)) (hAA : A * A = 1)
    (hMO : M ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)) (hMM : M * M = 1)
    (hrank : finrank K (commSpace A) = finrank K (commSpace M))
    (hodd : Odd (finrank K (commSpace M))) :
    ∃ g : spinGroup (quadMinus n K b c),
      spinAction (quadMinus n K b c) g * M * (spinAction (quadMinus n K b c) g)⁻¹ = A := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirrQ
  have hne : ∀ {T : Vm n K ≃ₗ[K] Vm n K}, Odd (finrank K (commSpace T)) → T ≠ 1 := by
    rintro T hT rfl
    have h0 : commSpace (1 : Vm n K ≃ₗ[K] Vm n K) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
      simp
    rw [h0, finrank_bot] at hT
    exact Nat.not_odd_zero hT
  have hAodd : Odd (finrank K (commSpace A)) := hrank ▸ hodd
  have hMord : orderOf M = 2 := orderOf_eq_prime (by rw [pow_two]; exact hMM) (hne hodd)
  have hAord : orderOf A = 2 := orderOf_eq_prime (by rw [pow_two]; exact hAA) (hne hAodd)
  have hlet : suzukiLetter (quadMinus n K b c) A = suzukiLetter (quadMinus n K b c) M := by
    rw [suzukiLetter_eq_b_iff.mpr hAodd, suzukiLetter_eq_b_iff.mpr hodd]
  obtain ⟨y, hyO, hyconj⟩ :=
    (isConj_iff_suzukiLetter_eq hQ hMO hMord hAO hAord).mpr ⟨hlet, hrank⟩
  have hex : ∃ u ∈ omegaGroup (quadMinus n K b c) hQ, u * M * u⁻¹ = A := by
    by_cases hy : y ∈ omegaGroup (quadMinus n K b c) hQ
    · exact ⟨y, hy, hyconj⟩
    · have hyodd : Odd (finrank K (commSpace y)) :=
        Nat.not_even_iff_odd.mp fun he => hy (mem_omegaGroup.mpr ⟨hyO, he⟩)
      refine ⟨y * M, mem_omegaGroup.mpr ⟨mul_mem hyO hMO, ?_⟩, ?_⟩
      · rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hyO hMO,
          ZMod.natCast_eq_one_iff_odd.mpr hyodd, ZMod.natCast_eq_one_iff_odd.mpr hodd]
        decide
      · calc y * M * M * (y * M)⁻¹ = y * M * y⁻¹ := by group
          _ = A := hyconj
  obtain ⟨u, huΩ, huconj⟩ := hex
  obtain ⟨g, hg⟩ :=
    GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_minus (n := n) hirrQ hn huΩ
  exact ⟨g, by rw [hg]; exact huconj⟩

private theorem omfoi_finrank_commSpace_model {n : ℕ} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {k : ℕ} (hk : 2 * k ≤ n - 1) {T r : Vm n K ≃ₗ[K] Vm n K}
    (hTO : T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c))
    (hT : omqnfActs n b c (omqnfPermA (n - 1) k) 1 T)
    (hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c))
    (hr1 : finrank K (commSpace r) = 1) (hfix : ∀ x, r (omqnfFrame n K x) = omqnfFrame n K x) :
    finrank K (commSpace (T * r)) = 2 * k + 1 := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirrQ
  have hσ := omqnf_spMonoPerm_mul_self_A (n - 1) k
  have hT2k : finrank K (commSpace T) = 2 * k := by
    rw [omqnf_finrank_commSpace hirrQ hT hσ, omqnf_support_card_A hk]
    simp only [Pi.one_apply, Finset.prod_const_one, if_true]
    omega
  have hhyp : Submodule.map (((T * r : Vm n K ≃ₗ[K] Vm n K) : Vm n K →ₗ[K] Vm n K) - 1)
      (omqnfHyp n K) = Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfHyp n K) := by
    rw [omqnfHyp, Submodule.map_span, Submodule.map_span]
    congr 1
    apply Set.EqOn.image_eq
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply, hfix x,
      Module.End.one_apply]
  have hlow : 2 * k ≤ finrank K (commSpace (T * r)) := by
    have h1 := omqnf_finrank_map_hyp hT hσ
    rw [omqnf_support_card_A hk, ← hhyp] at h1
    have h2 : finrank K (Submodule.map (((T * r : Vm n K ≃ₗ[K] Vm n K) : Vm n K →ₗ[K] Vm n K) - 1)
        (omqnfHyp n K)) ≤ finrank K (commSpace (T * r)) :=
      Submodule.finrank_mono LinearMap.map_le_range
    omega
  have hup : finrank K (commSpace (T * r)) ≤ 2 * k + 1 := by
    have hle : commSpace (T * r) ≤ commSpace T ⊔ commSpace r := by
      intro v hv
      obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
      have hw : (T * r) w - w = (T (r w) - r w) + (r w - w) := by
        rw [LinearEquiv.mul_apply]
        abel
      rw [hw]
      exact Submodule.add_mem_sup (sub_mem_commSpace T (r w)) (sub_mem_commSpace r w)
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (commSpace T) (commSpace r)
    rw [hT2k, hr1] at h2
    omega
  have hodd : Odd (finrank K (commSpace (T * r))) := by
    rw [← ZMod.natCast_eq_one_iff_odd, natCast_finrank_commSpace_mul hQ hTO hrO, hT2k, hr1]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  obtain ⟨m, hm⟩ := hodd
  omega

theorem omMinus_exists_conj_reflAut_eq_nW {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {h : spinGroup (quadMinus n K b c)}
    (hh : h * omMinusReflAut n hn hirrQ h = 1) :
    ∃ g : spinGroup (quadMinus n K b c),
      g * h * omMinusReflAut n hn hirrQ g⁻¹ = 1 ∨
      ∃ (x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group)
        (π : Equiv.Perm (Fin (n - 1))),
        omqnfRealizes (n - 1) x π 1 ∧ π * π = 1 ∧
        π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        g * h * omMinusReflAut n hn hirrQ g⁻¹ = (SmallO8mCurtis.curtisDatum n hn hirrQ).nW x := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirrQ
  have hdim : finrank K (Vm n K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    omega
  have hβ := spinAction_omMinusReflAut hn hirrQ (b := b) (c := c)
  have hspinO : ∀ g : spinGroup (quadMinus n K b c),
      spinAction (quadMinus n K b c) g ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) := by
    intro g
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    exact map_spinAction (quadMinus n K b c) g v
  have hspinΩ : ∀ g : spinGroup (quadMinus n K b c),
      spinAction (quadMinus n K b c) g ∈ omegaGroup (quadMinus n K b c) hQ := by
    intro g
    have hE : spinAction (quadMinus n K b c) g ∈
        CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadMinus n K b c) := by
      rw [← range_spinAction_quadMinus hn hirrQ]
      exact ⟨g, rfl⟩
    exact RootCentOmega.elementaryGroup_quadMinus_le_omegaGroup (hirr := hirrQ) hn hE
  set r := CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus n K b c) (planeVec n planeOne)
    with hr
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) :=
    CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup _ _
  have hrr : r * r = 1 := CFSG.ClassicalGroups.Orthogonal.reflect_mul_self _ _
  have hr1 : finrank K (commSpace r) = 1 := omfoi_finrank_commSpace_reflect hirrQ
  set A := spinAction (quadMinus n K b c) h * r with hA
  have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) :=
    mul_mem (hspinO h) hrO
  have hAA : A * A = 1 := by
    calc A * A = spinAction (quadMinus n K b c) h *
          (r * spinAction (quadMinus n K b c) h * r) := by rw [hA]; group
      _ = spinAction (quadMinus n K b c) (h * omMinusReflAut n hn hirrQ h) := by
          rw [map_mul, hβ]
      _ = 1 := by rw [hh, map_one]
  have hAodd : Odd (finrank K (commSpace A)) := by
    rw [← ZMod.natCast_eq_one_iff_odd, hA, natCast_finrank_commSpace_mul hQ (hspinO h) hrO, hr1,
      ZMod.natCast_eq_zero_iff_even.mpr (hspinΩ h).2, zero_add, Nat.cast_one]
  have hle : 2 * finrank K (commSpace A) ≤ 2 * n := by
    have := two_mul_finrank_commSpace_le hAA
    rwa [hdim] at this
  have key : ∀ (g₀ : spinGroup (quadMinus n K b c)) (M : Vm n K ≃ₗ[K] Vm n K),
      spinAction (quadMinus n K b c) g₀ * M * (spinAction (quadMinus n K b c) g₀)⁻¹ = A →
      spinAction (quadMinus n K b c) (g₀⁻¹ * h * omMinusReflAut n hn hirrQ g₀⁻¹⁻¹) = M * r := by
    intro g₀ M hg₀
    have hsh : spinAction (quadMinus n K b c) h = spinAction (quadMinus n K b c) g₀ * M *
        (spinAction (quadMinus n K b c) g₀)⁻¹ * r⁻¹ := by
      rw [hg₀, hA, mul_inv_cancel_right]
    rw [inv_inv, map_mul, map_mul, hβ, map_inv, hsh]
    group
  obtain ⟨m, hm⟩ := hAodd
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  ·
    obtain ⟨g₀, hg₀⟩ := omfoi_exists_conj hn hirrQ hAO hAA hrO hrr (by rw [hr1]; omega)
      (by rw [hr1]; exact odd_one)
    refine ⟨g₀⁻¹, Or.inl ?_⟩
    apply RootCentOmega.spinAction_quadMinus_injective hirrQ
    rw [key g₀ r hg₀, hrr, map_one]
  ·
    have hk : 2 * m ≤ n - 1 := by omega
    obtain ⟨x, hx⟩ := exists_omqnfRealizes_of_signedPerm (omqnfPermA (n - 1) m)
      (spIsSign_one (m := n - 1))
    have hacts := omqnf_spinAction_nW hn hirrQ hx (spIsSign_one (m := n - 1))
    set N := spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirrQ).nW x)
      with hN
    have hNN : N * N = 1 := hacts.mul_self_eq_one (omqnf_spMonoPerm_mul_self_A (n - 1) m)
    have hNr : N * r = r * N := by
      have h1 : N (planeVec n planeOne) = planeVec n planeOne := by
        rw [hacts.2]
        simp
      have h2 := CFSG.ClassicalGroups.Orthogonal.reflect_conj (hspinO
        ((SmallO8mCurtis.curtisDatum n hn hirrQ).nW x)) (planeVec n planeOne)
      rw [← hN, h1, ← hr] at h2
      calc N * r = N * r * N⁻¹ * N := by group
        _ = r * N := by rw [h2]
    have hMO : N * r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) :=
      mul_mem (hspinO _) hrO
    have hMM : N * r * (N * r) = 1 := by
      calc N * r * (N * r) = N * (r * N) * r := by group
        _ = N * (N * r) * r := by rw [hNr]
        _ = N * N * (r * r) := by group
        _ = 1 := by rw [hNN, hrr, one_mul]
    have hfix : ∀ y, r (omqnfFrame n K y) = omqnfFrame n K y := by
      intro y
      apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      rcases y with a | a
      · exact polar_planeVec_eVec n b c planeOne a
      · exact polar_planeVec_fVec n b c planeOne a
    have hMrank : finrank K (commSpace (N * r)) = 2 * m + 1 :=
      omfoi_finrank_commSpace_model hirrQ hk (hspinO _) hacts hrO hr1 hfix
    obtain ⟨g₀, hg₀⟩ := omfoi_exists_conj hn hirrQ hAO hAA hMO hMM (by rw [hMrank]; omega)
      (by rw [hMrank]; exact odd_two_mul_add_one m)
    refine ⟨g₀⁻¹, Or.inr ⟨x, _, hx, omqnfPermA_mul_self _ _, omqnfPermA_zero hm0 hk,
      omqnfPermA_one hm0 hk, ?_⟩⟩
    apply RootCentOmega.spinAction_quadMinus_injective hirrQ
    rw [key g₀ (N * r) hg₀, mul_assoc, hrr, mul_one]

end CFSG.LocalAnalysis.WeakClosure81

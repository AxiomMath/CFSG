module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusWeyl
public import CFSG.RankThree.GF2n.Smith81.S81QGraphCl
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusAut
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusMono
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFRankHyp
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFDefs
import CFSG.RankThree.OrthogonalInvolutions.Conjugacy
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem
open CFSG.StandardType
open CFSG.RankThree.GF2n.Smith81.D6Spin (graphSpin)
open CFSG.RankThree.OrthogonalInvolutions Module

private theorem ompoi_finrank_commSpace_funCongrLeft {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] (τ : Equiv.Perm ι) (hτ : τ * τ = 1) :
    finrank F (commSpace (LinearEquiv.funCongrLeft F F τ)) = τ.support.card / 2 := by
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    have := congrArg (fun p : Equiv.Perm ι => p x) hτ
    simpa [Equiv.Perm.mul_apply] using this
  have hsingle : ∀ x, LinearEquiv.funCongrLeft F F τ (Pi.single x 1) =
      Pi.single (τ x) (1 : F) := by
    intro x
    funext y
    change (Pi.single x (1 : F) : ι → F) (τ y) = (Pi.single (τ x) (1 : F) : ι → F) y
    by_cases hy : y = τ x
    · subst hy
      simp [hττ]
    · have hne : τ y ≠ x := fun h => hy (by rw [← h, hττ])
      simp [hne, hy]
  have hcs : commSpace (LinearEquiv.funCongrLeft F F τ) =
      Submodule.span F (Set.range fun x => Pi.basisFun F ι (τ x) - Pi.basisFun F ι x) := by
    rw [commSpace, LinearMap.range_eq_map, ← (Pi.basisFun F ι).span_eq, Submodule.map_span,
      ← Set.range_comp]
    congr 1
    refine congrArg Set.range (funext fun x => ?_)
    simp only [Function.comp_apply, Pi.basisFun_apply, LinearMap.sub_apply, LinearEquiv.coe_coe,
      hsingle, Module.End.one_apply]
  rw [hcs]
  exact omqnf_finrank_span_perm_sub (Pi.basisFun F ι).linearIndependent τ hτ

private theorem ompoi_funCongrLeft_spMonoPerm_mem {F : Type} [Field F] {n : ℕ} (s : Fin n → ℤ) :
    LinearEquiv.funCongrLeft F F (spMonoPerm (1 : Equiv.Perm (Fin n)) s) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [quadPlus_apply, quadPlus_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change v (spMonoPerm 1 s (Sum.inl i)) * v (spMonoPerm 1 s (Sum.inr i)) = _
  rw [spMonoPerm_inl, spMonoPerm_inr]
  split_ifs
  · rfl
  · exact mul_comm _ _

private theorem ompoi_exists_conj {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {A M : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F)) (hAA : A * A = 1)
    (hMO : M ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F)) (hMM : M * M = 1)
    (hrank : finrank F (commSpace A) = finrank F (commSpace M))
    (hodd : Odd (finrank F (commSpace M))) :
    ∃ g : spinGroup (quadPlus n F),
      spinAction (quadPlus n F) g * M * (spinAction (quadPlus n F) g)⁻¹ = A := by
  have hQ := nondegenerate_polarBilin_quadPlus n F
  have hne : ∀ {T : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)},
      Odd (finrank F (commSpace T)) → T ≠ 1 := by
    rintro T hT rfl
    have h0 : commSpace (1 : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
      simp
    rw [h0, finrank_bot] at hT
    exact Nat.not_odd_zero hT
  have hAodd : Odd (finrank F (commSpace A)) := hrank ▸ hodd
  have hMord : orderOf M = 2 := orderOf_eq_prime (by rw [pow_two]; exact hMM) (hne hodd)
  have hAord : orderOf A = 2 := orderOf_eq_prime (by rw [pow_two]; exact hAA) (hne hAodd)
  have hlet : suzukiLetter (quadPlus n F) A = suzukiLetter (quadPlus n F) M := by
    rw [suzukiLetter_eq_b_iff.mpr hAodd, suzukiLetter_eq_b_iff.mpr hodd]
  obtain ⟨y, hyO, hyconj⟩ :=
    (isConj_iff_suzukiLetter_eq hQ hMO hMord hAO hAord).mpr ⟨hlet, hrank⟩
  have hex : ∃ u ∈ omegaGroup (quadPlus n F) hQ, u * M * u⁻¹ = A := by
    by_cases hy : y ∈ omegaGroup (quadPlus n F) hQ
    · exact ⟨y, hy, hyconj⟩
    · have hyodd : Odd (finrank F (commSpace y)) :=
        Nat.not_even_iff_odd.mp fun he => hy (mem_omegaGroup.mpr ⟨hyO, he⟩)
      refine ⟨y * M, mem_omegaGroup.mpr ⟨mul_mem hyO hMO, ?_⟩, ?_⟩
      · rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hyO hMO,
          ZMod.natCast_eq_one_iff_odd.mpr hyodd, ZMod.natCast_eq_one_iff_odd.mpr hodd]
        decide
      · calc y * M * M * (y * M)⁻¹ = y * M * y⁻¹ := by group
          _ = A := hyconj
  obtain ⟨u, huΩ, huconj⟩ := hex
  obtain ⟨g, hg⟩ := GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus hn huΩ
  exact ⟨g, by rw [hg]; exact huconj⟩

theorem exists_conj_graphSpin_eq_nW {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {h : spinGroup (quadPlus n F)} (hh : h * graphSpin n F ⟨n - 1, by omega⟩ h = 1) :
    ∃ (g : spinGroup (quadPlus n F)) (x : (coxeterMatrix (isFiniteType_cartanD n)).Group)
      (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ), SpIsSign s ∧ OmRealizes n x π s ∧
      π ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩ ∧ s ⟨n - 1, by omega⟩ = 1 ∧
      g * h * graphSpin n F ⟨n - 1, by omega⟩ g⁻¹ = (omPlusCurtisDatum n F hn).nW x := by
  classical
  set i₀ : Fin n := ⟨n - 1, by omega⟩ with hi₀
  have hQ := nondegenerate_polarBilin_quadPlus n F
  have hdim : finrank F (Fin n ⊕ Fin n → F) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hspinO : ∀ g : spinGroup (quadPlus n F),
      spinAction (quadPlus n F) g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) := by
    intro g
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    exact map_spinAction (quadPlus n F) g v
  have hspinΩ : ∀ g : spinGroup (quadPlus n F),
      spinAction (quadPlus n F) g ∈ omegaGroup (quadPlus n F) hQ := by
    intro g
    have hE : spinAction (quadPlus n F) g ∈
        CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadPlus n F) := by
      rw [← range_spinAction_quadPlus hn]
      exact ⟨g, rfl⟩
    exact RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn hE
  set sw : Equiv.Perm (Fin n ⊕ Fin n) := Equiv.swap (Sum.inl i₀) (Sum.inr i₀) with hsw
  set S : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F) := LinearEquiv.funCongrLeft F F sw
    with hS
  have hβ : ∀ g, spinAction (quadPlus n F) (graphSpin n F i₀ g) =
      S * spinAction (quadPlus n F) g * S := by
    intro g
    refine LinearEquiv.ext fun v => ?_
    rw [spinAction_graphSpin]
    rfl
  have hSO : S ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    exact CFSG.RankThree.GF2n.Smith81.D6Spin.quadPlus_swapLin n F i₀ v
  have hSS : S * S = 1 := by
    refine LinearEquiv.ext fun v => funext fun a => ?_
    change v (sw (sw a)) = v a
    rw [hsw, Equiv.swap_apply_self]
  have hS1 : finrank F (commSpace S) = 1 := by
    rw [hS, ompoi_finrank_commSpace_funCongrLeft sw (Equiv.swap_mul_self _ _), hsw,
      Equiv.Perm.card_support_swap Sum.inl_ne_inr]
  set A := spinAction (quadPlus n F) h * S with hA
  have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) := mul_mem (hspinO h) hSO
  have hAA : A * A = 1 := by
    calc A * A = spinAction (quadPlus n F) h * (S * spinAction (quadPlus n F) h * S) := by
          rw [hA]; group
      _ = spinAction (quadPlus n F) (h * graphSpin n F i₀ h) := by rw [map_mul, hβ]
      _ = 1 := by rw [hh, map_one]
  have hAodd : Odd (finrank F (commSpace A)) := by
    rw [← ZMod.natCast_eq_one_iff_odd, hA, natCast_finrank_commSpace_mul hQ (hspinO h) hSO, hS1,
      ZMod.natCast_eq_zero_iff_even.mpr (hspinΩ h).2, zero_add, Nat.cast_one]
  have hle : 2 * finrank F (commSpace A) ≤ 2 * n := by
    have := two_mul_finrank_commSpace_le hAA
    rwa [hdim] at this
  obtain ⟨m, hm⟩ := hAodd
  have hj : 2 * m ≤ n - 1 := by omega
  set c := omqnfSignC n (2 * m) with hc
  set τ := spMonoPerm (1 : Equiv.Perm (Fin n)) c with hτ
  set T : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F) := LinearEquiv.funCongrLeft F F τ
    with hT
  have hTO : T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) :=
    ompoi_funCongrLeft_spMonoPerm_mem c
  have hττ : τ * τ = 1 := omqnf_spMonoPerm_mul_self_C n (2 * m)
  have hci₀ : c i₀ = 1 := by
    rw [hc, hi₀]
    unfold omqnfSignC
    rw [if_neg (by simp only; omega)]
  have hdisj : Equiv.Perm.Disjoint sw τ := by
    intro x
    rcases x with a | a
    · by_cases ha : a = i₀
      · right
        rw [ha, hτ, spMonoPerm_inl, if_pos hci₀]
        rfl
      · left
        exact Equiv.swap_apply_of_ne_of_ne (fun h => ha (Sum.inl_injective h)) Sum.inl_ne_inr
    · by_cases ha : a = i₀
      · right
        rw [ha, hτ, spMonoPerm_inr, if_pos hci₀]
        rfl
      · left
        exact Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => ha (Sum.inr_injective h))
  have hTS : T * S = LinearEquiv.funCongrLeft F F (sw * τ) := by
    refine LinearEquiv.ext fun v => funext fun x => ?_
    rfl
  have hσσ : sw * τ * (sw * τ) = 1 := by
    calc sw * τ * (sw * τ) = sw * (τ * sw) * τ := by group
      _ = sw * (sw * τ) * τ := by rw [hdisj.commute.eq.symm]
      _ = sw * sw * (τ * τ) := by group
      _ = 1 := by rw [hsw, Equiv.swap_mul_self, hττ, one_mul]
  have hMrank : finrank F (commSpace (T * S)) = 2 * m + 1 := by
    rw [hTS, ompoi_finrank_commSpace_funCongrLeft _ hσσ, hdisj.card_support_mul, hsw,
      Equiv.Perm.card_support_swap Sum.inl_ne_inr, hτ, hc, omqnf_support_card_C (by omega)]
    omega
  have hMO : T * S ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) := mul_mem hTO hSO
  have hMM : T * S * (T * S) = 1 := by
    rw [hTS]
    refine LinearEquiv.ext fun v => funext fun x => ?_
    change v ((sw * τ) ((sw * τ) x)) = v x
    rw [← Equiv.Perm.mul_apply, hσσ]
    rfl
  obtain ⟨g₀, hg₀⟩ := ompoi_exists_conj hn hAO hAA hMO hMM (by rw [hMrank]; omega)
    (by rw [hMrank]; exact odd_two_mul_add_one m)
  have key : spinAction (quadPlus n F) (g₀⁻¹ * h * graphSpin n F i₀ g₀⁻¹⁻¹) = T := by
    have hsh : spinAction (quadPlus n F) h = spinAction (quadPlus n F) g₀ * (T * S) *
        (spinAction (quadPlus n F) g₀)⁻¹ * S⁻¹ := by
      rw [hg₀, hA, mul_inv_cancel_right]
    rw [inv_inv, map_mul, map_mul, hβ, map_inv, hsh]
    calc _ = T * (S * S) := by group
      _ = T := by rw [hSS, mul_one]
  have hτsymm : τ.symm = τ := inv_eq_of_mul_eq_one_left hττ
  have hmat : (spinMatrix (quadPlus n F) (g₀⁻¹ * h * graphSpin n F i₀ g₀⁻¹⁻¹) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        Equiv.Perm.permMatrix F (spMonoPerm (1 : Equiv.Perm (Fin n)) c).symm := by
    rw [coe_spinMatrix, key, ← hτ, hτsymm]
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec]
    rfl
  have hprod : ∏ a, c a = 1 := by
    rw [hc, omqnfSignC_prod (by omega), pow_mul]
    simp
  obtain ⟨x, hx, hxg⟩ := exists_nW_eq_of_spinMatrix_eq hn (omqnfSignC_isSign n (2 * m)) hprod hmat
  exact ⟨g₀⁻¹, x, 1, c, omqnfSignC_isSign n (2 * m), hx, rfl, hci₀, hxg.symm⟩

end CFSG.LocalAnalysis.WeakClosure81

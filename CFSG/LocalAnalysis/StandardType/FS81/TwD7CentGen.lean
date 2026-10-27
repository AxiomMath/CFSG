module

public import CFSG.LocalAnalysis.StandardType.FS81.BasisMonomial
public import CFSG.LocalAnalysis.StandardType.FS81.RowOutTwD7
public import CFSG.LieType.SeitzGeneration.OrthBlocks
public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.LieType.SeitzGeneration.OrthRelRoot
import CFSG.LieType.SeitzGeneration.OrthNonsplitDims
import CFSG.LieType.SeitzGeneration.OrthEx
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Commutator
import CFSG.LieType.SeitzGeneration.HyperLinear
import CFSG.LieType.SeitzGeneration.OrthCubeBlocks
import CFSG.LieType.SeitzGeneration.OrthExLift
import CFSG.RankThree.PartOne.CTP.SeitzLinear
import CFSG.RankThree.PartOne.CTP.SeitzOrthModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Module QuadraticMap CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.OrthBlk CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
  (commutator_orthogonalGroup_eq_elementaryGroup_f2)
open CFSG.RankThree.Classical2 (orthDerived)

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem commute_eichler_of_fix_perp {U : Submodule (ZMod 2) V} (hU : PolarNondegOn Q U)
    {x : V ≃ₗ[ZMod 2] V} (hxU : ∀ u ∈ U, x u ∈ U) (hxP : ∀ v ∈ perp Q U, x v = v)
    {e w : V} (he : e ∈ perp Q U) (hw : w ∈ perp Q U) : Commute (eichler Q e w) x := by
  have hO : eichler Q e w ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (eichler_mem_elementaryGroup Q e w)
  have hfix : ∀ u ∈ U, eichler Q e w u = u := fun u hu =>
    eichler_apply_of_polar_eq_zero (mem_perp.mp he u hu) (mem_perp.mp hw u hu)
  have hstab : ∀ v ∈ perp Q U, eichler Q e w v ∈ perp Q U := fun v hv =>
    mem_perp.mpr fun s hs => by
      rw [← hfix s hs, polar_map_of_mem hO]
      exact mem_perp.mp hv s hs
  show eichler Q e w * x = x * eichler Q e w
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp ((isCompl_perp hU).sup_eq_top ▸
    Submodule.mem_top (x := v))
  simp only [LinearEquiv.mul_apply, map_add]
  rw [hxP u' hu', hfix _ (hxU u hu), hfix u hu, hxP _ (hstab u' hu')]

theorem commutator_le_of_commute_planes (hQ : (polarBilin Q).Nondegenerate)
    (hd : 7 ≤ finrank (ZMod 2) V) {U₁ U₂ : Submodule (ZMod 2) V}
    (hU₁ : PolarNondegOn Q U₁) (hU₂ : PolarNondegOn Q U₂) (hd₁ : finrank (ZMod 2) U₁ = 2)
    (hd₂ : finrank (ZMod 2) U₂ = 2) (h12 : U₁ ≤ perp Q U₂)
    {x₁ x₂ : V ≃ₗ[ZMod 2] V} (hx₁U : ∀ u ∈ U₁, x₁ u ∈ U₁) (hx₁P : ∀ v ∈ perp Q U₁, x₁ v = v)
    (hx₂U : ∀ u ∈ U₂, x₂ u ∈ U₂) (hx₂P : ∀ v ∈ perp Q U₂, x₂ v = v)
    {H : Subgroup (V ≃ₗ[ZMod 2] V)} (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₁ : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      Commute g x₁ → g ∈ H)
    (h₂ : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      Commute g x₂ → g ∈ H) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ H := by
  have hE := commutator_orthogonalGroup_eq_elementaryGroup_f2 hQ (by omega) (Or.inl (by omega))
  have hEichΩ : ∀ e w, eichler Q e w ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    fun e w => hE ▸ eichler_mem_elementaryGroup Q e w
  have hW₁ : PolarNondegOn Q (perp Q U₁) := polarNondegOn_perp hQ hU₁
  have hperp : perp Q (perp Q U₁) ≤ perp Q U₂ :=
    (LinearMap.BilinForm.orthogonal_orthogonal hQ (QuadraticMap.isSymm_polarBilin Q).isRefl
      U₁).le.trans h12
  have hS := OrthBlk.polarNondegOn_sup hU₁ hU₂ fun s hs t ht => by
    rw [polar_comm]
    exact mem_perp.mp (h12 hs) t ht
  have hdimS : finrank (ZMod 2) ↥(U₁ ⊔ U₂) ≤ 4 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
    omega
  have hcompl := Submodule.finrank_add_eq_of_isCompl (isCompl_perp hS)
  have h3 : 3 ≤ finrank (ZMod 2) ↥(perp Q (U₁ ⊔ U₂)) := by omega
  obtain ⟨P, hPe, hPf⟩ := exists_hypPair_in (polarNondegOn_perp hQ hS) h3
  have hle : perp Q (U₁ ⊔ U₂) ≤ perp Q U₁ ⊓ perp Q U₂ := le_inf
    (fun v hv => mem_perp.mpr fun s hs => mem_perp.mp hv s (Submodule.mem_sup_left hs))
    (fun v hv => mem_perp.mpr fun s hs => mem_perp.mp hv s (Submodule.mem_sup_right hs))
  rw [hE]
  refine elementaryGroup_le_of_two hH hQ hW₁ hperp (fun e he w hw => ?_) (fun e he w hw => ?_) P
    (hle hPe) (hle hPf)
  · exact h₁ _ (hEichΩ e w) (commute_eichler_of_fix_perp hU₁ hx₁U hx₁P he hw)
  · exact h₂ _ (hEichΩ e w) (commute_eichler_of_fix_perp hU₂ hx₂U hx₂P he hw)

end Model

theorem exists_mem_le_of_centralizer_le_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G (Row.twD7.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) :
    ∃ t ∈ K, t ∈ Subgroup.normalizer (E : Set G) ∧
      ∀ H : Subgroup G, Subgroup.centralizer ({B.b 1} : Set G) ⊓ K ≤ H → t ∈ H → K ≤ H := by
  classical
  obtain ⟨_hsimple, hHyp, hCanon⟩ := hstd
  obtain ⟨hrow, hdisjEK, hsup, hmax, hcard, -⟩ := hCanon
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨hb₀, hKC, hKn, hcenter, -, -, -, -⟩ := hA
  change RecOutTwD7 B b₀ at hrec
  obtain ⟨-, ⟨φ⟩⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hrow hcenter
  have hdisj : Disjoint (Subgroup.zpowers b₀) K := disjoint_zpowers_of_center hKC hcenter
  have hQ : (polarBilin (quadMinus 7 (ZMod 2) 1 1)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 7 (ZMod 2)
      (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
  have h14 : finrank (ZMod 2) (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) = 14 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  obtain ⟨B', F, hB', heven, hU, hφB'⟩ := exists_basis_frame_of_model hQ
    exists_totallySingular_three_quadMinus_seven (n := 7) (by norm_num) φ hb₀ hKC hdisj hsup
    hmax hcard
  have hR : B.realized K ⊆ evenFix0 7 := fun M hM =>
    realized_centralizer_subset_evenFix0_of_recOutTwD7 hB hKC hKn hdisjEK hrec
      (realized_mono B hKC hM)
  obtain ⟨j, hj⟩ := exists_eq_or_eq_inv_of_realized_evenFix0 (n := 7) (by norm_num) hdisj hB hB'
    hR heven 0
  obtain ⟨j', hj'⟩ := exists_ne j
  have hswap : spMat (Equiv.swap j.succ j'.succ) (fun _ => 1) ∈ evenFix0 7 := by
    refine ⟨Equiv.swap j.succ j'.succ, fun _ => 1, fun _ => Or.inl rfl,
      ⟨Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j).symm (Fin.succ_ne_zero j').symm, rfl,
        Finset.prod_const_one⟩, rfl⟩
  obtain ⟨t, htK, ht⟩ := heven hswap
  have htb : t * B'.b j.succ * t⁻¹ = B'.b j'.succ := by
    rw [(B'.acts_spMat_iff.mp ht) j.succ, Equiv.swap_apply_left]
    exact pow_one _
  have htN : t ∈ Subgroup.normalizer (E : Set G) := by
    rw [← hB'.1]
    exact B'.mem_normalizer_of_acts ht
  refine ⟨t, htK, htN, fun H hC htH => ?_⟩
  have hCj : Subgroup.centralizer ({B'.b j.succ} : Set G) ⊓ K ≤ H := by
    have hcent : Subgroup.centralizer ({B'.b j.succ} : Set G) =
        Subgroup.centralizer ({B.b 1} : Set G) := by
      rcases hj with h | h
      · rw [show B.b 1 = B.b (0 : Fin 7).succ from rfl, h]
      · ext g
        rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
          show B.b 1 = B.b (0 : Fin 7).succ from rfl, h]
        exact Commute.inv_right_iff.symm
    rw [hcent]
    exact hC
  have hnd : ∀ k, PolarNondegOn (quadMinus 7 (ZMod 2) 1 1) (F.U k) := fun k x hx hxy =>
    F.nondeg k x hx fun v hv => by
      rw [polar_comm]
      exact hxy v hv
  have hmaps : ∀ k, ∀ u ∈ F.U k, F.ι (Multiplicative.ofAdd (Pi.single k 1)) u ∈ F.U k :=
    fun k u hu => F.mapsTo _ k u hu
  have hfixP : ∀ k, ∀ v ∈ perp (quadMinus 7 (ZMod 2) 1 1) (F.U k),
      F.ι (Multiplicative.ofAdd (Pi.single k 1)) v = v := fun k v hv =>
    (F.fix _ v).mpr fun i hi u hu => by
      have hik : i = k := by
        by_contra hne
        exact hi (by simp [hne])
      subst hik
      exact mem_perp.mp hv u hu
  have horth : F.U j ≤ perp (quadMinus 7 (ZMod 2) 1 1) (F.U j') := fun u hu =>
    mem_perp.mpr fun s hs => F.orth j' j hj' s hs u hu
  let ι : ↥K →* ((Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)) :=
    (orthDerived (quadMinus 7 (ZMod 2) 1 1)).subtype.comp φ.toMonoidHom
  have hHV : (H.subgroupOf K).map ι ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 7 (ZMod 2) 1 1) := by
    rintro _ ⟨k, -, rfl⟩
    exact Subgroup.commutator_le_self _ (φ k).2
  have hcomm : ∀ (x : ↥K) (g) (hg : g ∈ orthDerived (quadMinus 7 (ZMod 2) 1 1)),
      Commute g ((φ x : ↥(orthDerived (quadMinus 7 (ZMod 2) 1 1))) :
        (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)) →
      ((φ.symm ⟨g, hg⟩ : ↥K) : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro x g hg hgx
    have h1 : φ.symm ⟨g, hg⟩ * x = x * φ.symm ⟨g, hg⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hgx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val h1
  have hmemHV : ∀ (g) (hg : g ∈ orthDerived (quadMinus 7 (ZMod 2) 1 1)),
      ((φ.symm ⟨g, hg⟩ : ↥K) : G) ∈ H → g ∈ (H.subgroupOf K).map ι := fun g hg hgH =>
    ⟨φ.symm ⟨g, hg⟩, hgH, by simp [ι]⟩
  have hbj : B'.b j.succ ∈ K := hB'.2.2 _ (Fin.succ_ne_zero j)
  have hbj' : B'.b j'.succ ∈ K := hB'.2.2 _ (Fin.succ_ne_zero j')
  have hΩ := commutator_le_of_commute_planes hQ (by rw [h14]; norm_num) (hnd j) (hnd j') (hU j)
    (hU j') horth (hmaps j) (hfixP j) (hmaps j') (hfixP j') hHV
    (fun g hg hgx => by
      rw [← hφB' j hbj] at hgx
      exact hmemHV g hg (hCj ⟨hcomm ⟨_, hbj⟩ g hg hgx, (φ.symm ⟨g, hg⟩).2⟩))
    (fun g hg hgx => by
      rw [← hφB' j' hbj'] at hgx
      have hk := hcomm ⟨_, hbj'⟩ g hg hgx
      set k : G := ((φ.symm ⟨g, hg⟩ : ↥K) : G) with hkdef
      have hkK : k ∈ K := (φ.symm ⟨g, hg⟩).2
      have hk'C : t⁻¹ * k * t ∈ Subgroup.centralizer ({B'.b j.succ} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
        change k * B'.b j'.succ = B'.b j'.succ * k at hk
        rw [← htb] at hk
        calc t⁻¹ * k * t * B'.b j.succ = t⁻¹ * (k * (t * B'.b j.succ * t⁻¹)) * t := by group
          _ = t⁻¹ * ((t * B'.b j.succ * t⁻¹) * k) * t := by rw [hk]
          _ = B'.b j.succ * (t⁻¹ * k * t) := by group
      have hk' : t⁻¹ * k * t ∈ Subgroup.centralizer ({B'.b j.succ} : Set G) ⊓ K :=
        ⟨hk'C, K.mul_mem (K.mul_mem (K.inv_mem htK) hkK) htK⟩
      have hkH : k ∈ H := by
        have := H.mul_mem (H.mul_mem htH (hCj hk')) (H.inv_mem htH)
        rwa [show t * (t⁻¹ * k * t) * t⁻¹ = k by group] at this
      exact hmemHV g hg hkH)
  intro k hk
  obtain ⟨k', hk'H, hk'⟩ := hΩ (φ ⟨k, hk⟩).2
  have hkk : k' = ⟨k, hk⟩ := φ.injective (Subtype.ext hk')
  rw [hkk] at hk'H
  exact hk'H

end CFSG.StandardType.FrameRoute.FS81

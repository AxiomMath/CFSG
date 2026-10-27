module

public import CFSG.LocalAnalysis.StandardType.GGLangOrbitTwo
public import CFSG.LocalAnalysis.StandardType.GGLangOrbitTorus
public import CFSG.LocalAnalysis.StandardType.GGLangWSLGamma
public import CFSG.LocalAnalysis.StandardType.GGLangModelIndex

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

open scoped commutatorElement

theorem prod_rootSL2_HSL_mem_rationalComponent_of_step
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hq : S.D.q = 2 ^ f)
    (hAlg : S.IsAlgebraic) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {α β : Fin τ.rank → ℤ} (hα : α ∈ componentRoots (rootCharHom a) i)
    (hβ : β ∈ rationalRoots S.ρ (rootCharHom a) i)
    (horth : iform α β = 0)
    {t t' : Lˣ} {m : ℕ} (hm : Odd m) (ht : t ^ m = 1) (ht' : t' ^ m = 1)
    (hstepα : S.D.step (rootSL2 τ L α (HSL t)) = rootSL2 τ L β (HSL t'))
    (hstepβ : S.D.step (rootSL2 τ L β (HSL t')) = rootSL2 τ L α (HSL t))
    (hstepWα : S.D.step (rootSL2 τ L α WSL) = rootSL2 τ L β WSL)
    (hstepWβ : S.D.step (rootSL2 τ L β WSL) = rootSL2 τ L α WSL) :
    rootSL2 τ L α (HSL t) * rootSL2 τ L β (HSL t') ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  haveI h2 : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S hq
  have hαr : IsRoot τ α := (isRootComponent_componentRoots i).isRoot α hα
  have hβr : IsRoot τ β := isRoot_of_mem_rationalRoots S i hβ
  let x : ModGL τ L := rootSL2 τ L α (HSL t)
  let y : ModGL τ L := rootSL2 τ L β (HSL t')
  let nα : ModGL τ L := rootSL2 τ L α WSL
  let nβ : ModGL τ L := rootSL2 τ L β WSL
  let d : ModGL τ L := x * y
  let w : ModGL τ L := nα * nβ
  change d ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i
  let bα : Fin τ.rank → Lˣ := fun j => t ^ corootPair α (Pi.single j 1)
  let bβ : Fin τ.rank → Lˣ := fun j => t' ^ corootPair β (Pi.single j 1)
  have hxdiag : x = rootDiagUnit τ bα := by
    change rootTorusSL2 τ L α t = rootDiagUnit τ bα
    exact CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hαr t
  have hydiag : y = rootDiagUnit τ bβ := by
    change rootTorusSL2 τ L β t' = rootDiagUnit τ bβ
    exact CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hβr t'
  have hxy : x * y = y * x := by
    rw [hxdiag, hydiag, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hxyc : Commute x y := (commute_iff_eq x y).2 hxy
  have hnα : nα = canonicalRep (coxeterSystem τ) L (rootReflection α) := by
    change rootSL2 τ L α WSL = _
    rw [show rootSL2 τ L α WSL = rootWeylSL2 τ L α 1 by simp [rootWeylSL2, nSL_one]]
    exact CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo hαr
  have hnβ : nβ = canonicalRep (coxeterSystem τ) L (rootReflection β) := by
    change rootSL2 τ L β WSL = _
    rw [show rootSL2 τ L β WSL = rootWeylSL2 τ L β 1 by simp [rootWeylSL2, nSL_one]]
    exact CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo hβr
  have hcomm : Commute nα nβ := by
    rw [hnα, hnβ]
    refine (commute_iff_eq _ _).2 ?_
    rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
      ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo]
    exact congrArg (fun u => canonicalRep (coxeterSystem τ) L u)
      (rootReflection_commute_of_iform_eq_zero hαr hβr horth).eq
  have hnα2 : nα ^ 2 = 1 := by
    change (rootSL2 τ L α WSL) ^ 2 = 1
    exact rootSL2_WSL_mul_self α
  have hnβ2 : nβ ^ 2 = 1 := by
    change (rootSL2 τ L β WSL) ^ 2 = 1
    exact rootSL2_WSL_mul_self β
  have hw2 : w ^ 2 = 1 := by
    change (nα * nβ) ^ 2 = 1
    rw [hcomm.mul_pow 2, hnα2, hnβ2, one_mul]
  have hstepα' : S.D.step x = y := hstepα
  have hstepβ' : S.D.step y = x := hstepβ
  have hstepWα' : S.D.step nα = nβ := hstepWα
  have hstepWβ' : S.D.step nβ = nα := hstepWβ
  have hdM : d ∈ S.D.model := by
    refine (S.D.mem_model).2 ⟨?_, ?_⟩
    · change x * y ∈ adjointGroup τ L
      exact mul_mem (by
        change rootSL2 τ L α (HSL t) ∈ adjointGroup τ L
        exact (exceptional_Lang_root_rank_one_data τ L α).2.2.2.2.1 (HSL t)) (by
        change rootSL2 τ L β (HSL t') ∈ adjointGroup τ L
        exact (exceptional_Lang_root_rank_one_data τ L β).2.2.2.2.1 (HSL t'))
    · change S.D.step (x * y) = x * y
      rw [map_mul, hstepα', hstepβ']
      exact hxy.symm
  have hwM : w ∈ S.D.model := by
    refine (S.D.mem_model).2 ⟨?_, ?_⟩
    · change nα * nβ ∈ adjointGroup τ L
      exact mul_mem (by
        change rootSL2 τ L α WSL ∈ adjointGroup τ L
        exact (exceptional_Lang_root_rank_one_data τ L α).2.2.2.2.1 WSL) (by
        change rootSL2 τ L β WSL ∈ adjointGroup τ L
        exact (exceptional_Lang_root_rank_one_data τ L β).2.2.2.2.1 WSL)
    · change S.D.step (nα * nβ) = nα * nβ
      rw [map_mul, hstepWα', hstepWβ']
      exact hcomm.symm.eq
  have hwΓ : w ∈ S.Γ := langModel_mem_Γ_of_sq_eq_one S hτ hq hAlg hwM hw2
  have hpowcomm : ∀ (c : Lˣ) (k : ℤ), (c ^ k) ^ m = (c ^ m) ^ k := by
    intro c k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hxm : x ^ m = 1 := by
    rw [hxdiag, rootDiagUnit_pow, ← rootDiagUnit_one]
    congr 1
    funext j
    rw [Pi.pow_apply]
    change (t ^ corootPair α (Pi.single j 1)) ^ m = 1
    rw [hpowcomm t (corootPair α (Pi.single j 1)), ht, one_zpow]
  have hym : y ^ m = 1 := by
    rw [hydiag, rootDiagUnit_pow, ← rootDiagUnit_one]
    congr 1
    funext j
    rw [Pi.pow_apply]
    change (t' ^ corootPair β (Pi.single j 1)) ^ m = 1
    rw [hpowcomm t' (corootPair β (Pi.single j 1)), ht', one_zpow]
  have hdm : d ^ m = 1 := by
    change (x * y) ^ m = 1
    rw [hxyc.mul_pow m, hxm, hym, one_mul]
  have hχ_of_orth : ∀ (ξ : Lˣ) (γ δ : Fin τ.rank → ℤ), IsRoot τ γ → iform γ δ = 0 →
      rootChar (fun j => ξ ^ corootPair γ (Pi.single j 1)) δ = 1 := by
    intro ξ γ δ hγ h0
    have hprod : ∀ (f : Fin τ.rank → ℤ), (∏ j, ξ ^ f j) = ξ ^ (∑ j, f j) := by
      intro f
      induction (Finset.univ : Finset (Fin τ.rank)) using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
    have hchar : rootChar (fun j => ξ ^ corootPair γ (Pi.single j 1)) δ =
        ξ ^ (∑ j, δ j * corootPair γ (Pi.single j 1)) := by
      rw [rootChar]
      have h1 : (∏ j, (ξ ^ corootPair γ (Pi.single j 1)) ^ δ j) =
          ∏ j, ξ ^ (corootPair γ (Pi.single j 1) * δ j) :=
        Finset.prod_congr rfl fun j _ => by rw [← zpow_mul]
      rw [h1, hprod]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hcp0 : corootPair γ δ = 0 := by
      rw [corootPair, h0]
      simp
    have hlin : corootPair γ δ = ∑ j, δ j * corootPair γ (Pi.single j 1) := by
      have hδ : δ = ∑ j, δ j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hδ]
      exact CFSG.HardMathSupport.Timmesfeld.RootAut.corootPair_sum hγ Finset.univ δ
        (fun j => Pi.single j 1)
    rw [hchar, ← hlin, hcp0, zpow_zero]
  have hχα : rootChar bβ α = 1 := by
    change rootChar (fun j => t' ^ corootPair β (Pi.single j 1)) α = 1
    exact hχ_of_orth t' β α hβr (by rw [iform_comm, horth])
  have hχβ : rootChar bα β = 1 := by
    change rootChar (fun j => t ^ corootPair α (Pi.single j 1)) β = 1
    exact hχ_of_orth t α β hαr horth
  have HSL_inv : ∀ c : Lˣ, ((HSL c : SL2 L))⁻¹ = HSL c⁻¹ := by
    intro c
    rw [inv_eq_iff_mul_eq_one]
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hconj : ∀ (γ : Fin τ.rank → ℤ) (c : Lˣ),
      rootSL2 τ L γ WSL * rootSL2 τ L γ (HSL c) =
        rootSL2 τ L γ (HSL c⁻¹) * rootSL2 τ L γ WSL := by
    intro γ c
    have h1 := rootWeylSL2_one_mul_rootTorusSL2 (τ := τ) (K := L) γ c
    rw [show rootSL2 τ L γ WSL = rootWeylSL2 τ L γ 1 by simp [rootWeylSL2, nSL_one],
      show rootSL2 τ L γ (HSL c) = rootTorusSL2 τ L γ c from rfl, h1,
      rootWeylSL2, nSL_eq_HSL_mul, map_mul,
      show rootWeylSL2 τ L γ 1 = rootSL2 τ L γ WSL by simp [rootWeylSL2, nSL_one]]
  have hxinv : x⁻¹ = rootSL2 τ L α (HSL t⁻¹) := by
    change (rootSL2 τ L α (HSL t))⁻¹ = _
    rw [← map_inv, HSL_inv]
  have hyinv : y⁻¹ = rootSL2 τ L β (HSL t'⁻¹) := by
    change (rootSL2 τ L β (HSL t'))⁻¹ = _
    rw [← map_inv, HSL_inv]
  have hnαx : nα * x = x⁻¹ * nα := by
    change rootSL2 τ L α WSL * rootSL2 τ L α (HSL t) = _
    rw [hxinv]
    exact hconj α t
  have hnβy : nβ * y = y⁻¹ * nβ := by
    change rootSL2 τ L β WSL * rootSL2 τ L β (HSL t') = _
    rw [hyinv]
    exact hconj β t'
  have hnαy : nα * y = y * nα := by
    have hc := (rootDiagUnit_mem_centralizer_iff hαr bβ).2 hχα
    rw [Subgroup.mem_centralizer_iff] at hc
    have h := hc nα (by change rootSL2 τ L α WSL ∈ rootRankOneGroup τ L α; exact ⟨WSL, rfl⟩)
    change nα * y = y * nα
    rw [hydiag]
    exact h
  have hnβx : nβ * x = x * nβ := by
    have hc := (rootDiagUnit_mem_centralizer_iff hβr bα).2 hχβ
    rw [Subgroup.mem_centralizer_iff] at hc
    have h := hc nβ (by change rootSL2 τ L β WSL ∈ rootRankOneGroup τ L β; exact ⟨WSL, rfl⟩)
    change nβ * x = x * nβ
    rw [hxdiag]
    exact h
  have hnαinv : nα⁻¹ = nα :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hnα2)
  have hnβinv : nβ⁻¹ = nβ :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hnβ2)
  have hnyinv : nα * y⁻¹ = y⁻¹ * nα := by
    have hc : Commute nα y := (commute_iff_eq nα y).2 hnαy
    exact hc.inv_right.eq
  have hnβsq : nβ * nβ = 1 := by simpa [pow_two] using hnβ2
  have hnαsq : nα * nα = 1 := by simpa [pow_two] using hnα2
  have hinnerβ : nβ * x * y * nβ = x * y⁻¹ := by
    calc nβ * x * y * nβ = x * (nβ * y) * nβ := by rw [hnβx]; group
      _ = x * (y⁻¹ * nβ) * nβ := by rw [hnβy]
      _ = x * y⁻¹ * (nβ * nβ) := by group
      _ = x * y⁻¹ := by rw [hnβsq, mul_one]
  have hinnerα : nα * (x * y⁻¹) * nα = x⁻¹ * y⁻¹ := by
    calc nα * (x * y⁻¹) * nα = (nα * x) * (y⁻¹ * nα) := by group
      _ = (x⁻¹ * nα) * (y⁻¹ * nα) := by rw [hnαx]
      _ = x⁻¹ * (nα * y⁻¹) * nα := by group
      _ = x⁻¹ * (y⁻¹ * nα) * nα := by rw [hnyinv]
      _ = x⁻¹ * y⁻¹ * (nα * nα) := by group
      _ = x⁻¹ * y⁻¹ := by rw [hnαsq, mul_one]
  have hwd : w * d * w⁻¹ = d⁻¹ := by
    change (nα * nβ) * (x * y) * (nα * nβ)⁻¹ = (x * y)⁻¹
    rw [mul_inv_rev, hnαinv, hnβinv]
    calc (nα * nβ) * (x * y) * (nβ * nα)
        = nα * (nβ * x * y * nβ) * nα := by group
      _ = nα * (x * y⁻¹) * nα := by rw [hinnerβ]
      _ = x⁻¹ * y⁻¹ := hinnerα
      _ = (x * y)⁻¹ := by
        rw [mul_inv_rev]
        exact (hxyc.inv_left.inv_right).eq
  have hd2 : d ^ 2 = ⁅d, w⁆ := by
    have hinv : w * d⁻¹ * w⁻¹ = d := by
      have h := congrArg Inv.inv hwd
      simpa [mul_assoc] using h
    rw [commutatorElement_def, pow_two]
    calc d * d = d * (w * d⁻¹ * w⁻¹) := by rw [hinv]
      _ = d * w * d⁻¹ * w⁻¹ := by group
  have hd2Γ : d ^ 2 ∈ S.Γ := by
    rw [hd2]
    exact Subgroup.commutator_mem_commutator hdM hwM
  have mem_rootSpan : ∀ (γ : Fin τ.rank → ℤ), γ ∈ rationalRoots S.ρ (rootCharHom a) i →
      ∀ A : SL2 L, rootSL2 τ L γ A ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    intro γ hγ A
    have hr : IsRoot τ γ := isRoot_of_mem_rationalRoots S i hγ
    have hle : rootRankOneGroup τ L γ ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
      rw [(exceptional_Lang_root_rank_one_torus_transport τ L hr).1]
      exact sup_le (le_iSup₂_of_le γ hγ le_rfl)
        (le_iSup₂_of_le (-γ) (neg_mem_rationalRoots S i hγ) le_rfl)
    exact hle (MonoidHom.mem_range.2 ⟨A, rfl⟩)
  have hαrroot : α ∈ rationalRoots S.ρ (rootCharHom a) i := ⟨0, α, hα, rfl⟩
  have hαnegrroot : -α ∈ rationalRoots S.ρ (rootCharHom a) i :=
    neg_mem_rationalRoots S i hαrroot
  have hdspan : d ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    change x * y ∈ _
    exact mul_mem (mem_rootSpan α hαrroot (HSL t)) (mem_rootSpan β hβ (HSL t'))
  have hwspan : w ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    change nα * nβ ∈ _
    exact mul_mem (mem_rootSpan α hαrroot WSL) (mem_rootSpan β hβ WSL)
  have hdΓ : d ∈ S.Γ := langModel_mem_Γ_of_sq_mem S hτ hq hAlg hdM hd2Γ
  have hdR : d ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := ⟨hdspan, hdΓ⟩
  have hwR : w ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := ⟨hwspan, hwΓ⟩
  have hcommut : ⁅d, w⁆ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.commutator_mem_commutator hdR hwR
  have hd2R : d ^ 2 ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [hd2]
    exact hcommut
  obtain ⟨r, rfl⟩ := hm
  have hd_eq : d = (d ^ 2) ^ ((2 * r + 1 + 1) / 2) := by
    rw [← pow_mul, show 2 * ((2 * r + 1 + 1) / 2) = 2 * r + 1 + 1 by omega,
      pow_succ, hdm, one_mul]
  rw [hd_eq]
  exact pow_mem hd2R _

theorem rootDiagUnit_mul_corootPair_mem_rationalComponent_of_step
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hq : S.D.q = 2 ^ f) (hAlg : S.IsAlgebraic)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {α β : Fin τ.rank → ℤ} (hα : α ∈ componentRoots (rootCharHom a) i)
    (hβ : β ∈ rationalRoots S.ρ (rootCharHom a) i) (horth : iform α β = 0)
    {t t' : Lˣ} {m : ℕ} (hm : Odd m) (ht : t ^ m = 1) (ht' : t' ^ m = 1)
    (hstepα : S.D.step (rootSL2 τ L α (HSL t)) = rootSL2 τ L β (HSL t'))
    (hstepβ : S.D.step (rootSL2 τ L β (HSL t')) = rootSL2 τ L α (HSL t))
    (hstepWα : S.D.step (rootSL2 τ L α WSL) = rootSL2 τ L β WSL)
    (hstepWβ : S.D.step (rootSL2 τ L β WSL) = rootSL2 τ L α WSL) :
    rootDiagUnit τ (fun j => t ^ corootPair α (Pi.single j 1) *
      t' ^ corootPair β (Pi.single j 1)) ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hαr : IsRoot τ α := (isRootComponent_componentRoots i).isRoot α hα
  have hβr : IsRoot τ β := isRoot_of_mem_rationalRoots S i hβ
  let bα : Fin τ.rank → Lˣ := fun j => t ^ corootPair α (Pi.single j 1)
  let bβ : Fin τ.rank → Lˣ := fun j => t' ^ corootPair β (Pi.single j 1)
  have hx : rootSL2 τ L α (HSL t) = rootDiagUnit τ bα := by
    change rootTorusSL2 τ L α t = rootDiagUnit τ bα
    exact CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hαr t
  have hy : rootSL2 τ L β (HSL t') = rootDiagUnit τ bβ := by
    change rootTorusSL2 τ L β t' = rootDiagUnit τ bβ
    exact CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hβr t'
  change rootDiagUnit τ (bα * bβ) ∈ _
  rw [rootDiagUnit_mul, ← hx, ← hy]
  exact prod_rootSL2_HSL_mem_rationalComponent_of_step S hτ hq hAlg i hα hβ horth
    hm ht ht' hstepα hstepβ hstepWα hstepWβ

end CFSG.StandardType.LangRat

end

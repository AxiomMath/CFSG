module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppSp
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourS2FramePlane
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppPumpup
public import CFSG.LocalAnalysis.StandardType.GGTPNTwA3Final
public import CFSG.LocalAnalysis.StandardType.GGKGPosLocalHypTw
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOmegaMinusTorality
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourR3CommOmega
import CFSG.LocalAnalysis.StandardType.GGLieModelPSULabel
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsCover
import CFSG.LocalAnalysis.StandardType.GGPZWeylB
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem F4Model

section CardWeyl

theorem card_ggAutomizer_and_weyl_of_tableBPos_S2 {G : Type} [Group G] {p : ℕ}
    {Bs X : Subgroup G} {f : ℕ} (hf : 1 ≤ f)
    (hX : GGTableBPosImage p Bs .POmegaMinus 4 f X ∨ GGTableBPosImage p Bs .PSU 6 f X) :
    Nat.card ↥(ggAutomizer X Bs) = 48 ∧ GGWeylReflectionGroup p (ggAutomizer X Bs) := by
  rcases hX with ⟨ψ, -, -, ε, hε, -, -⟩ | ⟨ψ, -, -, ε, hε, -, -⟩
  · refine ⟨?_, ⟨_, coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType, ?_, ε, hε⟩⟩
    · rw [← Nat.card_congr ε.toEquiv, coxeterMatrix_POmegaMinus_four]
      exact (ggCoxeterB_card 3 (by norm_num)).trans (by norm_num [Nat.factorial])
    · rw [coxeterMatrix_POmegaMinus_four]
      exact Or.inl ⟨3, Equiv.refl _, by omega,
        Or.inr (Or.inl ⟨by norm_num, (ggCoxeterMatrix_reindex_refl _).symm⟩)⟩
  · obtain ⟨σ, -, hσ⟩ := exists_coxeterMatrix_PSU_six hf
    have hM : coxeterMatrix (ggU .PSU 6 f).D.isFiniteType = (CoxeterMatrix.B 3).reindex σ := by
      ext i j
      rw [CoxeterMatrix.reindex_apply, ← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine ⟨?_, ⟨_, coxeterMatrix (ggU .PSU 6 f).D.isFiniteType, ?_, ε, hε⟩⟩
    · rw [← Nat.card_congr ε.toEquiv, hM,
        Nat.card_congr ((CoxeterMatrix.B 3).reindexGroupEquiv σ).toEquiv]
      exact (ggCoxeterB_card 3 (by norm_num)).trans (by norm_num [Nat.factorial])
    · rw [hM]
      exact Or.inl ⟨3, σ, by omega, Or.inr (Or.inl ⟨by norm_num, rfl⟩)⟩

end CardWeyl

section Endpoint

theorem ggF4QGeFourS2Endpoint_of_frame (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    {ψL : (ggU .POmegaMinus 4 f).K →* G}
    (hkerL : ψL.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K) (hrangeL : ψL.range = L)
    (hposL : GGTableBPos p Bs L .POmegaMinus 4 f ψL)
    (hposSU : ∀ (X : Subgroup G) (ψ : (ggU .PSU 6 f).K →* G),
      GGKGPosLocalHypTw p Bs X .PSU 6 f ψ → GGTableBPosImage p Bs .PSU 6 f X)
    (hposOm : ∀ (X : Subgroup G) (ψ : (ggU .POmegaMinus 4 f).K →* G),
      GGKGPosLocalHypTw p Bs X .POmegaMinus 4 f ψ → GGTableBPosImage p Bs .POmegaMinus 4 f X)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (he : ∀ i, GGIsReflection p
      ((e (CoxeterMatrix.F₄.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (R : F4Rep CoxeterMatrix.F₄.Group) (hRs : ∀ i, R.s i = CoxeterMatrix.F₄.simple i)
    {a : Fin 3 → CoxeterMatrix.F₄.Group}
    (haL : ∀ z, z ∈ Subgroup.closure (Set.range a) →
      ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs)
    {ga : CoxeterMatrix.F₄.Group}
    (hga : ga * a 0 * ga⁻¹ = R.s 0 ∧ ga * a 1 * ga⁻¹ = R.s 1 ∧ ga * a 2 * ga⁻¹ = R.s 2)
    (w₂ : CoxeterMatrix.F₄.Group)
    (hv : (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E1.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E1.neg.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E2.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E2.neg.toFun)
    (hrL : ((e (w₂ * CoxeterMatrix.F₄.simple 2 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
      MulAut ↥Bs) ∈ ggAutomizer L Bs)
    (huL : ((e (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
      MulAut ↥Bs) ∈ ggAutomizer L Bs) :
    ∃ (z : G) (A : Subgroup G),
      GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z A ∧
        GGCentralImage .PSU 6 f A ∧ GGTableBPosImage p Bs .PSU 6 f A ∧
        ∀ c ∈ Subgroup.closure ({R.s 1, R.s 2, R.s 3} : Set CoxeterMatrix.F₄.Group),
          ((e (w₂ * c * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈
            ggAutomizer A Bs := by
  classical
  have hR : GGSecFiveRestHyp p B Bs x L D J := hcfg.1
  have hc : GGConfig p B Bs x L D J := hR.1
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have : Fact p.Prime := ⟨hpp⟩
  have hf1 : 1 ≤ f := by omega
  have hAind : (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hF4W : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))
  have hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e :=
    ⟨hF4W, he⟩
  have hInnL : GGInnerDiagOn Bs L := hcfg.1.2.2.1.1
  obtain ⟨-, -, -, hcardL⟩ := id hposL
  have hrk : (ggU .POmegaMinus 4 f).D.rank = 3 := rfl
  rw [hrk] at hcardL
  obtain ⟨hB, hcard4⟩ := hc.eq_bstar_of_card_le hcardL
  obtain ⟨hpx, -, hxBs, hLx, -⟩ := hc.tableB_facts
  have hxne : x ≠ 1 := hc.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨xB, hxB⟩ : ∃ xB : ↥Bs, (xB : G) = x := ⟨⟨x, hxBs⟩, rfl⟩
  have hx1 : xB ≠ 1 := fun h => hxne (by rw [← hxB, h, Subgroup.coe_one])
  have hxL : ∀ φ ∈ ggAutomizer L Bs, φ xB = xB := by
    intro φ hφ
    obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
    apply Subtype.ext
    rw [hg xB, hxB]
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)
    rw [hgx]
    group
  have hfr := exists_bstarFrame_at hp2 hEl hNT hcard4 hAind e he R hRs haL hga hx1 hxL w₂ hv
  simp only [hRs] at hfr
  obtain ⟨r, hrdef⟩ : ∃ r : MulAut ↥Bs,
      r = ((e (w₂ * CoxeterMatrix.F₄.simple 2 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : MulAut ↥Bs,
      u = ((e (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) := ⟨_, rfl⟩
  obtain ⟨r', hr'def⟩ : ∃ r' : MulAut ↥Bs,
      r' = ((e (w₂ * CoxeterMatrix.F₄.simple 3 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) := ⟨_, rfl⟩
  rw [← hrdef, ← hudef, ← hr'def] at hfr
  rw [← hrdef] at hrL
  rw [← hudef] at huL
  obtain ⟨d, hrx, hux, hrd, hud, hr'd, hpl, hr'x, hmv, hopp⟩ := hfr
  have htorL := F4KGPosition.exists_ggTorus_conj_of_tableBPos_POmegaMinus hcfg (Or.inl rfl) hf hpf
    ψL hkerL hrangeL hposL
  obtain ⟨n, hnN, hn, hnc⟩ := ggF4QGeFourR3S1S3_POmegaMinus hcfg hf ⟨ψL, hkerL, hrangeL, hposL⟩ e
    hpres w₂ (hudef ▸ huL)
  rw [← hr'def] at hn
  rw [← hudef] at hnc
  have hxp' : xB ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hxB, Subgroup.coe_one]
    exact hEl.2 x hxBs)
  have hdD : (d : G) ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs u := ⟨⟨d, hrd, rfl⟩, ⟨d, hud, rfl⟩⟩
  have hDX : ¬ ggHyperplane Bs r ⊓ ggHyperplane Bs u ≤ Subgroup.centralizer (L : Set G) := by
    intro hle
    obtain ⟨φ, hφ, hφd⟩ := hmv
    obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
    apply hφd
    apply Subtype.ext
    rw [hg d]
    have hgd : g * d = d * g := Subgroup.mem_centralizer_iff.mp (hle hdD) g hgL
    rw [hgd]
    group
  obtain ⟨J', hJlay, hJcomp, hJcent, hSrJ, hSuJ, hLieJ, hpJ, hsmall⟩ :=
    exists_su4Plane_of_tableBPos_POmegaMinus hpp hp2 hEl hNT hAind hpres le_sup_left hf hpf hkerL
      hrangeL hposL htorL w₂ hrdef hudef hrL huL hDX
  obtain ⟨hPq, hPcard⟩ :=
    ggF4QGeFourOppPumpup_rankOne_POmegaMinus hcfg hpres hf hpf hkerL hrangeL hposL w₂ hudef huL
  obtain ⟨-, hStd, hnbr, -, hJA, -, hrA, huA, hr'A⟩ :=
    exists_oppPumpup_of_plane (ggPumpupInput_of_lBalance hLB) hc hB hpres w₂ hrdef hudef hr'def
      hrL huL hxB hrx hux hrd hud hr'd hpl hr'x hmv hnN hn hnc hJlay hJcomp hJcent hSrJ hSuJ hpJ
      hsmall hPq hPcard
  set D' : Subgroup G := ggHyperplane Bs r ⊓ ggHyperplane Bs u with hD'def
  set A : Subgroup G := ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J' with hAdef
  have hc' : GGConfig p B Bs x L D' J' := hR.config_of_stdSub hStd
  have hInnA : GGInnerDiagOn Bs A := hNPLA G p B Bs x L D J hR D' J' hStd d A hnbr
  have hΛ : LargeEvenInLambda2 (⟨.twA, 3, f⟩ : LargeEvenLabel) :=
    ⟨le_trans (by norm_num : 1 ≤ 2) hf, by norm_num, fun _ => hf⟩
  obtain ⟨labA, hlabA, -, hhA⟩ := ggNbrLabel_twA3_of_config hB3 hLB hc' hInnL hInnA hnbr hJA hpJ
    hJcent.le hf hpf hΛ (ggHasLabel_quotCenter_of_lieModel_PSU hLieJ)
  have hAN := isComponentOf_of_isNeighborOf hc'.1.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hc'.2.2 hnbr)
  have hd1 : d ≠ 1 := by
    have h := hopp 1 0
    rwa [map_one, OneMemClass.coe_one, MulAut.one_apply, pow_zero] at h
  have hdG1 : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hBCA : Bs ⊓ Subgroup.centralizer (A : Set G) = Subgroup.zpowers (d : G) := by
    have h := inf_centralizer_eq_zpowers_of_sHat hnbr.1
    rw [hB] at h
    exact h
  have hcardA : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (A : Set G)) ≤ Nat.card ↥Bs := by
    rw [hBCA, Nat.card_zpowers, orderOf_eq_prime (hEl.2 _ d.2) hdG1]
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ Nat.card ↥Bs := hc.tableB_facts.2.2.2.2
  have hgen : ∀ k : Fin 4, k ≠ 0 →
      ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom) (w₂ * R.s k * w₂⁻¹) ∈
        ggAutomizer A Bs := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · rw [hRs]
      rw [hudef] at huA
      exact huA
    · rw [hRs]
      rw [hrdef] at hrA
      exact hrA
    · rw [hRs]
      rw [hr'def] at hr'A
      exact hr'A
  have hPC : ∀ c ∈ Subgroup.closure ({R.s 1, R.s 2, R.s 3} : Set CoxeterMatrix.F₄.Group),
      ((e (w₂ * c * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈
        ggAutomizer A Bs := by
    have hle : Subgroup.closure ({R.s 1, R.s 2, R.s 3} : Set CoxeterMatrix.F₄.Group) ≤
        (ggAutomizer A Bs).comap
          (((ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom).comp
            (MulAut.conj w₂).toMonoidHom) := by
      rw [Subgroup.closure_le]
      rintro c (rfl | rfl | rfl)
      · exact hgen 1 (by decide)
      · exact hgen 2 (by decide)
      · exact hgen 3 (by decide)
    exact fun c hc => hle hc
  have hAAW : Nat.card ↥(ggAutomizer A Bs) ≤ 48 →
      ggAutomizer A Bs ≤ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    intro h48
    have h := le_range_of_card_le_48 R
      ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom)
      (Subtype.val_injective.comp e.injective) w₂ (X := ggAutomizer A Bs) hgen h48
    intro φ hφ
    obtain ⟨v, rfl⟩ := h hφ
    exact (e v).2
  have hdC : (d : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hAN.1.1 hh))
  have hfixA : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer A Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro b hb
    obtain ⟨j, hj⟩ := exists_eq_pow_of_frame_fix hpp hxp' hrx hr'd hpl hr'x (hb r hrA) (hb u huA)
      (hb r' hr'A)
    rw [hj, Subgroup.coe_pow]
    exact pow_mem hdC j
  have hFL : GGFixLineComp Bs (d : G) A := hc'.fixLineComp_nbr_of_fix hB hnbr hfixA
  have hoppW : ∀ w ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs), ∀ b : ↥Bs, (b : G) = (d : G) →
      ((w b : ↥Bs) : G) ∉ Subgroup.zpowers x := by
    rw [← hxB]
    exact forall_not_mem_zpowers_of_frame e hopp
  have hBsN : Bs ≤ Subgroup.normalizer (A : Set G) := by
    rw [← hB]
    exact hAN.2
  rcases hlabA with rfl | rfl
  ·
    have hAimg : GGCentralImage .PSU 6 f A :=
      ggF4Ends_centralImage_PSU (m := 5) hAN.1.2.2.1 (by norm_num) hf hhA
    have hApos : GGTableBPosImage p Bs .PSU 6 f A := by
      obtain ⟨ψA, hadmA, hkerA, hrangeA⟩ := id hAimg
      exact hposSU A ψA (ggKGPosLocalHypTw_of_f4 ggInnerDiagMpInput_holds hcfg hf hpf (by decide)
        ψA hadmA hkerA hrangeA hInnA hcardA)
    obtain ⟨h48, hWRA⟩ := card_ggAutomizer_and_weyl_of_tableBPos_S2 hf1 (Or.inr hApos)
    exact ⟨(d : G), A, ⟨hFL, hdG1, hBsN, hAAW h48.le, hWRA, hoppW⟩, hAimg, hApos, hPC⟩
  ·
    exfalso
    have hAimg : GGCentralImage .POmegaMinus 4 f A :=
      ggF4Ends_centralImage_POmegaMinus hAN.1.2.2.1 hf hhA
    have hApos : GGTableBPosImage p Bs .POmegaMinus 4 f A := by
      obtain ⟨ψA, hadmA, hkerA, hrangeA⟩ := id hAimg
      exact hposOm A ψA (ggKGPosLocalHypTw_of_f4 ggInnerDiagMpInput_holds hcfg hf hpf (by decide)
        ψA hadmA hkerA hrangeA hInnA hcardA)
    obtain ⟨h48, -⟩ := card_ggAutomizer_and_weyl_of_tableBPos_S2 hf1 (Or.inl hApos)
    have hfixL : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x := by
      intro b hb
      obtain ⟨i, j, hij⟩ := hpl b (hb r hrL) (hb u huL)
      obtain ⟨φ, hφ, hφd⟩ := hmv
      have hdp : d ^ p = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hEl.2 _ d.2)
      have hdj : d ^ j = 1 := by
        by_contra hne
        have hndvd : ¬ p ∣ j := fun ⟨c, hc⟩ => hne (by rw [hc, pow_mul, hdp, one_pow])
        obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
          ((Nat.Prime.coprime_iff_not_dvd hpp).2 hndvd).symm hpp.one_lt
        have hφj : φ (d ^ j) = d ^ j := by
          have h1 := hb φ hφ
          rw [hij, map_mul, map_pow, map_pow, hxL φ hφ] at h1
          rw [map_pow]
          exact mul_left_cancel h1
        have hdk : (d ^ j) ^ m = d := by
          rw [← pow_mul, ← Nat.div_add_mod (j * m) p, hm, pow_add, pow_mul, hdp, one_pow,
            one_mul, pow_one]
        apply hφd
        rw [← hdk, map_pow, hφj]
      rw [hij, hdj, mul_one, Subgroup.coe_pow, hxB]
      exact pow_mem (Subgroup.mem_zpowers x) i
    have hLfix : GGFixLineComp Bs x L := hc.fixLineComp_L_of_fix hfixL
    have huR : GGIsReflection p u := ggCoxRefl_isReflection hpres.2 ⟨w₂, 1, hudef⟩
    obtain ⟨w, hw, hwd⟩ := exists_mem_zpowers_of_tableBPos_POmegaMinus hpp hp2 hEl hNT hAind hpres
      hLfix hFL hBsN le_sup_left (hAAW h48.le) hf ⟨ψL, hkerL, hrangeL, hposL⟩ hApos huL huA huR
    exact hoppW w hw d rfl (hwd d rfl)

theorem ggF4QGeFourOppOmega_at (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L) {y : G} {K : Subgroup G}
    (hNb : GGNbr p B x D J y K)
    (hWF4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (hLim : GGCentralImage .POmegaMinus 4 f L)
    (hposSU : ∀ (X : Subgroup G) (ψ : (ggU .PSU 6 f).K →* G),
      GGKGPosLocalHypTw p Bs X .PSU 6 f ψ → GGTableBPosImage p Bs .PSU 6 f X)
    (hposOm : ∀ (X : Subgroup G) (ψ : (ggU .POmegaMinus 4 f).K →* G),
      GGKGPosLocalHypTw p Bs X .POmegaMinus 4 f ψ → GGTableBPosImage p Bs .POmegaMinus 4 f X) :
    ∃ (z : G) (A : Subgroup G),
      GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z A ∧
        GGCentralImage .PSU 6 f A := by
  classical
  set W := ggAutomizer L Bs ⊔ ggAutomizer K Bs with hWdef
  have hcfg : GGF4QGeFourCfg p B Bs x L D J y K := ⟨hR, hW, hq, hNb⟩
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hAind : W ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  obtain ⟨ψL0, hadmL, hkerL0, hrangeL0⟩ := hLim
  obtain ⟨ψL, hkerL, hrangeL, hposL'⟩ := hposOm L ψL0
    (ggKGPosLocalHypTw_of_f4_member ggInnerDiagMpInput_holds hcfg (Or.inl rfl) hf hpf (by decide)
      ψL0 hadmL hkerL0 hrangeL0)
  obtain ⟨εL, hεL, -, -⟩ := id hposL'
  obtain ⟨e, he⟩ := hWF4
  have hF4W : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))
  have hpres : GGCoxeterPres p W CoxeterMatrix.F₄ e := ⟨hF4W, he⟩
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_POmegaMinus_four]
    rfl
  obtain ⟨a, ha, ha01, ha12, ha02, haL⟩ :=
    exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_left εL hεL (Equiv.refl _) hM
  obtain ⟨R, hRs0⟩ := exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hRs : ∀ k, R.s k = CoxeterMatrix.F₄.simple k := by
    intro k
    rw [hRs0 k, CoxeterMatrix.toCoxeterSystem_simple]
  have haR : ∀ k, R.IsRefl (a k) := fun k => (F4Rep.isRefl_iff hRs0).2 (ha k)
  obtain ⟨e', a', g, he', haL', hga⟩ :=
    exists_f4Pres_tripleB e he R hRs haR ha01 ha12 ha02 fun z hz => (haL z).1 hz
  have hrL : ((e' (g⁻¹ * CoxeterMatrix.F₄.simple 2 * g⁻¹⁻¹) : ↥W) : MulAut ↥Bs) ∈
      ggAutomizer L Bs := by
    apply haL'
    rw [show g⁻¹ * CoxeterMatrix.F₄.simple 2 * g⁻¹⁻¹ = a' 2 by rw [← hRs 2, ← hga.2.2]; group]
    exact Subgroup.subset_closure ⟨2, rfl⟩
  have huL : ((e' (g⁻¹ * CoxeterMatrix.F₄.simple 1 * g⁻¹⁻¹) : ↥W) : MulAut ↥Bs) ∈
      ggAutomizer L Bs := by
    apply haL'
    rw [show g⁻¹ * CoxeterMatrix.F₄.simple 1 * g⁻¹⁻¹ = a' 1 by rw [← hRs 1, ← hga.2.1]; group]
    exact Subgroup.subset_closure ⟨1, rfl⟩
  obtain ⟨z, A, hEnd, hCI, -, -⟩ := ggF4QGeFourS2Endpoint_of_frame hLB hB3 hNPLA hcfg hf hpf
    hkerL hrangeL hposL' hposSU hposOm he' R hRs haL' hga g⁻¹
    (Or.inl (by rw [mul_inv_cancel, inv_one, map_one, Matrix.one_mulVec])) hrL huL
  exact ⟨z, A, hEnd, hCI⟩

theorem ggF4QGeFourOppOmegaInput_of_inputs (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput)
    (hSU : GGKGPosTwInput .PSU 6) (hOm : GGKGPosTwInput .POmegaMinus 4) :
    GGF4QGeFourOppOmegaInput := by
  intro G _ _ p B Bs x L D J hR hW hq y K hNb _ _ hWF4 f hf hpf hLim
  exact ggF4QGeFourOppOmega_at hLB hB3 hNPLA hR hW hq hNb hWF4 hf hpf hLim
    (fun X ψ => hSU G p Bs X f ψ) (fun X ψ => hOm G p Bs X f ψ)

end Endpoint

end CFSG.StandardType

end

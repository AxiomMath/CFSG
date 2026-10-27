module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCross
import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofFamilies
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofL3Aut
public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofCore
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofL3Type

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

open CFSG.Assembly.RankThreeEven (projSL)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedScalars)

open Matrix

namespace Item228Census4Proof

variable {F : Type} [Field F]

theorem toGL_slConjugation (x : GL (Fin 3) F) (g : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.toGL (slConjugation 3 F x g) = x * SpecialLinearGroup.toGL g * x⁻¹ := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_slConjugation]
  rfl

theorem toGL_mem_centMod_of_conjAut_fix {x : GL (Fin 3) F} {g : SpecialLinearGroup (Fin 3) F}
    (q : ℕ) (hfix : conjAut 3 F x (proj 3 F g) = proj 3 F g) :
    SpecialLinearGroup.toGL g ∈ Sec4.centMod (Sec4.slPi true 3 q F) x := by
  rw [Sec4.mem_centMod_iff_scalar]
  refine ⟨(Sec4.mem_slPi_true q).mpr g.2, ?_⟩
  rw [conjAut_proj, proj_eq_proj_iff] at hfix
  obtain ⟨c, -, hc⟩ := hfix
  set G₀ := SpecialLinearGroup.toGL g with hG₀
  set s := GeneralLinearGroup.scalar (Fin 3) c with hs
  have h2 : SpecialLinearGroup.toGL ((slConjugation 3 F x g)⁻¹ * g) = s := by
    apply Units.ext
    rw [SpecialLinearGroup.coe_GL_coe_matrix, hc, hs, GeneralLinearGroup.coe_scalar]
  rw [map_mul, map_inv, toGL_slConjugation] at h2
  have hcen : ∀ h : GL (Fin 3) F, h * s = s * h := fun h =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c h).eq
  refine ⟨s, ⟨c, rfl⟩, ?_⟩
  calc G₀ * x * G₀⁻¹ = G₀ * ((x * G₀ * x⁻¹)⁻¹ * G₀) * G₀⁻¹ * x := by group
    _ = s * x := by rw [h2, hcen G₀, mul_inv_cancel_right]

theorem toGL_mul_comm_of_slConjugation_fix {x : GL (Fin 3) F} {g : SpecialLinearGroup (Fin 3) F}
    (h : slConjugation 3 F x g = g) :
    SpecialLinearGroup.toGL g * x = x * SpecialLinearGroup.toGL g := by
  have h1 := congrArg SpecialLinearGroup.toGL h
  rw [toGL_slConjugation] at h1
  calc SpecialLinearGroup.toGL g * x = x * SpecialLinearGroup.toGL g * x⁻¹ * x := by rw [h1]
    _ = x * SpecialLinearGroup.toGL g := by group

theorem slConjugation_fix_of_toGL_mul_comm {x : GL (Fin 3) F} {g : SpecialLinearGroup (Fin 3) F}
    (h : SpecialLinearGroup.toGL g * x = x * SpecialLinearGroup.toGL g) :
    slConjugation 3 F x g = g := by
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, ← h, mul_inv_cancel_right]

theorem exists_data_true [Finite F] (h3 : 3 ∣ Nat.card F - 1) {x : GL (Fin 3) F}
    (hxZ : x ∉ StatedScalars (Fin 3) F) (hx3 : x ^ 3 ∈ StatedScalars (Fin 3) F) :
    ∃ (p f : ℕ) (_ : Sec4.PiField true p f F) (_ : Sec4.ModThree true (p ^ f)) (τ : F),
      τ ^ 3 = 1 ∧ τ ≠ 1 ∧ x ∈ Sec4.glPi true 3 (p ^ f) F ∧
      x ∉ Sec4.zPi true 3 (p ^ f) F ∧ x ^ 3 ∈ Sec4.zPi true 3 (p ^ f) F := by
  obtain ⟨p, f, hK⟩ := exists_piField_true F
  have hqK : Nat.card F = p ^ f := hK.card
  have hq : Sec4.ModThree true (p ^ f) := by
    change p ^ f % 3 = 1
    have h1 : 1 ≤ Nat.card F := Nat.card_pos
    rw [← hqK]
    omega
  obtain ⟨τ, hτ, hτ1⟩ := exists_cube_root_of_unity h3
  have hπ : true = false → UnitaryFieldData p f F := fun h => absurd h (by decide)
  have hq' : true = false → Sec4.ModThree false (p ^ f) := fun h => absurd h (by decide)
  have hZ := Sec4.zPi_eq hπ hq' hτ hτ1
  refine ⟨p, f, hK, hq, τ, hτ, hτ1, Sec4.mem_glPi_true _ x, ?_, ?_⟩
  · rw [hZ]
    exact fun h => hxZ h.2
  · rw [hZ]
    exact ⟨Sec4.mem_glPi_true _ _, hx3⟩

theorem false_of_fix_projectiveSL [Finite F] (h3 : 3 ∣ Nat.card F - 1) (hodd : Odd (Nat.card F))
    {x : GL (Fin 3) F} (hxZ : x ∉ StatedScalars (Fin 3) F)
    (hx3 : x ^ 3 ∈ StatedScalars (Fin 3) F) {Qs : Subgroup (projectiveSL 3 F)} {m : ℕ}
    (eQ : Qs ≃* projSL 2 (GaloisField 2 m)) (hm : 2 ≤ m)
    (hfix : ∀ q ∈ Qs, conjAut 3 F x q = q) : False := by
  obtain ⟨p, f, hK, hq, τ, hτ, hτ1, hxH, hxZ', hx3'⟩ := exists_data_true h3 hxZ hx3
  have h2 := two_ne_zero_of_odd_card hodd
  set M₀ : Subgroup (SpecialLinearGroup (Fin 3) F) := Qs.comap (proj 3 F) with hM₀
  set M : Subgroup (GL (Fin 3) F) := M₀.map SpecialLinearGroup.toGL with hMdef
  let ι : M₀ ≃* M := M₀.equivMapOfInjective _ SpecialLinearGroup.toGL_injective
  let ψ₀ : M₀ →* Qs := ((proj 3 F).comp M₀.subtype).codRestrict Qs fun g => g.2
  let ψ : M →* Qs := ψ₀.comp ι.symm.toMonoidHom
  have hιv : ∀ g : M₀, ((ι g : M) : GL (Fin 3) F) = SpecialLinearGroup.toGL g := fun g => rfl
  have hψι : ∀ g : M₀, ψ (ι g) = ψ₀ g := fun g => by
    change ψ₀ (ι.symm (ι g)) = ψ₀ g
    rw [MulEquiv.symm_apply_apply]
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨g, hg⟩ := proj_surjective 3 F (q : projectiveSL 3 F)
    have hgM : g ∈ M₀ := by
      change proj 3 F g ∈ Qs
      rw [hg]
      exact q.2
    refine ⟨ι ⟨g, hgM⟩, ?_⟩
    rw [hψι]
    exact Subtype.ext hg
  have hker : ∀ g : M, ψ g = 1 → (g : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := by
    intro g hg
    obtain ⟨g₀, rfl⟩ := ι.surjective g
    rw [hψι] at hg
    have h1 : proj 3 F (g₀ : SpecialLinearGroup (Fin 3) F) = 1 := congrArg Subtype.val hg
    rw [proj_eq_one_iff] at h1
    obtain ⟨c, -, hc⟩ := h1
    refine ⟨c, Units.ext ?_⟩
    rw [hιv, GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix, hc]
  have hMle : M ≤ Sec4.centMod (Sec4.slPi true 3 (p ^ f) F) x := by
    rintro _ ⟨g, hg, rfl⟩
    exact toGL_mem_centMod_of_conjAut_fix (p ^ f) (hfix _ hg)
  have : IsSimpleGroup Qs := isSimpleGroup_of_mulEquiv hm eQ
  exact false_of_le_centMod_odd hK hq hτ hτ1 h2 hxH hxZ' hx3' hMle ψ hψ hker
    (exists_not_commute_of_mulEquiv_projSL eQ) (exists_two_involutions hm eQ)

theorem false_of_fix_SL [Finite F] (h3 : 3 ∣ Nat.card F - 1) (hodd : Odd (Nat.card F))
    {x : GL (Fin 3) F} (hxZ : x ∉ StatedScalars (Fin 3) F)
    (hx3 : x ^ 3 ∈ StatedScalars (Fin 3) F) {Qs : Subgroup (SpecialLinearGroup (Fin 3) F)}
    {m : ℕ} (eQ : Qs ≃* projSL 2 (GaloisField 2 m)) (hm : 2 ≤ m)
    (hfix : ∀ k ∈ Qs, conjAut 3 F x (proj 3 F k) = proj 3 F k) : False := by
  obtain ⟨p, f, hK, hq, τ, hτ, hτ1, hxH, hxZ', hx3'⟩ := exists_data_true h3 hxZ hx3
  have h2 := two_ne_zero_of_odd_card hodd
  set M : Subgroup (GL (Fin 3) F) := Qs.map SpecialLinearGroup.toGL with hMdef
  let ι : Qs ≃* M := Qs.equivMapOfInjective _ SpecialLinearGroup.toGL_injective
  let ψ : M →* Qs := ι.symm.toMonoidHom
  have hψ : Function.Surjective ψ := ι.symm.surjective
  have hker : ∀ g : M, ψ g = 1 → (g : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := by
    intro g hg
    have h1 : g = 1 := ι.symm.injective (hg.trans (map_one _).symm)
    rw [h1]
    exact (StatedScalars (Fin 3) F).one_mem
  have hMle : M ≤ Sec4.centMod (Sec4.slPi true 3 (p ^ f) F) x := by
    rintro _ ⟨g, hg, rfl⟩
    exact toGL_mem_centMod_of_conjAut_fix (p ^ f) (hfix _ hg)
  have : IsSimpleGroup Qs := isSimpleGroup_of_mulEquiv hm eQ
  exact false_of_le_centMod_odd hK hq hτ hτ1 h2 hxH hxZ' hx3' hMle ψ hψ hker
    (exists_not_commute_of_mulEquiv_projSL eQ) (exists_two_involutions hm eQ)

theorem card_eq_of_config_SL_even [Finite F] (h3 : 3 ∣ Nat.card F - 1)
    (hev : Even (Nat.card F)) {β : MulAut (SpecialLinearGroup (Fin 3) F)} {x : GL (Fin 3) F}
    (hx : conjAut 3 F x = descendAut 3 F β) (hβ1 : β ≠ 1) (hβ3 : β ^ 3 = 1)
    {N Kb : Subgroup (SpecialLinearGroup (Fin 3) F)} {m : ℕ}
    (hcfg : Config228Aut (SpecialLinearGroup (Fin 3) F) β N Kb m) : Nat.card F = 2 ^ m := by
  have : CharP F 2 := charP_two_of_even_card hev
  have hβx : β = slConjugation 3 F x :=
    Sec4.descendAut_three_injective (hx.symm.trans rfl)
  have hxZ : x ∉ StatedScalars (Fin 3) F := by
    rintro ⟨c, hc⟩
    apply hβ1
    apply Sec4.descendAut_three_injective
    rw [← hx, map_one]
    exact (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl x).mpr ⟨c, hc⟩
  have hx3 : x ^ 3 ∈ StatedScalars (Fin 3) F := by
    obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl (x ^ 3)).mp
      (by rw [map_pow, hx, ← map_pow, hβ3, map_one])
    exact ⟨c, hc⟩
  obtain ⟨p, f, hK, hq, τ, hτ, hτ1, -, -, -⟩ := exists_data_true h3 hxZ hx3
  have hm2 := two_le_of_even hcfg.pos hcfg.even
  obtain ⟨eK⟩ := hcfg.equiv
  set N' : Subgroup (GL (Fin 3) F) := N.map SpecialLinearGroup.toGL with hN'
  set Kb' : Subgroup (GL (Fin 3) F) := Kb.map SpecialLinearGroup.toGL with hKb'
  have hfixβ : ∀ g : SpecialLinearGroup (Fin 3) F, β g = g ↔
      SpecialLinearGroup.toGL g * x = x * SpecialLinearGroup.toGL g := fun g => by
    rw [hβx]
    exact ⟨toGL_mul_comm_of_slConjugation_fix, slConjugation_fix_of_toGL_mul_comm⟩
  have hNC : N' ≤ Sec4.slPi true 3 (p ^ f) F ⊓ Subgroup.centralizer {x} := by
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨(Sec4.mem_slPi_true _).mpr k.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hfixβ k).mp (hcfg.fix k hk)
  have hnorm : ∀ g ∈ Sec4.slPi true 3 (p ^ f) F ⊓ Subgroup.centralizer {x}, ∀ k ∈ N',
      g * k * g⁻¹ ∈ N' := by
    intro g hg k hk
    obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.mp hg
    have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := (Sec4.mem_slPi_true _).mp hgL
    set g₀ : SpecialLinearGroup (Fin 3) F := ⟨g, hdet⟩ with hg₀
    have hgg : SpecialLinearGroup.toGL g₀ = g := Units.ext rfl
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC
    have hβg : β g₀ = g₀ := (hfixβ g₀).mpr (by rw [hgg]; exact hgC)
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    refine ⟨g₀ * k₀ * g₀⁻¹, hcfg.normalizes g₀ hβg k₀ hk₀, ?_⟩
    rw [map_mul, map_mul, map_inv, hgg]
  have hKbN : Kb' ≤ N' := Subgroup.map_mono hcfg.le
  let eKb : Kb ≃* Kb' := Kb.equivMapOfInjective _ SpecialLinearGroup.toGL_injective
  have : IsSimpleGroup Kb' := isSimpleGroup_of_mulEquiv hm2 (eKb.symm.trans eK)
  have hnc := exists_not_commute_of_mulEquiv_projSL (eKb.symm.trans eK)
  have hcard : Nat.card Kb' = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [← Nat.card_congr eKb.toEquiv, Nat.card_congr eK.toEquiv, card_projSL_two m (by omega)]
  have hU : Kb' = N' ∨ Nat.card N' = 62400 := by
    rcases hcfg.eq_or with h | h
    · exact Or.inl (by rw [hKb', hN', h])
    · right
      rw [← Nat.card_congr (N.equivMapOfInjective _ SpecialLinearGroup.toGL_injective).toEquiv]
      exact Item22Res4Proof.card_of_statedU34 h
  exact card_eq_two_pow_of_le_centralizer_even hK hq hτ hτ1 hxZ hx3 hNC hnorm hKbN hnc hcard
    hcfg.pos hcfg.even hU

end Item228Census4Proof

open Item228Census4Proof

section Certs


theorem census228L3TypeLinOdd_holds : Census228L3TypeLinOdd := by
  intro G _ _ X A K K₀ m hL hP hAmax hA27 hAN hAC hdiag _ _ ρ hρ hρr hKK hK0X hK0C hnorm hU hKm
    hm0 hme
  obtain ⟨F, _, _, h3, hodd, hiso⟩ := hP
  exfalso
  obtain ⟨b, hbA, hbN, hβ1, N, Kb, hcfg⟩ := Item228Census2Proof.config228Aut_of hAmax hA27 hAN
    hAC hρ hρr hKK hK0X hK0C hnorm hU hKm hm0 hme
  have hb3 : b ^ 3 = 1 := hAmax.prop.2 b hbA
  have hm2 := two_le_of_even hm0 hme
  obtain ⟨eK⟩ := hcfg.equiv
  have hβ3 := thetaQuotMulAut_pow_three hbN hb3
  rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  ·
    have hlin : inducedAutHom X e ⟨b, hbN⟩ ∈ linearAutGroup 3 F := by
      by_cases ho : Sec4.InducesOuterTheta b X
      · exact (outer223Cross_holds G X b hL hb3 (hdiag b hbA ho)).1 F h3 e hbN
      · obtain ⟨y, hy⟩ := mem_range_conj_of_not_inducesOuterTheta hbN ho
        rw [inducedAutHom_apply, ← hy, congr_mulAutConj]
        exact innAut_le_linearAutGroup 3 F ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := mem_linearAutGroup_iff.mp hlin
    rw [inducedAutHom_apply] at hx
    have hxZ : x ∉ StatedScalars (Fin 3) F := by
      rintro ⟨c, hc⟩
      apply hβ1
      have h1 := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl x).mpr ⟨c, hc⟩
      rw [hx] at h1
      exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
    have hx3 : x ^ 3 ∈ StatedScalars (Fin 3) F := by
      obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl (x ^ 3)).mp
        (by rw [map_pow, hx, ← map_pow, hβ3, map_one])
      exact ⟨c, hc⟩
    refine false_of_fix_projectiveSL h3 hodd hxZ hx3 (Qs := Kb.map e.toMonoidHom)
      ((Kb.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK) hm2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [hx]
    simp [MulAut.congr_apply, hcfg.fix k (hcfg.le hk)]
  ·
    have hlin : descendAut 3 F (inducedAutHom X e ⟨b, hbN⟩) ∈ linearAutGroup 3 F := by
      by_cases ho : Sec4.InducesOuterTheta b X
      · exact (outer223Cross_holds G X b hL hb3 (hdiag b hbA ho)).2.1 F h3 e hbN
      · obtain ⟨y, hy⟩ := mem_range_conj_of_not_inducesOuterTheta hbN ho
        rw [inducedAutHom_apply, ← hy, congr_mulAutConj, descendAut_conj, conj_proj_eq_conjAut]
        exact conjAut_mem_linearAutGroup _
    obtain ⟨x, hx⟩ := mem_linearAutGroup_iff.mp hlin
    rw [inducedAutHom_apply] at hx
    have hxZ : x ∉ StatedScalars (Fin 3) F := by
      rintro ⟨c, hc⟩
      apply hβ1
      have h1 := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl x).mpr ⟨c, hc⟩
      rw [hx, ← map_one (descendAut 3 F)] at h1
      exact (MulAut.congr e).injective
        ((Sec4.descendAut_three_injective h1).trans (map_one _).symm)
    have hx3 : x ^ 3 ∈ StatedScalars (Fin 3) F := by
      obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl (x ^ 3)).mp
        (by rw [map_pow, hx, ← map_pow, ← map_pow, hβ3, map_one, map_one])
      exact ⟨c, hc⟩
    refine false_of_fix_SL h3 hodd hxZ hx3 (Qs := Kb.map e.toMonoidHom)
      ((Kb.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK) hm2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [hx, descendAut_proj]
    congr 1
    simp [MulAut.congr_apply, hcfg.fix k (hcfg.le hk)]

theorem census228L3TypeSLEven_holds : Census228L3TypeSLEven := by
  intro G _ _ X A K K₀ m hL hP hAmax hA27 hAN hAC hdiag _ _ ρ hρ hρr hKK hK0X hK0C hnorm hU hKm
    hm0 hme
  obtain ⟨F, _, _, h3, heven, ⟨e⟩⟩ := hP
  obtain ⟨b, hbA, hbN, hβ1, N, Kb, hcfg⟩ := Item228Census2Proof.config228Aut_of hAmax hA27 hAN
    hAC hρ hρr hKK hK0X hK0C hnorm hU hKm hm0 hme
  have hb3 : b ^ 3 = 1 := hAmax.prop.2 b hbA
  have hβ3 := thetaQuotMulAut_pow_three hbN hb3
  have hlin : descendAut 3 F (inducedAutHom X e ⟨b, hbN⟩) ∈ linearAutGroup 3 F := by
    by_cases ho : Sec4.InducesOuterTheta b X
    · exact (outer223Cross_holds G X b hL hb3 (hdiag b hbA ho)).2.1 F h3 e hbN
    · obtain ⟨y, hy⟩ := mem_range_conj_of_not_inducesOuterTheta hbN ho
      rw [inducedAutHom_apply, ← hy, congr_mulAutConj, descendAut_conj, conj_proj_eq_conjAut]
      exact conjAut_mem_linearAutGroup _
  obtain ⟨x, hx⟩ := mem_linearAutGroup_iff.mp hlin
  rw [inducedAutHom_apply] at hx
  set β := Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hbN⟩) with hβ
  have hcfg' : Config228Aut (SpecialLinearGroup (Fin 3) F) (MulAut.congr e β)
      (N.map e.toMonoidHom) (Kb.map e.toMonoidHom) m := by
    refine ⟨?_, ?_, Subgroup.map_mono hcfg.le, ?_, hcfg.pos, hcfg.even, ?_⟩
    · rintro _ ⟨k, hk, rfl⟩
      simp [MulAut.congr_apply, hcfg.fix k hk]
    · intro g hg k hk
      obtain ⟨g', rfl⟩ := e.surjective g
      have hg' : β g' = g' := by
        have := congrArg e.symm hg
        simpa [MulAut.congr_apply] using this
      obtain ⟨k', hk', rfl⟩ := hk
      refine ⟨g' * k' * g'⁻¹, hcfg.normalizes g' hg' k' hk', ?_⟩
      simp [map_mul, map_inv]
    · obtain ⟨eK⟩ := hcfg.equiv
      exact ⟨(Kb.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK⟩
    · rcases hcfg.eq_or with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv
          (N.equivMapOfInjective e.toMonoidHom e.injective).symm h)
  have hβ1' : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hβ3' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hcard : Nat.card F = 2 ^ m := card_eq_of_config_SL_even h3 heven hx hβ1' hβ3' hcfg'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hFG : Fintype.card F = Fintype.card (GaloisField 2 m) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcard, GaloisField.card 2 m hm0.ne']
  exact Or.inl (Or.inl ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr
    (Fin 3) (FiniteField.ringEquivOfCardEq hFG))⟩)

end Certs

end CFSG.RankThree.PartTwo.Sec21

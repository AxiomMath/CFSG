module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryOrthBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryRecognition
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryFour
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalGen
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightOmega
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPOmegaPlus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPOmegaPlus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaPlus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpBlockFixed
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaPlusFixed

public section

namespace CFSG.StandardType.RCKC1

open Matrix CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.RCKRP CFSG.StandardType.RCKK1IIISp
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedLieAdmissible)


theorem parameters_of_row_III_of_unitary_cover
    {X : Type} [Group X] [Finite X] {n f : ℕ} {J : Subgroup X}
    (hf : 1 ≤ f) (π : (ggU .PSU n f).K →* X) (hπr : π.range = J)
    (hπk : π.ker ≤ Subgroup.center (ggU .PSU n f).K)
    (hrow : GGSixRCKJRow .III J) : f = 1 ∧ 4 ≤ n := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (2 * (g + 1))
  let σ := CFSG.LieType.BorelTits.unitaryInvolution F 2 (g + 1)
  have : Finite (ggU .PSU n (g + 1)).K := inferInstanceAs (Finite ↥(SU σ n))
  let j : (ggU .PSU n (g + 1)).K →* GL (Fin n) F := (SU σ n).subtype
  have hn : 3 ≤ n := three_le_of_row_III_of_matrix_range
    j (Subgroup.subtype_injective _) π (le_of_eq hπr.symm) hrow
  have hgood : (n, 2 ^ (g + 1)) ≠ (3, 2) := by
    intro hbad
    have hn3 : n = 3 := (Prod.mk.inj hbad).1
    have hg1 : g + 1 = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      (by simpa using (Prod.mk.inj hbad).2)
    obtain rfl : g = 0 := by omega
    subst n
    have hcard : Nat.card (ggU .PSU 3 (0 + 1)).K = 216 := by
      have hc := card_galoisField_two_mul 2 1 (by norm_num : 1 ≤ 1)
      have h := CFSG.RankThree.PartOne.KFOUT3.card_suAnti_three
        (K := GaloisField 2 (2 * 1)) hc (by norm_num : 1 ≤ 1)
      norm_num at h
      exact h
    have hJdvd : Nat.card J ∣ Nat.card (ggU .PSU 3 (0 + 1)).K := by
      rw [← hπr]
      exact Subgroup.card_range_dvd π
    have h64 := (two_pow_six_dvd_card_centerQuot_of_row_III hrow).trans
      ((Subgroup.card_quotient_dvd_card (Subgroup.center ↥J)).trans hJdvd)
    rw [hcard] at h64
    norm_num at h64
  have hadm : StatedLieAdmissible .PSU n 2 (g + 1) :=
    ⟨Nat.prime_two, by omega, hn, hgood⟩
  have hm := irg_lieModel_quot (Or.inr (Or.inl rfl)) hadm π hπr hπk
  obtain ⟨hf, ht⟩ := lieModel_parameters_of_row_III hrow hm
  refine ⟨by omega, ?_⟩
  rcases ht with ⟨hbad, -⟩ | ⟨-, hn4⟩
  · cases hbad
  · exact hn4

theorem false_of_row_III_of_linear_cover
    {X : Type} [Group X] [Finite X] {r f : ℕ} {J : Subgroup X}
    (hf : 1 ≤ f) (π : (ggU .PSL (r + 1) f).K →* X) (hπr : π.range = J)
    (hπk : π.ker ≤ Subgroup.center (ggU .PSL (r + 1) f).K)
    (hrow : GGSixRCKJRow .III J) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let j : (ggU .PSL (r + 1) f).K →* GL (Fin (r + 1)) (GaloisField 2 f) := SpecialLinearGroup.toGL
  have hj : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun a : GL (Fin (r + 1)) (GaloisField 2 f) =>
      (a : Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField 2 f))) hxy)
  have : Finite (ggU .PSL (r + 1) f).K :=
    inferInstanceAs (Finite (SpecialLinearGroup (Fin (r + 1)) (GaloisField 2 f)))
  have hn : 3 ≤ r + 1 := three_le_of_row_III_of_matrix_range j hj π (by rw [hπr]) hrow
  have hadm : StatedLieAdmissible .PSL (r + 1) 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, ?_, ?_⟩
    all_goals intro hbad; have := (Prod.mk.inj hbad).1; omega
  have hm := irg_lieModel_quot (Or.inl rfl) hadm π hπr hπk
  rcases (lieModel_parameters_of_row_III hrow hm).2 with ⟨hbad, -⟩ | ⟨hbad, -⟩
  all_goals cases hbad

theorem eq_one_of_row_III_of_selfDualTwo_plus_block
    {X : Type} [Group X] [Finite X] {k f : ℕ} (hf : 1 ≤ f)
    (φ : (ggU .POmegaPlus (k + 3) f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hrow : GGSixRCKJRow .III (J'.map φ)) : f = 1 := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hmodel := exists_blockModel_selfDualTwo_POmegaPlus_explicit
    k (g + 1) S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  obtain ⟨r, ι, _β₀, _hdim, _hlong, hcent, hrange, _rest⟩ := hmodel
  let ιA : (ggU .PSU r (max (g + 1) 1)).K →* (ggU .POmegaPlus (k + 3) (g + 1)).K := ι
  let π : (ggU .PSU r (max (g + 1) 1)).K →* X := φ.comp ιA
  have hπr : π.range = J'.map φ := by
    dsimp only [π]
    rw [MonoidHom.range_comp, show ιA.range = J' from hrange]
  have hπk : π.ker ≤ Subgroup.center (ggU .PSU r (max (g + 1) 1)).K := by
    intro y hy
    exact hcent y (hφk hy)
  have hg := (parameters_of_row_III_of_unitary_cover (by omega) π hπr hπk hrow).1
  omega

theorem false_of_row_III_of_dualPair_plus_block
    {X : Type} [Group X] [Finite X] {k f : ℕ} (hf : 1 ≤ f)
    (φ : (ggU .POmegaPlus (k + 3) f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K)
    (s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hsU : s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hsodd : Odd (orderOf s))
    {ε e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e ≠ e)
    (hεeq : ε = e + formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e < 2)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) {s} ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) {s} ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hrow : GGSixRCKJRow .III (J'.map φ)) : False := by
  subst hεeq
  have hSU : ∀ t ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      t ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hsU
  have hS : ∀ t ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      ∀ t' ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))), Commute t t' := by
    intro t ht t' ht'
    rw [Set.mem_singleton_iff] at ht ht'
    subst ht
    subst ht'
    exact Commute.refl _
  have hodd : ∀ t ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      Odd (orderOf t) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hsodd
  obtain ⟨r, ι, β₀, hdim, hlong, hcent, hrange, rest⟩ :=
    exists_blockModel_dualPair_POmegaPlus_explicit k f hf {s} hSU hS hodd he hpair hdeg hJe
  let ιA : (ggU .PSL (r + 1) f).K →* (ggU .POmegaPlus (k + 3) f).K := ι
  let π : (ggU .PSL (r + 1) f).K →* X := φ.comp ιA
  have hπr : π.range = J'.map φ := by
    dsimp only [π]
    rw [MonoidHom.range_comp]
    rw [show ιA.range = J' from hrange]
  have hπk : π.ker ≤ Subgroup.center (ggU .PSL (r + 1) f).K := by
    intro y hy
    exact hcent y (hφk hy)
  exact false_of_row_III_of_linear_cover hf π hπr hπk hrow

theorem fixedOrthBlockAt_of_binary_plus_selfDualTwo
    {X : Type} [Group X] {k : ℕ} {K J : Subgroup X}
    (φ : (ggU .POmegaPlus (k + 3) 1).K →* X)
    (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) 1).K)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 1))
      (LinearMap.toMatrix₂' (GaloisField 2 1)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 1)))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 4)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) 1).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) 1).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) 1).K)⁆)
    (hJmap : J'.map φ = J) : FixedOrthBlockAt K J := by
  have hcenter : Subgroup.center (ggU .POmegaPlus (k + 3) 1).K = ⊥ :=
    CFSG.SeitzReduction.OmegaPilot.center_spinGroup_quadPlus_eq_bot' (by omega)
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp
    (le_bot_iff.mp (hφk.trans (le_of_eq hcenter)))
  have hφK : ∀ u, φ u ∈ K := by
    intro u
    rw [← hφr]
    exact MonoidHom.mem_range.mpr ⟨u, rfl⟩
  let π : (ggU .POmegaPlus (k + 3) 1).K →* K := φ.codRestrict K hφK
  have hπbij : Function.Bijective π := by
    constructor
    · intro u v huv
      exact hφinj (congrArg Subtype.val huv)
    · intro v
      have hv : (v : X) ∈ φ.range := by rw [hφr]; exact v.2
      obtain ⟨u, hu⟩ := hv
      exact ⟨u, Subtype.ext hu⟩
  let η₀ : (ggU .POmegaPlus (k + 3) 1).K ≃* K := MulEquiv.ofBijective π hπbij
  let η : K ≃* spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 1)) := η₀.symm
  have hJπ : J'.map π = J.subgroupOf K := by
    ext v
    constructor
    · rintro ⟨u, hu, huv⟩
      change (v : X) ∈ J
      rw [← hJmap]
      exact ⟨u, hu, congrArg Subtype.val huv⟩
    · intro hv
      change (v : X) ∈ J at hv
      rw [← hJmap] at hv
      obtain ⟨u, hu, huv⟩ := hv
      exact ⟨u, hu, Subtype.ext huv⟩
  have hcomp : η.toMonoidHom.comp π = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro u
    change η₀.symm (η₀ u) = u
    exact η₀.symm_apply_apply u
  have hJη : (J.subgroupOf K).map η.toMonoidHom = J' := by
    rw [← hJπ, Subgroup.map_map, hcomp]
    ext u
    constructor
    · rintro ⟨v, hv, hvu⟩
      exact hvu ▸ hv
    · intro hu
      exact ⟨u, hu, rfl⟩
  refine Or.inl ⟨k, η, S, e, hSU, hS, hodd, he, hadj, hdeg₁, hdeg₂, ?_⟩
  rw [hJη]
  exact hJe

theorem parameters_of_row_III_of_fixed_plus_block
    {X : Type} [Group X] [Finite X] {k f : ℕ} (hf : 1 ≤ f)
    (φ : (ggU .POmegaPlus (k + 3) f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
      e.mulVec x = x → e.mulVec y = y → Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
      Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]))
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hrow : GGSixRCKJRow .III (J'.map φ)) :
    f = 1 ∧ Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e)) = 6 ∧
      LieModel (↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) .PSU 4 2 1 := by
  classical
  obtain ⟨t', m, ι, _β₀, hcase, _hlong, hcenter, hrange, _hframe⟩ :=
    exists_blockModel_selfDual_POmegaPlus_explicit k f hf S hSU hS hodd he hadj hdeg hnm hJe
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  let φ' : ↥(spinGroup Q) →* X := φ
  let π : (ggU t' m f).K →* X := φ'.comp ι
  have hπrange : π.range = J'.map φ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨ι y, le_of_eq hrange (MonoidHom.mem_range.mpr ⟨y, rfl⟩), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp (le_of_eq hrange.symm hy)
      exact ⟨z, rfl⟩
  have hφ'k : φ'.ker ≤ Subgroup.center ↥(spinGroup Q) := hφk
  have hπker : π.ker ≤ Subgroup.center (ggU t' m f).K := by
    intro y hy
    apply hcenter
    apply hφ'k
    show φ' (ι y) = 1
    exact hy
  have hrowπ : GGSixRCKJRow .III π.range := by rw [hπrange]; exact hrow
  rcases hcase with ⟨htag, hm3, hfin⟩ | ⟨htag, hm2, _hfin4⟩
  · rcases htag with ht | ht
    · subst ht
      by_cases hm4 : 4 ≤ m
      · have hadm : StatedLieAdmissible .POmegaPlus m 2 f := ⟨Nat.prime_two, hf, hm4⟩
        have hmodel := irg_lieModel_quot (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          hadm π rfl hπker
        rcases (lieModel_parameters_of_row_III hrowπ hmodel).2 with ⟨hbad, -⟩ | ⟨hbad, -⟩
        all_goals cases hbad
      · obtain rfl : m = 3 := by omega
        let η : (ggU .POmegaPlus 3 f).K ≃* Matrix.SpecialLinearGroup (Fin 4)
            (GaloisField 2 f) :=
          CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        let ν : (ggU .PSL (3 + 1) f).K →* X := π.comp η.symm.toMonoidHom
        have hνr : ν.range = π.range := by
          ext x
          constructor
          · rintro ⟨v, rfl⟩
            exact ⟨η.symm v, rfl⟩
          · rintro ⟨u, rfl⟩
            exact ⟨η u, congrArg π (η.symm_apply_apply u)⟩
        have hνk : ν.ker ≤ Subgroup.center (ggU .PSL (3 + 1) f).K := by
          rw [show ν.ker = π.ker.map η.toMonoidHom from
            MonoidHom.ker_comp_mulEquiv π η.symm]
          exact (Subgroup.map_mono hπker).trans (le_of_eq (Subgroup.map_center_eq η))
        exact (false_of_row_III_of_linear_cover hf ν hνr hνk hrowπ).elim
    · subst ht
      by_cases hm4 : 4 ≤ m
      · have hadm : StatedLieAdmissible .POmegaMinus m 2 f := ⟨Nat.prime_two, hf, hm4⟩
        have hmodel := irg_lieModel_quot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
          hadm π rfl hπker
        rcases (lieModel_parameters_of_row_III hrowπ hmodel).2 with ⟨hbad, -⟩ | ⟨hbad, -⟩
        all_goals cases hbad
      · obtain rfl : m = 3 := by omega
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        let F := GaloisField 2 (g + 1)
        let E := GaloisField 2 (2 * (g + 1))
        have hcardF : Nat.card F = 2 ^ (g + 1) :=
          GaloisField.card (p := 2) (n := g + 1) (by omega)
        have hcardE : Nat.card E = (2 ^ (g + 1)) ^ 2 :=
          card_galoisField_two_mul 2 (g + 1) (by omega)
        obtain ⟨_, η, -⟩ := CFSG.RankThree.PartOne.CTP.SU4Even.exists_equiv_su_four_even
          (F := F) (K := E) (f := g + 1)
          (b := (minusCoeffs 2 (g + 1)).1) (c := (minusCoeffs 2 (g + 1)).2)
          hcardF hcardE (minusCoeffs_irr 2 (g + 1))
        let η' : (ggU .POmegaMinus 3 (g + 1)).K ≃* (ggU .PSU 4 (g + 1)).K := η
        let ν : (ggU .PSU 4 (g + 1)).K →* X := π.comp η'.symm.toMonoidHom
        have hνr : ν.range = π.range := by
          ext x
          constructor
          · rintro ⟨v, rfl⟩
            exact ⟨η'.symm v, rfl⟩
          · rintro ⟨u, rfl⟩
            exact ⟨η' u, congrArg π (η'.symm_apply_apply u)⟩
        have hνk : ν.ker ≤ Subgroup.center (ggU .PSU 4 (g + 1)).K := by
          rw [show ν.ker = π.ker.map η'.toMonoidHom from
            MonoidHom.ker_comp_mulEquiv π η'.symm]
          exact (Subgroup.map_mono hπker).trans (le_of_eq (Subgroup.map_center_eq η'))
        have hg := (parameters_of_row_III_of_unitary_cover (by omega) ν hνr hνk hrowπ).1
        obtain rfl : g = 0 := by omega
        have hadm : StatedLieAdmissible .PSU 4 2 (0 + 1) := by
          refine ⟨Nat.prime_two, by omega, by omega, ?_⟩
          norm_num
        have hmodel := irg_lieModel_quot (Or.inr (Or.inl rfl)) hadm ν
          (hνr.trans hπrange) hνk
        exact ⟨rfl, by omega, hmodel⟩
  · subst htag
    subst hm2
    exact (false_of_row_III_of_linear_cover (r := 1) hf π rfl hπker hrowπ).elim

theorem field_eq_one_of_row_III_of_native_plus_model
    {X : Type} [Group X] [Finite X] {p m g : ℕ} {K J B : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBab : IsElemAbelian p B) (hdB : d ∈ B)
    (hrank : p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B)
    (hg : 1 ≤ g) (φ : (ggU .POmegaPlus m g).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus m g).K)
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (ggU .POmegaPlus m g).D φ b)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) : g = 1 := by
  obtain ⟨k, rfl⟩ := rckPOmegaPlus_rank_of_component φ hφr hJ
  obtain ⟨s, hs, hsodd, ε, hε, J', hJ'comp, hJ'map⟩ :=
    rckF1_POmegaPlus hp hp2 (hBab.2 d hdB) hg φ hφr hφk (hdiag d hdB) hJ
  let j := Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 g))
  have hSU : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))),
      a ∈ j.range := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    exact ⟨s, ha.symm⟩
  have hS : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))),
      ∀ b ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl _
  have hoddS : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))),
      Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  have hrow' : GGSixRCKJRow .III (J'.map φ) := by rw [hJ'map]; exact hrow
  obtain ⟨e, he, heε, hcase⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaPlus k g _ hSU hS hε
  rcases hcase with rfl | ⟨hne, hpair, hεeq⟩
  · have hadj := hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))))) e < 2
    · have hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 g,
          e.mulVec x = x → e.mulVec y = y → Spin.quadPlus (k + 3) (GaloisField 2 g) x = 0 →
          Spin.quadPlus (k + 3) (GaloisField 2 g) y = 0 →
          QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 g)) x y = 0 →
          ¬ LinearIndependent (GaloisField 2 g) ![x, y]) := by
        intro hm4
        exact rckF_POmegaPlus_not_omegaFourMinus hp hp2 hBab hdB hrank φ hφk hdiag s hs
          he hadj hm4 (hJ'comp.1.trans (Subgroup.commutator_le_self _)) hJ'map
      exact (parameters_of_row_III_of_fixed_plus_block hg φ hφk _ hSU hS hoddS
        he hadj hdeg2 hnm hJ'comp hrow').1
    · by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 g)
          (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))))) e < 4
      · exact eq_one_of_row_III_of_selfDualTwo_plus_block hg φ hφk _ hSU hS hoddS
          he hadj (by omega) hdeg4 hJ'comp hrow'
      · have hFE := ggSixLSevenFieldExtCase_POmegaPlus (k + 3) (GaloisField 2 g) (by omega)
          g (GaloisField.card (p := 2) (n := g) (by omega)) φ hφk _ hSU hS hoddS
          hε hJ'comp he heε (Or.inl ⟨rfl, by omega⟩)
        exact (not_fieldExtCase_of_row_III hrow' hg hFE).elim
  · by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))))) e < 2
    · exact (false_of_row_III_of_dualPair_plus_block hg φ hφk (j s) ⟨s, rfl⟩ hsodd
        he hpair hεeq hdeg2 hJ'comp hrow').elim
    · have hFE := ggSixLSevenFieldExtCase_POmegaPlus (k + 3) (GaloisField 2 g) (by omega)
        g (GaloisField.card (p := 2) (n := g) (by omega)) φ hφk _ hSU hS hoddS
        hε hJ'comp he heε (Or.inr ⟨hne, by omega⟩)
      exact (not_fieldExtCase_of_row_III hrow' hg hFE).elim

theorem fixedOrthBlockAt_or_fixedSix_of_binary_plus_model
    {X : Type} [Group X] [Finite X] {p k : ℕ} {K J B : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBab : IsElemAbelian p B) (hdB : d ∈ B)
    (hrank : p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B)
    (φ : (ggU .POmegaPlus (k + 3) 1).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) 1).K)
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (ggU .POmegaPlus (k + 3) 1).D φ b)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) :
    FixedOrthBlockAt K J ∨
      ∃ (s : (ggU .POmegaPlus (k + 3) 1).K)
        (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 1)) (J' : Subgroup (ggU .POmegaPlus (k + 3) 1).K),
        Odd (orderOf (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)) s)) ∧
        IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1)
          (Units.val '' {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)) s})) e ∧
        formAdj (RingHom.id (GaloisField 2 1))
          (LinearMap.toMatrix₂' (GaloisField 2 1)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 1)))) e = e ∧
        blockDegree (Algebra.adjoin (GaloisField 2 1)
          (Units.val '' {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)) s})) e < 2 ∧
        IsComponentOf J'
          ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)))
              {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)) s} e :
                Subgroup (ggU .POmegaPlus (k + 3) 1).K),
            (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)))
              {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)) s} e :
                Subgroup (ggU .POmegaPlus (k + 3) 1).K)⁆ ∧
        J'.map φ = J ∧
        Module.finrank (GaloisField 2 1) (LinearMap.range (Matrix.toLin' e)) = 6 ∧
        LieModel (↥J ⧸ Subgroup.center ↥J) .PSU 4 2 1 := by
  classical
  obtain ⟨s, hs, hsodd, ε, hε, J', hJ'comp, hJ'map⟩ :=
    rckF1_POmegaPlus hp hp2 (hBab.2 d hdB) (by omega) φ hφr hφk (hdiag d hdB) hJ
  let j := Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))
  have hSU : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))),
      a ∈ j.range := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    exact ⟨s, ha.symm⟩
  have hS : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))),
      ∀ b ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl _
  have hoddS : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))),
      Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  have hrow' : GGSixRCKJRow .III (J'.map φ) := by rw [hJ'map]; exact hrow
  obtain ⟨e, he, heε, hcase⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaPlus k 1 _ hSU hS hε
  rcases hcase with rfl | ⟨hne, hpair, hεeq⟩
  · have hadj := hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 1)
        (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))))) e < 2
    · have hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 1,
          e.mulVec x = x → e.mulVec y = y → Spin.quadPlus (k + 3) (GaloisField 2 1) x = 0 →
          Spin.quadPlus (k + 3) (GaloisField 2 1) y = 0 →
          QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 1)) x y = 0 →
          ¬ LinearIndependent (GaloisField 2 1) ![x, y]) := by
        intro hm4
        exact rckF_POmegaPlus_not_omegaFourMinus hp hp2 hBab hdB hrank φ hφk hdiag s hs
          he hadj hm4 (hJ'comp.1.trans (Subgroup.commutator_le_self _)) hJ'map
      obtain ⟨_, hdim, hmodel⟩ := parameters_of_row_III_of_fixed_plus_block (by omega)
        φ hφk _ hSU hS hoddS he hadj hdeg2 hnm hJ'comp hrow'
      rw [hJ'map] at hmodel
      exact Or.inr ⟨s, e, J', hsodd, he, hadj, hdeg2, hJ'comp, hJ'map, hdim, hmodel⟩
    · by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 1)
          (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))))) e < 4
      · exact Or.inl (fixedOrthBlockAt_of_binary_plus_selfDualTwo φ hφr hφk
          _ hSU hS hoddS he hadj (by omega) hdeg4 hJ'comp hJ'map)
      · have hFE := ggSixLSevenFieldExtCase_POmegaPlus (k + 3) (GaloisField 2 1) (by omega)
          1 (GaloisField.card (p := 2) (n := 1) (by omega)) φ hφk _ hSU hS hoddS
          hε hJ'comp he heε (Or.inl ⟨rfl, by omega⟩)
        exact (not_fieldExtCase_of_row_III hrow' (by omega) hFE).elim
  · by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 1)
        (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))))) e < 2
    · exact (false_of_row_III_of_dualPair_plus_block (by omega) φ hφk (j s) ⟨s, rfl⟩ hsodd
        he hpair hεeq hdeg2 hJ'comp hrow').elim
    · have hFE := ggSixLSevenFieldExtCase_POmegaPlus (k + 3) (GaloisField 2 1) (by omega)
        1 (GaloisField.card (p := 2) (n := 1) (by omega)) φ hφk _ hSU hS hoddS
        hε hJ'comp he heε (Or.inr ⟨hne, by omega⟩)
      exact (not_fieldExtCase_of_row_III hrow' (by omega) hFE).elim

theorem omegaSixEmbed_of_binary_plus_fixed_block_eq
    {X : Type} [Group X] {k : ℕ} {K J : Subgroup X}
    (φ : (ggU .POmegaPlus (k + 3) 1).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) 1).K)
    (s : (ggU .POmegaPlus (k + 3) 1).K)
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1)
      (Units.val '' {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)) s})) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 1))
      (LinearMap.toMatrix₂' (GaloisField 2 1)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 1)))) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 1)
      (Units.val '' {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)) s})) e < 2)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) 1).K}
    (hJ'eq : J' = glBlockCentralizer
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)))
      {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)) s} e)
    (hJ'map : J'.map φ = J)
    (hdim : Module.finrank (GaloisField 2 1) (LinearMap.range (Matrix.toLin' e)) = 6) :
    OmegaSixEmbed K J := by
  let j := Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))
  have hse : (j s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
      (GaloisField 2 1)) * e = e := mul_eq_self_of_blockDegree_lt_two_gf2 he hdeg
  have hblock := blockOn_glBlockCentralizer_of_mul_eq_self j he hse
  have hact : (fun (u : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 1)))) v =>
      (j u : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 1)).mulVec v) =
      fun u v => Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 1)) u v := by
    funext u v
    exact Spin.spinMatrix_mulVec _ u v
  rw [hact, ← hJ'eq] at hblock
  have hQ : IsUnit (LinearMap.toMatrix₂' (GaloisField 2 1)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 1)))).det :=
    (Matrix.nondegenerate_iff_det_ne_zero.mp
      (LinearMap.BilinForm.Nondegenerate.toMatrix'
        (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 1)))).isUnit
  exact Or.inl ⟨k + 3, φ, LinearMap.range (Matrix.toLin' e),
    LinearMap.ker (Matrix.toLin' e), J', hφr, hφk, hblock, hJ'map,
    polar_eq_zero_of_formAdj_eq_self _ hQ he.2.1 hadj, hdim⟩

theorem positions_of_row_III_of_plus_modelID
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBab : IsElemAbelian p B) (hdB : d ∈ B)
    (hrank : p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B)
    (hmodel : RCKClassicalModelIDAt .POmegaPlus K B)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) :
    FixedOrthBlockAt K J ∨
      (LieModel (↥J ⧸ Subgroup.center ↥J) .PSU 4 2 1 ∧ OmegaSixEmbed K J) := by
  rcases hmodel with ⟨m, g, φ, hg, hφr, hφk, hdiag⟩
  obtain rfl : g = 1 := field_eq_one_of_row_III_of_native_plus_model
    hp hp2 hBab hdB hrank hg φ hφr hφk hdiag hJ hrow
  obtain ⟨k, rfl⟩ := rckPOmegaPlus_rank_of_component φ hφr hJ
  rcases fixedOrthBlockAt_or_fixedSix_of_binary_plus_model
    hp hp2 hBab hdB hrank φ hφr hφk hdiag hJ hrow with hOrth | hSix
  · exact Or.inl hOrth
  · obtain ⟨s, e, J', hsodd, he, hadj, hdeg, hJe, hJ'map, hdim, hJmodel⟩ := hSix
    let j := Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))
    have hSU : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))),
        a ∈ j.range := by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      exact ⟨s, ha.symm⟩
    have hS : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))),
        ∀ b ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))), Commute a b := by
      intro a ha b hb
      rw [Set.mem_singleton_iff] at ha hb
      subst a
      subst b
      exact Commute.refl _
    have hoddS : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))),
        Odd (orderOf a) := by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      exact hsodd
    have hJ'eq := eq_glBlockCentralizer_of_finrank_six_POmegaPlus
      _ hSU hS hoddS he hadj hdeg hJe hdim
    exact Or.inr ⟨hJmodel,
      omegaSixEmbed_of_binary_plus_fixed_block_eq φ hφr hφk s he hadj hdeg hJ'eq hJ'map hdim⟩

theorem k2At_of_row_III_of_plus_modelID :
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n : ℕ) (ψ : (ggU t n 1).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    GGSixRCKJRow .III J →
    GGPresentsG0 G₀ (ggU t n 1).D t n 1 ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    B₁ ≤ Subgroup.normalizer (J : Set X) →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D → p ^ 4 ≤ Nat.card B₁ →
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) →
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    ∀ (rb : ↥J ⧸ Subgroup.center ↥J) (Vb : Subgroup (↥J ⧸ Subgroup.center ↥J)),
      RCKK1Data rb Vb → RCKPosShort ↥J rb Vb →
      ∀ (V : Subgroup X) (r : ↥J), (r : X) ∈ V → V ≤ J → IsElemAbelian 2 V → Nat.card V = 4 →
        QuotientGroup.mk' (Subgroup.center ↥J) r = rb →
        (V.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)) = Vb →
        (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) →
        (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (J : Set X) →
          Y ≤ Subgroup.centralizer {(r : X)} →
          (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set X)) →
          ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set X),
            v * y * v⁻¹ * y⁻¹ = (r : X) ^ k * z) →
        ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X,
          IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) →
          J ≤ K → Odd (Nat.card (Subgroup.center ↥K)) → K ≠ J →
          (∀ (m : ℕ) (η : ↥K ≃* CFSG.Open.StatedSp m (GaloisField 2 1)),
            3 ≤ m → ¬ (∀ v ∈ (V.subgroupOf K).map η.toMonoidHom, v ≠ 1 →
              ∃ x y : Fin m ⊕ Fin m → GaloisField 2 1,
                spB m x y = 0 ∧ SpSiegel x y v)) →
          (LieModel (↥J ⧸ Subgroup.center ↥J) .PSU 4 2 1 → ¬ OmegaSixEmbed K J) →
          ¬ FixedSpBlockAt K J → ¬ FixedSUBlockAt K J → ¬ FixedOrthBlockAt K J →
          B₁ ≤ Subgroup.normalizer (K : Set X) →
          (∃ d ∈ D, d ∉ Subgroup.zpowers e ∧ IsComponentOf J (K ⊓ Subgroup.centralizer {d})) →
          (RCKRP.RCKClassicalTag t → ∃ s : StatedLieTag,
            RCKRP.RCKClassicalTag s ∧ s ≠ .PSU ∧ s ≠ .PSL ∧
              RCKRP.RCKClassicalModelIDAt s K B₁) →
          RCKRP.RCKClassicalModelIDAt .POmegaPlus K B₁ →
          K2At K V r := by
  intro X _ _ t n ψ p G₀ A B₁ D J L
    hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
    hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0 hExists hNotCent hCompL
    hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard hr_eq hVmap hConj hK1'
    e heD hene K hKcomp hJK hOddK hKJ hNoPure hNoOm hNoSp hNoSU hNoOrth hB1K hJd
    hModel hPlus
  obtain ⟨d, hdD, _, hJcomp⟩ := hJd
  have hBab : IsElemAbelian p B₁ := isElemAbelian_of_le hA hB1A
  have hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁ := by
    rw [hB1cap, hDcard, ← pow_add]
    exact hB1card
  have hr1 : (r : X) ≠ 1 := by
    intro hr1
    apply hK1.2.1
    rw [← hr_eq, show r = 1 from Subtype.ext hr1, map_one]
  have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hr1, hConj⟩
  have hCore : CoreCommAt J V (r : X) :=
    rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
  have hShort : ShortAt J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
  rcases positions_of_row_III_of_plus_modelID hprime hpne2 hBab (hDB1 hdD) hrank hPlus hJcomp hJrow with
    hOrth | ⟨hJ, hEmbed⟩
  · exact k2At_of_fixedOrthBlockAt hOrth hJK hFour hCore hShort
  · exact k2At_of_omegaSixEmbed_shortAt_psu_four hOddCenJ hOddK hFour hCore hJ hShort hEmbed

end CFSG.StandardType.RCKC1

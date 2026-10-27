module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubRed
import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubType
import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubPGL
import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubDet
import CFSG.RankThree.PartTwo.Sec14.Ronan148WSubField
import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddGlue
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.PSL2Table.BlocksProduct
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree slPi glPi Type123)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

theorem two_lt_of_modThree {π : Bool} {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hq2 : π = false → 2 < p ^ f) (hq : ModThree π (p ^ f)) : 2 < p ^ f := by
  cases π
  · exact hq2 rfl
  · change p ^ f % 3 = 1 at hq
    have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega

theorem subL3Ident148 : SubL3Ident148 := by
  intro X _ _ P K₀ p f₁ _ hf₁ hp3 hpf hK hKs hPe hP9 hinv hfaith hfix
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨σ', F, _, hF, hq2, ⟨ψ₀⟩, hiso, hcyc⟩ := exists_model_of_isLThreeEpsAt hf₁ hp3 hK
  have := hF.finite
  have hPfin : Finite ↥P := Nat.finite_of_card_ne_zero (by omega)
  have hfaith' : ∀ ε ∈ P, ε ≠ 1 → ¬ K₀ ≤ Sec4.autFix ε := fun ε hε hε1 hle =>
    hε1 (hfaith ε hε fun k hk => Sec4.mem_autFix.mp (hle hk))
  have hρ₀inj := restrictAut_injective hinv hfaith'
  set β : ↥P →* MulAut (projImage (slPi σ' 3 (p ^ f₁) F)) :=
    (MulAut.congr ψ₀).toMonoidHom.comp (restrictAut hinv) with hβ
  have hβapp : ∀ (σ : ↥P) (m : projImage (slPi σ' 3 (p ^ f₁) F)),
      β σ m = ψ₀ (restrictAut hinv σ (ψ₀.symm m)) := fun σ m => rfl
  have hβinj : Function.Injective β := (MulAut.congr ψ₀).injective.comp hρ₀inj
  have hP3 : ∀ σ : ↥P, σ ^ 3 = 1 := fun σ =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hPe.2 σ σ.2)
  have hPc : ∀ σ τ : ↥P, σ * τ = τ * σ := fun σ τ => hPe.1.is_comm.comm σ τ
  have hβ3 : ∀ σ : ↥P, β σ ^ 3 = 1 := fun σ => by rw [← map_pow, hP3, map_one]
  have hfixM : ∀ σ : ↥P, σ ≠ 1 → ∀ m : projImage (slPi σ' 3 (p ^ f₁) F), β σ m = m →
      m ^ p = 1 → m = 1 := by
    intro σ hσ m hm hmp
    have h1 : restrictAut hinv σ (ψ₀.symm m) = ψ₀.symm m := by
      have := congrArg ψ₀.symm hm
      rwa [hβapp, MulEquiv.symm_apply_apply] at this
    have h2 : (σ : MulAut X) ((ψ₀.symm m : ↥K₀) : X) = (ψ₀.symm m : ↥K₀) := by
      rw [← restrictAut_apply hinv σ (ψ₀.symm m)]
      exact congrArg Subtype.val h1
    have h3 : ((ψ₀.symm m : ↥K₀) : X) ^ p = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hmp, map_one, Subgroup.coe_one]
    have h4 := hfix σ σ.2 (fun h => hσ (Subtype.ext h)) _ (ψ₀.symm m).2 h2 h3
    have h5 : ψ₀.symm m = 1 := Subtype.ext h4
    rw [← ψ₀.apply_symm_apply m, h5, map_one]
  have hpgl : ∀ σ : ↥P, ∃ y ∈ glPi σ' 3 (p ^ f₁) F, ∀ m : projImage (slPi σ' 3 (p ^ f₁) F),
      (β σ m : ProjGenLinGroup (Fin 3) F) = pmk y * m * (pmk y)⁻¹ := by
    intro σ
    rcases Ronan148W.aut_pgl_or_fix hF hq2 hpf (β σ) (hβ3 σ) with h | ⟨m, hm1, hmp, hmfix⟩
    · exact h
    · by_cases hσ : σ = 1
      · refine ⟨1, one_mem _, fun m => ?_⟩
        rw [hσ, map_one, MulAut.one_apply, map_one, one_mul, inv_one, mul_one]
      · exact absurd (hfixM σ hσ m hmfix hmp) hm1
  choose y hyH hy using hpgl
  by_cases hq : ModThree σ' (p ^ f₁)
  ·
    rcases heis_or_pgl_of_modThree hF hq (two_lt_of_modThree hp hf₁ hq2 hq) hP9 hP3 hPc β hβinj
        y hyH hy hfixM with
      ⟨y₁, y₂, h1, hy₂, ⟨ζ, hζ1, hζ⟩, hy₁3, hy₂3, ⟨l₁, hl₁, hl₁y⟩, hcorr⟩ |
      ⟨y, s, hyH', hy3, hs, hsZ, hs3, hys, hcorr⟩
    ·
      left
      have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
          A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
        fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
      set x₁ : X := ((ψ₀.symm (Sec4.projOf _ ⟨l₁, hl₁⟩) : ↥K₀) : X) with hx₁
      set x₂ : X := ((ψ₀.symm (Sec4.projOf _ ⟨y₂, hy₂⟩) : ↥K₀) : X) with hx₂
      have hx₁K : x₁ ∈ K₀ := (ψ₀.symm _).2
      have hx₂K : x₂ ∈ K₀ := (ψ₀.symm _).2
      have he₁ : ((ψ₀ ⟨x₁, hx₁K⟩ : projImage (slPi σ' 3 (p ^ f₁) F)) :
          ProjGenLinGroup (Fin 3) F) = pmk y₁ := by
        rw [show (⟨x₁, hx₁K⟩ : ↥K₀) = ψ₀.symm (Sec4.projOf _ ⟨l₁, hl₁⟩) from rfl,
          MulEquiv.apply_symm_apply, Sec4.coe_projOf, hl₁y]
      have he₂ : ((ψ₀ ⟨x₂, hx₂K⟩ : projImage (slPi σ' 3 (p ^ f₁) F)) :
          ProjGenLinGroup (Fin 3) F) = pmk y₂ := by
        rw [show (⟨x₂, hx₂K⟩ : ↥K₀) = ψ₀.symm (Sec4.projOf _ ⟨y₂, hy₂⟩) from rfl,
          MulEquiv.apply_symm_apply, Sec4.coe_projOf]
      have hnotc : ∀ w : GL (Fin 3) F, pmk y₂ = pmk w → y₁ * w = w * y₁ → False := by
        intro w hw hcw
        obtain ⟨c, hc⟩ : w⁻¹ * y₂ ∈ StatedScalars (Fin 3) F := by
          rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, hw, inv_mul_cancel]
        have hy₂w : y₂ = w * GeneralLinearGroup.scalar (Fin 3) c := by
          rw [hc]
          group
        have h2 : y₁ * y₂ * y₁⁻¹ = y₂ := by
          rw [hy₂w]
          calc y₁ * (w * GeneralLinearGroup.scalar (Fin 3) c) * y₁⁻¹ =
              (y₁ * w) * (GeneralLinearGroup.scalar (Fin 3) c * y₁⁻¹) := by group
            _ = (w * y₁) * (y₁⁻¹ * GeneralLinearGroup.scalar (Fin 3) c) := by rw [hcw, hsc]
            _ = w * GeneralLinearGroup.scalar (Fin 3) c := by group
        rw [hζ] at h2
        apply hζ1
        have h3 : GeneralLinearGroup.scalar (Fin 3) ζ = 1 := by
          have := congrArg (fun v => v * y₂⁻¹) h2
          simpa using this
        have h4 := congrArg (fun v : GL (Fin 3) F => (v : Matrix (Fin 3) (Fin 3) F) 0 0) h3
        simp [GeneralLinearGroup.coe_scalar] at h4
        exact h4
      have hcomm : pmk y₁ * pmk y₂ = pmk y₂ * pmk y₁ := by
        have h2 : pmk y₁ * pmk y₂ * (pmk y₁)⁻¹ = pmk y₂ := by
          rw [← map_inv, ← map_mul, ← map_mul, hζ, map_mul,
            Sec4.mk_eq_one_iff_mem_statedScalars.mpr ⟨ζ, rfl⟩, one_mul]
        calc pmk y₁ * pmk y₂ = pmk y₁ * pmk y₂ * (pmk y₁)⁻¹ * pmk y₁ := by group
          _ = pmk y₂ * pmk y₁ := by rw [h2]
      have hy₁3' : pmk y₁ ^ 3 = 1 := by
        rw [← map_pow]
        exact Sec4.mk_eq_one_iff_mem_statedScalars.mpr hy₁3
      have hy₂3' : pmk y₂ ^ 3 = 1 := by
        rw [← map_pow]
        exact Sec4.mk_eq_one_iff_mem_statedScalars.mpr hy₂3
      have hψ : ∀ a b : ↥K₀, ((ψ₀ a : projImage (slPi σ' 3 (p ^ f₁) F)) :
          ProjGenLinGroup (Fin 3) F) = ψ₀ b → a = b := fun a b h =>
        ψ₀.injective (Subtype.ext h)
      have hx₁₂ : x₁ * x₂ = x₂ * x₁ := by
        have := hψ (⟨x₁, hx₁K⟩ * ⟨x₂, hx₂K⟩) (⟨x₂, hx₂K⟩ * ⟨x₁, hx₁K⟩) (by
          rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, he₁, he₂, hcomm])
        exact congrArg Subtype.val this
      have hx₁3 : x₁ ^ 3 = 1 := by
        have := hψ (⟨x₁, hx₁K⟩ ^ 3) 1 (by
          rw [map_pow, Subgroup.coe_pow, he₁, hy₁3', map_one, Subgroup.coe_one])
        exact congrArg Subtype.val this
      have hx₂3 : x₂ ^ 3 = 1 := by
        have := hψ (⟨x₂, hx₂K⟩ ^ 3) 1 (by
          rw [map_pow, Subgroup.coe_pow, he₂, hy₂3', map_one, Subgroup.coe_one])
        exact congrArg Subtype.val this
      have hx₁1 : x₁ ≠ 1 := by
        intro h
        have h2 : pmk y₁ = 1 := by
          rw [← he₁, show (⟨x₁, hx₁K⟩ : ↥K₀) = 1 from Subtype.ext h, map_one, Subgroup.coe_one]
        obtain ⟨c, hc⟩ := Sec4.mk_eq_one_iff_mem_statedScalars.mp h2
        exact hnotc y₂ rfl (by rw [← hc, ← hsc])
      have hx₂n : x₂ ∉ Subgroup.zpowers x₁ := by
        rintro ⟨t, ht⟩
        have h2 : pmk y₂ = pmk (y₁ ^ t) := by
          rw [← he₂, map_zpow, ← he₁]
          have : (⟨x₂, hx₂K⟩ : ↥K₀) = ⟨x₁, hx₁K⟩ ^ t := Subtype.ext (by
            rw [Subgroup.coe_zpow]
            exact ht.symm)
          rw [this, map_zpow, Subgroup.coe_zpow]
        exact hnotc (y₁ ^ t) h2 (Commute.self_zpow y₁ t).eq
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hE9 : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup X) = 9 :=
        Sec4.card_zpowers_sup_zpowers hx₂3 (orderOf_eq_prime hx₁3 hx₁1) hx₂n hx₁₂.symm
      obtain ⟨hEc, hE3⟩ := comm_exp_of_sup_zpowers hx₁₂ hx₁3 hx₂3
      have htrans := Sec4.transitive_of_heis_pair hF hq ψ₀ hx₁K hx₂K he₁ he₂ h1 hy₂ hζ1 hζ
      refine ⟨⟨p, f₁, inferInstance, hf₁, hiso hq⟩, Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂,
        sup_le (Subgroup.zpowers_le.mpr hx₁K) (Subgroup.zpowers_le.mpr hx₂K),
        ⟨⟨⟨fun u v => Subtype.ext (hEc u u.2 v v.2)⟩⟩, hE3⟩, hE9,
        fun a ha ha1 b hb hb1 => ?_, fun σ hσ => ?_⟩
      · obtain ⟨n, hn, hnab⟩ := htrans a ha ha1 b hb hb1
        exact ⟨n, (Subgroup.mem_inf.mp hn).1, (Subgroup.mem_inf.mp hn).2, hnab⟩
      · obtain ⟨i, j, hij⟩ := hcorr ⟨σ, hσ⟩
        set e' : ↥K₀ := (⟨x₁, hx₁K⟩ : ↥K₀) ^ i * (⟨x₂, hx₂K⟩ : ↥K₀) ^ j with he'
        refine ⟨(e' : X), ?_, fun k hk => ?_⟩
        · rw [he', Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow]
          exact mul_mem (zpow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) i)
            (zpow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) j)
        · have h2 := hij (ψ₀ ⟨k, hk⟩)
          rw [hβapp, MulEquiv.symm_apply_apply] at h2
          have he'c : ((ψ₀ e' : projImage (slPi σ' 3 (p ^ f₁) F)) : ProjGenLinGroup (Fin 3) F) =
              pmk y₁ ^ i * pmk y₂ ^ j := by
            rw [he', map_mul, map_zpow, map_zpow, Subgroup.coe_mul, Subgroup.coe_zpow,
              Subgroup.coe_zpow, he₁, he₂]
          have h3 := hψ (restrictAut hinv ⟨σ, hσ⟩ ⟨k, hk⟩) (e' * ⟨k, hk⟩ * e'⁻¹) (by
            rw [h2, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
              Subgroup.coe_inv, he'c])
          have h4 := congrArg Subtype.val h3
          rw [restrictAut_apply] at h4
          rw [h4, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    ·
      right
      left
      refine ⟨σ', p, f₁, F, inferInstance, hF, hq, ψ₀, y, s, hyH', hy3, hs, hsZ, hs3, hys, ?_⟩
      rintro τ ⟨σ, hσ, hστ⟩
      obtain ⟨i, j, hij⟩ := hcorr ⟨σ, hσ⟩
      refine ⟨i, j, fun z => ?_⟩
      have hτρ : τ = restrictAut hinv ⟨σ, hσ⟩ := by
        ext z
        exact (hστ z).trans (restrictAut_apply hinv ⟨σ, hσ⟩ z).symm
      have h2 := hij (ψ₀ z)
      rw [hβapp, MulEquiv.symm_apply_apply, ← hτρ] at h2
      exact h2
  ·
    exfalso
    have hinn : ∀ σ : ↥P, ∃ k : ↥K₀, restrictAut hinv σ = MulAut.conj k := by
      intro σ
      obtain ⟨l, hl, z, hlz⟩ := exists_slPi_mul_scalar_of_not_modThree hF hp3 hq (hyH σ)
      refine ⟨ψ₀.symm (Sec4.projOf _ ⟨l, hl⟩), MulEquiv.ext fun k => ?_⟩
      apply ψ₀.injective
      apply Subtype.ext
      have h1 := hy σ (ψ₀ k)
      rw [hβapp, MulEquiv.symm_apply_apply] at h1
      rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
        Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Sec4.coe_projOf, hlz, map_mul,
        Sec4.mk_eq_one_iff_mem_statedScalars.mpr ⟨z, rfl⟩, mul_one]
    exact false_of_inner_of_cyclic hKs (restrictAut hinv) hρ₀inj hP9 hP3 hinn (hcyc hq)

theorem subHeis148 : SubHeis148 :=
  subHeis148_of_subL3 subL3Ident148

end CFSG.RankThree.PartTwo.Sec14.Ronan148T

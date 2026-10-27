module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3Rank
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3ProofModel
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofAut
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofModels
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentMat
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentGen
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardMat
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.RankThree.PartTwo.Sec19.Step1915W
import CFSG.RankThree.PartTwo.Sec19.Step1917ProofDefs
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofSetup

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open Matrix

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem conj_injective_projImage (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) :
    Function.Injective (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →*
      MulAut (projImage (slPi π 3 (p ^ f) K))) := by
  intro u v h
  have h1 : MulAut.conj (u * v⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  exact mul_inv_eq_one.mp (eq_one_of_conj_eq_one hK hq hq2 h1)

theorem card_hessian (hK : PiField π p f K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hdS : diagTau hτ ∈ slPi π 3 (p ^ f) K)
    (hcS : (cycThree : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K) :
    Nat.card (Subgroup.zpowers (projOf (slPi π 3 (p ^ f) K) ⟨diagTau hτ, hdS⟩) ⊔
      Subgroup.zpowers (projOf (slPi π 3 (p ^ f) K) ⟨cycThree, hcS⟩) :
        Subgroup (projImage (slPi π 3 (p ^ f) K))) = 9 := by
  have := hK.finite
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set d := diagTau hτ with hd_def
  set c := (cycThree : GL (Fin 3) K) with hc_def
  set x₁ := projOf (slPi π 3 (p ^ f) K) ⟨d, hdS⟩ with hx₁
  set x₂ := projOf (slPi π 3 (p ^ f) K) ⟨c, hcS⟩ with hx₂
  have cx₁ : (x₁ : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk d := rfl
  have cx₂ : (x₂ : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk c := rfl
  have hd3 : d ^ 3 = 1 := diagTau_pow_three hτ
  have hc3 : c ^ 3 = 1 := cycThree_pow_three
  have hx12 : x₁ * x₂ = x₂ * x₁ := Subtype.ext (by
    simp only [Subgroup.coe_mul, cx₁, cx₂]
    exact mk_diagTau_cycThree hτ)
  have hx13 : x₁ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, cx₁, ← map_pow, hd3, map_one, Subgroup.coe_one])
  have hx23 : x₂ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, cx₂, ← map_pow, hc3, map_one, Subgroup.coe_one])
  have hx1 : x₁ ≠ 1 := by
    intro h1
    have h2 : ProjGenLinGroup.mk d = 1 := congrArg Subtype.val h1
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨t, ht⟩ := h2
    have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) ht
    have e2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) ht
    simp only [coe_scalar_eq_smul, hd_def, coe_diagTau] at e0 e2
    simp at e0 e2
    rw [e2] at e0
    simp at e0
    exact hτ1 e0.symm
  have hx21 : x₂ ∉ Subgroup.zpowers x₁ := by
    intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : ProjGenLinGroup.mk (d ^ i) = ProjGenLinGroup.mk c := by
      rw [map_zpow]
      exact congrArg Subtype.val hi
    have h2 : ProjGenLinGroup.mk (c * (d ^ i)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨t, ht⟩ := h2
    have hdiag : d = diagHom (Units.mk0 τ hτ0, Units.mk0 τ hτ0 ^ 2, 1) := by
      rw [hd_def, diagTau_eq_diagUnits hτ hτ0]
      rfl
    have e11 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) ht
    rw [hdiag, ← map_zpow, ← map_inv, Units.val_mul, coe_diagHom, coe_scalar_eq_smul,
      hc_def, coe_cycThree] at e11
    simp [Matrix.mul_apply, Matrix.diagonal] at e11
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) (QuotientGroup.mk'_surjective _)
  exact card_zpowers_sup_zpowers hx23 (orderOf_eq_prime hx13 hx1) hx21 hx12.symm

theorem eq_pow_of_pow_three_eq_one {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hτ0 : τ ≠ 0)
    {μ : Kˣ} (hμ : μ ^ 3 = 1) :
    μ = Units.mk0 τ hτ0 ^ (2 * 0) ∨ μ = Units.mk0 τ hτ0 ^ (2 * 1) ∨
      μ = Units.mk0 τ hτ0 ^ (2 * 2) := by
  have hc3' : (μ : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hμ, Units.val_one]
  have hsum : τ ^ 2 + τ + 1 = 0 := by
    have : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hτ1)
  have hfac : ((μ : K) - 1) * ((μ : K) - τ ^ 2) * ((μ : K) - τ ^ 4) = 0 := by
    linear_combination hc3' + (-(μ : K) ^ 2 + τ ^ 2 * μ) * hsum +
      (-τ * (μ : K) ^ 2 + τ ^ 3 * μ - τ ^ 3 - 1) * hτ
  rcases mul_eq_zero.mp hfac with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · exact Or.inl (Units.ext (by simpa using sub_eq_zero.mp h1))
    · exact Or.inr (Or.inl (Units.ext (by simpa using sub_eq_zero.mp h2)))
  · exact Or.inr (Or.inr (Units.ext (by simpa using sub_eq_zero.mp h3)))

theorem exists_mk_diagUnits_eq_pow {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {a b c : Kˣ} {μ : Kˣ}
    (h : diagUnits a b c * cycThree * (diagUnits a b c)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) μ * cycThree) :
    ∃ j : ℕ, pmk (diagUnits a b c : GL (Fin 3) K) = pmk (diagTau hτ) ^ j := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set t := Units.mk0 τ hτ0 with ht
  have ht3 : t ^ 3 = 1 := Units.ext (by simp [ht, hτ])
  have h1 : diagUnits a b c * (cycThree * (diagUnits a b c)⁻¹ * cycThree⁻¹) =
      GeneralLinearGroup.scalar (Fin 3) μ := by
    rw [show diagUnits a b c * (cycThree * (diagUnits a b c)⁻¹ * cycThree⁻¹) =
        (diagUnits a b c * cycThree * (diagUnits a b c)⁻¹) * cycThree⁻¹ by group, h,
      mul_inv_cancel_right]
  rw [Sec12.KS128Move.diagUnits_inv, cycThree_conj_diagUnits, diagUnits_mul,
    Sec12.KS128Move.scalar_eq_diagUnits, Sec12.KS128Move.diagUnits_eq_iff] at h1
  obtain ⟨e1, e2, e3⟩ := h1
  have hμ3 : μ ^ 3 = 1 := by
    rw [show μ ^ 3 = μ * μ * μ by rw [pow_succ, pow_two]]
    nth_rewrite 1 [← e1]
    nth_rewrite 1 [← e2]
    rw [← e3]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    field_simp
  have hD : pmk (diagUnits a b c : GL (Fin 3) K) = pmk (diagUnits 1 μ (μ ^ 2)) := by
    refine (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mpr ⟨a⁻¹, mul_inv_cancel a, ?_, ?_⟩
    · rw [← e2]
    · rw [pow_two]
      nth_rewrite 1 [← e3]
      nth_rewrite 1 [← e2]
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
  rw [hD]
  have hdT : diagTau hτ = diagUnits t (t ^ 2) 1 := diagTau_eq_diagUnits hτ hτ0
  rcases eq_pow_of_pow_three_eq_one hτ hτ1 hτ0 hμ3 with h0 | h2 | h4
  · refine ⟨0, ?_⟩
    rw [h0, pow_zero, pow_zero, one_pow, Sec12.KS128Move.diagUnits_one, map_one]
  · refine ⟨2, ?_⟩
    rw [hdT, ← map_pow, Sec12.KS128Move.diagUnits_pow, h2]
    refine (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mpr ⟨t ^ 2, ?_, ?_, ?_⟩
    · rw [one_mul]
    · rw [← pow_add, ← pow_mul]
    · rw [← pow_mul, ← pow_add, one_pow]
      calc t ^ (2 * 1 * 2 + 2) = (t ^ 3) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [ht3, one_pow]
  · refine ⟨1, ?_⟩
    rw [hdT, pow_one, h4]
    refine (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mpr ⟨t, ?_, ?_, ?_⟩
    · rw [one_mul]
    · calc t ^ (2 * 2) * t = (t ^ 3) * t ^ 2 := by rw [← pow_succ, ← pow_add]
        _ = t ^ 2 := by rw [ht3, one_mul]
    · calc (t ^ (2 * 2)) ^ 2 * t = (t ^ 3) ^ 3 := by rw [← pow_mul, ← pow_succ, ← pow_mul]
        _ = 1 := by rw [ht3, one_pow]

theorem card_le_nine_of_isElemAbelian_mulAut_model (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8))
    {E : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K)))}
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  classical
  haveI : Fact p.Prime := ⟨hK.prime⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hK.finite
  haveI : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) (QuotientGroup.mk'_surjective _)
  haveI := finite_mulAut (projImage (slPi π 3 (p ^ f) K))
  have hf : 1 ≤ f := hK.one_le
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hiso : Sec4.IsoLThreePi (projImage (slPi π 3 (p ^ f) K)) p f :=
    Sec4.Item462AltProof.isoLThreePi_projImage_slPi hK hq
  have hfac := Sec13.Item138Proof.factorization_card_three_eq_two hf hiso h9
  have hOut : ¬ 9 ∣ Nat.card (Outer (projImage (slPi π 3 (p ^ f) K))) :=
    Sec19.Item19ResProof.not_nine_dvd_card_outer hf hiso (by omega) (fun h => h9 (Or.inl h))
      (fun h => h9 (Or.inr h))
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by rw [pow_one]; exact hE.2 g g.2)⟩
  have h27 := Sec19.Item19ResProof.card_le_of_isPGroup hfac hOut E hEp
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hk3 : k = 3 := by
    rw [hk] at hlt h27
    rcases (by omega : k ≤ 2 ∨ k = 3 ∨ 4 ≤ k) with h | h | h
    · have h' : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h
      norm_num at h'
      omega
    · exact h
    · have h' : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
      norm_num at h'
      omega
  have hE27 : Nat.card E = 27 := by rw [hk, hk3]; norm_num
  set Inn := CFSG.ComponentClassification.OuterAutomorphisms.inner
    (projImage (slPi π 3 (p ^ f) K)) with hInn
  set ψ : ↥E →* Outer (projImage (slPi π 3 (p ^ f) K)) := (QuotientGroup.mk' Inn).comp E.subtype with hψ
  have hker : ψ.ker = Inn.subgroupOf E := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (g : MulAut (projImage (slPi π 3 (p ^ f) K)))
  have hrange : Nat.card ψ.range ≤ 3 := by
    have hrange3 : IsPGroup 3 ψ.range :=
      hEp.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hrange3
    have hdvd : 3 ^ j ∣ Nat.card (Outer (projImage (slPi π 3 (p ^ f) K))) := hj ▸ Subgroup.card_subgroup_dvd_card ψ.range
    have hj1 : j ≤ 1 := by
      by_contra hj1
      push Not at hj1
      have h' := (Nat.pow_dvd_pow 3 hj1).trans hdvd
      norm_num at h'
      exact hOut h'
    rw [hj]
    calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
      _ = 3 := by norm_num
  have hcardE : Nat.card E = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, mul_comm]
  have hkerc : Nat.card ψ.ker = Nat.card (Inn ⊓ E : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K)))) := by
    rw [hker, ← Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  have hIE1 : 9 ≤ Nat.card (Inn ⊓ E : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K)))) := by
    rw [← hkerc]
    nlinarith [hcardE, hrange, hE27]
  have hIE2 : Nat.card (Inn ⊓ E : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K)))) ≤ 9 := by
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp (hEp.to_le (inf_le_right : Inn ⊓ E ≤ E))
    have h1 : Nat.card (Inn ⊓ E : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K)))) ∣ Nat.card (projImage (slPi π 3 (p ^ f) K)) :=
      (Subgroup.card_dvd_of_le inf_le_left).trans
        (Subgroup.card_range_dvd (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →* MulAut (projImage (slPi π 3 (p ^ f) K))))
    rw [hi] at h1 ⊢
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h1
    rw [hfac] at h2
    calc 3 ^ i ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      _ = 9 := by norm_num
  have hIE : Nat.card (Inn ⊓ E : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K)))) = 9 := le_antisymm hIE2 hIE1
  set S := (Inn ⊓ E).comap (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →* MulAut (projImage (slPi π 3 (p ^ f) K))) with hS
  have hSmap : S.map (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →* MulAut (projImage (slPi π 3 (p ^ f) K))) = Inn ⊓ E :=
    Subgroup.map_comap_eq_self inf_le_left
  have hS9 : Nat.card S = 9 := by
    rw [← hIE, ← hSmap, Subgroup.card_map_of_injective (conj_injective_projImage hK hq hq2)]
  have hSylS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by rw [hS9, Subgroup.card_top, hfac]; norm_num)
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hdS : diagTau hτ ∈ slPi π 3 (p ^ f) K := diagTau_mem_slPi hπ hq' hτ
  have hcS : (cycThree : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := cycThree_mem_slPi hπ
  set x₁ := projOf (slPi π 3 (p ^ f) K) ⟨diagTau hτ, hdS⟩ with hx₁
  set x₂ := projOf (slPi π 3 (p ^ f) K) ⟨cycThree, hcS⟩ with hx₂
  have hH9 := card_hessian hK hτ hτ1 hdS hcS
  have hSylH : CFSG.ABGLocalTools.IsSylowOf 3
      (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup (projImage (slPi π 3 (p ^ f) K))) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by rw [hH9, Subgroup.card_top, hfac]; norm_num)
  obtain ⟨n, -, hn⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hSylH hSylS
  obtain ⟨g, hgE, hgI⟩ : ∃ g ∈ E, g ∉ Inn := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Inn ⊓ E := fun x hx => ⟨hcon x hx, hx⟩
    have := Subgroup.card_le_of_le hle
    omega
  have hgS : ∀ s ∈ S, g s = s := by
    intro s hs
    have hsE : MulAut.conj s ∈ E := (Subgroup.mem_comap.mp hs).2
    have hcomm : g * MulAut.conj s = MulAut.conj s * g :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hgE⟩ ⟨_, hsE⟩)
    have h1 : MulAut.conj (g s) = MulAut.conj s := by
      rw [mulAut_conj_apply_eq, hcomm, mul_inv_cancel_right]
    exact conj_injective_projImage hK hq hq2 h1
  set g' : MulAut (projImage (slPi π 3 (p ^ f) K)) := (MulAut.conj n)⁻¹ * g * MulAut.conj n with hg'
  have hg'H : ∀ h ∈ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup (projImage (slPi π 3 (p ^ f) K))), g' h = h := by
    intro h hh
    have hS' : (MulAut.conj n) h ∈ S := by
      rw [hn]
      exact ⟨h, hh, rfl⟩
    rw [hg', MulAut.mul_apply, MulAut.mul_apply, hgS _ hS', MulAut.inv_apply_self]
  have hg'I : g' ∉ Inn := by
    intro hI
    apply hgI
    have hc : MulAut.conj n ∈ Inn := ⟨n, rfl⟩
    have hgg : g = MulAut.conj n * g' * (MulAut.conj n)⁻¹ := by rw [hg']; group
    rw [hgg]
    exact Inn.mul_mem (Inn.mul_mem hc hI) (Inn.inv_mem hc)
  have hg'3 : g' ^ 3 = 1 := by
    have hg3 : g ^ 3 = 1 := hE.2 g hgE
    rw [hg', show (MulAut.conj n)⁻¹ * g * MulAut.conj n =
        (MulAut.conj n)⁻¹ * g * ((MulAut.conj n)⁻¹)⁻¹ by rw [inv_inv], _root_.conj_pow, hg3,
      mul_one, mul_inv_cancel]
  rcases Sec11.KS11LieProof.aut_pgl_or_field hK hq2 g' hg'3 with ⟨y, -, hy⟩ | ⟨f₀, hf₀, -⟩
  swap
  · have h3 : p ^ f % 3 ≠ 0 := by
      cases π
      · change p ^ f % 3 = 2 at hq
        rw [hq]
        decide
      · change p ^ f % 3 = 1 at hq
        rw [hq]
        decide
    exact Sec19.Item19ResProof.not_three_dvd_of_mod_nine h3 (fun h => h9 (Or.inl h))
      (fun h => h9 (Or.inr h)) ⟨f₀, hf₀⟩
  have hfix₁ : g' x₁ = x₁ := hg'H x₁ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁))
  have hfix₂ : g' x₂ = x₂ := hg'H x₂ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂))
  obtain ⟨μ₁, hμ₁⟩ := exists_conj_eq_scalar_mul hy hfix₁ (d := diagTau hτ) rfl
  obtain ⟨a, b, c', k', -, hyeq⟩ := monomial_of_conj_diagTau hτ hτ1 hμ₁
  obtain ⟨μ, hμ⟩ := exists_conj_eq_scalar_mul hy hfix₂ (d := cycThree) rfl
  have hDc : diagUnits a b c' * cycThree * (diagUnits a b c')⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) μ * cycThree := by
    rw [← hμ, hyeq]
    group
  obtain ⟨j, hj⟩ := exists_mk_diagUnits_eq_pow hτ hτ1 hDc
  have hpy : pmk y = ((x₁ ^ j * x₂ ^ k' : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) := by
    rw [hyeq, map_mul, map_pow, hj, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    rfl
  apply hg'I
  refine ⟨x₁ ^ j * x₂ ^ k', MulEquiv.ext fun m => Subtype.ext ?_⟩
  rw [MulAut.conj_apply, hy m, hpy]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem card_le_nine_of_isElemAbelian_mulAut {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) (hq2 : 2 < p ^ e)
    (h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)) {E : Subgroup (MulAut X)}
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  have h := card_le_nine_of_isElemAbelian_mulAut_model hK hq hq2 h9
    (E := E.map (MulAut.congr φ).toMonoidHom) (isElemAbelian_map _ hE)
  rwa [Subgroup.card_map_of_injective (MulAut.congr φ).injective] at h

end CFSG.RankThree.PartTwo.Sec14.Ronan148W

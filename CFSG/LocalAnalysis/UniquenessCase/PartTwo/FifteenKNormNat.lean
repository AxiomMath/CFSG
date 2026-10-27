module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormOmPlus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormOmMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormSym
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormKlein
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLRep
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeSym4
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Adapters.RankTwoModelTransports
  CFSG.HardMathSupport.Solomon.Coordinator

private theorem s15k_norm_field_two {K : Type} [Field K] [Finite K] (hcard : Nat.card K = 2 ^ 1) :
    Nonempty (K ≃+* ZMod 2) := by
  have hK2 : Nat.card K = 2 := by simpa using hcard
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  exact ⟨(ZMod.ringEquivOfPrime K Nat.prime_two hK').symm⟩

private theorem s15k_norm_bc_eq_one {K : Type} [Field K] (e : K ≃+* ZMod 2) {b c : K}
    (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : e b = 1 ∧ e c = 1 := by
  have hpoly' : ∀ t : ZMod 2, t ^ 2 + e b * t + e c ≠ 0 := by
    intro t h0
    apply hpoly (e.symm t)
    apply e.injective
    simpa using h0
  have h0 := hpoly' 0
  have h1 := hpoly' 1
  generalize e b = x at h0 h1 ⊢
  generalize e c = y at h0 h1 ⊢
  revert x y
  decide

private theorem s15k_norm_card_eq {W : Type} [CommGroup W] {D : FFModel}
    {J : Subgroup (MulAut W)} {R : Subgroup W} (h : D.Realizes J R ⊥) (hker : D.ker = ⊥) :
    Nat.card R = Nat.card D.sec := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hker' : D.ker.subgroupOf D.sec = ⊥ := by rw [hker, Subgroup.bot_subgroupOf]
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)]
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker').trans
    QuotientGroup.quotientBot).toEquiv

private theorem s15k_norm_core_card_three : Nat.card (G6.coreMod 3) = 4 := by
  show Nat.card {x : G6.PermMod 3 // ∑ i, Multiplicative.toAdd x i = 0} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem s15k_norm_ker_three : (FFModel.symDn 3).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 3) ⊓ G6.coreMod 3 = ⊥
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz1
  have hsq : G6.allOnes 3 * G6.allOnes 3 = 1 := by decide +kernel
  have hnot : G6.allOnes 3 ∉ G6.coreMod 3 := by
    rw [G6.mem_coreMod]
    decide +kernel
  have hord : orderOf (G6.allOnes 3) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) (by decide +kernel)
  have hmod := zpow_mod_orderOf (G6.allOnes 3) k
  rw [hord] at hmod
  simp only [Nat.cast_ofNat] at hmod
  rw [← hmod]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]
  · exfalso
    apply hnot
    rw [← hmod, h, zpow_one] at hz2
    exact hz2

private theorem s15k_norm_symDn3_faithful : (FFModel.symDn 3).Faithful := by
  have key : ∀ σ : Equiv.Perm (Fin 3), (∀ m : G6.PermMod 3, ∑ i, Multiplicative.toAdd m i = 0 →
      G6.permAct 3 σ m * m⁻¹ = 1) → σ = 1 := by
    decide +kernel
  intro σ hσ
  refine key σ fun m hm => ?_
  have h1 : G6.permAct 3 σ m * m⁻¹ ∈ Subgroup.zpowers (G6.allOnes 3) ⊓ G6.coreMod 3 := hσ m hm
  have h2 : Subgroup.zpowers (G6.allOnes 3) ⊓ G6.coreMod 3 = ⊥ := s15k_norm_ker_three
  rwa [h2, Subgroup.mem_bot] at h1

private theorem s15k_norm_sym_three_card {W : Type} [CommGroup W] {J : Subgroup (MulAut W)}
    {R : Subgroup W} (h : SymmetricNatural J R ⊥ 3) : Nat.card J = 6 ∧ Nat.card R = 4 := by
  have hR : Nat.card R = 4 := by
    rw [s15k_norm_card_eq h s15k_norm_ker_three]
    exact s15k_norm_core_card_three
  obtain ⟨π₁, hπ⟩ := h
  let π : Equiv.Perm (Fin 3) →* ↥J := π₁
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on s15k_norm_symDn3_faithful hπ
  have hbij : Function.Bijective π := ⟨hinj, hπ.1⟩
  refine ⟨?_, hR⟩
  rw [← Nat.card_congr (Equiv.ofBijective π hbij), Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  rfl

theorem rNormNat153_holds : RNormNat153 := by
  intro W _ _ hW J R hJR hst hfaith x hx hxJ
  rcases hJR with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨m, hm, h⟩
  · obtain ⟨K, hF, hfin, hcard, hreal⟩ := h
    obtain ⟨e⟩ := s15k_norm_field_two hcard
    exact s15k_norm_nat_of_field e (glCongr_statedSL e n) (fun M _ => by
      rw [mclt_statedSL_eq_top]
      exact Subgroup.mem_top M) hreal hx hxJ
  · obtain ⟨-, K, hF, hfin, hcard, hreal⟩ := h
    obtain ⟨e⟩ := s15k_norm_field_two hcard
    exact s15k_norm_nat_of_field e (glCongr_statedSp e (n / 2))
      (fun M hM => s15k_norm_sp_zmod2 (n / 2) M hM) hreal hx hxJ
  · obtain ⟨-, K, hF, hfin, hcard, hreal⟩ := h
    obtain ⟨e⟩ := s15k_norm_field_two hcard
    have hmap : (CFSG.MatrixModel.isometryCore (StatedQuadPlus (n / 2) K)).map
        (glCongr (ι := Fin (n / 2) ⊕ Fin (n / 2)) e).toMonoidHom =
        CFSG.MatrixModel.isometryCore (StatedQuadPlus (n / 2) (ZMod 2)) :=
      CFSG.ClassicalInvolution.Upgrade.map_closure_preserving
        (QK := StatedQuadPlus (n / 2) K) (QL := StatedQuadPlus (n / 2) (ZMod 2)) e
        (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp e v)
    exact s15k_norm_nat_of_field e hmap
      (fun M hM => s15k_norm_omplus_zmod2 (by omega) M hM) hreal hx hxJ
  · obtain ⟨-, K, hF, hfin, b, c, hcard, hpoly, hreal⟩ := h
    obtain ⟨e⟩ := s15k_norm_field_two hcard
    obtain ⟨hb, hc⟩ := s15k_norm_bc_eq_one e hpoly
    have hmap : (CFSG.MatrixModel.isometryCore (StatedQuadMinus (n / 2) K b c)).map
        (glCongr (ι := Fin (n / 2 - 1) ⊕ Fin (n / 2 - 1) ⊕ Fin 2) e).toMonoidHom =
        CFSG.MatrixModel.isometryCore (StatedQuadMinus (n / 2) (ZMod 2) 1 1) :=
      CFSG.ClassicalInvolution.Upgrade.map_closure_preserving
        (QK := StatedQuadMinus (n / 2) K b c) (QL := StatedQuadMinus (n / 2) (ZMod 2) 1 1) e
        (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp e hb hc v)
    exact s15k_norm_nat_of_field e hmap
      (fun M hM => s15k_norm_omminus_zmod2 (by omega) M hM) hreal hx hxJ
  · rcases Nat.lt_or_ge m 5 with h5 | h5
    · interval_cases m
      · obtain ⟨hJ, hR⟩ := s15k_norm_sym_three_card h
        exact s15k_norm_klein_six hst hR hJ hfaith hx
      · obtain ⟨hJ, hR⟩ := s15k_jp_sym4_card h hfaith
        exact s15k_norm_klein_six hst hR hJ hfaith hx
    · obtain ⟨D⟩ := s15k_mcl_nonempty hW hst hfaith
      exact s15k_norm_mcrep D (fun A hA => s15k_norm_sym_range h5 h D A hA) hx hxJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

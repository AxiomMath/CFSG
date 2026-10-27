module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeSym
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeS3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeSym4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeO4
import CFSG.Quasithin.Background.B5FinSp
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

private theorem s15k_jp_stab {W : Type} [CommGroup W] {D : FFModel} {J : Subgroup (MulAut W)}
    {R Z : Subgroup W} (h : D.Realizes J R Z) : ∀ j ∈ J, ∀ r ∈ R, j r ∈ R := by
  obtain ⟨π, -, -, -, hUinv, -⟩ := h
  exact fun j hj r hr => hUinv ⟨j, hj⟩ r hr

private theorem s15k_jp_card_eq {W : Type} [CommGroup W] {D : FFModel}
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

private theorem s15k_jp_core_card_three : Nat.card (G6.coreMod 3) = 4 := by
  show Nat.card {x : G6.PermMod 3 // ∑ i, Multiplicative.toAdd x i = 0} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem s15k_jp_ker_three : (FFModel.symDn 3).ker = ⊥ := by
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

private theorem s15k_jp_symDn3_faithful : (FFModel.symDn 3).Faithful := by
  have key : ∀ σ : Equiv.Perm (Fin 3), (∀ m : G6.PermMod 3, ∑ i, Multiplicative.toAdd m i = 0 →
      G6.permAct 3 σ m * m⁻¹ = 1) → σ = 1 := by
    decide +kernel
  intro σ hσ
  refine key σ fun m hm => ?_
  have h1 : G6.permAct 3 σ m * m⁻¹ ∈ Subgroup.zpowers (G6.allOnes 3) ⊓ G6.coreMod 3 := hσ m hm
  have h2 : Subgroup.zpowers (G6.allOnes 3) ⊓ G6.coreMod 3 = ⊥ := s15k_jp_ker_three
  rwa [h2, Subgroup.mem_bot] at h1

theorem s15k_jp_sym_three {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {J : Subgroup (MulAut W)} {R : Subgroup W} (h : SymmetricNatural J R ⊥ 3)
    (hfaith : ∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R := by
  have hst := s15k_jp_stab h
  have hR : Nat.card R = 4 := by
    rw [s15k_jp_card_eq h s15k_jp_ker_three]
    exact s15k_jp_core_card_three
  obtain ⟨π₁, hπ⟩ := h
  let π : Equiv.Perm (Fin 3) →* ↥J := π₁
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on s15k_jp_symDn3_faithful hπ
  have hbij : Function.Bijective π := ⟨hinj, hπ.1⟩
  have hJ : Nat.card J = 6 := by
    rw [← Nat.card_congr (Equiv.ofBijective π hbij), Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    rfl
  have h3 := s15k_jp_s3 hW hst hR hJ hfaith
  exact ⟨h3.1, Or.inr ⟨h3.2.1, h3.2.2⟩⟩

theorem s15k_jp_sym_four {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {J : Subgroup (MulAut W)} {R : Subgroup W} (h : SymmetricNatural J R ⊥ 4)
    (hfaith : ∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R := by
  have hst := s15k_jp_stab h
  obtain ⟨hJ, hR⟩ := s15k_jp_sym4_card h hfaith
  have h3 := s15k_jp_s3 hW hst hR hJ hfaith
  exact ⟨h3.1, Or.inr ⟨h3.2.1, h3.2.2⟩⟩

theorem s15k_jp_sym {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {J : Subgroup (MulAut W)} {R : Subgroup W} {m : ℕ} (hm : 3 ≤ m)
    (h : SymmetricNatural J R ⊥ m) (hfaith : ∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R := by
  rcases Nat.lt_or_ge m 5 with h5 | h5
  · interval_cases m
    · exact s15k_jp_sym_three hW h hfaith
    · exact s15k_jp_sym_four hW h hfaith
  · exact s15k_jp_sym_five h5 h

theorem s15k_jp_sl_two {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {J : Subgroup (MulAut W)} {R : Subgroup W} (h : BinaryNaturalSL J R ⊥ 2 1)
    (hfaith : ∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R := by
  obtain ⟨K, hF, hfin, hcard, hreal⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have hst := s15k_jp_stab hreal
  have hR : Nat.card R = 4 := by
    rw [s15k_jp_card_eq hreal rfl]
    show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))) = 4
    rw [Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (Fin 2 → K) ≃ (Fin 2 → K)), Nat.card_fun, hK2]
    simp
  obtain ⟨π₁, hπ⟩ := hreal
  let π : ↥(StatedSL 2 K) →* ↥J := π₁
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful (StatedSL 2 K)) hπ
  have hJ : Nat.card J = 6 := by
    rw [← Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩),
      CFSG.Open.StatedAPI.card_statedSL_two, hK2]
    norm_num
  have h3 := s15k_jp_s3 hW hst hR hJ hfaith
  exact ⟨h3.1, Or.inr ⟨h3.2.1, h3.2.2⟩⟩

theorem s15k_jp_sp_four {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (h : NatSpn J R ⊥ 4 1) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R := by
  obtain ⟨-, K, hF, hfin, hcard, hreal⟩ := h
  exact s15k_jp_sym_five (by norm_num)
    (B5FinSp.symmetricNatural_six_of_binaryNaturalSp4 ⟨K, hF, hfin, hcard, hreal⟩)

private theorem s15k_jp_bc_eq_one {K : Type} [Field K] (e : K ≃+* ZMod 2) {b c : K}
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

theorem s15k_jp_orth_minus_four {W : Type} [CommGroup W] {J : Subgroup (MulAut W)}
    {R : Subgroup W} (h : NatOrthMinus J R ⊥ 4 1) : SymmetricNatural J R ⊥ 5 := by
  obtain ⟨-, K, hF, hfin, b, c, hcard, hpoly, hreal⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  obtain ⟨hb, hc⟩ := s15k_jp_bc_eq_one e hpoly
  have hmap := CFSG.ClassicalInvolution.Upgrade.map_closure_preserving
    (QK := StatedQuadMinus 2 K b c) (QL := StatedQuadMinus 2 (ZMod 2) 1 1) e
    (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp e hb hc v)
  exact s15k_jp_o4minus_zmod (s15k_jp_nat_transport e hmap hreal)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

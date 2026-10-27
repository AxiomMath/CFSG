module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3F3U3Model
import CFSG.Quasithin.Vol2.Ch3Sec3NFa2L2Gen
import CFSG.Quasithin.Vol2.Ch10SecQ34NA
import CFSG.Quasithin.Vol2.Ch10SecD33E
import CFSG.Quasithin.Vol2.Ch11SecU1L3IX
import CFSG.CharacterTheory.PSL2Table.Partition
import CFSG.Dihedral.Glauberman.DicksonMaxStructure
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Core
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxSL2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCentralQuotient
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinDS
import CFSG.Quasithin.Background.C1PackS15212C
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F7TwoFix
import CFSG.Quasithin.Background.F918H5
import CFSG.Quasithin.Background.FFC4Tr2
import CFSG.Quasithin.Background.FLc3Out
import CFSG.Quasithin.Background.FLcP0Mat
import CFSG.Quasithin.Background.GoldschmidtS146RBend1
import CFSG.Quasithin.Background.HPairBridge
import CFSG.Quasithin.Background.JonesParshallSmallSL
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S152Y15
import CFSG.Quasithin.EmptyFaithful.S152Y19
import CFSG.Quasithin.EmptyFaithful.S153E59A
import CFSG.Quasithin.EmptyFaithful.SzN15Top
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.H13.QRCBenderPairModel
import CFSG.Quasithin.Vol2.Ch11SecCB51Trans
import CFSG.Quasithin.Vol2.Ch11SecU1L3IU
import CFSG.Quasithin.Vol2.Ch11SecU1L3IV
import CFSG.Quasithin.Vol2.Ch1EightFourChar2
import CFSG.Quasithin.Vol2.Ch3Sec3L2qCore
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
import CFSG.Quasithin.Vol2.Ch3T325D
import CFSG.Quasithin.Vol2.Ch3T325J
import CFSG.RankThree.CentralLiftU.UnitaryTriRoots
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.KS.PKit
import CFSG.RankThree.PartOne.KS.PKitLines
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S8.Statements
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.Sporadic.J4.QT2LocMain
import CFSG.Sporadic.J4.QT2LocRadMain
import CFSG.Sporadic.Schreier.MathieuOddCore
import CFSG.Sporadic.Schreier.TitsOuterTwo

public section

namespace CFSG.RankThree.PartTwo.Sec20.F3U3

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

section PSL2

variable {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]

theorem card_of_mulEquiv_psl2 (hp2 : p ≠ 2) (e : H ≃* PSL(2, ZMod p)) :
    Nat.card H = p * (p ^ 2 - 1) / 2 := by
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Quasithin.H13.NFa2.card_psl_two_zmod Fact.out hp2

private theorem mul_sq_sub_one_div_two (hp2 : p ≠ 2) :
    p * (p ^ 2 - 1) / 2 = p * ((p ^ 2 - 1) / 2) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h2 : 2 ∣ p ^ 2 - 1 := by
    obtain ⟨k, rfl⟩ := hodd
    exact ⟨2 * k * k + 2 * k, by ring_nf; omega⟩
  exact Nat.mul_div_assoc p h2

private theorem not_dvd_sq_sub_one_div_two : ¬ p ∣ (p ^ 2 - 1) / 2 := by
  rintro ⟨k, hk⟩
  have hp := (Fact.out : p.Prime)
  have hp2 : 2 ≤ p := hp.two_le
  have hsq : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have h1 : p ^ 2 = 2 * (p * k) + 1 ∨ p ^ 2 = 2 * (p * k) + 2 := by omega
  rcases h1 with h | h
  · have hd : p ∣ p ^ 2 - 2 * (p * k) :=
      Nat.dvd_sub (dvd_pow_self p two_ne_zero) ⟨2 * k, by ring⟩
    rw [h, Nat.add_sub_cancel_left] at hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
  · have hd : p ∣ p ^ 2 - 2 * (p * k) :=
      Nat.dvd_sub (dvd_pow_self p two_ne_zero) ⟨2 * k, by ring⟩
    rw [h, Nat.add_sub_cancel_left] at hd
    have hp2' : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    subst hp2'
    omega

theorem isPerfect_of_mulEquiv_psl2 (hp5 : 5 ≤ p) (e : H ≃* PSL(2, ZMod p)) :
    Group.IsPerfect H := by
  have := CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.isPerfect_psl2_zmod (p := p) hp5
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem nontrivial_of_mulEquiv_psl2 (hp5 : 5 ≤ p) (e : H ≃* PSL(2, ZMod p)) : Nontrivial H := by
  have : Finite H := Nat.finite_of_card_ne_zero (by
    rw [card_of_mulEquiv_psl2 (by omega) e, mul_sq_sub_one_div_two (by omega)]
    have : 0 < (p ^ 2 - 1) / 2 := by
      have : 25 ≤ p ^ 2 := by nlinarith
      omega
    exact (Nat.mul_pos (Fact.out : p.Prime).pos this).ne')
  rw [← Finite.one_lt_card_iff_nontrivial, card_of_mulEquiv_psl2 (by omega) e,
    mul_sq_sub_one_div_two (by omega)]
  have : 1 ≤ (p ^ 2 - 1) / 2 := by
    have : 25 ≤ p ^ 2 := by nlinarith
    omega
  nlinarith

theorem exists_orderOf_eq_of_mulEquiv_psl2 (hp2 : p ≠ 2) (e : H ≃* PSL(2, ZMod p)) :
    ∃ u : H, orderOf u = p := by
  have hc := card_of_mulEquiv_psl2 hp2 e
  rw [mul_sq_sub_one_div_two hp2] at hc
  have hpos : 0 < (p ^ 2 - 1) / 2 := by
    by_contra h0
    push Not at h0
    have h00 : (p ^ 2 - 1) / 2 = 0 := by omega
    exact not_dvd_sq_sub_one_div_two (p := p) (h00 ▸ dvd_zero p)
  have : Finite H := Nat.finite_of_card_ne_zero (by
    rw [hc]; exact (Nat.mul_pos (Fact.out : p.Prime).pos hpos).ne')
  exact exists_prime_orderOf_dvd_card' p (by rw [hc]; exact dvd_mul_right p _)

theorem not_sq_dvd_card_of_mulEquiv_psl2 (hp2 : p ≠ 2) (e : H ≃* PSL(2, ZMod p)) :
    ¬ p ^ 2 ∣ Nat.card H := by
  rw [card_of_mulEquiv_psl2 hp2 e, mul_sq_sub_one_div_two hp2]
  intro h
  exact not_dvd_sq_sub_one_div_two (p := p)
    (Nat.dvd_of_mul_dvd_mul_left (Fact.out : p.Prime).pos (by rw [← pow_two]; exact h))

theorem card_normalizer_of_mulEquiv_psl2 (hp2 : p ≠ 2) (e : H ≃* PSL(2, ZMod p))
    {S : Subgroup H} (hS : Nat.card S = p) :
    Nat.card (Subgroup.normalizer (S : Set H)) = p * (p - 1) / 2 := by
  classical
  have hp := (Fact.out : p.Prime)
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hF
  have hcardF : Fintype.card (ZMod p) = p := ZMod.card p
  have hnd := not_sq_dvd_card_of_mulEquiv_psl2 hp2 (MulEquiv.refl PSL(2, ZMod p))
  have key : ∀ T : Subgroup PSL(2, ZMod p), Nat.card T = p →
      ∃ P : Sylow p PSL(2, ZMod p), (P : Subgroup PSL(2, ZMod p)) = T := by
    intro T hT
    obtain ⟨P, hP⟩ := (IsPGroup.of_card (n := 1) (by rw [hT, pow_one])).exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hdvd : p ^ k ∣ Nat.card PSL(2, ZMod p) := hk ▸ Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      exact hnd ((pow_dvd_pow p hk2).trans hdvd)
    rw [hT, hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  have hU : Nat.card (CFSG.PSL2Table.unipotent (ZMod p)) = p := by
    rw [CFSG.PSL2Table.card_unipotent h2, hcardF]
  set S' : Subgroup PSL(2, ZMod p) := S.map e.toMonoidHom with hS'
  have hS'c : Nat.card S' = p := by
    rw [hS', Subgroup.card_map_of_injective e.injective, hS]
  obtain ⟨P₁, hP₁⟩ := key _ hU
  obtain ⟨P₂, hP₂⟩ := key _ hS'c
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ZMod p) P₁ P₂
  have hS'eq : S' = (CFSG.PSL2Table.unipotent (ZMod p)).map (MulAut.conj g).toMonoidHom := by
    rw [← hP₂, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP₁]
    rfl
  have hN : Subgroup.normalizer (S' : Set PSL(2, ZMod p)) =
      (CFSG.PSL2Table.borel (ZMod p)).map (MulAut.conj g).toMonoidHom := by
    rw [hS'eq, CFSG.Glauberman.Dickson.MaxStructure.normalizer_map_conj,
      CFSG.AGLEmbedding.normalizer_unipotent_eq_borel hF]
  have hB := CFSG.PSL2Table.card_borel h2 (F := ZMod p)
  rw [hcardF] at hB
  have hNc : Nat.card (Subgroup.normalizer (S : Set H)) =
      Nat.card (CFSG.PSL2Table.borel (ZMod p)) := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.map_equiv_normalizer_eq, ← hS', hN,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [hNc]
  have : Nat.card (CFSG.PSL2Table.borel (ZMod p)) = (p - 1) * p / 2 := by omega
  rw [this, mul_comm]

theorem exists_ne_card_eq_of_mulEquiv_psl2 (hp5 : 5 ≤ p) (e : H ≃* PSL(2, ZMod p))
    {S : Subgroup H} (hS : Nat.card S = p) :
    ∃ S' : Subgroup H, Nat.card S' = p ∧ S' ≠ S := by
  have hsimp := CFSG.Quasithin.Vol2.Ch10.SecD.isSimpleGroup_of_psl2 hp5 e
  by_contra hno
  push Not at hno
  have hnorm : S.Normal := ⟨fun n hn g => by
    have hc : Nat.card (S.map (MulAut.conj g).toMonoidHom) = p := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hS]
    have := hno _ hc
    rw [← this]
    exact ⟨n, hn, rfl⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
  · rw [h, Subgroup.card_bot] at hS
    exact (Fact.out : p.Prime).one_lt.ne' hS.symm
  · rw [h, Subgroup.card_top, card_of_mulEquiv_psl2 (by omega) e,
      mul_sq_sub_one_div_two (by omega)] at hS
    have : 2 ≤ (p ^ 2 - 1) / 2 := by
      have : 25 ≤ p ^ 2 := by nlinarith
      omega
    have : p * 2 ≤ p * ((p ^ 2 - 1) / 2) := Nat.mul_le_mul_left p this
    omega

theorem exists_two_involutions_of_mulEquiv_psl2 (hp5 : 5 ≤ p) (e : H ≃* PSL(2, ZMod p)) :
    ∃ t₁ t₂ : H, t₁ ≠ t₂ ∧ orderOf t₁ = 2 ∧ orderOf t₂ = 2 := by
  have hsimp := CFSG.Quasithin.Vol2.Ch10.SecD.isSimpleGroup_of_psl2 hp5 e
  have hc := card_of_mulEquiv_psl2 (by omega) e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card H := by
    rw [hc, mul_sq_sub_one_div_two (by omega)]
    apply dvd_mul_of_dvd_right
    have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    obtain ⟨k, rfl⟩ := hodd
    refine ⟨k * k + k, ?_⟩
    have : (2 * k + 1) ^ 2 - 1 = 2 * (2 * (k * k + k)) := by ring_nf; omega
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have : Finite H := Nat.finite_of_card_ne_zero (by
    rw [hc, mul_sq_sub_one_div_two (by omega)]
    have : 0 < (p ^ 2 - 1) / 2 := by
      have : 25 ≤ p ^ 2 := by nlinarith
      omega
    exact (Nat.mul_pos (Fact.out : p.Prime).pos this).ne')
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hZ : Subgroup.center H = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
    · exact h
    · exfalso
      have hP := isPerfect_of_mulEquiv_psl2 hp5 e
      have : Nontrivial H := nontrivial_of_mulEquiv_psl2 hp5 e
      have hcomm := (commutator_eq_bot_iff_center_eq_top H).2 h
      rw [Group.IsPerfect.commutator_eq_top] at hcomm
      exact top_ne_bot hcomm
  have ht1 : t ∉ Subgroup.center H := by
    rw [hZ, Subgroup.mem_bot]
    rintro rfl
    rw [orderOf_one] at ht
    norm_num at ht
  rw [Subgroup.mem_center_iff] at ht1
  push Not at ht1
  obtain ⟨h, hh⟩ := ht1
  refine ⟨t, h * t * h⁻¹, fun heq => hh ?_, ht, ?_⟩
  · calc h * t = h * t * h⁻¹ * h := by group
      _ = t * h := by rw [← heq]
  · rw [show h * t * h⁻¹ = MulAut.conj h t from rfl, MulEquiv.orderOf_eq, ht]

theorem exists_map_conj_eq_of_card_eq {G : Type*} [Group G] [Finite G]
    (hG : ¬ p ^ 2 ∣ Nat.card G) {S T : Subgroup G} (hS : Nat.card S = p) (hT : Nat.card T = p) :
    ∃ g : G, T = S.map (MulAut.conj g).toMonoidHom := by
  have key : ∀ T : Subgroup G, Nat.card T = p → ∃ P : Sylow p G, (P : Subgroup G) = T := by
    intro T hT
    obtain ⟨P, hP⟩ := (IsPGroup.of_card (n := 1) (by rw [hT, pow_one])).exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hdvd : p ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      exact hG ((pow_dvd_pow p hk2).trans hdvd)
    rw [hT, hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk1
      _ = p := pow_one p
  obtain ⟨P₁, hP₁⟩ := key S hS
  obtain ⟨P₂, hP₂⟩ := key T hT
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P₁ P₂
  refine ⟨h, ?_⟩
  rw [← hP₂, ← hh, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP₁]
  rfl

end PSL2

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p : ℕ} [Fact p.Prime]
  (hK : Nat.card K = p ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p)

private theorem map_conj_inv_map_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩

private theorem map_conj_map_conj {G : Type*} [Group G] (H : Subgroup G) (g h : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

include hK hfix in
theorem map_conj_zGroup_eq {g₁ g₂ : ProjectiveSpecialUnitaryMatrixGroup J}
    (h : g₁ • pinf J hJ = g₂ • pinf J hJ) :
    (zGroup J hJ).map (MulAut.conj g₁).toMonoidHom =
      (zGroup J hJ).map (MulAut.conj g₂).toMonoidHom := by
  have h1 : (g₂⁻¹ * g₁) • pinf J hJ = pinf J hJ := by rw [mul_smul, h, inv_smul_smul]
  have h2 := conj_zGroup_eq_of_smul_pinf J hJ hK hfix h1
  calc (zGroup J hJ).map (MulAut.conj g₁).toMonoidHom
      = (zGroup J hJ).map (MulAut.conj (g₂ * (g₂⁻¹ * g₁))).toMonoidHom := by
        rw [mul_inv_cancel_left]
    _ = ((zGroup J hJ).map (MulAut.conj (g₂⁻¹ * g₁)).toMonoidHom).map
          (MulAut.conj g₂).toMonoidHom := (map_conj_map_conj _ _ _).symm
    _ = (zGroup J hJ).map (MulAut.conj g₂).toMonoidHom := by rw [h2]

private theorem map_conj_one {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext x
  simp [MulAut.conj_apply]

private theorem card_map_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

include hK hfix in
private theorem card_le_of_conj_le (hp2 : p ≠ 2) {k : ProjectiveSpecialUnitaryMatrixGroup J}
    {N : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (h1 : (zGroup J hJ).map (MulAut.conj k).toMonoidHom ≤ N)
    (h2 : ((zGroup J hJ).map (MulAut.conj (weyl J hJ)).toMonoidHom).map
      (MulAut.conj k).toMonoidHom ≤ N) :
    p * (p ^ 2 - 1) ≤ Nat.card N ∧
      ∃ ι : SL(2, ZMod p) →* ProjectiveSpecialUnitaryMatrixGroup J, Function.Injective ι ∧
        ι.range.map (MulAut.conj k).toMonoidHom ≤ N := by
  obtain ⟨ι, hιinj, hιcl, -⟩ := exists_iotaSL2 J hJ hK hfix hp2
  have hle : ι.range.map (MulAut.conj k).toMonoidHom ≤ N := by
    refine (Subgroup.map_mono hιcl).trans ?_
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact h1 ⟨x, hx, rfl⟩
    · exact h2 ⟨x, hx, rfl⟩
  refine ⟨?_, ι, hιinj, hle⟩
  have hc : Nat.card (ι.range.map (MulAut.conj k).toMonoidHom) = p * (p ^ 2 - 1) := by
    rw [card_map_conj, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective hιinj, Subgroup.card_top,
      CFSG.Quasithin.Vol2.Ch10.SecB.C10P34.card_sl2_zmod]
  rw [← hc]
  exact Subgroup.card_le_of_le hle

include hK hfix in
theorem not_mem_conj_zGroup (hp5 : 5 ≤ p)
    {Ω : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (e : Ω ≃* PSL(2, ZMod p))
    {u : ProjectiveSpecialUnitaryMatrixGroup J} (huΩ : u ∈ Ω) (hu : orderOf u = p)
    (g : ProjectiveSpecialUnitaryMatrixGroup J) :
    u ∉ (zGroup J hJ).map (MulAut.conj g).toMonoidHom := by
  intro hug
  have hp2 : p ≠ 2 := by omega
  set S : Subgroup Ω := Subgroup.zpowers ⟨u, huΩ⟩ with hSdef
  have hS : Nat.card S = p := by rw [hSdef, Nat.card_zpowers, Subgroup.orderOf_mk, hu]
  obtain ⟨S', hS'c, hS'ne⟩ := exists_ne_card_eq_of_mulEquiv_psl2 hp5 e hS
  have : Finite Ω := Subtype.finite
  obtain ⟨h, hS'eq⟩ :=
    exists_map_conj_eq_of_card_eq (not_sq_dvd_card_of_mulEquiv_psl2 hp2 e) hS hS'c
  have hSZ : Subgroup.zpowers u = (zGroup J hJ).map (MulAut.conj g).toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hug) ?_
    rw [card_map_conj, card_zGroup J hJ hK hfix hp2, Nat.card_zpowers, hu]
  have hmapS : S.map Ω.subtype = Subgroup.zpowers u := by
    rw [hSdef, MonoidHom.map_zpowers]
    rfl
  have hmapS' : S'.map Ω.subtype =
      (zGroup J hJ).map (MulAut.conj ((h : ProjectiveSpecialUnitaryMatrixGroup J) * g)).toMonoidHom
      := by
    rw [hS'eq, Subgroup.map_map, ← map_conj_map_conj, ← hSZ, ← hmapS, Subgroup.map_map]
    congr 1
  have hQ : g • pinf J hJ ≠ ((h : ProjectiveSpecialUnitaryMatrixGroup J) * g) • pinf J hJ := by
    intro hQ
    apply hS'ne
    apply Subgroup.map_injective Ω.subtype_injective
    rw [hmapS', hmapS, hSZ]
    exact (map_conj_zGroup_eq J hJ hK hfix hQ).symm
  obtain ⟨k, hk1, hk2⟩ := (MulAction.is_two_pretransitive_iff.mp
    (isMultiplyPretransitive_two J hJ p hK hfix)) (pinf_ne_pzero J hJ) hQ
  have hZk : (zGroup J hJ).map (MulAut.conj k).toMonoidHom ≤ Ω := by
    rw [map_conj_zGroup_eq J hJ hK hfix hk1, ← hSZ]
    exact Subgroup.zpowers_le.mpr huΩ
  have hZwk : ((zGroup J hJ).map (MulAut.conj (weyl J hJ)).toMonoidHom).map
      (MulAut.conj k).toMonoidHom ≤ Ω := by
    rw [map_conj_map_conj, map_conj_zGroup_eq J hJ hK hfix
      (show (k * weyl J hJ) • pinf J hJ = ((h : ProjectiveSpecialUnitaryMatrixGroup J) * g) •
        pinf J hJ by rw [mul_smul, weyl_smul_pinf, hk2]), ← hmapS']
    exact Subgroup.map_subtype_le S'
  have hcard := (card_le_of_conj_le J hJ hK hfix hp2 hZk hZwk).1
  rw [card_of_mulEquiv_psl2 hp2 e] at hcard
  have hpos : 0 < p * (p ^ 2 - 1) := by
    have : 25 ≤ p ^ 2 := by nlinarith
    exact Nat.mul_pos (by omega) (by omega)
  have := Nat.div_le_self (p * (p ^ 2 - 1)) 2
  omega

include hK hfix in
theorem eq_top_of_conj_zGroup_le (hp5 : 5 ≤ p) (hp3 : p % 3 = 1)
    {Ω M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (e : Ω ≃* PSL(2, ZMod p))
    (hΩM : Ω ≤ M) {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hZ : (zGroup J hJ).map (MulAut.conj g).toMonoidHom ≤ M) : M = ⊤ := by
  have hp2 : p ≠ 2 := by omega
  have hP := isPerfect_of_mulEquiv_psl2 hp5 e
  have hnt := nontrivial_of_mulEquiv_psl2 hp5 e
  set 𝒬 : Set (IsoPoint J) := {Q | ∃ g' : ProjectiveSpecialUnitaryMatrixGroup J,
    g' • pinf J hJ = Q ∧ (zGroup J hJ).map (MulAut.conj g').toMonoidHom ≤ M} with h𝒬
  have hmem : ∀ g' : ProjectiveSpecialUnitaryMatrixGroup J,
      g' • pinf J hJ ∈ 𝒬 ↔ (zGroup J hJ).map (MulAut.conj g').toMonoidHom ≤ M := by
    intro g'
    constructor
    · rintro ⟨g'', hg'', hle⟩
      rwa [← map_conj_zGroup_eq J hJ hK hfix hg'']
    · exact fun h => ⟨g', rfl, h⟩
  have h𝒬inv : ∀ m ∈ M, ∀ Q ∈ 𝒬, m • Q ∈ 𝒬 := by
    rintro m hm Q ⟨g', rfl, hg'⟩
    rw [← mul_smul, hmem, ← map_conj_map_conj]
    rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hg' hy)) (M.inv_mem hm)
  have hQ0 : g • pinf J hJ ∈ 𝒬 := ⟨g, rfl, hZ⟩
  obtain ⟨Q₁, hQ₁, hne⟩ : ∃ Q₁ ∈ 𝒬, Q₁ ≠ g • pinf J hJ := by
    by_contra hno
    push Not at hno
    have hΩstab : Ω ≤ MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
        (g • pinf J hJ) := fun x hx => hno _ (h𝒬inv x (hΩM hx) _ hQ0)
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj] at hΩstab
    have hΩ' : Ω.map (MulAut.conj g⁻¹).toMonoidHom ≤
        MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
      rw [← map_conj_inv_map_conj (MulAction.stabilizer _ (pinf J hJ)) g]
      exact Subgroup.map_mono hΩstab
    have : Group.IsSolvable
        (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)) :=
      isSolvable_stabilizer_pinf J hJ hK hfix
    have : Group.IsSolvable ↥(Ω.map (MulAut.conj g⁻¹).toMonoidHom) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hΩ')
    have : Group.IsSolvable Ω := Group.isSolvable_of_isSolvable_injective
      (f := (Ω.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).toMonoidHom)
      (Ω.equivMapOfInjective _ (MulAut.conj g⁻¹).injective).injective
    exact Group.IsPerfect.not_isSolvable Ω this
  obtain ⟨g₁, rfl, hg₁⟩ := hQ₁
  obtain ⟨k, hk1, hk2⟩ := (MulAction.is_two_pretransitive_iff.mp
    (isMultiplyPretransitive_two J hJ p hK hfix)) (pinf_ne_pzero J hJ) hne.symm
  have hZk : (zGroup J hJ).map (MulAut.conj k).toMonoidHom ≤ M := by
    rw [map_conj_zGroup_eq J hJ hK hfix hk1]
    exact hZ
  have hZwk : ((zGroup J hJ).map (MulAut.conj (weyl J hJ)).toMonoidHom).map
      (MulAut.conj k).toMonoidHom ≤ M := by
    rw [map_conj_map_conj, ← hmem, mul_smul, weyl_smul_pinf, hk2]
    exact ⟨g₁, rfl, hg₁⟩
  obtain ⟨ι, hιinj, hιcl, hιbl, hιoff, hιpres, -⟩ := exists_iotaSL2 J hJ hK hfix hp2
  have hιM : ∀ s ∈ ι.range, k * s * k⁻¹ ∈ M := by
    intro s hs
    have hcl : ι.range.map (MulAut.conj k).toMonoidHom ≤ M := by
      refine (Subgroup.map_mono hιcl).trans ?_
      rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro x (hx | hx)
      · exact hZk ⟨x, hx, rfl⟩
      · exact hZwk ⟨x, hx, rfl⟩
    exact hcl ⟨s, hs, rfl⟩
  have hbl𝒬 : ∀ x ∈ blockW J, k • x ∈ 𝒬 := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := hιbl x hx
    have : k • s • pinf J hJ = (k * s * k⁻¹) • (k • pinf J hJ) := by
      rw [← mul_smul, ← mul_smul, inv_mul_cancel_right]
    rw [this]
    exact h𝒬inv _ (hιM s hs) _ (hk1 ▸ hQ0)
  by_cases hoff : ∃ R : IsoPoint J, R ∉ blockW J ∧ k • R ∈ 𝒬
  ·
    obtain ⟨R, hRW, hRQ⟩ := hoff
    have hall : ∀ x : IsoPoint J, x ∈ 𝒬 := by
      intro x
      have hx' : x = k • (k⁻¹ • x) := by rw [smul_inv_smul]
      rw [hx']
      by_cases hxW : k⁻¹ • x ∈ blockW J
      · exact hbl𝒬 _ hxW
      · obtain ⟨s, hs, hsx⟩ := hιoff R (k⁻¹ • x) hRW hxW
        have : k • (k⁻¹ • x) = (k * s * k⁻¹) • (k • R) := by
          rw [← hsx, ← mul_smul, ← mul_smul, inv_mul_cancel_right]
        rw [this]
        exact h𝒬inv _ (hιM s hs) _ hRQ
    have hnc : Subgroup.normalClosure ((zGroup J hJ : Subgroup _) :
        Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ M := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro x hx
      obtain ⟨a, ha, h⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp h
      exact (hmem c).mp (hall _) ⟨a, ha, rfl⟩
    have hsimp := isSimpleGroup_psu J p hK hfix (by have := (Fact.out : p.Prime).two_le; omega)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure
      ((zGroup J hJ : Subgroup _) : Set (ProjectiveSpecialUnitaryMatrixGroup J))) with h | h
    · exfalso
      have hZbot : zGroup J hJ = ⊥ := eq_bot_iff.mpr (h ▸ Subgroup.le_normalClosure)
      have := card_zGroup J hJ hK hfix hp2
      rw [hZbot, Subgroup.card_bot] at this
      exact (Fact.out : p.Prime).one_lt.ne' this.symm
    · exact eq_top_iff.mpr (h ▸ hnc)
  ·
    push Not at hoff
    exfalso
    set Ω' := Ω.map (MulAut.conj k⁻¹).toMonoidHom with hΩ'
    have hP' : Group.IsPerfect Ω' := Group.IsPerfect.map (H := Ω) (MulAut.conj k⁻¹).toMonoidHom
    obtain ⟨t₁, t₂, ht, ho₁, ho₂⟩ := exists_two_involutions_of_mulEquiv_psl2 hp5 e
    refine false_of_isPerfect_of_stabilizes_blockW J hJ hK hfix hp2 hp3 hP'
      (t₁ := k⁻¹ * t₁ * k⁻¹⁻¹) (t₂ := k⁻¹ * t₂ * k⁻¹⁻¹) ⟨t₁, t₁.2, rfl⟩ ⟨t₂, t₂.2, rfl⟩ ?_ ?_ ?_ ?_
    · intro h
      apply ht
      apply Subtype.ext
      simpa using h
    · rw [show k⁻¹ * (t₁ : ProjectiveSpecialUnitaryMatrixGroup J) * k⁻¹⁻¹ =
        MulAut.conj k⁻¹ (t₁ : ProjectiveSpecialUnitaryMatrixGroup J) from rfl,
        MulEquiv.orderOf_eq, Subgroup.orderOf_coe, ho₁]
    · rw [show k⁻¹ * (t₂ : ProjectiveSpecialUnitaryMatrixGroup J) * k⁻¹⁻¹ =
        MulAut.conj k⁻¹ (t₂ : ProjectiveSpecialUnitaryMatrixGroup J) from rfl,
        MulEquiv.orderOf_eq, Subgroup.orderOf_coe, ho₂]
    · rintro _ ⟨h, hh, rfl⟩ x hx
      by_contra hhx
      apply hoff _ hhx
      have : k • ((MulAut.conj k⁻¹).toMonoidHom h • x) = h • (k • x) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ← mul_smul]
        congr 1
        group
      rw [this]
      exact h𝒬inv h (hΩM hh) _ (hbl𝒬 x hx)

include hK hfix in
theorem exists_conj_zGroup_le_of_sq_dvd {M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hM : p ^ 2 ∣ Nat.card M) :
    ∃ g : ProjectiveSpecialUnitaryMatrixGroup J,
      (zGroup J hJ).map (MulAut.conj g).toMonoidHom ≤ M := by
  have : Finite M := Subtype.finite
  obtain ⟨R⟩ : Nonempty (Sylow p M) := inferInstance
  have hR2 : p ^ 2 ∣ Nat.card R := R.pow_dvd_card_of_pow_dvd_card hM
  set R' : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) := (R : Subgroup M).map M.subtype
    with hR'
  have hR'p : IsPGroup p R' := R.isPGroup'.map M.subtype
  obtain ⟨g, hg⟩ := exists_le_conj_rootGroup J hJ hK hfix hR'p
  set R'' := R'.map (MulAut.conj g⁻¹).toMonoidHom with hR''
  have hR''U : R'' ≤ rootGroup J hJ := by
    rw [hR'', ← map_conj_inv_map_conj (rootGroup J hJ) g]
    exact Subgroup.map_mono hg
  have hcard : p ^ 2 ≤ Nat.card R'' := by
    rw [hR'', card_map_conj, hR', Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.le_of_dvd Nat.card_pos hR2
  have hZ := zGroup_le_of_le_rootGroup J hJ hK hfix hR''U hcard
  refine ⟨g, ?_⟩
  calc (zGroup J hJ).map (MulAut.conj g).toMonoidHom ≤ R''.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hZ
    _ = R' := by rw [hR'', map_conj_map_conj, mul_inv_cancel]; exact map_conj_one R'
    _ ≤ M := Subgroup.map_subtype_le _

private theorem false_of_orbit_count {p r a c : ℕ} (hp7 : 7 ≤ p) (hc : 2 * c = p * (p - 1))
    (hr : p ≤ r + 1) (hca : c * r ≤ a) (hsum : (p ^ 2 - 1) * r + a ≤ p ^ 3 + 1) : False := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have h1 : (q + 1) ^ 2 - 1 = q * (q + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [h1] at hsum
  rw [show q + 1 - 1 = q by omega] at hc
  have hrq : q ≤ r := by omega
  have h2 : (2 * q * (q + 2) + (q + 1) * q) * r ≤ 2 * ((q + 1) ^ 3 + 1) := by
    calc (2 * q * (q + 2) + (q + 1) * q) * r = 2 * (q * (q + 2) * r + c * r) := by
          rw [mul_add 2, ← mul_assoc 2 c, hc]; ring
      _ ≤ 2 * ((q + 1) ^ 3 + 1) := Nat.mul_le_mul_left 2 (by omega)
  have h3 := (Nat.mul_le_mul_left (2 * q * (q + 2) + (q + 1) * q) hrq).trans h2
  nlinarith

include hK hfix in
theorem false_of_not_sq_dvd (hp7 : 7 ≤ p) (hp3 : p % 3 = 1)
    {Ω M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (e : Ω ≃* PSL(2, ZMod p))
    (hΩM : Ω ≤ M) (hDM : torusGroup J hJ ≤ M) (hM : ¬ p ^ 2 ∣ Nat.card M) : False := by
  have hp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by omega
  have hp21 : 0 < p ^ 2 - 1 := by
    have : 49 ≤ p ^ 2 := by nlinarith
    omega
  have hgcd : Nat.gcd (p + 1) 3 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
  have hDcard : Nat.card (torusGroup J hJ) = p ^ 2 - 1 := by
    rw [card_torusGroup J hJ p hK hfix, hgcd, Nat.div_one]
  have hstabcard : Nat.card (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
      (pinf J hJ)) = p ^ 3 * (p ^ 2 - 1) := by
    rw [card_stabilizer_pinf J hJ p hK hfix, hgcd, Nat.div_one]
  obtain ⟨⟨u₀, hu₀Ω⟩, hu₀'⟩ := exists_orderOf_eq_of_mulEquiv_psl2 hp2 e
  have hu₀ : orderOf u₀ = p := (Subgroup.orderOf_mk u₀ hu₀Ω).symm.trans hu₀'
  have hu₀M : u₀ ∈ M := hΩM hu₀Ω
  have hu₀1 : u₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu₀
    exact hp.one_lt.ne hu₀
  obtain ⟨Pu, hF⟩ : ∃ Pu : IsoPoint J, ∀ w ∈ Subgroup.zpowers u₀,
      w • Pu = Pu ∧ (w ≠ 1 → ∀ x : IsoPoint J, w • x = x → x = Pu) := by
    obtain ⟨g, hg⟩ := exists_le_conj_rootGroup J hJ hK hfix
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu₀, pow_one]))
    refine ⟨g • pinf J hJ, fun w hw => ?_⟩
    obtain ⟨r, hr, rfl⟩ := hg hw
    have hr' : r • pinf J hJ = pinf J hJ := rootGroup_le_stabilizer J hJ hr
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, hr'], fun hw1 x hx => ?_⟩
    have hr1 : r ≠ 1 := by
      rintro rfl
      apply hw1
      group
    have : r • (g⁻¹ • x) = g⁻¹ • x := by
      rw [← mul_smul, show r * g⁻¹ = g⁻¹ * (g * r * g⁻¹) by group, mul_smul, hx]
    rw [← eq_pinf_of_mem_rootGroup J hJ hK hfix hr hr1 this, smul_inv_smul]
  have hu₀Pu : u₀ • Pu = Pu := (hF u₀ (Subgroup.mem_zpowers u₀)).1
  obtain ⟨ι, -, -, hιbl, -, -, hιY⟩ := exists_iotaSL2 J hJ hK hfix hp2
  obtain ⟨y, hyY, hy⟩ := exists_yGroup_two_le_card J hJ hK hfix hp2 hp3
  have hyD : y ∈ torusGroup J hJ := yGroup_le_torusGroup J hJ hyY
  have hyM : y ∈ M := hDM hyD
  have hyinf : y • pinf J hJ = pinf J hJ := torusGroup_le_stabilizer_pinf J hJ hyD
  have hB0 : ∀ v ∈ M, orderOf v = p → ∀ h : ProjectiveSpecialUnitaryMatrixGroup J,
      v ∉ (zGroup J hJ).map (MulAut.conj h).toMonoidHom := by
    intro v hvM hv h hvh
    obtain ⟨m, hm⟩ := exists_map_conj_eq_of_card_eq hM
      (S := Subgroup.zpowers (⟨u₀, hu₀M⟩ : M)) (T := Subgroup.zpowers (⟨v, hvM⟩ : M))
      (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu₀])
      (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hv])
    have hmem : (MulAut.conj m).toMonoidHom ⟨u₀, hu₀M⟩ ∈ Subgroup.zpowers (⟨v, hvM⟩ : M) := by
      rw [hm]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : v ^ k = (m : ProjectiveSpecialUnitaryMatrixGroup J) * u₀ *
        (m : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ := by
      simpa [MulAut.conj_apply] using congrArg Subtype.val hk
    apply not_mem_conj_zGroup J hJ hK hfix hp5 e hu₀Ω hu₀
      ((m : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * h)
    rw [← map_conj_map_conj]
    refine ⟨v ^ k, Subgroup.zpow_mem _ hvh k, ?_⟩
    rw [hk']
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hB1' : ∀ v ∈ M, orderOf v = p → ∀ Q ∈ blockW J, v • Q ≠ Q := by
    intro v hvM hv Q hQ hvQ
    obtain ⟨s, hs, rfl⟩ := hιbl Q hQ
    have hv''p : (s⁻¹ * v * s) • pinf J hJ = pinf J hJ := by
      rw [mul_smul, mul_smul, hvQ, inv_smul_smul]
    have hv''o : orderOf (s⁻¹ * v * s) = p := by
      rw [show s⁻¹ * v * s = MulAut.conj s⁻¹ v by simp [MulAut.conj_apply],
        MulEquiv.orderOf_eq, hv]
    have hv''U := mem_rootGroup_of_smul_pinf J hJ hK hfix hv''o hv''p
    have hv''Z : s⁻¹ * v * s ∉ zGroup J hJ := fun hz =>
      hB0 v hvM hv s ⟨_, hz, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    have hcard := hy _ hv''U hv''Z
    have hsy : s⁻¹ * y * s = y := by
      rw [mul_assoc, ← hιY s hs y hyY]
      group
    have hCU : Subgroup.closure {s⁻¹ * v * s, y * (s⁻¹ * v * s) * y⁻¹} ≤ rootGroup J hJ := by
      rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hv''U, conj_mem_rootGroup_of_smul_pinf J hJ p hK hfix hyinf hv''U⟩
    have hCM : Subgroup.closure {s⁻¹ * v * s, y * (s⁻¹ * v * s) * y⁻¹} ≤
        M.map (MulAut.conj s⁻¹).toMonoidHom := by
      have hv''M : s⁻¹ * v * s ∈ M.map (MulAut.conj s⁻¹).toMonoidHom :=
        ⟨v, hvM, by simp [MulAut.conj_apply]⟩
      have hyM' : y ∈ M.map (MulAut.conj s⁻¹).toMonoidHom :=
        ⟨y, hyM, by simpa [MulAut.conj_apply] using hsy⟩
      rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hv''M, Subgroup.mul_mem _ (Subgroup.mul_mem _ hyM' hv''M) (Subgroup.inv_mem _ hyM')⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
      ((IsPGroup.of_card (card_rootGroup J hJ p hK hfix)).to_le hCU)
    have hn2 : 2 ≤ n := by
      rw [hn] at hcard
      exact (pow_le_pow_iff_right₀ hp.one_lt).mp hcard
    apply hM
    calc p ^ 2 ∣ p ^ n := pow_dvd_pow p hn2
      _ = Nat.card (Subgroup.closure {s⁻¹ * v * s, y * (s⁻¹ * v * s) * y⁻¹}) := hn.symm
      _ ∣ Nat.card (M.map (MulAut.conj s⁻¹).toMonoidHom) := Subgroup.card_dvd_of_le hCM
      _ = Nat.card M := card_map_conj _ _
  have hB1 : ∀ m : M, m • Pu ∉ blockW J := by
    intro m hm
    refine hB1' ((m : ProjectiveSpecialUnitaryMatrixGroup J) * u₀ *
      (m : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹)
      (M.mul_mem (M.mul_mem m.2 hu₀M) (M.inv_mem m.2)) ?_ _ hm ?_
    · rw [show (m : ProjectiveSpecialUnitaryMatrixGroup J) * u₀ *
        (m : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ =
        MulAut.conj (m : ProjectiveSpecialUnitaryMatrixGroup J) u₀ from rfl,
        MulEquiv.orderOf_eq, hu₀]
    · rw [Subgroup.smul_def, mul_smul, mul_smul, inv_smul_smul, hu₀Pu]
  have hB2 : (MulAction.orbit M Pu).ncard ≡ 1 [MOD p] := by
    have hHu : IsPGroup p (Subgroup.zpowers (⟨u₀, hu₀M⟩ : M)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu₀, pow_one])
    have h := hHu.card_modEq_card_fixedPoints (MulAction.orbit M Pu)
    rw [Nat.card_coe_set_eq] at h
    have hfix1 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers (⟨u₀, hu₀M⟩ : M))
        (MulAction.orbit M Pu)) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨⟨Pu, MulAction.mem_orbit_self Pu⟩, MulAction.mem_fixedPoints.mpr ?_⟩, ?_⟩
      · rintro ⟨w, hw⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        apply Subtype.ext
        change ((⟨u₀, hu₀M⟩ ^ k : M) : ProjectiveSpecialUnitaryMatrixGroup J) • Pu = Pu
        rw [SubgroupClass.coe_zpow]
        exact (hF _ (Subgroup.zpow_mem_zpowers u₀ k)).1
      · rintro ⟨⟨x, hx⟩, hxfix⟩
        have h1 : u₀ • x = x := congrArg Subtype.val
          (MulAction.mem_fixedPoints.mp hxfix ⟨⟨u₀, hu₀M⟩, Subgroup.mem_zpowers _⟩)
        exact Subtype.ext (Subtype.ext ((hF u₀ (Subgroup.mem_zpowers u₀)).2 hu₀1 x h1))
    rwa [hfix1] at h
  have hB3 : p ^ 2 - 1 ∣ (MulAction.orbit M Pu).ncard := by
    have hfree : ∀ b : MulAction.orbit M Pu,
        MulAction.stabilizer ((torusGroup J hJ).subgroupOf M) b = ⊥ := by
      rintro ⟨_, m, rfl⟩
      rw [eq_bot_iff]
      intro d hd
      rw [Subgroup.mem_bot]
      have h1 : ((d : M) : ProjectiveSpecialUnitaryMatrixGroup J) • (m • Pu) = m • Pu :=
        congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hd)
      exact Subtype.ext (Subtype.ext (torusGroup_eq_one_of_smul_eq J hJ hK hfix
        (Subgroup.mem_subgroupOf.mp d.2) (hB1 m) h1))
    rw [← Nat.card_coe_set_eq, Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hfree),
      Nat.card_prod, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv, hDcard]
    exact dvd_mul_left _ _
  have hB5 : Nat.card (MulAction.stabilizer M (pinf J hJ)) ≤ p ^ 2 - 1 := by
    have hnp : ¬ p ∣ Nat.card (MulAction.stabilizer M (pinf J hJ)) := by
      intro hdvd
      obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' p hdvd
      refine hB1' ((v : M) : ProjectiveSpecialUnitaryMatrixGroup J) (v : M).2
        (by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hv]) _ (pinf_mem_blockW J hJ) ?_
      exact MulAction.mem_stabilizer_iff.mp v.2
    have hle : (MulAction.stabilizer M (pinf J hJ)).map M.subtype ≤
        MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hv
    have hdvd : Nat.card (MulAction.stabilizer M (pinf J hJ)) ∣ p ^ 3 * (p ^ 2 - 1) := by
      rw [← hstabcard, ← Subgroup.card_map_of_injective M.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    have hcop : Nat.Coprime (Nat.card (MulAction.stabilizer M (pinf J hJ))) (p ^ 3) :=
      Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp).symm
    exact Nat.le_of_dvd hp21 (hcop.dvd_of_dvd_mul_left hdvd)
  have hB6 : p * (p - 1) / 2 ≤ Nat.card (MulAction.stabilizer M Pu) := by
    have hS : Nat.card (Subgroup.zpowers (⟨u₀, hu₀Ω⟩ : Ω)) = p := by
      rw [Nat.card_zpowers, hu₀']
    rw [← card_normalizer_of_mulEquiv_psl2 hp2 e hS]
    have hfixN : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers (⟨u₀, hu₀Ω⟩ : Ω) : Set Ω),
        ((n : Ω) : ProjectiveSpecialUnitaryMatrixGroup J) • Pu = Pu := by
      intro n hn
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
        ((Subgroup.mem_normalizer_iff.mp hn _).mp (Subgroup.mem_zpowers _))
      have hk' : u₀ ^ k = (n : ProjectiveSpecialUnitaryMatrixGroup J) * u₀ *
          (n : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ := by
        simpa using congrArg Subtype.val hk
      have hw1 : u₀ ^ k ≠ 1 := by
        rw [hk']
        intro h1
        apply hu₀1
        calc u₀ = (n : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ *
              ((n : ProjectiveSpecialUnitaryMatrixGroup J) * u₀ *
                (n : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹) * n := by group
          _ = 1 := by rw [h1]; group
      refine (hF _ (Subgroup.zpow_mem_zpowers u₀ k)).2 hw1 _ ?_
      rw [hk', mul_smul, mul_smul, inv_smul_smul, hu₀Pu]
    refine Nat.card_le_card_of_injective
      (fun n => ⟨⟨((n : Ω) : ProjectiveSpecialUnitaryMatrixGroup J), hΩM (n : Ω).2⟩,
        hfixN n n.2⟩) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext
      (congrArg (fun x : MulAction.stabilizer M Pu =>
        ((x : M) : ProjectiveSpecialUnitaryMatrixGroup J)) hab))
  have hO1 := (MulAction.stabilizer M Pu).card_mul_index
  rw [MulAction.index_stabilizer] at hO1
  have hO2 := (MulAction.stabilizer M (pinf J hJ)).card_mul_index
  rw [MulAction.index_stabilizer] at hO2
  have hdisj : Disjoint (MulAction.orbit M Pu) (MulAction.orbit M (pinf J hJ)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨m₁, rfl⟩ ⟨m₂, h⟩
    change m₂ • pinf J hJ = m₁ • Pu at h
    apply hB1 (m₂⁻¹ * m₁)
    rw [mul_smul, ← h, inv_smul_smul]
    exact pinf_mem_blockW J hJ
  have hsum : (MulAction.orbit M Pu).ncard + (MulAction.orbit M (pinf J hJ)).ncard ≤
      p ^ 3 + 1 := by
    rw [← Set.ncard_union_eq hdisj, ← card_isoPoint J hJ p hK hfix, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  obtain ⟨r, hr⟩ := hB3
  have hr1 : p ≤ r + 1 := by
    have h0 : (MulAction.orbit M Pu).ncard + r ≡ 0 [MOD p] := by
      rw [hr, Nat.modEq_zero_iff_dvd]
      refine ⟨p * r, ?_⟩
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
      ring
    have h2 : 1 + r ≡ 0 [MOD p] := (hB2.add_right r).symm.trans h0
    have h3 : p ∣ r + 1 := by
      rw [add_comm]
      exact Nat.modEq_zero_iff_dvd.mp h2
    exact Nat.le_of_dvd (by omega) h3
  have hca : p * (p - 1) / 2 * r ≤ (MulAction.orbit M (pinf J hJ)).ncard := by
    have h1 := (Nat.mul_le_mul_right (MulAction.orbit M Pu).ncard hB6).trans_eq hO1
    have h2 := hO2.symm.trans_le
      (Nat.mul_le_mul_right (MulAction.orbit M (pinf J hJ)).ncard hB5)
    rw [hr] at h1
    refine Nat.le_of_mul_le_mul_left ?_ hp21
    rw [mul_left_comm]
    exact h1.trans h2
  have hc : 2 * (p * (p - 1) / 2) = p * (p - 1) := by
    have : Even (p * (p - 1)) := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [show q + 1 - 1 = q by omega, mul_comm]
      exact Nat.even_mul_succ_self q
    exact Nat.two_mul_div_two_of_even this
  exact false_of_orbit_count hp7 hc hr1 hca (hr ▸ hsum)

include hK hfix in
theorem torusGroup_sup_eq_top_of_mulEquiv_psl2 (hp7 : 7 ≤ p) (hp3 : p % 3 = 1)
    {Ω : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (e : Ω ≃* PSL(2, ZMod p)) :
    torusGroup J hJ ⊔ Ω = ⊤ := by
  by_cases hM : p ^ 2 ∣ Nat.card ↥(torusGroup J hJ ⊔ Ω)
  · obtain ⟨g, hg⟩ := exists_conj_zGroup_le_of_sq_dvd J hJ hK hfix hM
    exact eq_top_of_conj_zGroup_le J hJ hK hfix (by omega) hp3 e le_sup_right hg
  · exact (false_of_not_sq_dvd J hJ hK hfix hp7 hp3 e le_sup_right le_sup_left hM).elim

end CFSG.RankThree.PartTwo.Sec20.F3U3

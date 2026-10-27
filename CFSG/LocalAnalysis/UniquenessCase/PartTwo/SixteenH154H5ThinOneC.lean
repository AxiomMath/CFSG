module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.Quasithin.Background.SmithC27RTypeU33
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33PartialRanks
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SectionRank.ClassicalEven CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open scoped commutatorElement

variable {W : Type} [CommGroup W]

private instance s16h_H5C_finite_mulAut [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun f : MulAut W => (f : W → W)) (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_H5C_commutator_le_self {Γ : Type*} [Group Γ] (H : Subgroup Γ) :
    ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

private theorem s16h_H5C_false_of_oddRankTwo [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t) (h : CFSG.Quasithin.A3Facts.OddRankTwo ↥L) :
    False := by
  obtain ⟨q, hq, hq2, h2⟩ := h
  have h3 : CFSG.Open.pRank q (⊤ : Subgroup ↥L) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact hc.thin q hq hq2
  omega

private theorem s16h_H5C_injective_of_surjective_simple {G S : Type} [Group G] [Group S]
    [IsSimpleGroup G] [Nontrivial S] (f : G →* S) (hf : Function.Surjective f) :
    Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_pair_ne S
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    exact hab (by rw [MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x),
      MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top y)])

private theorem s16h_H5C_nontrivial_of_isQuasisimple {X : Type} [Group X]
    (h : CFSG.Open.IsQuasisimple X) : Nontrivial X := by
  haveI : Nontrivial (X ⧸ Subgroup.center X) := h.2.toNontrivial
  exact (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial

private theorem s16h_H5C_not_isCyclic_of_isElemAbelian_sq {G : Type*} [Group G] {p : ℕ}
    [Fact p.Prime] {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) : ¬ IsCyclic E := by
  intro hcyc
  haveI : IsCyclic E := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
  have htop : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' (Subgroup.zpowers g)).2 hg
  have hcardE : Nat.card E = orderOf g := by
    rw [← Subgroup.card_top (G := E), ← htop, Nat.card_zpowers]
  have hgp : g ^ p = 1 := Subtype.ext (hE.2 (g : G) g.2)
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have hle : orderOf g ≤ p := Nat.le_of_dvd (Fact.out : p.Prime).pos hdvd
  have hlt : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
  omega

private theorem s16h_H5C_two_le_pRank_of_center_alt_six {X : Type} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3)
    (he : Nonempty (X ⧸ Subgroup.center X ≃* ↥(alternatingGroup (Fin 6)))) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := he
  have hq : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact CFSG.Quasithin.A3Facts.two_le_pRank_alternating (n := 6) (by norm_num)
  obtain ⟨E, -, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (G := X ⧸ Subgroup.center X) (H := ⊤) (k := 2) hq
  let Z : Subgroup X := Subgroup.center X
  let P : Subgroup X := E.comap (QuotientGroup.mk' Z)
  have hPcard : Nat.card P = 3 ^ 3 := by
    have h1 : Nat.card P = Nat.card Z * Nat.card E :=
      QuotientGroup.card_preimage_mk Z (E : Set (X ⧸ Z))
    have hZ' : Nat.card Z = 3 := hZ
    rw [h1, hZ', hEcard]
    norm_num
  have hP3 : IsPGroup 3 P := IsPGroup.of_card hPcard
  have hPnc : ¬ IsCyclic P := by
    intro hcyc
    haveI : IsCyclic P := hcyc
    let f : P →* E :=
      ((QuotientGroup.mk' Z).comp P.subtype).codRestrict E (fun x => x.2)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z (y : X ⧸ Z)
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change (QuotientGroup.mk' Z) x ∈ E
        rw [hx]; exact y.2
      · exact Subtype.ext hx
    have hEcyc : IsCyclic E := isCyclic_of_surjective f hf
    exact s16h_H5C_not_isCyclic_of_isElemAbelian_sq (p := 3) hEab hEcard hEcyc
  exact CFSG.Quasithin.A3Facts.two_le_pRank_of_not_isCyclic (by norm_num) hP3 hPnc

theorem s16h_H5_not_thin_of_g2
    [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : G2NaturalDerived L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 1) :
    False := by
  obtain ⟨F, iF, fF, hF, π, hπ⟩ := h
  have hF2 : Nat.card F = 2 := hF.trans (pow_one 2)
  haveI : CharP F 2 := CFSG.Quasithin.FFC.charP_two_of_card_pow hF
  let e := CFSG.Quasithin.FFC.equivOfRealizes
    (CFSG.Quasithin.FFC.zornQ_faithful _ (s16h_H5C_commutator_le_self _)) hπ
  have hP : IsPSU 3 3 1 ↥L :=
    CFSG.Quasithin.SmithC27.isPSU_of_equiv_g2Derived hF2 e.symm
  have hLM : CFSG.Blueprint.LieModel ↥L .PSU 3 3 1 := Or.inl ⟨by decide, hP⟩
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = 2 :=
    pRank_three_eq_two_of_lieModel_PSU_three_three_one hLM
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact hc.thin 3 Nat.prime_three (by norm_num)
  omega

theorem s16h_H5_not_thin_of_tripleA6 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : TripleA6Six L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    False := by
  obtain ⟨K, hKfield, hKfin, Γ₀, hKcard, hdet, hhat, hcenter, hreal⟩ := h
  obtain ⟨π, hπ⟩ := hreal
  have hinj : Function.Injective π :=
    hπ.injective_of_faithful_on (FFModel.nat_faithful Γ₀)
  let e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have hodd : CFSG.Quasithin.A3Facts.OddRankTwo ↥Γ₀ :=
    ⟨3, Nat.prime_three, by norm_num,
      s16h_H5C_two_le_pRank_of_center_alt_six hhat.2.1 hhat.2.2⟩
  exact s16h_H5C_false_of_oddRankTwo hc
    (CFSG.Quasithin.A3Facts.OddRankTwo.of_mulEquiv e.symm hodd)

theorem s16h_H5_not_thin_of_u43 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : ∃ S : Type, ∃ _ : Group S, CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧ IsHat ↥L S) :
    False := by
  obtain ⟨S, hSgrp, hmodel, hhat⟩ := h
  have hFinS : Finite S := by
    obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨eK⟩⟩ :=
      (hmodel.statedClassicalModel_of_ne_zero (by norm_num) :
        StatedClassicalModel S .PSU 4 3 1)
    exact Finite.of_equiv _ eK.symm.toEquiv
  haveI : Finite S := hFinS
  have hsc : StatedClassicalModel S .PSU 4 3 1 :=
    hmodel.statedClassicalModel_of_ne_zero (by norm_num)
  obtain ⟨-, -, hrk⟩ :=
    CFSG.SectionRank.classical_model_rank (G := S) (t := .PSU) (n := 4) (p := 3) (f := 1)
      (by norm_num : (3 : ℕ) ≠ 2) hsc
  have hS4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
    rcases hrk with ⟨h, -⟩ | ⟨-, ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | h
    · exact absurd h (by decide)
    · exact absurd h (by norm_num)
    · exact h
    · exact absurd h (by decide)
    · exact h
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hhat
  have hq4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact hS4
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hthin : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact hc.thin 3 Nat.prime_three (by norm_num)
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 2 := by omega
  have h3 := CFSG.SectionRank.pRank_quotient_le_three (G := ↥L) (p := 3)
    (by norm_num : (3 : ℕ) ≠ 2) hle (Subgroup.center ↥L) le_rfl
  omega

theorem s16h_H5_not_thin_of_a7 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : A7Four L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) : False := by
  obtain ⟨α, hR⟩ := h
  obtain ⟨π, hπ⟩ := hR
  haveI : IsSimpleGroup (FFModel.a7Four α).Gam := alternatingGroup.isSimpleGroup (by simp)
  haveI : Nontrivial ↥L := s16h_H5C_nontrivial_of_isQuasisimple hc.comp.2.2
  have hinj : Function.Injective π := s16h_H5C_injective_of_surjective_simple π hπ.1
  let e : ↥L ≃* ↥(alternatingGroup (Fin 7)) :=
    (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm
  refine s16h_H5C_false_of_oddRankTwo hc ⟨3, Nat.prime_three, by norm_num, ?_⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact CFSG.Quasithin.A3Facts.two_le_pRank_alternating (n := 7) (by norm_num)

theorem s16h_H5_not_thin_of_sp6 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : IsSpn ↥L 6 1) : False := by
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := h
  have hdiv : 6 / 2 = 3 := by norm_num
  rw [hdiv] at e
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSp 3 K)) := by
    have hdvd : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hKcard]; norm_num
    have := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp
      (K := K) (n := 3) (r := 3) Nat.prime_three hdvd
    omega
  have h3' : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact h3
  exact s16h_H5C_false_of_oddRankTwo hc ⟨3, Nat.prime_three, by norm_num, h3'⟩

theorem s16h_H5_not_thin_of_m22 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : UC22.IsSpor ↥L .M22) : False := by
  obtain ⟨e⟩ := h
  haveI : Finite CFSG.Blueprint.NativeSporadic.M22 := inferInstance
  have hodd : CFSG.Quasithin.A3Facts.OddRankTwo CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Quasithin.A3Facts.oddRankTwo_M22
  have e' : ↥L ≃* CFSG.Blueprint.NativeSporadic.M22 := e
  exact s16h_H5C_false_of_oddRankTwo hc
    (CFSG.Quasithin.A3Facts.OddRankTwo.of_mulEquiv e' hodd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

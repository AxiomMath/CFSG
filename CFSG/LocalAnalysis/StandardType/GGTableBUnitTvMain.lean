module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvCore
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvModel
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthLSp
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutUnit
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB TableBOrthL

namespace UnitTv

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_noncyclic_of_torusLift {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) {L : Subgroup G}
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hlift : GGTorusLift p r R) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, hEker⟩ := hlift L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
  have hEG : IsElemAbelian p (E.map L.subtype) := isElemAbelian_map hE L.subtype
  have hcard : Nat.card (E.map L.subtype) = p ^ r := by
    rw [← Nat.card_congr (E.equivMapOfInjective _ L.subtype_injective).toEquiv, hEcard]
  exact ⟨E.map L.subtype, Subgroup.map_subtype_le E, isPGroup_of_isElemAbelian hEG,
    not_isCyclic_of_card hp.one_lt hEG.2 (by rw [hcard]; exact Nat.pow_le_pow_right hp.pos hr)⟩

theorem ggLTransvectionCenterInputOn_of_labels_two {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧
        (GGNoTransvectionSCr p r R I ∨ GGCenterCoprime p R ∧ GGNoTransvectionSC p R I)) :
    GGLTransvectionCenterInputOn S := by
  intro G _ _ p B Bs x L D J hC hM φ hφ htv b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hr2, hlift, hor⟩ :=
    largeEvenRawDatum_exists hraw
  have hnc := exists_noncyclic_of_torusLift hp hr2 hL θ hlift
  rcases hor with htvt | ⟨hZc, htvt⟩
  · exact mem_zpowers_of_noTransvectionSCr hC hnc hL θ hBsN
      (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hlift htvt hφ htv b
  · exact mem_zpowers_of_noTransvectionSC hC hnc hL θ hBsN h3 hZc htvt hφ htv b

end Config

section PerGroup

theorem ggNoTransvectionSCr_unitary {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hnd : ¬ (d = 6 ∧ p = 3)) :
    GGNoTransvectionSCr p (ggUnitaryTorusRank p d)
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc α _
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := by
    by_cases hpd : p ∣ d
    · have hrank : ggUnitaryTorusRank p d = d - 3 := by simp [ggUnitaryTorusRank, hpd]
      rw [hrank] at hr
      exact LineU.card_ge_of_dvd hp hp2 hd hpd hnd hr h3
    · have hrank : ggUnitaryTorusRank p d = d - 2 := by simp [ggUnitaryTorusRank, hpd]
      rw [hrank] at hr
      exact card_ge_of_not_dvd hp hp2 hd hr
  have hdnd : (d, n) ≠ (6, 1) := by
    rintro ⟨rfl, rfl⟩
    have h3' : p ∣ 3 := by simpa using hpq
    exact hnd ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ := exists_diagModel' hK hn hd hp hpq
    (LineU.unitaryUniversalCover_holds n d K hK hd hdnd) hψ hker hperf hA hAI hcard
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  have hM : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  exact not_transvection_of_model hM hK hp hp2 hpq hd hA hsc hdiag α

end PerGroup

end UnitTv

@[expose] def GGUnitaryTvLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ (lab.rank = 5 ∧ p = 3)

section Labels

theorem largeEvenLabelAll_unitary_tv {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitaryTvLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧
      (GGNoTransvectionSCr p r R I ∨ GGCenterCoprime p R ∧ GGNoTransvectionSC p R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn, hno⟩ := h
  dsimp only at ht hl hpn hno
  subst ht
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  have hlift := ggTorusLift_unitary hK hn (by omega : 3 ≤ l + 1) hdq hp hpn
  by_cases h4 : l = 3
  · subst h4
    have hp4 : ¬ p ∣ 4 := fun h4 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h4)))
    have hr : 2 ≤ ggUnitaryTorusRank p (3 + 1) := by
      simp only [ggUnitaryTorusRank]
      split_ifs with h
      · exact absurd h hp4
      · norm_num
    exact ⟨K, i1, i2, hK, ⟨hQ', _, hr, hlift, Or.inr
      ⟨CorFourTwoOpen.ggCenterCoprime_of_centerPrime
        (StdSubRestU.ggCenterPrime_unitary hK hn (by norm_num) (by simp) hp hp2 hp4),
        ggUnitaryFourTvSCInput_holds K n p hK hn hp hpn⟩⟩⟩
  · have hd5 : 5 ≤ l + 1 := by omega
    have hr2 : 2 ≤ ggUnitaryTorusRank p (l + 1) := by
      simp only [ggUnitaryTorusRank]
      split_ifs <;> omega
    exact ⟨K, i1, i2, hK, ⟨hQ', _, hr2, hlift, Or.inl
      (UnitTv.ggNoTransvectionSCr_unitary hK hn hd5 hp hpn fun ⟨h6, h3⟩ => hno ⟨by omega, h3⟩)⟩⟩

theorem ggLTransvectionCenterInputOn_unitary_of {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      GGUnitaryTvLabel p lab) : GGLTransvectionCenterInputOn S :=
  UnitTv.ggLTransvectionCenterInputOn_of_labels_two fun p lab hp hlab hs =>
    largeEvenLabelAll_unitary_tv hp hlab (h p lab hp hlab hs)

end Labels

end CFSG.StandardType

end

module

public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionInflate
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionCritical
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionIrreducible
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionRep
public import CFSG.RankThree.PartOne.S9.QD32.RigidityMain
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.OddCore37
open scoped commutatorElement

theorem criticalOddCoreTwoActionRecognition_of
    (hMTAWR3 : MinimalTwoActionWithoutRankThreeFixedGroup) :
    CriticalOddCoreTwoActionRecognition := by
  intro G _ _ p q A R Q hp hq hp3 hq2 hpq hA hR2 hRA hcomm hRne hQn hQp hRQ hrank
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hQnt : Nontrivial ↥Q := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    exact hRQ (by rw [h, Subgroup.commutator_bot_right])
  obtain ⟨D₀, hD₀c, hD₀ne, hD₀comm, hD₀exp, hD₀fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := q) hq2 hQp (P := ↥Q)
  set D : Subgroup G := D₀.map Q.subtype with hD
  have hDQ : D ≤ Q := Subgroup.map_subtype_le _
  have hDsub : D.subgroupOf Q = D₀ :=
    Subgroup.comap_map_eq_self_of_injective Q.subtype_injective D₀
  have hDchar : (D.subgroupOf Q).Characteristic := by
    rw [hDsub]
    exact hD₀c
  have hDne : D ≠ ⊥ := fun h =>
    hD₀ne ((Subgroup.map_eq_bot_iff_of_injective D₀ Q.subtype_injective).1 h)
  have hDexp : ∀ d ∈ D, d ^ q = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := congrArg Subtype.val (hD₀exp x hx)
    simpa using this
  have hDQcomm : ⁅D, Q⁆ ≤ D ⊓ Subgroup.centralizer (D : Set G) := by
    have h1 : ⁅D, Q⁆ = (⁅D₀, (⊤ : Subgroup ↥Q)⁆).map Q.subtype := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h1]
    refine (Subgroup.map_mono hD₀comm).trans ?_
    rintro _ ⟨x, ⟨hxD, hxc⟩, rfl⟩
    refine ⟨⟨x, hxD, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxc d hd)
  have hDn : D.Normal := normal_of_characteristic hDQ hDchar
  have hDq : IsPGroup q D := hQp.to_le hDQ
  have hDcl : ⁅⁅D, D⁆, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (Subgroup.commutator_mono le_rfl hDQ).trans (hDQcomm.trans inf_le_right)
  have hRD : ⁅R, D⁆ ≠ ⊥ := by
    intro hbot
    have hRcD : R ≤ Subgroup.centralizer (D : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    apply hRQ
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro r hr
    set φ : MulAut ↥Q := MulAut.conjNormal (H := Q) r with hφ
    have hφfix : φ ∈ fixingSubgroup (MulAut ↥Q) (D₀ : Set ↥Q) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      rw [MulAut.smul_def]
      apply Subtype.ext
      rw [hφ, MulAut.conjNormal_apply]
      have hyD : (y : G) ∈ D := ⟨y, hy, rfl⟩
      have h1 : (y : G) * r = r * y := Subgroup.mem_centralizer_iff.1 (hRcD hr) (y : G) hyD
      calc (r : G) * y * r⁻¹ = y * r * r⁻¹ := by rw [← h1]
        _ = y := by group
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hR2) ⟨r, hr⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hD₀fix) ⟨φ, hφfix⟩
    have h1 : orderOf φ ∣ orderOf r := orderOf_map_dvd (MulAut.conjNormal (H := Q)) r
    rw [Subgroup.orderOf_mk] at hk hm
    rw [hk] at h1
    have hcop : Nat.Coprime (q ^ m) (2 ^ k) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
    have h2 : orderOf φ = 1 := by
      have h3 : q ^ m ∣ 2 ^ k := hm ▸ h1
      rw [hm]
      exact hcop.eq_one_of_dvd h3
    have hφ1 : φ = 1 := orderOf_eq_one_iff.1 h2
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h4 := congrArg (fun f : MulAut ↥Q => ((f ⟨x, hx⟩ : ↥Q) : G)) hφ1
    simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply] at h4
    calc x * r = (r * x * r⁻¹) * r := by rw [h4]
      _ = r * x := by group
  have hrankD : ∀ r ∈ R, r ≠ 1 →
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2 := fun r hr hr1 =>
    (OddCore37.pRank_le_of_le hq (inf_le_inf_right _ hDQ)).trans (hrank r hr hr1)
  obtain ⟨S₀, hS₀R, -, h5, -, hDS₀, hshape⟩ := exists_qd32_below hMTAWR3 hp hq hp3 hq2 hpq hA
    Subgroup.le_normalizer_of_normal hDq hDexp hDcl hR2 hRA hcomm hRD hrankD
  have hrel : (inSubgroup frattini D).relIndex D = q ^ 4 := isQDShape_relIndex_frattini hq hshape
  have hRD0 : R ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro r ⟨hrR, hrc⟩
    by_contra hr1
    have hr1' : r ≠ 1 := fun h => hr1 (by rw [h]; exact Subgroup.one_mem _)
    have h3 := three_le_pRank_of_isQDShape hq hshape
    have h4 : D ≤ Q ⊓ Subgroup.centralizer ({r} : Set G) := fun d hd =>
      ⟨hDQ hd, Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hrc d hd)⟩
    have h5' := (OddCore37.pRank_le_of_le hq h4).trans (hrank r hrR hr1')
    omega
  obtain ⟨T, hTR, hTcrit, hAT, hTA, hidem, hAnorm, hle⟩ :=
    exists_critical_commutator hp hp2 hA hR2 hRA hcomm hRne
  have hW₁D : ⁅⁅T, A⁆, D⁆ ≠ ⊥ := by
    intro h
    have hle2 : ⁅T, A⁆ ≤ Subgroup.centralizer (D : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    apply hTA
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ R ⊓ Subgroup.centralizer (D : Set G) := ⟨hTR (hle hx), hle2 hx⟩
    rw [hRD0] at this
    exact this
  obtain ⟨S₁, hS₁W, hAS₁, -, hS₁qd, -, -⟩ := exists_qd32_below hMTAWR3 hp hq hp3 hq2 hpq hA
    Subgroup.le_normalizer_of_normal hDq hDexp hDcl (hR2.to_le (hle.trans hTR)) hAnorm hidem hW₁D
    (fun r hr hr1 => hrankD r (hTR (hle hr)) hr1)
  have hS₁R : S₁ ≤ R := hS₁W.trans (hle.trans hTR)
  have hcyc := isCyclic_inf_centralizer_of_qd32 hq hq2 hDq hrel hR2 hRD0 hS₁R hS₁qd
  have hRS₁ : R = S₁ :=
    criticalQuaternionDihedralOvergroupRigidity G R A T S₁ hR2
      (by rw [hA]; exact hp.odd_of_ne_two hp2) hRA hcomm hTR hTcrit (hS₁W.trans hle) hAS₁ hS₁qd hcyc
  have hRqd : Nonempty (R ≃* QD32) := hRS₁ ▸ hS₁qd
  have hA5 : Nat.card A = 5 := h5 ▸ hA
  have hDR : ⁅D, R⁆ = D :=
    le_antisymm (Subgroup.commutator_le_left D R)
      (calc D = ⁅D, S₀⁆ := hDS₀.symm
        _ ≤ ⁅D, R⁆ := Subgroup.commutator_mono le_rfl hS₀R)
  exact ⟨h5, hRqd, irreducible_of_qd32 hA5 hRA hcomm hRqd, D, hDQ, hDchar, hDne, hDQcomm, hDexp,
    hDR, hRD0, hrel, hshape⟩

end CFSG.RankThree.PartOne

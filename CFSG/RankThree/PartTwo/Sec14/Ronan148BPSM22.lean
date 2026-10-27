module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSTrans
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.RankThree.PartTwo.KFacts.KP4
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BM22Sg
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Quasithin.H13.NQCatT3Perm
public import Certificates.Certificate148010
public import CFSG.CharacterTheory.Burnside
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Transport
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPoint
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate2326
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166
public import Certificates.Certificate8169

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.M22

open Equiv Subgroup CFSG.Blueprint CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts.KP4 CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.RankThree.Asc83Table.M22 (x y X Y E GI GJ)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore solvable_prime_complement_core_characterization)
open CFSG.Sporadic.Mathieu (m22a m22b m22_eq card_M22 fam_m22_simplicity closure_pair_eq_top)
open scoped commutatorElement

theorem V_eq_commutator (i : Fin 4) : V i = ⁅V i, P0⁆ := by
  apply le_antisymm
  · obtain ⟨t, htP, h1, h2⟩ := exists_tw i
    have hAi : (vAE i)⁻¹ = vAE i := inv_eq_of_mul_eq_one_right (vAE_sq i)
    have hBi : (vBE i)⁻¹ = vBE i := inv_eq_of_mul_eq_one_right (vBE_sq i)
    have hA : vAE i ∈ V i := by
      rw [← V_eq_closure]; exact subset_closure (Set.mem_insert _ _)
    have hB : vBE i ∈ V i := by
      rw [← V_eq_closure]; exact subset_closure (Set.mem_insert_of_mem _ rfl)
    have c1 : ⁅vAE i, t⁆ = vBE i := by
      rw [commutatorElement_def]
      calc vAE i * t * (vAE i)⁻¹ * t⁻¹ = vAE i * (t * vAE i * t⁻¹)⁻¹ := by group
        _ = vAE i * (vAE i * vBE i)⁻¹ := by rw [h1]
        _ = vAE i * (vBE i * vAE i) := by rw [mul_inv_rev, hAi, hBi]
        _ = vBE i * (vAE i * vAE i) := by rw [← mul_assoc, vAE_vBE_comm, mul_assoc]
        _ = vBE i := by rw [vAE_sq, mul_one]
    have c2 : ⁅vBE i, t⁆ = vBE i * vAE i := by
      rw [commutatorElement_def]
      calc vBE i * t * (vBE i)⁻¹ * t⁻¹ = vBE i * (t * vBE i * t⁻¹)⁻¹ := by group
        _ = vBE i * vAE i := by rw [h2, hAi]
    have m1 : vBE i ∈ ⁅V i, P0⁆ := c1 ▸ Subgroup.commutator_mem_commutator hA htP
    have m2 : vBE i * vAE i ∈ ⁅V i, P0⁆ := c2 ▸ Subgroup.commutator_mem_commutator hB htP
    have m3 : vAE i ∈ ⁅V i, P0⁆ := by
      have := mul_mem (inv_mem m1) m2
      rwa [inv_mul_cancel_left] at this
    have hcl : closure ({vAE i, vBE i} : Set G22) ≤ ⁅V i, P0⁆ := by
      rw [closure_le]
      rintro _ (rfl | rfl)
      · exact m3
      · exact m1
    rwa [V_eq_closure] at hcl
  · rw [Subgroup.commutator_le]
    intro v hv p hp
    have hpv : p * v⁻¹ * p⁻¹ ∈ V i :=
      (mem_normalizer_iff.mp (P0_le_normalizer_V i hp) v⁻¹).mp (inv_mem hv)
    have e : ⁅v, p⁆ = v * (p * v⁻¹ * p⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hv hpv

theorem V_mem_sig {K : Subgroup G22} (i : Fin 4) (hVK : V i ≤ K) :
    V i ∈ {W : Subgroup G22 | W ≤ K ∧ W ∈ invariantPiSubgroups ⊤ P0 (piCompl 3) ∧
      W = ⁅W, P0⁆} :=
  ⟨hVK, mem_invariant_threePrime_iff.mpr ⟨not_three_dvd_card_V i, P0_le_normalizer_V i⟩,
    V_eq_commutator i⟩

theorem false_of_card_dvd {K Y : Subgroup G22} (hdvd : Nat.card Y ∣ 576) (hKY : K ≤ Y)
    (hKp : Group.IsPerfect K) (h3 : 3 ∣ Nat.card K) : False := by
  have hY : Group.IsSolvable Y := by
    obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 (show Nat.card Y ∣ 2 ^ 6 * 3 ^ 2 from hdvd)
    obtain ⟨i₁, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
    obtain ⟨i₂, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
    have : Fintype Y := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])
  have hKs : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKY)
  have hK1 : K ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h3
    norm_num at h3
  haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
  haveI := hKp
  exact Group.IsPerfect.not_isSolvable K hKs

theorem eq_A_of_normal {K : Subgroup G22} {k : Fin 4} (hKA : K ≤ A k)
    (hn : (K.subgroupOf (A k)).Normal) (hK1 : K ≠ ⊥) : K = A k := by
  obtain ⟨e⟩ := nonempty_A_equiv k
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (A k) := e.isSimpleGroup
  haveI := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf (A k)) with h | h
  · exfalso
    apply hK1
    rw [eq_bot_iff]
    intro g hg
    have : (⟨g, hKA hg⟩ : A k) ∈ K.subgroupOf (A k) := Subgroup.mem_subgroupOf.mpr hg
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · exact le_antisymm hKA (Subgroup.subgroupOf_eq_top.mp h)

section Core

theorem sigGenConcl_core {K Q : Subgroup G22} (hh : SigGenHyp P0 K Q (zpowers X)) :
    SigGenConcl P0 K := by
  classical
  have hQ3 : ¬ 3 ∣ Nat.card Q := fun h3 => (hh.inv.2.1 ⟨3, Nat.prime_three⟩ h3) rfl
  have hQC : Q ≤ centralizer ({lineE 0} : Set G22) := by
    intro q hq
    rw [mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_iff.mp (hh.cent hq) X (mem_zpowers X)
    exact this.symm
  have hQV : Q = V 0 := by
    rcases V_minimal 0 (le_V_of_not_dvd hQC hQ3) hh.inv.2.2 with h | h
    · exfalso
      apply hh.nontriv
      rw [h, Subgroup.commutator_bot_right]
      exact bot_le
    · exact h
  have hK1 : K ≠ ⊥ := by
    rintro rfl
    have := hh.three
    rw [Subgroup.card_bot] at this
    norm_num at this
  have hSN : P0 ⊔ V 0 ≤ normalizer (K : Set G22) := sup_le hh.normK (hQV ▸ hh.normQ)
  have hKN : K ≤ normalizer (K : Set G22) := Subgroup.le_normalizer
  have hKn : (K.subgroupOf (normalizer (K : Set G22))).Normal := Subgroup.normal_in_normalizer
  have hsig : ∀ i : Fin 4, V i ≤ K → V i ≤ sSup {W : Subgroup G22 | W ≤ K ∧
      W ∈ invariantPiSubgroups ⊤ P0 (piCompl 3) ∧ W = ⁅W, P0⁆} := fun i hi =>
    le_sSup (V_mem_sig i hi)
  have hA : ∀ k : Fin 4, normalizer (K : Set G22) = A k → SigGenConcl P0 K := by
    intro k hNA
    have hKA : K ≤ A k := hNA ▸ hKN
    rw [hNA] at hKn
    have hKeq := eq_A_of_normal hKA hKn hK1
    unfold SigGenConcl
    exact hKeq.le.trans (sup_le (hsig _ (hKeq ▸ (le_sup_left : V (pairFst k) ≤ A k)))
      (hsig _ (hKeq ▸ (le_sup_right : V (pairSnd k) ≤ A k))))
  rcases Certificates.certificate148010 _ hSN with hNt | hNA | hNA | hNN | hdvd
  ·
    haveI : K.Normal := Subgroup.normalizer_eq_top_iff.mp hNt
    haveI : IsSimpleGroup G22 := fam_m22_simplicity.2.2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · exact absurd h hK1
    · unfold SigGenConcl
      have htop := sup_eq_top_of_seven 0 ((P0_le_A 0).trans Subgroup.le_normalizer)
        (by rw [card_A]; norm_num)
      have hV : ∀ i : Fin 4, V i ≤ K := fun i => h ▸ le_top
      refine h.le.trans (htop.ge.trans (sup_le ?_ ?_))
      · exact sup_le (hsig 0 (hV 0)) (hsig 1 (hV 1))
      · exact sup_le (hsig 0 (hV 0)) (hsig 2 (hV 2))
  · exact hA 0 hNA
  · exact hA 1 hNA
  ·
    exfalso
    have hKR : K ≤ normalizer (R 0 : Set G22) := hNN ▸ hKN
    apply hh.nontriv
    obtain ⟨-, -, -, hmax, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
    set N0 : Subgroup K := (R 0).subgroupOf K with hN0
    have hN0n : N0.Normal := ⟨fun n hn k => by
      rw [hN0, Subgroup.mem_subgroupOf] at hn ⊢
      exact (mem_normalizer_iff.mp (hKR k.2) n).mp hn⟩
    have hN0p : IsPGroup 2 N0 := fun g => by
      obtain ⟨m, hm⟩ := isPGroup_R 0 ⟨((g : K) : G22), Subgroup.mem_subgroupOf.mp g.2⟩
      exact ⟨m, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hm))⟩
    have hN0s : Group.IsSolvable N0 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := hN0p.isNilpotent
      infer_instance
    have hN03 : ¬ 3 ∣ Nat.card N0 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := N0)).1 hN0p
      rw [hm]
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at this
    have hN0θ := hmax N0 hN0n hN0s hN03
    rw [Subgroup.commutator_le]
    intro k hk q hq
    have hkq : ⁅k, q⁆ ∈ K := by
      have : q * k⁻¹ * q⁻¹ ∈ K := (mem_normalizer_iff.mp (hh.normQ hq) k⁻¹).mp (inv_mem hk)
      have e : ⁅k, q⁆ = k * (q * k⁻¹ * q⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem hk this
    have hqR : q ∈ R 0 := (le_sup_left : V 0 ≤ R 0) (hQV ▸ hq)
    have hkqR : ⁅k, q⁆ ∈ R 0 := by
      have : k * q * k⁻¹ ∈ R 0 := (mem_normalizer_iff.mp (hKR hk) q).mp hqR
      rw [commutatorElement_def]
      exact mul_mem this (inv_mem hqR)
    exact ⟨⟨_, hkq⟩, hN0θ (Subgroup.mem_subgroupOf.mpr hkqR), rfl⟩
  · exact (false_of_card_dvd hdvd hKN hh.perf hh.three).elim

theorem GJ_mem_normalizer : GJ ∈ normalizer (P0 : Set G22) := by
  have h := E.mem_normalizer_of_conj 1 1 1 2 CFSG.RankThree.Asc83Table.M22.GJ_X
    CFSG.RankThree.Asc83Table.M22.GJ_Y
  rwa [E.closure_range] at h

theorem sigGenConcl_P0 {K Q D : Subgroup G22} (hh : SigGenHyp P0 K Q D) : SigGenConcl P0 K := by
  have hD3 : Nat.card D = 3 := by
    have h := hh.hyp.2
    rw [card_P0] at h
    omega
  obtain ⟨i, hi⟩ := exists_zpowers_eq hh.hyp.1 hD3
  have hlt : lineA i < 3 ∧ lineB i < 3 := by fin_cases i <;> decide
  have hne' : ¬ (lineA i = 0 ∧ lineB i = 0) := by fin_cases i <;> decide
  have hne : ((⟨lineA i, hlt.1⟩ : Fin 3), (⟨lineB i, hlt.2⟩ : Fin 3)) ≠ (0, 0) := by
    intro h
    apply hne'
    simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_zero] at h
    exact h
  obtain ⟨k, l, hkl⟩ := conj_x_facts _ _ hne
  set n : G22 := GI ^ (k : ℕ) * GJ ^ (l : ℕ) with hn
  have hnN : n ∈ normalizer (P0 : Set G22) :=
    mul_mem (pow_mem GI_mem_normalizer _) (pow_mem GJ_mem_normalizer _)
  have hnX : n * X * n⁻¹ = lineE i := by
    rw [lineE_eq]
    apply Subtype.ext
    simp only [hn, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
    exact hkl
  set f : G22 →* G22 := (MulAut.conj n).toMonoidHom with hf
  have hfi : Function.Injective f := (MulAut.conj n).injective
  have hfr : ∀ H : Subgroup G22, H ≤ f.range := fun H g _ =>
    ⟨n⁻¹ * g * n, by simp [hf, MulAut.conj_apply]; group⟩
  have hP0 : P0.comap f = P0 := by
    ext g
    rw [Subgroup.mem_comap]
    change n * g * n⁻¹ ∈ P0 ↔ g ∈ P0
    exact (mem_normalizer_iff.mp hnN g).symm
  have he : (MulAut.conj n).symm.toMonoidHom (lineE i) = X := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, ← hnX]
    group
  have hDX : D.comap f = zpowers X := by
    rw [hi, hf, Subgroup.comap_equiv_eq_map_symm', MonoidHom.map_zpowers, he]
  refine SigGenConcl.of_comap f hfi (hfr P0) (hfr K) ?_
  have hh' := hh.comap f hfi (hfr P0) (hfr K) (hfr Q)
  rw [hP0, hDX] at hh'
  rw [hP0]
  exact sigGenConcl_core hh'

theorem sigGenIn_m22 : SigGenIn148 G22 := by
  intro P K Q D _ hP9 hh
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 ⟨MulEquiv.refl G22⟩ hP9
  set f : G22 →* G22 := ψ.toMonoidHom with hf
  have hfi : Function.Injective f := ψ.injective
  have hfr : ∀ H : Subgroup G22, H ≤ f.range := fun H g _ => ⟨ψ.symm g, by simp [hf]⟩
  have hP0 : P.comap f = P0 := by
    rw [← hψ]
    exact Subgroup.comap_map_eq_self_of_injective hfi P0
  refine SigGenConcl.of_comap f hfi (hfr P) (hfr K) ?_
  have hh' := hh.comap f hfi (hfr P) (hfr K) (hfr Q)
  rw [hP0] at hh' ⊢
  exact sigGenConcl_P0 hh'

end Core

theorem threeSolvIn_m22 :
    ThreeSolvIn148 G22 := by
  intro P V _ hP9 hV3 hPV
  have hV : V ∈ invariantPiSubgroups ⊤ P (piCompl 3) := by
    refine ⟨le_top, ?_, hPV⟩
    intro q hq
    change (q : ℕ) ≠ 3
    intro h3
    rw [h3] at hq
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hV3 hq
  have h2 := m22_isPGroup_of_mem_invariant ⟨MulEquiv.refl G22⟩ hP9 hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h2.isNilpotent
  infer_instance

theorem rankTwo_m22 : RankTwo148 G22 := by
  intro E _ hE
  have h := Subgroup.card_subgroup_dvd_card E
  rw [hE, card_M22] at h
  norm_num at h

theorem inspIn148_m22 :
    InspIn148 NativeSporadic.M22 := by
  refine ⟨CFSG.Sporadic.Schreier.m22_center_eq_bot', fun α hα => ?_, threeSolvIn_m22,
    rankTwo_m22, sigGenIn_m22⟩
  have hodd : Odd (orderOf α) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hα)
  obtain ⟨g, rfl⟩ := CFSG.Quasithin.H13.NQCat.T3.oddInner_of_card_le
    CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card α hodd
  exact ⟨g, rfl⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.M22

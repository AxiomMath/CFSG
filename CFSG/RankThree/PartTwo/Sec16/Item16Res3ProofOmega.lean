module

public import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofOmega
public import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofDL
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def KS1616SzOdd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsKGroup Y → ∀ (X : Subgroup Y) (c : Y),
    ¬ 3 ∣ Nat.card X → c ∈ Subgroup.normalizer (X : Set Y) → c ^ 3 = 1 →
      Odd (Nat.card (X ⊓ Subgroup.centralizer ({c} : Set Y) : Subgroup Y)) →
        Group.IsSolvable X

@[expose] noncomputable def Step1616OmegaSolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Sec8.IsZ3PGLThreePi ↥(lBarA c L A) → ∀ b ∈ A, b ≠ 1 →
      Group.IsSolvable ↥(pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊓
        Subgroup.centralizer ({c} : Set G))

namespace Res3Omega

variable {G : Type} [Group G] [Finite G]

theorem le_thetaCen_of_isSolvable {X : Set G} {N : Subgroup G}
    (hNX : N ≤ Subgroup.centralizer X)
    (hnorm : Subgroup.centralizer X ≤ Subgroup.normalizer (N : Set G))
    (hsol : Group.IsSolvable N) (h3 : ¬ 3 ∣ Nat.card N) : N ≤ thetaCen X := by
  set C := Subgroup.centralizer X with hC
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
  set N' := N.subgroupOf C with hN'
  have e : N' ≃* N := Subgroup.subgroupOfEquivOfLe hNX
  have hN'n : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm g.2) n).mp hn
  have hsol' : Group.IsSolvable N' :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have h3' : ¬ 3 ∣ Nat.card N' := by rwa [Nat.card_congr e.toEquiv]
  have hle := hmax N' hN'n hsol' h3'
  rw [thetaCen, inSubgroup, ← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

omit [Finite G] in
theorem mem_centralizer_sup {b c x : G} (hb : x ∈ Subgroup.centralizer ({b} : Set G))
    (hc : x ∈ Subgroup.centralizer ({c} : Set G)) :
    x ∈ Subgroup.centralizer
      ((Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := by
  have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤
      Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hb).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem isKGroup_centralizer (h : TheoremFourHyp G) {b : G} (hb1 : b ≠ 1) :
    CFSG.IsKGroup ↥(Subgroup.centralizer ({b} : Set G)) := by
  have hCtop : Subgroup.centralizer ({b} : Set G) ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.isSimpleGroup
    have hcen : b ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({b} : Set G) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hbot | htop'
    · exact hb1 (by rw [hbot] at hcen; exact hcen)
    · obtain ⟨x, y, hxy⟩ := h.nonabelian
      apply hxy
      have hx : x ∈ Subgroup.center G := htop' ▸ Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
  exact (h.sectionFourHyp hCtop).kGroup

end Res3Omega

open Res3Omega Proof169 Proof1613Res

theorem step1616OmegaSz_of_solv (hSolv : Step1616OmegaSolv) (hK : KS1616SzOdd) :
    Step1616OmegaSz := by
  intro G _ _ A c L h hPGL hΩ hoddB S hS b hbB hb1 hoddb hbΩ hTO
  have hA := h.isElemAbelian
  have hA27 : Nat.card A = 27 := h.card_eq
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.toSec13Data.ne_one
  have hBA : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left
  have hbA : b ∈ A := hBA hbB
  have hbc : b ∉ Subgroup.zpowers c := by
    intro hb
    apply hbΩ
    rw [zpowers_eq_of_mem_of_ne_one h.card_zpowers hb hb1, hΩ]
    rfl
  obtain ⟨d, hdAL, hd1, hALd⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
    (Proof1614Trans.card_inf_eq_three_of_pgl h.toSec13Data hPGL)
  have hdA : d ∈ A := (Subgroup.mem_inf.mp hdAL).1
  have hB9 : Nat.card (Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) ≤ 9 := by
    rw [hALd]
    exact card_sup_zpowers_le (h.commute hcA hdA) h.card_zpowers
      (by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        rw [Nat.card_zpowers, orderOf_eq_prime (hA.2 d hdA) hd1])
  have hBeq : Subgroup.zpowers c ⊔ Subgroup.zpowers b = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    sup_eq_of_mem hA hA27 hBA hB9 (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) hbB hc1 hbc
  set X := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) with hX
  set N := X ⊓ Subgroup.centralizer ({c} : Set G) with hN
  have hNsol : Group.IsSolvable N := hSolv G A c L h hPGL b hbA hb1
  have h3X : ¬ 3 ∣ Nat.card X := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have h3N : ¬ 3 ∣ Nat.card N := fun h3 => h3X (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hNB : N ≤ Subgroup.centralizer
      ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G) := by
    intro x hx
    rw [← hBeq, sup_comm]
    exact mem_centralizer_sup ((pPrimeCoreOf_le 3 _) hx.1) hx.2
  have hBN : Subgroup.centralizer ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (N : Set G) := by
    intro g hg
    have hgb : g ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB) hg
    have hgc : g ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))) hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pPrimeCoreOf 3 _ hgb, Subgroup.le_normalizer hgc⟩
  have hNθ : N ≤ thetaCen ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G) :=
    le_thetaCen_of_isSolvable hNB hBN hNsol h3N
  have hNodd : Odd (Nat.card N) := Odd.of_dvd_nat hoddB (Subgroup.card_dvd_of_le hNθ)
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  have hKCb : CFSG.IsKGroup ↥Cb := isKGroup_centralizer h.toTheoremFourHyp hb1
  have hcCb : c ∈ Cb := Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.is_comm.comm ⟨c, hcA⟩ ⟨b, hbA⟩))
  set c' : ↥Cb := ⟨c, hcCb⟩ with hc'
  set X' := CFSG.pPrimeCore 3 ↥Cb with hX'
  have hXX' : X = X'.map Cb.subtype := rfl
  have hX'3 : ¬ 3 ∣ Nat.card X' := by
    rw [Nat.card_congr (X'.equivMapOfInjective Cb.subtype Cb.subtype_injective).toEquiv,
      ← hXX']
    exact h3X
  have hc'N : c' ∈ Subgroup.normalizer (X' : Set ↥Cb) := by
    have hXn : X'.Normal := CFSG.pPrimeCore_normal
    refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => hXn.conj_mem n hn c', fun hn => ?_⟩
    have := hXn.conj_mem _ hn c'⁻¹
    rwa [show c'⁻¹ * (c' * n * c'⁻¹) * c'⁻¹⁻¹ = n by group] at this
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using hA.2 c hcA)
  have hmap : (X' ⊓ Subgroup.centralizer ({c'} : Set ↥Cb)).map Cb.subtype = N := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      have hy'X : y' ∈ X' := (Subgroup.mem_inf.mp hy').1
      have hy'c : y' ∈ Subgroup.centralizer ({c'} : Set ↥Cb) := (Subgroup.mem_inf.mp hy').2
      refine Subgroup.mem_inf.mpr ⟨⟨y', hy'X, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy'c ⊢
      exact congrArg Subtype.val hy'c
    · intro hy
      obtain ⟨hyX, hyc⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨y', hy'X, rfl⟩ := hyX
      refine ⟨y', Subgroup.mem_inf.mpr ⟨hy'X, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
      exact Subtype.ext hyc
  have hodd' : Odd (Nat.card (X' ⊓ Subgroup.centralizer ({c'} : Set ↥Cb) : Subgroup ↥Cb)) := by
    rw [← Subgroup.card_map_of_injective Cb.subtype_injective, hmap]
    exact hNodd
  have hX'sol : Group.IsSolvable X' := hK ↥Cb hKCb X' c' hX'3 hc'N hc'3 hodd'
  have hXsol : Group.IsSolvable X := by
    rw [hXX']
    let e := X'.equivMapOfInjective Cb.subtype Cb.subtype_injective
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact hTO.trans (pPrimeCoreOf_le_inSubgroup_theta hXsol)

end CFSG.RankThree.PartTwo.Sec16

module

public import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalance
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofPGL
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartOne.S15K.AutLayer

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KS143LBalSec4 : Prop :=
  ∀ (C : Type) [Group C] [Finite C], SectionFourHyp C → ∀ b : C, b ^ 3 = 1 →
    Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pPrimeCore 3 C) b} : Set (C ⧸ CFSG.pPrimeCore 3 C))))

namespace Res2

theorem le_pPrimeCore_of_solvable {C : Type} [Group C] [Finite C] {b : C} (hb3 : b ^ 3 = 1)
    (hS : Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pPrimeCore 3 C) b} : Set (C ⧸ CFSG.pPrimeCore 3 C)))))
    {M : Subgroup C} (hMC : M ≤ Subgroup.centralizer ({b} : Set C))
    (hMN : Subgroup.centralizer ({b} : Set C) ≤ Subgroup.normalizer (M : Set C))
    (hM3 : ¬ 3 ∣ Nat.card M) {J : Subgroup C} (hJM : J ≤ M) (hJp : Group.IsPerfect J) :
    J ≤ CFSG.pPrimeCore 3 C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pPrimeCore 3 C with hO
  set ψ := QuotientGroup.mk' O with hψ
  set bb := ψ b with hbb
  set Mb := M.map ψ with hMb
  have hO3 : ¬ 3 ∣ Nat.card ψ.ker := by
    rw [hψ, QuotientGroup.ker_mk', ← Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact CFSG.pPrimeCore_coprime_card
  have hMbC : Mb ≤ Subgroup.centralizer ({bb} : Set (C ⧸ O)) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hbb, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hMC hm)]
  have hMbN : Subgroup.centralizer ({bb} : Set (C ⧸ O)) ≤
      Subgroup.normalizer (Mb : Set (C ⧸ O)) := by
    intro t ht
    have hσ3 : (MulAut.conj b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
    have hσβ : ∀ y, ψ (MulAut.conj b y) = MulAut.conj bb (ψ y) := fun y => by
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    have htfix : MulAut.conj bb t = t := by
      rw [MulAut.conj_apply]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp ht
      rw [← h1, mul_inv_cancel_right]
    obtain ⟨x, hx, rfl⟩ := CFSG.RankThree.PartOne.S15K.exists_fixed_lift Nat.prime_three ψ
      (QuotientGroup.mk'_surjective O) hO3 (MulAut.conj b) hσ3 (MulAut.conj bb) hσβ htfix
    have hxC : x ∈ Subgroup.centralizer ({b} : Set C) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply] at hx
      calc x * b = b * x * b⁻¹ * b := by rw [hx]
        _ = b * x := by group
    exact Subgroup.le_normalizer_map ψ ⟨x, hMN hxC, rfl⟩
  have hMb3 : Nat.Coprime 3 (Nat.card Mb) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hM3 (h3.trans (Subgroup.card_map_dvd M ψ))
  have hMbS : Mb ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({bb} : Set (C ⧸ O))) :=
    le_pPrimeCoreOf hMbC hMbN hMb3
  set Jb := J.map ψ with hJb
  have hJbS : Jb ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({bb} : Set (C ⧸ O))) :=
    (Subgroup.map_mono hJM).trans hMbS
  have hJbsol : Group.IsSolvable Jb :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJbS)
  have hJbp : Group.IsPerfect Jb :=
    Group.IsPerfect.ofSurjective (f := ψ.subgroupMap J) (ψ.subgroupMap_surjective J)
  have hJb1 : Jb = ⊥ := by
    by_contra hne
    have : Nontrivial Jb := (Subgroup.nontrivial_iff_ne_bot Jb).mpr hne
    exact Group.IsPerfect.not_isSolvable Jb hJbsol
  intro j hj
  have h1 : ψ j ∈ Jb := ⟨j, hj, rfl⟩
  rw [hJb1, Subgroup.mem_bot, hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end Res2

open Res2

theorem step143BalanceSz_of_sec4 (hbal : KS143LBalSec4) : Step143BalanceSz := by
  intro G _ _ A c L h a ha ha1 _ B hB haB J hJ _
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := h.isE27'
  have ha3 : a ^ 3 = 1 := hD.isElemAbelian.2 a ha
  have hac : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha3 ha1
  obtain ⟨b, hbB, -, hBeq⟩ := exists_closure_pair_of_mem hA hB haB hac
  have hbA : b ∈ A := hB.1 hbB
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  have hbCa : b ∈ Ca := Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hbA).symm
  have hCaTop : Ca ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.isSimpleGroup
    have hcen : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Ca := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hb | ht
    · exact ha1 (by rw [hb] at hcen; exact hcen)
    · obtain ⟨x, y, hxy⟩ := h.nonabelian
      apply hxy
      have hx : x ∈ Subgroup.center G := ht ▸ Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
  have hS4 : SectionFourHyp Ca := h.toTheoremFourHyp.sectionFourHyp hCaTop
  have hCB : ∀ x : G, x ∈ Subgroup.centralizer (B : Set G) ↔
      x ∈ Ca ∧ x ∈ Subgroup.centralizer ({b} : Set G) := by
    intro x
    rw [hBeq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff, hCa,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      exact ⟨(hx a (by simp)).symm, (hx b (by simp)).symm⟩
    · rintro ⟨hxa, hxb⟩ y (rfl | rfl)
      · exact hxa.symm
      · exact hxb.symm
  set MB := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hMB
  have hMBCa : MB ≤ Ca := fun x hx => ((hCB x).mp (pPrimeCoreOf_le 3 _ hx)).1
  set b' : Ca := ⟨b, hbCa⟩ with hb'
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 b hbA)
  have hcent : ∀ x : Ca, x ∈ Subgroup.centralizer ({b'} : Set Ca) ↔
      (x : G) ∈ Subgroup.centralizer ({b} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
  have hJM : J ≤ MB := le_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect (J.subgroupOf Ca) := by
    obtain ⟨hJMsub, hJθ⟩ := mem_thetaComponentsIn_iff.mp hJ
    have hp : Group.IsPerfect (J.subgroupOf MB) := hJθ.1
    have e1 : J.subgroupOf MB ≃* J.subgroupOf Ca :=
      (Subgroup.subgroupOfEquivOfLe hJMsub).trans
        (Subgroup.subgroupOfEquivOfLe (hJMsub.trans hMBCa)).symm
    exact Group.IsPerfect.ofSurjective (f := e1.toMonoidHom) e1.surjective
  have hMC : MB.subgroupOf Ca ≤ Subgroup.centralizer ({b'} : Set Ca) := fun x hx =>
    (hcent x).mpr ((hCB x).mp (pPrimeCoreOf_le 3 _ (Subgroup.mem_subgroupOf.mp hx))).2
  have hMN : Subgroup.centralizer ({b'} : Set Ca) ≤
      Subgroup.normalizer ((MB.subgroupOf Ca : Subgroup Ca) : Set Ca) := by
    intro x hx
    have hxB : (x : G) ∈ Subgroup.centralizer (B : Set G) := (hCB x).mpr ⟨x.2, (hcent x).mp hx⟩
    have hxN := le_normalizer_pPrimeCoreOf 3 _ hxB
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hxN (y : G)
  have hM3 : ¬ 3 ∣ Nat.card (MB.subgroupOf Ca) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMBCa).toEquiv,
      ← Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact coprime_card_pPrimeCoreOf 3 _
  have hle := le_pPrimeCore_of_solvable hb'3 (hbal Ca hS4 b' hb'3) hMC hMN hM3
    (fun y hy => Subgroup.mem_subgroupOf.mpr (hJM (Subgroup.mem_subgroupOf.mp hy))) hJp
  intro x hx
  have hxCa : x ∈ Ca := hMBCa (hJM hx)
  exact ⟨⟨x, hxCa⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end CFSG.RankThree.PartTwo.Sec14

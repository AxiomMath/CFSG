module

public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Core
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.GroupTheory.PCoreSurjective
import CFSG.Holt.Induced
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.Quasithin.H13.U3S1347H
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC9R96

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (toImg9 xbar9 wbar9 toImg9_surjective
  mem_ker_toImg9)

variable {G : Type} [Group G] [Finite G]

namespace Core

variable {D : Data G} {Y H : Subgroup G} {q : ℕ}

theorem opp_inf_I9_le_pCoreOf (S : Core D Y H q) :
    Opp 3 Y ⊓ F09.I9 H ≤ pCoreOf 2 (Opp 3 Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.Quasithin.H13.U3.inf_le_pCoreOf_of_coprime_three
    (S.opp_le_H.trans (SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H))
    (SteinbergBM.coprime_card_inSubgroup_pPrimeCore H)
    S.isSimpleGroup_bar2_opp S.three_dvd_card_bar2_opp

theorem isPGroup_ker_toImg9 (S : Core D Y H q) (hXH : Opp 3 Y ≤ H) :
    IsPGroup 2 (toImg9 hXH).ker := by
  have hO : IsPGroup 2 ↥(pCoreOf 2 (Opp 3 Y)) := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact CFSG.pCore_isPGroup.map _
  intro g
  have hg : ((g : ↥(Opp 3 Y)) : G) ∈ pCoreOf 2 (Opp 3 Y) :=
    S.opp_inf_I9_le_pCoreOf ⟨(g : ↥(Opp 3 Y)).2, (mem_ker_toImg9 hXH).1 g.2⟩
  obtain ⟨k, hk⟩ := hO ⟨_, hg⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

theorem isL2Odd_bar2_xbar9 (S : Core D Y H q) : IsL2Odd (Bar2 (xbar9 Y H)) q := by
  have hXH : Opp 3 Y ≤ H := S.opp_le_H
  have hle : F09.img9 H (Opp 3 Y) ≤ F09.img9 H (F09.L9 Y H) :=
    Subgroup.map_mono fun y hy => F09.opp_le_L9 Y H hy
  obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (toImg9 hXH)
    (toImg9_surjective hXH) (S.isPGroup_ker_toImg9 hXH)
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    (e.trans (UC6S846.bar2Equiv (Subgroup.subgroupOfEquivOfLe hle)).symm) S.shape_opp

theorem exists_le_opp_card_eq_img9_eq (S : Core D Y H q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Qb : Subgroup (F09.Hbar9 H)} (hQ : IsPGroup p Qb) (hQX : Qb ≤ F09.img9 H (Opp 3 Y)) :
    ∃ A : Subgroup G, A ≤ Opp 3 Y ∧ Nat.card A = Nat.card Qb ∧ F09.img9 H A = Qb := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXH : Opp 3 Y ≤ H := S.opp_le_H
  set ψ := toImg9 hXH
  set Qc : Subgroup ↥(F09.img9 H (Opp 3 Y)) := Qb.subgroupOf (F09.img9 H (Opp 3 Y))
  have eQ : ↥Qc ≃* ↥Qb := Subgroup.subgroupOfEquivOfLe hQX
  obtain ⟨P, -, -, hP, hPQ⟩ := CFSG.Holt.exists_isPGroup_map_eq_of_map_le (H := ⊤) (E := ⊥) ψ
    (hQ.of_equiv eQ.symm)
    (by rw [Subgroup.map_top_of_surjective ψ (toImg9_surjective hXH)]; exact le_top)
    IsPGroup.of_bot bot_le (by rw [Subgroup.map_bot]; exact bot_le)
  have hcop : p.Coprime (Nat.card ψ.ker) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (S.isPGroup_ker_toImg9 hXH)
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  obtain ⟨e⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_pGroup_equiv_image p hp ψ hcop P hP
  refine ⟨P.map (Opp 3 Y).subtype, Subgroup.map_subtype_le P, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Opp 3 Y).subtype_injective, Nat.card_congr e.toEquiv, hPQ,
      Nat.card_congr eQ.toEquiv]
  · ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
      have h1 : ψ x ∈ Qc := hPQ ▸ Subgroup.mem_map_of_mem ψ hx
      have hxy' : Subgroup.inclusion hXH x = y := Subtype.ext hxy
      have h2 : ((ψ x : ↥(F09.img9 H (Opp 3 Y))) : F09.Hbar9 H) =
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) y := by
        rw [← hxy']
        rfl
      rw [← h2]
      exact Subgroup.mem_subgroupOf.1 h1
    · intro hz
      have hz' : (⟨z, hQX hz⟩ : ↥(F09.img9 H (Opp 3 Y))) ∈ P.map ψ := by
        rw [hPQ]
        exact Subgroup.mem_subgroupOf.2 hz
      obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 hz'
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hXH x,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, hx, rfl⟩), congrArg Subtype.val hxz⟩

theorem normalizer_le_wbar9 (S : Core D Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Opp 3 Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M) :
    ∀ Dq : Subgroup (F09.Lbar9 Y H), Dq ≤ xbar9 Y H → Nat.card Dq = 3 →
      normalizer (Dq : Set (F09.Lbar9 Y H)) ≤ wbar9 D Y H := by
  intro Dq hDq h3 xb hxb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Lb := F09.img9 H (F09.L9 Y H)
  have hDb : Nat.card (Dq.map Lb.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective Lb.subtype_injective, h3]
  have hDbX : Dq.map Lb.subtype ≤ F09.img9 H (Opp 3 Y) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hDq hd
  obtain ⟨A, hAX, hAc, hAD⟩ := S.exists_le_opp_card_eq_img9_eq Nat.prime_three (by norm_num)
    (IsPGroup.of_card (n := 1) (by rw [hDb, pow_one])) hDbX
  rw [hDb] at hAc
  have hAH : A ≤ H := hAX.trans S.opp_le_H
  have hNA : normalizer (A : Set G) ≤ D.M :=
    hN A hAX (by rw [hAc]; exact Nat.prime_three) (by rw [hAc]; decide)
  have hA3 : IsPGroup 3 (A.subgroupOf H) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hAc, pow_one])
  have hx : (xb : F09.Hbar9 H) ∈ normalizer ((F09.img9 H A : Subgroup (F09.Hbar9 H)) :
      Set (F09.Hbar9 H)) := by
    rw [hAD]
    exact Subgroup.le_normalizer_map Lb.subtype ⟨xb, hxb, rfl⟩
  obtain ⟨g, hg, hgx⟩ := CFSG.AGLEmbedding.exists_mem_normalizer_mk_eq_of_mem_normalizer
    Nat.prime_three (CFSG.pPrimeCore 3 ↥H) CFSG.pPrimeCore_coprime_card hA3 hx
  have hgM : (g : G) ∈ D.M := by
    apply hNA
    have := Subgroup.le_normalizer_map H.subtype ⟨g, hg, rfl⟩
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAH] at this
  rw [wbar9, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 ⟨g.2, hgM⟩, hgx⟩

end Core

end CFSG.LocalAnalysis.UniquenessCase.UC9R96

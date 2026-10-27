module

public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.Goldschmidt.Steps.G37Quot
public import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport

public section

namespace CFSG.RankThree.PartTwo.Sec11.Eii

open CFSG CFSG.Open CFSG.Goldschmidt

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_of_selfCentralizing {p : ℕ} (hp : p.Prime) {A N U V : Subgroup G}
    (hA : IsPGroup p A) (hN : ¬ p ∣ Nat.card N) (hAN : A ≤ Subgroup.normalizer (N : Set G))
    (hVN : V ≤ N) (hNU : N ≤ Subgroup.normalizer (U : Set G))
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hNV : N ≤ Subgroup.normalizer (V : Set G))
    (hVA : ⁅V, A⁆ ≤ U)
    (hself : ∀ x ∈ N, (∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ U) → x ∈ V) :
    ⁅N, A⁆ ≤ U := by
  have hNA : ⁅N, A⁆ ≤ N := Subgroup.le_normalizer_iff_commutator_le_left.mp hAN
  have h1 : ⁅⁅A, V⁆, N⁆ ≤ U := by
    rw [Subgroup.commutator_comm A V]
    exact (Subgroup.commutator_mono hVA le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hNU)
  have h2 : ⁅⁅V, N⁆, A⁆ ≤ U := by
    have hVN' : ⁅V, N⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hNV
    exact (Subgroup.commutator_mono hVN' le_rfl).trans hVA
  have h3 : ⁅⁅N, A⁆, V⁆ ≤ U :=
    Sec6.three_subgroups_mod hAU (hVN.trans hNU) hNU h1 h2
  have h4 : ⁅N, A⁆ ≤ V := by
    intro x hx
    refine hself x (hNA hx) fun v hv => ?_
    exact h3 (Subgroup.commutator_mem_commutator hx hv)
  rw [← CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp A N hA hN hAN]
  exact (Subgroup.commutator_mono h4 le_rfl).trans hVA

omit [Finite G] in
theorem le_normalizer_oddCoreOf {N : Subgroup G} :
    Subgroup.normalizer (N : Set G) ≤ Subgroup.normalizer (oddCoreOf N : Set G) := by
  intro g hg
  refine RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq ?_
  rw [← Sec8.oddCoreOf_map_conj',
    RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer hg]

omit [Finite G] in
theorem le_normalizer_oddCoreOf_self (N : Subgroup G) :
    N ≤ Subgroup.normalizer (oddCoreOf N : Set G) :=
  Subgroup.le_normalizer.trans le_normalizer_oddCoreOf

omit [Finite G] in
theorem le_normalizer_preOf {N : Subgroup G} (W : Subgroup (N ⧸ goldschmidtOddCore N))
    [W.Normal] : N ≤ Subgroup.normalizer (preOf N W : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨h, hh⟩ * v * ⟨h, hh⟩⁻¹, ?_, rfl⟩
    change QuotientGroup.mk' (goldschmidtOddCore N) (⟨h, hh⟩ * v * ⟨h, hh⟩⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact ‹W.Normal›.conj_mem _ hv _
  · rintro ⟨v, hv, hvy⟩
    have hy : y = (⟨h, hh⟩⁻¹ * v * ⟨h, hh⟩ : N) := by
      have hvy' : (v : G) = h * y * h⁻¹ := hvy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hvy']
      group
    refine ⟨⟨h, hh⟩⁻¹ * v * ⟨h, hh⟩, ?_, hy.symm⟩
    change QuotientGroup.mk' (goldschmidtOddCore N) (⟨h, hh⟩⁻¹ * v * ⟨h, hh⟩) ∈ W
    rw [map_mul, map_mul, map_inv]
    have := ‹W.Normal›.conj_mem _ hv (QuotientGroup.mk' (goldschmidtOddCore N) ⟨h, hh⟩)⁻¹
    rwa [inv_inv] at this

theorem mem_preOf_pCore_of_commutator_mem {N : Subgroup G} (hNs : Group.IsSolvable N) {x : G}
    (hx : x ∈ N)
    (h : ∀ v ∈ preOf N (pCore 2 (N ⧸ goldschmidtOddCore N)),
      x * v * x⁻¹ * v⁻¹ ∈ oddCoreOf N) :
    x ∈ preOf N (pCore 2 (N ⧸ goldschmidtOddCore N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (goldschmidtOddCore N) with hπ
  have hQs : Group.IsSolvable (N ⧸ goldschmidtOddCore N) := inferInstance
  have hcore : pPrimeCore 2 (N ⧸ goldschmidtOddCore N) = ⊥ := by
    rw [← goldschmidtOddCore_eq_pPrimeCore]
    exact goldschmidtOddCore_quotient_eq_bot N
  have hcent : π ⟨x, hx⟩ ∈ Subgroup.centralizer
      (pCore 2 (N ⧸ goldschmidtOddCore N) : Set (N ⧸ goldschmidtOddCore N)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore N) q
    have hnV : (n : G) ∈ preOf N (pCore 2 (N ⧸ goldschmidtOddCore N)) := ⟨n, hq, rfl⟩
    obtain ⟨o, ho, hoe⟩ := h n hnV
    have ho' : o = ⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹ * n⁻¹ := Subtype.ext hoe
    have h1 : π (⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹ * n⁻¹) = 1 := by
      rw [← ho', hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ho
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π n * π ⟨x, hx⟩ = (π ⟨x, hx⟩ * π n * (π ⟨x, hx⟩)⁻¹ * (π n)⁻¹)⁻¹ *
          (π ⟨x, hx⟩ * π n) := by group
      _ = π ⟨x, hx⟩ * π n := by rw [h1, inv_one, one_mul]
  exact ⟨⟨x, hx⟩, centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hQs hcore hcent, rfl⟩

theorem preOf_pCore_le_sup {N T : Subgroup G} (hT : fusionIsSylowIn 2 T N) :
    preOf N (pCore 2 (N ⧸ goldschmidtOddCore N)) ≤ T ⊔ oddCoreOf N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPT⟩ := Sec8.exists_sylow_map_eq hT
  set Pbar := P.mapSurjective (QuotientGroup.mk'_surjective (goldschmidtOddCore N)) with hPbar
  have hTP : T.subgroupOf N = (P : Subgroup N) := by
    rw [← hPT]
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  have hbar : barOf N T = (Pbar : Subgroup (N ⧸ goldschmidtOddCore N)) := by
    rw [barOf, hTP]
    rfl
  rw [← G37.preOf_barOf' hT.1, G37.le_preOf_iff (G37.preOf_le _), G37.barOf_preOf, hbar]
  exact IsPGroup.le_sylow_of_normal pCore_isPGroup Pbar

theorem commutator_le_oddCoreOf {A N T : Subgroup G} (hA : IsPGroup 3 A)
    (hN3 : ¬ 3 ∣ Nat.card N) (hNs : Group.IsSolvable N)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hT : fusionIsSylowIn 2 T N)
    (hTA : ⁅T, A⁆ = ⊥) : ⁅N, A⁆ ≤ oddCoreOf N := by
  have hAU : A ≤ Subgroup.normalizer (oddCoreOf N : Set G) := hAN.trans le_normalizer_oddCoreOf
  have hTU : T ≤ Subgroup.normalizer (oddCoreOf N : Set G) :=
    hT.1.trans (le_normalizer_oddCoreOf_self N)
  refine commutator_le_of_selfCentralizing Nat.prime_three hA hN3 hAN (G37.preOf_le _)
    (le_normalizer_oddCoreOf_self N) hAU (le_normalizer_preOf _) ?_
    (fun x hx h => mem_preOf_pCore_of_commutator_mem hNs hx h)
  refine (Subgroup.commutator_mono (preOf_pCore_le_sup hT) le_rfl).trans ?_
  refine (Sec6.commutator_sup_le_of_le_normalizer hTU hAU).trans ?_
  rw [hTA, bot_sup_eq]

theorem odd_card_of_le_oddCoreOf {N M : Subgroup G} (hM : M ≤ oddCoreOf N) :
    Odd (Nat.card M) := by
  have h := Subgroup.card_dvd_of_le hM
  exact Odd.of_dvd_nat (Sec8.odd_card_oddCoreOf N) h

theorem commutator_eq_bot_of_le_of_sylow {A M S T : Subgroup G} (hA : IsPGroup 3 A)
    (hM3 : ¬ 3 ∣ Nat.card M) (hAM : A ≤ Subgroup.normalizer (M : Set G))
    (hS : fusionIsSylowIn 2 S M) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hSA : ⁅S, A⁆ = ⊥) (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) : ⁅T, A⁆ = ⊥ := by
  obtain ⟨S', hS', hTS', hAS'⟩ := G310.exists_invariant_sylow_containing Nat.prime_three
    Nat.prime_two hA hM3 hAM hTM hT hAT
  obtain ⟨g, hg, rfl⟩ := G310.exists_conj_of_invariant_sylows Nat.prime_three Nat.prime_two hA
    hM3 hAM hS hS' hAS hAS'
  have hAg : A.map (MulAut.conj g).toMonoidHom = A :=
    RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hg).2)
  rw [eq_bot_iff]
  calc ⁅T, A⁆ ≤ ⁅S.map (MulAut.conj g).toMonoidHom, A⁆ := Subgroup.commutator_mono hTS' le_rfl
    _ = (⁅S, A⁆).map (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.map_commutator, hAg]
    _ = ⊥ := by rw [hSA, Subgroup.map_bot]

end CFSG.RankThree.PartTwo.Sec11.Eii

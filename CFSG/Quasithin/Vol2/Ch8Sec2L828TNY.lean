module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNK
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LM1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped commutatorElement

section NY

variable {G : Type} [Group G] [Finite G]

theorem s828N_perfect_le_oTwoUpper {H Y : Subgroup G} (hYH : Y ≤ H) (hY : ⁅Y, Y⁆ = Y) :
    Y ≤ oTwoUpper H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup ↥H := Y.subgroupOf H with hK
  have hKmap : K.map H.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYH
  have hKperf : ⁅K, K⁆ = K := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hKmap, hY]
  have hRn : (oTwoUpper (⊤ : Subgroup ↥H)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_oTwoUpper ⊤))
  set R := oTwoUpper (⊤ : Subgroup ↥H) with hR
  have hP : IsPGroup 2 (↥H ⧸ R) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (⊤ : Subgroup ↥H) (Subgroup.mem_top x)
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  have : Group.IsNilpotent (↥H ⧸ R) := hP.isNilpotent
  set K' := K.map (QuotientGroup.mk' R)
  have hK' : ⁅K', K'⁆ = K' := by rw [← Subgroup.map_commutator, hKperf]
  have hKR : K ≤ R := by
    by_contra hle
    have hne : K' ≠ ⊥ := by
      intro hb
      apply hle
      rw [← QuotientGroup.ker_mk' R, ← Subgroup.map_eq_bot_iff]
      exact hb
    exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hK'
  intro y hy
  have hyK : (⟨y, hYH hy⟩ : ↥H) ∈ K := hy
  exact oTwoUpper_subgroup_map_le H (Subgroup.mem_map_of_mem H.subtype (hKR hyK))

theorem s828N_solvable_of_comm_le {K Z : Subgroup G} (hZK : Z ≤ K)
    (hKZ : ⁅K, Z⁆ ≤ pCoreOf 2 K) : Group.IsSolvable ↥Z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 ↥((pCoreOf 2 K).subgroupOf Z) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).comap_of_injective Z.subtype Z.subtype_injective
  have hcomm : commutator ↥Z ≤ (pCoreOf 2 K).subgroupOf Z := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf]
    exact hKZ (Subgroup.commutator_mem_commutator (hZK a.2) b.2)
  have hD : IsPGroup 2 ↥(commutator ↥Z) := hO2.to_le hcomm
  have : Group.IsNilpotent ↥(commutator ↥Z) := hD.isNilpotent
  exact Group.isSolvable_of_ker_le_range (commutator ↥Z).subtype (Abelianization.of (G := ↥Z))
    (by rw [Abelianization.ker_of, Subgroup.range_subtype])

theorem s828N_three_mem {U K Y : Subgroup G}
    (hrank : CFSG.Open.pRank 3 (Subgroup.normalizer (U : Set G)) ≤ 2)
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hNK : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hcc : ⁅K, Subgroup.centralizer (U : Set G)⁆ ≤ pCoreOf 2 K)
    (hnc : ∀ S : Sylow 3 ↥K, ¬ IsCyclic (S : Subgroup ↥K))
    (hYC : Y ≤ Subgroup.centralizer (U : Set G)) :
    ∀ y ∈ Y, y ^ 3 = 1 → y ∈ K := by
  intro y hy hy3
  by_contra hyK
  have hyC := hYC hy
  have hyU : y ∈ Subgroup.normalizer (U : Set G) := Subgroup.centralizer_le_normalizer _ hyC
  exact s828N_no_three hrank hKU hnc hyU (hNK hyU) hy3
    (fun x hx => hcc (Subgroup.commutator_mem_commutator hx hyC)) hyK

theorem s828N_sylow3_cyclic {U K Y : Subgroup G}
    (hrank : CFSG.Open.pRank 3 (Subgroup.normalizer (U : Set G)) ≤ 2)
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hNK : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hcc : ⁅K, Subgroup.centralizer (U : Set G)⁆ ≤ pCoreOf 2 K)
    (hnc : ∀ S : Sylow 3 ↥K, ¬ IsCyclic (S : Subgroup ↥K))
    (hYC : Y ≤ Subgroup.centralizer (U : Set G))
    (h9 : ¬ 9 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (U : Set G))) :
    ∀ S : Sylow 3 ↥Y, IsCyclic (S : Subgroup ↥Y) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro S
  by_contra hS
  have : Fact (IsPGroup 3 ↥(S : Subgroup ↥Y)) := ⟨S.isPGroup'⟩
  obtain ⟨S₁, -, hS₁card, hS₁el⟩ := CFSG.lemma_4_5_a (by norm_num : (3 : ℕ) ≠ 2) hS
  set E : Subgroup G := (S₁.map (S : Subgroup ↥Y).subtype).map Y.subtype with hEdef
  have hEcard : Nat.card E = 3 ^ 2 := by
    rw [hEdef, Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hS₁card]
  have hEY : E ≤ Y := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hmemE : ∀ e ∈ E, ∃ s ∈ S₁, e = (((s : ↥(S : Subgroup ↥Y)) : ↥Y) : G) := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  have hS3 : ∀ s ∈ S₁, s ^ 3 = 1 := fun s hs => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hS₁el.exponent_dvd_p ⟨s, hs⟩
    exact congrArg Subtype.val h
  have hEK : E ≤ K ⊓ Subgroup.centralizer (U : Set G) := by
    intro e he
    refine ⟨?_, hYC (hEY he)⟩
    obtain ⟨s, hs, rfl⟩ := hmemE e he
    refine s828N_three_mem hrank hKU hNK hcc hnc hYC _ (hEY he) ?_
    have h := hS3 s hs
    have h2 := congrArg (fun x : ↥(S : Subgroup ↥Y) => (((x : ↥Y)) : G)) h
    simpa using h2
  have h9' : 9 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (U : Set G)) := by
    have := Subgroup.card_dvd_of_le hEK
    rwa [hEcard] at this
  exact h9 h9'

end NY

end CFSG.Quasithin.H13

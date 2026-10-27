module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem515

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def L2TorusFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → LieModel X .PSL 2 2 n →
    ∀ S C : Subgroup X, IsSylowTwoOf S ⊤ → C ≤ Subgroup.normalizer (S : Set X) → C ⊓ S = ⊥ →
      C ⊔ S = Subgroup.normalizer (S : Set X) → IsCyclic ↥C ∧ Nat.card C = 2 ^ n - 1

section Helpers

variable {G : Type} [Group G]

theorem le_normalizer_subgroupOf {L A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf L ≤ Subgroup.normalizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (hAB hx) y

theorem mem_normalizer_of_mem_normalizer_subgroupOf {L B : Subgroup G} (hBL : B ≤ L) {x : ↥L}
    (hx : x ∈ Subgroup.normalizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L)) :
    (x : G) ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro g
  constructor
  · intro hg
    have h1 : (⟨g, hBL hg⟩ : ↥L) ∈ B.subgroupOf L := Subgroup.mem_subgroupOf.mpr hg
    have h2 := (hx ⟨g, hBL hg⟩).mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  · intro hg
    have hgL : g ∈ L := by
      have h1 : (x : G) * g * (x : G)⁻¹ ∈ L := hBL hg
      have h2 := L.mul_mem (L.mul_mem (L.inv_mem x.2) h1) x.2
      simpa [mul_assoc] using h2
    have h1 : x * (⟨g, hgL⟩ : ↥L) * x⁻¹ ∈ B.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hg
    have h2 := (hx ⟨g, hgL⟩).mpr h1
    rw [Subgroup.mem_subgroupOf] at h2
    exact h2

end Helpers

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem isSylowTwoOf_borel (h : Hyp5_0_1 G T M L n) : IsSylowTwoOf (T ⊓ L) (borelL T L) := by
  have hS : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hS le_sup_left h.sup_le_normalizer
  exact A4.isSylowTwoOf_mono hSL (inf_le_borel T L) inf_le_left

theorem borelL_eq_sup (h : Hyp5_0_1 G T M L n) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) : D ⊔ (T ⊓ L) = borelL T L :=
  sup_eq_of_isHall_isSylow hD h.isSylowTwoOf_borel

theorem inf_eq_bot_of_isHall {D S : Subgroup G} {X : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D X) (hS : IsPGroup 2 S) : D ⊓ S = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hS
  rw [hm]
  exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hD.2.1)

theorem isCyclic_card_of_isHall (h : Hyp5_0_1 G T M L n) (hF : L2TorusFact) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) : IsCyclic ↥D ∧ Nat.card D = 2 ^ n - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDB : D ≤ borelL T L := hD.1
  have hDL : D ≤ L := hDB.trans inf_le_left
  have hTLL : T ⊓ L ≤ L := inf_le_right
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set D' : Subgroup ↥L := D.subgroupOf L with hD'
  set S' : Subgroup ↥L := (T ⊓ L).subgroupOf L with hS'
  have hSyl : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf le_sup_right) le_sup_left h.sup_le_normalizer
  have hPS : CFSG.pCore 2 ↥L ≤ S' := by
    intro x hx
    rw [hS', Subgroup.mem_subgroupOf]
    have hx' : (x : G) ∈ pCoreOf 2 L := ⟨x, by assumption, rfl⟩
    exact F7.isSylowTwoOf_pCoreOf_le hSyl hx'
  have hS'2 : IsPGroup 2 S' :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTLL).symm
  have hcD' : Nat.card D' = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hD'odd : Odd (Nat.card D') := hcD' ▸ hD.2.1
  have hDP : D' ⊓ CFSG.pCore 2 ↥L = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hD'odd)
  have hinj : Function.Injective (π.comp D'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hx' : (x : ↥L) ∈ D' ⊓ CFSG.pCore 2 ↥L := ⟨x.2, hx⟩
    rw [hDP, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hx')
  have hrange : (π.comp D'.subtype).range = D'.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eD : ↥D ≃* ↥(D'.map π) :=
    ((Subgroup.subgroupOfEquivOfLe hDL).symm.trans (MonoidHom.ofInjective hinj)).trans
      (MulEquiv.subgroupCongr hrange)
  set Db : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := D'.map π with hDb
  set Sb : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := S'.map π with hSb
  have hSb2 : IsPGroup 2 Sb := hS'2.map π
  have hSbSyl : IsSylowTwoOf Sb ⊤ := by
    refine ⟨le_top, hSb2, ?_⟩
    show ¬ 2 ∣ Sb.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    intro h2
    exact hSyl.2.2 (h2.trans (Subgroup.index_map_dvd _ hπs))
  have hDbN : Db ≤ Subgroup.normalizer (Sb : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map π)
    exact le_normalizer_subgroupOf (hDB.trans inf_le_right)
  have hcDb : Nat.card Db = Nat.card D := (Nat.card_congr eD.toEquiv).symm
  have hDbSb : Db ⊓ Sb = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hSb2
    rw [hm, hcDb]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hD.2.1)
  have hsup : Db ⊔ Sb = Subgroup.normalizer (Sb : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    refine le_antisymm (sup_le hDbN Subgroup.le_normalizer) ?_
    intro xb hxb
    obtain ⟨x, rfl⟩ := hπs xb
    have hx1 : x ∈ Subgroup.normalizer ((Sb.comap π : Subgroup ↥L) : Set ↥L) :=
      Subgroup.le_normalizer_comap π hxb
    have hcomap : Sb.comap π = S' := by
      rw [hSb, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hPS
    rw [hcomap] at hx1
    have hxN : (x : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      mem_normalizer_of_mem_normalizer_subgroupOf hTLL hx1
    have hxB : (x : G) ∈ D ⊔ (T ⊓ L) := by
      rw [h.borelL_eq_sup hD]
      exact ⟨x.2, hxN⟩
    have hx2 : x ∈ D' ⊔ S' := by
      rw [hD', hS', ← Subgroup.subgroupOf_sup hDL hTLL, Subgroup.mem_subgroupOf]
      exact hxB
    have hx3 : π x ∈ (D' ⊔ S').map π := Subgroup.mem_map_of_mem π hx2
    rwa [Subgroup.map_sup] at hx3
  obtain ⟨hcyc, hcard⟩ := hF (↥L ⧸ CFSG.pCore 2 ↥L) n h.two_le h.lie Sb Db hSbSyl hDbN hDbSb hsup
  exact ⟨isCyclic_of_surjective eD.symm.toMonoidHom eD.symm.surjective, hcDb ▸ hcard⟩

end Hyp5_0_1

end CFSG.Quasithin.H13

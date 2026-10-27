module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open scoped Pointwise

section General

variable {Q : Type*} [Group Q] [Finite Q]

theorem not_dvd_index_of_sylow_le {r : ℕ} [Fact r.Prime] {C : Subgroup Q} {S : Sylow r Q}
    (hS : (S : Subgroup Q) ≤ C) : ¬ r ∣ C.index :=
  fun h => S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hS))

theorem eq_top_of_forall_sylow_le {C : Subgroup Q}
    (h : ∀ r : ℕ, (hr : r.Prime) → haveI : Fact r.Prime := ⟨hr⟩;
      ∃ S : Sylow r Q, (S : Subgroup Q) ≤ C) : C = ⊤ := by
  rw [← Subgroup.index_eq_one]
  by_contra hne
  obtain ⟨r, hr, hdvd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, hS⟩ := h r hr
  exact not_dvd_index_of_sylow_le hS hdvd

theorem isPGroup_two_quotient_of_forall_sylow_le {C : Subgroup Q} [C.Normal]
    (h : ∀ r : ℕ, (hr : r.Prime) → r ≠ 2 → haveI : Fact r.Prime := ⟨hr⟩;
      ∃ S : Sylow r Q, (S : Subgroup Q) ≤ C) : IsPGroup 2 (Q ⧸ C) := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card (Q ⧸ C)) with
    ⟨k, hk⟩ | ⟨r, hr, hdvd, hodd⟩
  · exact IsPGroup.of_card hk
  · have : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    obtain ⟨S, hS⟩ := h r hr hr2
    exact absurd hdvd (not_dvd_index_of_sylow_le hS)

end General

section Solvable

variable {G : Type*} [Group G]

theorem isSolvable_sup_of_le_normalizer {A R : Subgroup G} (hA : Group.IsSolvable A)
    (hR : Group.IsSolvable R) (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    Group.IsSolvable (A ⊔ R : Subgroup G) := by
  set W := A ⊔ R with hW
  have hWR : W ≤ Subgroup.normalizer (R : Set G) := sup_le hAR Subgroup.le_normalizer
  have hRn : (R.subgroupOf W).Normal := ⟨fun x hx w => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hWR w.2) _).mp hx⟩
  have hRW : Group.IsSolvable (R.subgroupOf W) := Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe (le_sup_right : R ≤ W)).symm.toMonoidHom)
    (MulEquiv.surjective _)
  have hq : Group.IsSolvable (W ⧸ R.subgroupOf W) := by
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (R.subgroupOf W)).comp (Subgroup.inclusion le_sup_left)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      have hw : (w : G) ∈ (A : Set G) * (R : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right A R hAR]
        exact w.2
      obtain ⟨a, ha, x, hx, hax⟩ := hw
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      change a⁻¹ * (w : G) ∈ R
      rw [← hax, inv_mul_cancel_left]
      exact hx
  exact Group.isSolvable_of_ker_le_range (R.subgroupOf W).subtype
    (QuotientGroup.mk' (R.subgroupOf W)) (by
      intro x hx
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact ⟨⟨x, hx⟩, rfl⟩)

theorem isSolvable_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G] {R : Subgroup G}
    (hR : IsPGroup p R) : Group.IsSolvable R :=
  haveI : Group.IsNilpotent R := hR.isNilpotent
  inferInstance

end Solvable

section Star

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def centralizerStar (Q L : Subgroup G) : Subgroup Q :=
  (Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))).comap
    ((starQuot G).comp Q.subtype)

omit [Finite G] in
theorem mem_centralizerStar {Q L : Subgroup G} {q : Q} :
    q ∈ centralizerStar Q L ↔
      starQuot G q ∈ Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
  Iff.rfl

omit [Finite G] in
theorem centralizerStar_normal {Q L : Subgroup G} (hQL : Q ≤ Subgroup.normalizer (L : Set G)) :
    (centralizerStar Q L).Normal := by
  refine ⟨fun c hc q => ?_⟩
  rw [mem_centralizerStar] at hc ⊢
  have hqn : starQuot G q ∈ Subgroup.normalizer
      (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ (hQL q.2))
  have hcn : starQuot G q ∈ Subgroup.normalizer
      (Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) :
        Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy l hl
      have hl' : (starQuot G q)⁻¹ * l * starQuot G q ∈ L.map (starQuot G) := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hqn) l).mp hl
        simpa using this
      have := hy _ hl'
      calc l * (starQuot G q * y * (starQuot G q)⁻¹)
          = starQuot G q * ((starQuot G q)⁻¹ * l * starQuot G q * y) * (starQuot G q)⁻¹ := by
            group
        _ = starQuot G q * (y * ((starQuot G q)⁻¹ * l * starQuot G q)) * (starQuot G q)⁻¹ := by
            rw [this]
        _ = starQuot G q * y * (starQuot G q)⁻¹ * l := by group
    · intro hy l hl
      have hl' : starQuot G q * l * (starQuot G q)⁻¹ ∈ L.map (starQuot G) :=
        (Subgroup.mem_normalizer_iff.mp hqn l).mp hl
      have := hy _ hl'
      have h2 : starQuot G q * (l * y) * (starQuot G q)⁻¹ =
          starQuot G q * (y * l) * (starQuot G q)⁻¹ := by
        calc starQuot G q * (l * y) * (starQuot G q)⁻¹
            = (starQuot G q * l * (starQuot G q)⁻¹) * (starQuot G q * y * (starQuot G q)⁻¹) := by
              group
          _ = (starQuot G q * y * (starQuot G q)⁻¹) * (starQuot G q * l * (starQuot G q)⁻¹) :=
              this
          _ = starQuot G q * (y * l) * (starQuot G q)⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp hcn _).mp hc

theorem exists_sylow_not_le_centralizer {A Q L : Subgroup G} (hA : IsPGroup 3 A)
    (hQ : ¬ 3 ∣ Nat.card Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hne : ¬ Q.map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    ∃ (r : ℕ) (_ : Fact r.Prime) (S : Sylow r Q),
      A ≤ Subgroup.normalizer (((S : Subgroup Q).map Q.subtype : Subgroup G) : Set G) ∧
      ¬ ((S : Subgroup Q).map Q.subtype).map (starQuot G) ≤
        Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
  by_contra hno
  push Not at hno
  apply hne
  have htop : centralizerStar Q L = ⊤ := by
    refine eq_top_of_forall_sylow_le fun r hr => ?_
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨S, hS⟩ := exists_sylow_le_normalizer hA hQ hAQ r
    refine ⟨S, fun s hs => ?_⟩
    rw [mem_centralizerStar]
    exact hno r ⟨hr⟩ S hS (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hs))
  rintro _ ⟨q, hq, rfl⟩
  have : (⟨q, hq⟩ : Q) ∈ centralizerStar Q L := htop ▸ Subgroup.mem_top _
  exact this

theorem isPGroup_two_quotient_centralizer {A Q L : Subgroup G} (hA : IsPGroup 3 A)
    (hQ : ¬ 3 ∣ Nat.card Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    (hodd : ∀ (r : ℕ) (_ : Fact r.Prime), r ≠ 2 → ∀ S : Sylow r Q,
      A ≤ Subgroup.normalizer (((S : Subgroup Q).map Q.subtype : Subgroup G) : Set G) →
      ((S : Subgroup Q).map Q.subtype).map (starQuot G) ≤
        Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    haveI := centralizerStar_normal hQL
    IsPGroup 2 (Q ⧸ centralizerStar Q L) := by
  have := centralizerStar_normal hQL
  refine isPGroup_two_quotient_of_forall_sylow_le fun r hr hr2 => ?_
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, hS⟩ := exists_sylow_le_normalizer hA hQ hAQ r
  refine ⟨S, fun s hs => ?_⟩
  rw [mem_centralizerStar]
  exact hodd r ⟨hr⟩ hr2 S hS (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hs))

end Star

end CFSG.RankThree.PartTwo.Sec4

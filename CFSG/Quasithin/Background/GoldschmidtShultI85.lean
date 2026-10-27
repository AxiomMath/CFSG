module

public import CFSG.Quasithin.Background.GoldschmidtShultAut
public import CFSG.Quasithin.Background.GoldschmidtShultThm

public section

namespace CFSG.Quasithin.Shult

open CFSG.Open

theorem eq_of_card_two {G : Type*} [Group G] {V : Subgroup G} (h : Nat.card V = 2) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (1 : ↥V)).mp h
  have h1 := hc ⟨a, ha⟩ (fun e => ha1 (congrArg Subtype.val e))
  have h2 := hc ⟨b, hb⟩ (fun e => hb1 (congrArg Subtype.val e))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem shultI85Part2 :
    ShultI85Part2 := by
  intro G _ _ M V h hN
  rcases shultI85Part1 G M V h with ⟨h2, -⟩ | ⟨f, -, hQ, -, -, -⟩
  · have hnorm : ∀ m ∈ M, ∀ v ∈ V, (m * v * m⁻¹) ∈ V := by
      intro m hm v hv
      rw [← h.normalizer_eq] at hm
      exact (Subgroup.mem_normalizer_iff.mp hm v).mp hv
    have hcomm : ∀ m ∈ M, ∀ v ∈ V, v * m = m * v := by
      intro m hm v hv
      by_cases hv1 : v = 1
      · simp [hv1]
      · have hmv := hnorm m hm v hv
        have hmv1 : m * v * m⁻¹ ≠ 1 := fun e => hv1 (by simpa using e)
        have heq := eq_of_card_two h2 hmv hv hmv1 hv1
        calc v * m = (m * v * m⁻¹) * m := by rw [heq]
          _ = m * v := by group
    have hC : ∀ m : ↥M, m ∈ (Subgroup.centralizer (V : Set G)).subgroupOf M := by
      intro m
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      exact fun v hv => hcomm m m.2 v hv
    have : Subsingleton (↥M ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf M) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact QuotientGroup.eq.2 (hC _)
    infer_instance
  · exact isSolvable_quotient_of_bender_hull h.normalizer_eq Subgroup.le_normalClosure h.2.1
      h.2.2.2.2.1 hQ.isBenderHull

end CFSG.Quasithin.Shult

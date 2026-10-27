module

public import CFSG.Fischer.Classification.Basic.Center
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

theorem pair_image {X Y : Type} [Group X] [Group Y] {E : Set X}
    (hP : Pair X E) (f : X →* Y) (hf : Function.Surjective f)
    (hne : ∀ e ∈ E, f e ≠ 1) : Pair Y (f '' E) := by
  obtain ⟨hfin, ⟨e₀, hE⟩, h2, h3, hgen⟩ := hP
  have hfinY : Finite Y := Finite.of_surjective f hf
  refine ⟨hfinY, ⟨f e₀, ?_⟩, ?_, ?_, ?_⟩
  · rw [hE]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact f.map_isConj hx
    · intro hy
      obtain ⟨c, rfl⟩ := isConj_iff.1 hy
      obtain ⟨g, rfl⟩ := hf c
      exact ⟨g * e₀ * g⁻¹, isConj_iff.2 ⟨g, rfl⟩, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hdvd : orderOf (f x) ∣ 2 := by
      have := orderOf_map_dvd f x
      rwa [h2 x hx] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) (hne x hx)
    · exact h
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hdvd : orderOf (f x * f y) ∣ orderOf (x * y) := by
      rw [← map_mul]
      exact orderOf_map_dvd f (x * y)
    have hle : orderOf (x * y) ≤ 3 := by
      have h' := h3 x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h'
      omega
    have hle' := (Nat.le_of_dvd (orderOf_pos _) hdvd).trans hle
    have hpos := orderOf_pos (f x * f y)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective f hf]

theorem comm_or_eq_of_map {X Y : Type} [Group X] [Group Y] {E : Set X}
    (hP : Pair X E) (f : X →* Y) {x y : X} (hx : x ∈ E) (hy : y ∈ E)
    (h : f x * f y = f y * f x) : x * y = y * x ∨ f x = f y := by
  by_cases hc : x * y = y * x
  · exact Or.inl hc
  refine Or.inr ?_
  have h3' : (x * y) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP hx hy hc, pow_orderOf_eq_one]
  have h3 : (f x * f y) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow, h3', map_one]
  have hcomm : Commute (f x) (f y) := h
  have h2 : (f x * f y) ^ 2 = 1 := by
    rw [hcomm.mul_pow, sq, sq, ← map_mul, ← map_mul, Pair.mul_self hP hx, Pair.mul_self hP hy,
      map_one, mul_one]
  have hxy : f x * f y = 1 := by
    have h' : (f x * f y) ^ 3 = (f x * f y) ^ 2 * (f x * f y) := pow_succ _ 2
    rw [h3, h2, one_mul] at h'
    exact h'.symm
  rw [eq_inv_of_mul_eq_one_left hxy, ← map_inv, Pair.inv_eq hP hy]

theorem pCore_quotient_center_eq_bot {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (h : CFSG.pCore p G ≤ Subgroup.center G) :
    CFSG.pCore p (G ⧸ Subgroup.center G) = ⊥ := by
  have hB : IsPGroup p (CFSG.pCore p (G ⧸ Subgroup.center G)) := CFSG.pCore_isPGroup
  have hnilB : Group.IsNilpotent (CFSG.pCore p (G ⧸ Subgroup.center G)) :=
    CFSG.pCore_isNilpotent
  let π : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  let M : Subgroup G := (CFSG.pCore p (G ⧸ Subgroup.center G)).comap π
  have hMn : M.Normal := Subgroup.Normal.comap CFSG.pCore_normal π
  let f : M →* CFSG.pCore p (G ⧸ Subgroup.center G) :=
    π.subgroupComap (CFSG.pCore p (G ⧸ Subgroup.center G))
  have hfsurj : Function.Surjective f :=
    π.subgroupComap_surjective _ (QuotientGroup.mk'_surjective _)
  have hfker : f.ker ≤ Subgroup.center M := by
    intro x hx
    have hx1 : (QuotientGroup.mk (x : G) : G ⧸ Subgroup.center G) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hxZ : (x : G) ∈ Subgroup.center G := (QuotientGroup.eq_one_iff _).1 hx1
    refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    simpa using Subgroup.mem_center_iff.1 hxZ g
  have hnilM : Group.IsNilpotent M := Subgroup.isNilpotent_of_ker_le_center f hfker
  let P : Sylow p M := default
  have hPker : (P : Subgroup M) ≤ f.ker := by
    intro x hx
    have hx' : (x : G) ∈ CFSG.pCore p G :=
      Sylow.map_le_pCore hMn hnilM p P (Subgroup.mem_map_of_mem M.subtype hx)
    exact MonoidHom.mem_ker.2 (Subtype.ext ((QuotientGroup.eq_one_iff (x : G)).2 (h hx')))
  have h1 : f.ker.index ∣ (P : Subgroup M).index := Subgroup.index_dvd_of_le hPker
  have h2 : ¬ p ∣ (P : Subgroup M).index := P.not_dvd_index
  have h3 : f.ker.index = Nat.card (CFSG.pCore p (G ⧸ Subgroup.center G)) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective f hfsurj, Subgroup.card_top]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hB
  have hn0 : n = 0 := by
    by_contra hn0
    exact h2 (dvd_trans (by rw [h3, hn]; exact dvd_pow_self p hn0) h1)
  rw [hn0, pow_zero] at hn
  exact Subgroup.card_eq_one.1 hn

end CFSG.RankThree.PartOne.FIS

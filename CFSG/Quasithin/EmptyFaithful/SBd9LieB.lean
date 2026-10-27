module

public import CFSG.Quasithin.EmptyFaithful.SBd9LieA

public section

namespace CFSG.Quasithin.SBd9

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin
open scoped commutatorElement

section Model

variable {G : Type} [Group G] {K : Type} [Field K]

theorem mem_centerOf_iff {L : Subgroup G} {x : ↥L} :
    (x : G) ∈ centerOf L ↔ x ∈ Subgroup.center ↥L := by
  constructor
  · rintro ⟨-, hx⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx g g.2)
  · intro hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨h, hh⟩)

structure IsBorelModel (L Q : Subgroup G) (ρ : ↥L →* projectiveSL 3 K) : Prop where
  surj : Function.Surjective ρ
  ker_eq : ρ.ker = Subgroup.center ↥L
  two : IsPGroup 2 ρ.ker
  map_eq : (Q.subgroupOf L).map ρ = projUnitriangular 3 K

variable {L Q : Subgroup G} {ρ : ↥L →* projectiveSL 3 K}

theorem IsBorelModel.ker_le [Finite G] (h : IsBorelModel L Q ρ) (hQ : IsSylowTwoOf Q L) :
    ρ.ker ≤ Q.subgroupOf L :=
  SzN2.ker_le_of_isSylowTwoOf h.two (isSylowTwoOf_top_subgroupOf hQ)

theorem IsBorelModel.mem_iff [Finite G] (h : IsBorelModel L Q ρ) (hQ : IsSylowTwoOf Q L)
    (x : ↥L) : ρ x ∈ projUnitriangular 3 K ↔ (x : G) ∈ Q := by
  rw [← h.map_eq, ← Subgroup.mem_comap, Subgroup.comap_map_eq_self (h.ker_le hQ),
    Subgroup.mem_subgroupOf]

theorem IsBorelModel.mem_normalizer_iff [Finite G] (h : IsBorelModel L Q ρ)
    (hQ : IsSylowTwoOf Q L) (x : ↥L) :
    ρ x ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) ↔
      (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
  have hker := h.ker_le hQ
  constructor
  · intro hx
    rw [← h.map_eq] at hx
    have h1 := SzN2.mem_normalizer_of_ker_le ρ hker hx
    have h2 := (A312.mem_normalizer_map_subtype_iff L (Q.subgroupOf L) x).mp h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hQ.1] at h2
  · intro hx
    rw [← h.map_eq]
    refine SzN2.map_mem_normalizer_map ρ h.surj hker ?_
    rw [A312.mem_normalizer_map_subtype_iff L (Q.subgroupOf L) x,
      Subgroup.map_subgroupOf_eq_of_le hQ.1]
    exact hx

theorem IsBorelModel.mem_centralizer (h : IsBorelModel L Q ρ) {x : G} (hxL : x ∈ L)
    (hx : x ∈ Subgroup.centralizer (Q : Set G)) :
    ρ ⟨x, hxL⟩ ∈ Subgroup.centralizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  rw [← h.map_eq] at hu
  obtain ⟨q, hq, rfl⟩ := hu
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx q (Subgroup.mem_subgroupOf.mp hq))

theorem IsBorelModel.eq_one_iff (h : IsBorelModel L Q ρ) (x : ↥L) :
    ρ x = 1 ↔ (x : G) ∈ centerOf L := by
  rw [mem_centerOf_iff, ← h.ker_eq, MonoidHom.mem_ker]

theorem IsBorelModel.center_le [Finite G] (h : IsBorelModel L Q ρ) (hQ : IsSylowTwoOf Q L) :
    centerOf L ≤ Q := by
  intro x hx
  have hxL : x ∈ L := hx.1
  have h1 : ρ ⟨x, hxL⟩ = 1 := (h.eq_one_iff ⟨x, hxL⟩).mpr hx
  exact (h.mem_iff hQ ⟨x, hxL⟩).mp (h1 ▸ (projUnitriangular 3 K).one_mem)

section Fields

variable [Finite G] [Finite K] [CharP K 2]

theorem IsBorelModel.solv (h : IsBorelModel L Q ρ) (hQ : IsSylowTwoOf Q L)
    (hK4 : ∃ s : Finset K, s.card = 4) :
    ∀ X : Subgroup G, Q ≤ X → X ≤ L → Group.IsSolvable ↥X →
      X ≤ Subgroup.normalizer (Q : Set G) :=
  fun _ hQX hXL hX => SzN2.L_normalizes_of_solvable_overgroup ρ h.surj h.two
    (projectiveSL_solvable_overgroup_le_normalizer hK4) hQ hQX hXL hX

theorem IsBorelModel.cent (h : IsBorelModel L Q ρ) (hQ : IsSylowTwoOf Q L) :
    L ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
  rintro x ⟨hxL, hx⟩
  obtain ⟨c, hc⟩ := exists_corner_of_mem_centralizer (h.mem_centralizer hxL hx)
  refine (h.mem_iff hQ ⟨x, hxL⟩).mp ?_
  rw [hc]
  exact Subgroup.mem_map_of_mem _ (corner_mem_unitriangular c)

omit [Finite G] in
theorem IsBorelModel.card_le (h : IsBorelModel L Q ρ) (W : Subgroup G)
    (hW : W ≤ L ⊓ Subgroup.centralizer (Q : Set G)) (hWZ : W ⊓ centerOf L = ⊥) :
    Nat.card ↥W ≤ Nat.card K := by
  have hex : ∀ w : ↥W, ∃ c : K, ρ ⟨(w : G), (hW w.2).1⟩ = proj 3 K (corner c) := fun w =>
    exists_corner_of_mem_centralizer (h.mem_centralizer (hW w.2).1 (hW w.2).2)
  choose f hf using hex
  refine Nat.card_le_card_of_injective f fun w₁ w₂ hw => ?_
  have h12 : ρ ⟨(w₁ : G), (hW w₁.2).1⟩ = ρ ⟨(w₂ : G), (hW w₂.2).1⟩ := by rw [hf, hf, hw]
  have hyL : (w₁ : G)⁻¹ * (w₂ : G) ∈ L := L.mul_mem (L.inv_mem (hW w₁.2).1) (hW w₂.2).1
  have h1 : ρ ⟨(w₁ : G)⁻¹ * (w₂ : G), hyL⟩ = 1 := by
    have e : (⟨(w₁ : G)⁻¹ * (w₂ : G), hyL⟩ : ↥L) =
        (⟨(w₁ : G), (hW w₁.2).1⟩ : ↥L)⁻¹ * ⟨(w₂ : G), (hW w₂.2).1⟩ := rfl
    rw [e, map_mul, map_inv, h12, inv_mul_cancel]
  have h2 : (w₁ : G)⁻¹ * (w₂ : G) ∈ centerOf L := (h.eq_one_iff ⟨_, hyL⟩).mp h1
  have h3 : (w₁ : G)⁻¹ * (w₂ : G) ∈ W ⊓ centerOf L := ⟨W.mul_mem (W.inv_mem w₁.2) w₂.2, h2⟩
  rw [hWZ, Subgroup.mem_bot, inv_mul_eq_one] at h3
  exact Subtype.ext h3

theorem IsBorelModel.exp_dvd (h : IsBorelModel L Q ρ) (hQ : IsSylowTwoOf Q L) (W : Subgroup G)
    (hW : W ≤ L ⊓ Subgroup.centralizer (Q : Set G)) (hWZ : ¬ W ≤ centerOf L) (m : ℕ)
    (hm : ∀ b ∈ L ⊓ Subgroup.normalizer (Q : Set G), ∀ w ∈ W, ⁅b ^ m, w⁆ ∈ centerOf L) :
    Nat.card K - 1 ∣ m := by
  obtain ⟨w, hwW, hwZ⟩ := Set.not_subset.mp hWZ
  have hwL : w ∈ L := (hW hwW).1
  obtain ⟨c0, hc0⟩ := exists_corner_of_mem_centralizer (h.mem_centralizer hwL (hW hwW).2)
  have hc0ne : c0 ≠ 0 := by
    rintro rfl
    apply hwZ
    refine (h.eq_one_iff ⟨w, hwL⟩).mp ?_
    rw [hc0, corner_zero, map_one]
  have hall : ∀ a : Kˣ, a ^ m = 1 := by
    intro a
    obtain ⟨β, hβ⟩ := h.surj (proj 3 K (torus a))
    have hβN : (β : G) ∈ Subgroup.normalizer (Q : Set G) := by
      rw [← h.mem_normalizer_iff hQ, hβ, normalizer_projUnitriangular (K := K) (n := 3) 2]
      exact Subgroup.mem_map_of_mem _ (torus_mem_upperTriangular a)
    have hcomm := hm (β : G) ⟨β.2, hβN⟩ w hwW
    have hmem : ((⁅β ^ m, (⟨w, hwL⟩ : ↥L)⁆ : ↥L) : G) ∈ centerOf L := hcomm
    have h1 : ρ ⁅β ^ m, (⟨w, hwL⟩ : ↥L)⁆ = 1 := (h.eq_one_iff _).mpr hmem
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, map_pow, hβ, hc0] at h1
    have hact : ∀ c : K, proj 3 K (torus a) * proj 3 K (corner c) =
        proj 3 K (corner ((a : K) * c)) * proj 3 K (torus a) := fun c => by
      rw [← map_mul, torus_mul_corner, map_mul]
    rw [pow_mul_proj_corner hact m c0] at h1
    have h2 := proj_corner_injective (mul_right_cancel h1)
    have h3 : ((a : K) ^ m - 1) * c0 = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact Units.ext (by simpa [sub_eq_zero] using h4)
    · exact absurd h4 hc0ne
  have hdvd := Monoid.exponent_dvd_of_forall_pow_eq_one hall
  rwa [IsCyclic.exponent_eq_card, Nat.card_units] at hdvd

theorem IsBorelModel.reg4 (h : IsBorelModel L Q ρ) (hQ : IsSylowTwoOf Q L) (hK : Nat.card K = 4)
    {y : G} (hyL : y ∈ L) (hyN : y ∈ Subgroup.normalizer (Q : Set G)) (hy3 : orderOf y = 3)
    {x : G} (hxL : x ∈ L) (hxC : x ∈ Subgroup.centralizer (Q : Set G)) (hxy : x * y = y * x) :
    x ∈ centerOf L := by
  have hyU : ρ ⟨y, hyL⟩ ∉ projUnitriangular 3 K := by
    intro hmem
    have hyQ : y ∈ Q := (h.mem_iff hQ ⟨y, hyL⟩).mp hmem
    obtain ⟨k, hk⟩ := hQ.2.1 ⟨y, hyQ⟩
    have hk' : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : 3 ∣ 2 ^ k := hy3 ▸ orderOf_dvd_of_pow_eq_one hk'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hyN' : ρ ⟨y, hyL⟩ ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) :=
    (h.mem_normalizer_iff hQ ⟨y, hyL⟩).mpr hyN
  obtain ⟨a, ha1, hact⟩ := exists_ne_one_of_mem_normalizer hK hyN' hyU
  obtain ⟨c, hc⟩ := exists_corner_of_mem_centralizer (h.mem_centralizer hxL hxC)
  have hcomm : ρ ⟨x, hxL⟩ * ρ ⟨y, hyL⟩ = ρ ⟨y, hyL⟩ * ρ ⟨x, hxL⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxy
  rw [hc, hact c] at hcomm
  have h1 := proj_corner_injective (mul_right_cancel hcomm)
  have h2 : (1 - a) * c = 0 := by linear_combination h1
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3).symm ha1
    · exact h3
  refine (h.eq_one_iff ⟨x, hxL⟩).mp ?_
  rw [hc, hc0, corner_zero, map_one]

end Fields

end Model

end CFSG.Quasithin.SBd9

module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.EmptyFaithful.S152O4Mod

public section

namespace CFSG.Quasithin.R3c5

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

omit [Group G] in
theorem exists_mul_of_mem_sup_centralizer {G : Type} [Group G] {L : Subgroup G} {y : G}
    (hy : y ∈ L ⊔ Subgroup.centralizer (L : Set G)) :
    ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set G), y = l * c := by
  let S : Subgroup G :=
    { carrier := {x | ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set G), x = l * c}
      one_mem' := ⟨1, L.one_mem, 1, Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, c₁, hc₁, rfl⟩ ⟨l₂, hl₂, c₂, hc₂, rfl⟩
        refine ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, c₁ * c₂, Subgroup.mul_mem _ hc₁ hc₂, ?_⟩
        have h := Subgroup.mem_centralizer_iff.mp hc₁ l₂ hl₂
        calc l₁ * c₁ * (l₂ * c₂) = l₁ * (c₁ * l₂) * c₂ := by group
          _ = l₁ * (l₂ * c₁) * c₂ := by rw [← h]
          _ = l₁ * l₂ * (c₁ * c₂) := by group
      inv_mem' := by
        rintro _ ⟨l, hl, c, hc, rfl⟩
        refine ⟨l⁻¹, L.inv_mem hl, c⁻¹, Subgroup.inv_mem _ hc, ?_⟩
        have h := Subgroup.mem_centralizer_iff.mp hc l hl
        have h' : c⁻¹ * l⁻¹ = l⁻¹ * c⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, h]
        rw [mul_inv_rev, h'] }
  have hle : L ⊔ Subgroup.centralizer (L : Set G) ≤ S := by
    refine sup_le ?_ ?_
    · intro x hx
      exact ⟨x, hx, 1, Subgroup.one_mem _, by simp⟩
    · intro x hx
      exact ⟨1, L.one_mem, x, hx, by simp⟩
  exact hle hy

variable [Finite G]

theorem not_mem_sup_centralizer {I L : Subgroup G} (hLI : L ≤ I)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥L)) (hr : 2 ≤ CFSG.Open.pRank 3 L)
    (hI3 : CFSG.Open.pRank 3 I ≤ 2) {y : G} (hyI : y ∈ I) (hy3 : orderOf y = 3) (hyL : y ∉ L) :
    y ∉ L ⊔ Subgroup.centralizer (L : Set G) := by
  intro hy
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hy
  have hcomm : Commute l c := (Subgroup.mem_centralizer_iff.mp hc l hl)
  have hcI : c ∈ I := by
    have := I.mul_mem (I.inv_mem (hLI hl)) hyI
    simpa using this
  have hy1 : (l * c) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (l * c)
    rwa [hy3] at this
  have hc3 : c ^ 3 = (l ^ 3)⁻¹ := by
    rw [hcomm.mul_pow] at hy1
    exact eq_inv_of_mul_eq_one_right hy1
  have hc3L : c ^ 3 ∈ L := by
    rw [hc3]
    exact L.inv_mem (L.pow_mem hl 3)
  have hc3C : c ^ 3 ∈ Subgroup.centralizer (L : Set G) := Subgroup.pow_mem _ hc 3
  have hc3Z : (⟨c ^ 3, hc3L⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc3C g g.2)
  obtain ⟨k, hk⟩ := hZ ⟨_, hc3Z⟩
  have hk' : (c ^ 3) ^ 2 ^ k = 1 := congrArg (fun a : ↥(Subgroup.center ↥L) => ((a : ↥L) : G)) hk
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 4 ^ k = 3 * m + 1 := by
    have : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    exact ⟨4 ^ k / 3, by omega⟩
  have h4 : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
    rw [← mul_pow]
    norm_num
  set c₃ : G := c ^ 4 ^ k with hc₃
  have hc₃eq : c₃ = (c ^ 3) ^ m * c := by
    rw [hc₃, hm, pow_succ, pow_mul]
  have hc₃3 : c₃ ^ 3 = 1 := by
    rw [hc₃, ← pow_mul, mul_comm, pow_mul, h4, pow_mul, hk', one_pow]
  have hc₃C : c₃ ∈ Subgroup.centralizer (L : Set G) := Subgroup.pow_mem _ hc _
  have hc₃I : c₃ ∈ I := I.pow_mem hcI _
  have hc₃L : c₃ ∉ L := by
    intro hc₃L
    have hZ' : (⟨c₃, hc₃L⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc₃C g g.2)
    obtain ⟨j, hj⟩ := hZ ⟨_, hZ'⟩
    have hj' : c₃ ^ 2 ^ j = 1 := congrArg (fun a : ↥(Subgroup.center ↥L) => ((a : ↥L) : G)) hj
    have h1 : orderOf c₃ ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    have h2 : orderOf c₃ ∣ 3 := orderOf_dvd_of_pow_eq_one hc₃3
    have h3 : orderOf c₃ = 1 := by
      have h4 : orderOf c₃ ∣ Nat.gcd (2 ^ j) 3 := Nat.dvd_gcd h1 h2
      have h5 : Nat.gcd (2 ^ j) 3 = 1 := by
        apply Nat.Coprime.pow_left
        norm_num
      rw [h5] at h4
      exact Nat.dvd_one.mp h4
    have hc₃1 : c₃ = 1 := orderOf_eq_one_iff.mp h3
    have hcL : c ∈ L := by
      have : c = ((c ^ 3) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right (hc₃eq ▸ hc₃1)
      rw [this]
      exact L.inv_mem (L.pow_mem hc3L m)
    exact hyL (L.mul_mem hl hcL)
  obtain ⟨E, hEL, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
  have hEI : E ≤ I := hEL.trans hLI
  have hc₃E : c₃ ∉ E := fun h => hc₃L (hEL h)
  have hc₃E' : c₃ ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.centralizer_le (by exact hEL) hc₃C
  have := CFSG.AGLEmbedding.succ_le_pRank_of_isElemAbelian_of_mem_centralizer Nat.prime_three hE
    hEcard hc₃3 hc₃E hc₃E' hEI hc₃I
  omega

end CFSG.Quasithin.R3c5

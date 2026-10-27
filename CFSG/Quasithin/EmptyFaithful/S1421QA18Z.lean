module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421QA18

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem exists_z_carrier (h : Hyp1421 G T M) :
    ∃ z : G, z ≠ 1 ∧ z ^ 2 = 1 ∧ z ∈ quasithinOmegaOneCenter T ∧
      ∀ g ∈ quasithinOmegaOneCenter T, g = 1 ∨ g = z := by
  obtain ⟨x, y, hxy, hxyu⟩ := Nat.card_eq_two_iff.mp h.card_omegaOneCenter
  have hmem : ∀ g : ↥(quasithinOmegaOneCenter T), g = x ∨ g = y := fun g => by
    have : g ∈ ({x, y} : Set ↥(quasithinOmegaOneCenter T)) := by rw [hxyu]; trivial
    simpa using this
  rcases hmem 1 with h1 | h1
  ·
    refine ⟨(y : G), ?_, ?_, y.2, fun g hg => ?_⟩
    · intro hy
      have : y = 1 := Subtype.ext hy
      exact hxy (h1.symm.trans this.symm)
    · have h2 : (y : ↥(quasithinOmegaOneCenter T)) ^ 2 = 1 ∨
          (y : ↥(quasithinOmegaOneCenter T)) ^ 2 = y := by
        rcases hmem (y ^ 2) with e | e
        · exact Or.inl (e.trans h1.symm)
        · exact Or.inr e
      rcases h2 with e | e
      · simpa using congrArg Subtype.val e
      · exfalso
        have : y = 1 := by
          have h3 : y ^ 2 = y * 1 := by rw [e, mul_one]
          rw [sq] at h3
          exact mul_left_cancel h3
        exact hxy (h1.symm.trans this.symm)
    · rcases hmem ⟨g, hg⟩ with e | e
      · exact Or.inl (by simpa [← h1] using congrArg Subtype.val e)
      · exact Or.inr (by simpa using congrArg Subtype.val e)
  ·
    refine ⟨(x : G), ?_, ?_, x.2, fun g hg => ?_⟩
    · intro hx
      have : x = 1 := Subtype.ext hx
      exact hxy (this.trans h1)
    · have h2 : (x : ↥(quasithinOmegaOneCenter T)) ^ 2 = 1 ∨
          (x : ↥(quasithinOmegaOneCenter T)) ^ 2 = x := by
        rcases hmem (x ^ 2) with e | e
        · exact Or.inr e
        · exact Or.inl (e.trans h1.symm)
      rcases h2 with e | e
      · simpa using congrArg Subtype.val e
      · exfalso
        have : x = 1 := by
          have h3 : x ^ 2 = x * 1 := by rw [e, mul_one]
          rw [sq] at h3
          exact mul_left_cancel h3
        exact hxy (this.trans h1)
    · rcases hmem ⟨g, hg⟩ with e | e
      · exact Or.inr (by simpa using congrArg Subtype.val e)
      · exact Or.inl (by simpa [← h1] using congrArg Subtype.val e)

omit [Finite G] in
theorem centralizer_singleton_eq {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T)
    (hZ : ∀ g ∈ quasithinOmegaOneCenter T, g = 1 ∨ g = z) :
    Subgroup.centralizer ({z} : Set G) = mcOf T := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro hg w hw
    rcases hZ w hw with rfl | rfl
    · simp
    · exact hg
  · intro hg
    exact hg z hz

theorem le_twoPrimeResidual_mcOf (h : Hyp1421 G T M) : T ≤ twoPrimeResidual (mcOf T) := by
  have hT : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_isSylowTwo h.sylow h.toQTFE14.t_le_mc
  rw [← conjClosure_eq_twoPrimeResidual hT]
  exact le_conjClosure T (mcOf T)

omit [Finite G] in
theorem twoPrimeResidual_le (H : Subgroup G) : twoPrimeResidual H ≤ H := by
  refine iInf_le_of_le H ?_
  exact iInf_le_of_le ⟨le_rfl, Subgroup.le_normalizer, by simp⟩ le_rfl

theorem exists_z (h : Hyp1421 G T M) :
    ∃ z : G, z ^ 2 = 1 ∧ z ≠ 1 ∧ z ∈ T ∧ z ∈ quasithinOmegaOneCenter T ∧
      z ∈ twoPrimeResidual (mcOf T) ∧
      z ∈ Subgroup.centralizer (twoPrimeResidual (mcOf T) : Set G) ∧
      Subgroup.centralizer ({z} : Set G) = mcOf T ∧
      ∀ g ∈ quasithinOmegaOneCenter T, g = 1 ∨ g = z := by
  obtain ⟨z, hz1, hz2, hzZ, hZ⟩ := exists_z_carrier h
  have hzT : z ∈ T := (quasithinOmegaOneCenter_le_center T hzZ).1
  refine ⟨z, hz2, hz1, hzT, hzZ, le_twoPrimeResidual_mcOf h hzT, ?_,
    centralizer_singleton_eq hzZ hZ, hZ⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hwM : w ∈ mcOf T := twoPrimeResidual_le _ hw
  exact (Subgroup.mem_centralizer_iff.mp hwM z hzZ).symm

end S1421QA18

end CFSG.Quasithin

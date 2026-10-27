module

public import CFSG.Quasithin.H13.KGFactF618A
public import CFSG.Quasithin.H13.KGFactF618C
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases11
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

namespace KGF618

theorem mul_self_mem_of_index_dvd_two {G : Type*} [Group G] {H : Subgroup G} (h : H.index ∣ 2)
    (a : G) : a * a ∈ H := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    exact Subgroup.mem_top _
  · exact Subgroup.mul_self_mem_of_index_two h2 a

theorem conclusion_hatSym {D : Type} [Group D] [Finite D] {n : ℕ} (h : F6.IsHatSym n D)
    (hn : 2 ≤ n) (hnp : ¬ (n.factorial / 2).Prime) {d : ℕ} (hd : d ∣ 3 * (n.factorial / 2))
    (h2 : Nat.Coprime d 2) (h15 : ¬ d ∣ 15) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b := by
  obtain ⟨φ, -, -, hA⟩ := h
  refine conclusion_of_good (N := (alternatingGroup (Fin n)).comap φ) (fun x => ?_)
    (good_hatAlt hA hn hnp hd h2 h15)
  rw [Subgroup.mem_comap, map_mul, Equiv.Perm.mem_alternatingGroup, map_mul, Int.units_mul_self]

theorem conclusion_sym_seven {D : Type} [Group D] [Finite D] (e : D ≃* Equiv.Perm (Fin 7)) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b := by
  refine conclusion_of_mulEquiv e (N := alternatingGroup (Fin 7)) (fun σ => ?_)
    (good_alt_seven (MulEquiv.refl _))
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Int.units_mul_self]

theorem conclusion_psigma {D : Type} [Group D] [Finite D] {p : ℕ} (hp3 : 3 ≤ p)
    (h : F6.IsL2FieldExtCat p D) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b := by
  obtain ⟨hp, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨Kq, -, hqs, hidx, -, hcard⟩ :=
    CFSG.Quasithin.Insp9.exists_normal_psl_of_psigma hp hp3 K hK e
  have hp2 : p ≠ 2 := by omega
  have hcop : Nat.Coprime (p ^ 2) 2 :=
    Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  refine conclusion_of_good (mul_self_mem_of_index_dvd_two hidx)
    ⟨hqs, ne_sixty_mul_two_pow ?_ hcop fun h15 => ?_⟩
  · have h1 : p ^ 2 ∣ 2 * Nat.card ↥Kq := by
      rw [hcard]
      exact dvd_mul_right _ _
    exact (Nat.Coprime.dvd_mul_left hcop).1 h1
  · have h1 := Nat.le_of_dvd (by norm_num) h15
    have hp3' : p ≤ 3 := by nlinarith
    have hp3'' : p = 3 := by omega
    subst hp3''
    norm_num at h15

theorem conclusion_caseEight {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : F6.IsF618CaseEightCat G₁ G₂) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b := by
  obtain ⟨hD, -⟩ := h
  rcases hD with hS | ⟨p, -, hp8, hL⟩
  · exact conclusion_hatSym hS (by norm_num) (by norm_num [Nat.factorial]) (d := 9)
      (by norm_num [Nat.factorial]) (by norm_num) (by norm_num)
  · exact conclusion_psigma (by omega) hL

theorem conclusion_caseNine {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : F6.IsF618CaseNineCat G₁ G₂) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b := by
  obtain ⟨hD, -⟩ := h
  rcases hD with hS | hS | ⟨p, -, hp24, hL⟩
  · obtain ⟨e⟩ := hS
    exact conclusion_sym_seven e
  · exact conclusion_hatSym hS (by norm_num) (by norm_num [Nat.factorial]) (d := 7)
      (by norm_num [Nat.factorial]) (by norm_num) (by norm_num)
  · exact conclusion_psigma (by omega) hL

theorem conclusion_caseEleven {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : F6.IsF618CaseEleven G₁ G₂) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b := by
  obtain ⟨⟨p, hp8, hG⟩, -⟩ := h
  obtain ⟨Kq, hidx, hSL⟩ := CFSG.Quasithin.Insp9.exists_index_two_isSLEps3 hG
  exact conclusion_of_good (fun x => Subgroup.mul_self_mem_of_index_two hidx x)
    (good_isSLEps3 hp8 hSL)

theorem conclusion_caseThirteen
    {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D} (h : F6.IsF618CaseThirteen G₁ G₂) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b := by
  obtain ⟨⟨e⟩, -⟩ := h
  have hidx : (inner ↥NativeSporadic.M12).index = 2 :=
    CFSG.ComponentClassification.M12Cover.card_outer
  obtain ⟨_, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m12_simplicity
  have hnc : ∃ a b : ↥NativeSporadic.M12, a * b ≠ b * a :=
    exists_ne_comm (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)
  have hinj : Function.Injective
      (MulAut.conj : ↥NativeSporadic.M12 →* MulAut ↥NativeSporadic.M12) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ Subgroup.center ↥NativeSporadic.M12 := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hw := congrArg (fun f : MulAut ↥NativeSporadic.M12 => f w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at hw
      calc w * z = (z * w * z⁻¹) * z := by rw [hw]
        _ = z * w := by group
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥NativeSporadic.M12) with hZ | hZ
    · rw [hZ, Subgroup.mem_bot] at hzc
      exact hzc
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hb : b ∈ Subgroup.center ↥NativeSporadic.M12 := hZ ▸ Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  exact conclusion_of_mulEquiv e (fun x => Subgroup.mul_self_mem_of_index_two hidx x)
    (good_M12 (MonoidHom.ofInjective hinj).symm)

end KGF618

end CFSG.Quasithin.H13.A5

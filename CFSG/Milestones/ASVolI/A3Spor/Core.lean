module

public import CFSG.Milestones.ASVolI.A3OddFacts

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique

theorem burnsideA315s_Config.nilpotent {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) : Group.IsNilpotent ↥B := by
  rcases hc.cases with hab | ⟨r, hr, hBr⟩
  · infer_instance
  · haveI : Fact r.Prime := ⟨hr⟩
    exact hBr.isNilpotent

theorem burnsideA315s_Config.exists_prime {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ Nat.card ↥B := by
  by_contra hno
  push Not at hno
  apply hc.not3
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
  intro d hd hdB
  have hd2 : d ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hc.odd) (even_iff_two_dvd.2 hdB)
  by_contra hd3
  have h5 : 5 ≤ d := by
    have := hd.two_le
    have : d ≠ 4 := by
      rintro rfl
      exact absurd hd (by decide)
    omega
  exact hno d hd h5 hdB

theorem burnsideA315s_hall_of_prime {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {r : ℕ} (hr : r.Prime) (hrB : r ∣ Nat.card ↥B) :
    ∃ K : Subgroup X, S ≤ K ∧ K ≤ B ⊔ S ∧ Group.IsSolvable ↥K ∧
      r ∣ Nat.card ↥K ∧ ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K → p = 2 ∨ p = r := by
  have hsolv : Group.IsSolvable ↥(B ⊔ S) := hc.sup_solvable (burnsideA315s_Config.nilpotent hc)
  let π : Set Nat.Primes := {p | p.val = 2 ∨ p.val = r}
  have hSH : S ≤ B ⊔ S := le_sup_right
  have hSπ : CFSG.IsPiSubgroup π (S.subgroupOf (B ⊔ S)) := by
    intro p hp
    have hS2 : IsPGroup 2 ↥(S.subgroupOf (B ⊔ S)) :=
      hc.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk] at hp
    left
    exact (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).1 (p.2.dvd_of_dvd_pow hp)
  obtain ⟨K', hK', hSK'⟩ := CFSG.SolvableHall.solvable_hall_containment hsolv π _ hSπ
  refine ⟨K'.map (B ⊔ S).subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨⟨s, hSH hs⟩, hSK' (Subgroup.mem_subgroupOf.2 hs), rfl⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · have hK's : Group.IsSolvable ↥K' :=
      Group.isSolvable_of_isSolvable_injective K'.subtype_injective
    exact Group.isSolvable_of_surjective ((B ⊔ S).subtype.subgroupMap_surjective K')
  · rw [Subgroup.card_map_of_injective (B ⊔ S).subtype_injective]
    have hrH : r ∣ Nat.card ↥(B ⊔ S) := hrB.trans (Subgroup.card_dvd_of_le le_sup_left)
    have hri : ¬ r ∣ K'.index := by
      intro hri
      exact hK'.p_in_pi_of_p_dvd_index ⟨r, hr⟩ hri (Or.inr rfl)
    rw [← K'.card_mul_index] at hrH
    exact (hr.dvd_mul.1 hrH).resolve_right hri
  · intro p hp hpK
    rw [Subgroup.card_map_of_injective (B ⊔ S).subtype_injective] at hpK
    exact hK'.p_in_pi_of_p_dvd_card ⟨p, hp⟩ hpK

theorem burnsideA315s_hall_index {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {S₀ : Subgroup X} (hS₀ : IsSylowTwoOf S₀ ⊤) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrB : r ∣ Nat.card ↥B) :
    ∃ g : X, ∃ K : Subgroup X, S ≤ K ∧ K ≤ B ⊔ S ∧ S.map (MulAut.conj g).toMonoidHom = S₀ ∧
      S₀ ≤ K.map (MulAut.conj g).toMonoidHom ∧
      Group.IsSolvable ↥(K.map (MulAut.conj g).toMonoidHom) ∧
      ∃ m : ℕ, Nat.card ↥(K.map (MulAut.conj g).toMonoidHom) = m * Nat.card ↥S₀ ∧ r ∣ m ∧
        ∀ p : ℕ, p.Prime → p ∣ m → p = r := by
  obtain ⟨K, hSK, hKH, hKs, hrK, hK⟩ := burnsideA315s_hall_of_prime hc hr hrB
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hc.sylow
  obtain ⟨h3, h4⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hS₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (h1.toSylow h2) (h3.toSylow h4)
  have hSg : S.map (MulAut.conj g).toMonoidHom = S₀ := by
    have := congrArg (fun P : Sylow 2 X => (P : Subgroup X)) hg
    exact this
  have hS₀K₀ : S₀ ≤ K.map (MulAut.conj g).toMonoidHom := hSg ▸ Subgroup.map_mono hSK
  have hK₀ : Nat.card ↥(K.map (MulAut.conj g).toMonoidHom) = Nat.card ↥K :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hK₀s : Group.IsSolvable ↥(K.map (MulAut.conj g).toMonoidHom) :=
    Group.isSolvable_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap_surjective K)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hS₀K₀
  rw [mul_comm] at hm
  obtain ⟨a, ha⟩ := h3.exists_card_eq
  refine ⟨g, K, hSK, hKH, hSg, hS₀K₀, hK₀s, m, hm, ?_, ?_⟩
  · have : r ∣ m * 2 ^ a := by rw [← ha, ← hm, hK₀]; exact hrK
    rcases hr.dvd_mul.1 this with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)) hr2
  · intro p hp hpm
    have hpK : p ∣ Nat.card ↥K := by
      rw [← hK₀, hm]
      exact Dvd.dvd.mul_right hpm _
    rcases hK p hp hpK with rfl | h
    ·
      exfalso
      have hidx : S₀.index = m * (K.map (MulAut.conj g).toMonoidHom).index := by
        have e1 := Subgroup.card_mul_index S₀
        have e2 := Subgroup.card_mul_index (K.map (MulAut.conj g).toMonoidHom)
        rw [hm, ← e1] at e2
        have hpos : 0 < Nat.card ↥S₀ := Nat.card_pos
        have : Nat.card ↥S₀ * (m * (K.map (MulAut.conj g).toMonoidHom).index) =
            Nat.card ↥S₀ * S₀.index := by rw [← e2]; ring
        exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
      have hodd : ¬ 2 ∣ S₀.index := h4
      rw [hidx] at hodd
      exact hodd (Dvd.dvd.mul_right hpm _)
    · exact h

theorem burnsideA315s_false_of_overgroups {X : Type} [Group X] [Finite X] {S₀ : Subgroup X}
    (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hidx : ∀ Z : Subgroup X, S₀ ≤ Z → Group.IsSolvable ↥Z → ∀ m : ℕ,
      Nat.card ↥Z = m * Nat.card ↥S₀ → m = 1 ∨ 3 ∣ m)
    {S B : Subgroup X} (hc : burnsideA315x_Config X S B) : False := by
  obtain ⟨r, hr, hr5, hrB⟩ := burnsideA315s_Config.exists_prime hc
  obtain ⟨g, K, -, -, -, hS₀K, hs, m, hm, hrm, hpm⟩ :=
    burnsideA315s_hall_index hc hS₀ hr (by omega) hrB
  rcases hidx _ hS₀K hs m hm with h | h
  · rw [h] at hrm
    exact hr.one_lt.ne' (Nat.dvd_one.1 hrm)
  · have := hpm 3 Nat.prime_three h
    omega

theorem burnsideA315s_noConfig_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ S B : Subgroup Y, ¬ burnsideA315x_Config Y S B) :
    ∀ S B : Subgroup X, ¬ burnsideA315x_Config X S B :=
  fun _ _ hc => h _ _ (hc.map e)

end CFSG.ASVolI

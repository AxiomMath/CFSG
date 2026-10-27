module

public import CFSG.Quasithin.Vol2.F134LieU3
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OArith
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OOrbit
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OOrder

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open CFSG.Quasithin.F134.LieU3 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K]

theorem rkOneUStar_free (h : UnitaryFieldData p f K) {u : Equiv.Perm (hypIsotropicLines h 1 1)}
    (hu : u ∈ rkOneUStar h) {y : hypIsotropicLines h 1 1} (hy : y ≠ infL h) (huy : u y = y) :
    u = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hreg, -⟩ := unitary_rank_one_root_structure h
  obtain ⟨x, ⟨hxU, hx0⟩, -⟩ := hreg y hy
  obtain ⟨z, -, hz⟩ := hreg (zeroL h) zeroL_ne_infL
  have h1 : x⁻¹ * u * x = 1 := by
    have e1 := hz (x⁻¹ * u * x) ⟨mul_mem (mul_mem (inv_mem hxU) hu) hxU, by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hx0, huy,
        Equiv.Perm.inv_eq_iff_eq.2 hx0.symm]⟩
    have e2 := hz 1 ⟨one_mem _, rfl⟩
    rw [e1, e2]
  calc u = x * (x⁻¹ * u * x) * x⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem exists_smul_eq_of_range (h : UnitaryFieldData p f K) {X : Type} [Group X]
    (Φ : X →* Equiv.Perm (hypIsotropicLines h 1 1)) (hrange : Φ.range = rkOneG h)
    (x y : hypIsotropicLines h 1 1) : ∃ g : X, Φ g x = y := by
  have : Finite (hypIsotropicLines h 1 1) := finite_hypIsotropicLines_one h
  have hcard : 1 < Nat.card (hypIsotropicLines h 1 1) := by
    rw [card_hypIsotropicLines_one h]
    have := h.prime.pos
    have : 1 ≤ (p ^ f) ^ 3 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ h.prime.pos)
    omega
  have : Nontrivial (hypIsotropicLines h 1 1) := Finite.one_lt_card_iff_nontrivial.1 hcard
  obtain ⟨x', hx'⟩ := exists_ne x
  obtain ⟨y', hy'⟩ := exists_ne y
  obtain ⟨g, hg, hgx, -⟩ := rkOneG_two_transitive h x x' y y' hx'.symm hy'.symm
  rw [← hrange] at hg
  obtain ⟨γ, rfl⟩ := hg
  exact ⟨γ, hgx⟩

theorem false_of_char {X : Type} [Group X] [Finite X] {p a : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (ha : 2 ≤ a) (hX : StatedClassicalModel X .PSU 3 p 1) {S H Q : Subgroup X}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hQH : Q ≤ H)
    (hH : Nat.card H = p ^ a * Nat.card S) (hQ : Nat.card Q = p ^ a) : False := by
  have hQp : IsPGroup p Q := IsPGroup.of_card hQ
  obtain ⟨R, hQR⟩ := hQp.exists_le_sylow
  obtain ⟨K, _, h, Φ, hΦ, hrange, hRU⟩ := exists_perm_comap_rkOneUStar_eq hX R
  have : Finite (hypIsotropicLines h 1 1) := finite_hypIsotropicLines_one h
  let _ : MulAction X (hypIsotropicLines h 1 1) := MulAction.compHom _ Φ
  have hsmul : ∀ (g : X) (L : hypIsotropicLines h 1 1), g • L = Φ g L := fun _ _ => rfl
  have hQU : ∀ g ∈ Q, Φ g ∈ rkOneUStar h := fun g hg => by
    have : g ∈ (rkOneUStar h).comap Φ := by
      rw [hRU]
      exact hQR hg
    exact this
  have hfix : ∀ g ∈ Q, g • infL h = infL h := fun g hg => by
    rw [hsmul]
    exact rkOneUStar_fix h (hQU g hg)
  have hfree : ∀ g ∈ Q, ∀ y : hypIsotropicLines h 1 1, y ≠ infL h → g • y = y → g = 1 :=
    fun g hg y hy hgy => hΦ (by
      rw [map_one]
      exact rkOneUStar_free h (hQU g hg) hy (by rw [← hsmul]; exact hgy))
  have hdvd1 := card_dvd_ncard_orbit_sub_one hQH hfix hfree
  have hdvd2 := ncard_orbit_dvd hQH hfix (s := Nat.card S) (by rw [hH, hQ])
  set m := (MulAction.orbit H (infL h)).ncard with hm
  have hmpos : 0 < m := by
    rw [hm, Set.ncard_pos]
    exact ⟨_, MulAction.mem_orbit_self _⟩
  by_cases hm1 : m = 1
  ·
    have hHfix : ∀ g ∈ H, g • infL h = infL h := by
      intro g hg
      obtain ⟨y, hy⟩ := Set.ncard_eq_one.1 hm1
      have h1 : infL h ∈ MulAction.orbit H (infL h) := MulAction.mem_orbit_self _
      have h2 : g • infL h ∈ MulAction.orbit H (infL h) :=
        MulAction.mem_orbit_iff.2 ⟨⟨g, hg⟩, rfl⟩
      rw [hy] at h1 h2
      rw [Set.mem_singleton_iff] at h1 h2
      rw [h2, h1]
    have hHS : H ≤ MulAction.stabilizer X (infL h) := fun g hg =>
      MulAction.mem_stabilizer_iff.2 (hHfix g hg)
    have hdS : Nat.card S ∣ Nat.card (MulAction.stabilizer X (infL h)) := by
      refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hHS)
      rw [hH]
      exact Dvd.intro_left _ rfl
    have htrans : MulAction.IsPretransitive X (hypIsotropicLines h 1 1) :=
      ⟨fun x y => by
        obtain ⟨g, hg⟩ := exists_smul_eq_of_range h Φ hrange x y
        exact ⟨g, by rw [hsmul]; exact hg⟩⟩
    have hmul := Subgroup.card_mul_index (MulAction.stabilizer X (infL h))
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ,
      card_hypIsotropicLines_one h, pow_one] at hmul
    have hmulS := Subgroup.card_mul_index S
    obtain ⟨c, hc⟩ := hdS
    rw [hc] at hmul
    have hpos : 0 < Nat.card S := Nat.card_pos
    have hidx : S.index = c * (p ^ 3 + 1) := by
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [hmulS, ← hmul]
      ring
    apply hSi
    rw [hidx]
    refine Dvd.dvd.mul_left ?_ _
    have hodd : p % 2 = 1 := by
      rcases hp.out.eq_two_or_odd with h2 | h2
      · omega
      · exact h2
    have : p ^ 3 % 2 = 1 := by simp [Nat.pow_mod, hodd]
    omega
  ·
    have hm2 : 2 ≤ m := by omega
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS2
    rw [hk] at hdvd2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
    have hmX : m ∣ Nat.card X := hdvd2.trans (hk ▸ Subgroup.card_subgroup_dvd_card S)
    have hX1 := card_dvd_of_model hX
    have hodd : p % 2 = 1 := by
      rcases hp.out.eq_two_or_odd with h2 | h2
      · omega
      · exact h2
    have h2j : 2 ^ j ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := hj ▸ hmX.trans hX1
    have hfin := dvd_of_dvd_two_pow (by omega) hodd h2j
    refine false_of_dvd_of_modEq (r := p) (by omega) hm2 (hj ▸ hfin) ?_
    rw [hQ] at hdvd1
    exact (pow_dvd_pow p ha).trans hdvd1

end CFSG.Quasithin.H13.NQCore.U3O

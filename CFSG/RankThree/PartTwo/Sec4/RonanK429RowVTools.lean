module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cfg
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace RowV

theorem lt_of_dvd_ordL {q B M : ℕ} (hM : 0 < M) (hB : M < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hd : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ M) : q < B := by
  by_contra h'
  have h := not_lt.mp h'
  have h1 := Nat.le_of_dvd hM hd
  have h2 : B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    gcongr
  omega

theorem lt_of_dvd_ordU {q B M : ℕ} (hM : 0 < M) (hB : M < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hd : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ M) : q < B := by
  by_contra h'
  have h := not_lt.mp h'
  have h1 := Nat.le_of_dvd hM hd
  have h2 : B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    calc B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by gcongr
      _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by gcongr; omega
  omega

theorem not_isoLThreePi_of_dvd {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {N B : ℕ}
    (hN : 0 < N) (hd : Nat.card X ∣ N) (hB : 3 * N < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hL : ∀ q < B, q % 3 = 1 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 3 * N)
    (hU : ∀ q < B, q % 3 = 2 → q ≠ 2 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 3 * N)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) : ¬ IsoLThreePi X p e := by
  have hp : p.Prime := Fact.out
  have h3d : 3 * Nat.card X ∣ 3 * N := Nat.mul_dvd_mul_left 3 hd
  have hq1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  rintro (⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩)
  · have hc := KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv] at hc
    have hg : Nat.gcd 3 (p ^ e - 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hg, mul_comm] at hc
    rw [hc] at h3d
    exact hL _ (lt_of_dvd_ordL (by omega) hB h3d) h1 h3d
  · have hc := KS14.card_projSU_three_mul_gcd p e he
    rw [← Nat.card_congr φ.toEquiv] at hc
    have hg : Nat.gcd 3 (p ^ e + 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hg, mul_comm] at hc
    by_cases hq2 : p ^ e = 2
    · rw [hq2] at hc
      have hcard : Nat.card X = 72 := by omega
      have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨rfl, rfl⟩ := (Nat.prime_two.pow_eq_iff).mp hq2
      have hs := Sec13.isSolvable_projSU_two
      have hsolv : IsSolvable X :=
        solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      exact Group.IsPerfect.not_isSolvable X hsolv
    · rw [hc] at h3d
      exact hU _ (lt_of_dvd_ordU (by omega) hB h3d) h2 hq2 h3d

theorem not_isType429_of_dvd {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {N B : ℕ}
    (hN : 0 < N) (hd : Nat.card X ∣ N) (hB : 3 * N < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hL : ∀ q < B, q % 3 = 1 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 3 * N)
    (hU : ∀ q < B, q % 3 = 2 → q ≠ 2 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 3 * N)
    (h7 : ¬ 2520 ∣ N) (h12 : ¬ 95040 ∣ N) (h22 : ¬ 443520 ∣ N) (hJ : ¬ 604800 ∣ N) :
    ¬ IsType429 X := by
  rintro (⟨p, e, hp, he, h⟩ | h | h | h | h)
  · exact not_isoLThreePi_of_dvd hN hd hB hL hU he h
  · obtain ⟨φ⟩ := h
    apply h7
    rw [← KS14.card_alternatingGroup_five_seven_ten.2.1, ← Nat.card_congr φ.toEquiv]
    exact hd
  · obtain ⟨φ⟩ := h
    apply h12
    rw [← KS14.card_nativeM12, ← Nat.card_congr φ.toEquiv]
    exact hd
  · obtain ⟨φ⟩ := h
    apply h22
    rw [← KS14.card_nativeM22, ← Nat.card_congr φ.toEquiv]
    exact hd
  · obtain ⟨φ⟩ := h
    apply hJ
    rw [← KS14.card_nativeJ2, ← Nat.card_congr φ.toEquiv]
    exact hd

theorem noCfgS429_of_dvd {S : Type} [Group S] [Finite S]
    (h : ∀ (X : Type) [Group X] [Finite X] [Group.IsPerfect X], Nat.card X ∣ Nat.card S →
      ¬ IsType429 X) :
    NoCfgS429 S := by
  intro A σ K hc
  haveI : Group.IsPerfect K := hc.isPerfect
  exact h (K ⧸ CFSG.pCore 2 K)
    ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card K)) hc.isType

theorem noCfgS429_of_card {S : Type} [Group S] [Finite S] {N B : ℕ} (hS : Nat.card S ∣ N)
    (hN : 0 < N) (hB : 3 * N < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hL : ∀ q < B, q % 3 = 1 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 3 * N)
    (hU : ∀ q < B, q % 3 = 2 → q ≠ 2 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 3 * N)
    (h7 : ¬ 2520 ∣ N) (h12 : ¬ 95040 ∣ N) (h22 : ¬ 443520 ∣ N) (hJ : ¬ 604800 ∣ N) :
    NoCfgS429 S :=
  noCfgS429_of_dvd fun _ _ _ _ hd =>
    not_isType429_of_dvd hN (hd.trans hS) hB hL hU h7 h12 h22 hJ

theorem autFix_conj_eq_centralizer {M : Type*} [Group M] (w : M) :
    autFix (MulAut.conj w) = Subgroup.centralizer ({w} : Set M) := by
  ext z
  rw [mem_autFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc z * w = w * z * w⁻¹ * w := by rw [h]
      _ = w * z := by group
  · intro h
    rw [← h]
    group

theorem noCfgS429_of_inner {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (hin : ∀ τ : MulAut S, τ ^ 3 = 1 → τ ∈ (MulAut.conj : S →* MulAut S).range) {N B : ℕ}
    (hC : ∀ x : S, orderOf x = 3 → Nat.card (Subgroup.centralizer ({x} : Set S)) ∣ N)
    (hN : 0 < N) (hB : 3 * N < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hL : ∀ q < B, q % 3 = 1 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 3 * N)
    (hU : ∀ q < B, q % 3 = 2 → q ≠ 2 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 3 * N)
    (h7 : ¬ 2520 ∣ N) (h12 : ¬ 95040 ∣ N) (h22 : ¬ 443520 ∣ N) (hJ : ¬ 604800 ∣ N) :
    NoCfgS429 S := by
  intro A σ K hc
  have h3 : σ ^ 3 = 1 := hc.isE27.1.2 σ hc.mem
  obtain ⟨s, rfl⟩ := hin σ h3
  have hs3 : s ^ 3 = 1 := by
    have h3' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow]; exact h3
    have hmem : s ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun τ : MulAut S => τ g) h3'
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [h]
        _ = s ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hs1 : s ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  haveI : Group.IsPerfect K := hc.isPerfect
  have hK : Nat.card K ∣ N := by
    have hle : K ≤ Subgroup.centralizer ({s} : Set S) := by
      rw [← autFix_conj_eq_centralizer]
      exact hc.le_autFix
    exact (Subgroup.card_dvd_of_le hle).trans (hC s hso)
  exact not_isType429_of_dvd hN ((Subgroup.card_quotient_dvd_card _).trans hK) hB hL hU h7 h12
    h22 hJ hc.isType

theorem center_eq_bot_of_simple {S : Type*} [Group S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem card_centralizer_congr {S T : Type*} [Group S] [Group T] (φ : S ≃* T) (x : S) :
    Nat.card (Subgroup.centralizer ({x} : Set S)) =
      Nat.card (Subgroup.centralizer ({φ x} : Set T)) := by
  have hmap : (Subgroup.centralizer ({x} : Set S)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ x} : Set T) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨φ.symm y, φ.injective ?_, φ.apply_symm_apply y⟩
      rw [map_mul, map_mul, φ.apply_symm_apply, hy]
  rw [← hmap]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).toEquiv

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429

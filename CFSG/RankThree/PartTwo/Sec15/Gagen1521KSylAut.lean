module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1521TDefs
import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryO.GL3
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace Proof1521KS

theorem commute_of_isPGroup_pgl3 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {S : Subgroup (Matrix.ProjGenLinGroup (Fin 3) K)}
    (hS : IsPGroup p S) : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
  haveI : Fact p.Prime := ⟨hp⟩
  let π : GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K := Matrix.ProjGenLinGroup.mk
  let H : Subgroup (GL (Fin 3) K) := S.comap π
  let f : ↥H →* ↥S := (π.comp H.subtype).codRestrict S fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
    exact ⟨⟨g, hy⟩, rfl⟩
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥H) := inferInstance
  have hQab : IsMulCommutative ↥((Q : Subgroup ↥H).map H.subtype) :=
    CFSG.SignalizerFunctorTheorem.McBride.UnitaryO.isMulCommutative_of_isPGroup_gl3 hp h5 hpK
      (Q.2.map H.subtype)
  have htop : (Q : Subgroup ↥H).map f = ⊤ := by
    rw [← Sylow.coe_mapSurjective hf Q]
    exact ((Q.mapSurjective hf).is_maximal' (hS.to_subgroup ⊤) le_top).symm
  have hlift : ∀ x ∈ S, ∃ a ∈ (Q : Subgroup ↥H).map H.subtype, π a = x := by
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥S) ∈ (Q : Subgroup ↥H).map f := htop ▸ Subgroup.mem_top _
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hmem
    exact ⟨q, Subgroup.mem_map_of_mem H.subtype hq, congrArg Subtype.val hqx⟩
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := hlift x hx
  obtain ⟨b, hb, rfl⟩ := hlift y hy
  have hab : a * b = b * a :=
    congrArg Subtype.val ((isMulCommutative_iff.mp hQab) ⟨a, ha⟩ ⟨b, hb⟩)
  rw [← map_mul, ← map_mul, hab]

theorem isMulCommutative_of_injective_pgl3 {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (φ : X →* Matrix.ProjGenLinGroup (Fin 3) K) (hφ : Function.Injective φ) (S : Subgroup X)
    (hS : IsPGroup p S) : IsMulCommutative S := by
  have h := commute_of_isPGroup_pgl3 hp h5 hpK (hS.map φ)
  refine isMulCommutative_iff.mpr fun a b => Subtype.ext (hφ ?_)
  simp only [Subgroup.coe_mul, map_mul]
  exact h _ (Subgroup.mem_map_of_mem φ a.2) _ (Subgroup.mem_map_of_mem φ b.2)

theorem not_dvd_of_isChoice1519 {m p : ℕ} (hm : 1 ≤ m) (hp2 : p ≠ 2) (h : IsChoice1519 m p) :
    ¬ p ∣ m := by
  obtain ⟨hp, hsign, hcase⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  have hF : ∀ n : ℕ, (2 : ZMod p) ^ (p * n) = (2 : ZMod p) ^ n := fun n => by
    rw [pow_mul, ZMod.pow_card]
  rintro ⟨n, rfl⟩
  have hn : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hm
  rcases hcase with ⟨k, hk, -, hk1, hkmin⟩ | ⟨-, hmin⟩
  · have hpk : p ∣ k := by
      have hdvd : p ∣ 2 * k := ⟨n, hk.symm⟩
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hp2
      · exact h2
    obtain ⟨k', rfl⟩ := hpk
    have hk' : 1 ≤ k' := by
      rcases Nat.eq_zero_or_pos k' with h0 | h0
      · subst h0
        have h0' : p * n = 0 := by rw [hk]; ring
        rcases Nat.mul_eq_zero.mp h0' with h | h
        · exact absurd h hp.ne_zero
        · omega
      · exact h0
    refine hkmin k' (Dvd.intro_left p rfl) ?_ (by rw [← hF k']; exact hk1)
    exact lt_mul_left hk' hp.one_lt
  · refine hmin n (Dvd.intro_left p rfl) (lt_mul_left hn hp.one_lt) ?_
    rw [← hF n]
    exact hsign

theorem not_dvd_two_mul_mul {p m d : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpm : ¬ p ∣ m)
    (hd : d ∣ 3) : ¬ p ∣ 2 * m * d := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact absurd (Nat.le_of_dvd two_pos h) (by omega)
    · exact hpm h
  · exact absurd (Nat.le_of_dvd three_pos (h.trans hd)) (by omega)

theorem exists_eq_conj_of_pow_eq_one {X : Type} [Group X] [Finite X] {p N : ℕ} (hp : p.Prime)
    (hout : Nat.card (Outer X) ∣ N) (hpN : ¬ p ∣ N) (φ : MulAut X) (k : ℕ)
    (hφ : φ ^ p ^ k = 1) : ∃ x : X, φ = MulAut.conj x := by
  set π := QuotientGroup.mk' (inner X) with hπ
  have h1 : orderOf (π φ) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hφ, map_one])
  have h2 : orderOf (π φ) ∣ N := (orderOf_dvd_natCard (π φ)).trans hout
  have hcop : Nat.Coprime (p ^ k) N :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)
  have h3 : orderOf (π φ) = 1 := Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  obtain ⟨x, hx⟩ := h3
  exact ⟨x, hx.symm⟩

end Proof1521KS

open Proof1521KS

theorem ks1521SylAut : KS1521SylAut := by
  intro X _ _ m hm hX p hch hp3
  have hp : p.Prime := hch.1
  haveI : Fact p.Prime := ⟨hp⟩
  have h5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p
      exact absurd hp (by norm_num)
    · exact h
  have hpm : ¬ p ∣ m := not_dvd_of_isChoice1519 hm (by omega) hch
  have hp2pow : ∀ n : ℕ, ¬ p ∣ 2 ^ n := fun n h =>
    absurd (Nat.le_of_dvd two_pos (hp.dvd_of_dvd_pow h)) (by omega)
  have hm0 : m ≠ 0 := by omega
  rcases hX with ⟨-, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 2 m := by
      refine ⟨Nat.prime_two, hm, ?_⟩
      simp
    have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) le_rfl Nat.prime_two hm
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm e)).1
    refine ⟨fun S hS => isMulCommutative_of_injective_pgl3 hp h5 ?_
      ((CFSG.PGLModel.projSL 3 (GaloisField 2 m)).subtype.comp e.toMonoidHom)
      (Subtype.val_injective.comp e.injective) S hS,
      fun φ k hφ => exists_eq_conj_of_pow_eq_one hp hout
        (not_dvd_two_mul_mul hp hp3 hpm (Nat.gcd_dvd_left 3 _)) φ k hφ⟩
    rw [GaloisField.card 2 m hm0]
    exact hp2pow m
  · have hm1 : m ≠ 1 := by
      rintro rfl
      have h2 := hch.2.1
      simp only [sign1519, pow_one] at h2
      rw [if_neg (by norm_num)] at h2
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by
        have h32 : ((3 : ℕ) : ZMod p) = (2 : ZMod p) + 1 := by push_cast; ring
        rw [h32, h2]
        ring
      rw [ZMod.natCast_eq_zero_iff] at h3
      exact absurd (Nat.le_of_dvd three_pos h3) (by omega)
    have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 2 m := by
      refine ⟨Nat.prime_two, hm, le_rfl, ?_⟩
      intro h
      have h' : 2 ^ m = 2 ^ 1 := by simpa using h
      exact hm1 (Nat.pow_right_injective le_rfl h')
    have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) le_rfl Nat.prime_two hm
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e)).1
    refine ⟨fun S hS => isMulCommutative_of_injective_pgl3 hp h5 ?_
      ((CFSG.PGLModel.projSU 3 2 m).subtype.comp e.toMonoidHom)
      (Subtype.val_injective.comp e.injective) S hS,
      fun φ k hφ => exists_eq_conj_of_pow_eq_one hp hout
        (not_dvd_two_mul_mul hp hp3 hpm (Nat.gcd_dvd_left 3 _)) φ k hφ⟩
    rw [GaloisField.card 2 (2 * m) (by omega)]
    exact hp2pow (2 * m)

end CFSG.RankThree.PartTwo.Sec15

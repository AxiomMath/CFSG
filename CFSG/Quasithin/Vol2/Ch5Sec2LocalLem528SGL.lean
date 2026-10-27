module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases1
public import CFSG.Sporadic.J4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint
open CFSG.LieType.BorelTits
open scoped commutatorElement

theorem card_GL_dvd_GL9 {d : ℕ} (hd : d ≤ 9) :
    Nat.card (GL (Fin d) (ZMod 2)) ∣ 699612310033197642547200 := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases d <;> decide

theorem prime_dvd_card_GL_nine {p : ℕ} (hp : p.Prime) (h : p ∣ 699612310033197642547200) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 31 ∨ p = 73 ∨ p = 127 := by
  have e : (699612310033197642547200 : ℕ) =
      2 ^ 36 * 3 ^ 5 * 5 ^ 2 * 7 ^ 3 * 17 * 31 * 73 * 127 := by norm_num
  rw [e] at h
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
            · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
              · exact Or.inl (hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h))
              · exact Or.inr (Or.inl (hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h)))
            · exact Or.inr (Or.inr (Or.inl (hq 5 Nat.prime_five (hp.dvd_of_dvd_pow h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) (hp.dvd_of_dvd_pow h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 17 (by norm_num) h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 31 (by norm_num) h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 73 (by norm_num) h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hq 127 (by norm_num) h)))))))

variable {X : Type} [Group X]

theorem false_of_dvd_gl9
    (h : Nat.card X ∣ 699612310033197642547200)
    (hX : IsPSL 2 5 2 X ∨
      (∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 X) ∨
      IsSporadic .J1 X ∨ IsSporadic .J4 X) : False := by
  have hsp : ∀ {s : TauCeti.SporadicName} {N : ℕ}, Nat.card (NativeSporadic.Carrier s) = N →
      IsSporadic s X → Nat.card X = N := fun hN ⟨e⟩ => (Nat.card_congr e.toEquiv).trans hN
  rcases hX with hX | ⟨p, hp, hp5, hp8, hX⟩ | hX | hX
  · rw [card_of_isPSL (by norm_num) hX] at h
    exact absurd h (by decide)
  · have h2 := two_mul_card_of_isPSL_two hp (by omega) hX
    have hpX : p ∣ Nat.card X := by
      have : p ∣ 2 * Nat.card X := h2 ▸ dvd_mul_right p _
      exact ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)).dvd_of_dvd_mul_left this
    rcases prime_dvd_card_GL_nine hp (hpX.trans h) with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> simp_all
  · rw [hsp (s := .J1) (N := 175560) CFSG.Sporadic.J1.card_J1 hX] at h
    exact absurd h (by decide)
  · rw [hsp (s := .J4) (N := 86775571046077562880) CFSG.Sporadic.J4.card_J4 hX] at h
    exact absurd h (by decide)

variable {G : Type} [Group G] [Finite G]

noncomputable def pCoreConj (Kh : Subgroup G) : ↥Kh →* MulAut ↥(pCoreOf 2 Kh) :=
  (pCoreOf 2 Kh).normalizerMonoidHom.comp (Subgroup.inclusion (le_normalizer_pCoreOf 2 Kh))

noncomputable def frattiniRep (Kh : Subgroup G) :
    ↥Kh →* MulAut (↥(pCoreOf 2 Kh) ⧸ frattini ↥(pCoreOf 2 Kh)) :=
  (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
    (frattini ↥(pCoreOf 2 Kh))).comp (pCoreConj Kh)

omit [Finite G] in
theorem pCoreConj_apply_coe (Kh : Subgroup G) (g : ↥Kh) (r : ↥(pCoreOf 2 Kh)) :
    ((pCoreConj Kh g r : ↥(pCoreOf 2 Kh)) : G) = (g : G) * r * (g : G)⁻¹ := by
  simp [pCoreConj]

omit [Finite G] in
theorem mem_of_pCoreConj_eq_one {Kh : Subgroup G}
    (hchar : Kh ⊓ Subgroup.centralizer (pCoreOf 2 Kh : Set G) ≤ pCoreOf 2 Kh) {g : ↥Kh}
    (hg : pCoreConj Kh g = 1) : (g : G) ∈ pCoreOf 2 Kh := by
  refine hchar (Subgroup.mem_inf.mpr ⟨g.2, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩)
  have h3 := congrArg (fun a : MulAut ↥(pCoreOf 2 Kh) => ((a ⟨r, hr⟩ : ↥(pCoreOf 2 Kh)) : G)) hg
  simp only [pCoreConj_apply_coe, MulAut.one_apply] at h3
  calc r * (g : G) = ((g : G) * r * (g : G)⁻¹) * (g : G) := by rw [h3]
    _ = (g : G) * r := by group

theorem ker_frattiniRep {Kh : Subgroup G}
    (hchar : Kh ⊓ Subgroup.centralizer (pCoreOf 2 Kh : Set G) ≤ pCoreOf 2 Kh) :
    (frattiniRep Kh).ker = (pCoreOf 2 Kh).subgroupOf Kh := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (pCoreOf 2 Kh) := pCoreOf_isPGroup 2 Kh
  have hf2 : IsPGroup 2 (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini ↥(pCoreOf 2 Kh))).ker :=
    CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup 2 hR2
  have hcomm := (CFSG.GroupTheory.frattini_elementary_quotient hR2).2.1
  apply le_antisymm
  ·
    have hker2 : IsPGroup 2 (frattiniRep Kh).ker := by
      intro g
      obtain ⟨n, hn⟩ := hf2 ⟨pCoreConj Kh g, g.2⟩
      have h1 : pCoreConj Kh ((g : ↥Kh) ^ 2 ^ n) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hn
      have h2 := mem_of_pCoreConj_eq_one hchar h1
      obtain ⟨m, hm⟩ := hR2 ⟨_, h2⟩
      refine ⟨n + m, Subtype.ext (Subtype.ext ?_)⟩
      have hm' : ((((g : ↥Kh) ^ 2 ^ n : ↥Kh) : G)) ^ 2 ^ m = 1 := congrArg Subtype.val hm
      rw [SubgroupClass.coe_pow] at hm'
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [pow_add, pow_mul, hm']
    have hnorm : Kh ≤ Subgroup.normalizer
        (((frattiniRep Kh).ker.map Kh.subtype : Subgroup G) : Set G) := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
      rw [show ((frattiniRep Kh).ker.map Kh.subtype).subgroupOf Kh = (frattiniRep Kh).ker from
        Subgroup.comap_map_eq_self_of_injective Kh.subtype_injective _]
      exact MonoidHom.normal_ker _
    have hle := le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _) hnorm
      (hker2.map Kh.subtype)
    intro g hg
    exact hle ⟨g, hg, rfl⟩
  ·
    intro g hg
    have hg' : (g : G) ∈ pCoreOf 2 Kh := hg
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥(pCoreOf 2 Kh)) y
    change CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism _ (pCoreConj Kh g)
      (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply]
    have e : pCoreConj Kh g x = ⟨(g : G), hg'⟩ * x * ⟨(g : G), hg'⟩⁻¹ :=
      Subtype.ext (by rw [pCoreConj_apply_coe]; rfl)
    rw [e, map_mul, map_mul, map_inv, hcomm.is_comm.comm (QuotientGroup.mk' _ _)
      (QuotientGroup.mk' _ x), mul_assoc, mul_inv_cancel, mul_one]

theorem card_frattini_quotient_le {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hR : Nat.card R ≤ 2 ^ 11) (hc : 4 ≤ Nat.card (⁅R, R⁆ : Subgroup G)) :
    Nat.card (↥R ⧸ frattini ↥R) ≤ 2 ^ 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := (CFSG.GroupTheory.frattini_elementary_quotient hR2).2.1
  have hle : ⁅R, R⁆ ≤ (frattini ↥R).map R.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : ↥R), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hcomm.is_comm.comm (QuotientGroup.mk (s := frattini ↥R) ⟨a, ha⟩)
        (QuotientGroup.mk ⟨b, hb⟩)]
    group
  have h1 : 4 ≤ Nat.card (frattini ↥R) := by
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective R.subtype_injective] at this
    omega
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥R)
  by_contra hgt
  have : 2 ^ 9 * 4 < Nat.card (↥R ⧸ frattini ↥R) * Nat.card (frattini ↥R) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (lt_of_not_ge hgt) (by norm_num))
      (Nat.mul_le_mul_left _ h1)
  rw [← h2] at this
  have h3 : Nat.card ↥R = Nat.card R := rfl
  omega

end CFSG.Quasithin.H13

module

public import CFSG.Walter.Bender1970.S2.Involutions
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups
public import CFSG.Assembly.Defs

public section

namespace CFSG.Walter

open scoped MatrixGroups Pointwise

@[expose] def CyclicFreeNormalizer {L : Type*} [Group L] (S : Subgroup L) : Prop :=
  ∃ d ∈ Subgroup.normalizer (S : Set L),
    (∀ n ∈ Subgroup.normalizer (S : Set L), ∃ m : ℕ, ∀ v ∈ S, n * v * n⁻¹ = d ^ m * v * (d ^ m)⁻¹) ∧
    (∀ n ∈ Subgroup.normalizer (S : Set L), ∀ u ∈ S, u ≠ 1 → n * u * n⁻¹ = u →
      ∀ v ∈ S, n * v * n⁻¹ = v)

structure Bender38Type (L : Type*) [Group L] : Prop where
  sylow : ∀ S : Sylow 2 L, (∀ x ∈ (S : Subgroup L), x ^ 2 = 1) ∧ 4 ≤ Nat.card S
  isConj : ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y
  normalizer : ∀ S : Sylow 2 L, 8 < Nat.card S → CyclicFreeNormalizer (S : Subgroup L)
  psl : ∀ S : Sylow 2 L, Nat.card S = 4 → ∃ p f : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 0 < f ∧
    5 ≤ p ^ f ∧ Nonempty (L ≃* PSL(2, GaloisField p f))

section Transport

variable {L P : Type*} [Group L] [Group P]

theorem CyclicFreeNormalizer.of_mulEquiv (e : L ≃* P) {S : Subgroup L}
    (h : CyclicFreeNormalizer (S.map e.toMonoidHom)) : CyclicFreeNormalizer S := by
  obtain ⟨d, hd, hcyc, hfree⟩ := h
  have hmemS : ∀ v : L, e v ∈ S.map e.toMonoidHom ↔ v ∈ S := fun v => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hN : ∀ n : L, e n ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup P) : Set P) ↔
      n ∈ Subgroup.normalizer (S : Set L) := by
    intro n
    simp only [Subgroup.mem_normalizer_iff]
    constructor
    · intro h v
      rw [← hmemS, ← hmemS (n * v * n⁻¹), map_mul, map_mul, map_inv]
      exact h (e v)
    · intro h w
      obtain ⟨v, rfl⟩ := e.surjective w
      rw [hmemS, ← map_inv, ← map_mul, ← map_mul, hmemS]
      exact h v
  refine ⟨e.symm d, (hN _).mp (by rwa [MulEquiv.apply_symm_apply]), fun n hn => ?_,
    fun n hn u hu hu1 hnu v hv => ?_⟩
  · obtain ⟨m, hm⟩ := hcyc (e n) ((hN n).mpr hn)
    refine ⟨m, fun v hv => e.injective ?_⟩
    have := hm (e v) ((hmemS v).mpr hv)
    simpa [map_mul, map_inv, map_pow] using this
  · apply e.injective
    have h1 := hfree (e n) ((hN n).mpr hn) (e u) ((hmemS u).mpr hu)
      (fun h => hu1 (e.injective (h.trans (map_one e).symm)))
      (by rw [← map_inv, ← map_mul, ← map_mul, hnu])
      (e v) ((hmemS v).mpr hv)
    simpa [map_mul, map_inv] using h1

end Transport

section Even

variable {f : ℕ}

theorem psl2_even_cyclicFreeNormalizer (hf : 2 ≤ f) (U : Sylow 2 PSL(2, GaloisField 2 f)) :
    CyclicFreeNormalizer (U : Subgroup PSL(2, GaloisField 2 f)) := by
  classical
  set P := PSL(2, GaloisField 2 f)
  set Ug := (U : Subgroup P) with hUg
  obtain ⟨D, hDcyc, -, hUD, hsup, hreg⟩ := psl2_even_normalizer_sylow_two hf U
  obtain ⟨hUel, -⟩ := psl2_even_sylow_two hf U
  have hUcomm : ∀ a ∈ Ug, ∀ b ∈ Ug, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDN : D ≤ Subgroup.normalizer (Ug : Set P) := hsup ▸ le_sup_right
  have hprod : ((D ⊔ Ug : Subgroup P) : Set P) = (D : Set P) * (Ug : Set P) :=
    Subgroup.coe_mul_of_left_le_normalizer_right D Ug hDN
  have hmemN : ∀ n ∈ Subgroup.normalizer (Ug : Set P), ∃ d ∈ D, ∃ u ∈ Ug, d * u = n := by
    intro n hn
    rw [← hsup, sup_comm] at hn
    have : n ∈ ((D ⊔ Ug : Subgroup P) : Set P) := hn
    rw [hprod] at this
    obtain ⟨d, hd, u, hu, hdu⟩ := this
    exact ⟨d, hd, u, hu, hdu⟩
  obtain ⟨d₀, hd₀⟩ := IsCyclic.exists_generator (α := D)
  have hconj : ∀ d u v : P, u ∈ Ug → v ∈ Ug → d * u * v * (d * u)⁻¹ = d * v * d⁻¹ := by
    intro d u v hu hv
    calc d * u * v * (d * u)⁻¹ = d * (u * v * u⁻¹) * d⁻¹ := by group
      _ = d * v * d⁻¹ := by rw [hUcomm u hu v hv, mul_inv_cancel_right]
  refine ⟨d₀, hDN d₀.2, fun n hn => ?_, fun n hn u hu hu1 hnu v hv => ?_⟩
  · obtain ⟨d, hd, u, hu, rfl⟩ := hmemN n hn
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers.mpr (hd₀ ⟨d, hd⟩) :
      (⟨d, hd⟩ : D) ∈ Submonoid.powers d₀)
    refine ⟨m, fun v hv => ?_⟩
    rw [hconj d u v hu hv]
    have : (d₀ : P) ^ m = d := congrArg Subtype.val hm
    rw [this]
  · obtain ⟨d, hd, u', hu', rfl⟩ := hmemN n hn
    rw [hconj d u' u hu' hu] at hnu
    obtain ⟨d', -, huniq⟩ := hreg u hu hu1 u hu hu1
    have h1 : (⟨d, hd⟩ : D) = d' := huniq ⟨d, hd⟩ hnu
    have h2 : (1 : D) = d' := huniq 1 (by simp)
    have hd1 : d = 1 := congrArg Subtype.val (h1.trans h2.symm)
    rw [hconj d u' v hu' hv, hd1, one_mul, inv_one, mul_one]

end Even

theorem bender38Type_of_isTypeL2_or_isTypeJR
    {L : Type} [Group L] [Finite L]
    (hnonab : ∃ a b : L, a * b ≠ b * a) (hL : IsTypeL2 L ∨ IsTypeJR L) : Bender38Type L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    fun x y hx hy => isConj_of_isTypeL2_or_isTypeJR hL hx hy
  have hsylow : ∀ {P : Type} [Group P] [Finite P] (e : L ≃* P) (S : Sylow 2 L),
      ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 P) : Subgroup P) =
        (S : Subgroup L).map e.toMonoidHom := fun e S => Sylow.coe_mapSurjective _ _
  have hcardmap : ∀ {P : Type} [Group P] (e : L ≃* P) (S : Subgroup L),
      Nat.card (S.map e.toMonoidHom) = Nat.card S := fun e S =>
    Subgroup.card_map_of_injective e.injective
  have hsq : ∀ {P : Type} [Group P] (e : L ≃* P) (S : Subgroup L),
      (∀ x ∈ S.map e.toMonoidHom, x ^ 2 = 1) → ∀ x ∈ S, x ^ 2 = 1 := by
    intro P _ e S h x hx
    apply e.injective
    rw [map_pow, map_one]
    exact h (e x) ⟨x, hx, rfl⟩
  have helem : ∀ {P : Type} [Group P] (A : Subgroup P), IsElementaryAbelian 2 A →
      ∀ x ∈ A, x ^ 2 = 1 := fun A hA x hx => by
    have := hA
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  rcases hL with hL2 | hJR
  · rcases isTypeL2_iff.mp hL2 with ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩
    ·
      have hU : ∀ S : Sylow 2 L, IsElementaryAbelian 2 ((S : Subgroup L).map e.toMonoidHom) ∧
          Nat.card S = 2 ^ f := by
        intro S
        have h := psl2_even_sylow_two hf (S.mapSurjective (f := e.toMonoidHom) e.surjective)
        rw [hsylow e S] at h
        exact ⟨h.1, (hcardmap e S).symm.trans h.2⟩
      refine ⟨fun S => ⟨hsq e S (helem _ (hU S).1), ?_⟩, hconj, fun S _ => ?_, fun S hS4 => ?_⟩
      · rw [(hU S).2]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      · have h := psl2_even_cyclicFreeNormalizer hf
          (S.mapSurjective (f := e.toMonoidHom) e.surjective)
        rw [hsylow e S] at h
        exact CyclicFreeNormalizer.of_mulEquiv e h
      · have hf2 : f = 2 := by
          have h := (hU S).2
          rw [hS4] at h
          exact Nat.pow_right_injective (le_refl 2) (show 2 ^ f = 2 ^ 2 by rw [← h])
        subst hf2
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        obtain ⟨e'⟩ := nonempty_psl2_five_mulEquiv_psl2_four
        exact ⟨5, 1, inferInstance, by decide, one_pos, by norm_num, ⟨e.trans e'.symm⟩⟩
    ·
      have hU : ∀ S : Sylow 2 L, IsKleinFour ((S : Subgroup L).map e.toMonoidHom) := by
        intro S
        have h := psl2_odd_sylow_two_isKleinFour hpodd hf h8
          (S.mapSurjective (f := e.toMonoidHom) e.surjective)
        rwa [hsylow e S] at h
      have hcard : ∀ S : Sylow 2 L, Nat.card S = 4 := fun S =>
        (hcardmap e S).symm.trans (hU S).card_four
      refine ⟨fun S => ⟨hsq e S fun x hx => ?_, (hcard S).ge⟩, hconj,
        fun S hS => absurd hS (by rw [hcard S]; norm_num),
        fun _ _ => ⟨p, f, hp, hpodd, hf, h5, ⟨e⟩⟩⟩
      have := hU S
      have h1 := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : (S : Subgroup L).map e.toMonoidHom)
      rw [IsKleinFour.exponent_two] at h1
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.coe_pow] at h2
      exact h2
  ·
    have hS := fun S => hJR.sylow_two_of_nonabelian hnonab S
    refine ⟨fun S => ⟨helem _ (hS S).1, by rw [(hS S).2]; norm_num⟩, hconj,
      fun S h => absurd h (by rw [(hS S).2]; norm_num),
      fun S h => absurd h (by rw [(hS S).2]; norm_num)⟩

end CFSG.Walter

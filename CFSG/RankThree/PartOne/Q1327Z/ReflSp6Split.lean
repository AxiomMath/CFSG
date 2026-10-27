module

public import CFSG.RankThree.PartOne.Q1327Z.SpRoot
public import CFSG.RankThree.PartOne.Q1327C.BSp6
public import CFSG.RankThree.PartOne.N143X.PRankTorus

public section

namespace CFSG.RankThree.PartOne.Q1327Z

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327C CFSG.RankThree.PartOne.Q1327T
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.RankThree.PartTwo.Census
  CFSG.LieType.Universal.Symplectic.SpExtras

section Torus

variable {K : Type} [Field K] {p : ℕ}

theorem torusP_eq_spTorus (hp : p ≠ 0) : torusP p K = KFCL.Sp.spTorus p 3 K := by
  ext x
  rw [mem_torusP, KFCL.Sp.mem_spTorus_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => (t i : K), fun i => ?_, ?_⟩
    · have := congrArg Units.val (ht i)
      simpa using this
    · rw [mat_apply, coe_torusHom]
      congr 1
      funext a
      rcases a with i | i <;> simp
  · rintro ⟨y, hy, hxy⟩
    have hy0 : ∀ i, y i ≠ 0 := fun i h0 => by
      have := hy i
      rw [h0, zero_pow hp] at this
      exact zero_ne_one this
    refine ⟨fun i => Units.mk0 (y i) (hy0 i), fun i => Units.ext (by simpa using hy i), ?_⟩
    apply mat_injective
    rw [hxy, mat_apply, coe_torusHom]
    congr 1

end Torus

variable {G : Type} [Group G] [Finite G]

theorem refl_sp6split {p : ℕ} {X A₀ F : Subgroup G} (h : Q1327.T123Base p X A₀ F)
    (hm : Sp6Cell p X) {t : MulAut ↥F} (ht : t ∈ torusImage F X) (hrefl : IsAutReflection p F t)
    {c₀ : G} (hc₀ : c₀ ∈ autMovedInG F t) (hc₀1 : c₀ ≠ 1) :
    ∃ y ∈ X ⊓ Subgroup.centralizer (autFixedInG F t : Set G), ¬ Commute c₀ (y * c₀ * y⁻¹) := by
  classical
  obtain ⟨f, hf1, hpq, hcl⟩ := hm
  have hcl' := hcl
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hcl'
  have hp := h.prime
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  let N : Subgroup ↥(StatedSp 3 K) := (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K)
  have hN : N = ⊥ :=
    CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by norm_num)
  let Ψ : (↥X ⧸ Subgroup.center ↥X) ≃* StatedSp 3 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot)
  have hordY : Nat.card (↥X ⧸ Subgroup.center ↥X) = CFSG.Open.ordBC 3 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.1 rfl
  have hcardM : Nat.card (StatedSp 3 K) = CFSG.Open.ordBC 3 (2 ^ f) := by
    rw [← hordY]
    exact (Nat.card_congr Ψ.toEquiv).symm
  have hKu : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
  have hrK : p ∣ Nat.card Kˣ := by rw [hKu]; exact hpq
  have hTcard : Nat.card (torus 3 K) = (2 ^ f - 1) ^ 3 := by
    have h1 : Nat.card (torus 3 K) = Nat.card (Fin 3 → Kˣ) :=
      (Nat.card_congr (MonoidHom.ofInjective (torusHom_injective (r := 3) (k := K))).toEquiv).symm
    rw [h1, Nat.card_fun, hKu, Nat.card_fin]
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hidx : ¬ p ∣ (torus 3 K).index := by
    apply not_dvd_index_of_val
    rw [hcardM, hTcard]
    have hpq1 : ¬ p ∣ 2 ^ f := by
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
      omega
    have hprod : CFSG.Open.ordBC 3 (2 ^ f) =
        (2 ^ f) ^ 9 * (((2 ^ f) ^ 2 - 1) * (((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1))) := by
      rw [CFSG.Open.ordBC, gcd_two_two_pow_sub_one hf1, Nat.div_one]
      have : Finset.Icc 1 3 = {1, 2, 3} := by decide
      rw [this, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
    have hne1 : (2 ^ f - 1) ≠ 0 := by omega
    have hn2 : ∀ m : ℕ, 1 ≤ m → (2 ^ f) ^ m - 1 ≠ 0 := fun m hm1 => by
      have : 1 < (2 ^ f) ^ m := Nat.one_lt_pow (by omega) (by omega)
      omega
    have hnd2 : ¬ p ∣ 2 := fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hnd4 : ¬ p ∣ 4 := fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hnd6 : ¬ p ∣ 6 := fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases p
      · omega
      · exact absurd hp (by norm_num)
    have hvals : ∀ m : ℕ, 1 ≤ m → ¬ p ∣ m →
        padicValNat p ((2 ^ f) ^ m - 1) = padicValNat p (2 ^ f - 1) := fun m hm1 hmp => by
      have := padicValNat_pow_sub_one_eq (p := p) (q := 2 ^ f) (m := m) hp5 hq2 hpq hm1 hmp
      simpa using this
    have hv2 := hvals 2 (by norm_num) hnd2
    have hv4 := hvals 4 (by norm_num) hnd4
    have hv6 := hvals 6 (by norm_num) hnd6
    have hz : padicValNat p ((2 ^ f) ^ 9) = 0 := padicValNat.eq_zero_of_not_dvd (fun hd =>
      hpq1 (hp.dvd_of_dvd_pow hd))
    have hM : padicValNat p (CFSG.Open.ordBC 3 (2 ^ f)) = 3 * padicValNat p (2 ^ f - 1) := by
      rw [hprod, padicValNat.mul (pow_ne_zero 9 (by omega))
        (mul_ne_zero (hn2 2 (by omega)) (mul_ne_zero (hn2 4 (by omega)) (hn2 6 (by omega)))),
        padicValNat.mul (hn2 2 (by omega)) (mul_ne_zero (hn2 4 (by omega)) (hn2 6 (by omega))),
        padicValNat.mul (hn2 4 (by omega)) (hn2 6 (by omega)), hz, hv2, hv4, hv6]
      ring
    have hT : padicValNat p ((2 ^ f - 1) ^ 3) = 3 * padicValNat p (2 ^ f - 1) :=
      padicValNat.pow (2 ^ f - 1) 3
    rw [hM, hT]
  let E : Subgroup (↥X ⧸ Subgroup.center ↥X) := bar X F
  have hEel : IsElementaryAbelian p E := barF_elem h
  let Em : Subgroup (StatedSp 3 K) := E.map Ψ.toMonoidHom
  have hEmP : IsPGroup p Em := (IsElementaryAbelian.isPGroup p E).map Ψ.toMonoidHom
  obtain ⟨g, hg⟩ := N143X.exists_conj_map_le_of_not_dvd_index' hidx hEmP
  let χ : (↥X ⧸ Subgroup.center ↥X) ≃* StatedSp 3 K := Ψ.trans (MulAut.conj g)
  have hEχ : E.map χ.toMonoidHom = Em.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  have hle : E.map χ.toMonoidHom ≤ torusP p K := by
    rintro x hx
    have hxT : x ∈ torus 3 K := hg (hEχ ▸ hx)
    obtain ⟨t, rfl⟩ := hxT
    obtain ⟨y, hy, hyx⟩ := hx
    have hyp : y ^ p = 1 := barF_exp h y hy
    have h1 : torusHom (t ^ p) = (1 : StatedSp 3 K) := by
      rw [map_pow]
      have : (χ y) ^ p = 1 := by rw [← map_pow, hyp, map_one]
      rwa [show χ y = torusHom t from hyx] at this
    have h2 : t ^ p = 1 := torusHom_injective (by rw [h1, map_one])
    exact mem_torusP.2 ⟨t, fun i => by simpa using congrFun h2 i, rfl⟩
  have hcardE : Nat.card (E.map χ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective χ.injective]
    exact barF_card h
  have hE : E.map χ.toMonoidHom = torusP p K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_torusP hp hrK, hcardE])
  let ε : ↥X →* StatedSp 3 K := χ.toMonoidHom.comp (proj X)
  have hT : (F.subgroupOf X).map ε = torusP p K := by
    rw [← hE]
    exact (Subgroup.map_map _ _ _).symm
  refine refl_of_quotient h ε (χ.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ ?_ ht hrefl
    hc₀ hc₀1
  · intro z hz
    have h1 : χ (proj X z) = 1 := hz
    have h2 : proj X z = 1 := (map_eq_one_iff χ χ.injective).1 h1
    exact (QuotientGroup.eq_one_iff z).1 h2
  · rw [hT, torusP_eq_spTorus hp.ne_zero]
    exact noncommOK_spTorus hp

end CFSG.RankThree.PartOne.Q1327Z

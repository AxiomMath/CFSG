module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL2Aut
public import CFSG.Quasithin.EmptyFaithful.Insp7NumA

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.K1 CFSG.GorensteinWalter
  CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

namespace Insp7

theorem ringEquiv_eq_one_of_card_prime {F : Type} [Field F] [Fintype F] {p : ℕ} (hp : p.Prime)
    (hF : Fintype.card F = p) (σ : F ≃+* F) : σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  let e : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp hF).symm
  have h : (e.toRingHom.comp (σ.toRingHom.comp e.symm.toRingHom)) = RingHom.id (ZMod p) :=
    RingHom.ext_zmod _ _
  ext x
  have h1 := congrArg (fun f : ZMod p →+* ZMod p => f (e x)) h
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply, RingHom.id_apply] at h1
  exact e.injective h1

theorem sq_inner_psl2 {K : Type} [Field K] [Fintype K] [DecidableEq K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Fintype.card K = p) (hq5 : 5 ≤ p) (α : MulAut PSL(2, K)) :
    ∃ g : PSL(2, K), α * α = MulAut.conj g := by
  have : Fact p.Prime := ⟨hp⟩
  have hKc : Nat.card K = p ^ 1 := by rw [Nat.card_eq_fintype_card, hK, pow_one]
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, hKc⟩
  have hcard3 : 3 < Nat.card K := by rw [Nat.card_eq_fintype_card, hK]; omega
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective K hKc hodd hcard3 α
  have hσ : x.right = 1 := ringEquiv_eq_one_of_card_prime hp hK x.right
  have hαx : α = pgl2InnerAutPSL2 K hodd hcard3 x.left := by
    rw [← hx, pGammaL2ToMulAutPSL2_eq_mul, hσ, map_one, mul_one]
  have hmem := Subgroup.mul_self_mem_of_index_two (pgl2_psl2Range_index_eq_two K hodd) x.left
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, ?_⟩
  rw [hαx, ← map_mul, ← hg, pgl2InnerAutPSL2_toPGL]

theorem exists_two_pow_of_fermatMersenne {p n : ℕ} (hFM : IsFermatOrMersennePrime p) (hq5 : 5 ≤ p)
    (hn : n * 2 = if p % 4 = 1 then p - 1 else p + 1) : ∃ a : ℕ, n = 2 ^ a := by
  obtain ⟨-, ⟨k, hk⟩ | ⟨k, hk2, hk⟩⟩ := hFM
  ·
    have hk1 : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      subst this
      simp at hk
      omega
    have h4 : 2 ^ 2 ∣ 2 ^ (2 ^ k) :=
      Nat.pow_dvd_pow 2 (by calc 2 = 2 ^ 1 := by norm_num
                              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1)
    have hp4 : p % 4 = 1 := by omega
    rw [ite_eq_left hp4] at hn
    refine ⟨2 ^ k - 1, ?_⟩
    have h2 : 2 ^ (2 ^ k) = 2 ^ (2 ^ k - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    omega
  ·
    have h4 : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk2
    have hpos : 0 < 2 ^ k := by positivity
    have hp4 : p % 4 ≠ 1 := by omega
    rw [ite_eq_right hp4] at hn
    refine ⟨k - 1, ?_⟩
    have h2 : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    omega

theorem exists_two_pow_card_centralizer_psl2 {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} (hFM : IsFermatOrMersennePrime p) (hK : Fintype.card K = p) (hchar : ringChar K ≠ 2)
    (hq5 : 5 ≤ p) {t : PSL(2, K)} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ a : ℕ, Nat.card (Subgroup.centralizer ({t} : Set PSL(2, K))) = 2 ^ a := by
  obtain ⟨T₀, w, hcyc, hw, hw2, hinv, hconj, hcent, hcard⟩ :=
    psl2_torus_data hchar (hK ▸ hq5)
  obtain ⟨x, hxT, hx⟩ := hconj t ht2 ht1
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply ht1
    have h1 : c * t * c⁻¹ = 1 := hc
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  have hx2 : x * x = 1 := by
    rw [← hc]
    calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hmap : (Subgroup.centralizer ({t} : Set PSL(2, K))).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({x} : Set PSL(2, K)) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : g * t = t * g := hg
      rw [← hc]
      calc c * g * c⁻¹ * (c * t * c⁻¹) = c * (g * t) * c⁻¹ := by group
        _ = c * (t * g) * c⁻¹ := by rw [hg']
        _ = c * t * c⁻¹ * (c * g * c⁻¹) := by group
    · intro hy
      refine ⟨c⁻¹ * y * c, ?_, by group⟩
      have hy' : y * x = x * y := hy
      show c⁻¹ * y * c * t = t * (c⁻¹ * y * c)
      have ht' : t = c⁻¹ * x * c := by rw [← hc]; group
      calc c⁻¹ * y * c * t = c⁻¹ * (y * x) * c := by rw [ht']; group
        _ = c⁻¹ * (x * y) * c := by rw [hy']
        _ = t * (c⁻¹ * y * c) := by rw [ht']; group
  have hcard' : Nat.card (Subgroup.centralizer ({t} : Set PSL(2, K))) =
      Nat.card (Subgroup.centralizer ({x} : Set PSL(2, K))) := by
    rw [← hmap]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).toEquiv)
  rw [hcard', hcent x hxT hx1 hx2]
  obtain ⟨a, ha⟩ := exists_two_pow_of_fermatMersenne hFM hq5 (n := Nat.card T₀)
    (by rw [hcard, hK])
  exact ⟨a + 1, by rw [ha, pow_succ]; ring⟩

theorem fm_ne_two {p : ℕ} (hFM : IsFermatOrMersennePrime p) : p ≠ 2 := by
  obtain ⟨-, ⟨k, hk⟩ | ⟨k, hk2, hk⟩⟩ := hFM
  · have : 2 ≤ 2 ^ (2 ^ k) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    omega
  · have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega

@[expose] def OddL2Fam (L : Type) [Group L] : Prop :=
  ∃ p : ℕ, IsFermatOrMersennePrime p ∧ StatedClassicalModel L .PSL 2 p 1

theorem pow_eq_one_of_sq_inner {L Gc : Type} [Group L] [Group Gc] (hZ : Subgroup.center L = ⊥)
    (ρ : Gc →* MulAut L) (hρ : Function.Injective ρ) (z : L) (a : ℕ)
    (hcl : ∀ l : L, l * z = z * l → l ^ (2 ^ a) = 1) (c : Gc)
    (hcomm : ρ c * MulAut.conj z = MulAut.conj z * ρ c) (l : L)
    (hl : ρ c * ρ c = MulAut.conj l) : c ^ (2 ^ (a + 1)) = 1 := by
  have h1 : MulAut.conj l * MulAut.conj z = MulAut.conj z * MulAut.conj l := by
    rw [← hl]
    calc ρ c * ρ c * MulAut.conj z = ρ c * (ρ c * MulAut.conj z) := by rw [mul_assoc]
      _ = ρ c * (MulAut.conj z * ρ c) := by rw [hcomm]
      _ = (ρ c * MulAut.conj z) * ρ c := by rw [mul_assoc]
      _ = (MulAut.conj z * ρ c) * ρ c := by rw [hcomm]
      _ = MulAut.conj z * (ρ c * ρ c) := by rw [mul_assoc]
  have h2 : l * z = z * l := by
    have h3 : MulAut.conj (l * z * (z * l)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, h1]
      simp
    have h4 : l * z * (z * l)⁻¹ ∈ Subgroup.center L := by
      rw [← ker_conj_eq_center]
      exact h3
    rw [hZ, Subgroup.mem_bot] at h4
    exact mul_inv_eq_one.mp h4
  have h5 := hcl l h2
  apply hρ
  rw [map_pow, map_one, pow_succ, pow_mul', pow_two, hl, ← map_pow, h5, map_one]

theorem map_centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (d : G) :
    (Subgroup.centralizer ({d} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ d} : Set H) := by
  ext h
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hg]
  · intro hh
    refine ⟨φ.symm h, ?_, by simp⟩
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hh]

theorem numFactAt_oddL2 : NumFactAt OddL2Fam := by
  intro L _ _ hq hF z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard hC9
  obtain ⟨p, hFM, hmodel⟩ := hF
  have hp : p.Prime := hFM.1
  have hp2 : p ≠ 2 := fm_ne_two hFM
  obtain ⟨K, _, _, _, e, hq1, hchar, hq5⟩ := psl2_model_data hp2 hmodel
  have hKp : Fintype.card K = p := by rw [hq1, pow_one]
  have hp5 : 5 ≤ p := hKp ▸ hq5
  have hZ : Subgroup.center L = ⊥ := by
    have h1 : (Subgroup.center L).map e.toMonoidHom = Subgroup.center PSL(2, K) :=
      Subgroup.map_center_eq e
    rw [psl2_center_eq_bot K] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ Subgroup.one_mem _)
  have hez1 : e z ≠ 1 := fun h => hz1 (e.injective (by rw [h, map_one]))
  have hez2 : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
  obtain ⟨a, ha⟩ := exists_two_pow_card_centralizer_psl2 hFM hKp hchar hp5 hez1 hez2
  have hcardL : Nat.card (Subgroup.centralizer ({z} : Set L)) = 2 ^ a := by
    rw [← ha, ← map_centralizer_singleton_mulEquiv e z]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv)
  have hcl : ∀ l : L, l * z = z * l → l ^ (2 ^ a) = 1 := by
    intro l hl
    have hmem : l ∈ Subgroup.centralizer ({z} : Set L) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hl
    have h := pow_card_eq_one' (G := ↥(Subgroup.centralizer ({z} : Set L))) (x := ⟨l, hmem⟩)
    rw [hcardL] at h
    exact congrArg Subtype.val h
  have hpow : ∀ c : Gc, c ∈ Subgroup.centralizer ({ž} : Set Gc) → c ^ (2 ^ (a + 1)) = 1 := by
    intro c hc
    have hcc : c * ž = ž * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hρc : ρ c * MulAut.conj z = MulAut.conj z * ρ c := by
      rw [← hž, ← map_mul, ← map_mul, hcc]
    obtain ⟨g, hg⟩ := sq_inner_psl2 hp hp2 hKp hp5 (transAut e (ρ c))
    refine pow_eq_one_of_sq_inner hZ ρ hρ z a hcl c hρc (e.symm g) ?_
    ext x
    apply e.injective
    have h1 := congrArg (fun m : MulAut PSL(2, K) => m (e x)) hg
    simp only [MulAut.mul_apply, transAut_apply, MulAut.conj_apply] at h1
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1
  have hC2 : IsPGroup 2 (Subgroup.centralizer ({ž} : Set Gc)) := fun g =>
    ⟨a + 1, Subtype.ext (hpow g.1 g.2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hC2
  rw [hm] at hC9
  have h3 : 3 ∣ 2 ^ m := ⟨3 * Nat.card Ŝ, by rw [hC9]; ring⟩
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

end Insp7

end CFSG.Quasithin

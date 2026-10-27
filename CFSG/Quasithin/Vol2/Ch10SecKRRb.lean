module

public import CFSG.Quasithin.Vol2.Ch10SecKRRa
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRR

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven Matrix
open CFSG.QuasithinUnique.Vol2Native.EvenWit

theorem exists_two_le_pRank_psl3_two {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (hm : StatedClassicalModel S .PSL 3 2 f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧ 2 ≤ CFSG.pRank r S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hKu : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' f
  · have h3 : 3 ∣ Nat.card Kˣ := by
      rw [hKu]
      have := two_pow_even_mod k
      rw [← hk] at this
      have : 0 < 2 ^ f := by positivity
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
    refine ⟨3, Nat.prime_three, by norm_num, hKu ▸ h3,
      two_le_pRank_of_mulEquiv Nat.prime_three e ?_⟩
    exact two_le_pRank_three_of_cubic hζ (StatedSL 3 K)
      (torusDiag_mem_SL (by simp [Fin.prod_univ_three]))
      (torusDiag_mem_SL (by simp [Fin.prod_univ_three])) (cycGL_mem_SL K)
  · have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmod : 2 ^ f % 3 = 2 := by rw [hk]; exact two_pow_odd_mod k
    have hodd : (2 ^ f - 1) % 2 = 1 := by
      have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      omega
    have hr : (2 ^ f - 1).minFac.Prime := Nat.minFac_prime (by omega)
    have hr2 : (2 ^ f - 1).minFac ≠ 2 := fun h => by
      have h' := Nat.minFac_dvd (2 ^ f - 1)
      rw [h] at h'
      omega
    have hr3 : (2 ^ f - 1).minFac ≠ 3 := fun h => by
      have h' := Nat.minFac_dvd (2 ^ f - 1)
      rw [h] at h'
      omega
    have := Fact.mk hr
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) (2 ^ f - 1).minFac
      (by rw [hKu]; exact Nat.minFac_dvd _)
    refine ⟨_, hr, hr2, Nat.minFac_dvd _, two_le_pRank_of_mulEquiv hr e ?_⟩
    exact two_le_pRank_torus hr3 hζ (i₀ := (0 : Fin 3)) (i₁ := 1) (i₂ := 2) (by decide)
      (by decide) (by decide) (torusDiag_mem_SL (prod_torusVec ζ _ _))
      (torusDiag_mem_SL (prod_torusVec ζ _ _))

theorem two_le_pRank_sl3_torus {K : Type} [Field K] [Finite K] {r : ℕ} (hr : r.Prime)
    (hrd : r ∣ Nat.card K - 1) : 2 ≤ CFSG.pRank r ↥(StatedSL 3 K) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units])
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hr.one_lt.ne hζ
  let x : ↥(StatedSL 3 K) := ⟨torusDiag (torusVec ζ 0 2), torusDiag_mem_SL (prod_torusVec ζ _ _)⟩
  let y : ↥(StatedSL 3 K) := ⟨torusDiag (torusVec ζ 1 2), torusDiag_mem_SL (prod_torusVec ζ _ _)⟩
  have hpow : ∀ n : ℕ, ∀ j : Fin 3, torusDiag (torusVec ζ j 2) ^ n =
      torusDiag (torusVec (ζ ^ n) j 2) := fun n j => by rw [← map_pow, torusVec_pow]
  have hent {d d' : Fin 3 → Kˣ} (h : torusDiag d = torusDiag d') (i : Fin 3) : d i = d' i :=
    congrFun (torusDiag_injective h) i
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine two_le_pRank_of_gens (x := x) (y := y) ?_ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, hpow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]
    rfl
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, hpow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]
    rfl
  · exact Subtype.ext ((Commute.all (torusVec ζ 0 2) (torusVec ζ 1 2)).map torusDiag).eq
  · intro h
    have h1 : (torusDiag (torusVec ζ (0 : Fin 3) 2) : GL (Fin 3) K) = torusDiag 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    have h2 := hent h1 0
    rw [torusVec_apply_left ζ (by decide)] at h2
    exact hζ1 h2
  · intro n h
    have h1 : (torusDiag (torusVec (ζ ^ n) (0 : Fin 3) 2) : GL (Fin 3) K) =
        torusDiag (torusVec ζ 1 2) := by
      rw [← hpow n 0]
      exact congrArg Subtype.val h
    have h2 := hent h1 1
    rw [torusVec_apply_of_ne _ (by decide) (by decide), torusVec_apply_left ζ (by decide)] at h2
    exact hζ1 h2.symm

theorem det_eq_one_of_mem_closure {n : ℕ} {K : Type} [Field K]
    {s : Set (GL (Fin n) K)} (hs : ∀ g ∈ s, (g : Matrix (Fin n) (Fin n) K).det = 1)
    {g : GL (Fin n) K} (hg : g ∈ Subgroup.closure s) : (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have hle : Subgroup.closure s ≤ (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker :=
    (Subgroup.closure_le _).mpr fun a ha => by
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      exact Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact hs a ha)
  have h1 := hle hg
  rw [MonoidHom.mem_ker] at h1
  have h2 := congrArg Units.val h1
  rwa [GeneralLinearGroup.val_det_apply] at h2

theorem not_dvd_card_scalars {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K).det = 1) {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card ↥((StatedScalars (Fin 3) K).subgroupOf H) := by
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h3 : x ^ 3 = 1 := by
    obtain ⟨⟨g, hgH⟩, hg⟩ := x
    obtain ⟨u, rfl⟩ := Subgroup.mem_subgroupOf.mp hg
    have hu : u ^ 3 = 1 := by
      have h1 := hdet _ hgH
      rw [← GeneralLinearGroup.val_det_apply, GeneralLinearGroup.det_scalar,
        Fintype.card_fin] at h1
      exact Units.ext h1
    apply Subtype.ext
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hu, map_one]
  have h := orderOf_dvd_of_pow_eq_one h3
  rw [hx] at h
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem two_le_pRank_sl3_odd {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hK : Nat.card K = p) : 2 ≤ CFSG.pRank p ↥(StatedSL 3 K) := by
  have hq : 2 ≤ CFSG.pRank p (StatedProj (StatedSL 3 K)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    have := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := 3) (a := 1) (b := 2) le_rfl
      (by norm_num) (p := p) (f := 1) (by rw [pow_one]; exact hK)
    simpa using this
  refine two_le_pRank_of_surjective_coprime (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_ hq
  rw [QuotientGroup.ker_mk']
  exact not_dvd_card_scalars (fun g hg => det_eq_one_of_mem_closure (fun a ha => ha) hg) hp5

theorem two_le_pRank_su3_odd {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hK : Nat.card K = p ^ 2) : 2 ≤ CFSG.pRank p ↥(StatedSU 3 p K) := by
  have hq : 2 ≤ CFSG.pRank p (StatedProj (StatedSU 3 p K)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    have := CFSG.SectionRank.ClassicalOdd.two_mul_le_pRank_SU_three (K := K) (p := p) (f := 1)
      (by omega) (by rw [pow_one]; exact hK)
    rw [pow_one] at this
    simpa using this
  refine two_le_pRank_of_surjective_coprime (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_ hq
  rw [QuotientGroup.ker_mk']
  exact not_dvd_card_scalars (fun g hg => det_eq_one_of_mem_closure (fun a ha => ha.1) hg) hp5

end CFSG.Quasithin.Vol2.Ch10.SecB.KRR

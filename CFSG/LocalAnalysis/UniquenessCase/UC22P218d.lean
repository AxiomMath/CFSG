module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P218c
import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
import CFSG.RankThree.PartOne.LIT.RankProjective
import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (projUnipotent)
open CFSG.Quasithin.H13.L32A.C.SkPf (map_congr_symm_eq congr_symm_apply mem_normalizer_of_map_conj_eq
  isSylowTwoOf_sylow sp4T spTau sp4T_range_le)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL rhoL_mk rhoL_mk_coe)

theorem uc22p218d_mul_pow_mul_inv_mem {M : Type*} [Group M] {U : Subgroup M} {a u : M}
    (ha : a ∈ normalizer (U : Set M)) (hu : u ∈ U) (k : ℕ) : (a * u) ^ k * (a ^ k)⁻¹ ∈ U := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : a ^ k * (a * u * a⁻¹) * (a ^ k)⁻¹ ∈ U :=
      (mem_normalizer_iff.1 (pow_mem ha k) _).1 ((mem_normalizer_iff.1 ha u).1 hu)
    have e : (a * u) ^ (k + 1) * (a ^ (k + 1))⁻¹ =
        ((a * u) ^ k * (a ^ k)⁻¹) * (a ^ k * (a * u * a⁻¹) * (a ^ k)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact mul_mem ih hc

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem uc22p218d_exists_torus_pow (α : MulAut (StatedProj (StatedSp 2 K)))
    (hαU : (projUnipotent 2 K).map α.toMonoidHom = projUnipotent 2 K) {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) :
    ∃ k : ℕ, ∀ t : Fin 2 → Kˣ, α (sp4T K t) * (sp4T K t ^ k)⁻¹ ∈ projUnipotent 2 K := by
  obtain ⟨i, ε, hε, hact⟩ := uc22p218c_exists_torus_action α hαU
  obtain ⟨c, rfl⟩ := hm
  have hsq : (fun y : Fin 2 → Kˣ => (spTau^[ε] y) ^ 2 ^ i)^[2] = fun y => y ^ 2 ^ (2 * i + ε) := by
    funext y
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · show (y ^ 2 ^ i) ^ 2 ^ i = y ^ 2 ^ (2 * i + 0)
      rw [← pow_mul]
      congr 1
      ring
    · show spTau (spTau y ^ 2 ^ i) ^ 2 ^ i = y ^ 2 ^ (2 * i + 1)
      rw [uc22p218c_spTau_pow, uc22p218c_spTau_spTau, ← pow_mul, ← pow_mul]
      congr 1
      ring
  refine ⟨2 ^ ((2 * i + ε) * (c + 1)), fun t => ?_⟩
  have h1 := uc22p218c_iterate_mul_inv_mem hαU (sp4T K) (fun y => (spTau^[ε] y) ^ 2 ^ i) hact (2 * (c + 1)) t
  have hα' : α ^ (2 * (c + 1)) = α := by
    rw [show 2 * (c + 1) = (2 * c + 1) + 1 by ring, pow_succ, hα, one_mul]
  rwa [hα', Function.iterate_mul, hsq, uc22p218c_iterate_pow_two_pow, map_pow] at h1

theorem uc22p218d_exists_pow_action (α : MulAut (StatedProj (StatedSp 2 K)))
    (hαU : (projUnipotent 2 K).map α.toMonoidHom = projUnipotent 2 K) {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) :
    ∃ k : ℕ, ∀ b ∈ normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))), α b * (b ^ k)⁻¹ ∈ projUnipotent 2 K := by
  obtain ⟨k, hk⟩ := uc22p218d_exists_torus_pow α hαU hm hα
  refine ⟨k, fun b hb => ?_⟩
  have hαu : ∀ u ∈ projUnipotent 2 K, α u ∈ projUnipotent 2 K := fun u hu => by
    have h1 := mem_map_of_mem α.toMonoidHom hu
    rwa [hαU] at h1
  have hb' := uc22p218c_normalizer_le_sup hb
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ sp4T_range_le] at hb'
  obtain ⟨_, ⟨t, rfl⟩, u, hu, rfl⟩ := hb'
  have hh : sp4T K t ∈ normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))) := sp4T_range_le ⟨t, rfl⟩
  have h2 : sp4T K t ^ k * α u * (sp4T K t ^ k)⁻¹ ∈ projUnipotent 2 K :=
    (mem_normalizer_iff.1 (pow_mem hh k) _).1 (hαu u hu)
  have e : α (sp4T K t * u) * ((sp4T K t * u) ^ k)⁻¹ =
      (α (sp4T K t) * (sp4T K t ^ k)⁻¹) * (sp4T K t ^ k * α u * (sp4T K t ^ k)⁻¹) *
        ((sp4T K t * u) ^ k * (sp4T K t ^ k)⁻¹)⁻¹ := by
    rw [map_mul]
    group
  rw [e]
  exact mul_mem (mul_mem (hk t) h2) (inv_mem (uc22p218d_mul_pow_mul_inv_mem hh hu k))

theorem uc22p218d_pow_card_sub_one_mem {b : StatedProj (StatedSp 2 K)}
    (hb : b ∈ normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K)))) : b ^ (Nat.card K - 1) ∈ projUnipotent 2 K := by
  have hb' := uc22p218c_normalizer_le_sup hb
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ sp4T_range_le] at hb'
  obtain ⟨_, ⟨t, rfl⟩, u, hu, rfl⟩ := hb'
  have h1 := uc22p218d_mul_pow_mul_inv_mem (sp4T_range_le ⟨t, rfl⟩) hu (Nat.card K - 1)
  have ht : t ^ (Nat.card K - 1) = 1 := by
    funext j
    rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units]
    exact pow_card_eq_one'
  rwa [← map_pow, ht, map_one, inv_one, mul_one] at h1

theorem uc22p218d_not_dvd_index {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : r ∣ Nat.card K - 1) :
    ¬ r ∣ (normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K)))).index := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  obtain ⟨s, hs⟩ : ∃ s, Nat.card K = s + 1 := ⟨Nat.card K - 1, by omega⟩
  have hs0 : 0 < s := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hT : Nat.card (sp4T K).range = s ^ 2 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective uc22p218c_sp4T_injective, Subgroup.card_top,
      Nat.card_pi, Fin.prod_univ_two, Nat.card_units, hs, Nat.add_sub_cancel, sq]
  obtain ⟨c, hc⟩ : s ^ 2 ∣ Nat.card (normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K)))) := hT ▸ Subgroup.card_dvd_of_le sp4T_range_le
  have hP := Subgroup.index_mul_card (normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))))
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hIcc, Finset.prod_pair (by norm_num),
    hc, hs] at hP
  have e1 : (s + 1) ^ (2 * 1) - 1 = s * (s + 2) := by
    rw [show (s + 1) ^ (2 * 1) = s * (s + 2) + 1 by ring, Nat.add_sub_cancel]
  have e2 : (s + 1) ^ (2 * 2) - 1 = s * ((s + 2) * ((s + 1) ^ 2 + 1)) := by
    rw [show (s + 1) ^ (2 * 2) = s * ((s + 2) * ((s + 1) ^ 2 + 1)) + 1 by ring, Nat.add_sub_cancel]
  rw [e1, e2] at hP
  set i := (normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
    Set (StatedProj (StatedSp 2 K)))).index with hi
  have hP' : i * c = (s + 1) ^ 4 * (s + 2) ^ 2 * ((s + 1) ^ 2 + 1) := by
    refine Nat.eq_of_mul_eq_mul_left (pow_pos hs0 2) ?_
    calc s ^ 2 * (i * c) = i * (s ^ 2 * c) := by ring
      _ = (s + 1) ^ 2 ^ 2 * (s * (s + 2) * (s * ((s + 2) * ((s + 1) ^ 2 + 1)))) := hP
      _ = s ^ 2 * ((s + 1) ^ 4 * (s + 2) ^ 2 * ((s + 1) ^ 2 + 1)) := by ring
  intro hri
  have h1 : r ∣ (s + 1) ^ 4 * (s + 2) ^ 2 * ((s + 1) ^ 2 + 1) := hP' ▸ dvd_mul_of_dvd_left hri c
  have hs' : s ≡ 0 [MOD r] := Nat.modEq_zero_iff_dvd.2 (by rwa [hs, Nat.add_sub_cancel] at hrK)
  have h8 := (((hs'.add_right 1).pow 4).mul ((hs'.add_right 2).pow 2)).mul (((hs'.add_right 1).pow 2).add_right 1)
  have h2 : r ∣ 2 ^ 3 := by
    have h3 := (h8.dvd_iff dvd_rfl).1 h1
    norm_num at h3 ⊢
    exact h3
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))

end Model

section Abstract

variable {X : Type} [Group X]

theorem uc22p218d_pow_action_sp4 {n : ℕ} (hX : IsSp4 X n) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    {α : MulAut X} (hαU : U.map α.toMonoidHom = U) {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) :
    ∃ k : ℕ, ∀ b ∈ normalizer (U : Set X), α b * (b ^ k)⁻¹ ∈ U := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  obtain ⟨φ, rfl⟩ := uc22p218c_exists_mulEquiv_map e hU
  have hα' : (MulAut.congr φ).symm α ^ m = 1 := by rw [← map_pow, hα, map_one]
  obtain ⟨k, hk⟩ := uc22p218d_exists_pow_action _ (map_congr_symm_eq φ hαU) hm hα'
  refine ⟨k, fun b hb => ?_⟩
  rw [CFSG.Quasithin.H13.L32A.C.SkPf.normalizer_map] at hb
  obtain ⟨b', hb', rfl⟩ := mem_map.1 hb
  have h1 := mem_map_of_mem φ.toMonoidHom (hk b' hb')
  simp only [map_mul, map_inv, map_pow, MulEquiv.coe_toMonoidHom, congr_symm_apply,
    MulEquiv.apply_symm_apply] at h1 ⊢
  exact h1

theorem uc22p218d_pow_sub_one_mem_sp4 {n : ℕ} (hX : IsSp4 X n) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) {b : X}
    (hb : b ∈ normalizer (U : Set X)) : b ^ (2 ^ n - 1) ∈ U := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  obtain ⟨φ, rfl⟩ := uc22p218c_exists_mulEquiv_map e hU
  rw [CFSG.Quasithin.H13.L32A.C.SkPf.normalizer_map] at hb
  obtain ⟨b', hb', rfl⟩ := mem_map.1 hb
  rw [← map_pow, ← hK]
  exact mem_map_of_mem _ (uc22p218d_pow_card_sub_one_mem hb')

theorem uc22p218d_not_dvd_card_sylow_sp4 [Finite X] {n r : ℕ} (hX : IsSp4 X n) (hr : r.Prime)
    (hrn : r ∣ 2 ^ n - 1) : ¬ r ∣ Nat.card (Sylow 2 X) := by
  obtain ⟨⟨-, hn1, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨φ, hφ⟩ := uc22p218c_exists_mulEquiv_map e (isSylowTwoOf_sylow P)
  have hc : Nat.card (Sylow 2 X) = (normalizer ((P : Subgroup X) : Set X)).index := Sylow.card_eq_index_normalizer P
  rw [hc, ← hφ, CFSG.Quasithin.H13.L32A.C.SkPf.normalizer_map, Subgroup.index_map_of_bijective φ.bijective]
  exact uc22p218d_not_dvd_index hr (uc22p218c_ne_two_of_dvd hn1 hrn) (by rw [hK]; exact hrn)

theorem uc22p218d_pRank_le_two_sp4 [Finite X] {n p : ℕ} (hX : IsSp4 X n) (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (CFSG.PGLModel.projSpEquivStatedProj 2 K)]
  exact CFSG.RankThree.PartOne.LIT.pRank_projSp_two_le hp hp2
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2)

theorem uc22p218d_three_le_of_odd {n : ℕ} (hX : IsSp4 X n) (hn : Odd n) : 3 ≤ n := by
  obtain ⟨⟨-, -, -, hne⟩, -⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  obtain ⟨k, rfl⟩ := hn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact absurd (by norm_num) hne
  · omega

theorem uc22p218d_center_eq_bot_sp4 {n : ℕ} (hX : IsSp4 X n) : center X = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  exact CFSG.QuasithinUnique.Lin2.Five.center_eq_bot_of_equiv e

end Abstract

section Group

variable {G : Type} [Group G] [Finite G]

theorem uc22p218d_mem_of_mk_mem {L : Subgroup G} (Q : Sylow 2 ↥L) {y : ↥L}
    (hy : (QuotientGroup.mk y : Bar2 L) ∈ (Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :
    (y : G) ∈ (Q : Subgroup ↥L).map L.subtype := by
  obtain ⟨q, hq, hqe⟩ := mem_map.1 hy
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hqe
  have h1 := mul_mem hq (CFSG.fitting_pCore_le_sylow Q hqe)
  rw [mul_inv_cancel_left] at h1
  exact mem_map_of_mem L.subtype h1

theorem uc22p218d_mk_mem_normalizer {L : Subgroup G} (Q : Sylow 2 ↥L) {x : G} (hxL : x ∈ L)
    (hxS : x ∈ normalizer (((Q : Subgroup ↥L).map L.subtype : Subgroup G) : Set G)) :
    (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) ∈
      normalizer (((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) :
        Set (Bar2 L)) := by
  refine mem_normalizer_of_map_conj_eq (CFSG.Quasithin.H13.L32A.C.SkPf.map_eq_of_forall_mem fun u hu => ?_)
  obtain ⟨q, hq, rfl⟩ := mem_map.1 hu
  have h1 : L.subtype (⟨x, hxL⟩ * q * (⟨x, hxL⟩ : ↥L)⁻¹) ∈ (Q : Subgroup ↥L).map L.subtype :=
    (mem_normalizer_iff.1 hxS q).1 (mem_map_of_mem L.subtype hq)
  refine mem_map.2 ⟨_, (mem_map_iff_mem L.subtype_injective).1 h1, ?_⟩
  rw [MulAut.conj_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem uc22p218d_rhoL_map_eq {L : Subgroup G} (Q : Sylow 2 ↥L) {t : G} (htL : t ∈ normalizer (L : Set G))
    (htS : t ∈ normalizer (((Q : Subgroup ↥L).map L.subtype : Subgroup G) : Set G)) :
    ((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map (rhoL L ⟨t, htL⟩).toMonoidHom =
      (Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
  refine CFSG.Quasithin.H13.L32A.C.SkPf.map_eq_of_forall_mem fun u hu => ?_
  obtain ⟨q, hq, rfl⟩ := mem_map.1 hu
  have h1 : ((Subgroup.normalizerMonoidHom L ⟨t, htL⟩ q : ↥L) : G) ∈ (Q : Subgroup ↥L).map L.subtype := by
    rw [rhoL_mk_coe]
    exact (mem_normalizer_iff.1 htS q).1 (mem_map_of_mem L.subtype hq)
  exact mem_map.2 ⟨_, (mem_map_iff_mem L.subtype_injective).1 h1, (rhoL_mk L ⟨t, htL⟩ q).symm⟩

theorem uc22p218d_exists_pow_conj_mem_sp4 {L S : Subgroup G} {n : ℕ} (hS : IsSylowOf 2 S L)
    (hX : IsSp4 (Bar2 L) n) {x : G} (hxL : x ∈ normalizer (L : Set G)) (hxS : x ∈ normalizer (S : Set G))
    {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) :
    ∃ k : ℕ, ∀ h ∈ L, h ∈ normalizer (S : Set G) → x * h * x⁻¹ * (h ^ k)⁻¹ ∈ S := by
  obtain ⟨Q, rfl⟩ := hS
  have hSb : IsSylowTwoOf ((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) ⊤ :=
    isSylowTwoOf_sylow (Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)))
  have hα : rhoL L ⟨x, hxL⟩ ^ m = 1 := by
    have h1 : (⟨x, hxL⟩ : ↥(normalizer (L : Set G))) ^ m = 1 := Subtype.ext (by simpa using hxm)
    rw [← map_pow, h1, map_one]
  obtain ⟨k, hk⟩ := uc22p218d_pow_action_sp4 hX hSb (uc22p218d_rhoL_map_eq Q hxL hxS) hm hα
  refine ⟨k, fun h hhL hhS => ?_⟩
  have h1 := hk _ (uc22p218d_mk_mem_normalizer Q hhL hhS)
  rw [rhoL_mk, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h1
  have h2 := uc22p218d_mem_of_mk_mem Q h1
  rwa [Subgroup.coe_mul, rhoL_mk_coe, Subgroup.coe_inv, Subgroup.coe_pow] at h2

theorem uc22p218d_pow_sub_one_mem_of_bar2 {L S : Subgroup G} {n : ℕ} (hS : IsSylowOf 2 S L)
    (hX : IsSp4 (Bar2 L) n) {h : G} (hhL : h ∈ L) (hhS : h ∈ normalizer (S : Set G)) : h ^ (2 ^ n - 1) ∈ S := by
  obtain ⟨Q, rfl⟩ := hS
  have hSb : IsSylowTwoOf ((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) ⊤ :=
    isSylowTwoOf_sylow (Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)))
  have h1 := uc22p218d_pow_sub_one_mem_sp4 hX hSb (uc22p218d_mk_mem_normalizer Q hhL hhS)
  rw [← QuotientGroup.mk_pow] at h1
  have h2 := uc22p218d_mem_of_mk_mem Q h1
  rwa [Subgroup.coe_pow] at h2

theorem uc22p218d_eq_one_of_pow_eq_one {L S : Subgroup G} {n p : ℕ} (hS : IsSylowOf 2 S L)
    (hX : IsSp4 (Bar2 L) n) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ 2 ^ n - 1) {h : G} (hhL : h ∈ L)
    (hhS : h ∈ normalizer (S : Set G)) (hhp : h ^ p = 1) : h = 1 := by
  have h1 := uc22p218d_pow_sub_one_mem_of_bar2 hS hX hhL hhS
  obtain ⟨a, ha⟩ := hS.isPGroup ⟨_, h1⟩
  have ha' : h ^ ((2 ^ n - 1) * 2 ^ a) = 1 := by
    rw [pow_mul]
    exact congrArg Subtype.val ha
  have hcop : Nat.Coprime p ((2 ^ n - 1) * 2 ^ a) :=
    Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
      (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have h2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hhp) (orderOf_dvd_of_pow_eq_one ha')
  rwa [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h2

theorem uc22p218d_not_dvd_card_sylow_of_bar2 {L : Subgroup G} {n r : ℕ} (hX : IsSp4 (Bar2 L) n) (hr : r.Prime)
    (hrn : r ∣ 2 ^ n - 1) : ¬ r ∣ Nat.card (Sylow 2 ↥L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ Q := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.fitting_pCore_le_sylow Q
  have h1 : (normalizer (((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) :
      Set (Bar2 L))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
    rw [comap_normalizer_eq_of_surjective _ hπ, comap_map_eq, sup_eq_left.2 hker]
  have h2 : Nat.card (Sylow 2 (Bar2 L)) = (normalizer (((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
      Subgroup (Bar2 L)) : Set (Bar2 L))).index := Sylow.card_eq_index_normalizer (Q.mapSurjective hπ)
  have h3 : Nat.card (Sylow 2 ↥L) = (normalizer ((Q : Subgroup ↥L) : Set ↥L)).index :=
    Sylow.card_eq_index_normalizer Q
  rw [h3, ← h1, index_comap_of_surjective _ hπ, ← h2]
  exact uc22p218d_not_dvd_card_sylow_sp4 hX hr hrn

theorem uc22p218d_pRank_le_two_of_bar2 {L : Subgroup G} {n p : ℕ} (hX : IsSp4 (Bar2 L) n) (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p L ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hm]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L) hN]
  exact uc22p218d_pRank_le_two_sp4 hX hp hp2

end Group

end CFSG.LocalAnalysis.UniquenessCase.UC22

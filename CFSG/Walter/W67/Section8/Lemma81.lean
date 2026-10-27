module

public import CFSG.Walter.W67.Lemma26i

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

namespace Lemma81

variable {G : Type} [Group G]

theorem index_ne_two_of_perfect (hperf : commutator G = ⊤) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (G ⧸ N) :=
    isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, h2])
  have h1 := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', hperf, top_le_iff] at h1
  rw [h1, Subgroup.index_top] at h2
  omega

theorem mem_oddPart_of_dihedral {Y : Subgroup G} {n : ℕ} (hn : n % 4 = 2)
    (e : Y ≃* DihedralGroup n) {y : G} (hy : y ∈ Y) (hodd : Odd (orderOf y)) :
    y ∈ oddPart Y := by
  have : NeZero n := ⟨by omega⟩
  set R : Subgroup (DihedralGroup n) := Subgroup.zpowers (DihedralGroup.r (2 : ZMod n)) with hR
  have hRn : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · rw [show DihedralGroup.r i * DihedralGroup.r 2 ^ k * (DihedralGroup.r i)⁻¹ =
        DihedralGroup.r 2 ^ k by
          rw [(Commute.zpow_right (show Commute (DihedralGroup.r i) (DihedralGroup.r 2) from
            by simp [Commute, SemiconjBy, add_comm]) k).eq, mul_inv_cancel_right]]
      exact Subgroup.zpow_mem_zpowers _ k
    · have hconj : DihedralGroup.sr i * DihedralGroup.r 2 * (DihedralGroup.sr i)⁻¹ =
          (DihedralGroup.r 2)⁻¹ := by
        simp [DihedralGroup.inv_sr]
      have : DihedralGroup.sr i * DihedralGroup.r 2 ^ k * (DihedralGroup.sr i)⁻¹ =
          ((DihedralGroup.r 2)⁻¹) ^ k := by
        rw [← hconj, conj_zpow]
      rw [this, inv_zpow']
      exact Subgroup.zpow_mem_zpowers _ (-k)
  have hRcard : Nat.Coprime 2 (Nat.card R) := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r]
    have hval : Nat.gcd n (2 : ZMod n).val = 2 := by
      rcases Nat.lt_or_ge n 3 with h3 | h3
      · interval_cases n
        · omega
        · omega
        · rfl
      · have : (2 : ZMod n).val = 2 := by
          rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_cast, ZMod.val_natCast]
          exact Nat.mod_eq_of_lt (by omega)
        rw [this]
        exact Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hval]
    refine Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ?_)
    have h' : n / 2 % 2 = 1 := by omega
    exact h'
  set N : Subgroup Y := R.comap e.toMonoidHom with hN
  have hNn : N.Normal := hRn.comap _
  have hNcard : Nat.Coprime 2 (Nat.card N) := by
    have : Nat.card N = Nat.card R := by
      rw [hN, ← Subgroup.card_map_of_injective (f := e.toMonoidHom) (by exact e.injective),
        Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) (by exact e.surjective)]
    rwa [this]
  have hle : N ≤ CFSG.pPrimeCore 2 Y := CFSG.le_pPrimeCore_of_normal_coprime hNn hNcard
  have hmem : (⟨y, hy⟩ : Y) ∈ N := by
    change e ⟨y, hy⟩ ∈ R
    have hodd' : Odd (orderOf (e ⟨y, hy⟩)) := by
      rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    generalize e ⟨y, hy⟩ = x at hodd'
    rcases x with i | i
    · rw [DihedralGroup.orderOf_r] at hodd'
      have h2 : 2 ∣ i.val := by
        have hdi := Nat.gcd_dvd_right n i.val
        have hk : Nat.gcd n i.val * (n / Nat.gcd n i.val) = n :=
          Nat.mul_div_cancel' (Nat.gcd_dvd_left n i.val)
        have hev : Even (Nat.gcd n i.val) := by
          by_contra hno
          rw [Nat.not_even_iff_odd] at hno
          have : Odd n := hk ▸ hno.mul hodd'
          rw [Nat.odd_iff] at this
          omega
        exact (even_iff_two_dvd.mp hev).trans hdi
      obtain ⟨k, hk⟩ := h2
      have : DihedralGroup.r i = DihedralGroup.r (2 : ZMod n) ^ k := by
        have h1 : DihedralGroup.r i = (DihedralGroup.r 1 : DihedralGroup n) ^ i.val := by
          rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
        have h2 : DihedralGroup.r (2 : ZMod n) = (DihedralGroup.r 1 : DihedralGroup n) ^ 2 := by
          rw [DihedralGroup.r_one_pow]
          norm_num
        rw [h1, h2, ← pow_mul, hk]
      rw [this]
      exact Subgroup.npow_mem_zpowers _ k
    · rw [DihedralGroup.orderOf_sr] at hodd'
      exact absurd hodd' (by decide)
  exact ⟨⟨y, hy⟩, hle hmem, rfl⟩

section PSL

variable {p f : ℕ} [Fact p.Prime] {K : Subgroup G}

theorem inf_centralizer_eq_map (e : K ≃* PSL(2, GaloisField p f)) {t : G}
    {t' : PSL(2, GaloisField p f)} (ht' : psl2Emb e t' = t) :
    K ⊓ Subgroup.centralizer ({t} : Set G) =
      (Subgroup.centralizer ({t'} : Set PSL(2, GaloisField p f))).map (psl2Emb e) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨hxK, hxt⟩
    obtain ⟨y, rfl⟩ := PSL2Sub.exists_emb_eq e hxK
    refine ⟨y, PSL2Sub.emb_injective e ?_, rfl⟩
    rw [map_mul, map_mul, ht']
    exact hxt
  · rintro ⟨y, hy, rfl⟩
    refine ⟨PSL2Sub.emb_mem e y, ?_⟩
    rw [← ht', ← map_mul, ← map_mul, hy]

theorem mem_oddPart_inf_centralizer (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p)
    (hf : 0 < f) (hq : p ^ f % 8 = 3) {t : G} (htK : t ∈ K) (ht : orderOf t = 2) {y : G}
    (hy : y ∈ K ⊓ Subgroup.centralizer ({t} : Set G)) (hodd : Odd (orderOf y)) :
    y ∈ oddPart (K ⊓ Subgroup.centralizer ({t} : Set G)) := by
  obtain ⟨t', ht'⟩ := PSL2Sub.exists_emb_eq e htK
  have ht'2 : orderOf t' = 2 := by
    rw [← orderOf_injective (psl2Emb e) (PSL2Sub.emb_injective e) t', ht', ht]
  obtain ⟨-, ⟨d⟩⟩ := (psl2_odd_centralizer_involution hp hf ht'2).2 (by omega)
  let iso1 : (K ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ≃*
      Subgroup.centralizer ({t'} : Set PSL(2, GaloisField p f)) :=
    (MulEquiv.subgroupCongr (inf_centralizer_eq_map e ht')).trans
      (Subgroup.equivMapOfInjective _ _ (PSL2Sub.emb_injective e)).symm
  exact mem_oddPart_of_dihedral (n := (p ^ f + 1) / 2) (by omega) (iso1.trans d) hy hodd

theorem exists_odd_mem_inf_centralizer (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p)
    (hf : 0 < f) (hq : p ^ f % 8 = 3) (hq3 : 3 < p ^ f) {t : G} (htK : t ∈ K)
    (ht : orderOf t = 2) :
    ∃ a ∈ K ⊓ Subgroup.centralizer ({t} : Set G), a ≠ 1 ∧ Odd (orderOf a) := by
  obtain ⟨t', ht'⟩ := PSL2Sub.exists_emb_eq e htK
  have ht'2 : orderOf t' = 2 := by
    rw [← orderOf_injective (psl2Emb e) (PSL2Sub.emb_injective e) t', ht', ht]
  obtain ⟨hcard, -⟩ := (psl2_odd_centralizer_involution hp hf ht'2).2 (by omega)
  set m := (p ^ f + 1) / 4 with hm
  have hm1 : 1 < m := by omega
  have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
  set ℓ := m.minFac with hℓ
  have hℓp : ℓ.Prime := Nat.minFac_prime (by omega)
  have hℓm : ℓ ∣ m := Nat.minFac_dvd m
  have hℓodd : Odd ℓ := Odd.of_dvd_nat hmodd hℓm
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hdvd : ℓ ∣ Nat.card (Subgroup.centralizer ({t'} : Set PSL(2, GaloisField p f))) := by
    rw [hcard]
    exact hℓm.trans ⟨4, by omega⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer
    ({t'} : Set PSL(2, GaloisField p f))) ℓ hdvd
  refine ⟨psl2Emb e c, ?_, ?_, ?_⟩
  · rw [inf_centralizer_eq_map e ht']
    exact ⟨c, c.2, rfl⟩
  · intro h1
    have : orderOf (psl2Emb e (c : PSL(2, GaloisField p f))) = ℓ := by
      rw [orderOf_injective (psl2Emb e) (PSL2Sub.emb_injective e), Subgroup.orderOf_coe, hc]
    rw [h1, orderOf_one] at this
    exact hℓp.one_lt.ne this
  · rw [orderOf_injective (psl2Emb e) (PSL2Sub.emb_injective e), Subgroup.orderOf_coe, hc]
    exact hℓodd

end PSL

end Lemma81


namespace Lemma81

variable {G : Type} [Group G] [Finite G]

theorem three_pow_mod_eight_of_odd {f : ℕ} (hf : Odd f) : 3 ^ f % 8 = 3 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem three_pow_mod_eight_of_even {f : ℕ} (hf : Even f) : 3 ^ f % 8 = 1 := by
  obtain ⟨k, rfl⟩ := hf
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem odd_f_of_std (s : Std G) (hp : s.p = 3) : Odd s.f ∧ 1 < s.f := by
  have h8 := s.toHyp.mod_eight
  have hq : s.q = 3 ^ s.f := by
    change s.p ^ s.f = 3 ^ s.f
    rw [hp]
  rw [hq] at h8
  refine ⟨?_, ?_⟩
  · by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    rw [three_pow_mod_eight_of_even hev] at h8
    omega
  · have h3 := s.three_lt_q
    rw [hq] at h3
    by_contra h1
    interval_cases hf : s.f
    · norm_num at h3
    · norm_num at h3

theorem A₀_ne_bot
    (s : Std G) (hp : s.p = 3) (h610 : Nat.card s.fr.E < s.f) {T₂ : G}
    (hT : T₂ ∈ s.fr.T) (hT2 : orderOf T₂ = 2) : s.fr.A₀ T₂ ≠ ⊥ := by
  obtain ⟨hfodd, -⟩ := odd_f_of_std s hp
  have heX : s.eX s.fr.E = Nat.card s.fr.E := by
    unfold Hyp.eX
    rw [s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]
  obtain ⟨hdvd, ⟨eK⟩, -⟩ := lemma_2_6_i G s.toHyp s.fr (le_refl _) s.E_ne_bot
  set f' := s.f / s.eX s.fr.E with hf'
  have he0 : 0 < Nat.card s.fr.E := Nat.card_pos
  rw [heX] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hf'c : f' = c := by
    rw [hf', heX, hc, Nat.mul_div_cancel_left _ he0]
  have hcodd : Odd c := by
    have : Odd (Nat.card s.fr.E * c) := hc ▸ hfodd
    exact Nat.Odd.of_mul_right this
  have hc1 : 1 < c := by
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c
      · rw [hc, mul_zero] at hfodd
        exact absurd hfodd (by decide)
      · rw [hc, mul_one] at h610
        exact absurd h610 (lt_irrefl _)
    · omega
  have hq8 : s.p ^ f' % 8 = 3 := by
    rw [hp, hf'c, three_pow_mod_eight_of_odd hcodd]
  have hq3 : 3 < s.p ^ f' := by
    rw [hp, hf'c]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ 3 ^ c := Nat.pow_le_pow_right (by norm_num) hc1
  have hTKE : T₂ ∈ s.KX s.fr.E := by
    refine ⟨s.fr.T_le_K hT, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS hx) T₂ (s.fr.T_le_S hT)).symm
  obtain ⟨a, ⟨haKE, haT⟩, ha1, haodd⟩ :=
    exists_odd_mem_inf_centralizer eK s.odd_p (by show 0 < f'; rw [hf'c]; omega) hq8 hq3
      hTKE hT2
  have hqmain : s.p ^ s.f % 8 = 3 := by
    rw [hp, three_pow_mod_eight_of_odd hfodd]
  have haA : a ∈ s.fr.A T₂ :=
    mem_oddPart_inf_centralizer s.iso s.odd_p s.f_pos hqmain (s.fr.T_le_K hT) hT2
      ⟨haKE.1, haT⟩ haodd
  intro hbot
  have : a ∈ s.fr.A₀ T₂ := ⟨haA, haKE.2⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact ha1 this

theorem exists_involution_T {h : Hyp G} (fr : Frame h) :
    ∃ T₂ ∈ fr.T, orderOf T₂ = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := fr.T) 2
    (by rw [fr.card_T]; norm_num)
  exact ⟨t, t.2, by rw [← ht, Subgroup.orderOf_coe]⟩

end Lemma81

open Lemma81 in
theorem lemma_8_1_of
    (h43ab : S_prop_4_3_ab) (h43c : S_prop_4_3_c) (h610 : S_prop_6_10) :
    S_lemma_8_1 := by
  intro G _ _ s hp hR
  have hidx := index_ne_two_of_perfect s.perfect
  obtain ⟨hfodd, hf1⟩ := odd_f_of_std s hp
  let hI : HypI G :=
    { toHyp := s.toHyp
      fr := s.fr
      p_eq_three := hp
      odd_f := hfodd
      one_lt_f := hf1
      perfect := s.perfect
      cover := lemma_2_6_cover G s.toHyp s.fr hidx }
  obtain ⟨T₂, hT, hT2⟩ := exists_involution_T s.fr
  obtain ⟨U, hU3, hNV, hUE, hUV, -, hCV, -, -⟩ := h43ab G s.toHyp s.fr hp hidx hT hT2
  obtain ⟨hNA, hCA⟩ := h43c G s hp hT hT2 hR
  exact ⟨{ toHypI := hI
           T₂ := T₂
           T₂_mem := hT
           T₂_order := hT2
           U := U
           card_U := hU3
           G3a := hNV
           G3a' := ⟨hUE, hUV⟩
           G3b := hCV
           G3c := hNA
           G3c' := fun Aα h1 h2 => (hCA Aα h1 h2).1
           G4 := A₀_ne_bot s hp (h610 G s hp hR) hT hT2 }, rfl, rfl⟩

end CFSG.Walter.W67

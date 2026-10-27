module

public import CFSG.Walter.W67.Section5.Prop56A2a
public import CFSG.Walter.W67.Section6.Util

public section

namespace CFSG.Walter.W67

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Std

variable (s : Std G)

theorem odd_f_of_p3 (hp : s.p = 3) : Odd s.f := by
  have h := s.q_mod_four hp
  rw [Hyp.q, hp] at h
  by_contra hf
  rw [Nat.not_odd_iff_even] at hf
  obtain ⟨k, hk⟩ := hf
  rw [hk, ← two_mul, pow_mul, Nat.pow_mod] at h
  norm_num at h

theorem three_dvd_f (h26i : S_lemma_2_6_i) (h3 : 3 ∣ Nat.card s.fr.E) : 3 ∣ s.f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, hxE⟩, hox⟩ := exists_prime_orderOf_dvd_card' (G := s.fr.E) 3 h3
  rw [Subgroup.orderOf_mk] at hox
  have hXE : Subgroup.zpowers x ≤ s.fr.E := Subgroup.zpowers_le.mpr hxE
  have hXcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hox]
  have hX1 : Subgroup.zpowers x ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hXcard
    norm_num at hXcard
  have heX : s.eX (Subgroup.zpowers x) = 3 := by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one, hXcard]
  obtain ⟨hediv, -, -⟩ := h26i G s.toHyp s.fr hXE hX1
  rwa [heX] at hediv

include s in
theorem elementary_sylow (S : Sylow 2 G) : IsElementaryAbelian 2 (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G s.fr.S S
  have := s.fr.isElementaryAbelian_S
  rw [← hg, Sylow.coe_subgroup_smul]
  exact IsElementaryAbelian.map _

theorem factorization_three_card_K_le (hp : s.p = 3) :
    (Nat.card s.K).factorization 3 ≤ s.f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 s.K) := inferInstance
  have h1 := s.card_le_q_of_le_K hp (Q := (P : Subgroup s.K).map s.K.subtype)
    (P.isPGroup'.map _) (Subgroup.map_subtype_le _)
  rw [Subgroup.card_map_of_injective s.K.subtype_injective, Sylow.card_eq_multiplicity, Hyp.q,
    hp] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

theorem factorization_three_card_E_lt (h26i : S_lemma_2_6_i) :
    (Nat.card s.fr.E).factorization 3 < s.f := by
  have heX : s.eX s.fr.E = Nat.card s.fr.E := by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]
  obtain ⟨hediv, -, -⟩ := h26i G s.toHyp s.fr le_rfl s.E_ne_bot
  rw [heX] at hediv
  have h1 : 3 ^ (Nat.card s.fr.E).factorization 3 ∣ s.f :=
    (Nat.ordProj_dvd _ _).trans hediv
  have h2 := (Frame5.three_mul_le_three_pow ((Nat.card s.fr.E).factorization 3)).trans
    (Nat.le_of_dvd s.f_pos h1)
  have := s.f_pos
  omega

theorem centralizer_involution
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    {u : G} (hu : orderOf u = 2) :
    (Nat.card (Subgroup.centralizer ({u} : Set G))).factorization 3 < 2 * s.f := by
  have hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 :=
    fun N hN => index_ne_two_of_perfect_std s.perfect N hN
  obtain ⟨g, hg⟩ := isConj_iff.mp ((h22 G s.toHyp s.fr hidx).2.2 s.J u s.orderOf_J hu)
  have hcard : Nat.card (Subgroup.centralizer ({u} : Set G)) = Nat.card s.H := by
    rw [← hg, ← Sec6.cj_centralizer_singleton, Sec6.card_cj]
  rw [hcard]
  have hH : s.H ≤ Subgroup.zpowers s.J ⊔ (s.K ⊔ s.fr.E) := fun x hx => by
    obtain ⟨j, hj, m, hm, rfl⟩ := s.fr.exists_decomp_H_JM hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hm)
  have hJN : Subgroup.zpowers s.J ≤ Subgroup.normalizer ((s.K ⊔ s.fr.E : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun m hm =>
        (s.fr.commute_of_mem_KE (Subgroup.mem_zpowers _) hm).symm))
  have e1 := Sec52.card_sup_mul_card_inf hJN
  have e2 := Sec52.card_sup_mul_card_inf s.fr.E_le_normalizer_K
  rw [sup_comm] at e2
  have hdvd : Nat.card s.H ∣ Nat.card s.K * Nat.card s.fr.E * 2 := by
    have d1 := Subgroup.card_dvd_of_le hH
    have d2 : Nat.card (Subgroup.zpowers s.J ⊔ (s.K ⊔ s.fr.E) : Subgroup G) ∣
        Nat.card (s.K ⊔ s.fr.E : Subgroup G) * 2 := by
      rw [Nat.card_zpowers, s.orderOf_J] at e1
      exact Dvd.intro _ e1
    have d3 : Nat.card (s.K ⊔ s.fr.E : Subgroup G) ∣ Nat.card s.K * Nat.card s.fr.E :=
      Dvd.intro _ e2
    exact d1.trans (d2.trans (Nat.mul_dvd_mul_right d3 2))
  have hK0 : Nat.card s.K ≠ 0 := Nat.card_pos.ne'
  have hE0 : Nat.card s.fr.E ≠ 0 := Nat.card_pos.ne'
  have hfac := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
    (by positivity : Nat.card s.K * Nat.card s.fr.E * 2 ≠ 0)).mpr hdvd 3
  rw [Nat.factorization_mul (by positivity) (by norm_num), Nat.factorization_mul hK0 hE0,
    Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)] at hfac
  have h1 := s.factorization_three_card_K_le hp
  have h2 := s.factorization_three_card_E_lt h26i
  omega

theorem centralizer_B (h26i : S_lemma_2_6_i) (hp : s.p = 3) (f5 : Frame5 s) {y : G}
    (hyE : y ∈ s.fr.E) {k : ℕ} (hyk : y ^ (3 ^ k) = 1) (hy1 : y ≠ 1) {b : G} (hb : b ∈ f5.B)
    (hyb : y * b = b * y) : b ^ (3 ^ (s.f / 3) - 1) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.zpowers y with hXdef
  have hXE : X ≤ s.fr.E := Subgroup.zpowers_le.mpr hyE
  have hX1 : X ≠ ⊥ := fun h => hy1 (by
    have : y ∈ X := Subgroup.mem_zpowers y
    rwa [h, Subgroup.mem_bot] at this)
  obtain ⟨j, -, hoy⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hyk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.mp (by rw [hoy, pow_zero]))
  have heX : s.eX X = 3 ^ j := by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one, hXdef, Nat.card_zpowers,
      hoy]
  obtain ⟨hediv, ⟨hiso⟩, -⟩ := h26i G s.toHyp s.fr hXE hX1
  set m := s.f / s.eX X with hm
  rw [heX] at hediv
  have hm' : m = s.f / 3 ^ j := by rw [hm, heX]
  have hfm : s.f = 3 ^ j * m := by rw [hm']; exact (Nat.mul_div_cancel' hediv).symm
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfm
    exact s.f_pos.ne' hfm
  have hbKX : b ∈ s.KX X := Subgroup.mem_inf.mpr ⟨f5.B_le hb, by
    rw [hXdef, Sec52.centralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff]
    exact hyb.symm⟩
  have hFcard' : Nat.card (GaloisField s.p m) = s.p ^ m := GaloisField.card _ _ hm0
  have hFcard : Nat.card (GaloisField s.p m) = 3 ^ m := by
    rw [GaloisField.card _ _ hm0, hp]
  have hKXcard : Nat.card (s.KX X) = 3 ^ m * ((3 ^ m) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr hiso.toEquiv,
      psl2_card_formula _ ⟨s.p, m, Fact.out, s.odd_p, Nat.pos_of_ne_zero hm0, hFcard'⟩, hFcard]
  have hob3 : Nat.Coprime (orderOf b) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    exact f5.three_not_dvd_B hp (h.trans (Subgroup.orderOf_dvd_natCard _ hb))
  have hev : 2 ∣ (3 ^ m) ^ 2 - 1 := by
    have : Odd ((3 ^ m) ^ 2) := (Odd.pow (by decide)).pow
    exact (Nat.Odd.sub_odd this odd_one).two_dvd
  have h1 : orderOf b ∣ (3 ^ m) ^ 2 - 1 := by
    have h2 := Subgroup.orderOf_dvd_natCard _ hbKX
    rw [hKXcard, Nat.mul_div_assoc _ hev] at h2
    exact ((Nat.Coprime.pow_right m hob3).dvd_of_dvd_mul_left h2).trans (Nat.div_dvd_of_dvd hev)
  have h3 : orderOf b ∣ 3 ^ s.f - 1 := by
    have h4 := f5.card_B
    rw [Hyp.q, hp] at h4
    rw [← h4]
    exact (Subgroup.orderOf_dvd_natCard _ hb).trans (Dvd.intro_left _ rfl)
  have h5 : orderOf b ∣ 3 ^ m - 1 := by
    have h6 := Nat.dvd_gcd h1 h3
    rw [← pow_mul, Nat.pow_sub_one_gcd_pow_sub_one] at h6
    have hg : Nat.gcd (m * 2) s.f = m := by
      rw [hfm, mul_comm (3 ^ j) m, Nat.gcd_mul_left]
      have : Nat.gcd 2 (3 ^ j) = 1 := Nat.Coprime.pow_right _ (by norm_num)
      rw [this, mul_one]
    rwa [hg] at h6
  have h7 : m ∣ s.f / 3 := by
    have : s.f / 3 = 3 ^ (j - 1) * m := by
      rw [hfm, show 3 ^ j = 3 * 3 ^ (j - 1) by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)], mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [this]
    exact Dvd.intro_left _ rfl
  exact orderOf_dvd_iff_pow_eq_one.mp (h5.trans (Nat.pow_sub_one_dvd_pow_sub_one 3 h7))

end Std

namespace Frame5

variable {s : Std G} {f5 : Frame5 s}

namespace RData

variable {R : Subgroup G} (hR : f5.RData R)
include hR

theorem exists_decomp
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) {g : G}
    (hgH : g ∈ s.H) (hgN : g ∈ Subgroup.normalizer (R : Set G)) :
    ∃ j ∈ Subgroup.zpowers s.J, ∃ u ∈ f5.P₁, ∃ b ∈ f5.B, ∃ e ∈ s.fr.E, g = j * (u * b * e) := by
  obtain ⟨j, hj, m, hm, rfl⟩ := s.fr.exists_decomp_H_JM hgH
  have hjN : j ∈ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr hR.J_le hj
  have hmN : m ∈ Subgroup.normalizer (R : Set G) := by
    have := (Subgroup.normalizer (R : Set G)).mul_mem
      ((Subgroup.normalizer (R : Set G)).inv_mem hjN) hgN
    rwa [inv_mul_cancel_left] at this
  have hmH : m ∈ s.H := sup_le s.K_le_H s.fr.E_le_H hm
  have hmP : m ∈ Subgroup.normalizer (f5.P₁ : Set G) := by
    rw [← hR.inf_H h22 h26i hp]
    exact Sec54.mem_normalizer_inf hmN (Subgroup.le_normalizer hmH)
  have hk : m ∈ Subgroup.normalizer (f5.P₁ : Set G) ⊓ (s.K ⊔ s.fr.E) :=
    Subgroup.mem_inf.mpr ⟨hmP, hm⟩
  rw [f5.normalizer_eq] at hk
  have hBN := f5.B_le_normalizer_P₁
  have hEN : s.fr.E ≤ Subgroup.normalizer ((f5.P₁ ⊔ f5.B : Subgroup G) : Set G) :=
    fun e he => Sec52.mem_normalizer_sup (f5.E_le_normalizer_P₁ he) (f5.E_le_normalizer_B he)
  obtain ⟨y, hy, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hk
  obtain ⟨u, hu, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hBN).mp hy
  exact ⟨j, hj, u, hu, b, hb, e, he, rfl⟩

theorem normalizer_inf_H_le
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    Subgroup.normalizer (R : Set G) ⊓ s.H ≤
      (Subgroup.zpowers s.J ⊔ f5.B ⊔ s.fr.E) ⊔ Subgroup.centralizer (R : Set G) := by
  intro g hg
  obtain ⟨hgN, hgH⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨j, hj, u, hu, b, hb, e, he, rfl⟩ := hR.exists_decomp h22 h26i hp hgH hgN
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.mem_sup_left hj))) (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_right (hR.P₁_le_centralizer hu)) (Subgroup.mem_sup_left
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)))) (Subgroup.mem_sup_left
    (Subgroup.mem_sup_right he)))

variable (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
include hRc

theorem J_not_mem_centralizer
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hRq : Nat.card R = s.q ^ 2) : s.J ∉ Subgroup.centralizer (R : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hJ
  obtain ⟨hP₂c, -⟩ := hR.card_P₂ hRc h22 h26i hp hRq
  have hP₂1 : Sec56.invSub s.J R hRc ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hP₂c
    have := s.one_lt_q
    omega
  obtain ⟨y, hy, hy1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hP₂1
  obtain ⟨hyR, hyJ⟩ := hy
  have h1 : s.J * y * s.J⁻¹ = y := by
    rw [(Subgroup.mem_centralizer_iff.mp hJ y hyR).symm, mul_inv_cancel_right]
  have hy2 : y * y = 1 := by
    have h2 : y = y⁻¹ := h1.symm.trans hyJ
    calc y * y = y * y⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel y
  have hodd : Odd (orderOf y) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR.isPGroup
    exact Odd.of_dvd_nat (hk ▸ Odd.pow (by decide)) (Subgroup.orderOf_dvd_natCard R hyR)
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hy2])
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact hy1 (orderOf_eq_one_iff.mp h)
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem H_inf_centralizer_le
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hRq : Nat.card R = s.q ^ 2) : s.H ⊓ Subgroup.centralizer (R : Set G) ≤ f5.P₁ := by
  intro c hc
  obtain ⟨hcH, hcC⟩ := Subgroup.mem_inf.mp hc
  have hcP : c ∈ Subgroup.centralizer (f5.P₁ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => Subgroup.mem_centralizer_iff.mp hcC u
      (hR.P₁_le hu)
  by_cases hodd : Odd (orderOf c)
  · exact f5.mem_P₁_of_odd h26i hcH hcP hodd
  exfalso
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨d, hd⟩ := hodd
  have hd0 : d ≠ 0 := by
    intro h
    have := orderOf_pos c
    omega
  set t := c ^ d with htdef
  have hot : orderOf t = 2 := by
    rw [htdef, orderOf_pow_of_dvd hd0 (by rw [hd]; exact ⟨2, by omega⟩), hd]
    exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hd0) (by ring)
  have htH : t ∈ s.H := s.H.pow_mem hcH d
  have htC : t ∈ Subgroup.centralizer (R : Set G) := (Subgroup.centralizer _).pow_mem hcC d
  have htP : t ∈ Subgroup.centralizer (f5.P₁ : Set G) :=
    (Subgroup.centralizer _).pow_mem hcP d
  have htt : t * t = 1 := by rw [← pow_two, ← hot, pow_orderOf_eq_one]
  obtain ⟨j, hj, m, hm, hjm⟩ := s.fr.exists_decomp_H_JM htH
  have hjc : j * m = m * j := s.fr.commute_of_mem_KE hj hm
  have hjj : j * j = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hj with rfl | rfl
    · exact mul_one 1
    · exact s.J_mul_J
  have hmm : m * m = 1 := by
    calc m * m = (j * j)⁻¹ * (j * (j * m) * m) := by group
      _ = (j * j)⁻¹ * (j * (m * j) * m) := by rw [hjc]
      _ = (j * j)⁻¹ * ((j * m) * (j * m)) := by group
      _ = 1 := by rw [← hjm, htt, hjj]; group
  have hmK := s.fr.mem_K_of_mem_KE_of_mul_self hm hmm
  have hmC : m ∈ Subgroup.centralizer (f5.P₁ : Set G) := by
    have h1 : m = j⁻¹ * t := by rw [hjm]; group
    rw [h1]
    exact mul_mem (inv_mem (Subgroup.zpowers_le.mpr f5.J_mem_centralizer_P₁ hj)) htP
  have hmP := f5.K_inf_centralizer_le hmK hmC
  have hm1 : m = 1 := by
    have h2 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hmm])
    have hq : Odd (Nat.card f5.P₁) := by
      rw [f5.card_P₁, Hyp.q]
      exact s.odd_p.pow
    have h4 : Odd (orderOf m) := Odd.of_dvd_nat hq (Subgroup.orderOf_dvd_natCard _ hmP)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h4
      exact absurd h4 (by decide)
  rw [hm1, mul_one] at hjm
  rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hj with h | h
  · rw [hjm, h, orderOf_one] at hot
    norm_num at hot
  · rw [hjm, h] at htC
    exact hR.J_not_mem_centralizer hRc h22 h26i hp hRq htC

end RData

end Frame5

end CFSG.Walter.W67

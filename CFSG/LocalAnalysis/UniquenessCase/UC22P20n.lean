module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20m
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

theorem uc22p20n_arith {p k b : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (h : (2 ^ k + 1) ∣ p ^ b) : ∃ k' : ℕ, p = 2 ^ k' + 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h
  have h1 : p - 1 ∣ p ^ j - 1 := Nat.sub_one_dvd_pow_sub_one p j
  have h2 : p ^ j - 1 = 2 ^ k := by rw [← hj]; simp
  rw [h2] at h1
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact ⟨a, (Nat.sub_eq_iff_eq_add hp.one_le).1 ha⟩

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem uc22p20n_coe_sup_of_perm {H K : Subgroup G} (h : (H : Set G) * K = K * H) :
    ((H ⊔ K : Subgroup G) : Set G) = H * K := by
  rw [Subgroup.sup_eq_closure_mul]
  refine Set.Subset.antisymm (fun x hx => ?_) Subgroup.subset_closure
  induction hx using Subgroup.closure_induction'' with
  | one => exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  | mem _ hx => exact hx
  | inv_mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have h1 : b⁻¹ * a⁻¹ ∈ (K : Set G) * H := ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
    rw [← h] at h1
    obtain ⟨a', ha', b', hb', e⟩ := h1
    have e' : a' * b' = b⁻¹ * a⁻¹ := e
    exact ⟨a', ha', b', hb', by show a' * b' = (a * b)⁻¹; rw [e']; group⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨c, hc, d, hd, rfl⟩ := hy
    have h1 : b * c ∈ (K : Set G) * H := ⟨b, hb, c, hc, rfl⟩
    rw [← h] at h1
    obtain ⟨c', hc', b', hb', e⟩ := h1
    have e' : c' * b' = b * c := e
    refine ⟨a * c', H.mul_mem ha hc', b' * d, K.mul_mem hb' hd, ?_⟩
    show a * c' * (b' * d) = a * b * (c * d)
    calc a * c' * (b' * d) = a * (c' * b') * d := by group
      _ = a * (b * c) * d := by rw [e']
      _ = a * b * (c * d) := by group

theorem uc22p20n_card_sup_perm {p : ℕ} [Fact p.Prime] {P S : Subgroup G} (hPp : IsPGroup p ↥P)
    (hS2 : IsPGroup 2 ↥S) (hPS : (P : Set G) * S = (S : Set G) * P) :
    ∃ a n : ℕ, Nat.card ↥(P ⊔ S) = 2 ^ a * p ^ n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRcoe : ((P ⊔ S : Subgroup G) : Set G) = P * S := uc22p20n_coe_sup_of_perm hPS
  have hPR : P ≤ P ⊔ S := le_sup_left
  have hSR : S ≤ P ⊔ S := le_sup_right
  set R : Subgroup G := P ⊔ S with hR
  set S' : Subgroup ↥R := S.subgroupOf R with hS'
  set P' : Subgroup ↥R := P.subgroupOf R with hP'
  have hP'p : IsPGroup p ↥P' := hPp.comap_subtype
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hS2
  have hS'card : Nat.card S' = 2 ^ a := by
    rw [← ha]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSR).toEquiv
  set o : ↥R ⧸ S' := QuotientGroup.mk 1 with ho
  have horb : MulAction.orbit P' o = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : (x : G) ∈ ((P : Set G) * S) := by rw [← hRcoe]; exact x.2
    obtain ⟨u, hu, v, hv, hxe⟩ := hx
    refine ⟨⟨⟨u, hPR hu⟩, hu⟩, ?_⟩
    show (⟨u, hPR hu⟩ : ↥R) • o = (QuotientGroup.mk x : ↥R ⧸ S')
    rw [ho, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have hxe' : u * v = (x : G) := hxe
    have : ((⟨u, hPR hu⟩ : ↥R)⁻¹ * x : ↥R).1 = v := by
      show u⁻¹ * (x : G) = v
      rw [← hxe']; group
    rw [this]
    exact hv
  obtain ⟨n, hn⟩ := hP'p.card_orbit o
  have hidx : S'.index = p ^ n := by
    have h1 : Nat.card (MulAction.orbit P' o) = Nat.card (↥R ⧸ S') := by
      rw [horb]
      exact Nat.card_congr (Equiv.Set.univ _)
    rw [Subgroup.index_eq_card, ← h1, hn]
  refine ⟨a, n, ?_⟩
  rw [← Subgroup.card_mul_index S', hS'card, hidx]

theorem uc22p20n_card_image_dvd {L R : Subgroup G} (hRL : R ≤ L) :
    Nat.card ↥((R.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ∣ Nat.card ↥R := by
  have h1 := Subgroup.card_map_dvd (H := R.subgroupOf L) (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have h2 : Nat.card ↥(R.subgroupOf L) = Nat.card ↥R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
  rwa [h2] at h1

theorem uc22p20n_le_normalizer_of_div (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hDiv : uc22p20kDiv (Bar2 L)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hnf : ¬ ∃ k : ℕ, p = 2 ^ k + 1) {P : Subgroup G} (hPp : IsPGroup p ↥P) (hPL : P ≤ L)
    (hperm : Permutes P D.T) : P ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  have hS2 : IsPGroup 2 ↥(D.T ⊓ L) := D.sylowM.isPGroup.to_inf_left
  have hPS : (P : Set G) * ↑(D.T ⊓ L) = (↑(D.T ⊓ L) : Set G) * P := by
    have h1 := Subgroup.mul_inf_assoc P D.T L hPL
    have h2 := Subgroup.inf_mul_assoc L D.T P hPL
    rw [inf_comm] at h2
    have hperm' : (P : Set G) * D.T = D.T * P := hperm
    rw [h1, h2, hperm', Set.inter_comm]
  obtain ⟨a, n, hcard⟩ := uc22p20n_card_sup_perm (p := p) hPp hS2 hPS
  have hPR : P ≤ P ⊔ (D.T ⊓ L) := le_sup_left
  have hSR : D.T ⊓ L ≤ P ⊔ (D.T ⊓ L) := le_sup_right
  have hRL : P ⊔ (D.T ⊓ L) ≤ L := sup_le hPL inf_le_right
  have hUY : ((uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL) :
      Subgroup (Bar2 L)) ≤ ((P ⊔ (D.T ⊓ L)).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.2 (hSR (Subgroup.mem_subgroupOf.1 hl)), rfl⟩
  have hYnot : ¬ ((P ⊔ (D.T ⊓ L)).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≤
      normalizer (((uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL) :
        Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    intro hle
    apply hnot
    intro x hx
    have hxL : x ∈ L := hPL hx
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩ ∈
        ((P ⊔ (D.T ⊓ L)).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 (hPR hx), rfl⟩
    exact uc22p20i_mem_normalizer_of_borel D hL ⟨x, hxL⟩ (hle hmem)
  obtain ⟨k, hk1, hkdvd⟩ := hDiv _ _ hUY hYnot
  have hdvd : (2 ^ k + 1) ∣ 2 ^ a * p ^ n := by
    rw [← hcard]
    exact hkdvd.trans (uc22p20n_card_image_dvd hRL)
  have hodd : Odd (2 ^ k + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have hcop : Nat.Coprime (2 ^ k + 1) (2 ^ a) := (Nat.coprime_two_right.mpr hodd).pow_right a
  exact hnf (uc22p20n_arith hp hk1 (hcop.dvd_of_dvd_mul_left hdvd))

end Normalizer

section Prime

theorem uc22p20n_not_fermat {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P B : Subgroup G} (hPp : IsPGroup p ↥P) (hPc : IsCyclic ↥P)
    (hBN : B ≤ normalizer (P : Set G)) (hBodd : Odd (Nat.card B)) (hPB : ⁅P, B⁆ = P)
    (hPne : P ≠ ⊥) : ¬ ∃ k : ℕ, p = 2 ^ k + 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨k₀, hk₀⟩
  obtain ⟨g, hg⟩ := hPc.exists_generator
  set g' : G := (g : G) with hg'
  have hgP : g' ∈ P := g.2
  have hPeq : ∀ x ∈ P, ∃ s : ℤ, g' ^ s = x := by
    intro x hx
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    exact ⟨s, by simpa using congrArg Subtype.val hs⟩
  have hg1 : g' ≠ 1 := by
    intro h1
    apply hPne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨s, rfl⟩ := hPeq x hx
    rw [h1, one_zpow]
    exact Subgroup.one_mem _
  have hordp : p ∣ orderOf g' := by
    obtain ⟨k, hk⟩ := hPp g
    have hk' : g' ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf g' ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      simp only [pow_zero] at hj'
      exact hg1 (orderOf_eq_one_iff.1 hj')
    rw [hj']
    exact dvd_pow_self p hj0
  have hmain : ∀ b ∈ B, ∃ m : ℤ, b * g' * b⁻¹ = g' ^ m ∧ (p : ℤ) ∣ m - 1 := by
    intro b hb
    have hbg : b * g' * b⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hBN hb) g').1 hgP
    obtain ⟨m, hm⟩ := hPeq _ hbg
    refine ⟨m, hm.symm, ?_⟩
    have hiter : ∀ i : ℕ, b ^ i * g' * (b ^ i)⁻¹ = g' ^ (m ^ i) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have e : b ^ (i + 1) * g' * (b ^ (i + 1))⁻¹ = b * (b ^ i * g' * (b ^ i)⁻¹) * b⁻¹ := by
          group
        rw [e, ih, ← conj_zpow, ← hm, ← zpow_mul, pow_succ']
    set n := orderOf b with hn
    have hnodd : Odd n := by
      have h1 : orderOf (⟨b, hb⟩ : ↥B) ∣ Nat.card B := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hBodd h1
    have hnpos : 0 < n := orderOf_pos b
    have h2 : g' ^ (m ^ n) = g' := by
      have := hiter n
      rw [hn, pow_orderOf_eq_one] at this
      simpa using this.symm
    have h3 : g' ^ (m ^ n - 1) = 1 := by
      rw [zpow_sub_one, h2, mul_inv_cancel]
    have h4 : (orderOf g' : ℤ) ∣ m ^ n - 1 := orderOf_dvd_iff_zpow_eq_one.2 h3
    have h5 : (p : ℤ) ∣ m ^ n - 1 := (Int.natCast_dvd_natCast.2 hordp).trans h4
    have h6 : (((m : ℤ) : ZMod p)) ^ n = 1 := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (m ^ n) p).2 h5
      push_cast at this
      exact this.symm
    set a : ZMod p := ((m : ℤ) : ZMod p) with ha
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, zero_pow hnpos.ne'] at h6
      exact zero_ne_one h6
    have hfer : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha0
    have hcop : Nat.Coprime n (p - 1) := by
      have := (Nat.coprime_two_right.mpr hnodd).pow_right k₀
      have hp1 : p - 1 = 2 ^ k₀ := by rw [hk₀]; simp
      rwa [hp1]
    have h7 : orderOf a ∣ Nat.gcd n (p - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h6) (orderOf_dvd_of_pow_eq_one hfer)
    rw [hcop] at h7
    have h8 : a = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h7)
    have h9 := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 m p).1 (by rw [← ha, h8]; simp)
    exact h9
  have hcommP : ∀ x ∈ P, ∀ b ∈ B, ⁅x, b⁆ ∈ Subgroup.zpowers (g' ^ (p : ℤ)) := by
    intro x hx b hb
    obtain ⟨s, rfl⟩ := hPeq x hx
    obtain ⟨m, hm, t, ht⟩ := hmain b hb
    have hconj : ∀ s : ℤ, b * g' ^ s * b⁻¹ = g' ^ (m * s) := by
      intro s
      rw [← conj_zpow, hm, ← zpow_mul]
    have e1 : ⁅g' ^ s, b⁆ = g' ^ s * (b * g' ^ s * b⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1, hconj, ← zpow_neg, ← zpow_add]
    refine Subgroup.mem_zpowers_iff.2 ⟨-(s * t), ?_⟩
    rw [← zpow_mul]
    congr 1
    have : m = p * t + 1 := by linarith
    rw [this]
    ring
  have hPle : ⁅P, B⁆ ≤ Subgroup.zpowers (g' ^ (p : ℤ)) :=
    Subgroup.commutator_le.2 fun x hx b hb => hcommP x hx b hb
  rw [hPB] at hPle
  have hg'mem : g' ∈ Subgroup.zpowers (g' ^ (p : ℤ)) := hPle hgP
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg'mem
  have h1 : g' ^ ((p : ℤ) * k - 1) = 1 := by
    rw [zpow_sub_one, zpow_mul, hk, mul_inv_cancel]
  have hdv : (orderOf g' : ℤ) ∣ (p : ℤ) * k - 1 := orderOf_dvd_iff_zpow_eq_one.2 h1
  have hpd : (p : ℤ) ∣ (p : ℤ) * k - 1 := (Int.natCast_dvd_natCast.2 hordp).trans hdv
  have h2 : (p : ℤ) ∣ 1 := by
    have := dvd_sub (dvd_mul_right (p : ℤ) k) hpd
    simpa using this
  have h3 : p ∣ 1 := by exact_mod_cast h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)


end Prime

section Final

variable {G : Type} [Group G] [Finite G]

theorem uc22p20n_normL0_of_props (D : Data G) (Ch : Choice2011 G)
    (hS : H1930 D → ∀ L ∈ calL D.T D.M, uc22p20jSandwich (Bar2 L))
    (hDiv : H1930 D → ∀ L ∈ calL D.T D.M, uc22p20kDiv (Bar2 L)) : NormL0 D Ch := by
  intro h1930 c p hpσ P hPp hPcyc hPM hPU hPperm hBP hPB
  by_cases hP0 : P = ⊥
  · rw [hP0]
    exact bot_le
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hpσ
  have hPL : P ≤ c.L := uc22p22m_le_L_ctx c hPU hPB
  have hnf := uc22p20n_not_fermat hpp hp2 hPp hPcyc hBP
    (uc22p22f_odd_card_B c.toCtx22.toCtx21) hPB hP0
  have hPS : P ≤ normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) :=
    uc22p20n_le_normalizer_of_div D c.hL.1 (hDiv h1930 c.L c.hL.1) hpp hp2 hnf hPp hPL hPperm
  obtain ⟨Q, hQ, hTQ, hL0Q⟩ :=
    uc22p20m_l0Parabolic_of_sandwich D hS h1930 c.L c.hL.1 c.L0 c.hL0 c.hLge
  have hPQ : P ≤ Q := uc22p22m_le_of_parabolic D.sylowG c.hL.1.1 hQ hTQ hPL hPS
  rw [hL0Q]
  exact hPQ.trans (uc22p22m_le_normalizer_Hinf Q)

end Final

section Chain


variable {G : Type} [Group G] [Finite G]

theorem uc22p20n_l0Parabolic_of_s20_7 (D : Data G) (h20_7 : S20_7 D) : L0Parabolic D :=
  uc22p20m_l0Parabolic_of_sandwich D fun h1930 L hL => by
    obtain ⟨B, N, hBN⟩ := uc22p20l_splitBN_of_shape D h20_7 h1930 hL
    exact uc22p20j_sandwich_of_splitBN hBN

theorem uc22p20n_normL0_of_s20_7 (D : Data G) (Ch : Choice2011 G) (h20_7 : S20_7 D) : NormL0 D Ch :=
  uc22p20n_normL0_of_props D Ch
    (fun h1930 L hL => by
      obtain ⟨B, N, hBN⟩ := uc22p20l_splitBN_of_shape D h20_7 h1930 hL
      exact uc22p20j_sandwich_of_splitBN hBN)
    (fun h1930 L hL => by
      obtain ⟨B, N, hBN⟩ := uc22p20l_splitBN_of_shape D h20_7 h1930 hL
      exact uc22p20k_div_of_splitBN hBN)

end Chain

end CFSG.LocalAnalysis.UniquenessCase.UC22

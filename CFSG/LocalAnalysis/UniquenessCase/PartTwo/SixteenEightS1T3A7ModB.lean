module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7ModA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarPt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A67Cyc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute H K hcomm).2
  have hx' : x ∈ ((H ⊔ K : Subgroup G) : Set G) := hx
  rw [h] at hx'
  obtain ⟨h, hh, k, hk, hk'⟩ := hx'
  exact ⟨h, hh, k, hk, hk'⟩

theorem s16t3_normal_of_sup_of_commute {G : Type*} [Group G] {N K A : Subgroup G}
    (hNA : N ≤ A) (hNK : N ⊔ K = A)
    (hcomm : ∀ n ∈ N, ∀ k ∈ K, n * k = k * n) : (N.subgroupOf A).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hNA]
  intro x a hx ha
  have ha' : a ∈ N ⊔ K := by rw [hNK]; exact ha
  obtain ⟨n, hn, k, hk, rfl⟩ := s16t3_exists_mul_of_mem_sup_of_commute hcomm ha'
  have hkx : k * x * k⁻¹ = x := by
    rw [← hcomm x hx k hk, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : (n * k) * x * (n * k)⁻¹ = n * x * n⁻¹ := by
    rw [mul_inv_rev]
    calc n * k * x * (k⁻¹ * n⁻¹) = n * (k * x * k⁻¹) * n⁻¹ := by group
      _ = n * x * n⁻¹ := by rw [hkx]
  rw [hconj]
  exact N.mul_mem (N.mul_mem hn hx) (N.inv_mem hn)

private theorem s16t3_mulAut_congr_conj {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (x : G) : MulAut.congr φ (MulAut.conj x) = MulAut.conj (φ x) := by
  ext y
  simp [MulAut.conj_apply]

theorem s16t3_exists_injective_perm_seven_ext {L N : Subgroup (MulAut W)} (hLN : L ≤ N)
    (hNnorm : N ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (e : ↥L ≃* alternatingGroup (Fin 7))
    (hC : Subgroup.centralizer (L.subgroupOf N : Set ↥N) = ⊥) :
    ∃ θ : ↥N →* Equiv.Perm (Fin 7), Function.Injective θ ∧
      ∀ l : ↥L, θ ⟨(l : MulAut W), hLN l.2⟩ = (e l : Equiv.Perm (Fin 7)) := by
  haveI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hNnorm
  let c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7))
  have hc : Function.Bijective c :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)
  let eAut : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective c hc
  let ψ : ↥N →* MulAut ↥L :=
    (MulAut.congr (Subgroup.subgroupOfEquivOfLe hLN)).toMonoidHom.comp
      (MulAut.conjNormal (H := L.subgroupOf N))
  have hconjInj : Function.Injective
      (MulAut.conjNormal (H := L.subgroupOf N) : ↥N →* MulAut ↥(L.subgroupOf N)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have : g ∈ Subgroup.centralizer (L.subgroupOf N : Set ↥N) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := congrArg (fun φ : MulAut ↥(L.subgroupOf N) =>
        ((φ ⟨n, hn⟩ : ↥(L.subgroupOf N)) : ↥N)) hg
      have h2 : g * n * g⁻¹ = n := by simpa [MulAut.conjNormal_apply] using h1
      calc n * g = (g * n * g⁻¹) * g := by rw [h2]
        _ = g * n := by group
    rw [hC] at this
    exact this
  have hψ : Function.Injective ψ :=
    (MulAut.congr (Subgroup.subgroupOfEquivOfLe hLN)).injective.comp hconjInj
  refine ⟨eAut.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp ψ),
    eAut.symm.injective.comp ((MulAut.congr e).injective.comp hψ), ?_⟩
  intro l
  have hx : (⟨(l : MulAut W), hLN l.2⟩ : ↥N) =
      (((⟨⟨(l : MulAut W), hLN l.2⟩, l.2⟩ : ↥(L.subgroupOf N)) : ↥(L.subgroupOf N)) : ↥N) := rfl
  have hψl : ψ ⟨(l : MulAut W), hLN l.2⟩ = MulAut.conj l := by
    rw [hx]
    change (MulAut.congr (Subgroup.subgroupOfEquivOfLe hLN))
        ((MulAut.conjNormal (H := L.subgroupOf N))
          (((⟨⟨(l : MulAut W), hLN l.2⟩, l.2⟩ : ↥(L.subgroupOf N)) : ↥(L.subgroupOf N)) : ↥N))
      = MulAut.conj l
    rw [show ((⟨⟨(l : MulAut W), hLN l.2⟩, l.2⟩ : ↥(L.subgroupOf N)) : ↥N) =
        (↑(⟨⟨(l : MulAut W), hLN l.2⟩, l.2⟩ : ↥(L.subgroupOf N)) : ↥N) from rfl,
      MulAut.conjNormal_val, s16t3_mulAut_congr_conj]
    rfl
  show eAut.symm ((MulAut.congr e) (ψ ⟨(l : MulAut W), hLN l.2⟩)) = (e l : Equiv.Perm (Fin 7))
  rw [hψl, s16t3_mulAut_congr_conj]
  rw [show MulAut.conj (e l) = eAut (e l) from by
    rw [show eAut (e l) = c (e l) from rfl, MulAut.conjNormal_val]]
  exact MulEquiv.symm_apply_apply eAut (e l)

private theorem s16t3_mem_of_odd_order_of_relIndex_le_two {G : Type*} [Group G] [Finite G]
    {L N : Subgroup G} (hLN : (L.subgroupOf N).Normal) (h : L.relIndex N ≤ 2)
    {x : G} (hxN : x ∈ N) (hx : Odd (orderOf x)) : x ∈ L := by
  set x' : ↥N := ⟨x, hxN⟩ with hx'
  set q : ↥N ⧸ L.subgroupOf N := QuotientGroup.mk' (L.subgroupOf N) x' with hq
  have hq_dvd : orderOf q ∣ L.relIndex N := by
    rw [Subgroup.relIndex]
    exact orderOf_dvd_natCard q
  have hq2 : orderOf q ∣ 2 := by
    have hpos : 0 < L.relIndex N := by
      rw [Subgroup.relIndex]
      exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rcases (by omega : L.relIndex N = 1 ∨ L.relIndex N = 2) with h1 | h2
    · rw [h1] at hq_dvd
      exact Nat.dvd_one.mp hq_dvd ▸ one_dvd 2
    · rwa [h2] at hq_dvd
  have hqx : orderOf q ∣ orderOf x := by
    apply orderOf_dvd_of_pow_eq_one
    have hx'ord : (x' : ↥N) ^ orderOf x = 1 := by
      rw [← show orderOf (x' : ↥N) = orderOf x from (Subgroup.orderOf_coe x').symm]
      exact pow_orderOf_eq_one _
    calc q ^ orderOf x = QuotientGroup.mk' (L.subgroupOf N) ((x' : ↥N) ^ orderOf x) := by
          rw [hq, ← map_pow]
      _ = 1 := by rw [hx'ord, map_one]
  have hq1 : orderOf q = 1 := by
    have hcop : Nat.Coprime 2 (orderOf x) := hx.coprime_two_left
    have hd := Nat.dvd_gcd hq2 hqx
    rw [hcop.gcd_eq_one] at hd
    exact Nat.dvd_one.mp hd
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff x').mp (orderOf_eq_one_iff.mp hq1))

theorem s16t3_exists_sylow_le_alt_seven {L N P : Subgroup (MulAut W)}
    (hLN : L ≤ N) (hNnorm : N ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (e : ↥L ≃* alternatingGroup (Fin 7))
    (hC : Subgroup.centralizer (L.subgroupOf N : Set ↥N) = ⊥)
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P N) :
    ∃ J : Subgroup (MulAut W), J ≤ N ∧ P ≤ J ∧ Nat.card ↥J = 9 * Nat.card ↥P := by
  obtain ⟨θ, hθinj, hθL⟩ := s16t3_exists_injective_perm_seven_ext hLN hNnorm e hC
  have hA7 : alternatingGroup (Fin 7) ≤ θ.range := by
    intro y hy
    obtain ⟨l, hl⟩ := e.surjective ⟨y, hy⟩
    refine ⟨⟨(l : MulAut W), hLN l.2⟩, ?_⟩
    rw [hθL l, hl]
  let PN' : Subgroup (Equiv.Perm (Fin 7)) := (P.subgroupOf N).map θ
  have hP'2 : IsPGroup 2 PN' := (hP.isPGroup.comap_subtype (K := N)).map θ
  have hPN'le : PN' ≤ θ.range := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨y, rfl⟩
  have hP'card : Nat.card ↥PN' = Nat.card ↥P := by
    rw [show PN' = (P.subgroupOf N).map θ from rfl,
      Subgroup.card_map_of_injective hθinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.le).toEquiv
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf 2 PN' θ.range := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hPN'le, hP'2, ?_⟩
    rw [show θ.range = (⊤ : Subgroup ↥N).map θ from (Subgroup.map_top θ).symm,
      show PN' = (P.subgroupOf N).map θ from rfl,
      Subgroup.relIndex_map_map_of_injective _ _ hθinj,
      Subgroup.relIndex_top_right]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hP).2.2
  obtain ⟨J', hJ'le, hPN'leJ', hJ'card⟩ := s16t3_exists_sylow_le_perm_seven θ.range hA7 hP'syl
  let J₁ : Subgroup (MulAut W) := (J'.comap θ).map N.subtype
  have hJ₁le : J₁ ≤ N := Subgroup.map_subtype_le _
  have hJ₁card : Nat.card ↥J₁ = 9 * Nat.card ↥P := by
    rw [show J₁ = (J'.comap θ).map N.subtype from rfl,
      Subgroup.card_map_of_injective N.subtype_injective]
    have hcomap : Nat.card ↥(J'.comap θ) = Nat.card ↥J' := by
      rw [← Subgroup.card_map_of_injective hθinj]
      congr 1
      rw [Subgroup.map_comap_eq, inf_eq_right.mpr hJ'le]
    rw [hcomap, hJ'card, hP'card]
  have hPleJ₁ : P ≤ J₁ := by
    intro x hx
    refine Subgroup.mem_map.2 ⟨⟨x, hP.le hx⟩, ?_, rfl⟩
    exact hPN'leJ' (Subgroup.mem_map.2 ⟨⟨x, hP.le hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩)
  exact ⟨J₁, hJ₁le, hPleJ₁, hJ₁card⟩

theorem s16t3_exists_J_alt7_aux (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    (e : ↥L ≃* alternatingGroup (Fin 7)) (hK : Nat.card ↥(s1t3KBar A L) = 168) :
    ∃ J : Subgroup (MulAut W), J ≤ A ∧ T ≤ J ∧ (∃ x : ℕ, Nat.card ↥J = 2 ^ x * 3 ^ 3) ∧
      ∀ g ∈ J, IsPGroup 3 (Subgroup.zpowers g) →
        ∃ (n : ↥L) (k : MulAut W), (n : MulAut W) * k = g ∧ k ∈ s1t3KBar A L ∧
          (((e n : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).cycleType = 0 ∨
            ((e n : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).cycleType = {3} ∨
            ((e n : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).cycleType = {3, 3}) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N, hNA, hLleN, hNfix, hNcomm, hNKbot, hNKsup, hKcase⟩ := h.structure_of_seven h7
  let K : Subgroup (MulAut W) := s1t3KBar A L
  have hKA : K ≤ A := inf_le_left
  have hNnormA : (N.subgroupOf A).Normal := s16t3_normal_of_sup_of_commute hNA hNKsup hNcomm
  have hKnormA : (K.subgroupOf A).Normal := by
    refine s16t3_normal_of_sup_of_commute (N := K) (K := N) (A := A) hKA ?_ ?_
    · rw [sup_comm]; exact hNKsup
    · intro k hk n hn; exact (hNcomm n hn k hk).symm
  have hA_normN : A ≤ Subgroup.normalizer (N : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mp hNnormA
  have hA_normK : A ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).mp hKnormA
  have hTNsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ N) N :=
    h.sylow.inf_of_le_normalizer hNA hA_normN
  have hTKsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K :=
    h.sylow.inf_of_le_normalizer hKA hA_normK
  have hNnorm_L : N ≤ Subgroup.normalizer (L : Set (MulAut W)) := hNA.trans h.normal
  haveI hLNsub : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLleN).mpr hNnorm_L
  have hrel : L.relIndex N ≤ 2 := by
    have hAcard : Nat.card ↥A = Nat.card ↥N * Nat.card ↥K := by
      have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute N K hNcomm).1
      rw [hNKsup, hNKbot, Subgroup.card_bot, mul_one] at h
      exact h
    have hdvd := h.card_dvd_of_seven h7
    have hN_dvd : Nat.card ↥N ∣ 2 * Nat.card ↥L := by
      have hdvd' : Nat.card ↥N * Nat.card ↥K ∣ 336 * Nat.card ↥L := by
        rwa [hAcard] at hdvd
      rw [hK] at hdvd'
      have h' : Nat.card ↥N * 168 ∣ 168 * (2 * Nat.card ↥L) := by
        rwa [show (336 : ℕ) = 168 * 2 by norm_num, mul_assoc] at hdvd'
      rw [mul_comm (Nat.card ↥N) 168] at h'
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 168)).1 h'
    have hLNcard : Nat.card ↥N = Nat.card ↥L * L.relIndex N := by
      rw [← (L.subgroupOf N).card_mul_index, Subgroup.relIndex,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLleN).toEquiv]
    have hrel_dvd : L.relIndex N ∣ 2 := by
      have h := hN_dvd
      rw [hLNcard, mul_comm (2 : ℕ) (Nat.card ↥L)] at h
      exact (Nat.mul_dvd_mul_iff_left (Nat.card_pos (α := ↥L))).1 h
    exact Nat.le_of_dvd (by norm_num) hrel_dvd
  have hC : Subgroup.centralizer (L.subgroupOf N : Set ↥N) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxK : (x : MulAut W) ∈ K := by
      refine ⟨hNA x.2, ?_⟩
      change (x : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W))
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hxl := (Subgroup.mem_centralizer_iff.1 hx) ⟨(l : MulAut W), hLleN hl⟩
        (Subgroup.mem_subgroupOf.2 hl)
      exact congrArg Subtype.val hxl
    have hbot : (x : MulAut W) ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hNKbot]; exact ⟨x.2, hxK⟩
    exact Subtype.ext (by simpa using hbot)
  obtain ⟨J₁, hJ₁le, hTNleJ₁, hJ₁card⟩ :=
    s16t3_exists_sylow_le_alt_seven hLleN hNnorm_L e hC hTNsyl
  obtain ⟨I₀, hI₀, hI₀T, J₂, hJ₂le, hT₂le, hJ₂mem, hJ₂card, -⟩ := h.exists_point_stabilizer h7 hK
  have hJ₂leK : J₂ ≤ K := hJ₂le
  have hTcardT : Nat.card ↥T = Nat.card ↥(T ⊓ N) * Nat.card ↥(T ⊓ K) := by
    have hA := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute N K hNcomm).1
    rw [hNKsup, hNKbot, Subgroup.card_bot, mul_one] at hA
    rw [h.sylow.card_eq, hA, Nat.factorization_mul (Nat.card_pos (α := ↥N)).ne'
        (Nat.card_pos (α := ↥K)).ne',
      Finsupp.add_apply, pow_add, (hTNsyl.card_eq).symm, (hTKsyl.card_eq).symm]
  have hTleJ : T ≤ J₁ ⊔ J₂ := by
    have hcomm : ∀ h ∈ T ⊓ N, ∀ k ∈ T ⊓ K, h * k = k * h :=
      fun h hh k hk => hNcomm h hh.2 k hk.2
    have hcardprod : Nat.card ↥((T ⊓ N) ⊔ (T ⊓ K)) =
        Nat.card ↥(T ⊓ N) * Nat.card ↥(T ⊓ K) := by
      have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (T ⊓ N) (T ⊓ K) hcomm).1
      have hinf : (T ⊓ N) ⊓ (T ⊓ K) = ⊥ := by
        apply le_antisymm _ bot_le
        rw [← hNKbot]
        exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
      rw [hinf, Subgroup.card_bot, mul_one] at h
      exact h
    have hle : (T ⊓ N) ⊔ (T ⊓ K) ≤ T := sup_le inf_le_left inf_le_left
    have heq : (T ⊓ N) ⊔ (T ⊓ K) = T :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardprod, hTcardT])
    rw [← heq]
    exact sup_le_sup hTNleJ₁ hT₂le
  refine ⟨J₁ ⊔ J₂, sup_le (hJ₁le.trans hNA) (hJ₂leK.trans hKA), hTleJ, ?_, ?_⟩
  · have hcomm : ∀ h ∈ J₁, ∀ k ∈ J₂, h * k = k * h :=
      fun h hh k hk => hNcomm h (hJ₁le hh) k (hJ₂leK hk)
    have hcardJ : Nat.card ↥(J₁ ⊔ J₂) = 27 * Nat.card ↥T := by
      have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute J₁ J₂ hcomm).1
      have hinf : J₁ ⊓ J₂ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        have hxN : x ∈ N := hJ₁le hx.1
        have hxK : x ∈ K := hJ₂leK hx.2
        have : x ∈ (⊥ : Subgroup (MulAut W)) := by rw [← hNKbot]; exact ⟨hxN, hxK⟩
        simpa using this
      rw [hinf, Subgroup.card_bot, mul_one] at h
      rw [h, hJ₁card, hJ₂card, hTcardT]
      ring
    obtain ⟨m, hm⟩ := h.sylow.isPGroup.exists_card_eq
    refine ⟨m, ?_⟩
    rw [hcardJ, hm]
    ring
  · intro g hg hg3
    have hcomm : ∀ h ∈ J₁, ∀ k ∈ J₂, h * k = k * h :=
      fun h hh k hk => hNcomm h (hJ₁le hh) k (hJ₂leK hk)
    obtain ⟨j₁, hj₁, j₂, hj₂, hgjk⟩ := s16t3_exists_mul_of_mem_sup_of_commute hcomm hg
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3) (G := Subgroup.zpowers g)).1 hg3
    have horder : orderOf g = 3 ^ m := by rw [← Nat.card_zpowers]; exact hm
    have hgpow : g ^ 3 ^ m = 1 := (orderOf_dvd_iff_pow_eq_one).1 (by rw [horder])
    have hcommg : Commute j₁ j₂ := hcomm j₁ hj₁ j₂ hj₂
    have hj₁pow : j₁ ^ 3 ^ m = 1 := by
      have h1 : (j₁ * j₂) ^ 3 ^ m = 1 := by rw [hgjk]; exact hgpow
      rw [hcommg.mul_pow] at h1
      have h2 : j₁ ^ 3 ^ m = (j₂ ^ 3 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hmemN : j₁ ^ 3 ^ m ∈ N := hJ₁le (J₁.pow_mem hj₁ _)
      have hmemK : (j₂ ^ 3 ^ m)⁻¹ ∈ K := K.inv_mem (hJ₂leK (J₂.pow_mem hj₂ _))
      have hbot : j₁ ^ 3 ^ m ∈ (⊥ : Subgroup (MulAut W)) := by
        rw [← hNKbot]; exact ⟨hmemN, h2 ▸ hmemK⟩
      simpa using hbot
    have hoddj : Odd (orderOf j₁) := by
      have hdvd : orderOf j₁ ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hj₁pow
      exact Nat.not_even_iff_odd.1 fun he =>
        (by norm_num : ¬ (2 : ℕ) ∣ 3)
          (Nat.prime_two.dvd_of_dvd_pow (even_iff_two_dvd.mp he |>.trans hdvd))
    have hj₁L : j₁ ∈ L :=
      s16t3_mem_of_odd_order_of_relIndex_le_two hLNsub hrel (hJ₁le hj₁) hoddj
    refine ⟨⟨j₁, hj₁L⟩, j₂, hgjk, hJ₂leK hj₂, ?_⟩
    have hdvd : orderOf ((e ⟨j₁, hj₁L⟩ : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) ∣ 3 ^ m := by
      apply orderOf_dvd_of_pow_eq_one
      have h1 : (⟨j₁, hj₁L⟩ : ↥L) ^ 3 ^ m = 1 := Subtype.ext hj₁pow
      calc ((e ⟨j₁, hj₁L⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ^ 3 ^ m
          = ((e (⟨j₁, hj₁L⟩ ^ 3 ^ m) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
            rw [map_pow, ← Subgroup.coe_pow]
        _ = 1 := by rw [h1, map_one]; rfl
    exact s16t3_cycleType_of_isPGroup_three (n := 7) (by norm_num)
      ((e ⟨j₁, hj₁L⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) (by
        rw [IsPGroup.iff_card]
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
        exact ⟨k, by rw [Nat.card_zpowers]; exact hk⟩)


end CFSG.LocalAnalysis.UniquenessCase.PartTwo

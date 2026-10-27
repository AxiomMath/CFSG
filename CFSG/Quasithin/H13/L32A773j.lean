module

public import CFSG.Quasithin.H13.L32A773i

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem perm5_sq_of_pow_four : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → σ ^ 4 = 1 →
    σ ^ 2 = 1 := by
  decide +kernel

theorem perm5_gen_aux : ∀ a ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin 5) =>
      σ ^ 2 = 1 ∧ σ ≠ 1 ∧ Equiv.Perm.sign σ = 1),
    ∀ b ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin 5) =>
      σ ^ 2 = 1 ∧ σ ≠ 1 ∧ Equiv.Perm.sign σ = 1),
    ∀ c ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin 5) =>
      σ ^ 2 = 1 ∧ σ ≠ 1 ∧ Equiv.Perm.sign σ = 1),
    (a * b) ^ 2 = 1 → a ≠ b → c ≠ a → c ≠ b → c ≠ a * b →
      (∃ x ∈ [a, b, a * b], (x * c) ^ 5 = 1 ∧ x * c ≠ 1) ∧
        (∃ x ∈ [a, b, a * b], (x * c) ^ 3 = 1 ∧ x * c ≠ 1) := by
  decide +kernel

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem mem_m1_of {φ : ↥(hz T V) →* Equiv.Perm (Fin 5)}
    (hk : φ.ker = CFSG.Open.pCore 2 ↥(hz T V)) {g : ↥(hz T V)}
    (hg : φ g ∈ Subgroup.normalizer
      (((pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).subgroupOf (hz T V)).map φ : Set _)) :
    (g : G) ∈ m1 T L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hLTV, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨-, h4⟩ := R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334
  have hNC := normalizer_eq_centralizer_of_card_two hV1
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set P₁ := (R.subgroupOf (hz T V)).map φ with hP₁
  have hRH : R ≤ hz T V := (pCoreOf_le_of_le C.hyp le_sup_right).trans hTH
  have hP₁4 : Nat.card ↥P₁ = 4 := by rw [hP₁, card_map_phi hk hRH, h4]
  set N := L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) with hN
  have hNH : N ≤ hz T V := fun x hx => by
    have := (Subgroup.mem_inf.mp hx).2
    rwa [hNC] at this
  have hQN : pCoreOf 2 (hz T V) ≤ N := fun x hx => Subgroup.mem_inf.mpr
    ⟨C.T_le_L (pCoreOf_le_of_le C.hyp hTH hx), by rw [hNC]; exact pCoreOf_le 2 _ hx⟩
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hidx : (N.subgroupOf L).index = 7 :=
    index_inf_normalizer_V1 (C.hyp.hyp1281One C.h13322 C.hMod) (le_sup_left.trans hLTV)
      inf_le_left hzV1 hz1 hgen
  have hNcard : Nat.card ↥N = 3 * 2 ^ 14 := by
    have h1 := Subgroup.relIndex_mul_card N L
    have hNL : N ≤ L := inf_le_left
    rw [show N.relIndex L = 7 from hidx, inf_eq_left.mpr hNL, C.card_L] at h1
    norm_num at h1 ⊢
    omega
  have hNstar : Nat.card ↥((N.subgroupOf (hz T V)).map φ) = 24 := by
    rw [card_map_phi hk hNH]
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V)) N
    rw [inf_eq_left.mpr hQN, C.card_QH, hNcard] at h1
    norm_num at h1 ⊢
    omega
  have hNR : ∀ n ∈ N, n ∈ Subgroup.normalizer (R : Set G) := fun n hn => by
    rw [hR, C.R1_eq_pCoreOf_l1]
    exact normalizer_le_normalizer_pCoreOf 2 _ (le_normalizer_oTwoRes _ hn)
  have hNP : (N.subgroupOf (hz T V)).map φ ≤ Subgroup.normalizer (P₁ : Set _) := by
    rintro _ ⟨n, hn, rfl⟩
    have hn' := hNR _ (Subgroup.mem_subgroupOf.mp hn)
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨?_, ?_⟩
    · rintro ⟨r, hr, rfl⟩
      refine ⟨n * r * n⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by
        rw [map_mul, map_mul, map_inv]⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp hn' _).mp (Subgroup.mem_subgroupOf.mp hr)
    · rintro ⟨r, hr, hrx⟩
      refine ⟨n⁻¹ * r * n, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn') _).mp
          (Subgroup.mem_subgroupOf.mp hr)
        simpa using this
      · rw [map_mul, map_mul, map_inv, hrx]
        group
  have hP₁A : P₁ ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    have hrK : (r : G) ∈ kz T V := by
      have := Subgroup.mem_subgroupOf.mp hr
      rw [hR, C.R1_eq_inf] at this
      exact (Subgroup.mem_inf.mp this).2
    exact sign_phi_kz hrK
  have hnt : Subgroup.normalizer (P₁ : Set (Equiv.Perm (Fin 5))) ≠ ⊤ := by
    intro htop
    have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hn : (P₁.subgroupOf (alternatingGroup (Fin 5))).Normal := ⟨fun y hy a => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have ha : (a : Equiv.Perm (Fin 5)) ∈ Subgroup.normalizer (P₁ : Set _) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_normalizer_iff.mp ha _).mp hy⟩
    have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁A).toEquiv
    rcases hn.eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.card_bot, hP₁4] at hc
      norm_num at hc
    · rw [ht, Subgroup.card_top, hP₁4, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at hc
      norm_num at hc
  have hNeq : Subgroup.normalizer (P₁ : Set (Equiv.Perm (Fin 5))) =
      (N.subgroupOf (hz T V)).map φ := by
    have hd1 : 24 ∣ Nat.card ↥(Subgroup.normalizer (P₁ : Set (Equiv.Perm (Fin 5)))) := by
      rw [← hNstar]
      exact Subgroup.card_dvd_of_le hNP
    have hd2 : Nat.card ↥(Subgroup.normalizer (P₁ : Set (Equiv.Perm (Fin 5)))) ∣ 120 := by
      have := Subgroup.card_subgroup_dvd_card
        (Subgroup.normalizer (P₁ : Set (Equiv.Perm (Fin 5))))
      rwa [Nat.card_perm, Nat.card_fin] at this
    have hne : Nat.card ↥(Subgroup.normalizer (P₁ : Set (Equiv.Perm (Fin 5)))) ≠ 120 :=
      fun h => hnt (Subgroup.eq_top_of_card_eq _ (by rw [h, Nat.card_perm, Nat.card_fin]; rfl))
    obtain ⟨j, hj⟩ := hd1
    have hj5 : j ∣ 5 := by
      rw [hj] at hd2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) (show 24 * j ∣ 24 * 5 from hd2)
    have hj1 : j = 1 := by
      rcases (Nat.dvd_prime (by norm_num)).mp hj5 with h | h
      · exact h
      · exact absurd (by rw [hj, h]) hne
    exact (Subgroup.eq_of_le_of_card_ge hNP (by rw [hNstar, hj, hj1])).symm
  rw [hNeq] at hg
  obtain ⟨n, hn, hng⟩ := hg
  have hq : n⁻¹ * g ∈ CFSG.Open.pCore 2 ↥(hz T V) := by
    rw [← hk, MonoidHom.mem_ker, map_mul, map_inv, hng, inv_mul_cancel]
  have hqL : ((n⁻¹ * g : ↥(hz T V)) : G) ∈ L :=
    C.T_le_L (pCoreOf_le_of_le C.hyp hTH (mem_pCoreOf_iff'.mpr hq))
  have hgL : (g : G) ∈ L := by
    have := mul_mem (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)).1 hqL
    simpa using this
  exact Subgroup.mem_inf.mpr ⟨g.2, Subgroup.le_normalizer hgL⟩

theorem kz_eq_sup {k : G} (hk : k ∈ kz T V) (hkM : k ∉ m1 T L V) :
    kz T V = sL T L V ⊔ (sL T L V).map (MulAut.conj k).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hs, hφk⟩ := exists_phi C.hyp C.h63
  obtain ⟨-, h4⟩ := R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have hSK := C.sL_le_kz
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  have hRH : R ≤ hz T V := (pCoreOf_le_of_le C.hyp le_sup_right).trans hTH
  set P₁ := (R.subgroupOf (hz T V)).map φ with hP₁
  have hP₁4 : Nat.card ↥P₁ = 4 := by rw [hP₁, card_map_phi hφk hRH, h4]
  have hSH : sL T L V ≤ hz T V := hSK.trans hKH
  set Sk := (sL T L V).map (MulAut.conj k).toMonoidHom with hSk
  set K₀ := sL T L V ⊔ Sk with hK₀
  have hSkK : Sk ≤ kz T V := by
    rintro _ ⟨s, hs', rfl⟩
    exact mul_mem (mul_mem hk (hSK hs')) (inv_mem hk)
  have hK₀K : K₀ ≤ kz T V := sup_le hSK hSkK
  have hQN : pCoreOf 2 (hz T V) ≤ Subgroup.normalizer (sL T L V : Set G) :=
    (pCoreOf_le_of_le C.hyp hTH).trans C.T_le_normalizer_sL
  have hP₁S : ∀ p ∈ P₁, ∃ s : G, ∃ hs : s ∈ sL T L V, φ ⟨s, hSH hs⟩ = p := by
    rintro _ ⟨r, hr, rfl⟩
    have hr0 : (r : G) ∈ (sL T L V ⊔ pCoreOf 2 (hz T V) : Subgroup G) := by
      rw [C.sup_eq_R1]
      exact Subgroup.mem_subgroupOf.mp hr
    have hr' : (r : G) ∈ ((sL T L V ⊔ pCoreOf 2 (hz T V) : Subgroup G) : Set G) := hr0
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hQN] at hr'
    obtain ⟨s, hs', q, hq, hsq⟩ := hr'
    refine ⟨s, hs', ?_⟩
    have hq' : (⟨q, pCoreOf_le 2 _ hq⟩ : ↥(hz T V)) ∈ CFSG.Open.pCore 2 ↥(hz T V) :=
      mem_pCoreOf_iff'.mp hq
    rw [← hφk, MonoidHom.mem_ker] at hq'
    have e : r = ⟨s, hSH hs'⟩ * ⟨q, pCoreOf_le 2 _ hq⟩ := Subtype.ext hsq.symm
    rw [e, map_mul, hq', mul_one]
  have hSP₁ : ∀ s (hs : s ∈ sL T L V), φ ⟨s, hSH hs⟩ ∈ P₁ := fun s hs =>
    ⟨⟨s, hSH hs⟩, Subgroup.mem_subgroupOf.mpr (C.sL_le_R1 hs), rfl⟩
  set M := (K₀.subgroupOf (hz T V)).map φ with hM
  have hMA : M ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    exact sign_phi_kz (hK₀K (Subgroup.mem_subgroupOf.mp hx))
  have hP₁M : P₁ ≤ M := fun p hp => by
    obtain ⟨s, hs', rfl⟩ := hP₁S p hp
    exact ⟨⟨s, hSH hs'⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hs'), rfl⟩
  set g := φ ⟨k, hKH hk⟩ with hg
  have hgP : ∀ p ∈ P₁, g * p * g⁻¹ ∈ M := fun p hp => by
    obtain ⟨s, hs', rfl⟩ := hP₁S p hp
    refine ⟨⟨k * s * k⁻¹, mul_mem (mul_mem (hKH hk) (hSH hs')) (inv_mem (hKH hk))⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ⟨s, hs', rfl⟩), ?_⟩
    rw [hg, ← map_inv, ← map_mul, ← map_mul]
    rfl
  obtain ⟨x, hxP, hxc⟩ : ∃ x ∈ P₁, g * x * g⁻¹ ∉ P₁ := by
    by_contra hcon
    push Not at hcon
    apply hkM
    refine C.mem_m1_of hφk (g := ⟨k, hKH hk⟩) ?_
    have hle : P₁.map (MulAut.conj g).toMonoidHom ≤ P₁ := by
      rintro _ ⟨p, hp, rfl⟩
      exact hcon p hp
    have heq : P₁.map (MulAut.conj g).toMonoidHom = P₁ := Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (K := P₁) (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective).symm)
    exact conjSub_eq_self_iff.mp (show conjSub g P₁ = P₁ from heq)
  have hP₁2 : ∀ p ∈ P₁, p ^ 2 = 1 := fun p hp => by
    have h1 : p ^ 4 = 1 := by
      have := Subgroup.orderOf_dvd_natCard P₁ hp
      rw [hP₁4] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    exact perm5_sq_of_pow_four p (Equiv.Perm.mem_alternatingGroup.mp (hMA (hP₁M hp))) h1
  have hx1 : x ≠ 1 := fun h => hxc (by rw [h, mul_one, mul_inv_cancel]; exact one_mem _)
  obtain ⟨b, hbP, hb1, hbx⟩ : ∃ b ∈ P₁, b ≠ 1 ∧ b ≠ x := by
    by_contra hcon
    push Not at hcon
    have hsub : (P₁ : Set (Equiv.Perm (Fin 5))) ⊆ {1, x} := fun p hp => by
      by_cases h : p = 1
      · exact Or.inl h
      · exact Or.inr (hcon p hp h)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h0 : (P₁ : Set (Equiv.Perm (Fin 5))).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hP₁4
    rw [h0] at h1
    have h2 := Set.ncard_insert_le (1 : Equiv.Perm (Fin 5)) ({x} : Set _)
    rw [Set.ncard_singleton] at h2
    omega
  have hdt : ∀ p ∈ P₁, p ≠ 1 → p ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin 5) =>
      σ ^ 2 = 1 ∧ σ ≠ 1 ∧ Equiv.Perm.sign σ = 1) := fun p hp hp1 => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hP₁2 p hp, hp1, Equiv.Perm.mem_alternatingGroup.mp (hMA (hP₁M hp))⟩
  have hcdt : g * x * g⁻¹ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin 5) =>
      σ ^ 2 = 1 ∧ σ ≠ 1 ∧ Equiv.Perm.sign σ = 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by rw [conj_pow, hP₁2 x hxP, mul_one, mul_inv_cancel], fun h => hx1 ?_, ?_⟩
    · calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · rw [map_mul, map_mul, map_inv, Equiv.Perm.mem_alternatingGroup.mp (hMA (hP₁M hxP))]
      group
  have hab := hP₁2 _ (mul_mem hxP hbP)
  obtain ⟨⟨y₅, hy₅, hy₅o, hy₅1⟩, ⟨y₃, hy₃, hy₃o, hy₃1⟩⟩ := perm5_gen_aux x (hdt x hxP hx1)
    b (hdt b hbP hb1) _ hcdt hab (Ne.symm hbx) (fun h => hxc (by rw [h]; exact hxP))
    (fun h => hxc (by rw [h]; exact hbP)) (fun h => hxc (by rw [h]; exact mul_mem hxP hbP))
  have hyP : ∀ y ∈ [x, b, x * b], y ∈ P₁ := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact hxP
    · exact hbP
    · exact mul_mem hxP hbP
  have hcM := hgP x hxP
  have hdvd : ∀ {y : Equiv.Perm (Fin 5)} {n : ℕ}, n.Prime → y ∈ M → y ^ n = 1 → y ≠ 1 →
      n ∣ Nat.card ↥M := fun {y n} hn hyM hyn hy1 => by
    have : Fact n.Prime := ⟨hn⟩
    have h1 := Subgroup.orderOf_dvd_natCard M hyM
    rwa [orderOf_eq_prime hyn hy1] at h1
  have h5 := hdvd Nat.prime_five (mul_mem (hP₁M (hyP _ hy₅)) hcM) hy₅o hy₅1
  have h3 := hdvd Nat.prime_three (mul_mem (hP₁M (hyP _ hy₃)) hcM) hy₃o hy₃1
  have h4' : 4 ∣ Nat.card ↥M := by
    rw [← hP₁4]
    exact Subgroup.card_dvd_of_le hP₁M
  have hA5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h60 : 60 ∣ Nat.card ↥M := by
    have h12 : 12 ∣ Nat.card ↥M :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4' h3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 12 5) h12 h5
  have hMeq : M = alternatingGroup (Fin 5) := Subgroup.eq_of_le_of_card_ge hMA (by
    rw [hA5]
    exact Nat.le_of_dvd Nat.card_pos h60)
  have hO : oTwoUpper (hz T V) ⊓ pCoreOf 2 (hz T V) ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro q hq
    obtain ⟨-, hqQ⟩ := Subgroup.mem_inf.mp hq
    have hqS : q ∈ Subgroup.normalizer (sL T L V : Set G) := hQN hqQ
    have hqSk : q ∈ Subgroup.normalizer (Sk : Set G) := by
      have hq' : k⁻¹ * q * k ∈ pCoreOf 2 (hz T V) := by
        have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pCoreOf 2 (hz T V) (inv_mem (hKH hk))) q).mp hqQ
        simpa using this
      have hq'S := hQN hq'
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [show Sk = conjSub k (sL T L V) from rfl, mem_conjSub, mem_conjSub]
      rw [show k⁻¹ * (q * y * q⁻¹) * k = (k⁻¹ * q * k) * (k⁻¹ * y * k) * (k⁻¹ * q * k)⁻¹ by
        group]
      exact Subgroup.mem_normalizer_iff.mp hq'S _
    rw [← conjSub_eq_self_iff] at hqS hqSk ⊢
    rw [hK₀, conjSub, Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) hqS hqSk
  exact (eq_oTwoUpper_of hφk hK₀K hO (show alternatingGroup (Fin 5) ≤ M from hMeq.ge)).symm

end Ctx73

end CFSG.Quasithin.H13.L32A

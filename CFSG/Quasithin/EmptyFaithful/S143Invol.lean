module

public import CFSG.Quasithin.EmptyFaithful.S143Aux
public import CFSG.Quasithin.EmptyFaithful.S143Struct
public import CFSG.Quasithin.EmptyFaithful.S143Q8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

variable {G : Type} [Group G] [Finite G]

theorem eq_of_two_pow_mul_odd_eq {a b i : ℕ} (hi : ¬ 2 ∣ i) (h : 2 ^ b * i = 2 ^ a * 3) :
    b = a := by
  have hi0 : i ≠ 0 := fun h0 => hi (h0 ▸ dvd_zero 2)
  have h3 : ¬ 2 ∣ 3 := by norm_num
  have hv1 : padicValNat 2 (2 ^ b * i) = b := by
    rw [padicValNat.mul (by positivity) hi0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hi, add_zero]
  have hv2 : padicValNat 2 (2 ^ a * 3) = a := by
    rw [padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd h3, add_zero]
  rw [← hv1, ← hv2, h]

theorem card_sylow_eq_two_mul {P T : Subgroup G} (hT : IsSylowTwoOf T P)
    (e : Nonempty (OTwoQuot P ≃* Equiv.Perm (Fin 3))) :
    Nat.card T = 2 * Nat.card (pCoreOf 2 P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := e
  have hq : Nat.card (OTwoQuot P) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h1 : Nat.card P = Nat.card (OTwoQuot P) * Nat.card (CFSG.Open.pCore 2 ↥P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥P)
  have hOcard : Nat.card (pCoreOf 2 P) = Nat.card (CFSG.Open.pCore 2 ↥P) :=
    Subgroup.card_map_of_injective P.subtype_injective
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥P) 2).exists_card_eq
  obtain ⟨b, hb⟩ := hT.2.1.exists_card_eq
  have h2 : Nat.card (T.subgroupOf P) * (T.subgroupOf P).index = Nat.card P :=
    Subgroup.card_mul_index _
  have h3 : Nat.card (T.subgroupOf P) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
  have hkey : 2 ^ b * (T.subgroupOf P).index = 2 ^ (a + 1) * 3 := by
    rw [← hb, ← h3, h2, h1, hq, ha, pow_succ]
    ring
  have hba := eq_of_two_pow_mul_odd_eq hT.2.2 hkey
  rw [hOcard, ha, hb, hba, pow_succ]
  ring

variable {T M L : Subgroup G}

theorem exists_involution_mem_diff_RU {g : G} {A : Subgroup G} {t : G}
    (hc : Counter T M g) (c18 : Concl14318 T M g A t) (hW : Nat.card (wOf T M) = 16)
    (hidx : (rOf T M ⊔ uOfL22 T M).relIndex T = 2) :
    ∃ t ∈ T, t ∉ rOf T M ⊔ uOfL22 T M ∧ orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1281 := hc.h1281
  set L := yOfL22 T M with hL
  set R := rOf T M with hR
  set U := uOfL22 T M with hU
  set I₂ := iTwo T M with hI₂
  set P : Subgroup G := L ⊔ T with hP
  set N : Subgroup G := pCoreOf 2 P with hN
  have hTM : T ≤ M := hc.hyp.m_max.1.2
  have hLM : L ≤ M := yOfL22_le T M
  have hPM : P ≤ M := sup_le hLM hTM
  have hUT : U ≤ T := uOfL22_le_T_of_hyp h1281
  have hUI : U ≤ I₂ := le_conjClosure _ _
  have hI₂P : I₂ ≤ P := by
    refine conjClosure_le fun l hl u hu => ?_
    exact P.mul_mem (P.mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right (hUT hu)))
      (P.inv_mem (Subgroup.mem_sup_left hl))
  have hRnorm : M ≤ Subgroup.normalizer (R : Set G) :=
    (normal_i2_of_hyp h1281).trans (normalizer_le_normalizer_pCoreOf 2 I₂)
  have hRI : R ≤ I₂ := pCoreOf_le 2 I₂
  have hRN : R ≤ N := le_pCoreOf_of_le_normalizer 2 (hRI.trans hI₂P)
    (fun x hx => hRnorm (hPM hx)) (pCoreOf_isPGroup 2 I₂)
  have hsyl : IsSylowTwoOf T P := sylow_LT_of_hyp h1281
  have hNT : N ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hcardT : Nat.card T = 2 * Nat.card N := card_sylow_eq_two_mul hsyl h1281.sThree
  have hRT : R ≤ T := le_sup_left.trans (rq_le_of_hyp h1281)
  have hRUT : R ⊔ U ≤ T := sup_le hRT hUT
  have hUR : U ≤ Subgroup.normalizer (R : Set G) := hUT.trans (hTM.trans hRnorm)
  have hcent : I₂ ⊓ Subgroup.centralizer (VZ T M : Set G) = R := c18.a.i2_cent
  have hRU : R ⊓ U = wOf T M := by
    rw [← hcent]
    ext x
    simp only [wOf, Subgroup.mem_inf]
    exact ⟨fun ⟨⟨_, hxC⟩, hxU⟩ => ⟨hxU, hxC⟩, fun ⟨hxU, hxC⟩ => ⟨⟨hUI hxU, hxC⟩, hxU⟩⟩
  have hprod := card_sup_mul_card_inf_of_le_normalizer hUR
  rw [hRU, hW, c18.b.card_R, hc.c15.q8sq.1] at hprod
  have hRUcard : Nat.card ↥(R ⊔ U) = 128 := by omega
  have hTcard : Nat.card T = 256 := by
    have := Subgroup.relIndex_mul_card (R ⊔ U) T
    rw [hidx, inf_eq_left.mpr hRUT, hRUcard] at this
    omega
  have hNcard : Nat.card N = 128 := by omega
  have hRNidx : R.relIndex N = 2 := by
    have := Subgroup.relIndex_mul_card R N
    rw [inf_eq_left.mpr hRN, c18.b.card_R, hNcard] at this
    omega
  obtain ⟨x, hxI, hx3⟩ : ∃ x ∈ I₂, orderOf x = 3 := by
    obtain ⟨e⟩ := c18.a.i2_sThree
    have hq : Nat.card (OTwoQuot I₂) = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have h1 : Nat.card I₂ = Nat.card (OTwoQuot I₂) * Nat.card (CFSG.Open.pCore 2 ↥I₂) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥I₂)
    have hdvd : 3 ∣ Nat.card I₂ := by rw [h1, hq]; exact Dvd.dvd.mul_right (by norm_num) _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := I₂) 3 hdvd
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I₂ hxI) r).mp hr
  have hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P (hI₂P hxI)) n).mp hn
  have hNU : N ⊓ U ≤ R := by
    rintro u ⟨huN, huU⟩
    have huC : u ∈ Subgroup.centralizer (VZ T M : Set G) := by
      have : u ∈ P ⊓ Subgroup.centralizer (VZ T M : Set G) := by
        rw [h1281.centralizer]; exact huN
      exact this.2
    rw [← hcent]
    exact ⟨hUI huU, huC⟩
  obtain ⟨c, hcN, hcRU, hc2⟩ := exists_involution_mem_diff_sup hRN hRNidx hx3' hxR hxN
    (c18.a.r_fpf x hxI hx3) (by rw [c18.b.card_R]; norm_num) hUR hNU
  exact ⟨c, hNT hcN, hcRU, hc2⟩

theorem card_wOf {g : G} (hc : Counter T M g) : Nat.card (wOf T M) = 16 := by
  have h := hc.h1281
  have hq8 := hc.c15.q8sq
  obtain ⟨hVred, -⟩ := h.isTwoReducedIn
  have hVel := hVred.2.2.1
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.omegaOneCenter_ne_bot
    exact ⟨z, z.2, fun h => hz (Subtype.ext h)⟩
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ uOfL22 T M := le_conjClosure _ _
  have hzV : z ∈ VZ T M := hZV hzZ
  obtain ⟨v, hvV, hvZ⟩ : ∃ v ∈ VZ T M, v ∉ quasithinOmegaOneCenter T := by
    by_contra hall
    push Not at hall
    have h1 : VZ T M = quasithinOmegaOneCenter T := le_antisymm hall hZV
    have h2 := h.rank_two
    rw [h1, h.card_omegaOneCenter] at h2
    omega
  have hVH : VZ T M ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun z' hz' => by
      have := congrArg Subtype.val (hVel.1.is_comm.comm ⟨z', hZV hz'⟩ ⟨w, hw⟩)
      simpa using this
  have hUH : uOfL22 T M ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    conjClosure_le fun x hx w hw => by
      have hx' : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := hx
      exact (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)).mul_mem
        ((Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)).mul_mem hx' (hVH hw))
        ((Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)).inv_mem hx')
  have hZcenter : quasithinOmegaOneCenter T ≤ centerOf (uOfL22 T M) := fun z' hz' =>
    ⟨hVU (hZV hz'), Subgroup.mem_centralizer_iff.mpr fun u hu =>
      ((Subgroup.mem_centralizer_iff.mp (hUH hu)) z' hz').symm⟩
  have hcenter : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T :=
    (Subgroup.eq_of_le_of_card_ge hZcenter (by
      rw [isQ8Sq_card_centerOf hq8, h.card_omegaOneCenter])).symm
  have hvc : v ∉ centerOf (uOfL22 T M) := by rw [hcenter]; exact hvZ
  have hv1 : v ≠ 1 := fun h1 => hvZ (h1 ▸ (quasithinOmegaOneCenter T).one_mem)
  have hz2 : z * z = 1 := by
    have := hVel.2 z hzV
    rwa [pow_two] at this
  have hW : wOf T M = uOfL22 T M ⊓ Subgroup.centralizer ({v} : Set G) := by
    ext x
    simp only [wOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
    refine ⟨fun ⟨hxU, hxC⟩ => ⟨hxU, hxC v hvV⟩, fun ⟨hxU, hxv⟩ => ⟨hxU, fun w hw => ?_⟩⟩
    have hxz : ∀ z' ∈ quasithinOmegaOneCenter T, z' * x = x * z' := fun z' hz' =>
      (Subgroup.mem_centralizer_iff.mp (hUH hxU)) z' hz'
    have hcases := eq_or_eq_or_eq_or_eq_of_card_four h.rank_two (a := (1 : VZ T M))
      (b := ⟨z, hzV⟩) (c := ⟨v, hvV⟩) (d := ⟨z * v, (VZ T M).mul_mem hzV hvV⟩)
      (fun he => hz1 (congrArg Subtype.val he).symm)
      (fun he => hv1 (congrArg Subtype.val he).symm)
      (fun he => hvZ (by
        have : z * v = 1 := (congrArg Subtype.val he).symm
        have hzv : v = z := by
          have := eq_inv_of_mul_eq_one_right this
          rw [this]; exact inv_eq_of_mul_eq_one_right hz2
        rw [hzv]; exact hzZ))
      (fun he => hvZ (by
        have := congrArg Subtype.val he
        simp only at this
        rw [← this]; exact hzZ))
      (fun he => hv1 (by
        have := congrArg Subtype.val he
        simpa using this))
      (fun he => hz1 (by
        have := congrArg Subtype.val he
        simpa using this.symm)) ⟨w, hw⟩
    rcases hcases with he | he | he | he
    · have := congrArg Subtype.val he
      simp only at this
      rw [this]; simp
    · have := congrArg Subtype.val he
      simp only at this
      rw [this]; exact hxz z hzZ
    · have := congrArg Subtype.val he
      simp only at this
      rw [this]; exact hxv
    · have := congrArg Subtype.val he
      simp only at this
      rw [this]
      calc z * v * x = z * (v * x) := mul_assoc _ _ _
        _ = z * (x * v) := by rw [hxv]
        _ = (z * x) * v := (mul_assoc _ _ _).symm
        _ = (x * z) * v := by rw [hxz z hzZ]
        _ = x * (z * v) := mul_assoc _ _ _
  rw [hW]
  exact isQ8Sq_card_centralizer hq8 v (hVU hvV) hvc

end S143

open S143 in
theorem lemma_14_3_21_one :
    ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
      Counter T M g → Concl14318 T M g A t → Concl14319 T M A →
        Subgroup.centralizer (A : Set G) = A →
          ((rOf T M ⊔ uOfL22 T M).relIndex T = 2 →
            ∃ t ∈ T, t ∉ rOf T M ⊔ uOfL22 T M ∧ orderOf t = 2) := by
  intro G _ _ T M g A t hc c18 _ _ hidx
  exact exists_involution_mem_diff_RU hc c18 (card_wOf hc) hidx

end CFSG.Quasithin

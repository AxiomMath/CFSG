module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

omit [Finite G] in
theorem le_mcOf_self (T : Subgroup G) : T ≤ mcOf T := fun t ht =>
  Subgroup.mem_centralizer_iff.mpr fun _ hz =>
    ((Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hz).2.1 t ht)).symm

theorem divisors_4608_cases : ∀ n ∈ Nat.divisors 4608, 2 ^ 7 ∣ n → ¬ 2 ^ 8 ∣ n → 3 ∣ n →
    ¬ 9 ∣ n → n = 384 := by decide +kernel

theorem card_Cw_eq (h : Ctx T M g A t d x) : Nat.card ↥(Cw T d x) = 384 := by
  have hTH : T ≤ mcOf T := le_mcOf_self T
  have hTwC : Tw T d x ≤ Cw T d x := inf_le_inf_right _ hTH
  have hCG : Cw T d x ≤ Gw d x := inf_le_right
  have hCH : Cw T d x ≤ mcOf T := inf_le_left
  have h48 : Nat.card ↥(K0 T d x) = 48 := h.hO.1
  have hdvdH : Nat.card ↥(Cw T d x) ∣ 4608 := by
    rw [← card_mcOf h]; exact Subgroup.card_dvd_of_le hCH
  have h2 : 2 ^ 7 ∣ Nat.card ↥(Cw T d x) := by
    have := Subgroup.card_dvd_of_le hTwC
    rwa [card_Tw_eq h] at this
  have h2' : ¬ 2 ^ 8 ∣ Nat.card ↥(Cw T d x) := by
    intro hdv
    obtain ⟨hSle, -, hodd⟩ := h.hSyl
    have hG := card_eq_card_mul_relIndex hSle
    have hCdvd : Nat.card ↥(Cw T d x) ∣ Nat.card ↥(Gw d x) := Subgroup.card_dvd_of_le hCG
    have hTc : Nat.card ↥(T ⊓ Gw d x) = 2 ^ 7 := card_Tw_eq h
    rw [hTc] at hG
    have hdvd8 : 2 ^ 7 * 2 ∣ 2 ^ 7 * (T ⊓ Gw d x).relIndex (Gw d x) := by
      rw [← hG]; simpa [pow_succ] using hdv.trans hCdvd
    exact hodd ((Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2 ^ 7)).mp hdvd8)
  have h3 : 3 ∣ Nat.card ↥(Cw T d x) := by
    have := Subgroup.card_dvd_of_le (inf_le_inf_right (Gw d x) (oTwoUpper_le (mcOf T)) :
      K0 T d x ≤ Cw T d x)
    rw [h48] at this
    exact (by norm_num : 3 ∣ 48).trans this
  have h9 : ¬ 9 ∣ Nat.card ↥(Cw T d x) := by
    intro hdv
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(Cw T d x)) 3
      (n := 2) (by simpa using hdv)
    have hKle : K.map (Cw T d x).subtype ≤ K0 T d x := by
      rintro _ ⟨k, hk, rfl⟩
      have hodd : Odd (orderOf (k : G)) := by
        rw [Subgroup.orderOf_coe]
        have hd : orderOf k ∣ 3 ^ 2 := hK ▸ Subgroup.orderOf_dvd_natCard K hk
        exact Odd.of_dvd_nat (by decide) hd
      exact ⟨mem_oTwoUpper_of_odd (hCH k.2) hodd, hCG k.2⟩
    have := Subgroup.card_dvd_of_le hKle
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK, h48] at this
    revert this; norm_num
  exact divisors_4608_cases _ (Nat.mem_divisors.mpr ⟨hdvdH, by norm_num⟩) h2 h2' h3 h9

omit [Finite G] in
theorem K0_normal_of_ctx (T : Subgroup G) (d x : G) :
    ((K0 T d x).subgroupOf (Cw T d x)).Normal := by
  refine ⟨fun n hn g' => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  refine ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper (mcOf T) g'.2.1) n).mp hn.1
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g'.2.2 hn.2) (Subgroup.inv_mem _ g'.2.2)

theorem sq_mem_K0 (h : Ctx T M g A t d x) : d * d ∈ K0 T d x := by
  have hzZ := sq_mem_omegaOneCenter h.c h.hD h.hd4
  have hzU : d * d ∈ uOfL22 T M :=
    Hyp1281Two.VZ_le_uOfL22 T M (Hyp1281Two.omegaOneCenter_le_VZ T M hzZ)
  have hzw : (d * d) * wOfX d x = wOfX d x * (d * d) := by
    have hd : d ∈ dOf T M := h.hD ▸ Subgroup.mem_zpowers d
    have hzX : d * d ∈ Xgen T M := (Xgen T M).mul_mem (le_Wgen (dOf_mem_delta h.c) hd)
      (le_Wgen (dOf_mem_delta h.c) hd)
    exact Xgen_comm h.c h.hD h.hd4 _ hzX _ (wOfX_mem_Xgen h.c h.hD h.hx)
  refine ⟨uOfL22_le_oTwoUpper h.c hzU, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact hzw.symm

theorem K0_contains_z_of_ctx (h : Ctx T M g A t d x) :
    ∀ N : Subgroup G, N ≤ K0 T d x → (N.subgroupOf (K0 T d x)).Normal → N ≠ ⊥ →
      d * d ∈ N := by
  intro N hNK hNn hN1
  have hzZ := sq_mem_omegaOneCenter h.c h.hD h.hd4
  have hdd := dd_facts h.hd4
  have hzK := sq_mem_K0 h
  have hbot : N.subgroupOf (K0 T d x) ≠ ⊥ := by
    intro hb
    apply hN1
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have h1 : (⟨n, hNK hn⟩ : ↥(K0 T d x)) ∈ N.subgroupOf (K0 T d x) :=
      Subgroup.mem_subgroupOf.mpr hn
    rw [hb, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have := z4StarSL23_normal_contains h.hO (z := (⟨d * d, hzK⟩ : ↥(K0 T d x)))
    (Subtype.ext hdd.1) (fun hh => hdd.2 (congrArg Subtype.val hh))
    (fun g' => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (oTwoUpper_le _ g'.2.1) (d * d) hzZ).symm) hNn hbot
  exact Subgroup.mem_subgroupOf.mp this

end InspW2

end S143

end CFSG.Quasithin

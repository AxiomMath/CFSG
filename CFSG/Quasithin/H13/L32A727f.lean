module

public import CFSG.Quasithin.H13.L32A727c

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_sup_of_normal {X : Type*} [Group X] {K A : Subgroup X} (hK : K.Normal)
    {k : X} (hk : k ∈ K) : k ∈ Subgroup.normalizer ((K ⊔ A : Subgroup X) : Set X) := by
  have key : ∀ c ∈ K, ∀ x ∈ K ⊔ A, c * x * c⁻¹ ∈ K ⊔ A := fun c hc x hx => by
    have h1 : c * (x * c⁻¹ * x⁻¹) ∈ K := K.mul_mem hc (hK.conj_mem _ (K.inv_mem hc) x)
    have e : c * x * c⁻¹ = c * (x * c⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact (K ⊔ A).mul_mem (Subgroup.mem_sup_left h1) hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key k hk x, fun hx => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hx
  simpa [mul_assoc] using this

theorem not_isPGroup_l1_star (S : Setting147 G T L V H) (h1332 : Stmt13_3_2)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hKn : K.Normal) (hK : IsPGroup 3 ↥K)
    (hHe : H = pre H K ⊔ (l1 T L V ⊔ T))
    (hLP : ¬ modO2Image H (l1 T L V) ≤ CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) :
    ¬ IsPGroup 3 ↥(modO2Image H (l1 T L V)) := by
  intro hL3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L1s := modO2Image H (l1 T L V) with hL1s
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hKN : ∀ x : ↥H ⧸ CFSG.pCore 2 ↥H, x ∈ Subgroup.normalizer (K : Set _) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hKn.conj_mem k hk x, fun hk => by
        have := hKn.conj_mem _ hk x⁻¹
        convert this using 1
        group⟩
  have hN3 : IsPGroup 3 ↥(K ⊔ L1s) := by
    have hc := TJ1.card_sup_mul_card_inf (X := L1s) (N := K) (fun l _ => hKN l)
    obtain ⟨a, ha⟩ := hL3.exists_card_eq
    obtain ⟨b, hb⟩ := hK.exists_card_eq
    rw [ha, hb, ← pow_add, sup_comm] at hc
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (Dvd.intro _ hc)
    exact IsPGroup.of_card hi
  have hTL1 : modO2Image H T ≤ Subgroup.normalizer (L1s : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_le_normalizer' (Setting147.T_le_N_l1 S h1332)
  have hNn : (K ⊔ L1s).Normal := by
    have htop : (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
        Subgroup.normalizer ((K ⊔ L1s : Subgroup _) : Set _) := by
      have e := congrArg (modO2Image H) hHe
      rw [modO2Image_self, modO2Image_sup (pre_le K) (sup_le hl1H hTH),
        modO2Image_sup hl1H hTH, modO2Image_pre] at e
      rw [e]
      refine sup_le (fun k hk => mem_normalizer_sup_of_normal hKn hk) (sup_le ?_ ?_)
      · exact fun l hl => mem_normalizer_sup (hKN l) (Subgroup.le_normalizer hl)
      · exact fun t ht => mem_normalizer_sup (hKN t) (hTL1 ht)
    exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr htop)
  exact hLP (le_sup_right.trans (le_sSup ⟨hNn, hN3⟩))

theorem exists_involution_l1_star (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hL3 : ¬ IsPGroup 3 ↥(modO2Image H (l1 T L V))) :
    ∃ j ∈ modO2Image H (l1 T L V), orderOf j = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L1s := modO2Image H (l1 T L V) with hL1s
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hdvd : Nat.card ↥L1s ∣ Nat.card ↥(l1 T L V) := by
    have h1 := Subgroup.card_map_dvd ((l1 T L V).subgroupOf H)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hl1H).toEquiv] at h1
  have hidx := (M76.relIndex_l1_T S h1222 h1332 h1334).1
  have hcard : Nat.card ↥(l1 T L V) = 3 * Nat.card ↥(pCoreOf 2 (l1 T L V)) := by
    have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 (l1 T L V)) (K := l1 T L V)
    rw [inf_eq_left.mpr (pCoreOf_le 2 (l1 T L V)), hidx] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 (l1 T L V)).exists_card_eq
  rw [hcard, ha] at hdvd
  by_contra hno
  apply hL3
  rintro ⟨x, hx⟩
  have hxd : orderOf x ∣ 3 * 2 ^ a := (Subgroup.orderOf_dvd_natCard L1s hx).trans hdvd
  have hodd : ¬ 2 ∣ orderOf x := by
    intro h2
    apply hno
    refine ⟨x ^ (orderOf x / 2), L1s.pow_mem hx _, ?_⟩
    rw [orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos x) h2) (by norm_num)).ne'
      (Nat.div_dvd_of_dvd h2), Nat.div_div_self h2 (orderOf_pos x).ne']
  have h3 : orderOf x ∣ 3 := by
    have hcop : Nat.Coprime (orderOf x) (2 ^ a) :=
      Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    exact hcop.dvd_of_dvd_mul_right hxd
  refine ⟨1, Subtype.ext ?_⟩
  simpa using orderOf_dvd_iff_pow_eq_one.mp h3

end CFSG.Quasithin.H13.L32A.R727

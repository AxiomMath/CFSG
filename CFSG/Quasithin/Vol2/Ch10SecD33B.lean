module

public import CFSG.Quasithin.Vol2.Ch10SecD33A
public import CFSG.Quasithin.Vol2.Ch10SecDFacts33
public import CFSG.Quasithin.Vol2.Ch10SecD32A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem not_isMaxSubgroupIn_of_le_T1 (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) {N : Subgroup G}
    (hN : N ≤ T1 T L) (hNL : N ≤ L) : ¬ IsMaxSubgroupIn L N := by
  rintro ⟨-, hmax⟩
  obtain ⟨-, -, hv1, hv11, -, -⟩ := hd
  have hNC : N ≤ L ⊓ Subgroup.centralizer ({v₁} : Set G) := fun n hn =>
    ⟨hNL hn, Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hv1.2) n (hN hn))⟩
  obtain ⟨l, hlL, hlo, hlv, hlC⟩ := exists_odd_mem_centralizer h3 hc hv1.1 hv11
  have hlK : l ∈ L ⊓ Subgroup.centralizer ({v₁} : Set G) := by
    refine ⟨hlL, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc l * v₁ = l * v₁ * l⁻¹ * l := by group
      _ = v₁ * l := by rw [hlv]
  have hlN : l ∉ N := by
    intro hlN
    apply hlC
    obtain ⟨k, hk⟩ := h.fsu.sylow.1 ⟨l, (hN hlN).1⟩
    have hk' : l ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf l ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hodd := hlo
    rw [hj] at hodd
    have hj0 : j = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hne).mpr even_two)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    rw [hj]
    exact Subgroup.one_mem _
  have hlt : N < L ⊓ Subgroup.centralizer ({v₁} : Set G) :=
    lt_of_le_of_ne hNC fun heq => hlN (heq ▸ hlK)
  have hKL := hmax _ hlt inf_le_left
  obtain ⟨w, hw, hw1, hwv⟩ : ∃ w ∈ fsuUL T L I, w ≠ 1 ∧ w ≠ v₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : (fsuUL T L I : Set G) ⊆ {1, v₁} := fun w hw => by
      by_cases hw1 : w = 1
      · exact Or.inl hw1
      · exact Or.inr (hcon w hw hw1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair (Ne.symm hv11), ← Nat.card_coe_set_eq] at h1
    have h8 : Nat.card ↥(fsuUL T L I) = 8 := card_V1 h3 hc
    have h8' : Nat.card ↥(fsuUL T L I : Set G) = 8 := h8
    omega
  obtain ⟨l', hl'L, hl'v⟩ := exists_conj_eq_of_mem_V1 h3 hc hv1.1 hw hv11 hw1
  have hl'K : l' ∈ L ⊓ Subgroup.centralizer ({v₁} : Set G) := by
    rw [hKL]
    exact hl'L
  have := Subgroup.mem_centralizer_singleton_iff.mp hl'K.2
  apply hwv
  rw [← hl'v, this]
  group

theorem exists_odd_mem_inf_fsuM (h1023 : Stmt10_2_3) (h10213 : Stmt10_2_13) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) :
    ∃ y ∈ H ⊓ fsuM T L, Odd (orderOf y) ∧ y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : oTwoUpper (H ⊓ fsuM T L) = ⊥ := by
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    exact hcon y hy.1 hy.2
  have hn := (h10213 G T L I h).2.2 H hH
  obtain ⟨-, -, h3', -⟩ := h1023 G T L I h H hH (by rw [hn]; norm_num)
  obtain ⟨-, hmaxpar, -⟩ := h3' h3.1
  have hM := hmaxpar L (Or.inl rfl)
  rw [hbot, sup_bot_eq] at hM
  exact not_isMaxSubgroupIn_of_le_T1 h h3 hc hd
    (inf_le_left.trans (SecA.T0_le_T1 h.fsu.maximal.1)) inf_le_right hM

theorem forall_odd_mem_of_normal (hW : FactSymFiveWrTwo) {H N : Subgroup G}
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) (hNH : N ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) {y : G} (hyN : y ∈ N) (hyo : Odd (orderOf y))
    (hy1 : y ≠ 1) {x : G} (hx : x ∈ H) (hxo : Odd (orderOf x)) : x ∈ N := by
  set P := CFSG.pCore 2 ↥H with hP
  have hNn : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have hN'n : (((N.subgroupOf H).map (QuotientGroup.mk' P)).map e.toMonoidHom).Normal :=
    (hNn.map _ (QuotientGroup.mk'_surjective P)).map e.toMonoidHom e.surjective
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hodd_notin : ∀ w : ↥H, Odd (orderOf (w : G)) → w ∈ P → w = 1 := by
    intro w hwo hwP
    obtain ⟨k, hk⟩ := hP2 ⟨w, hwP⟩
    have hk' : (w : G) ^ 2 ^ k = 1 := by
      simpa using congrArg (fun u : ↥P => ((u : ↥H) : G)) hk
    have hdvd : orderOf (w : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hodd := hwo
    rw [hj] at hodd
    have hj0 : j = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hne).mpr even_two)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact Subtype.ext hj
  have hN'ne : ((N.subgroupOf H).map (QuotientGroup.mk' P)).map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    have hmem : e (QuotientGroup.mk' P ⟨y, hNH hyN⟩) ∈
        ((N.subgroupOf H).map (QuotientGroup.mk' P)).map e.toMonoidHom :=
      ⟨_, ⟨⟨y, hNH hyN⟩, Subgroup.mem_subgroupOf.mpr hyN, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hmem
    exact hy1 (congrArg Subtype.val (hodd_notin ⟨y, hNH hyN⟩ hyo hmem))
  have hxW : e (QuotientGroup.mk' P ⟨x, hx⟩) ∈
      ((N.subgroupOf H).map (QuotientGroup.mk' P)).map e.toMonoidHom := by
    refine hW.1 _ hN'n hN'ne (mem_oTwoUpper_of_odd trivial ?_)
    have h1 := MulEquiv.orderOf_eq e (QuotientGroup.mk' P ⟨x, hx⟩)
    have h2 := orderOf_map_dvd (QuotientGroup.mk' P) (⟨x, hx⟩ : ↥H)
    rw [Subgroup.orderOf_mk] at h2
    rw [h1]
    exact Odd.of_dvd_nat hxo h2
  obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp hxW
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hq
  have hq' : QuotientGroup.mk' P n = QuotientGroup.mk' P ⟨x, hx⟩ := e.injective hqe
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hq'
  have hxsup : x ∈ N ⊔ pCoreOf 2 H := by
    have e1 : x = (n : G) * ((n⁻¹ * ⟨x, hx⟩ : ↥H) : G) := by simp
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hn))
      (Subgroup.mem_sup_right ⟨n⁻¹ * ⟨x, hx⟩,
        hq', rfl⟩)
  exact mem_of_odd_of_mem_sup ((Subgroup.map_subtype_le _).trans hHN)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hxsup hxo

theorem oTwoUpper_le_Kz (hW : FactSymFiveWrTwo) (h1023 : Stmt10_2_3) (h10213 : Stmt10_2_13)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hHz : H ≤ Subgroup.centralizer ({v₁ * v₂} : Set G)) :
    oTwoUpper H ≤ Kz T L (v₁ * v₂) := by
  have hn := (h10213 G T L I h).2.2 H hH
  obtain ⟨-, -, h3', -⟩ := h1023 G T L I h H hH (by rw [hn]; norm_num)
  obtain ⟨hO2L0, -, ⟨e⟩⟩ := h3' h3.1
  obtain ⟨y, hy, hyo, hy1⟩ := exists_odd_mem_inf_fsuM h1023 h10213 h h3 hc hd hH
  have hyX : y ∈ Xz T L (v₁ * v₂) :=
    mem_oTwoUpper_of_odd ⟨hO2L0 (mem_oTwoUpper_of_odd hy hyo), hHz hy.1⟩ hyo
  have hyK : y ∈ Kz T L (v₁ * v₂) := le_conjClosure _ _ hyX
  have hKzN : H ≤ Subgroup.normalizer ((Kz T L (v₁ * v₂) ⊓ H : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf (le_normalizer_conjClosure _ _ (hHz hx))
      (Subgroup.le_normalizer hx)
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact (forall_odd_mem_of_normal hW e inf_le_right hKzN ⟨hyK, hy.1⟩ hyo hy1 hx.1 hx.2).1

theorem oTwoUpper_sup_eq {T H : Subgroup G} (hT : IsSylowTwoOf T H) : oTwoUpper H ⊔ T = H := by
  refine le_antisymm (sup_le (oTwoUpper_le H) hT.1) ?_
  have h1 : (oTwoUpper H ⊔ T).relIndex H ∣ T.relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_right
  have h2 : (oTwoUpper H ⊔ T).relIndex H ∣ (oTwoUpper H).relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_left
  obtain ⟨k, hk⟩ := exists_relIndex_oTwoUpper_eq_two_pow (le_refl H)
  rw [inf_eq_right.mpr (oTwoUpper_le H)] at hk
  rw [hk] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hj0 : j = 0 := by
    by_contra hne
    exact hT.2.2 ((dvd_pow_self 2 hne).trans (hj ▸ h1))
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.mp hj

theorem not_Kz_le_fsuM (hW : FactSymFiveWrTwo) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1023 : Stmt10_2_3) (h10213 : Stmt10_2_13)
    (h1032 : Stmt10_3_2) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) :
    ¬ Kz T L (v₁ * v₂) ≤ fsuM T L := by
  intro hKM
  obtain ⟨H, hH, hHz⟩ := exists_isHStar_le_centralizer h37 h38 h1032 h h3 hc hd
  apply hH.2.1
  have hO := (oTwoUpper_le_Kz hW h1023 h10213 h h3 hc hd hH hHz).trans hKM
  rw [← oTwoUpper_sup_eq (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hH.1.1)]
  exact sup_le hO (SecA.le_fsuM T L)

end CFSG.Quasithin.Vol2.Ch10.SecD

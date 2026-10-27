module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoAssemble
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeavesCent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4CoverCert
public import CFSG.Quasithin.Vol2.Ch12Sec6L12R1Defs
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoFam

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint Subgroup

section Setup

variable {G : Type} [Group G] [Finite G] {K L E : Subgroup G}

theorem Setup.imageT0_facts (S : Setup K L E) {T T₀ : Subgroup G}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T K) (hT₀ : T₀ ≤ T)
    (hT₀N : T₀ ≤ Subgroup.normalizer (L : Set G)) (hidx : T₀.relIndex T ≤ 2) {a : ℕ}
    (ha : 2 ^ (a + 1) ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) :
    IsPGroup 2 ↥((T₀.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) ∧
      (T₀.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) ≤
        Subgroup.normalizer (((L.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) :
          Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set (↥K ⧸ Subgroup.center ↥K)) ∧
      2 ^ a ≤ Nat.card ↥((T₀.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) := by
  set mk := QuotientGroup.mk' (Subgroup.center ↥K) with hmk
  set TK : Subgroup ↥K := T.subgroupOf K with hTK
  set T₀K : Subgroup ↥K := T₀.subgroupOf K with hT₀K
  set Q : Subgroup (↥K ⧸ Subgroup.center ↥K) := TK.map mk with hQ
  set P : Subgroup (↥K ⧸ Subgroup.center ↥K) := T₀K.map mk with hP
  have hQidx : ¬ 2 ∣ Q.index := by
    intro h2
    have h1 : Q.index ∣ TK.index :=
      Subgroup.index_map_dvd TK (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
    exact hT.2.2 (h2.trans h1)
  have hQa : 2 ^ (a + 1) ∣ Nat.card ↥Q := by
    have hmul : Nat.card ↥Q * Q.index = Nat.card (↥K ⧸ Subgroup.center ↥K) :=
      Subgroup.card_mul_index Q
    have hodd : Odd Q.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hQidx)
    have hcop : Nat.Coprime (2 ^ (a + 1)) Q.index :=
      Nat.Coprime.pow_left (a + 1) (Nat.coprime_two_left.mpr hodd)
    have hd : 2 ^ (a + 1) ∣ Nat.card ↥Q * Q.index := by
      rw [hmul]
      exact ha
    exact hcop.dvd_of_dvd_mul_right hd
  have hQcard := card_map_mk_mul_card_inf (K := K) TK
  have hPcard := card_map_mk_mul_card_inf (K := K) T₀K
  have hTKcard : Nat.card ↥TK = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
  have hT₀Kcard : Nat.card ↥T₀K = Nat.card ↥T₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hT₀.trans hT.1)).toEquiv
  have hrel : Nat.card ↥T = T₀.relIndex T * Nat.card ↥T₀ := by
    have := Subgroup.relIndex_mul_card (H := T₀) (K := T)
    rw [inf_eq_left.mpr hT₀] at this
    rw [← this, mul_comm]
  have hsub : Nat.card ↥(T₀K ⊓ Subgroup.center ↥K) ≤ Nat.card ↥(TK ⊓ Subgroup.center ↥K) := by
    apply Subgroup.card_le_of_le
    apply inf_le_inf_right
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hT₀ (Subgroup.mem_subgroupOf.mp hx))
  have hQpos : 0 < Nat.card ↥(TK ⊓ Subgroup.center ↥K) := Nat.card_pos
  have hQle : Nat.card ↥Q ≤ 2 * Nat.card ↥P := by
    have key : Nat.card ↥Q * Nat.card ↥(TK ⊓ Subgroup.center ↥K) ≤
        (2 * Nat.card ↥P) * Nat.card ↥(TK ⊓ Subgroup.center ↥K) := by
      calc Nat.card ↥Q * Nat.card ↥(TK ⊓ Subgroup.center ↥K) = Nat.card ↥TK := hQcard
        _ = Nat.card ↥T := hTKcard
        _ = T₀.relIndex T * Nat.card ↥T₀ := hrel
        _ = T₀.relIndex T * (Nat.card ↥P * Nat.card ↥(T₀K ⊓ Subgroup.center ↥K)) := by
          rw [hPcard, hT₀Kcard]
        _ ≤ 2 * (Nat.card ↥P * Nat.card ↥(TK ⊓ Subgroup.center ↥K)) :=
          Nat.mul_le_mul hidx (Nat.mul_le_mul_left _ hsub)
        _ = (2 * Nat.card ↥P) * Nat.card ↥(TK ⊓ Subgroup.center ↥K) := by ring
    exact Nat.le_of_mul_le_mul_right key hQpos
  have hPa : 2 ^ a ≤ Nat.card ↥P := by
    have h1 : 2 ^ (a + 1) ≤ Nat.card ↥Q := Nat.le_of_dvd Nat.card_pos hQa
    have h2 : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ, mul_comm]
    omega
  have hPp : IsPGroup 2 ↥P := by
    intro x
    obtain ⟨t, ht, hx⟩ := Subgroup.mem_map.mp x.2
    have htT : (t : G) ∈ T := hT₀ (Subgroup.mem_subgroupOf.mp ht)
    obtain ⟨k, hk⟩ := hT.2.1 ⟨(t : G), htT⟩
    have hk' : (t : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have htk : t ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx, ← map_pow, htk, map_one]
  have hPN : P ≤ Subgroup.normalizer
      (((L.subgroupOf K).map mk : Subgroup (↥K ⧸ Subgroup.center ↥K)) :
        Set (↥K ⧸ Subgroup.center ↥K)) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    exact mk_mem_normalizer_map S.hLK t (hT₀N (Subgroup.mem_subgroupOf.mp ht))
  exact ⟨hPp, hPN, hPa⟩

theorem Setup.exists_A6TypeCent (S : Setup K L E)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥K))) :
    ∃ u, A6TypeCent ((L.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) u := by
  have hY := S.config
  have hC2 : Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) = 2 := S.hC
  have hnt : Nontrivial ↥(E ⊓ Subgroup.centralizer (L : Set G)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hC2]; norm_num)
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥(E ⊓ Subgroup.centralizer (L : Set G)))
  have hxE : (x : G) ∈ E := (Subgroup.mem_inf.mp x.2).1
  have hxC : (x : G) ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp x.2).2
  have hxL : (x : G) ∈ L := pCoreOf_le_self L (S.hE hxE)
  have hx2 : (x : G) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥(E ⊓ Subgroup.centralizer (L : Set G))) (x := x)
    rw [hC2] at this
    exact congrArg Subtype.val this
  have hxne : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  set k : ↥K := ⟨(x : G), S.le_K hxE⟩ with hk
  have hk2 : k ^ 2 = 1 := Subtype.ext (by simpa [hk] using hx2)
  have hk1 : k ≠ 1 := fun h => hxne (by simpa [hk] using congrArg Subtype.val h)
  have hko : orderOf k = 2 := orderOf_eq_prime hk2 hk1
  refine ⟨QuotientGroup.mk' (Subgroup.center ↥K) k, hY.1, hY.2.1, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨k, Subgroup.mem_subgroupOf.mpr hxL, rfl⟩
  · refine orderOf_eq_prime (by rw [← map_pow, hk2, map_one]) ?_
    intro h
    have hkZ : k ∈ Subgroup.center ↥K := (QuotientGroup.eq_one_iff k).mp h
    have hd : orderOf k ∣ Nat.card ↥(Subgroup.center ↥K) := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hkZ
      exact this
    rw [hko] at hd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  · intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hcomm : (l : G) * x = x * l := Subgroup.mem_centralizer_iff.mp hxC (l : G) hlL
    have hkl : k * l = l * k := Subtype.ext (by simpa [hk] using hcomm.symm)
    rw [← map_mul, ← map_mul, hkl]

end Setup

section Cases

variable {G : Type} [Group G] [Finite G] {K L E : Subgroup G}

theorem false_of_HeCent
    (S : Setup K L E) (hK : CFSG.IsQuasisimple ↥K) {T T₀ : Subgroup G}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T K) (hT₀ : T₀ ≤ T)
    (hT₀N : T₀ ≤ Subgroup.normalizer (L : Set G)) (hidx : T₀.relIndex T ≤ 2)
    (hHe : A6CentHe) (e : (↥K ⧸ Subgroup.center ↥K) ≃* NativeSporadic.He) : False := by
  have ha : 2 ^ (9 + 1) ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.He.card_He]
    norm_num
  obtain ⟨hPp, hPN, hPa⟩ := S.imageT0_facts hT hT₀ hT₀N hidx ha
  have hbot : Subgroup.center ↥K = ⊥ :=
    CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate ↥K hK ⟨e⟩
  have hodd : Odd (Nat.card ↥(Subgroup.center ↥K)) := by
    rw [hbot, Subgroup.card_bot]
    exact odd_one
  obtain ⟨u, hu⟩ := S.exists_A6TypeCent hodd
  exact (not_le.mpr (hHe _ ⟨e⟩ _ _ u hu hPp hPN)) hPa

theorem false_of_RuP (S : Setup K L E) {T T₀ : Subgroup G}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T K) (hT₀ : T₀ ≤ T)
    (hT₀N : T₀ ≤ Subgroup.normalizer (L : Set G)) (hidx : T₀.relIndex T ≤ 2)
    (hRu : A6PRu) (e : (↥K ⧸ Subgroup.center ↥K) ≃* NativeSporadic.Ru) : False := by
  have ha : 2 ^ (13 + 1) ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ru.card_Ru]
    norm_num
  obtain ⟨hPp, hPN, hPa⟩ := S.imageT0_facts hT hT₀ hT₀N hidx ha
  have hY := S.config
  exact (not_le.mpr (hRu _ ⟨e⟩ _ _ hY.1 hY.2.1 hPp hPN)) hPa

theorem false_of_J4Cent
    (S : Setup K L E) (hK : CFSG.IsQuasisimple ↥K)
    {T T₀ : Subgroup G} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T K) (hT₀ : T₀ ≤ T)
    (hT₀N : T₀ ≤ Subgroup.normalizer (L : Set G)) (hidx : T₀.relIndex T ≤ 2)
    (hJ4 : A6CentJ4) (e : (↥K ⧸ Subgroup.center ↥K) ≃* NativeSporadic.J4) : False := by
  have ha : 2 ^ (20 + 1) ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4]
    norm_num
  obtain ⟨hPp, hPN, hPa⟩ := S.imageT0_facts hT hT₀ hT₀N hidx ha
  have hodd : Odd (Nat.card ↥(Subgroup.center ↥K)) :=
    CFSG.ComponentClassification.RankTwoSporadic.oddMultiplier_of_noPerfectDoubleCover
      (CFSG.Sporadic.Recognition.J4Multiplier.noPerfectDoubleCover_J4
        CFSG.ComponentClassification.RankTwoSporadic.J4.j4_foxCert
        CFSG.ComponentClassification.RankTwoSporadic.J4.j4_formCert)
      ↥K (Group.isPerfect_def.mp hK.1) ⟨e⟩
  obtain ⟨u, hu⟩ := S.exists_A6TypeCent hodd
  exact (not_le.mpr (hJ4 _ ⟨e⟩ _ _ u hu hPp hPN)) hPa

end Cases

theorem factKv1262aTwo_of_leavesCent
    (hLevi : LeviA6Free) (hM22 : A6LocM22) (hM23 : A6LocM23) (hM24 : A6LocM24)
    (hHS : A6LocHS) (hL52 : A6LocL52) (hJ2 : A6LocJ2) (hHe : A6CentHe) (hRu : A6PRu)
    (hJ4 : A6CentJ4) : CFSG.Quasithin.H13.FactKv1262aTwo := by
  intro G _ _ K T T₀ L E hK hList hT hT₀ hT₀N hidx hLK hperf hO2 hE hEab hEcard hLN hEcomm hC
  let S : Setup K L E := ⟨hLK, hperf, hO2, hE, hEab, hLN, hEcomm, hEcard, hC⟩
  have hY := S.config
  have h16 : 16 ≤ Nat.card ↥((E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) := by
    rcases S.card_F_cases with h | h <;> omega
  have hD := xdata_of_config hY h16
  rcases hList with hA | hB | hC' | hD' | hE'
  · obtain ⟨n, h5, h8, ⟨e⟩⟩ := hA
    exact (false_of_alt_fin hD h5 h8 e).elim
  · obtain ⟨p, hp, hp2, h⟩ := hB
    exact (false_of_odd hD hp hp2 h).elim
  · rcases hC' with hC1 | hTits
    · obtain ⟨f, hf⟩ := hC1
      rcases hf with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
      · exact (false_of_L2_even hD h1.1 h1.2).elim
      · exact (false_of_levi hLevi (Or.inl ⟨rfl, rfl, h2.1⟩) (Or.inl ⟨by decide, h2.2⟩) hD).elim
      · exact (false_of_levi hLevi (Or.inr (Or.inl ⟨rfl, rfl, h3.1⟩))
          (Or.inl ⟨by decide, h3.2⟩) hD).elim
      · exact (false_of_levi hLevi (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h4.1⟩)))
          (Or.inl ⟨by decide, h4.2⟩) hD).elim
      · exact (false_of_levi hLevi (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h5.1⟩))))
          (Or.inr (Or.inl ⟨rfl, by decide, h5.2⟩)) hD).elim
      · exact (false_of_levi hLevi
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h6.1⟩)))))
          (Or.inr (Or.inl ⟨rfl, by decide, h6.2⟩)) hD).elim
      · exact (false_of_levi hLevi
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h7.1, h7.2.1⟩))))))
          (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h7.2.2⟩))) hD).elim
      · exact (false_of_sz hD h8.2.2).elim
    · exact (false_of_levi hLevi
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))))
        (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hTits⟩))) hD).elim
  · obtain ⟨n, hn, hm⟩ := hD'
    rcases hn with rfl | rfl
    · exact (false_of_L4 hD hm).elim
    · have h16' := hL52 (↥K ⧸ Subgroup.center ↥K) hm _ _ hY
      have h2 := S.two_dvd_card_center_of_le16 h16'
      rw [card_center_L52_eq_one hK hm] at h2
      norm_num at h2
  · obtain ⟨s, hs, ⟨e⟩⟩ := hE'
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (false_of_card_not_dvd hD ((Nat.card_congr e.toEquiv).trans
        CFSG.Sporadic.Mathieu.card_M11) (by norm_num)).elim
    · exact (false_of_card_not_dvd hD ((Nat.card_congr e.toEquiv).trans
        CFSG.Sporadic.Mathieu.card_M12) (by norm_num)).elim
    · exact ⟨Or.inl ⟨e⟩, S.centralizer_le_center_of_card_le
        (hM22 (↥K ⧸ Subgroup.center ↥K) ⟨e⟩ _ _ hY)⟩
    · have h2 := S.two_dvd_card_center_of_le16 (hM23 (↥K ⧸ Subgroup.center ↥K) ⟨e⟩ _ _ hY)
      rw [card_center_M23_eq_one hK e] at h2
      norm_num at h2
    · have h2 := S.two_dvd_card_center_of_le16 (hM24 (↥K ⧸ Subgroup.center ↥K) ⟨e⟩ _ _ hY)
      have ho := odd_card_center_M24 hK e
      rw [Nat.odd_iff] at ho
      omega
    · exact (false_of_card_not_dvd hD ((Nat.card_congr e.toEquiv).trans
        CFSG.Sporadic.J1.card_J1) (by norm_num)).elim
    · exact (false_of_lt16 hD (hJ2 (↥K ⧸ Subgroup.center ↥K) ⟨e⟩ _ _ hY)).elim
    · exact (false_of_J4Cent S hK hT hT₀ hT₀N hidx hJ4 e).elim
    · exact ⟨Or.inr ⟨e⟩, S.centralizer_le_center_of_card_le
        (hHS (↥K ⧸ Subgroup.center ↥K) ⟨e⟩ _ _ hY)⟩
    · exact (false_of_HeCent S hK hT hT₀ hT₀N hidx hHe e).elim
    · exact (false_of_RuP S hT hT₀ hT₀N hidx hRu e).elim

end CFSG.Quasithin.H13.K1262Two

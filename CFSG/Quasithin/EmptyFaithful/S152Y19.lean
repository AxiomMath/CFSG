module

public import CFSG.Quasithin.EmptyFaithful.S152Y17

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem piStar_injective_Ys (h : Data T Mc M) (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥) :
    Function.Injective ((piStar h).comp (Ys T Mc M).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro u hu
  have hu1 : piStar h (u : OTwoQuot M) = 1 := MonoidHom.mem_ker.mp hu
  have hmem : (u : OTwoQuot M) ∈ Ys T Mc M ⊓ (piStar h).ker := ⟨u.2, hu1⟩
  rw [hK, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (Subtype.ext hmem)

theorem Ys_card_of_K_bot (h : Data T Mc M) (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥) :
    Nat.card (Ys T Mc M) = Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) := by
  have h1 : Nat.card ((piStar h).comp (Ys T Mc M).subtype).range = Nat.card ↥(Ys T Mc M) :=
    (Nat.card_congr (MonoidHom.ofInjective (piStar_injective_Ys h hK)).toEquiv).symm
  rw [MonoidHom.range_comp, Subgroup.range_subtype, Data.map_Ys h] at h1
  exact h1.symm

theorem Ys_pow_three_of_K_bot (h : Data T Mc M)
    (hEexp : ∀ a ∈ oTwoUpper (mBar0 T Mc M), a ^ 3 = 1)
    (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥) : ∀ y ∈ Ys T Mc M, y ^ 3 = 1 := by
  intro y hy
  have : (⟨y, hy⟩ : ↥(Ys T Mc M)) ^ 3 = 1 := by
    apply piStar_injective_Ys h hK
    show piStar h (y ^ 3) = piStar h 1
    rw [map_pow, map_one]
    exact hEexp _ (Data.piStar_mem_of_mem_Ys h hy)
  exact congrArg Subtype.val this

theorem Ys_elemAbelian_of_K_bot (h : Data T Mc M)
    (hE9 : Nat.card (oTwoUpper (mBar0 T Mc M)) = 9)
    (hEexp : ∀ a ∈ oTwoUpper (mBar0 T Mc M), a ^ 3 = 1)
    (hEab : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∀ b ∈ oTwoUpper (mBar0 T Mc M), a * b = b * a)
    (hYE : autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M))
    (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥) :
    CFSG.Open.IsElemAbelian 3 (Ys T Mc M) ∧ Nat.card (Ys T Mc M) = 9 := by
  have hinj : Function.Injective ((piStar h).comp (Ys T Mc M).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have hu1 : piStar h (u : OTwoQuot M) = 1 := MonoidHom.mem_ker.mp hu
    have hmem : (u : OTwoQuot M) ∈ Ys T Mc M ⊓ (piStar h).ker := ⟨u.2, hu1⟩
    rw [hK, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hab : ∀ a ∈ Ys T Mc M, ∀ b ∈ Ys T Mc M, a * b = b * a := by
    intro a ha b hb
    have hπ : piStar h a * piStar h b = piStar h b * piStar h a :=
      hEab _ (Data.piStar_mem_of_mem_Ys h ha) _ (Data.piStar_mem_of_mem_Ys h hb)
    have : (⟨a, ha⟩ : ↥(Ys T Mc M)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      apply hinj
      show piStar h (a * b) = piStar h (b * a)
      rw [map_mul, map_mul]
      exact hπ
    exact congrArg Subtype.val this
  have hexp : ∀ a ∈ Ys T Mc M, a ^ 3 = 1 := by
    intro a ha
    have : (⟨a, ha⟩ : ↥(Ys T Mc M)) ^ 3 = 1 := by
      apply hinj
      show piStar h (a ^ 3) = piStar h 1
      rw [map_pow, map_one]
      exact hEexp _ (Data.piStar_mem_of_mem_Ys h ha)
    exact congrArg Subtype.val this
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩, hexp⟩, ?_⟩
  have h1 : Nat.card ((piStar h).comp (Ys T Mc M).subtype).range = Nat.card ↥(Ys T Mc M) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [MonoidHom.range_comp, Subgroup.range_subtype, Data.map_Ys h, hYE] at h1
  rw [← h1]
  exact hE9

theorem threePrime_of_K_bot (h : Data T Mc M)
    (hE9 : Nat.card (oTwoUpper (mBar0 T Mc M)) = 9)
    (hEexp : ∀ a ∈ oTwoUpper (mBar0 T Mc M), a ^ 3 = 1)
    (hEab : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∀ b ∈ oTwoUpper (mBar0 T Mc M), a * b = b * a)
    (hYE : autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M))
    (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥) :
    IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
  intro hdvd
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYsEA, hYscard⟩ := Ys_elemAbelian_of_K_bot h hE9 hEexp hEab hYE hK
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))) 3 hdvd
  have hcM : (c : G) ∈ M := c.2.1
  have hcC : (c : G) ∈ Subgroup.centralizer (V154 T Mc M : Set G) := c.2.2
  have hcG : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hc
  set cs : OTwoQuot M := QuotientGroup.mk ⟨(c : G), hcM⟩ with hcs
  have hcs1 : cs ≠ 1 := by
    intro hone
    have hmem : (c : G) ∈ pCoreOf 2 M := (mk_eq_one_iff_mem_pCoreOf ⟨(c : G), hcM⟩).mp hone
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨(c : G), hmem⟩
    have hk' : (c : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd := orderOf_dvd_of_pow_eq_one hk'
    rw [hcG] at hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hcs3 : cs ^ 3 = 1 := by
    rw [hcs, ← QuotientGroup.mk_pow]
    have : (⟨(c : G), hcM⟩ : ↥M) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      have := pow_orderOf_eq_one (c : G)
      rwa [hcG] at this
    rw [this]
    rfl
  have hcsord : orderOf cs = 3 := orderOf_eq_prime hcs3 hcs1
  have hcsC : cs ∈ imageOTwoQuot M (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) :=
    mem_imageOTwoQuot_iff.mpr ⟨c, hcM, ⟨hcM, hcC⟩, rfl⟩
  have hcsker : cs ∈ (piStar h).ker :=
    MonoidHom.mem_ker.mpr ((piStar_mk_eq_one_iff h hcM).mpr hcC)
  have hcomm : ∀ e ∈ Ys T Mc M, Commute e cs := by
    intro y hy
    have h0 := Data.Ys_Rcs_centralize h
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
    exact Subgroup.mem_centralizer_iff.mp (h0 hcsC) y (Subgroup.mem_sup_left hy)
  have hcsY : cs ∉ Ys T Mc M := by
    intro hY
    have hmem : cs ∈ Ys T Mc M ⊓ (piStar h).ker := ⟨hY, hcsker⟩
    rw [hK, Subgroup.mem_bot] at hmem
    exact hcs1 hmem
  obtain ⟨hEA, hcard⟩ := exists_elemAbelian_sup_zpowers (p := 3) hYsEA hcsord hcomm hcsY
  have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot M)) :=
    le_pRank Nat.prime_three le_top hEA (k := 3) (by rw [hcard, hYscard]; norm_num)
  have h4 := pRank_Mstar_le_two h Nat.prime_three (by norm_num)
  omega

theorem Ys_isPOnePlusTwo (h : Data T Mc M)
    (hE9 : Nat.card (oTwoUpper (mBar0 T Mc M)) = 9)
    (hEexp : ∀ a ∈ oTwoUpper (mBar0 T Mc M), a ^ 3 = 1)
    (hEab : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∀ b ∈ oTwoUpper (mBar0 T Mc M), a * b = b * a)
    {b : MulAut (V154 T Mc M)} (hbR : b ∈ autOn (rcOf Mc M) (V154 T Mc M))
    (hbinv : ∀ a ∈ oTwoUpper (mBar0 T Mc M), b * a * b⁻¹ = a⁻¹)
    (hnonab : ¬ ∀ a ∈ Ys T Mc M, ∀ c ∈ Ys T Mc M, a * c = c * a) :
    IsPOnePlusTwo 3 ↥(Ys T Mc M) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEodd : Odd (Nat.card (oTwoUpper (mBar0 T Mc M))) := by rw [hE9]; decide
  have hodd := Data.Ys_odd h hEodd
  have hKc := K_central_Ys h
  have hcomm_le := Data.commutator_le_K h hEab
  have hK_le := Data.K_le_commutator h hEodd
  have hcube : ∀ y ∈ Ys T Mc M, y ^ 3 ∈ Ys T Mc M ⊓ (piStar h).ker := by
    intro y hy
    refine ⟨(Ys T Mc M).pow_mem hy 3, MonoidHom.mem_ker.mpr ?_⟩
    rw [map_pow]
    exact hEexp _ (Data.piStar_mem_of_mem_Ys h hy)
  have hcomm3 : ∀ a ∈ Ys T Mc M, ∀ a' ∈ Ys T Mc M, ⁅a, a'⁆ ^ 3 = 1 := by
    intro a ha a' ha'
    have hc : ⁅a, a'⁆ ∈ Ys T Mc M ⊓ (piStar h).ker :=
      hcomm_le (Subgroup.commutator_mem_commutator ha ha')
    have hac : Commute a ⁅a, a'⁆ := hKc _ hc a ha
    rw [hac.commutatorElement_pow_left 3]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hKc _ (hcube a ha) a' ha').symm
  have hKexp : ∀ k ∈ Ys T Mc M ⊓ (piStar h).ker, k ^ 3 = 1 := by
    intro k hk
    have key : ∀ x ∈ ⁅Ys T Mc M, Ys T Mc M⁆,
        x ∈ Ys T Mc M ⊓ (piStar h).ker ∧ x ^ 3 = 1 := by
      intro x hx
      rw [Subgroup.commutator_def] at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, a', ha', rfl⟩ := hx
        exact ⟨hcomm_le (Subgroup.commutator_mem_commutator ha ha'), hcomm3 a ha a' ha'⟩
      | one => exact ⟨(Ys T Mc M ⊓ (piStar h).ker).one_mem, one_pow 3⟩
      | mul x y _ _ hx hy =>
        refine ⟨(Ys T Mc M ⊓ (piStar h).ker).mul_mem hx.1 hy.1, ?_⟩
        have hxy : Commute x y := (hKc x hx.1 y hy.1.1).symm
        rw [hxy.mul_pow, hx.2, hy.2, one_mul]
      | inv x _ hx =>
        exact ⟨(Ys T Mc M ⊓ (piStar h).ker).inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩
    exact (key k (hK_le hk)).2
  obtain ⟨r, hrR, hrb⟩ := Data.exists_Rcs_of_mem_autOn h hbR
  have hrN : r ∈ Subgroup.normalizer (Ys T Mc M : Set (OTwoQuot M)) :=
    Data.Ls_le_normalizer_Ys h (Rcs_le_Ls T Mc M hrR)
  have hrK := Rcs_comm_K h r hrR
  have hexp : ∀ y ∈ Ys T Mc M, y ^ 3 = 1 := by
    intro y hy
    have hconj : r * y * r⁻¹ ∈ Ys T Mc M := (Subgroup.mem_normalizer_iff.mp hrN y).mp hy
    set k := (r * y * r⁻¹) * y with hkdef
    have hk : k ∈ Ys T Mc M ⊓ (piStar h).ker := by
      refine ⟨(Ys T Mc M).mul_mem hconj hy, MonoidHom.mem_ker.mpr ?_⟩
      rw [hkdef, map_mul, map_mul, map_mul, map_inv, hrb,
        hbinv _ (Data.piStar_mem_of_mem_Ys h hy), inv_mul_cancel]
    have hy3 := hcube y hy
    have e1 : r * y ^ 3 * r⁻¹ = y ^ 3 := by
      rw [hrK _ hy3]; group
    have e2 : r * y ^ 3 * r⁻¹ = (k * y⁻¹) ^ 3 := by
      have : r * y * r⁻¹ = k * y⁻¹ := by rw [hkdef]; group
      rw [← conj_pow, this]
    have e3 : (k * y⁻¹) ^ 3 = (y ^ 3)⁻¹ := by
      have hc : Commute k y⁻¹ := (hKc k hk y⁻¹ ((Ys T Mc M).inv_mem hy)).symm
      rw [hc.mul_pow, hKexp k hk, one_mul, inv_pow]
    have e4 : y ^ 3 = (y ^ 3)⁻¹ := e1.symm.trans (e2.trans e3)
    have hsq : (y ^ 3) ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      calc y ^ 3 * y ^ 3 = y ^ 3 * (y ^ 3)⁻¹ := by rw [← e4]
        _ = 1 := mul_inv_cancel _
    have hodd' : Odd (orderOf (y ^ 3)) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hy3.1)
    exact eq_one_of_odd_of_two_power hodd' hsq
  have hP3 : IsPGroup 3 ↥(Ys T Mc M) := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  have hΩ : Subgroup.closure {x : ↥(Ys T Mc M) | x ^ 3 = 1} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.subset_closure (Subtype.ext (by simpa using hexp x x.2))
  have hcl : ClassLeTwo (⊤ : Subgroup ↥(Ys T Mc M)) := by
    unfold ClassLeTwo
    have hcen : ⁅(⊤ : Subgroup ↥(Ys T Mc M)), ⊤⁆ ≤ Subgroup.center ↥(Ys T Mc M) := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_center_iff]
      intro z
      have hc : ⁅(a : OTwoQuot M), (b : OTwoQuot M)⁆ ∈ Ys T Mc M ⊓ (piStar h).ker :=
        hcomm_le (Subgroup.commutator_mem_commutator a.2 b.2)
      exact Subtype.ext (hKc _ hc z z.2)
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro c hc g _
    have hcz := Subgroup.mem_center_iff.mp (hcen hc) g
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr hcz.symm)
  have hrank_le : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Ys T Mc M)) ≤ 2 := by
    have h1 := pRank_top_subtype (p := 3) (Ys T Mc M)
    have h2 := CFSG.SectionRank.pRank_mono (p := 3) Nat.prime_three.one_lt
      (le_top : Ys T Mc M ≤ ⊤)
    have h3 := pRank_Mstar_le_two h Nat.prime_three (by norm_num)
    omega
  have hrank_ge : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Ys T Mc M)) := by
    rw [pRank_top_subtype (p := 3) (Ys T Mc M)]
    push Not at hnonab
    obtain ⟨a, ha, a', ha', hne⟩ := hnonab
    have hzK : ⁅a, a'⁆ ∈ Ys T Mc M ⊓ (piStar h).ker :=
      hcomm_le (Subgroup.commutator_mem_commutator ha ha')
    have hz1 : ⁅a, a'⁆ ≠ 1 := fun h1 => hne (commutatorElement_eq_one_iff_mul_comm.mp h1)
    have hz3 : ⁅a, a'⁆ ^ 3 = 1 := hcomm3 a ha a' ha'
    have haK : a ∉ Ys T Mc M ⊓ (piStar h).ker := fun haK =>
      hne (hKc a haK a' ha').symm
    have ha1 : a ≠ 1 := fun h1 => haK (h1 ▸ (Ys T Mc M ⊓ (piStar h).ker).one_mem)
    have hao : orderOf a = 3 := orderOf_eq_prime (hexp a ha) ha1
    have hEz : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers ⁅a, a'⁆) := by
      refine ⟨inferInstance, fun x hx => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
    have hzle : Subgroup.zpowers ⁅a, a'⁆ ≤ Ys T Mc M ⊓ (piStar h).ker :=
      Subgroup.zpowers_le.mpr hzK
    have hcommz : ∀ e ∈ Subgroup.zpowers ⁅a, a'⁆, Commute e a := by
      intro e he
      exact (hKc e (hzle he) a ha).symm
    have haz : a ∉ Subgroup.zpowers ⁅a, a'⁆ := fun h1 => haK (hzle h1)
    obtain ⟨hEA, hcard⟩ := exists_elemAbelian_sup_zpowers (p := 3) hEz hao hcommz haz
    have hzcard : Nat.card (Subgroup.zpowers ⁅a, a'⁆) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
    exact le_pRank Nat.prime_three
      (sup_le (Subgroup.zpowers_le.mpr hzK.1) (Subgroup.zpowers_le.mpr ha)) hEA (k := 2)
      (by rw [hcard, hzcard]; norm_num)
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Ys T Mc M)) = 2 := le_antisymm hrank_le hrank_ge
  rcases isElemAbelianOfRank_two_or_isPOnePlusTwo (p := 3) (by norm_num) hP3 hΩ hrank hcl with
    hA | hP
  · exfalso
    obtain ⟨e⟩ : Nonempty (↥(Ys T Mc M) ≃* Multiplicative (Fin 2 → ZMod 3)) := hA
    apply hnonab
    intro a ha c hc
    have h1 : e (⟨a, ha⟩ * ⟨c, hc⟩) = e (⟨c, hc⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (e.injective h1)
  · exact hP

end S152Y

end CFSG.Quasithin

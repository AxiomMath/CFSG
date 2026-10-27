module

public import CFSG.Quasithin.EmptyFaithful.S152Y19

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

section Generic

theorem isCyclic_of_centralizing {B : Type} [Group B] [Finite B]
    (hB : CFSG.Open.pRank 3 (⊤ : Subgroup B) ≤ 2) {S : Subgroup B} (hS : IsPGroup 3 S) {y : B}
    (hy : orderOf y = 3) (hyS : y ∉ S) (hc : ∀ s ∈ S, Commute s y) : IsCyclic ↥S := by
  by_contra hnc
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSf : Fact (IsPGroup 3 ↥S) := ⟨hS⟩
  obtain ⟨F, -, hFcard, hF⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have hFc : IsMulCommutative ↥F := hF.toIsMulCommutative
  have hFexp : ∀ a ∈ F, a ^ 3 = 1 := fun a ha =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := F) a ha
  set F' : Subgroup B := F.map S.subtype with hF'
  have hF'le : F' ≤ S := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hF'ea : CFSG.Open.IsElemAbelian 3 F' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := a.2
      obtain ⟨b', hb', hb'e⟩ := b.2
      apply Subtype.ext
      have h1 : (⟨a', ha'⟩ : ↥F) * ⟨b', hb'⟩ = ⟨b', hb'⟩ * ⟨a', ha'⟩ := mul_comm' _ _
      have h2 : a' * b' = b' * a' := congrArg Subtype.val h1
      show (a : B) * (b : B) = (b : B) * (a : B)
      rw [← ha'e, ← hb'e]
      exact congrArg Subtype.val h2
    · rintro _ ⟨a, ha, rfl⟩
      have := hFexp a ha
      simpa using congrArg Subtype.val this
  have hF'card : Nat.card F' = 3 ^ 2 := by
    rw [hF', Subgroup.card_map_of_injective S.subtype_injective, hFcard]
  obtain ⟨hEA, hcard⟩ := exists_elemAbelian_sup_zpowers (p := 3) hF'ea hy
    (fun e he => hc e (hF'le he)) (fun hh => hyS (hF'le hh))
  have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup B) :=
    le_pRank Nat.prime_three le_top hEA (k := 3) (by rw [hcard, hF'card]; norm_num)
  omega

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem Ys_normal (hYnorm : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G)) :
    (Ys T Mc M).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
  have hmem : (QuotientGroup.mk m : OTwoQuot M) ∈ imageOTwoQuot M M :=
    mem_imageOTwoQuot_iff.mpr ⟨m, m.2, m.2, rfl⟩
  have := imageOTwoQuot_le_normalizer hYnorm hmem
  exact (Subgroup.mem_normalizer_iff.mp this n).mp hn

theorem sylow_structure (h : Data T Mc M)
    (hA : autOn M (V154 T Mc M) = mBar0 T Mc M)
    (hX36 : Nat.card (mBar0 T Mc M) = 36)
    (hE9 : Nat.card (oTwoUpper (mBar0 T Mc M)) = 9)
    (hEexp : ∀ a ∈ oTwoUpper (mBar0 T Mc M), a ^ 3 = 1)
    (hEab : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∀ b ∈ oTwoUpper (mBar0 T Mc M), a * b = b * a)
    (hYcard : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 3)
    (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥)
    (hYnorm : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G))
    {P : Subgroup G} (hP : IsSylowIn 3 P M) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card P = 3 ^ (m + 1) ∧ IsZ3TimesZ3Pow m ↥P := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYM : yOf152 T Mc M ≤ M := h.yOf_le_M
  have hY'card : Nat.card (Ys T Mc M) = 3 := (Ys_card_of_K_bot h hK).trans hYcard
  have hY'exp := Ys_pow_three_of_K_bot h hEexp hK
  have : (Ys T Mc M).Normal := Ys_normal hYnorm
  obtain ⟨hPM, hP3, hPidx⟩ := hP
  have hP3' : IsPGroup 3 (P.subgroupOf M) := hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  have hPm3 : IsPGroup 3 ↥(imageOTwoQuot M P) := hP3'.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M))
  have hPmidx : ¬ 3 ∣ (imageOTwoQuot M P).index := by
    intro hd
    apply hPidx
    have h1 : (imageOTwoQuot M P).index ∣ (P.subgroupOf M).index :=
      Subgroup.index_map_dvd (P.subgroupOf M) (QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥M))
    exact hd.trans h1
  let PmS : Sylow 3 (OTwoQuot M) := hPm3.toSylow hPmidx
  have hY3 : IsPGroup 3 ↥(Ys T Mc M) := fun g => ⟨1, Subtype.ext (by simpa using hY'exp g g.2)⟩
  have hY'le : Ys T Mc M ≤ imageOTwoQuot M P := hY3.le_sylow_of_normal PmS
  set Y' := Ys T Mc M with hY'
  set Pm := imageOTwoQuot M P with hPm
  set E := oTwoUpper (mBar0 T Mc M) with hEdef
  set Yb := autOn (yOf152 T Mc M) (V154 T Mc M) with hYbdef
  have hπPm : ∀ s ∈ Pm, piStar h s ∈ E := by
    intro s hs
    have h1 : piStar h s ∈ autOn P (V154 T Mc M) := by
      rw [← map_piStar_imageOTwoQuot h hPM]
      exact Subgroup.mem_map_of_mem _ hs
    have h2 : piStar h s ∈ mBar0 T Mc M := by
      rw [← hA]
      exact A4.autOn_mono hPM h1
    obtain ⟨k, hk⟩ := hPm3 ⟨s, hs⟩
    have hk' : s ^ 3 ^ k = 1 := congrArg Subtype.val hk
    have hodd : Odd (orderOf (piStar h s)) := by
      refine Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one (n := 3 ^ k) ?_)
      rw [← map_pow, hk', map_one]
    exact mem_oTwoUpper_of_odd h2 hodd
  have hπY : ∀ y ∈ Y', piStar h y ∈ E := fun y hy => Data.piStar_mem_of_mem_Ys h hy
  have hcentral : ∀ s ∈ Pm, ∀ y ∈ Y', s * y = y * s := by
    intro s hs y hy
    have hc : ⁅s, y⁆ ∈ Y' ⊓ (piStar h).ker := by
      refine ⟨?_, MonoidHom.mem_ker.mpr ?_⟩
      · rw [commutatorElement_def]
        exact Y'.mul_mem ((inferInstance : Y'.Normal).conj_mem y hy s) (Y'.inv_mem hy)
      · rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hEab _ (hπPm s hs) _ (hπY y hy))
    rw [hK, Subgroup.mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  have hYb_le : Yb ≤ E := by
    rw [hYbdef, ← Data.map_Ys h]
    rintro _ ⟨y, hy, rfl⟩
    exact hπY y hy
  obtain ⟨e, heE, heY⟩ : ∃ e ∈ E, e ∉ Yb := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Yb := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    omega
  have he1 : e ≠ 1 := fun h1 => heY (h1 ▸ Yb.one_mem)
  have heo : orderOf e = 3 := orderOf_eq_prime (hEexp e heE) he1
  have hYbEA : CFSG.Open.IsElemAbelian 3 Yb :=
    ⟨⟨⟨fun a b => Subtype.ext (hEab _ (hYb_le a.2) _ (hYb_le b.2))⟩⟩,
      fun x hx => hEexp x (hYb_le hx)⟩
  obtain ⟨-, hYbecard⟩ := exists_elemAbelian_sup_zpowers (p := 3) hYbEA heo
    (fun a ha => hEab a (hYb_le ha) e heE) heY
  have hsupE : Yb ⊔ Subgroup.zpowers e = E := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hYb_le (Subgroup.zpowers_le.mpr heE))
    omega
  have hLE : Yb ≤ Subgroup.normalizer (Subgroup.zpowers e : Set (MulAut (V154 T Mc M))) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute e a from hEab e heE a (hYb_le ha)) k).eq
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right Yb (Subgroup.zpowers e) hLE
  have hbot : Yb ⊓ Subgroup.zpowers e = ⊥ := by
    have hdvd : Nat.card ↥(Yb ⊓ Subgroup.zpowers e) ∣ 3 := by
      have h1 := Subgroup.card_dvd_of_le
        (inf_le_right : Yb ⊓ Subgroup.zpowers e ≤ Subgroup.zpowers e)
      rwa [Nat.card_zpowers, heo] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      apply heY
      have h2 := Subgroup.eq_of_le_of_card_ge
        (inf_le_right : Yb ⊓ Subgroup.zpowers e ≤ Subgroup.zpowers e)
        (by rw [h1, Nat.card_zpowers, heo])
      have he' : e ∈ Yb ⊓ Subgroup.zpowers e := by
        rw [h2]; exact Subgroup.mem_zpowers e
      exact he'.1
  set S₁ : Subgroup (OTwoQuot M) := Pm ⊓ (Subgroup.zpowers e).comap (piStar h) with hS₁
  have hS₁Pm : S₁ ≤ Pm := inf_le_left
  have hdecomp : ∀ s ∈ Pm, ∃ y ∈ Y', ∃ t ∈ S₁, s = y * t := by
    intro s hs
    have hsE : piStar h s ∈ Yb ⊔ Subgroup.zpowers e := by
      rw [hsupE]; exact hπPm s hs
    rw [← SetLike.mem_coe, hmul] at hsE
    obtain ⟨a, ha, w, hw, hasw⟩ := hsE
    rw [hYbdef, ← Data.map_Ys h] at ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨y, hy, y⁻¹ * s, ⟨Pm.mul_mem (Pm.inv_mem (hY'le hy)) hs, ?_⟩, by group⟩
    show piStar h (y⁻¹ * s) ∈ Subgroup.zpowers e
    rw [map_mul, map_inv, ← hasw, inv_mul_cancel_left]
    exact hw
  have hint : Y' ⊓ S₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyY, hyP, hye⟩
    have hπy : piStar h y ∈ Yb ⊓ Subgroup.zpowers e :=
      ⟨by rw [hYbdef, ← Data.map_Ys h]; exact Subgroup.mem_map_of_mem _ hyY, hye⟩
    rw [hbot, Subgroup.mem_bot] at hπy
    have hmem : y ∈ Y' ⊓ (piStar h).ker := ⟨hyY, hπy⟩
    rw [hK] at hmem
    exact hmem
  have hcomm : ∀ (y : ↥Y') (t : ↥S₁), Commute (Y'.subtype y) (S₁.subtype t) :=
    fun y t => (hcentral t (hS₁Pm t.2) y y.2).symm
  let f₂ : ↥Y' × ↥S₁ →* OTwoQuot M := MonoidHom.noncommCoprod Y'.subtype S₁.subtype hcomm
  have hf₂ : ∀ z : ↥Y' × ↥S₁, f₂ z = (z.1 : OTwoQuot M) * (z.2 : OTwoQuot M) := fun z => rfl
  have hinj : Function.Injective f₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨y, t⟩ hz
    rw [MonoidHom.mem_ker, hf₂] at hz
    have hmem : (y : OTwoQuot M) ∈ Y' ⊓ S₁ := by
      refine ⟨y.2, ?_⟩
      have : (y : OTwoQuot M) = ((t : OTwoQuot M))⁻¹ := eq_inv_of_mul_eq_one_left hz
      rw [this]
      exact S₁.inv_mem t.2
    rw [hint] at hmem
    have hy1 : (y : OTwoQuot M) = 1 := hmem
    have ht1 : (t : OTwoQuot M) = 1 := by
      rw [hy1, one_mul] at hz
      exact hz
    simp only [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hy1, Subtype.ext ht1⟩
  have hrange : f₂.range = Pm := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    apply le_antisymm
    · exact sup_le hY'le hS₁Pm
    · intro s hs
      obtain ⟨y, hy, t, ht, rfl⟩ := hdecomp s hs
      exact Subgroup.mul_mem_sup hy ht
  let e₂ : ↥Y' × ↥S₁ ≃* ↥Pm :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let φ : ↥(P.subgroupOf M) →* OTwoQuot M :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M)).comp (P.subgroupOf M).subtype
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : (QuotientGroup.mk (x : ↥M) : OTwoQuot M) = 1 := MonoidHom.mem_ker.mp hx
    have hmem : ((x : ↥M) : G) ∈ pCoreOf 2 M := (mk_eq_one_iff_mem_pCoreOf (x : ↥M)).mp hx1
    have hxP : ((x : ↥M) : G) ∈ P := x.2
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨((x : ↥M) : G), hmem⟩
    obtain ⟨j, hj⟩ := hP3 ⟨((x : ↥M) : G), hxP⟩
    have hk' : ((x : ↥M) : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hj' : ((x : ↥M) : G) ^ 3 ^ j = 1 := congrArg Subtype.val hj
    have hodd : Odd (orderOf ((x : ↥M) : G)) :=
      Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hj')
    have h1 : ((x : ↥M) : G) = 1 := eq_one_of_odd_of_two_power hodd hk'
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  have hφrange : φ.range = Pm := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  let e₁ : ↥P ≃* ↥Pm :=
    (Subgroup.subgroupOfEquivOfLe hPM).symm.trans
      ((MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hφrange))
  have hS₁3 : IsPGroup 3 ↥S₁ := hPm3.to_le hS₁Pm
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y') 3 (by rw [hY'card])
  have hy₀o : orderOf (y₀ : OTwoQuot M) = 3 := by rw [Subgroup.orderOf_coe]; exact hy₀
  have hy₀S : (y₀ : OTwoQuot M) ∉ S₁ := by
    intro hh
    have hmem : (y₀ : OTwoQuot M) ∈ Y' ⊓ S₁ := ⟨y₀.2, hh⟩
    rw [hint] at hmem
    have h1 : (y₀ : OTwoQuot M) = 1 := hmem
    rw [h1, orderOf_one] at hy₀o
    omega
  have hcyc : IsCyclic ↥S₁ :=
    isCyclic_of_centralizing (pRank_Mstar_le_two h Nat.prime_three (by norm_num)) hS₁3 hy₀o hy₀S
      (fun s hs => hcentral s (hS₁Pm hs) y₀ y₀.2)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hS₁3
  have hcardPm : Nat.card ↥Pm = 3 * 3 ^ m := by
    have h1 : Nat.card ↥f₂.range = Nat.card (↥Y' × ↥S₁) :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hrange, Nat.card_prod, hY'card, hm] at h1
    exact h1
  have hcardP : Nat.card ↥P = 3 ^ (m + 1) := by
    rw [Nat.card_congr e₁.toEquiv, hcardPm, pow_succ]
    ring
  have h9M : 9 ∣ Nat.card ↥M := by
    have h1 : Nat.card (autOn M (V154 T Mc M)) ∣ Nat.card ↥M := by
      unfold autOn
      have h2 := Subgroup.card_map_dvd (M.subgroupOf (Subgroup.normalizer (V154 T Mc M : Set G)))
        (conjAct (V154 T Mc M))
      have h3 : Nat.card ↥(M.subgroupOf (Subgroup.normalizer (V154 T Mc M : Set G))) =
          Nat.card ↥M := Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.hMV).toEquiv
      rwa [h3] at h2
    rw [hA, hX36] at h1
    exact (by norm_num : 9 ∣ 36).trans h1
  have hm1 : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    have hMcard : Nat.card ↥(P.subgroupOf M) * (P.subgroupOf M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    have hcP : Nat.card ↥(P.subgroupOf M) = Nat.card ↥P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
    rw [hcP, hcardP, hm0'] at hMcard
    rw [← hMcard] at h9M
    obtain ⟨c, hc⟩ := h9M
    have hidx : (P.subgroupOf M).index = 3 * c := by
      simp at hc
      omega
    exact hPidx ⟨c, hidx⟩
  refine ⟨m, hm1, hcardP, ⟨?_⟩⟩
  have hYcyc : IsCyclic ↥Y' := isCyclic_of_prime_card hY'card
  have eY : Multiplicative (ZMod 3) ≃* ↥Y' := by
    have := zmodCyclicMulEquiv hYcyc
    rw [hY'card] at this
    exact this
  have eS : Multiplicative (ZMod (3 ^ m)) ≃* ↥S₁ := by
    have := zmodCyclicMulEquiv hcyc
    rw [hm] at this
    exact this
  exact (e₁.trans (e₂.symm.trans (MulEquiv.prodCongr eY.symm eS.symm)))


theorem exists_sylow_three (h : Data T Mc M)
    (hA : autOn M (V154 T Mc M) = mBar0 T Mc M)
    (hX36 : Nat.card (mBar0 T Mc M) = 36)
    (hE9 : Nat.card (oTwoUpper (mBar0 T Mc M)) = 9)
    (hEexp : ∀ a ∈ oTwoUpper (mBar0 T Mc M), a ^ 3 = 1)
    (hEab : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∀ b ∈ oTwoUpper (mBar0 T Mc M), a * b = b * a)
    (hYcard : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 3)
    (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥)
    (hYnorm : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G)) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ P : Subgroup G, IsSylowIn 3 P M → IsZ3TimesZ3Pow n ↥P := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : ∀ P : Subgroup G, IsSylowIn 3 P M →
      Nat.card P = 3 ^ (Nat.card ↥M).factorization 3 := by
    intro P hP
    have h1 : Nat.card ↥(hP.toSylow : Subgroup ↥M) = 3 ^ (Nat.card ↥M).factorization 3 :=
      Sylow.card_eq_multiplicity _
    rw [IsSylowIn.coe_toSylow] at h1
    rw [← h1]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.le).toEquiv).symm
  obtain ⟨P₀, hP₀, -⟩ := exists_isSylowIn_ge 3 (bot_le : (⊥ : Subgroup G) ≤ M)
    (IsPGroup.of_card (n := 0) (by simp))
  obtain ⟨m₀, hm₀, hcard₀, -⟩ := sylow_structure h hA hX36 hE9 hEexp hEab hYcard hK hYnorm hP₀
  refine ⟨m₀, hm₀, fun P hP => ?_⟩
  obtain ⟨m, -, hcardm, hiso⟩ := sylow_structure h hA hX36 hE9 hEexp hEab hYcard hK hYnorm hP
  have h1 : 3 ^ (m + 1) = 3 ^ (m₀ + 1) := by
    rw [← hcardm, ← hcard₀, hcard P hP, hcard P₀ hP₀]
  have h2 : m + 1 = m₀ + 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have h3 : m = m₀ := by omega
  subst h3
  exact hiso

end Main

end S152Y

end CFSG.Quasithin

module

public import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

section Abstract

variable {K : Type} [Group K] [Finite K]

theorem eq_one_of_mem_oddCore_of_mul_self {o : K} (ho : o ∈ CFSG.oddCore K) (ho2 : o * o = 1) :
    o = 1 := by
  have hodd : Odd (Nat.card (CFSG.oddCore K)) := CFSG.ABGLocalTools.odd_card_oddCore
  have hord : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
  have hoddo : Odd (orderOf o) := by
    rw [← Subgroup.orderOf_mk o ho]
    exact Odd.of_dvd_nat hodd (orderOf_dvd_natCard _)
  rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hoddo
    exact absurd hoddo (by decide)

theorem inf_oddCore_eq_bot_of_isPGroup {P : Subgroup K} (hP : IsPGroup 2 P) :
    P ⊓ CFSG.oddCore K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Subgroup.inf_eq_bot_of_coprime ?_
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr CFSG.ABGLocalTools.odd_card_oddCore)

end Abstract

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem center_le_oddCore_of_pCore_eq_bot (hC : HypothesisC D)
    (hP : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) :
    Subgroup.center (Halpha D hC.alpha) ≤ CFSG.oddCore (Halpha D hC.alpha) := by
  have h := center_le_pCore_sup_oddCore (K := Halpha D hC.alpha)
  rwa [hP, bot_sup_eq] at h

theorem mem_DalphaStar_of_mul_self_eq_one (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hP : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {t : G} (htH : t ∈ Halpha D hC.alpha)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : t ∈ DalphaStar D hC.alpha := by
  classical
  have hZO := center_le_oddCore_of_pCore_eq_bot hC hP
  set π := QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))
  have hinv : ∀ x : Halpha D hC.alpha, x * x = 1 → x ≠ 1 → orderOf (π x) = 2 := by
    intro x hx2 hx1
    refine orderOf_eq_prime (by rw [pow_two, ← map_mul, hx2, map_one]) fun h => hx1 ?_
    exact eq_one_of_mem_oddCore_of_mul_self (hZO ((QuotientGroup.eq_one_iff x).mp h)) hx2
  obtain ⟨d₀, hd₀⟩ := DstarH_nonempty hC
  have hd₀G : (d₀ : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hd₀)
  have hd₀2 : d₀ * d₀ = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hd₀G)
  have hd₀1 : d₀ ≠ 1 := fun h => hC.setup.oddT.ne_one hd₀G (congrArg Subtype.val h)
  set t' : Halpha D hC.alpha := ⟨t, htH⟩
  have ht'2 : t' * t' = 1 := Subtype.ext ht2
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := isConj_iff.mp (IsBenderGroup.isConj_of_orderOf_eq_two hH.bender
    (hinv d₀ hd₀2 hd₀1) (hinv t' ht'2 ht'1))
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ c
  set w := (c * d₀ * c⁻¹)⁻¹ * t' with hw
  have hwZ : w ∈ Subgroup.center (Halpha D hC.alpha) := by
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center (Halpha D hC.alpha)), hw]
    change π _ = 1
    rw [map_mul, map_inv, map_mul, map_mul, map_inv]
    change (π c * π d₀ * (π c)⁻¹)⁻¹ * π t' = 1
    rw [hc, inv_mul_cancel]
  have hcd2 : (c * d₀ * c⁻¹) * (c * d₀ * c⁻¹) = 1 := by
    calc (c * d₀ * c⁻¹) * (c * d₀ * c⁻¹) = c * (d₀ * d₀) * c⁻¹ := by group
      _ = 1 := by rw [hd₀2, mul_one, mul_inv_cancel]
  have hteq : t' = (c * d₀ * c⁻¹) * w := by rw [hw, mul_inv_cancel_left]
  have hw2 : w * w = 1 := by
    have hwc : ∀ y, w * y = y * w := fun y => (Subgroup.mem_center_iff.mp hwZ y).symm
    have h1 : t' * t' = (c * d₀ * c⁻¹) * (c * d₀ * c⁻¹) * (w * w) := by
      rw [hteq]
      calc (c * d₀ * c⁻¹) * w * ((c * d₀ * c⁻¹) * w)
          = (c * d₀ * c⁻¹) * (w * (c * d₀ * c⁻¹)) * w := by group
        _ = (c * d₀ * c⁻¹) * (c * d₀ * c⁻¹) * (w * w) := by rw [hwc]; group
    rw [ht'2, hcd2, one_mul] at h1
    exact h1.symm
  have hw1 : w = 1 := eq_one_of_mem_oddCore_of_mul_self (hZO hwZ) hw2
  rw [hw1, mul_one] at hteq
  have hmem : t' ∈ DstarH hC := by
    rw [hteq]
    exact DstarH_conj_mem hC hd₀
  exact (mem_DstarH_iff hC).mp hmem

theorem commute_of_mem_sylow_of_mul_self_eq_one (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hP : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) (T : Sylow 2 (Halpha D hC.alpha))
    {v t : Halpha D hC.alpha} (hv : v ∈ (T : Subgroup (Halpha D hC.alpha))) (hv2 : v * v = 1)
    (ht : t ∈ (T : Subgroup (Halpha D hC.alpha))) : Commute t v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZO := center_le_oddCore_of_pCore_eq_bot hC hP
  set π := QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Tb := T.mapSurjective hπs
  have hTb : (Tb : Subgroup _) = (T : Subgroup (Halpha D hC.alpha)).map π :=
    Sylow.coe_mapSurjective hπs T
  have hvb : π v ∈ (Tb : Subgroup _) := by rw [hTb]; exact Subgroup.mem_map_of_mem π hv
  have htb : π t ∈ (Tb : Subgroup _) := by rw [hTb]; exact Subgroup.mem_map_of_mem π ht
  have hcomm := IsBenderGroup.commute_of_mul_self_eq_one hH.bender Tb hvb
    (by rw [← map_mul, hv2, map_one]) (π t) htb
  set c := t * v * t⁻¹ * v⁻¹ with hcdef
  have hcZ : c ∈ Subgroup.center (Halpha D hC.alpha) := by
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center (Halpha D hC.alpha)), hcdef]
    change π _ = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm.symm.eq]
    group
  have hcT : c ∈ (T : Subgroup (Halpha D hC.alpha)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hv) (Subgroup.inv_mem _ ht))
      (Subgroup.inv_mem _ hv)
  have hc1 : c = 1 := by
    have hmem : c ∈ (T : Subgroup (Halpha D hC.alpha)) ⊓ CFSG.oddCore (Halpha D hC.alpha) :=
      ⟨hcT, hZO hcZ⟩
    rwa [inf_oddCore_eq_bot_of_isPGroup T.isPGroup', Subgroup.mem_bot] at hmem
  have h : t * v * t⁻¹ = v := by
    rw [hcdef, mul_inv_eq_one] at hc1
    exact hc1
  calc t * v = t * v * t⁻¹ * t := by group
    _ = v * t := by rw [h]

theorem exists_omegaOne (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hP : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) (T : Sylow 2 (Halpha D hC.alpha)) :
    ∃ U : Subgroup G, (∀ x, x ∈ U ↔
        x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ∧ x * x = 1) ∧
      ∃ k : ℕ, 2 ≤ k ∧ Nat.card U = 2 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  have hcomm : ∀ x ∈ TG, ∀ y ∈ TG, y * y = 1 → Commute x y := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hy2
    exact (commute_of_mem_sylow_of_mul_self_eq_one hC hH hP T hy (Subtype.ext hy2) hx).map
      (Halpha D hC.alpha).subtype
  let U : Subgroup G :=
    { carrier := {x | x ∈ TG ∧ x * x = 1}
      one_mem' := ⟨TG.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨TG.mul_mem ha hb, ?_⟩
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [(hcomm a ha b hb hb2).eq]
          _ = 1 := by rw [← mul_assoc, ha2, one_mul, hb2]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨TG.inv_mem ha, ?_⟩
        rw [← mul_inv_rev, ha2, inv_one] }
  refine ⟨U, fun x => Iff.rfl, ?_⟩
  have hUT : U ≤ TG := fun x hx => hx.1
  have hU2 : IsPGroup 2 U := (T.isPGroup'.map _).to_le hUT
  obtain ⟨k, hk⟩ := hU2.exists_card_eq
  refine ⟨k, ?_, hk⟩
  have hZO := center_le_oddCore_of_pCore_eq_bot hC hP
  set π := QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Tb := T.mapSurjective hπs
  have hTb : (Tb : Subgroup _) = (T : Subgroup (Halpha D hC.alpha)).map π :=
    Sylow.coe_mapSurjective hπs T
  have h4 := IsBenderGroup.four_le_card_center hH.bender Tb
  have hpre : ∀ z : Subgroup.center (Tb : Subgroup (Halpha D hC.alpha ⧸
      Subgroup.center (Halpha D hC.alpha))), ∃ t : Halpha D hC.alpha,
      t ∈ (T : Subgroup (Halpha D hC.alpha)) ∧ π t = z.1.1 := by
    intro z
    have hz : z.1.1 ∈ (T : Subgroup (Halpha D hC.alpha)).map π := by
      rw [← hTb]
      exact z.1.2
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp hz
    exact ⟨t, ht, hte⟩
  choose f hfT hf using hpre
  have hfU : ∀ z, ((f z : Halpha D hC.alpha) : G) ∈ U := by
    intro z
    refine ⟨Subgroup.mem_map_of_mem _ (hfT z), ?_⟩
    have hz2 := IsBenderGroup.mul_self_eq_one_of_commute hH.bender Tb z.1.2 (fun y hy => by
      have := Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm)
    have hsqZ : f z * f z ∈ Subgroup.center (Halpha D hC.alpha) := by
      rw [← QuotientGroup.eq_one_iff (N := Subgroup.center (Halpha D hC.alpha))]
      change π (f z * f z) = 1
      rw [map_mul, hf z]
      exact hz2
    have hsq : f z * f z = 1 := by
      have hmem : f z * f z ∈ (T : Subgroup (Halpha D hC.alpha)) ⊓
          CFSG.oddCore (Halpha D hC.alpha) :=
        ⟨Subgroup.mul_mem _ (hfT z) (hfT z), hZO hsqZ⟩
      rwa [inf_oddCore_eq_bot_of_isPGroup T.isPGroup', Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hsq
  have hinj : Function.Injective fun z => (⟨(f z : G), hfU z⟩ : U) := by
    intro a b hab
    have h0 : ((f a : Halpha D hC.alpha) : G) = ((f b : Halpha D hC.alpha) : G) :=
      congrArg (fun x : U => (x : G)) hab
    have h1 : f a = f b := Subtype.ext h0
    have h2 := hf a
    rw [h1, hf b] at h2
    exact Subtype.ext (Subtype.ext h2.symm)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hk] at hle
  by_contra hk2
  interval_cases k <;> omega

theorem mem_block_of_commute (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hP : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {γ : Set G} (hγ : γ ∈ blockClass hC.alpha)
    {w w' : G} (hwγ : w ∈ γ) (hw : w ∈ DalphaStar D hC.alpha) (hw' : w' ∈ DalphaStar D hC.alpha)
    (hne : w ≠ w') (hc : Commute w w') : w' ∈ γ := by
  have hwD := DalphaStar_subset hC.isBlock_alpha hw
  have hw'D := DalphaStar_subset hC.isBlock_alpha hw'
  have hwH : w ∈ Halpha D hC.alpha := Subgroup.subset_closure hw
  have hw'H : w' ∈ Halpha D hC.alpha := Subgroup.subset_closure hw'
  have h2 : w * w' * (w * w') = 1 := by
    calc w * w' * (w * w') = w * (w' * w) * w' := by group
      _ = w * (w * w') * w' := by rw [hc.eq]
      _ = 1 := by rw [← mul_assoc, hC.setup.oddT.mul_self_eq_one hwD, one_mul,
          hC.setup.oddT.mul_self_eq_one hw'D]
  have h1 : w * w' ≠ 1 := fun h => hne (hC.setup.oddT.eq_of_mul_eq_one hwD h)
  have hmem := mem_DalphaStar_of_mul_self_eq_one hC hH hP
    ((Halpha D hC.alpha).mul_mem hwH hw'H) h2 h1
  exact mem_block_of_mul_mem hC hH hγ hwγ hwD hw'D hne hc
    (DalphaStar_subset hC.isBlock_alpha hmem)

theorem block_eq_involutions (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hP : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {v : G} (hv : v ∈ β) (T : Sylow 2 (Halpha D hC.alpha))
    (hvT : v ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    β = {x | x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ∧
      x * x = 1 ∧ x ≠ 1} := by
  have hvD : v ∈ D := (mem_Dalpha_iff.mp hβ).2.1 hv
  obtain ⟨v', hv'T, rfl⟩ := Subgroup.mem_map.mp hvT
  have hv'2 : v' * v' = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hvD)
  have hcomm : ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)), Commute t v' := fun t ht =>
    commute_of_mem_sylow_of_mul_self_eq_one hC hH hP T hv'T hv'2 ht
  have hTv : ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)),
      (t : G) * (Halpha D hC.alpha).subtype v' * (t : G)⁻¹ = (Halpha D hC.alpha).subtype v' := by
    intro t ht
    have h := congrArg Subtype.val (hcomm t ht).eq
    simp only [Subgroup.coe_mul] at h
    change (t : G) * v' * (t : G)⁻¹ = v'
    rw [h, mul_inv_cancel_right]
  ext x
  constructor
  · intro hx
    have hxD : x ∈ D := (mem_Dalpha_iff.mp hβ).2.1 hx
    exact ⟨block_subset_sylow hC hH hβ hv T hvT hTv hx, hC.setup.oddT.mul_self_eq_one hxD,
      hC.setup.oddT.ne_one hxD⟩
  · rintro ⟨hxT, hx2, hx1⟩
    obtain ⟨x', hx'T, rfl⟩ := Subgroup.mem_map.mp hxT
    have hxs := mem_DalphaStar_of_mul_self_eq_one hC hH hP x'.2 hx2 hx1
    by_cases hxv : (x' : G) = v'
    · rw [show (Halpha D hC.alpha).subtype x' = (Halpha D hC.alpha).subtype v' from hxv]
      exact hv
    · refine mem_block_of_commute hC hH hP (mem_Dalpha_iff.mp hβ).1 hv
        (subset_DalphaStar hβ hv) hxs (Ne.symm hxv) ?_
      exact ((hcomm x' hx'T).map (Halpha D hC.alpha).subtype).symm

theorem alpha_structure_of_pCore_eq_bot (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hP : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) :
    (∀ a ∈ hC.alpha, ∀ b ∈ hC.alpha, Commute a b) ∧
      (∀ a ∈ hC.alpha, ∀ b ∈ hC.alpha, a ≠ b → a * b ∈ hC.alpha) ∧
      ∃ k : ℕ, 2 ≤ k ∧ hC.alpha.ncard = 2 ^ k - 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hβ⟩ := exists_mem_Dalpha hC
  have hβc := (mem_Dalpha_iff.mp hβ).1
  obtain ⟨v, hv⟩ := blockClass_nonempty hC.isBlock_alpha.nonempty hβc
  have hvH : v ∈ Halpha D hC.alpha := Subgroup.subset_closure (subset_DalphaStar hβ hv)
  have hvD : v ∈ D := (mem_Dalpha_iff.mp hβ).2.1 hv
  have hv2 : IsPGroup 2 (Subgroup.zpowers (⟨v, hvH⟩ : Halpha D hC.alpha)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hC.setup.oddT.orderOf_eq_two hvD
  obtain ⟨T, hT⟩ := hv2.exists_le_sylow
  have hvT : v ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :=
    ⟨⟨v, hvH⟩, hT (Subgroup.mem_zpowers _), rfl⟩
  have hβeq := block_eq_involutions hC hH hP hβ hv T hvT
  obtain ⟨U, hU, k, hk2, hUcard⟩ := exists_omegaOne hC hH hP T
  have hUc : ∀ x ∈ U, ∀ y ∈ U, Commute x y := by
    intro x hx y hy
    have hxy := ((hU _).mp (U.mul_mem hx hy)).2
    have hx2 := ((hU x).mp hx).2
    have hy2 := ((hU y).mp hy).2
    calc x * y = x * (x * y * (x * y)) * y := by rw [hxy, mul_one]
      _ = (x * x) * y * x * (y * y) := by group
      _ = y * x := by rw [hx2, hy2, one_mul, mul_one]
  have hβU : β = (U : Set G) \ {1} := by
    rw [hβeq]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff, hU x]
    tauto
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβc
  have hα : hC.alpha = (fun x => g⁻¹ * x * g) '' β := by
    rw [hg, Set.image_image]
    simp only [show ∀ x : G, g⁻¹ * (g * x * g⁻¹) * g = x from fun x => by group, Set.image_id']
  have hinj : Function.Injective fun x : G => g⁻¹ * x * g := fun a b h => by simpa using h
  refine ⟨?_, ?_, k, hk2, ?_⟩
  · intro a' ha' b' hb'
    rw [hα] at ha' hb'
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨b, hb, rfl⟩ := hb'
    have ha' : a ∈ U := by rw [hβU] at ha; exact ha.1
    have hb' : b ∈ U := by rw [hβU] at hb; exact hb.1
    simpa using (hUc a ha' b hb').conj g⁻¹
  · intro a' ha' b' hb' hne
    rw [hα] at ha' hb' ⊢
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨b, hb, rfl⟩ := hb'
    have hab : a ≠ b := fun h => hne (by rw [h])
    rw [hβU] at ha hb
    refine ⟨a * b, ?_, by group⟩
    rw [hβU]
    refine ⟨U.mul_mem ha.1 hb.1, fun h => hab ?_⟩
    have h1 : a * b = 1 := h
    have ha2 := ((hU a).mp ha.1).2
    calc a = a * (a * b) := by rw [h1, mul_one]
      _ = b := by rw [← mul_assoc, ha2, one_mul]
  · have hUn : (U : Set G).ncard = 2 ^ k := by rw [← Nat.card_coe_set_eq]; exact hUcard
    rw [hα, Set.ncard_image_of_injective _ hinj, hβU,
      Set.ncard_diff_singleton_of_mem (show (1 : G) ∈ (U : Set G) from U.one_mem), hUn]

end CFSG.OddTranspositions.PartThree.Nine

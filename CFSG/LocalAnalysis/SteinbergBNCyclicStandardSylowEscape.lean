module

public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OrderTwoHull

public section

namespace CFSG.LocalAnalysis

open Subgroup
open scoped Pointwise

theorem eq_of_orderOf_eq_two_of_isCyclic_subgroup {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} (hX : IsCyclic X) {a b : G} (ha : a ∈ X) (hb : b ∈ X) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) : a = b := by
  have := Fintype.ofFinite X
  have hx : orderOf (⟨a, ha⟩ : X) = 2 := by rwa [Subgroup.orderOf_mk]
  have hy : orderOf (⟨b, hb⟩ : X) = 2 := by rwa [Subgroup.orderOf_mk]
  have h := IsCyclic.card_orderOf_eq_totient (hx ▸ orderOf_dvd_card : 2 ∣ Fintype.card X)
  rw [Nat.totient_two] at h
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h
  have hxa : (⟨a, ha⟩ : X) ∈ ({c} : Finset X) :=
    hc ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hya : (⟨b, hb⟩ : X) ∈ ({c} : Finset X) :=
    hc ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [Finset.mem_singleton] at hxa hya
  exact congrArg Subtype.val (hxa.trans hya.symm)

theorem cyclic_standard_original_Sylow_conjugate_escape {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htS : t ∈ S) (ht : orderOf t = 2) :
    let C := centralizer (L : Set G)
    let M := normalizer (L : Set G)
    let Sg := (S : Subgroup C).map C.subtype
    ∀ T : Sylow 2 M, Sg ≤ (T : Subgroup M).map M.subtype →
      let T' := (T : Subgroup M).map M.subtype
      ((t : G) ∈ T' ∧ ∀ x ∈ T', x * t = t * x) ∧ T' ≤ centralizer ({(t : G)} : Set G) ∧
      {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} ∩ (T' : Set G) = {(t : G)} ∧
      ∃ g : G, g ∉ M ∧
        let R := Sg.map (MulAut.conj g⁻¹).toMonoidHom ⊓ M
        R ≤ T' ∧ R ≠ ⊥ ∧ IsCyclic R ∧ R ⊓ Sg = ⊥ ∧ g⁻¹ * t * g ∈ R ∧
          orderOf (g⁻¹ * t * g) = 2 ∧ (∀ x ∈ R, orderOf x = 2 → x = g⁻¹ * t * g) ∧
          g⁻¹ * t * g ∈ T' ∧ g⁻¹ * t * g ∉ Sg := by
  intro C M Sg T hST T'
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have hCM : C ≤ M := centralizer_le_normalizer _
  have hSgC : Sg ≤ C := map_subtype_le _
  have htSg : (t : G) ∈ Sg := ⟨t, htS, rfl⟩
  have hSgcyc : IsCyclic Sg := by
    have e : (S : Subgroup C) ≃* Sg :=
      (S : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hCnorm : ∀ m ∈ M, ∀ c ∈ C, m * c * m⁻¹ ∈ C := fun m hm c hc => by
    rw [mem_centralizer_iff] at hc ⊢
    intro l hl
    have hl' : m⁻¹ * l * m⁻¹⁻¹ ∈ L := (mem_normalizer_iff.mp (inv_mem hm) l).mp hl
    rw [inv_inv] at hl'
    have h1 := hc _ hl'
    calc l * (m * c * m⁻¹) = m * ((m⁻¹ * l * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * l * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * l := by group
  have hT'M : T' ≤ M := map_subtype_le _
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map M.subtype
  have hCT : C ⊓ T' = Sg := by
    refine le_antisymm ?_ (le_inf hSgC hST)
    have hQ : IsPGroup 2 ((C ⊓ T').subgroupOf C) :=
      (hT'2.to_le inf_le_right).of_equiv ((subgroupOfEquivOfLe inf_le_left).symm)
    have hSQ : (S : Subgroup C) ≤ (C ⊓ T').subgroupOf C := fun s hs => by
      rw [mem_subgroupOf]
      exact ⟨s.2, hST ⟨s, hs, rfl⟩⟩
    have h1 := S.is_maximal' hQ hSQ
    intro x hx
    have hx' : (⟨x, (mem_inf.mp hx).1⟩ : C) ∈ (C ⊓ T').subgroupOf C := by
      rw [mem_subgroupOf]
      exact hx
    rw [h1] at hx'
    exact ⟨_, hx', rfl⟩
  have hinvol : ∀ x ∈ C, x ∈ T' → orderOf x = 2 → x = t := fun x hxC hxT hx2 => by
    have hx : x ∈ Sg := by rw [← hCT]; exact mem_inf.mpr ⟨hxC, hxT⟩
    exact eq_of_orderOf_eq_two_of_isCyclic_subgroup hSgcyc hx htSg hx2 ht2
  have hcomm : ∀ x ∈ T', x * t = t * x := fun x hx => by
    have h1 : x * t * x⁻¹ = t := hinvol _ (hCnorm x (hT'M hx) t t.2)
      (mul_mem (mul_mem hx (hST htSg)) (inv_mem hx))
      (by rw [show x * (t : G) * x⁻¹ = MulAut.conj x t from rfl, MulEquiv.orderOf_eq, ht2])
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [h1]
  have hTt : T' ≤ centralizer ({(t : G)} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hcomm x hx)
  have hMfus : ∀ m ∈ M, m⁻¹ * t * m ∈ T' → m⁻¹ * t * m = t := fun m hm hmT => by
    have hC1 : m⁻¹ * t * m ∈ C := by
      have h := hCnorm _ (inv_mem hm) t t.2
      rwa [inv_inv] at h
    exact hinvol _ hC1 hmT
      (by rw [show m⁻¹ * (t : G) * m = MulAut.conj m⁻¹ t by simp,
        MulEquiv.orderOf_eq, ht2])
  have hfusset : {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} ∩ (T' : Set G) = {(t : G)} := by
    ext x
    constructor
    · rintro ⟨⟨m, hm, rfl⟩, hx⟩
      exact hMfus m hm hx
    · rintro rfl
      exact ⟨⟨1, one_mem _, by group⟩, hST htSg⟩
  refine ⟨⟨hST htSg, hcomm⟩, hTt, hfusset, ?_⟩
  have ht1 : (t : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hCtM : centralizer ({(t : G)} : Set G) ≤ M :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL t.2 ht2).1
  obtain ⟨x, hxM, hxT, hxt⟩ : ∃ x : G, x ∉ M ∧ x⁻¹ * t * x ∈ T' ∧ x⁻¹ * t * x ≠ t := by
    by_cases hsyl : Nat.card T' = 2 ^ (Nat.card G).factorization 2
    ·
      by_contra hcon
      push Not at hcon
      have hclosed : CFSG.Open.fusionStronglyClosed ((zpowers (t : G) : Subgroup G) : Set G)
          ((Sylow.ofCard T' hsyl : Sylow 2 G) : Subgroup G) := by
        intro a ha g hg
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
        rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · have h1 : (t : G) ^ (j + j) = 1 := by
            rw [← two_mul, zpow_mul, show (t : G) ^ (2 : ℤ) = 1 by
              rw [zpow_two, ← sq, ← ht2, pow_orderOf_eq_one], one_zpow]
          rw [h1, mul_one, inv_mul_cancel]
          exact one_mem _
        · have h1 : (t : G) ^ (2 * j + 1) = t := by
            rw [zpow_add, zpow_mul, show (t : G) ^ (2 : ℤ) = 1 by
              rw [zpow_two, ← sq, ← ht2, pow_orderOf_eq_one], one_zpow, one_mul, zpow_one]
          rw [h1] at hg ⊢
          by_cases hgM : g ∈ M
          · rw [hMfus g hgM hg]
            exact mem_zpowers _
          · by_cases hgt : g⁻¹ * t * g = t
            · rw [hgt]
              exact mem_zpowers _
            · exact absurd (hcon g hgM hg) hgt
      exact CFSG.ShultStronglyClosedTI.no_order_two_strongly_closed hnonab _ (zpowers (t : G))
        (zpowers_le.mpr (hST htSg)) hclosed (by rw [Nat.card_zpowers, ht2])
    ·
      obtain ⟨V, hTV⟩ := hT'2.exists_le_sylow
      have hTVne : T' ≠ (V : Subgroup G) := fun h => hsyl (by rw [h, Sylow.card_eq_multiplicity])
      have hlt : T'.subgroupOf V < ⊤ := by
        refine lt_top_iff_ne_top.mpr fun h => hTVne (le_antisymm hTV fun v hv => ?_)
        have : (⟨v, hv⟩ : V) ∈ T'.subgroupOf V := h ▸ mem_top _
        exact this
      have : Group.IsNilpotent (V : Subgroup G) := V.isPGroup'.isNilpotent
      obtain ⟨y, hyN, hyT⟩ :=
        IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
      have hnorm : ∀ z ∈ T', (y : G) * z * (y : G)⁻¹ ∈ T' ∧ (y : G)⁻¹ * z * y ∈ T' := by
        intro z hz
        have hzV : (⟨z, hTV hz⟩ : V) ∈ T'.subgroupOf V := hz
        have h1 := (mem_normalizer_iff.mp hyN _).mp hzV
        have h2 := (mem_normalizer_iff.mp (inv_mem hyN) _).mp hzV
        rw [inv_inv] at h2
        exact ⟨h1, h2⟩
      have hyM : (y : G) ∉ M := by
        intro hyM
        apply hyT
        set W := T' ⊔ zpowers (y : G)
        have hWV : W ≤ V := sup_le hTV (zpowers_le.mpr y.2)
        have hWM : W ≤ M := sup_le hT'M (zpowers_le.mpr hyM)
        have hW2 : IsPGroup 2 (W.subgroupOf M) :=
          (V.isPGroup'.to_le hWV).of_equiv (subgroupOfEquivOfLe hWM).symm
        have hTW : (T : Subgroup M) ≤ W.subgroupOf M := fun s hs => by
          rw [mem_subgroupOf]
          exact mem_sup_left ⟨s, hs, rfl⟩
        have h1 := T.is_maximal' hW2 hTW
        have hyW : (⟨y, hyM⟩ : M) ∈ W.subgroupOf M := by
          rw [mem_subgroupOf]
          exact mem_sup_right (mem_zpowers _)
        rw [h1] at hyW
        rw [mem_subgroupOf]
        exact ⟨_, hyW, rfl⟩
      refine ⟨y, hyM, (hnorm t (hST htSg)).2, fun hyt => hyM (hCtM ?_)⟩
      rw [mem_centralizer_singleton_iff]
      calc (y : G) * t = y * ((y : G)⁻¹ * t * y) := by rw [hyt]
        _ = t * y := by group
  have hSg2 : IsPGroup 2 Sg := S.isPGroup'.map C.subtype
  set R₀ := Sg.map (MulAut.conj x⁻¹).toMonoidHom ⊓ M with hR₀
  have hR₀2 : IsPGroup 2 (R₀.subgroupOf M) :=
    ((hSg2.map _).to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨P, hP⟩ := hR₀2.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M T P
  have hR₀T : ∀ r ∈ R₀, (m : G)⁻¹ * r * m ∈ T' := by
    intro r hr
    have h1 : (⟨r, (mem_inf.mp hr).2⟩ : M) ∈ (P : Subgroup M) := hP (by
      rw [mem_subgroupOf]
      exact hr)
    rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    refine ⟨_, h1, ?_⟩
    simp [MulAut.smul_def, MulAut.inv_def]
  set g : G := x * m with hg
  have hgM : g ∉ M := fun h => hxM (by
    have := mul_mem h (inv_mem m.2)
    rwa [hg, mul_inv_cancel_right] at this)
  refine ⟨g, hgM, ?_⟩
  intro R
  have hconj : ∀ s : G, (MulAut.conj g⁻¹).toMonoidHom s = (m : G)⁻¹ * (x⁻¹ * s * x) * m :=
    fun s => by simp [hg, mul_assoc]
  have hRT : R ≤ T' := by
    intro y hy
    obtain ⟨⟨s, hs, hsy⟩, hyM⟩ := mem_inf.mp hy
    rw [hconj] at hsy
    have h1 : x⁻¹ * s * x ∈ R₀ := mem_inf.mpr ⟨⟨s, hs, by simp⟩, by
      have h2 := mul_mem (mul_mem m.2 hyM) (inv_mem m.2)
      rwa [← hsy, show (m : G) * ((m : G)⁻¹ * (x⁻¹ * s * x) * m) * (m : G)⁻¹ =
        x⁻¹ * s * x from by group] at h2⟩
    have h3 := hR₀T _ h1
    rw [← hsy]
    exact h3
  set tg := g⁻¹ * t * g with htg
  have htgR : tg ∈ R := by
    refine mem_inf.mpr ⟨⟨t, htSg, by rw [hconj]; simp only [htg, hg]; group⟩, ?_⟩
    have h1 := mul_mem (mul_mem (inv_mem m.2) (hT'M hxT)) m.2
    rwa [show (m : G)⁻¹ * (x⁻¹ * t * x) * m = tg from by simp only [htg, hg]; group] at h1
  have htg2 : orderOf tg = 2 := by
    rw [htg, show g⁻¹ * (t : G) * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht2]
  have htg1 : tg ≠ 1 := fun h => by
    rw [h, orderOf_one] at htg2
    exact absurd htg2 (by norm_num)
  have hSgg : IsCyclic (Sg.map (MulAut.conj g⁻¹).toMonoidHom) := by
    have e : Sg ≃* Sg.map (MulAut.conj g⁻¹).toMonoidHom :=
      Sg.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hRle : R ≤ Sg.map (MulAut.conj g⁻¹).toMonoidHom := inf_le_left
  have hRcyc : IsCyclic R := by
    have e : R.subgroupOf (Sg.map (MulAut.conj g⁻¹).toMonoidHom) ≃* R := subgroupOfEquivOfLe hRle
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hRS : R ⊓ Sg = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    by_contra hy1
    obtain ⟨hyR, hySg⟩ := mem_inf.mp hy
    have hgC : g⁻¹ ∉ normalizer (C : Set G) := by
      rw [hL.2.2.2.1]
      exact fun h => hgM (by have := inv_mem h; rwa [inv_inv] at this)
    have hodd : Odd (Nat.card (C ⊓ C.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G)) :=
      hL.2.2.1 g⁻¹ hgC
    have hyCC : y ∈ C ⊓ C.map (MulAut.conj g⁻¹).toMonoidHom :=
      mem_inf.mpr ⟨hSgC hySg, map_mono hSgC (hRle hyR)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hSg2 ⟨y, hySg⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k ≠ 0 := fun h => hy1 (by rw [h, pow_zero] at hk; exact orderOf_eq_one_iff.mp hk)
    have h2 : 2 ∣ orderOf y := hk ▸ dvd_pow_self 2 hk0
    have h3 : orderOf y ∣ Nat.card (C ⊓ C.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) :=
      Subgroup.orderOf_dvd_natCard _ hyCC
    obtain ⟨j, hj⟩ := hodd
    have := h2.trans h3
    omega
  refine ⟨hRT, fun h => htg1 (by rw [h] at htgR; exact htgR), hRcyc, hRS, htgR, htg2,
    fun y hy hy2 => eq_of_orderOf_eq_two_of_isCyclic_subgroup hSgg (hRle hy) (hRle htgR) hy2 htg2,
    hRT htgR, fun h => htg1 ?_⟩
  have h1 : tg ∈ R ⊓ Sg := mem_inf.mpr ⟨htgR, h⟩
  rw [hRS] at h1
  exact h1

end CFSG.LocalAnalysis

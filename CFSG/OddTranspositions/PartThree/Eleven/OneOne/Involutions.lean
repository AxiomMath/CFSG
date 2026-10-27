module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Frame
import CFSG.OddTranspositions.SixFiveInputs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.SecondKindCentralizer
import CFSG.OddTranspositions.WidthOne

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenOneHyp

variable {hC : HypothesisC D}

private theorem s11v_zpowers_eq_one_or {x y : G} (hx : orderOf x = 2)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf] at hy
  rw [hx] at hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨i, hi, hyi⟩ := hy
  interval_cases i
  · left; simpa using hyi.symm
  · right; simpa using hyi.symm

private theorem s11v_d_not_mem_DalphaStar (hC : HypothesisC D) :
    hC.d ∉ DalphaStar D hC.alpha := by
  rintro ⟨β, hβ, hdβ⟩
  obtain ⟨hclass, -, hne, -⟩ := hβ
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hclass
  have hgN : g ∉ Subgroup.normalizer hC.alpha := by
    intro hgN
    apply hne
    rw [hg]
    exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hgN
  exact (Set.disjoint_left.mp (hC.isBlock_alpha.disjoint_conj hgN) hC.d_mem_alpha)
    (hg ▸ hdβ)

private theorem s11v_mk_d_eq_one (h : ElevenOneHyp hC) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      ⟨hC.d, h.d_mem_Halpha⟩ = 1 := by
  refine (QuotientGroup.eq_one_iff (N := CFSG.solvableRadical (Halpha D hC.alpha))
    ⟨hC.d, h.d_mem_Halpha⟩).mpr ?_
  have hu : (hC.d : G) ∈ Malpha D hC.alpha := by
    rw [h.Malpha_eq]; exact Subgroup.mem_zpowers _
  obtain ⟨m, hm, hmv⟩ := Subgroup.mem_map.mp hu
  have hm' : m = ⟨hC.d, h.d_mem_Halpha⟩ := Subtype.ext hmv
  rw [← hm']; exact hm

private theorem s11v_coset_eq_or_mul (h : ElevenOneHyp hC)
    {a b : Halpha D hC.alpha}
    (hab : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) :
    (a : G) = (b : G) ∨ (a : G) = (b : G) * hC.d := by
  have hmem : a * b⁻¹ ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.solvableRadical (Halpha D hC.alpha)) (a * b⁻¹)]
    show (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) (a * b⁻¹) = 1
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hM : ((a * b⁻¹ : Halpha D hC.alpha) : G) ∈ Malpha D hC.alpha :=
    Subgroup.mem_map.mpr ⟨a * b⁻¹, hmem, rfl⟩
  rw [h.Malpha_eq] at hM
  have hM' : ((a * b⁻¹ : Halpha D hC.alpha) : G) = 1 ∨
      ((a * b⁻¹ : Halpha D hC.alpha) : G) = hC.d :=
    s11v_zpowers_eq_one_or (hC.setup.oddT.1 hC.d hC.hd) hM
  have hcoe : ((a * b⁻¹ : Halpha D hC.alpha) : G) = (a : G) * (b : G)⁻¹ := by simp
  rw [hcoe] at hM'
  have hcenter : (⟨hC.d, h.d_mem_Halpha⟩ : Halpha D hC.alpha) ∈
      Subgroup.center (Halpha D hC.alpha) := by
    rw [← h.center]
    have hu : (hC.d : G) ∈ Malpha D hC.alpha := by
      rw [h.Malpha_eq]; exact Subgroup.mem_zpowers _
    obtain ⟨m, hm, hmv⟩ := Subgroup.mem_map.mp hu
    have hm' : m = ⟨hC.d, h.d_mem_Halpha⟩ := Subtype.ext hmv
    rw [← hm']; exact hm
  rcases hM' with h1 | hd
  · left
    exact mul_inv_eq_one.mp h1
  · right
    have hcomm : hC.d * (b : G) = (b : G) * hC.d := by
      have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcenter b)
      simpa only [Subgroup.coe_mul] using h.symm
    have ha : (a : G) = hC.d * (b : G) := by
      rw [← hd, mul_assoc, inv_mul_cancel, mul_one]
    rw [ha, hcomm]

private theorem s11v_commute_of_commute_mul {a b c : G} (hD : IsOddTransp D)
    (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hab : Commute a b) (hne : a ≠ b)
    (hct : Commute c (a * b)) : Commute c a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : a * a = 1 := hD.mul_self_eq_one ha
  have hb2 : b * b = 1 := hD.mul_self_eq_one hb
  have hc2 : c * c = 1 := hD.mul_self_eq_one hc
  have hca_comm_of_sq : (c * a) * (c * a) = 1 → Commute c a := by
    intro hsq
    show c * a = a * c
    calc c * a = (c * a)⁻¹ := (inv_eq_of_mul_eq_one_right hsq).symm
      _ = a⁻¹ * c⁻¹ := mul_inv_rev c a
      _ = a * c := by rw [inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hc2]
  by_contra hca
  have hm_odd : Odd (orderOf (c * a)) := by
    rcases hD.2 c hc a ha with h2 | ho
    · exact absurd (hca_comm_of_sq (by
        rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp h2)) hca
    · exact ho
  have hm_ne : orderOf (c * a) ≠ 1 := by
    intro h1
    apply hca
    have hca1 : c * a = 1 := orderOf_eq_one_iff.mp h1
    have hc : c = a := by
      calc c = c * 1 := (mul_one c).symm
        _ = c * (a * a) := by rw [ha2]
        _ = (c * a) * a := by rw [mul_assoc]
        _ = 1 * a := by rw [hca1]
        _ = a := one_mul a
    rw [hc]
  have ht2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = ((a * b) * a) * b := (mul_assoc (a * b) a b).symm
      _ = (a * (b * a)) * b := by rw [mul_assoc a b a]
      _ = (a * (a * b)) * b := by rw [← hab.eq]
      _ = ((a * a) * b) * b := by rw [← mul_assoc]
      _ = (1 * b) * b := by rw [ha2]
      _ = 1 := by rw [one_mul, hb2]
  have ht_ne : a * b ≠ 1 := by
    intro h
    apply hne
    have hb : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [inv_eq_of_mul_eq_one_right ha2] at hb
    exact hb.symm
  have ht : orderOf (a * b) = 2 := orderOf_eq_prime (p := 2) (by rw [pow_two]; exact ht2) ht_ne
  have hcat : Commute (c * a) (a * b) :=
    hct.mul_left ((Commute.refl a).mul_right hab)
  have hcop : (orderOf (c * a)).Coprime (orderOf (a * b)) := by
    rw [ht]; exact Odd.coprime_two_right hm_odd
  have hb_eq : b = a * (a * b) := by rw [← mul_assoc, ha2, one_mul]
  have hcb_eq : c * b = (c * a) * (a * b) := by
    conv_lhs => rw [hb_eq]
    exact (mul_assoc c a (a * b)).symm
  have hord : orderOf (c * b) = orderOf (c * a) * 2 := by
    rw [hcb_eq, hcat.orderOf_mul_eq_mul_orderOf_of_coprime hcop, ht]
  have hfin : IsOfFinOrder (c * a) := isOfFinOrder_of_finite _
  have hpos : 0 < orderOf (c * a) := hfin.orderOf_pos
  rcases hD.2 c hc b hb with h | h
  · rw [hord] at h
    have hle := Nat.le_of_dvd (by norm_num) h
    omega
  · rw [hord] at h
    exact Nat.not_odd_iff_even.2 even_two (Nat.odd_mul.1 h).2

private theorem s11v_mem_Halpha_of_mem_D_commute (h : ElevenOneHyp hC) {x : G}
    (hxD : x ∈ D) (hxu : Commute x hC.d) : x ∈ Halpha D hC.alpha := by
  have hx := hC.eq_alpha_union ▸ hxD
  rcases hx with (hxα | hxE) | hxA
  · rw [h.alpha_eq] at hxα
    rw [Set.mem_singleton_iff] at hxα
    rw [hxα]; exact h.d_mem_Halpha
  · exact Subgroup.subset_closure hxE
  · exfalso
    rw [hC.AalphaStar_eq_diff_alpha] at hxA
    exact hxA.1.2 hxu

private theorem s11v_sl25_unique_involution (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
    (hg : g ^ 2 = 1) (hg1 : g ≠ 1) : g = -1 := by
  revert g
  set_option maxRecDepth 100000 in
  decide

private theorem s11v_sq_eq_one_of_orderOf_eq_two {K : Type*} [Group K] {g : K}
    (hg : orderOf g = 2) : g ^ 2 = 1 := by
  have := pow_orderOf_eq_one g
  rwa [hg] at this

private theorem s11v_Malpha_ne_bot (h : ElevenOneHyp hC) : Malpha D hC.alpha ≠ ⊥ := by
  intro hbot
  have hu : hC.d ∈ Malpha D hC.alpha := by
    rw [h.Malpha_eq]; exact Subgroup.mem_zpowers _
  rw [hbot] at hu
  have hd1 : hC.d = 1 := Subgroup.mem_bot.mp hu
  have hord := hC.setup.oddT.1 hC.d hC.hd
  rw [hd1, orderOf_one] at hord
  exact absurd hord (by norm_num)

private theorem s11v_mk_eq_one_of_mem_lift (h : ElevenOneHyp hC)
    {L : Subgroup G} (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
    (hML : Malpha D hC.alpha ≤ L)
    {y : G} (hy : y ∈ Halpha D hC.alpha) (hy2 : orderOf y = 2) (hyL : y ∈ L) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨y, hy⟩ = 1 := by
  have huL : hC.d ∈ L := hML (by rw [h.Malpha_eq]; exact Subgroup.mem_zpowers _)
  have hord_u : orderOf (⟨hC.d, huL⟩ : L) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hC.setup.oddT.1 hC.d hC.hd
  have hord_y : orderOf (⟨y, hyL⟩ : L) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hy2
  have hu2 : (e ⟨hC.d, huL⟩) ^ 2 = 1 := by
    rw [← map_pow, s11v_sq_eq_one_of_orderOf_eq_two hord_u, map_one]
  have hy2' : (e ⟨y, hyL⟩) ^ 2 = 1 := by
    rw [← map_pow, s11v_sq_eq_one_of_orderOf_eq_two hord_y, map_one]
  have hu1 : e ⟨hC.d, huL⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨hC.d, huL⟩ : L) = 1 := e.injective (by rw [h1, map_one])
    have : orderOf (⟨hC.d, huL⟩ : L) = 1 := by rw [h2, orderOf_one]
    rw [hord_u] at this
    exact absurd this (by norm_num)
  have hy1 : e ⟨y, hyL⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨y, hyL⟩ : L) = 1 := e.injective (by rw [h1, map_one])
    have : orderOf (⟨y, hyL⟩ : L) = 1 := by rw [h2, orderOf_one]
    rw [hord_y] at this
    exact absurd this (by norm_num)
  have huel : e ⟨hC.d, huL⟩ = -1 := s11v_sl25_unique_involution _ hu2 hu1
  have hyel : e ⟨y, hyL⟩ = -1 := s11v_sl25_unique_involution _ hy2' hy1
  have heq : (⟨hC.d, huL⟩ : L) = ⟨y, hyL⟩ := e.injective (by rw [huel, hyel])
  have hyd : y = hC.d := (congrArg Subtype.val heq).symm
  have hyu : (⟨y, hy⟩ : Halpha D hC.alpha) = ⟨hC.d, h.d_mem_Halpha⟩ := Subtype.ext hyd
  rw [hyu]; exact s11v_mk_d_eq_one h

private theorem s11v_frame_pair (h : ElevenOneHyp hC)
    {x z : Halpha D hC.alpha} (hx : x ∈ DstarH hC) (hz : z ∈ DstarH hC)
    (hxz : Commute x z) (hne : x ≠ z) :
    ∃ c d : G, c ∈ D ∧ d ∈ D ∧ c ≠ d ∧ Commute c d ∧ (x : G) * (z : G) * hC.d = c * d := by
  have hxD : (x : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hx)
  have hzD : (z : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hz)
  have hx2 : x * x = 1 := by
    apply Subtype.ext
    exact hC.setup.oddT.mul_self_eq_one hxD
  have hz2 : z * z = 1 := by
    apply Subtype.ext
    exact hC.setup.oddT.mul_self_eq_one hzD
  have hxz2 : (x * z) ^ 2 = 1 := by
    rw [pow_two]
    calc (x * z) * (x * z) = ((x * z) * x) * z := (mul_assoc (x * z) x z).symm
      _ = (x * (z * x)) * z := by rw [mul_assoc x z x]
      _ = (x * (x * z)) * z := by rw [← hxz.eq]
      _ = ((x * x) * z) * z := by rw [← mul_assoc]
      _ = (1 * z) * z := by rw [hx2]
      _ = 1 := by rw [one_mul, hz2]
  have hK : IsPGroup 2 (Subgroup.closure ({x, z} : Set (Halpha D hC.alpha))) :=
    CFSG.Timmesfeld.isPGroup_two_closure_pair hx2 hz2 (k := 1) (by
      simpa only [pow_one] using hxz2)
  obtain ⟨T, hKT⟩ := IsPGroup.exists_le_sylow hK
  have hTmap : IsPGroup 2 ((T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype) :=
    T.isPGroup'.map (Halpha D hC.alpha).subtype
  obtain ⟨S, hTmapS⟩ := IsPGroup.exists_le_sylow hTmap
  obtain ⟨v, hv⟩ := h.exists_frame S T hTmapS
  have hxT : x ∈ (T : Subgroup (Halpha D hC.alpha)) :=
    hKT (Subgroup.subset_closure (by simp))
  have hzT : z ∈ (T : Subgroup (Halpha D hC.alpha)) :=
    hKT (Subgroup.subset_closure (by simp))
  have hxS : (x : G) ∈ (S : Subgroup G) :=
    hTmapS (Subgroup.mem_map.mpr ⟨x, hxT, rfl⟩)
  have hzS : (z : G) ∈ (S : Subgroup G) :=
    hTmapS (Subgroup.mem_map.mpr ⟨z, hzT, rfl⟩)
  have hvS : ∀ i, v i ∈ (S : Subgroup G) := by
    intro i
    have hmem : v i ∈ (S : Set G) ∩ D :=
      hv.inter_eq.symm ▸ Set.mem_insert_of_mem _ (Set.mem_range_self i)
    exact hmem.1
  have hxne_u : (x : G) ≠ hC.d := by
    intro hxu
    exact s11v_d_not_mem_DalphaStar hC (hxu ▸ (mem_DstarH_iff hC).mp hx)
  have hzne_u : (z : G) ≠ hC.d := by
    intro hzu
    exact s11v_d_not_mem_DalphaStar hC (hzu ▸ (mem_DstarH_iff hC).mp hz)
  have hxins : (x : G) ∈ insert hC.d (Set.range v) :=
    hv.inter_eq ▸ (⟨hxS, hxD⟩ : (x : G) ∈ (S : Set G) ∩ D)
  have hzins : (z : G) ∈ insert hC.d (Set.range v) :=
    hv.inter_eq ▸ (⟨hzS, hzD⟩ : (z : G) ∈ (S : Set G) ∩ D)
  obtain ⟨i, hi⟩ : ∃ i, v i = (x : G) := by
    rw [Set.mem_insert_iff] at hxins
    rcases hxins with h | h
    · exact absurd h hxne_u
    · exact h
  obtain ⟨j, hj⟩ : ∃ j, v j = (z : G) := by
    rw [Set.mem_insert_iff] at hzins
    rcases hzins with h | h
    · exact absurd h hzne_u
    · exact h
  have hij : i ≠ j := by
    intro hij
    apply hne
    apply Subtype.ext
    rw [← hi, ← hj, hij]
  let s : Finset (Fin 4) := {i, j}
  have hs_card : s.card = 2 := by simp [s, hij]
  have hcard : (sᶜ).card = 2 := by
    rw [Finset.card_compl, hs_card, Fintype.card_fin]
  obtain ⟨k, l, hkl, hkl_eq⟩ := Finset.card_eq_two.mp hcard
  have hks : k ∉ s := Finset.mem_compl.mp (by rw [hkl_eq]; simp)
  have hls : l ∉ s := Finset.mem_compl.mp (by rw [hkl_eq]; simp)
  have his : i ∈ s := by simp [s]
  have hjs : j ∈ s := by simp [s]
  have hki : k ≠ i := fun h => hks (h ▸ his)
  have hkj : k ≠ j := fun h => hks (h ▸ hjs)
  have hli : l ≠ i := fun h => hls (h ▸ his)
  have hlj : l ≠ j := fun h => hls (h ▸ hjs)
  have hik : i ≠ k := fun h => hki h.symm
  have hil : i ≠ l := fun h => hli h.symm
  have hjk : j ≠ k := fun h => hkj h.symm
  have hjl : j ≠ l := fun h => hlj h.symm
  have hunion : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ := by
    have h1 : ({i, j, k, l} : Finset (Fin 4)) = s ∪ sᶜ := by
      ext m
      simp only [s, hkl_eq, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      tauto
    rw [h1, Finset.union_compl]
  have hv_comm : (Set.range v).Pairwise Commute := by
    intro a ha b hb hab
    obtain ⟨m, rfl⟩ := ha
    obtain ⟨n, rfl⟩ := hb
    exact commute_of_mul_mem_of_isPGroup hC.setup.oddT S.isPGroup'
      (DalphaStar_subset hC.isBlock_alpha (hv.mem m))
      (DalphaStar_subset hC.isBlock_alpha (hv.mem n))
      (S.mul_mem (hvS m) (hvS n))
  let V : Subgroup G := Subgroup.closure (Set.range v)
  letI : CommGroup V := Subgroup.closureCommGroupOfComm hv_comm
  let f : Fin 4 → V := fun m => ⟨v m, Subgroup.subset_closure (Set.mem_range_self m)⟩
  let uV : V := ⟨hC.d, by
    rw [← hv.prod_eq]
    exact V.mul_mem (V.mul_mem (V.mul_mem (f 0).2 (f 1).2) (f 2).2) (f 3).2⟩
  have huV : (uV : G) = hC.d := rfl
  have hprod_univ : (∏ m : Fin 4, f m) = uV := by
    rw [Fin.prod_univ_four]
    apply Subtype.ext
    rw [huV]
    simpa only [Subgroup.coe_mul, Subgroup.coe_mk] using hv.prod_eq
  have hprod_ijkl : f i * f j * f k * f l = uV := by
    have hset : ({i, j, k, l} : Finset (Fin 4)) =
        insert i (insert j (insert k (insert l ∅))) := rfl
    have h4 : Finset.prod ({i, j, k, l} : Finset (Fin 4)) f =
        f i * f j * f k * f l := by
      rw [hset, Finset.prod_insert, Finset.prod_insert, Finset.prod_insert, Finset.prod_insert,
        Finset.prod_empty, mul_one]
      · ac_rfl
      all_goals simp [hij, hik, hil, hjk, hjl, hkl]
    rw [← h4, hunion]
    exact hprod_univ
  have hGprod : v i * v j * v k * v l = hC.d := by
    have h := congrArg Subtype.val hprod_ijkl
    rw [huV] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_mk] using h
  have hvi2 : v i * v i = 1 :=
    hC.setup.oddT.mul_self_eq_one (DalphaStar_subset hC.isBlock_alpha (hv.mem i))
  have hvj2 : v j * v j = 1 :=
    hC.setup.oddT.mul_self_eq_one (DalphaStar_subset hC.isBlock_alpha (hv.mem j))
  have hvij : Commute (v i) (v j) :=
    commute_of_mul_mem_of_isPGroup hC.setup.oddT S.isPGroup'
      (DalphaStar_subset hC.isBlock_alpha (hv.mem i))
      (DalphaStar_subset hC.isBlock_alpha (hv.mem j))
      (S.mul_mem (hvS i) (hvS j))
  have ht2 : (v i * v j) * (v i * v j) = 1 := by
    calc (v i * v j) * (v i * v j) = ((v i * v j) * v i) * v j :=
          (mul_assoc (v i * v j) (v i) (v j)).symm
      _ = (v i * (v j * v i)) * v j := by rw [mul_assoc (v i) (v j) (v i)]
      _ = (v i * (v i * v j)) * v j := by rw [← hvij.eq]
      _ = ((v i * v i) * v j) * v j := by rw [← mul_assoc]
      _ = (1 * v j) * v j := by rw [hvi2]
      _ = 1 := by rw [one_mul, hvj2]
  refine ⟨v k, v l, DalphaStar_subset hC.isBlock_alpha (hv.mem k),
    DalphaStar_subset hC.isBlock_alpha (hv.mem l), ?_, ?_, ?_⟩
  · intro h; exact hkl (hv.injective h)
  · exact commute_of_mul_mem_of_isPGroup hC.setup.oddT S.isPGroup'
      (DalphaStar_subset hC.isBlock_alpha (hv.mem k))
      (DalphaStar_subset hC.isBlock_alpha (hv.mem l))
      (S.mul_mem (hvS k) (hvS l))
  · rw [← hi, ← hj]
    have hu_eq : hC.d = v i * v j * (v k * v l) := by rw [hGprod.symm, mul_assoc]
    calc v i * v j * hC.d = v i * v j * (v i * v j * (v k * v l)) := by rw [hu_eq]
      _ = ((v i * v j) * (v i * v j)) * (v k * v l) :=
          (mul_assoc (v i * v j) (v i * v j) (v k * v l)).symm
      _ = 1 * (v k * v l) := by rw [ht2]
      _ = v k * v l := by rw [one_mul]

theorem involution_mem (h : ElevenOneHyp hC) {y : G} (hy : y ∈ Halpha D hC.alpha)
    (hy2 : orderOf y = 2) :
    y ∈ D ∨ ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ Commute a b ∧ y = a * b := by
  by_cases hyq : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨y, hy⟩ = 1
  · have hyM : (⟨y, hy⟩ : Halpha D hC.alpha) ∈ CFSG.solvableRadical (Halpha D hC.alpha) :=
      (QuotientGroup.eq_one_iff (N := CFSG.solvableRadical (Halpha D hC.alpha))
        ⟨y, hy⟩).mp hyq
    have hyMal : y ∈ Malpha D hC.alpha := Subgroup.mem_map.mpr ⟨⟨y, hy⟩, hyM, rfl⟩
    rw [h.Malpha_eq] at hyMal
    rcases s11v_zpowers_eq_one_or (hC.setup.oddT.1 hC.d hC.hd) hyMal with h1 | hd
    · rw [h1, orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    · left; rw [hd]; exact hC.hd
  · have hdvd : orderOf (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        ⟨y, hy⟩) ∣ 2 := by
      have h1 : orderOf (⟨y, hy⟩ : Halpha D hC.alpha) = 2 := by
        rw [← Subgroup.orderOf_coe]; exact hy2
      have h2 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
        ⟨y, hy⟩
      rwa [h1] at h2
    have hord : orderOf (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        ⟨y, hy⟩) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hyq
      · exact h2
    obtain ⟨A, B, hAB⟩ := h.facts.factors
    obtain ⟨-, -, hinf, -, -, -⟩ := h.derived hAB
    rcases hAB.involutions _ hord with hΘ | hprod | hA | hB
    · obtain ⟨x, hx, hxq⟩ := hΘ
      have hxD : (x : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hx)
      rcases s11v_coset_eq_or_mul h (a := ⟨y, hy⟩) (b := x) hxq.symm with h1 | h2
      · left
        have hmem : ((⟨y, hy⟩ : Halpha D hC.alpha) : G) ∈ D := h1.symm ▸ hxD
        simpa using hmem
      · right
        have hxne_u : (x : G) ≠ hC.d := by
          intro hxu
          exact s11v_d_not_mem_DalphaStar hC (hxu ▸ (mem_DstarH_iff hC).mp hx)
        exact ⟨(x : G), hxD, hC.d, hC.hd, hxne_u,
          (hC.DalphaStar_subset_commute ((mem_DstarH_iff hC).mp hx)).2, h2⟩
    · obtain ⟨p, hp, q, hq, hpq_ne, hpq_c, hy_pq⟩ := hprod
      obtain ⟨x, hx, hxq⟩ := hp
      obtain ⟨z, hz, hzq⟩ := hq
      have hxz_c : Commute x z :=
        (h.commute_iff hx hz).mpr (by rw [hxq, hzq]; exact hpq_c)
      have hxz_ne : x ≠ z := by
        intro hxz
        exact hpq_ne (by rw [← hxq, ← hzq, hxz])
      have hyq' : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨y, hy⟩ =
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (x * z) := by
        rw [map_mul, hxq, hzq]; exact hy_pq
      have hxD : (x : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hx)
      have hzD : (z : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hz)
      rcases s11v_coset_eq_or_mul h (a := ⟨y, hy⟩) (b := x * z) hyq' with h1 | h2
      · right
        refine ⟨(x : G), hxD, (z : G), hzD, ?_, ?_, h1⟩
        · intro h; exact hxz_ne (Subtype.ext h)
        · show (x : G) * (z : G) = (z : G) * (x : G)
          exact congrArg Subtype.val hxz_c
      · obtain ⟨c, d, hcD, hdD, hcd_ne, hcd_c, hcd_eq⟩ :=
          s11v_frame_pair h hx hz hxz_c hxz_ne
        right
        have hfin : y = c * d := by
          have h2' : y = (x : G) * (z : G) * hC.d := h2
          rw [h2', hcd_eq]
        exact ⟨c, hcD, d, hdD, hcd_ne, hcd_c, hfin⟩
    · obtain ⟨e⟩ := (h.liftH_equiv hAB (s11v_Malpha_ne_bot h)).1
      have hML : Malpha D hC.alpha ≤ liftH hC A := by rw [← hinf]; exact inf_le_left
      have hyL : y ∈ liftH hC A := Subgroup.mem_map.mpr ⟨⟨y, hy⟩, hA, rfl⟩
      exact absurd (s11v_mk_eq_one_of_mem_lift h e hML hy hy2 hyL) hyq
    · obtain ⟨e⟩ := (h.liftH_equiv hAB (s11v_Malpha_ne_bot h)).2
      have hML : Malpha D hC.alpha ≤ liftH hC B := by rw [← hinf]; exact inf_le_right
      have hyL : y ∈ liftH hC B := Subgroup.mem_map.mpr ⟨⟨y, hy⟩, hB, rfl⟩
      exact absurd (s11v_mk_eq_one_of_mem_lift h e hML hy hy2 hyL) hyq

theorem not_mem_of_not_mem_Halpha (h : ElevenOneHyp hC) {x : G}
    (hx : x ∈ Subgroup.centralizer {hC.d}) (hxH : x ∉ Halpha D hC.alpha) (hx2 : orderOf x = 2) :
    x ∉ D ∧ ¬ ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ Commute a b ∧ x = a * b := by
  have hxu : Commute x hC.d := Subgroup.mem_centralizer_singleton_iff.mp hx
  constructor
  · intro hxD
    exact hxH (s11v_mem_Halpha_of_mem_D_commute h hxD hxu)
  · rintro ⟨a, ha, b, hb, hab_ne, hab_c, hxab⟩
    have huab : Commute hC.d (a * b) := by rw [← hxab]; exact hxu.symm
    have hua : Commute hC.d a :=
      s11v_commute_of_commute_mul hC.setup.oddT ha hb hC.hd hab_c hab_ne huab
    have hub : Commute hC.d b := by
      have hct' : Commute hC.d (b * a) := by rw [← hab_c.eq]; exact huab
      exact s11v_commute_of_commute_mul hC.setup.oddT hb ha hC.hd hab_c.symm hab_ne.symm hct'
    have haH : a ∈ Halpha D hC.alpha := s11v_mem_Halpha_of_mem_D_commute h ha hua.symm
    have hbH : b ∈ Halpha D hC.alpha := s11v_mem_Halpha_of_mem_D_commute h hb hub.symm
    have hxmem : x ∈ Halpha D hC.alpha := by
      rw [hxab]; exact (Halpha D hC.alpha).mul_mem haH hbH
    exact hxH hxmem

end ElevenOneHyp

end CFSG.OddTranspositions.PartThree

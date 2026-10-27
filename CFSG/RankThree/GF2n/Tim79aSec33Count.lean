module

public import CFSG.RankThree.GF2n.Tim79aSec33Defs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem card_sup_le_mul_of_le_normalizer_count33 {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  have e := Subgroup.coe_mul_of_left_le_normalizer_right A B h
  calc Nat.card ↥(A ⊔ B) = Nat.card ↑((A ⊔ B : Subgroup G) : Set G) := rfl
    _ = Nat.card ↑((A : Set G) * (B : Set G)) := by rw [e]
    _ ≤ Nat.card ↑(A : Set G) * Nat.card ↑(B : Set G) := Set.natCard_mul_le
    _ = Nat.card ↥A * Nat.card ↥B := rfl

theorem card_biSup_le_prod_count33 {ι : Type*} [DecidableEq ι] {W : Subgroup G}
    (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (A : ι → Subgroup G) (s : Finset ι)
    (hA : ∀ i ∈ s, A i ≤ W) :
    Nat.card ↥(⨆ i ∈ s, A i) ≤ ∏ i ∈ s, Nat.card ↥(A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.iSup_insert, Finset.prod_insert hj]
    have hAs : ∀ i ∈ s, A i ≤ W := fun i hi => hA i (Finset.mem_insert_of_mem hi)
    have hBW : (⨆ i ∈ s, A i) ≤ W := iSup₂_le hAs
    have hjW : A j ≤ W := hA j (Finset.mem_insert_self j s)
    have hn : A j ≤ Subgroup.normalizer ((⨆ i ∈ s, A i : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        have e : x * b * x⁻¹ = b := by
          rw [hW x (hjW hx) b (hBW hb)]
          group
        rw [e]
        exact hb
      · intro hb
        have h2 := hW x⁻¹ (W.inv_mem (hjW hx)) _ (hBW hb)
        have e : b = x * b * x⁻¹ := by
          calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
            _ = (x * b * x⁻¹) * x⁻¹ * x := by rw [h2]
            _ = x * b * x⁻¹ := by group
        rw [e]
        exact hb
    exact (card_sup_le_mul_of_le_normalizer_count33 hn).trans
      (Nat.mul_le_mul_left _ (ih hAs))

theorem one_add_card_mul_le_card_count33 [Finite G] {ι : Type*} {W : Subgroup G}
    (T : Finset ι) (B : ι → Subgroup G) (a : ℕ) (hBW : ∀ i ∈ T, B i ≤ W)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → B i ⊓ B j = ⊥)
    (hcard : ∀ i ∈ T, Nat.card ↥(B i) = a) :
    1 + T.card * (a - 1) ≤ Nat.card ↥W := by
  classical
  haveI := Fintype.ofFinite G
  have hcardK : ∀ K : Subgroup G, (Finset.univ.filter (· ∈ K)).card = Nat.card ↥K := by
    intro K
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set t : ι → Finset G := fun i => (Finset.univ.filter (· ∈ B i)).erase 1 with ht_def
  set w : Finset G := (Finset.univ.filter (· ∈ W)).erase 1 with hw_def
  have ht : ∀ i ∈ T, (t i).card = a - 1 := by
    intro i hi
    rw [ht_def, Finset.card_erase_of_mem (by simp [(B i).one_mem]), hcardK, hcard i hi]
  have hsub : T.biUnion t ⊆ w := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    simp only [ht_def, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [hw_def, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hx.1, hBW i hi hx.2⟩
  have hdis : (T : Set ι).PairwiseDisjoint t := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    simp only [ht_def, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      at hxi hxj
    have hx : x ∈ B i ⊓ B j := ⟨hxi.2, hxj.2⟩
    rw [hdisj i hi j hj hij] at hx
    exact hxi.1 ((Subgroup.mem_bot).mp hx)
  have h1 : (T.biUnion t).card = T.card * (a - 1) := by
    rw [Finset.card_biUnion hdis, Finset.sum_congr rfl ht, Finset.sum_const, smul_eq_mul]
  have h2 : w.card = Nat.card ↥W - 1 := by
    rw [hw_def, Finset.card_erase_of_mem (by simp [W.one_mem]), hcardK]
  have h3 := Finset.card_le_card hsub
  have h4 : 1 ≤ Nat.card ↥W := Nat.card_pos
  omega

theorem exists_subgroup_commutator_mem_count33 {W W' : Subgroup G} (hW'W : W' ≤ W) :
    ∃ K : Subgroup G, ∀ x, x ∈ K ↔
      x ∈ Subgroup.normalizer (W : Set G) ∧ ∀ w ∈ W, ⁅w, x⁆ ∈ W' := by
  have hconj : ∀ x : G, (∀ w ∈ W, ⁅w, x⁆ ∈ W') → ∀ u ∈ W', x * u * x⁻¹ ∈ W' := by
    intro x hx u hu
    have e : x * u * x⁻¹ = ⁅u, x⁆⁻¹ * u := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact W'.mul_mem (W'.inv_mem (hx u (hW'W hu))) hu
  refine ⟨{ carrier := {x | x ∈ Subgroup.normalizer (W : Set G) ∧ ∀ w ∈ W, ⁅w, x⁆ ∈ W'}
            one_mem' := ⟨Subgroup.one_mem _, fun w _ => by
              rw [commutatorElement_one_right]
              exact W'.one_mem⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨Subgroup.mul_mem _ hxN hyN, fun w hw => ?_⟩
    have e : ⁅w, x * y⁆ = ⁅w, x⁆ * (x * ⁅w, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact W'.mul_mem (hx w hw) (hconj x hx _ (hy w hw))
  · rintro x ⟨hxN, hx⟩
    refine ⟨Subgroup.inv_mem _ hxN, fun w hw => ?_⟩
    have hw1 : x⁻¹ * w * x ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) w).mp hw
      simpa using this
    have e : ⁅w, x⁻¹⁆ = ⁅x⁻¹ * w * x, x⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact W'.inv_mem (hx _ hw1)

theorem card_eq_card_barOf_mul_count33 {V H S : Subgroup G} (hSH : S ≤ H) :
    Nat.card ↥S = Nat.card ↥(barOf V H S) * Nat.card ↥(S ⊓ wOf V H) := by
  set f : ↥S →* Hbar V H := (piBar V H).comp (Subgroup.inclusion hSH)
  have hrange : f.range = barOf V H S := by
    ext y
    rw [MonoidHom.mem_range, mem_barOf_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hSH x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Nat.card ↥f.ker = Nat.card ↥(S ⊓ wOf V H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2,
          (piBar_eq_one_iff (Subgroup.inclusion hSH x.1)).mp (MonoidHom.mem_ker.mp x.2)⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩,
          MonoidHom.mem_ker.mpr ((piBar_eq_one_iff (⟨x.1, hSH x.2.1⟩ : ↥H)).mpr x.2.2)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [← Subgroup.card_ker_mul_card_range f, hrange, hker, mul_comm]

theorem card_Aof_count33 {V H : Subgroup G} {x : G} (hx : x ∈ H) :
    Nat.card ↥(Aof V H x) = Nat.card ↥(V ⊓ wOf V H) := by
  have hW : conjSubgroup x (wOf V H) = wOf V H :=
    mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_wOf V H hx)
  have e : Aof V H x = conjSubgroup x (V ⊓ wOf V H) := by
    rw [conjSubgroup_inf, hW]
    rfl
  rw [e, card_conjSubgroup]

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem exists_Dy_mem_conj_count33 (hc : MinCex M V Q P H) {y : G} (hy : y ∈ xOf V H) :
    ∃ d ∈ Dy V H, (d : Hbar V H) ∈ barOf V H (conjSubgroup y V) := by
  have hVH : V ≤ H := hc.V_le_H
  have hyH : y ∈ H := xOf_le_H hVH hy
  obtain ⟨v, hvV, hvW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  have hwV : y * v * y⁻¹ ∈ conjSubgroup y V := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hvV
  have hwH : y * v * y⁻¹ ∈ H := conjSubgroup_le_of_le_of_mem hVH hyH hwV
  have hwX : y * v * y⁻¹ ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hyH) hwV
  have hwW : y * v * y⁻¹ ∉ wOf V H := by
    intro hwW
    apply hvW
    have := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (H.inv_mem hyH))
      (y * v * y⁻¹)).mp hwW
    simpa [mul_assoc] using this
  have hw1 : y * v * y⁻¹ ≠ 1 := fun h => hwW (h ▸ (wOf V H).one_mem)
  refine ⟨⟨piBar V H ⟨_, hwH⟩, mem_barOf_iff.mpr ⟨⟨_, hwH⟩, hwX, rfl⟩⟩, ?_, ?_⟩
  · exact mem_dbarOf_iff.mpr ⟨⟨_, hwH⟩,
      ⟨hw1, conjSubgroup y V, conjSubgroup_mem_omegaOf hyH, hwV⟩, hwW, rfl⟩
  · exact mem_barOf_iff.mpr ⟨⟨_, hwH⟩, hwV, rfl⟩

theorem imgZ_surjInv_count33 (hc : MinCex M V Q P H) (g : XbarZ V H) :
    imgZ V H (conjSubgroup ((Function.surjInv (xToZ_surjective hc.V_le_H) g :
      ↥(xOf V H)) : G) V) = conjSub (VZ V H) g := by
  rw [imgZ_conj hc.V_le_H, Function.surjInv_eq (xToZ_surjective hc.V_le_H) g]
  rfl

theorem card_wOf_le_pow_count33 (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    {s : Finset (XbarZ V H)} (hs : (⨆ g ∈ s, conjSub (VZ V H) g) = ⊤) :
    Nat.card ↥(wOf V H) ≤ Nat.card ↥(V ⊓ wOf V H) ^ s.card := by
  classical
  have hVH : V ≤ H := hc.V_le_H
  set ℓ := Function.surjInv (xToZ_surjective hVH)
  have hℓX : ∀ g, ((ℓ g : ↥(xOf V H)) : G) ∈ xOf V H := fun g => (ℓ g).2
  have hℓH : ∀ g, ((ℓ g : ↥(xOf V H)) : G) ∈ H := fun g => xOf_le_H hVH (ℓ g).2
  have himg : ∀ g, imgZ V H (conjSubgroup ((ℓ g : ↥(xOf V H)) : G) V) = conjSub (VZ V H) g :=
    hc.imgZ_surjInv_count33
  set S₀ : Subgroup G := ⨆ g ∈ s, conjSubgroup ((ℓ g : ↥(xOf V H)) : G) V
  set W' : Subgroup G := ⨆ g ∈ s, Aof V H ((ℓ g : ↥(xOf V H)) : G)
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hc.Vtilde_ne_bot hd
    have htop : (⊤ : Subgroup (XbarZ V H)) = ⊥ := by
      rw [← hs]
      simp
    exact eq_bot_iff.mpr (le_top.trans htop.le)
  set K₀ : Subgroup (Xbar V H) :=
    (barOf V H (wOf V H ⊔ S₀)).subgroupOf (barOf V H (xOf V H)) with hK₀
  have hmap : K₀.map (projZ V H) = ⊤ := by
    rw [eq_top_iff, ← hs]
    refine iSup₂_le fun g hg => ?_
    rw [← himg g]
    refine Subgroup.map_mono ?_
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact barOf_mono (le_sup_of_le_right (le_iSup₂_of_le g hg le_rfl)) hz
  have hker : (projZ V H).ker = Subgroup.center (Xbar V H) := QuotientGroup.ker_mk' _
  have hK : K₀ ⊔ Subgroup.center (Xbar V H) = ⊤ := by
    have h1 := Subgroup.comap_map_eq (projZ V H) K₀
    rw [hmap, Subgroup.comap_top, hker] at h1
    exact h1.symm
  have hdK : ∃ d ∈ Dy V H, d ∈ K₀ := by
    obtain ⟨g₀, hg₀⟩ := hsne
    obtain ⟨d, hdD, hdV⟩ := hc.exists_Dy_mem_conj_count33 (hℓX g₀)
    refine ⟨d, hdD, ?_⟩
    rw [hK₀, Subgroup.mem_subgroupOf]
    exact barOf_mono (le_sup_of_le_right (le_iSup₂_of_le g₀ hg₀ le_rfl)) hdV
  have hXle : xOf V H ≤ wOf V H ⊔ S₀ := xOf_le_sup_of_sup_center hd hVH le_rfl hK hdK
  have hW'W : W' ≤ wOf V H := iSup₂_le fun g _ => inf_le_right
  obtain ⟨K, hKmem⟩ := exists_subgroup_commutator_mem_count33 hW'W
  have hWK : wOf V H ≤ K := by
    intro x hx
    rw [hKmem]
    refine ⟨H_le_normalizer_wOf V H (wOf_le_H V H hx), fun w hw => ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc.wOf_isElemAbelian.comm hw hx)]
    exact W'.one_mem
  have hVK : ∀ g ∈ s, conjSubgroup ((ℓ g : ↥(xOf V H)) : G) V ≤ K := by
    intro g hg b hb
    have hbH : b ∈ H := conjSubgroup_le_of_le_of_mem hVH (hℓH g) hb
    rw [hKmem]
    refine ⟨H_le_normalizer_wOf V H hbH, fun w hw => ?_⟩
    have h1 : w * b * w⁻¹ ∈ conjSubgroup ((ℓ g : ↥(xOf V H)) : G) V :=
      (hc.wOf_conj_facts (hℓH g)).2.1 w hw b hb
    have h2 : b * w⁻¹ * b⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hbH) w⁻¹).mp
        ((wOf V H).inv_mem hw)
    have hA : ⁅w, b⁆ ∈ Aof V H ((ℓ g : ↥(xOf V H)) : G) := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hb)
      · have e : ⁅w, b⁆ = w * (b * w⁻¹ * b⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact (wOf V H).mul_mem hw h2
    have hle : Aof V H ((ℓ g : ↥(xOf V H)) : G) ≤ W' := le_iSup₂_of_le g hg le_rfl
    exact hle hA
  have hXK : xOf V H ≤ K := hXle.trans (sup_le hWK (iSup₂_le hVK))
  have hcomm : ⁅wOf V H, xOf V H⁆ ≤ W' := by
    rw [Subgroup.commutator_le]
    intro w hw x hx
    exact ((hKmem x).mp (hXK hx)).2 w hw
  rw [hc.commutator_wOf_xOf] at hcomm
  have hc1 : Nat.card ↥(wOf V H) ≤ Nat.card ↥W' := Subgroup.card_le_of_le hcomm
  have hc2 : Nat.card ↥W' ≤ ∏ g ∈ s, Nat.card ↥(Aof V H ((ℓ g : ↥(xOf V H)) : G)) :=
    card_biSup_le_prod_count33 (fun x hx y hy => hc.wOf_isElemAbelian.comm hx hy) _ s
      (fun g _ => inf_le_right)
  have hc3 : ∏ g ∈ s, Nat.card ↥(Aof V H ((ℓ g : ↥(xOf V H)) : G)) =
      Nat.card ↥(V ⊓ wOf V H) ^ s.card := by
    rw [Finset.prod_congr rfl (fun g _ => card_Aof_count33 (hℓH g)), Finset.prod_const]
  rw [← hc3]
  exact hc1.trans hc2

theorem one_add_mul_le_card_wOf_count33 (hc : MinCex M V Q P H) {T : Finset (XbarZ V H)}
    (hT : Set.InjOn (fun g => conjSub (VZ V H) g) (T : Set (XbarZ V H))) :
    1 + T.card * (Nat.card ↥(V ⊓ wOf V H) - 1) ≤ Nat.card ↥(wOf V H) := by
  have hVH : V ≤ H := hc.V_le_H
  set ℓ := Function.surjInv (xToZ_surjective hVH)
  have hℓH : ∀ g, ((ℓ g : ↥(xOf V H)) : G) ∈ H := fun g => xOf_le_H hVH (ℓ g).2
  have himg : ∀ g, imgZ V H (conjSubgroup ((ℓ g : ↥(xOf V H)) : G) V) = conjSub (VZ V H) g :=
    hc.imgZ_surjInv_count33
  refine one_add_card_mul_le_card_count33 T (fun g => Aof V H ((ℓ g : ↥(xOf V H)) : G)) _
    (fun g _ => inf_le_right) ?_ (fun g _ => card_Aof_count33 (hℓH g))
  intro g hg g' hg' hne
  have hne' : conjSubgroup ((ℓ g' : ↥(xOf V H)) : G) V ≠
      conjSubgroup ((ℓ g : ↥(xOf V H)) : G) V := by
    intro heq
    apply hne
    apply hT hg hg'
    change conjSub (VZ V H) g = conjSub (VZ V H) g'
    rw [← himg g, ← himg g', heq]
  have hti := isTI_conjSubgroup hc.ti ((ℓ g : ↥(xOf V H)) : G)
  have e : conjSubgroup (((ℓ g' : ↥(xOf V H)) : G) * ((ℓ g : ↥(xOf V H)) : G)⁻¹)
      (conjSubgroup ((ℓ g : ↥(xOf V H)) : G) V) = conjSubgroup ((ℓ g' : ↥(xOf V H)) : G) V := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
  have hbot := inf_conjSubgroup_eq_bot_of_isTI hti
    (g := ((ℓ g' : ↥(xOf V H)) : G) * ((ℓ g : ↥(xOf V H)) : G)⁻¹) (by rw [e]; exact hne')
  rw [e] at hbot
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ conjSubgroup ((ℓ g : ↥(xOf V H)) : G) V ⊓
      conjSubgroup ((ℓ g' : ↥(xOf V H)) : G) V := ⟨hx.1.1, hx.2.1⟩
  rw [hbot] at hx'
  exact hx'

end MinCex

theorem sec33CountStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec33Setup M V Q P H →
      UnitaryRootFacts (XbarZ V H) (VZ V H) →
      Nat.card ↥V < Nat.card ↥(V ⊓ wOf V H) * Nat.card ↥(V ⊓ wOf V H) := by
  intro G _ _ M V Q P H hs hF
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hd : Sec23Data V H := hs.setup.data
  obtain ⟨k, N, hk1, hkN, ⟨s, hsk, hsT⟩, ⟨T, hTN, hTinj⟩⟩ := hF.count
  have hVq : Nat.card ↥V = Nat.card ↥(barOf V H V) * Nat.card ↥(V ⊓ wOf V H) :=
    card_eq_card_barOf_mul_count33 hc.V_le_H
  have hqZ : Nat.card ↥(VZ V H) = Nat.card ↥(barOf V H V) := hc.card_Vtilde hd
  have ha2 : 1 < Nat.card ↥(V ⊓ wOf V H) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hc.V_inf_wOf_ne_bot
  have hup := hc.card_wOf_le_pow_count33 hd hsT
  have hlow := hc.one_add_mul_le_card_wOf_count33 hTinj
  rw [hTN] at hlow
  rw [hqZ] at hkN
  set a := Nat.card ↥(V ⊓ wOf V H)
  set q := Nat.card ↥(barOf V H V)
  rw [hVq]
  by_contra hlt
  have haq : a ≤ q := Nat.le_of_mul_le_mul_right (not_lt.mp hlt) (by omega)
  have h1 : a ^ s.card ≤ a ^ k := Nat.pow_le_pow_right (by omega) hsk
  have h2 : a ^ k = a * a ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h3 : a ^ (k - 1) ≤ q ^ (k - 1) := Nat.pow_le_pow_left haq _
  have h4 : a ≤ 2 * (a - 1) := by omega
  have h5 : a * a ^ (k - 1) ≤ 2 * (a - 1) * q ^ (k - 1) := Nat.mul_le_mul h4 h3
  have h6 : 2 * (a - 1) * q ^ (k - 1) = (a - 1) * (2 * q ^ (k - 1)) := by ring
  have h7 : (a - 1) * (2 * q ^ (k - 1)) ≤ (a - 1) * N := Nat.mul_le_mul_left _ hkN
  have h8 : N * (a - 1) = (a - 1) * N := mul_comm _ _
  omega

end CFSG.RankThree.GF2n.Tim79a

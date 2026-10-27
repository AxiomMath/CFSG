module

public import CFSG.Quasithin.AppendixH.H15.H157Std

public section

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H153 CFSG.Quasithin.H.Coc24
  CFSG.ASVolI.ChH CFSG.Monster.Code

@[expose] def evenSupp (F : Finset (Fin 24)) : Subgroup (G6.PermMod 24) where
  carrier := {u | u ∈ G6.coreMod 24 ∧ ∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → i ∈ F}
  mul_mem' := by
    intro u v hu hv
    refine ⟨Subgroup.mul_mem (G6.coreMod 24) hu.1 hv.1, fun i hi => ?_⟩
    rw [toAdd_mul, Pi.add_apply] at hi
    by_cases h : Multiplicative.toAdd u i = 0
    · rw [h, zero_add] at hi
      exact hv.2 i hi
    · exact hu.2 i h
  one_mem' := by
    refine ⟨Subgroup.one_mem (G6.coreMod 24), fun i hi => ?_⟩
    rw [toAdd_one] at hi
    exact absurd rfl hi
  inv_mem' := by
    intro u hu
    refine ⟨Subgroup.inv_mem (G6.coreMod 24) hu.1, fun i hi => ?_⟩
    rw [toAdd_inv, Pi.neg_apply] at hi
    exact hu.2 i (neg_ne_zero.mp hi)

theorem mem_evenSupp {F : Finset (Fin 24)} {u : G6.PermMod 24} :
    u ∈ evenSupp F ↔
      u ∈ G6.coreMod 24 ∧ ∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → i ∈ F :=
  Iff.rfl

theorem permAct_tP_eq_self {u : G6.PermMod 24}
    (hsupp : ∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → i ∈ tFix) :
    G6.permAct 24 tP u = u := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  by_cases hi : i ∈ tFix
  · have h1 : tP⁻¹ i = i := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact ((mem_tFix_iff i).1 hi).symm
    rw [h1]
  · have h0i : Multiplicative.toAdd u i = 0 := by
      by_contra h
      exact hi (hsupp i h)
    have h0j : Multiplicative.toAdd u (tP⁻¹ i) = 0 := by
      by_contra h
      have hj : tP⁻¹ i ∈ tFix := hsupp _ h
      have hfix : tP (tP⁻¹ i) = tP⁻¹ i := (mem_tFix_iff _).1 hj
      have hii : i = tP⁻¹ i := by
        rw [← hfix, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
      exact hi (hii.symm ▸ hj)
    rw [h0i, h0j]

theorem not_mem_golayC_of_supp {F : Finset (Fin 24)} (hF : F.card < 8) {u : G6.PermMod 24}
    (hu1 : u ≠ 1) (hsupp : ∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → i ∈ F) :
    u ∉ golayC := by
  intro hu
  have hC : Multiplicative.toAdd u ∈ CFSG.Monster.Code.C := (mem_golayC_iff' u).1 hu
  have hne : Multiplicative.toAdd u ≠ 0 := by
    intro h
    exact hu1 (Multiplicative.toAdd.injective (by rw [h, toAdd_one]))
  have h8 := CFSG.Monster.Code.eight_le_wt hC hne
  have hle := hammingNorm_le_of_support (Multiplicative.toAdd u) F hsupp
  omega

theorem kappa_injOn_evenSupp {F : Finset (Fin 24)} (hF : F.card < 8) {u v : G6.PermMod 24}
    (hu : u ∈ evenSupp F) (hv : v ∈ evenSupp F) (h : cocodeCoords.κ u = cocodeCoords.κ v) :
    u = v := by
  have huv : u * v⁻¹ ∈ evenSupp F :=
    Subgroup.mul_mem (evenSupp F) hu (Subgroup.inv_mem (evenSupp F) hv)
  have hκ : cocodeCoords.κ (u * v⁻¹) = 1 := by
    have h1 : cocodeCoords.κ (u * v⁻¹)
        = cocodeCoords.κ u * cocodeCoords.κ (v⁻¹) := map_mul cocodeCoords.κ u v⁻¹
    have h2 : cocodeCoords.κ (v⁻¹) = (cocodeCoords.κ v)⁻¹ := map_inv cocodeCoords.κ v
    have h3 : cocodeCoords.κ v * (cocodeCoords.κ v)⁻¹ = 1 := mul_inv_cancel (cocodeCoords.κ v)
    rw [h1, h2, h, h3]
  have hgolay : u * v⁻¹ ∈ golayC := (cocodeCoords.ker_iff (u * v⁻¹) huv.1).1 hκ
  by_contra hne
  have hne1 : u * v⁻¹ ≠ 1 := fun h1 => hne (mul_inv_eq_one.mp h1)
  exact (not_mem_golayC_of_supp hF hne1 huv.2) hgolay

theorem kappa_mem_fixW_tA {u : G6.PermMod 24} (hu : u ∈ evenSupp tFix) :
    cocodeCoords.κ u ∈ fixW tA := by
  rw [mem_fixW]
  have h := SecCoords.κ_permAct_rho cocodeCoords AutPerm
    (fun _ hσ => preserves_cocode hσ) tA (mem_evenSupp.1 hu).1
  calc rhoM24 tA (cocodeCoords.κ u)
      = cocodeCoords.κ (G6.permAct 24 (tA : S24) u) := h.symm
    _ = cocodeCoords.κ (G6.permAct 24 tP u) := rfl
    _ = cocodeCoords.κ u := by rw [permAct_tP_eq_self (mem_evenSupp.1 hu).2]

@[expose] def eFix : ↥tFix ≃ Fin 6 where
  toFun i := colOf i.1
  invFun j := ⟨fixPt j, fixPt_mem_tFix j⟩
  left_inv i := by
    apply Subtype.ext
    exact (eq_fixPt_colOf i.2).symm
  right_inv j := colOf_fixPt j

def evenSuppEquiv :
    ↥(evenSupp tFix) ≃ {f : Fin 6 → ZMod 2 // ∑ j, f j = 0} where
  toFun u := ⟨fun j => Multiplicative.toAdd (u : G6.PermMod 24) (fixPt j), by
    have hcore : ∑ i, Multiplicative.toAdd (u : G6.PermMod 24) i = 0 :=
      (G6.mem_coreMod).1 (mem_evenSupp.1 u.2).1
    have hsupp : ∀ i : Fin 24,
        Multiplicative.toAdd (u : G6.PermMod 24) i ≠ 0 → i ∈ tFix :=
      (mem_evenSupp.1 u.2).2
    have h1 : ∑ j : Fin 6, Multiplicative.toAdd (u : G6.PermMod 24) (fixPt j)
        = ∑ i : ↥tFix, Multiplicative.toAdd (u : G6.PermMod 24) i.1 := by
      rw [(Equiv.sum_comp eFix
        (fun j : Fin 6 => Multiplicative.toAdd (u : G6.PermMod 24) (fixPt j))).symm]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [show fixPt (eFix i) = i.1 from (eq_fixPt_colOf i.2).symm])
    have h2 : ∑ i : ↥tFix, Multiplicative.toAdd (u : G6.PermMod 24) i.1
        = ∑ k ∈ tFix, Multiplicative.toAdd (u : G6.PermMod 24) k := by
      rw [Finset.univ_eq_attach tFix]
      exact Finset.sum_attach tFix
        (fun i : Fin 24 => Multiplicative.toAdd (u : G6.PermMod 24) i)
    have h3 : ∑ k ∈ tFix, Multiplicative.toAdd (u : G6.PermMod 24) k
        = ∑ k : Fin 24, Multiplicative.toAdd (u : G6.PermMod 24) k :=
      Finset.sum_subset (Finset.subset_univ tFix) (fun i _ hi => by
        by_contra h
        exact hi (hsupp i h))
    rw [h1, h2, h3, hcore]⟩
  invFun f := ⟨Multiplicative.ofAdd (fun i =>
      if h : i ∈ tFix then f.1 (eFix ⟨i, h⟩) else 0), by
    refine mem_evenSupp.2 ⟨?_, ?_⟩
    · rw [G6.mem_coreMod]
      have hg : Multiplicative.toAdd (Multiplicative.ofAdd (fun i =>
          if h : i ∈ tFix then f.1 (eFix ⟨i, h⟩) else 0)) =
          (fun i => if h : i ∈ tFix then f.1 (eFix ⟨i, h⟩) else 0) :=
        Equiv.apply_symm_apply Multiplicative.toAdd _
      rw [hg]
      have hsum : ∑ i : Fin 24, (if h : i ∈ tFix then f.1 (eFix ⟨i, h⟩) else 0)
          = ∑ i ∈ tFix, (if h : i ∈ tFix then f.1 (eFix ⟨i, h⟩) else 0) :=
        (Finset.sum_subset (Finset.subset_univ tFix) (fun i _ hi => by simp [hi])).symm
      rw [hsum]
      have hcongr : ∑ i ∈ tFix, (if h : i ∈ tFix then f.1 (eFix ⟨i, h⟩) else 0)
          = ∑ i : ↥tFix, f.1 (eFix i) := by
        rw [← Finset.sum_attach tFix
          (fun i : Fin 24 => if h : i ∈ tFix then f.1 (eFix ⟨i, h⟩) else 0),
          Finset.univ_eq_attach tFix]
        exact Finset.sum_congr rfl (fun i _ => by simp [i.2])
      rw [hcongr]
      exact (Equiv.sum_comp eFix f.1).trans f.2
    · intro i hi
      by_cases h : i ∈ tFix
      · exact h
      · simp [h] at hi⟩
  left_inv u := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    have hg : Multiplicative.toAdd (Multiplicative.ofAdd (fun i =>
        if h : i ∈ tFix then Multiplicative.toAdd (u : G6.PermMod 24) (fixPt (eFix ⟨i, h⟩))
        else 0)) =
        (fun i => if h : i ∈ tFix then
          Multiplicative.toAdd (u : G6.PermMod 24) (fixPt (eFix ⟨i, h⟩)) else 0) :=
      Equiv.apply_symm_apply Multiplicative.toAdd _
    rw [hg]
    funext i
    by_cases h : i ∈ tFix
    · rw [dif_pos h]
      rw [show eFix ⟨i, h⟩ = colOf i from rfl, (eq_fixPt_colOf h).symm]
    · rw [dif_neg h]
      have h0 : Multiplicative.toAdd (u : G6.PermMod 24) i = 0 := by
        by_contra h'
        exact h ((mem_evenSupp.1 u.2).2 i h')
      rw [h0]
  right_inv f := by
    apply Subtype.ext
    show (fun j : Fin 6 => Multiplicative.toAdd
        (Multiplicative.ofAdd (fun i => if h : i ∈ tFix then f.1 (eFix ⟨i, h⟩) else 0))
        (fixPt j)) = f.1
    funext j
    rw [show Multiplicative.toAdd (Multiplicative.ofAdd (fun i =>
        if h : i ∈ tFix then f.1 (eFix ⟨i, h⟩) else 0)) =
        (fun i => if h : i ∈ tFix then f.1 (eFix ⟨i, h⟩) else 0) from
      Equiv.apply_symm_apply Multiplicative.toAdd _]
    show (if h : fixPt j ∈ tFix then f.1 (eFix ⟨fixPt j, h⟩) else 0) = f.1 j
    rw [dif_pos (fixPt_mem_tFix j)]
    rw [show eFix ⟨fixPt j, fixPt_mem_tFix j⟩ = j from colOf_fixPt j]

theorem card_evenSupp_tFix : Nat.card ↥(evenSupp tFix) = 32 := by
  rw [Nat.card_congr evenSuppEquiv, Nat.card_eq_fintype_card]
  decide

theorem mem_fixW_tA_iff (w : W11) :
    w ∈ fixW tA ↔ ∃ u : G6.PermMod 24, u ∈ evenSupp tFix ∧ cocodeCoords.κ u = w := by
  haveI : Fintype ↥(evenSupp tFix) := Fintype.ofFinite _
  haveI : Fintype ↥(fixW tA) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(evenSupp tFix) = Fintype.card ↥(fixW tA) := by
    have h1 := card_evenSupp_tFix
    have h2 := card_fixW_tA
    rw [Nat.card_eq_fintype_card] at h1 h2
    rw [h1, h2]
  let f : ↥(evenSupp tFix) → ↥(fixW tA) :=
    fun u => ⟨cocodeCoords.κ u.1, kappa_mem_fixW_tA u.2⟩
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    have h1 : cocodeCoords.κ u.1 = cocodeCoords.κ v.1 := by
      simpa only [f] using congrArg Subtype.val huv
    exact kappa_injOn_evenSupp (F := tFix) (by rw [card_tFix]; norm_num) u.2 v.2 h1
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
  constructor
  · rintro hw
    obtain ⟨u, hu⟩ := hbij.2 ⟨w, hw⟩
    refine ⟨u.1, u.2, ?_⟩
    simpa only [f] using congrArg Subtype.val hu
  · rintro ⟨u, hu, hκ⟩
    rw [← hκ]
    exact kappa_mem_fixW_tA hu

theorem kappa_eY_tFix : eY tFix ∈ evenSupp tFix ∧ cocodeCoords.κ (eY tFix) = z0 := by
  refine ⟨mem_evenSupp.2 ⟨?_, ?_⟩, ?_⟩
  · rw [G6.mem_coreMod, sum_toAdd_eY, card_tFix]
    decide
  · intro i hi
    by_cases h : i ∈ tFix
    · exact h
    · rw [toAdd_eY, if_neg h] at hi
      exact absurd rfl hi
  · have hbits : ∀ i : Fin 24, (i ∈ tFix ↔ (4491298).testBit (i : ℕ) = true) := by
      decide +kernel
    have h : Multiplicative.toAdd (eY tFix) = bvec 24 4491298 := by
      funext i
      rw [toAdd_eY, bvec_apply]
      by_cases hi : i ∈ tFix
      · rw [if_pos hi, if_pos ((hbits i).1 hi)]
      · rw [if_neg hi, if_neg (fun h' => hi ((hbits i).2 h'))]
    have hval : actM ccECols 4491298 = 31 := by decide +kernel
    change Multiplicative.ofAdd (ccE (Multiplicative.toAdd (eY tFix))) = z0
    rw [h, ccE_bvec, hval]
    rfl

theorem mem_fixW_iff_core {y : ↥AutPerm} (hy : Is3A y) (w : W11) :
    w ∈ fixW y ↔ ∃ u : G6.PermMod 24, u ∈ G6.coreMod 24 ∧
      (∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → (y : S24) i = i) ∧ cocodeCoords.κ u = w := by
  obtain ⟨c, hc⟩ := hy
  have hcy : (c : S24) * (y : S24) * (c : S24)⁻¹ = tP := by
    have := congrArg Subtype.val hc
    simpa [tA] using this
  have hiff : w ∈ fixW y ↔ rhoM24 c w ∈ fixW tA := by
    rw [← mem_fixW_conj c y w, hc]
  rw [hiff, mem_fixW_tA_iff]
  constructor
  · rintro ⟨u, hu, hκ⟩
    refine ⟨G6.permAct 24 (c : S24)⁻¹ u, ?_, ?_, ?_⟩
    · exact G6.permAct_mem_coreMod _ (mem_evenSupp.1 hu).1
    · intro i hi
      rw [G6.permAct_apply] at hi
      rw [inv_inv] at hi
      have hci : (c : S24) i ∈ tFix := (mem_evenSupp.1 hu).2 _ hi
      have hfix : tP ((c : S24) i) = (c : S24) i := (mem_tFix_iff _).1 hci
      have h3 : ((c : S24) * (y : S24) * (c : S24)⁻¹) ((c : S24) i) = (c : S24) i := by
        rw [hcy]
        exact hfix
      have h2 : (c : S24) ((y : S24) i) = (c : S24) i := by
        simpa [Equiv.Perm.mul_apply] using h3
      exact (c : S24).injective h2
    · have hk' : cocodeCoords.κ (G6.permAct 24 ((c⁻¹ : ↥AutPerm) : S24) u) = w := by
        rw [SecCoords.κ_permAct_rho cocodeCoords AutPerm
            (fun _ hσ => preserves_cocode hσ) (c⁻¹) (mem_evenSupp.1 hu).1, hκ]
        show (rhoM24 c⁻¹ * rhoM24 c) w = w
        rw [← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      simpa only [Subgroup.coe_inv] using hk'
  · rintro ⟨u, hu_core, hu_supp, hκ⟩
    refine ⟨G6.permAct 24 (c : S24) u, ?_, ?_⟩
    · refine mem_evenSupp.2 ⟨G6.permAct_mem_coreMod _ hu_core, ?_⟩
      intro i hi
      rw [G6.permAct_apply] at hi
      have hyi : (y : S24) ((c : S24)⁻¹ i) = (c : S24)⁻¹ i := hu_supp _ hi
      rw [mem_tFix_iff, ← hcy]
      simp only [Equiv.Perm.mul_apply]
      rw [hyi]
      simp
    · have hk' : cocodeCoords.κ (G6.permAct 24 (c : S24) u) = rhoM24 c w := by
        rw [SecCoords.κ_permAct_rho cocodeCoords AutPerm
            (fun _ hσ => preserves_cocode hσ) c hu_core, hκ]
        rfl
      exact hk'

theorem not_mem_golayC_of_fix {y : ↥AutPerm} (hy : Is3A y) {u : G6.PermMod 24} (hu1 : u ≠ 1)
    (hsupp : ∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → (y : S24) i = i) : u ∉ golayC := by
  refine not_mem_golayC_of_supp (F := Finset.univ.filter fun i : Fin 24 => (y : S24) i = i)
    ?_ hu1 ?_
  · rw [Is3A.card_fixedPoints hy]
    norm_num
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsupp i hi

end CFSG.ASVolI.AppH.H157

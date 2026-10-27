module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Sixteen21
public import CFSG.LocalAnalysis.WeakClosure81.Twelve
public import CFSG.LocalAnalysis.WeakClosure81.W183Mem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem w183l31_normalizes_of_sylow {Y : Type} [Group Y] {T L A : Subgroup Y} (hT : IsPGroup 2 T)
    (hL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hAT : A ≤ T) (hA : IsSylowIn 2 A L) :
    ∀ t ∈ T, t ∈ Subgroup.normalizer (A : Set Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTLp : IsPGroup 2 ↥(T ⊓ L) := hT.to_le inf_le_left
  have hATL : A ≤ T ⊓ L := le_inf hAT hA.le
  have hTL : T ⊓ L ≤ L := inf_le_right
  have hnotdvd : ¬ 2 ∣ A.relIndex (T ⊓ L) := by
    intro hd
    apply hA.not_dvd_relIndex
    rw [← Subgroup.relIndex_mul_relIndex A (T ⊓ L) L hATL hTL]
    exact dvd_mul_of_dvd_left hd _
  have hne : A.relIndex (T ⊓ L) ≠ 0 := fun h0 => hnotdvd (by rw [h0]; exact dvd_zero 2)
  haveI : (A.subgroupOf (T ⊓ L)).FiniteIndex := Subgroup.finiteIndex_iff.mpr hne
  obtain ⟨n, hn⟩ := hTLp.index (A.subgroupOf (T ⊓ L))
  have hn' : A.relIndex (T ⊓ L) = 2 ^ n := hn
  have hn0 : n = 0 := by
    by_contra hkne
    apply hnotdvd
    rw [hn']
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
    rw [pow_succ']
    exact dvd_mul_right 2 _
  have hAeq : A = T ⊓ L := by
    refine le_antisymm hATL ?_
    rw [← Subgroup.relIndex_eq_one, hn', hn0, pow_zero]
  intro t ht
  rw [hAeq, Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht), hL t ht x hx.2⟩, fun hx => ?_⟩
  have hx' : x = t⁻¹ * (t * x * t⁻¹) * t := by group
  rw [hx']
  refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht, ?_⟩
  simpa using hL t⁻¹ (T.inv_mem ht) (t * x * t⁻¹) hx.2

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem w183l31_mem_M_of_normal (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {g : G} (hg : Gam183 V H (eOmegaZ H D.T) i g) (hgT : vInH V H g ≤ D.T)
    (hnorm : ∀ t ∈ M.img D.T, t ∈ Subgroup.normalizer
      ((M.img (vInH V H g) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W))) : g ∈ D.M := by
  refine x.mem_M_of_wClos_normalizes M hg hgT ?_
  intro w hw hwW
  exact hnorm (M.ρ ⟨w, hw⟩) (M.mem_img.2 ⟨⟨w, hw⟩, E3.wClos_le i D.T hwW, rfl⟩)

theorem w183l31_member_eq_V (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) (hgM : g ∈ D.M) :
    vInH V H g = V ∧ Gam183 V H (eOmegaZ H D.T) i 1 := by
  have hVH : V ≤ H := x.hyp.V_le_T.trans x.hyp.hyp171.2.1
  have hgN : g ∈ Subgroup.normalizer (V : Set G) := by
    rw [x.hyp.setting.normalizer_eq]
    exact hgM
  have hconj : conjSubgroup V g = V := conjSubgroup_eq_iff_mem_normalizer.mpr hgN
  refine ⟨?_, ?_⟩
  · unfold vInH
    rw [hconj, inf_eq_left.2 hVH]
  · have hconj1 : conjSubgroup V 1 = conjSubgroup V g := by
      rw [conjSubgroup_one, hconj]
    simpa [Gam183, hconj1] using hg

theorem w183l31_gam183_conj (hV1 : Gam183 V H (eOmegaZ H D.T) i 1) {h : G} (hh : h ∈ H) :
    Gam183 V H (eOmegaZ H D.T) i h := by
  simpa using Gam183.conj (Hyp183.normalizer_eOmegaZ H D.T) hh hV1

theorem w183l31_centralizer_le_conj (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) :
    Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ conjSubgroup D.M g := by
  have hlt : (⊥ : Subgroup G) < eOmegaZ H D.T ⊓ conjSubgroup V₀ g :=
    bot_lt_iff_ne_bot.mpr (x.inf_ne_bot_of_gam183 hg)
  obtain ⟨w, hw, hwbot⟩ := SetLike.exists_of_lt hlt
  have hw1 : w ≠ 1 := fun h => hwbot (Subgroup.mem_bot.mpr h)
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw.1)).trans
    (centralizer_le_conj_M x.hyp.setting x.hyp.ne_bot g hw.2 hw1)

theorem w183l31_inCalO (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hV1 : Gam183 V H (eOmegaZ H D.T) i 1) {h : G} (hh : h ∈ H)
    (hcard : Nat.card ↥(M.img V) = 4)
    (hK : M.img V ⊓ Subgroup.normalizer
      ((M.img (conjSubgroup V h) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥)
    (hK' : M.img (conjSubgroup V h) ⊓ Subgroup.normalizer
      ((M.img V : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥) :
    InCalO 2 D.M V₀ V h := by
  have hVH : V ≤ H := x.hyp.V_le_T.trans x.hyp.hyp171.2.1
  have hHh : conjSubgroup H h = H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hh)
  have hVhH : conjSubgroup V h ≤ H := (E3.conjSubgroup_mono_left h hVH).trans (le_of_eq hHh)
  have hv1 : vInH V H 1 = V := by
    unfold vInH
    rw [conjSubgroup_one, inf_eq_left.2 hVH]
  have hv : vInH V H h = conjSubgroup V h := by
    unfold vInH
    rw [inf_eq_left.2 hVhH]
  have hCE : Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ conjSubgroup D.M h :=
    x.w183l31_centralizer_le_conj (w183l31_gam183_conj hV1 hh)
  have hCEDM : Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ D.M :=
    x.hyp.centralizer_eOmegaZ_le_M
  have hEDM : eOmegaZ H D.T ≤ D.M :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      x.hyp.isElemAbelian_eOmegaZ.1).trans hCEDM
  have hEconj : conjSubgroup (eOmegaZ H D.T) h = eOmegaZ H D.T :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Hyp183.normalizer_eOmegaZ H D.T hh)
  have hCconj : conjSubgroup (Subgroup.centralizer (eOmegaZ H D.T : Set G)) h =
      Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
    rw [E3.conjSubgroup_centralizer, hEconj]
  have hcardVh : Nat.card ↥(M.img (conjSubgroup V h)) = 4 := by
    have hcj : cj (M.ρ ⟨h, hh⟩) (M.img (conjSubgroup V h)) = M.img V := by
      rw [M.img_conj (A := conjSubgroup V h) hVhH ⟨h, hh⟩, conjSubgroup_conjSubgroup,
        mul_inv_cancel, conjSubgroup_one]
    have hcard_cj : Nat.card ↥(cj (M.ρ ⟨h, hh⟩) (M.img (conjSubgroup V h))) =
        Nat.card ↥(M.img (conjSubgroup V h)) := by
      rw [cj]
      exact Subgroup.card_map_of_injective (MulAut.conj (M.ρ ⟨h, hh⟩)).injective
    rw [hcj, hcard] at hcard_cj
    exact hcard_cj.symm
  have hrelC : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex V = 4 := by
    rw [← M.card_img hVH, hcard]
  have h4 : padicValNat 2 4 = 2 := by
    simpa using (padicValNat.prime_pow (p := 2) 2)
  have hmqC : E3.mQuot V (Subgroup.centralizer (eOmegaZ H D.T : Set G)) = 2 := by
    unfold E3.mQuot
    rw [hrelC]
    exact h4
  have hnot_le : ¬ conjSubgroup V h ≤ D.M := by
    intro hle
    have hbot : M.img (conjSubgroup V h) = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      obtain ⟨y, hyS, hyρ⟩ := M.mem_img.1 hr
      have hyM : (y : G) ∈ conjSubgroup D.M 1 := by
        rw [conjSubgroup_one]
        exact hle hyS
      have hnorm := x.hyp.img_normalizer_of_mem_conj M y.2 hyM
      have hnorm' : M.ρ y ∈
          Subgroup.normalizer (M.img V : Set (LGL 2 M.W)) := by
        simpa [hv1] using hnorm
      have hmem : M.ρ y ∈ M.img (conjSubgroup V h) ⊓
          Subgroup.normalizer (M.img V : Set (LGL 2 M.W)) :=
        ⟨by rw [hyρ]; exact hr, hnorm'⟩
      simpa [← hyρ] using (by rw [hK'] at hmem; exact hmem)
    have h41 : (4 : ℕ) = 1 := by rw [← hcardVh, hbot, Subgroup.card_bot]
    exact absurd h41 (by norm_num)
  have hnot_dual : ¬ V ≤ conjSubgroup D.M h := by
    intro hle
    have hbot : M.img V = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      obtain ⟨y, hyS, hyρ⟩ := M.mem_img.1 hr
      have hyM : (y : G) ∈ conjSubgroup D.M h := hle hyS
      have hnorm := x.hyp.img_normalizer_of_mem_conj M y.2 hyM
      have hnorm' : M.ρ y ∈
          Subgroup.normalizer (M.img (conjSubgroup V h) : Set (LGL 2 M.W)) := by
        simpa [hv] using hnorm
      have hmem : M.ρ y ∈ M.img V ⊓
          Subgroup.normalizer (M.img (conjSubgroup V h) : Set (LGL 2 M.W)) :=
        ⟨by rw [hyρ]; exact hr, hnorm'⟩
      simpa [← hyρ] using (by rw [hK] at hmem; exact hmem)
    have h41 : (4 : ℕ) = 1 := by rw [← hcard, hbot, Subgroup.card_bot]
    exact absurd h41 (by norm_num)
  have hmq : E3.mQuot V (conjSubgroup D.M h) ≤ 2 := by
    calc E3.mQuot V (conjSubgroup D.M h)
        = E3.mQuot V (V ⊓ conjSubgroup D.M h) :=
          (mQuot_inf_left V (conjSubgroup D.M h)).symm
      _ ≤ E3.mQuot V (V ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) :=
          E3.mQuot_mono (inf_le_inf_left V hCE)
      _ = E3.mQuot V (Subgroup.centralizer (eOmegaZ H D.T : Set G)) := mQuot_inf_left V _
      _ ≤ 2 := le_of_eq hmqC
  have hmqDual : E3.mQuot (conjSubgroup V h) D.M ≤ 2 := by
    calc E3.mQuot (conjSubgroup V h) D.M
        = E3.mQuot (conjSubgroup V h) (conjSubgroup V h ⊓ D.M) :=
          (mQuot_inf_left (conjSubgroup V h) D.M).symm
      _ ≤ E3.mQuot (conjSubgroup V h)
            (conjSubgroup V h ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) :=
          E3.mQuot_mono (inf_le_inf_left (conjSubgroup V h) hCEDM)
      _ = E3.mQuot (conjSubgroup V h)
            (conjSubgroup (V ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) h) := by
          rw [E3.conjSubgroup_inf, hCconj]
      _ = E3.mQuot V (V ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) :=
          E3.mQuot_conjSubgroup V (V ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) h
      _ = E3.mQuot V (Subgroup.centralizer (eOmegaZ H D.T : Set G)) := mQuot_inf_left V _
      _ ≤ 2 := le_of_eq hmqC
  have hEnonbot : eOmegaZ H D.T ⊓ V₀ ≠ ⊥ := by
    simpa [conjSubgroup_one] using x.inf_ne_bot_of_gam183 hV1
  have hthird : V₀ ≠ ⊥ → V₀ ⊓ conjSubgroup D.M h ≠ ⊥ := fun _ => by
    intro hbot
    refine hEnonbot (le_bot_iff.mp ?_)
    exact (le_inf inf_le_right
      (inf_le_left.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr
        x.hyp.isElemAbelian_eOmegaZ.1).trans hCE))).trans (le_of_eq hbot)
  have hEq : conjSubgroup (eOmegaZ H D.T ⊓ V₀) h = eOmegaZ H D.T ⊓ conjSubgroup V₀ h := by
    rw [E3.conjSubgroup_inf, hEconj]
  have hconj_nonbot : conjSubgroup (eOmegaZ H D.T ⊓ V₀) h ≠ ⊥ := fun hbot =>
    hEnonbot ((conjSubgroup_eq_bot_iff).1 hbot)
  have hthird_dual : V₀ ≠ ⊥ → conjSubgroup V₀ h ⊓ D.M ≠ ⊥ := fun _ => by
    intro hbot
    refine hconj_nonbot (le_bot_iff.mp ?_)
    rw [hEq]
    exact (le_inf inf_le_right (inf_le_left.trans hEDM)).trans (le_of_eq hbot)
  exact ⟨⟨hnot_le, hmq, hthird⟩, ⟨hnot_dual, hmqDual, hthird_dual⟩⟩

theorem w183l31_U_eq (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hV1 : Gam183 V H (eOmegaZ H D.T) i 1) {h : G} (hh : h ∈ H)
    (hcard : Nat.card ↥(M.img V) = 4)
    (hK : M.img V ⊓ Subgroup.normalizer
      ((M.img (conjSubgroup V h) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥) :
    V ⊓ conjSubgroup D.M h = V ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ∧
      E3.mQuot V (conjSubgroup D.M h) = 2 := by
  have hVH : V ≤ H := x.hyp.V_le_T.trans x.hyp.hyp171.2.1
  have hHh : conjSubgroup H h = H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hh)
  have hVhH : conjSubgroup V h ≤ H := (E3.conjSubgroup_mono_left h hVH).trans (le_of_eq hHh)
  have hv : vInH V H h = conjSubgroup V h := by
    unfold vInH
    rw [inf_eq_left.2 hVhH]
  have hCE : Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ conjSubgroup D.M h :=
    x.w183l31_centralizer_le_conj (w183l31_gam183_conj hV1 hh)
  have hle : V ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ V ⊓ conjSubgroup D.M h :=
    inf_le_inf_left V hCE
  have hge : V ⊓ conjSubgroup D.M h ≤ V ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
    rintro u ⟨huV, huM⟩
    have huH : u ∈ H := hVH huV
    have hnorm := x.hyp.img_normalizer_of_mem_conj M huH huM
    have hnorm' : M.ρ ⟨u, huH⟩ ∈
        Subgroup.normalizer (M.img (conjSubgroup V h) : Set (LGL 2 M.W)) := by
      simpa [hv] using hnorm
    have hmem : M.ρ ⟨u, huH⟩ ∈ M.img V ⊓
        Subgroup.normalizer (M.img (conjSubgroup V h) : Set (LGL 2 M.W)) :=
      ⟨M.mem_img.2 ⟨⟨u, huH⟩, huV, rfl⟩, hnorm'⟩
    rw [hK] at hmem
    exact ⟨huV, (M.ρ_eq_one_iff ⟨u, huH⟩).1 (Subgroup.mem_bot.1 hmem)⟩
  refine ⟨le_antisymm hge hle, ?_⟩
  have hrelC : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex V = 4 := by
    rw [← M.card_img hVH, hcard]
  have h4 : padicValNat 2 4 = 2 := by
    simpa using (padicValNat.prime_pow (p := 2) 2)
  calc E3.mQuot V (conjSubgroup D.M h)
      = E3.mQuot V (V ⊓ conjSubgroup D.M h) :=
        (mQuot_inf_left V (conjSubgroup D.M h)).symm
    _ = E3.mQuot V (V ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) := by
        rw [le_antisymm hge hle]
    _ = E3.mQuot V (Subgroup.centralizer (eOmegaZ H D.T : Set G)) := mQuot_inf_left V _
    _ = 2 := by
        unfold E3.mQuot
        rw [hrelC]
        exact h4

private theorem w183l31_normalizer_le_normalizer_centralizer (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
  Subgroup.le_normalizer_of_normal_subgroupOf (H := Subgroup.centralizer (X : Set G))
    (K := Subgroup.normalizer (X : Set G))
    (Subgroup.centralizer_le_normalizer (X : Set G))

private theorem w183l31_mem_sup_of_le_normalizer {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) {x : G} :
    x ∈ A ⊔ C ↔ ∃ a ∈ A, ∃ c ∈ C, a * c = x := by
  constructor
  · intro hx
    have hx' : x ∈ (A : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A C hAC]
      exact hx
    exact Set.mem_mul.mp hx'
  · rintro ⟨a, ha, c, hc, rfl⟩
    show a * c ∈ (↑(A ⊔ C) : Set G)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A C hAC]
    exact Set.mem_mul.mpr ⟨a, ha, c, hc, rfl⟩

theorem w183l31_exists_member_le_T (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {A : Subgroup (LGL 2 M.W)} (hA : A ∈ packFamilyU D V H i M) (hAT : A ≤ M.img D.T) :
    ∃ g : G, Gam183 V H (eOmegaZ H D.T) i g ∧ vInH V H g ≤ D.T ∧ M.img (vInH V H g) = A := by
  obtain ⟨g₀, hg₀, hAeq⟩ := hA
  set Dg : Subgroup G := vInH V H g₀ with hDgdef
  have hAeqD : A = M.img Dg := hAeq.trans (congrArg M.img hDgdef.symm)
  have hAleD : M.img Dg ≤ M.img D.T := hAeqD ▸ hAT
  have hDgH : Dg ≤ H := by rw [hDgdef]; exact inf_le_right
  have hDgab : IsElemAbelian 2 Dg := by
    rw [hDgdef]
    exact (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g₀).mono inf_le_left
  have hDgP : IsPGroup 2 Dg := CFSG.Open.IsElemAbelian.isPGroup hDgab
  set C : Subgroup G := H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) with hCdef
  have hCnormH : H ≤ Subgroup.normalizer (C : Set G) := by
    rw [hCdef]
    exact (le_inf H.le_normalizer
      ((Hyp183.normalizer_eOmegaZ H D.T).trans
        (w183l31_normalizer_le_normalizer_centralizer (eOmegaZ H D.T)))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTC : D.T ≤ Subgroup.normalizer (C : Set G) := x.hyp.hyp171.2.1.trans hCnormH
  have hDgJ : Dg ≤ D.T ⊔ C := by
    intro d hd
    have hdH : d ∈ H := hDgH hd
    have hρd : M.ρ ⟨d, hdH⟩ ∈ M.img D.T :=
      hAleD (M.mem_img.2 ⟨⟨d, hdH⟩, hd, rfl⟩)
    obtain ⟨j, hjT, hjρ⟩ := M.mem_img.1 hρd
    have hρ1 : M.ρ (j⁻¹ * ⟨d, hdH⟩) = 1 := by
      rw [map_mul, map_inv, hjρ, inv_mul_cancel]
    have hmemC : (j : G)⁻¹ * d ∈ C := by
      rw [hCdef]
      refine ⟨H.mul_mem (H.inv_mem j.2) hdH, ?_⟩
      have h1 := (M.ρ_eq_one_iff (j⁻¹ * ⟨d, hdH⟩)).1 hρ1
      simpa using h1
    rw [← mul_inv_cancel_left (j : G) d]
    exact (D.T ⊔ C).mul_mem (Subgroup.mem_sup_left hjT) (Subgroup.mem_sup_right hmemC)
  have hSJ : IsSylowIn 2 D.T (D.T ⊔ C) :=
    isSylowIn_of_le_of_le x.hyp.isSylowIn_T le_sup_left
      (sup_le x.hyp.hyp171.2.1 inf_le_left)
  obtain ⟨y, hyJ, hDy⟩ := E3.exists_le_conj_of_isSylowIn hSJ hDgJ hDgP
  obtain ⟨t, htT, c, hcC, htc⟩ := (w183l31_mem_sup_of_le_normalizer hTC).mp hyJ
  rw [hCdef] at hcC
  have hcH : c ∈ H := hcC.1
  have hcCent : c ∈ Subgroup.centralizer (eOmegaZ H D.T : Set G) := hcC.2
  have hDg_le_c : Dg ≤ conjSubgroup D.T c := by
    have h1 : Dg ≤ conjSubgroup (conjSubgroup D.T t) c := by
      rw [conjSubgroup_conjSubgroup]
      rw [htc]
      exact hDy
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer htT)] at h1
  have hc₀le : conjSubgroup Dg c⁻¹ ≤ D.T :=
    (E3.conjSubgroup_le_iff_le_inv (A := Dg) (B := D.T) (h := c⁻¹)).mpr (by
      simpa using hDg_le_c)
  set g : G := g₀ * c⁻¹ with hgdef
  have hg : Gam183 V H (eOmegaZ H D.T) i g := by
    rw [hgdef]
    exact Gam183.conj (Hyp183.normalizer_eOmegaZ H D.T) (H.inv_mem hcH) hg₀
  have hgT : vInH V H g ≤ D.T := by
    rw [hgdef, vInH_mul g₀ (H.inv_mem hcH), ← hDgdef]
    exact hc₀le
  have hAeqg : M.img (vInH V H g) = A := by
    have h1 : M.img (vInH V H g) = M.img (conjSubgroup Dg c⁻¹) := by
      rw [hgdef, vInH_mul g₀ (H.inv_mem hcH), ← hDgdef]
    have h2 : M.img (conjSubgroup Dg c⁻¹) = A := by
      have hkey := M.img_conj (A := Dg) hDgH ⟨c, hcH⟩
      have hρc : M.ρ ⟨c, hcH⟩ = 1 := (M.ρ_eq_one_iff ⟨c, hcH⟩).2 hcCent
      rw [hρc, cj_one] at hkey
      rw [hAeqD]
      exact hkey.symm
    exact h1.trans h2
  exact ⟨g, hg, hgT, hAeqg⟩

theorem w183l31_img_normal (M : ModDataE H (eOmegaZ H D.T)) {L : Subgroup G} (hLH : L ≤ H)
    (hLn : H ≤ Subgroup.normalizer (L : Set G)) :
    ∀ y ∈ M.img H, ∀ l ∈ M.img L, y * l * y⁻¹ ∈ M.img L := by
  intro y hy l hl
  obtain ⟨j, -, rfl⟩ := M.mem_img.1 hy
  obtain ⟨j', hj'L, rfl⟩ := M.mem_img.1 hl
  refine M.mem_img.2 ⟨j * j' * j⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hLn j.2) (j' : G)).mp hj'L, ?_⟩
  rw [map_mul, map_mul, map_inv]

section Certified


theorem w183l31_hyp64 (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hV1 : Gam183 V H (eOmegaZ H D.T) i 1) {h : G} (hh : h ∈ H)
    (hcard : Nat.card ↥(M.img V) = 4)
    (hK : M.img V ⊓ Subgroup.normalizer
      ((M.img (conjSubgroup V h) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥)
    (hK' : M.img (conjSubgroup V h) ⊓ Subgroup.normalizer
      ((M.img V : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥) :
    Hyp64 2 D.M V₀ V h := by
  have hO : InCalO 2 D.M V₀ V h := x.w183l31_inCalO M hV1 hh hcard hK hK'
  have hm2 : 2 < mBar D.M V₀ V x.hyp.setting.isElemAbelian := by
    have := x.bound
    omega
  exact w183b2_sixteen21 x.h162 x.hyp.setting x.hyp.ne_bot x.mbar hm2 hO

end Certified

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end

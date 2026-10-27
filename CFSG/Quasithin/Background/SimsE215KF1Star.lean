module

public import CFSG.Quasithin.Background.SimsE215KF1
import CFSG.Quasithin.Vol2.Ch3E213MOS2
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Star

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem star_conjSubgroup {M H Y : Subgroup Γ} {g : Γ} (hg : g ∈ H) :
    E2.star M H (conjSubgroup Y g) = conjSubgroup (E2.star M H Y) (E2P.starMap M H ⟨g, hg⟩) := by
  rw [E214E.conjSubgroup_eq_conjSub_inv, E214E.conjSubgroup_eq_conjSub_inv, ← map_inv]
  exact E2.star_conjSub (M := M) (H := H) (X := Y) (g := g⁻¹) (H.inv_mem hg)

theorem star_sup_conjSubgroup {H T M V : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V)
    (hg : g ∈ H) :
    E2.star M H (V ⊔ conjSubgroup V g) =
      E2.star M H V ⊔ conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hg⟩) := by
  have hconjH : conjSubgroup V g ≤ H := by
    rintro x ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) (h.le_H hv)) (H.inv_mem (H.inv_mem hg))
  rw [E2.star_sup h.le_H hconjH, star_conjSubgroup hg]

theorem isSylowTwoOf_star_inf_star {H T M I : Subgroup Γ} (hT : IsSylowTwoOf T H)
    (hIH : I ≤ H) (hTI : IsSylowTwoOf (T ⊓ I) I) :
    IsSylowTwoOf (E2.star M H T ⊓ E2.star M H I) (E2.star M H I) := by
  have hfin : Finite (E2.StarQuot M H) := E2P.finite_starQuot M H
  set ρ : ↥I →* E2.StarQuot M H := (E2P.starMap M H).comp (Subgroup.inclusion hIH) with hρ
  have hrange : ρ.range = E2.star M H I := by
    rw [hρ, MonoidHom.range_comp, E2P.star_def]
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have himage : ((T ⊓ I).subgroupOf I).map ρ = E2.star M H (T ⊓ I) := by
    rw [hρ, E2P.star_def, ← Subgroup.map_map]
    congr 1
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx, rfl⟩
  have hSyl := E2P.isSylowTwoOf_map_hom hTI ρ
  rw [himage, hrange] at hSyl
  have hle : E2.star M H (T ⊓ I) ≤ E2.star M H T ⊓ E2.star M H I :=
    le_inf (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_left))
      (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_right))
  have hT2 : IsPGroup 2 (E2.star M H T) := by
    have hT2' : IsPGroup 2 (T.subgroupOf H) :=
      hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    exact hT2'.map _
  have heq : E2.star M H T ⊓ E2.star M H I = E2.star M H (T ⊓ I) :=
    E2P.eq_of_isSylowTwoOf_le (K := E2.star M H I) hSyl (hT2.to_le inf_le_left) hle inf_le_right
  rw [heq]
  exact hSyl

theorem star_pCoreOf_le {M H I : Subgroup Γ} (hIH : I ≤ H) :
    E2.star M H (pCoreOf 2 I) ≤ pCoreOf 2 (E2.star M H I) := by
  rw [E2P.star_def, ← CFSG.GroupTheory.pCoreOf_subgroupOf 2 hIH, E2P.star_def]
  exact E1.map_pCoreOf_le (E2P.starMap M H) (I.subgroupOf H)

theorem card_star_eq_relIndex {H T M V : Subgroup Γ} (h : E2.Hyp28 H T M V) :
    Nat.card ↥(E2.star M H V) = (V ⊓ pCoreOf 2 H).relIndex V := by
  have hcard : Nat.card ↥(E2.star M H V) = (kerIn M H ⊓ V).relIndex V := by
    rw [E2P.star_def, ← Subgroup.relIndex_ker, E2P.ker_starMap,
      Subgroup.relIndex_subgroupOf h.le_H, ← Subgroup.inf_relIndex_right (kerIn M H) V]
  have hJ : kerIn M H ⊓ V = V ⊓ pCoreOf 2 H := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact ⟨hx.2, h.minParabolic.le_pCoreOf_of_isPGroup_of_le_kerIn
        ((B6.isPGroup_of_isElemAbelian h.elem).to_le inf_le_right) inf_le_left hx⟩
    · intro x hx
      exact ⟨h.minParabolic.pCoreOf_le_kerIn hx.2, hx.1⟩
  rw [hcard, hJ]

omit [Finite Γ] in
theorem conjSubgroup_inf_pCoreOf_eq {I V : Subgroup Γ} {g : Γ} (hg : g ∈ I) :
    conjSubgroup (V ⊓ pCoreOf 2 I) g = conjSubgroup V g ⊓ pCoreOf 2 I := by
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_pCoreOf,
    C5.conjSubgroup_eq_self (Subgroup.le_normalizer hg)]

omit [Finite Γ] in
theorem conjSubgroup_centralizer_of_mem {X : Subgroup Γ} {g : Γ} (hg : g ∈ X) :
    conjSubgroup (Subgroup.centralizer (X : Set Γ)) g = Subgroup.centralizer (X : Set Γ) := by
  rw [C5.conjSubgroup_centralizer, C5.conjSubgroup_eq_self (Subgroup.le_normalizer hg)]

omit [Finite Γ] in
theorem commutator_sup_le_pCoreOf {I A B : Subgroup Γ} (h : A ⊔ B ≤ pCoreOf 2 I) :
    ⁅A ⊔ B, I⁆ ≤ pCoreOf 2 I :=
  (Subgroup.commutator_mono h le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I))

theorem star_inf_pCoreOf_le {M H I X : Subgroup Γ} (hIH : I ≤ H) :
    E2.star M H (X ⊓ pCoreOf 2 I) ≤ E2.star M H X ⊓ pCoreOf 2 (E2.star M H I) :=
  le_inf (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_left))
    ((Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_right)).trans (star_pCoreOf_le hIH))

omit [Finite Γ] in
theorem isMulCommutative_star {M H V : Subgroup Γ} (hV : IsMulCommutative ↥V) :
    IsMulCommutative ↥(E2.star M H V) :=
  IsMulCommutative.of_comm fun a b => Subtype.ext
    (Ch3E213M.OS.star_comm (M := M) (H := H) (V := V)
      (fun v hv w hw => congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : ↥V) ⟨w, hw⟩))
      a.1 a.2 b.1 b.2)

theorem conjSubgroup_inf_pCoreOf_le_centralizer {X : Type} [Group X] {V I : Subgroup X} {g : X}
    (hI : I = V ⊔ conjSubgroup V g) (hV : IsMulCommutative ↥V)
    (hc : ⁅conjSubgroup V g ⊓ pCoreOf 2 I, V⁆ = ⊥) :
    conjSubgroup V g ⊓ pCoreOf 2 I ≤ Subgroup.centralizer (I : Set X) := by
  have hVg : IsMulCommutative ↥(conjSubgroup V g) := isMulCommutative_conjSubgroup hV g
  have hsup : V ⊔ conjSubgroup V g ≤
      Subgroup.centralizer ((conjSubgroup V g ⊓ pCoreOf 2 I : Subgroup X) : Set X) := by
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.mpr
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)
    · exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr hVg).trans
        (Subgroup.centralizer_le (fun x hx => hx.1))
  rw [hI] at hsup ⊢
  exact Subgroup.le_centralizer_iff.mp hsup

theorem star_conjSubgroup_inf_pCoreOf_le_centralizer {H T M V I : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hIH : I ≤ H) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g)
    (hc : ⁅conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hIH hg⟩) ⊓
        pCoreOf 2 (E2.star M H V ⊔ conjSubgroup (E2.star M H V)
          (E2P.starMap M H ⟨g, hIH hg⟩)), E2.star M H V⁆ = ⊥) :
    E2.star M H (conjSubgroup V g ⊓ pCoreOf 2 I) ≤
      Subgroup.centralizer (E2.star M H I : Set (E2.StarQuot M H)) := by
  have hst : E2.star M H I = E2.star M H V ⊔
      conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hIH hg⟩) := by
    rw [hgen]
    exact star_sup_conjSubgroup h (hIH hg)
  have hA : E2.star M H (conjSubgroup V g ⊓ pCoreOf 2 I) ≤
      conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hIH hg⟩) ⊓
        pCoreOf 2 (E2.star M H V ⊔ conjSubgroup (E2.star M H V)
          (E2P.starMap M H ⟨g, hIH hg⟩)) := by
    have h := star_inf_pCoreOf_le (M := M) (H := H) (I := I) (X := conjSubgroup V g) hIH
    rw [star_conjSubgroup (M := M) (H := H) (Y := V) (hIH hg), hst] at h
    exact h
  rw [hst]
  exact hA.trans (conjSubgroup_inf_pCoreOf_le_centralizer
    (I := E2.star M H V ⊔ conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hIH hg⟩))
    (V := E2.star M H V) (g := E2P.starMap M H ⟨g, hIH hg⟩) rfl
    (isMulCommutative_star h.elem.1) hc)

theorem star_inf_pCoreOf_le_centralizer {H T M V I : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hIH : I ≤ H) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g)
    (hc : ⁅conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hIH hg⟩) ⊓
        pCoreOf 2 (E2.star M H V ⊔ conjSubgroup (E2.star M H V)
          (E2P.starMap M H ⟨g, hIH hg⟩)), E2.star M H V⁆ = ⊥) :
    E2.star M H (V ⊓ pCoreOf 2 I) ≤
      Subgroup.centralizer (E2.star M H I : Set (E2.StarQuot M H)) := by
  have hAcent := star_conjSubgroup_inf_pCoreOf_le_centralizer h hIH hg hgen hc
  have hconj : conjSubgroup (V ⊓ pCoreOf 2 I) g = conjSubgroup V g ⊓ pCoreOf 2 I :=
    conjSubgroup_inf_pCoreOf_eq hg
  have hBA := star_conjSubgroup (M := M) (H := H) (Y := V ⊓ pCoreOf 2 I) (hIH hg)
  have hB_eq : E2.star M H (V ⊓ pCoreOf 2 I) =
      conjSubgroup (E2.star M H (conjSubgroup V g ⊓ pCoreOf 2 I))
        (E2P.starMap M H ⟨g, hIH hg⟩)⁻¹ := by
    rw [← hconj, hBA, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  rw [hB_eq]
  refine (C5.conjSubgroup_mono hAcent _).trans ?_
  exact le_of_eq (conjSubgroup_centralizer_of_mem
    ((E2.star M H I).inv_mem (E2.starMap_mem_star (hIH hg) hg)))

omit [Finite Γ] in
theorem star_commutator_le_kerIn {M H X Y : Subgroup Γ} (hXH : X ≤ H) (hYH : Y ≤ H)
    (hC : E2.star M H X ≤ Subgroup.centralizer (E2.star M H Y : Set (E2.StarQuot M H))) :
    ⁅X, Y⁆ ≤ kerIn M H := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxH : x ∈ H := hXH hx
  have hyH : y ∈ H := hYH hy
  have hcomm : E2P.starMap M H ⟨y, hyH⟩ * E2P.starMap M H ⟨x, hxH⟩ =
      E2P.starMap M H ⟨x, hxH⟩ * E2P.starMap M H ⟨y, hyH⟩ :=
    Subgroup.mem_centralizer_iff.mp (hC (E2.starMap_mem_star hxH hx))
      _ (E2.starMap_mem_star hyH hy)
  have hmem : ⁅x, y⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hxH hyH) (H.inv_mem hxH)) (H.inv_mem hyH)
  have h1 : E2P.starMap M H ⟨⁅x, y⁆, hmem⟩ = 1 := by
    have e : (⟨⁅x, y⁆, hmem⟩ : ↥H) = ⁅(⟨x, hxH⟩ : ↥H), (⟨y, hyH⟩ : ↥H)⁆ :=
      Subtype.ext rfl
    rw [e, map_commutatorElement, commutatorElement_def, hcomm.symm]
    group
  have h2 : (⟨⁅x, y⁆, hmem⟩ : ↥H) ∈ (E2P.starMap M H).ker := h1
  rw [E2P.ker_starMap, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem commutator_le_pCoreOf_of_star {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V)
    (hIH : I ≤ H) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g)
    (hc : ⁅conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hIH hg⟩) ⊓
        pCoreOf 2 (E2.star M H V ⊔ conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hIH hg⟩)),
        E2.star M H V⁆ = ⊥) :
    ⁅(conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I), I⁆ ≤ pCoreOf 2 H := by
  set A : Subgroup Γ := conjSubgroup V g ⊓ pCoreOf 2 I with hAdef
  set B : Subgroup Γ := V ⊓ pCoreOf 2 I with hBdef
  have hAcent := star_conjSubgroup_inf_pCoreOf_le_centralizer h hIH hg hgen hc
  have hBcent := star_inf_pCoreOf_le_centralizer h hIH hg hgen hc
  have hABp : A ⊔ B ≤ pCoreOf 2 I := sup_le inf_le_right inf_le_right
  have hABH : A ⊔ B ≤ H :=
    (hABp.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)).trans hIH
  have hABstar : E2.star M H (A ⊔ B) ≤
      Subgroup.centralizer (E2.star M H I : Set (E2.StarQuot M H)) := by
    rw [E2.star_sup (le_sup_left.trans hABH) (le_sup_right.trans hABH)]
    exact sup_le hAcent hBcent
  have hcommJ : ⁅A ⊔ B, I⁆ ≤ kerIn M H :=
    star_commutator_le_kerIn hABH hIH hABstar
  have hcommO : ⁅A ⊔ B, I⁆ ≤ pCoreOf 2 I := commutator_sup_le_pCoreOf hABp
  have hgrp : IsPGroup 2 ↥⁅A ⊔ B, I⁆ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le hcommO
  exact h.minParabolic.le_pCoreOf_of_isPGroup_of_le_kerIn hgrp hcommJ

omit [Finite Γ] in
theorem kerIn_inf_le_kerIn {M H I : Subgroup Γ} (hIH : I ≤ H) :
    kerIn M H ⊓ I ≤ kerIn (M ⊓ I) I := by
  rintro x ⟨hx, hxI⟩
  rw [mem_kerIn]
  intro i hi
  exact ⟨hx i (hIH hi), I.mul_mem (I.mul_mem hi hxI) (I.inv_mem hi)⟩

theorem not_isPGroup_of_odd_dvd_card {X : Type} [Group X] [Finite X] {d : ℕ} (hd : Odd d)
    (hd1 : 1 < d) (h : d ∣ Nat.card X) : ¬ IsPGroup 2 X := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  exact E2.false_of_odd_dvd_two_pow hd hd1 (hn ▸ h)

theorem not_isPGroup_of_isPSL_two_two {X : Type} [Group X] [Finite X] {k : ℕ}
    (h : IsPSL 2 2 k X) (hk : 1 < k) : ¬ IsPGroup 2 X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Ch3E213M.exists_equiv_projectiveSL_of_isPSL h
  have hq : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]
  refine not_isPGroup_of_odd_dvd_card (d := (2 ^ k) ^ 2 - 1) ?_ ?_ ?_
  · rw [hq]
    exact Ch3E213M.odd_two_pow_sub_one (by omega)
  · have h4 : 4 ≤ (2 ^ k) ^ 2 := by
      rw [hq]
      exact le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  · rw [Nat.card_congr e.toEquiv, Ch3E213M.card_projectiveSL_two_pow hK]
    exact ⟨2 ^ k, by rw [mul_comm]⟩

theorem not_isPGroup_of_dihedral {X : Type} [Group X] [Finite X] {p a : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 1 ≤ a) (h : Nonempty (X ≃* DihedralGroup (p ^ a))) :
    ¬ IsPGroup 2 X := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card X = 2 * p ^ a := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  refine not_isPGroup_of_odd_dvd_card (d := p ^ a) (hp.odd_of_ne_two hp2).pow ?_ ?_
  · exact Nat.one_lt_pow (by omega) hp.one_lt
  · rw [hcard]
    exact ⟨2, by rw [mul_comm]⟩

theorem not_isPGroup_of_isSp4Full {X : Type} [Group X] [Finite X] {k : ℕ} (hk : 1 ≤ k)
    (h : IsSp4Full k X) : ¬ IsPGroup 2 X := by
  have hodd : Odd ((2 ^ k) ^ 2 + 1) := by
    have h2 : Even ((2 : ℕ) ^ k) := Even.pow_of_ne_zero ⟨1, by norm_num⟩ (by omega)
    exact (h2.pow_of_ne_zero (n := 2) (by norm_num)).add_one
  refine not_isPGroup_of_odd_dvd_card hodd ?_ ?_
  · have h1 : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  · rcases h with h | ⟨rfl, ⟨e⟩⟩
    · exact E213M.sq_add_one_dvd_card (Or.inl h)
    · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      norm_num

theorem not_isPGroup_suzukiGroup {a : ℕ} {K : Type} [Field K] [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ IsPGroup 2 ↥(CFSG.Blueprint.suzukiGroup a K) := by
  have hcard : Nat.card ↥(CFSG.Blueprint.suzukiGroup a K) =
      ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 *
        (2 ^ (2 * a + 1) - 1) := by
    calc Nat.card ↥(CFSG.Blueprint.suzukiGroup a K)
        = Nat.card ↥(CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
          Nat.card_congr (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup
            hK).toEquiv
      _ = ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 *
            (2 ^ (2 * a + 1) - 1) :=
          CFSG.SectionRank.card_suzukiMatrixGroup (m := a) (by omega)
  refine not_isPGroup_of_odd_dvd_card (d := 2 ^ (2 * a + 1) - 1) ?_ ?_ ?_
  · exact Ch3E213M.odd_two_pow_sub_one (by omega)
  · have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
      le_trans (by norm_num : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  · rw [hcard]
    exact ⟨((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2, by ring⟩

theorem not_isPGroup_of_isSz {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsSz n X) :
    ¬ IsPGroup 2 X := by
  obtain ⟨a, ha, hn, K, _, _, hK, ⟨e⟩⟩ := Ch3E213M.exists_equiv_suzukiGroup_of_isSz h
  intro hP
  exact not_isPGroup_suzukiGroup ha (by rw [← hn]; exact hK) (hP.of_equiv e)

theorem not_isPGroup_star_of_isInIHTV {H T M V I : Subgroup Γ} (hI : IsInIHTV H T M V I) :
    ¬ IsPGroup 2 ↥(E2.star M H I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hIH, -, -, -, _, -, hcases⟩ := hI
  have hcard : Nat.card ↥(E2.star M H I) = (kerIn M H ⊓ I).relIndex I :=
    SimsE210.natCard_star_eq_relIndex hIH
  intro hP
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : Nat.card (E2.StarQuot (M ⊓ I) I) ∣ 2 ^ n := by
    rw [← hn, ← E2.relIndex_kerIn_eq_card, hcard]
    exact Subgroup.relIndex_dvd_of_le_left (L := I) (kerIn_inf_le_kerIn hIH)
  have h2 : IsPGroup 2 (E2.StarQuot (M ⊓ I) I) := IsPGroup.of_card_dvd_pow hdvd
  rcases hcases with ⟨hk1, hY, -⟩ | ⟨-, p, a, hp, hp2, ha, hD⟩ | ⟨-, hk1, hY, -⟩
  · rcases hY with hPSL | hSz
    · exact not_isPGroup_of_isPSL_two_two hPSL hk1 h2
    · exact not_isPGroup_of_isSz hSz h2
  · exact not_isPGroup_of_dihedral hp hp2 ha hD h2
  · exact not_isPGroup_of_isSp4Full hk1 hY h2

theorem kf1All_of_starCentral {H T M V : Subgroup Γ} (h : E2.Hyp28 H T M V)
    (hS : StarCentral H T M V) : KF1All H T M V := by
  obtain ⟨F₀, hFn, hVF, hcent⟩ := hS
  intro I g hI hg hgen
  have hIH : I ≤ H := hI.1
  have hgH : g ∈ H := hIH hg
  have hIstar : E2.star M H I =
      E2.star M H V ⊔ conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hgH⟩) := by
    rw [hgen, star_sup_conjSubgroup h hgH]
  have hSyl : IsSylowTwoOf (E2.star M H T ⊓
      (E2.star M H V ⊔ conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hgH⟩)))
      (E2.star M H V ⊔ conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hgH⟩)) :=
    hIstar ▸ isSylowTwoOf_star_inf_star h.minParabolic.isSylow hIH hI.2.2.1
  exact commutator_le_pCoreOf_of_star h hIH hg hgen
    (commutator_conjSubgroup_inf_pCoreOf_eq_bot_of_normal hFn hVF hcent hSyl)

theorem kf1All_of_relIndex_eq_two {H T M V : Subgroup Γ} (h : E2.Hyp28 H T M V)
    (h2 : (V ⊓ pCoreOf 2 H).relIndex V = 2) : KF1All H T M V := by
  intro I g hI hg hgen
  have hIH : I ≤ H := hI.1
  have hgH : g ∈ H := hIH hg
  have hV2 : Nat.card ↥(E2.star M H V) = 2 := by
    rw [card_star_eq_relIndex h, h2]
  have hgW : E2P.starMap M H ⟨g, hgH⟩ ∈
      E2.star M H V ⊔ conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hgH⟩) := by
    have hmem : E2P.starMap M H ⟨g, hgH⟩ ∈ E2.star M H I := by
      rw [E2P.star_def]
      exact Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    rwa [hgen, star_sup_conjSubgroup h hgH] at hmem
  have hnot : ¬ IsPGroup 2 ↥(E2.star M H V ⊔
      conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hgH⟩)) := by
    rw [← star_sup_conjSubgroup h hgH, ← hgen]
    exact not_isPGroup_star_of_isInIHTV hI
  refine commutator_le_pCoreOf_of_star h hIH hg hgen ?_
  have hG1 : conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hgH⟩) ⊓
      pCoreOf 2 (E2.star M H V ⊔
        conjSubgroup (E2.star M H V) (E2P.starMap M H ⟨g, hgH⟩)) = ⊥ :=
    conjSubgroup_inf_pCoreOf_eq_bot hV2 hgW hnot
  rw [hG1, Subgroup.commutator_bot_left]

theorem starCentral_of_kg1 {H T M V : Subgroup Γ}
    (hY28 : E2.Hyp28 (⊤ : Subgroup (E2.StarQuot M H))
      (E2.star M H T) (E2.star M H M) (E2.star M H V))
    {F₀ : Subgroup (E2.StarQuot M H)} (hF₀ : F₀.Normal)
    (hKG1 : pCoreOf 2 (E2.star M H M) ≤ F₀ ∧
      ∀ x ∈ E2.star M H T ⊓ F₀, x ^ 2 = 1 →
        x ∈ Subgroup.centralizer
          ((E2.star M H T ⊓ F₀ : Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H))) :
    StarCentral H T M V := by
  refine ⟨F₀, hF₀, hY28.le_pCoreOf.trans hKG1.1, ?_⟩
  intro v hv
  exact hKG1.2 v ⟨hY28.le_T hv, hY28.le_pCoreOf.trans hKG1.1 hv⟩ (hY28.elem.2 v hv)

end Star

end CFSG.Quasithin.SimsE2.KF1

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveOrbit
import CFSG.GroupTheory.PerfectSylowCenter
import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveSylow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem mk_pow_orderOf_eq_one {M : Subgroup G} {a : G} (ha : a ∈ M) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) ^ orderOf a = 1 := by
  haveI : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hcoe : orderOf (⟨a, ha⟩ : ↥M) = orderOf a := (Subgroup.orderOf_coe _).symm
  have h : (⟨a, ha⟩ : ↥M) ^ orderOf a = 1 := by
    rw [← hcoe]
    exact pow_orderOf_eq_one _
  rw [← map_pow, h, map_one]

theorem centralizer_mk_eq_map_centralizer_bar2 {M : Subgroup G} {a : G} (ha : a ∈ M)
    (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2) :
    Subgroup.centralizer
        ({(QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩)} : Set (Bar2 M)) =
      (Subgroup.centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
  classical
  haveI : Fact (orderOf a).Prime := ⟨hr⟩
  let N : Subgroup ↥M := CFSG.pCore 2 ↥M
  haveI : N.Normal := CFSG.pCore_normal
  let q : ↥M →* Bar2 M := QuotientGroup.mk' N
  let T : Subgroup ↥M := Subgroup.zpowers (⟨a, ha⟩ : ↥M)
  have hTcard : Nat.card ↥T = orderOf a := by
    rw [show Nat.card ↥T = orderOf (⟨a, ha⟩ : ↥M) from Nat.card_zpowers _]
    exact (Subgroup.orderOf_coe _).symm
  haveI : Fact (IsPGroup (orderOf a) ↥T) :=
    ⟨IsPGroup.of_card (G := ↥T) (n := 1) (by rw [hTcard, pow_one])⟩
  have hcop : Nat.Coprime (orderOf a) (Nat.card N) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [show N = CFSG.pCore 2 ↥M from rfl, hn]
    exact (hr.odd_of_ne_two hr2).coprime_two_right.pow_right n
  have h := CFSG.centralizer_map_quotient_eq_map_centralizer (G := ↥M) (p := orderOf a)
    T N CFSG.pCore_normal hcop
  change Subgroup.centralizer ((T.map q : Subgroup (Bar2 M)) : Set (Bar2 M)) =
    (Subgroup.centralizer (T : Set ↥M)).map q at h
  rw [show T.map q = Subgroup.zpowers (q ⟨a, ha⟩) from MonoidHom.map_zpowers q ⟨a, ha⟩] at h
  simp only [T, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  exact h

theorem isPerfect_barImage_of_mem_calC {M L : Subgroup G} (hL : L ∈ calC M) :
    Group.IsPerfect ↥(barImage M L) := by
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.2.1
  haveI : Group.IsPerfect ↥(L.subgroupOf M) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLM).symm.surjective
  exact Group.IsPerfect.map (H := L.subgroupOf M) (QuotientGroup.mk' (CFSG.pCore 2 ↥M))

theorem map_centralizer_coe_le_centralizer {M : Subgroup G} {a : G} (ha : a ∈ M) :
    (Subgroup.centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M)).map M.subtype ≤
      Subgroup.centralizer ({a} : Set G) := by
  rintro x ⟨c, hc, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hca : (⟨a, ha⟩ : ↥M) * c = c * (⟨a, ha⟩ : ↥M) :=
    Subgroup.mem_centralizer_iff.mp hc ⟨a, ha⟩ (Set.mem_singleton _)
  exact (congrArg Subtype.val hca).symm

private theorem map_perfectResidual_eq_range {W Q : Type*} [Group W] [Finite W] [Group Q]
    (ψ : W →* Q) [Group.IsPerfect ψ.range] :
    (CFSG.perfectResidual W).map ψ = ψ.range := by
  have h := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image
    (homomorphism := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have h' : Subgroup.map ψ.rangeRestrict (CFSG.perfectResidual W) = ⊤ := h
  calc (CFSG.perfectResidual W).map ψ
      = ((CFSG.perfectResidual W).map ψ.rangeRestrict).map ψ.range.subtype := by
        rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
    _ = (⊤ : Subgroup ↥ψ.range).map ψ.range.subtype := by rw [h']
    _ = ψ.range := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem isPerfect_map_perfectResidual_subtype {W : Subgroup G} :
    ⁅(CFSG.perfectResidual ↥W).map W.subtype,
        (CFSG.perfectResidual ↥W).map W.subtype⁆ =
      (CFSG.perfectResidual ↥W).map W.subtype := by
  haveI : Group.IsPerfect ↥(CFSG.perfectResidual ↥W) :=
    CFSG.perfect_residual_characterization.2.2.1
  haveI : Group.IsPerfect ↥((CFSG.perfectResidual ↥W).map W.subtype) :=
    Group.IsPerfect.map (H := CFSG.perfectResidual ↥W) W.subtype
  exact Subgroup.isPerfect_iff.mp inferInstance

private theorem range_orbitDiagonalHom_le_centralizer {M L : Subgroup G} {a : G}
    (hL : L ∈ calC M) (ha : a ∈ M) (hr : (orderOf a).Prime)
    (haL : a ∉ Subgroup.normalizer (L : Set G)) :
    (orbitDiagonalHom (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) (barImage M L)
      (orderOf a) (mk_pow_orderOf_eq_one ha)
      (conjugatesCommute_barImage hL ha hr haL)).range ≤
      Subgroup.centralizer
        ({(QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩)} : Set (Bar2 M)) := by
  rintro z ⟨y, rfl⟩
  exact orbitDiagonalHom_mem_centralizer (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩)
    (barImage M L) (orderOf a) (mk_pow_orderOf_eq_one ha)
    (conjugatesCommute_barImage hL ha hr haL) y

private theorem iSup_conjugatePower_le {M L : Subgroup G} {a : G} (hLM : L ≤ M) (ha : a ∈ M) :
    (⨆ i : Fin (orderOf a), conjugatePower a L i) ≤ M := by
  refine iSup_le fun i => ?_
  rw [conjugatePower]
  refine Subgroup.map_le_iff_le_comap.mpr fun x hx => ?_
  have h : (MulAut.conj (a ^ (i : ℕ))) x = a ^ (i : ℕ) * x * (a ^ (i : ℕ))⁻¹ := by
    rw [MulAut.conj_apply]
  change (MulAut.conj (a ^ (i : ℕ))) x ∈ M
  rw [h]
  exact M.mul_mem (M.mul_mem (M.pow_mem ha (i : ℕ)) (hLM hx))
    (M.inv_mem (M.pow_mem ha (i : ℕ)))

private theorem pCore_le_normalizer_iSup_conjugatePower {M L : Subgroup G} {a : G}
    (hL : L ∈ calC M) (ha : a ∈ M) :
    let X : Subgroup G := ⨆ i : Fin (orderOf a), conjugatePower a L i
    pCoreOf 2 M ≤ Subgroup.normalizer (X : Set G) := by
  intro X
  exact (le_iInf fun i : Fin (orderOf a) =>
      uc22p22u_pCore_normalizes_calC (conjugatePower_mem_calC hL ha i)).trans
    (Subgroup.iInf_normalizer_le_normalizer_iSup
      (fun i : Fin (orderOf a) => conjugatePower a L i))

private theorem range_orbitDiagonalHom_le_map_iSup {M L : Subgroup G} {a : G}
    (hL : L ∈ calC M) (ha : a ∈ M) (hr : (orderOf a).Prime)
    (haL : a ∉ Subgroup.normalizer (L : Set G)) :
    (orbitDiagonalHom (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) (barImage M L)
      (orderOf a) (mk_pow_orderOf_eq_one ha)
      (conjugatesCommute_barImage hL ha hr haL)).range ≤
      ((⨆ i : Fin (orderOf a), conjugatePower a L i).subgroupOf M).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  rintro z ⟨y, rfl⟩
  rw [orbitDiagonalHom_apply]
  refine Subgroup.list_prod_mem (K := ((⨆ i : Fin (orderOf a),
    conjugatePower a L i).subgroupOf M).map q) fun f hf => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn'
    (orbitDiagonalFactor (q ⟨a, ha⟩) (orderOf a) y) f).1 hf
  have hfac : orbitDiagonalFactor (q ⟨a, ha⟩) (orderOf a) y i ∈
      barImage M (conjugatePower a L (i : ℕ)) := by
    rw [barImage_conjugatePower hLM ha (i : ℕ)]
    exact orbitDiagonalFactor_mem_conjugatePower (q ⟨a, ha⟩) (barImage M L)
      (orderOf a) y i
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono M
    (le_iSup (fun i : Fin (orderOf a) => conjugatePower a L i) i)) hfac

private theorem perfect_le_iSup_of_map_le {M L : Subgroup G} {a : G} {D : Subgroup G}
    (hL : L ∈ calC M) (ha : a ∈ M) (hDM : D ≤ M) (hDperf : ⁅D, D⁆ = D)
    (hmap : (D.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ≤
      ((⨆ i : Fin (orderOf a), conjugatePower a L i).subgroupOf M).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) :
    D ≤ ⨆ i : Fin (orderOf a), conjugatePower a L i := by
  classical
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let X : Subgroup G := ⨆ i : Fin (orderOf a), conjugatePower a L i
  let Y : Subgroup G := X ⊔ pCoreOf 2 M
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hXM : X ≤ M := by simpa only [X] using iSup_conjugatePower_le hLM ha
  have hXY : X ≤ Y := le_sup_left
  have hpcX : pCoreOf 2 M ≤ Subgroup.normalizer (X : Set G) := by
    simpa only [X] using pCore_le_normalizer_iSup_conjugatePower hL ha
  have hYN : Y ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hpcX
  haveI hNX : (X.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr hYN
  have hDsubX : D.subgroupOf M ≤ (X.subgroupOf M) ⊔ CFSG.pCore 2 ↥M := by
    have h1 := (Subgroup.map_le_iff_le_comap.mp hmap)
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  have hDY : D ≤ Y := by
    have h1 := Subgroup.map_mono (f := M.subtype) hDsubX
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDM,
      Subgroup.map_subgroupOf_eq_of_le hXM] at h1
  haveI hSolv : Group.IsSolvable ↥((pCoreOf 2 M).subgroupOf Y) := by
    haveI : Group.IsSolvable ↥(pCoreOf 2 M) := uc22p22u_isSolvable_pCoreOf M
    let e := Subgroup.subgroupOfEquivOfLe (show pCoreOf 2 M ≤ Y from le_sup_right)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom)
      (fun x y h => e.injective h)
  haveI hPerf : Group.IsPerfect ↥(D.subgroupOf Y) := by
    haveI : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hDperf
    let e := Subgroup.subgroupOfEquivOfLe hDY
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
      (fun x => ⟨e x, by simp⟩)
  have htop : (X.subgroupOf Y) ⊔ ((pCoreOf 2 M).subgroupOf Y) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXY le_sup_right]
    simpa only [Y] using Subgroup.subgroupOf_self (X ⊔ pCoreOf 2 M)
  have h := CFSG.ClassicalInvolution.LBalanceProof.perfect_le_of_le_sup_solvable
    (P := D.subgroupOf Y) (N := X.subgroupOf Y) (S := (pCoreOf 2 M).subgroupOf Y)
    (by rw [htop]; exact le_top)
  intro d hd
  have hdY : d ∈ Y := hDY hd
  have hmem : (⟨d, hdY⟩ : ↥Y) ∈ D.subgroupOf Y := hd
  exact h hmem

private theorem map_subgroupOf_diagonalPreimage_eq {M : Subgroup G} {a : G} (ha : a ∈ M)
    (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2) {E : Subgroup (Bar2 M)}
    (hE : E ≤ Subgroup.centralizer
      ({(QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩)} : Set (Bar2 M))) :
    (((Subgroup.centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M)).map M.subtype ⊓
      barPreimage M E).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) = E := by
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  apply le_antisymm
  · rintro z ⟨x, hx, rfl⟩
    have hxW : (x : G) ∈ (Subgroup.centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M)).map
        M.subtype ⊓ barPreimage M E := hx
    exact (uc22p21c_mem_barPreimage.mp hxW.2).2
  · intro y hy
    have hyCM : y ∈ (Subgroup.centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M)).map q := by
      rw [← centralizer_mk_eq_map_centralizer_bar2 ha hr hr2]
      exact hE hy
    obtain ⟨c, hc, hq⟩ := Subgroup.mem_map.mp hyCM
    refine ⟨c, Subgroup.mem_subgroupOf.mpr ?_, hq⟩
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem M.subtype hc, ?_⟩
    rw [uc22p21c_mem_barPreimage]
    exact ⟨c.2, by rw [hq]; exact hy⟩

private theorem subgroupOf_map_subtype_map_eq {M : Subgroup G} {DM : Subgroup ↥M}
    {q : ↥M →* Bar2 M} :
    ((DM.map M.subtype).subgroupOf M).map q = DM.map q := by
  rw [← Subgroup.comap_subtype]
  rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective DM]

private theorem exists_perfect_map_diagonal {M L : Subgroup G} {a : G} (hL : L ∈ calC M)
    (ha : a ∈ M) (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2)
    (haL : a ∉ Subgroup.normalizer (L : Set G)) :
    ∃ D : Subgroup G, D ≤ M ∧ D ≤ Subgroup.centralizer ({a} : Set G) ∧ ⁅D, D⁆ = D ∧
      (D.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) =
        (orbitDiagonalHom (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) (barImage M L)
          (orderOf a) (mk_pow_orderOf_eq_one ha)
          (conjugatesCommute_barImage hL ha hr haL)).range := by
  classical
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let δ : ↥(barImage M L) →* Bar2 M :=
    orbitDiagonalHom (q ⟨a, ha⟩) (barImage M L) (orderOf a) (mk_pow_orderOf_eq_one ha)
      (conjugatesCommute_barImage hL ha hr haL)
  let E : Subgroup (Bar2 M) := δ.range
  let W : Subgroup G :=
    (Subgroup.centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M)).map M.subtype ⊓ barPreimage M E
  have hWM : W ≤ M := inf_le_of_left_le
    (Subgroup.map_subtype_le (K := Subgroup.centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M)))
  let ψ : ↥W →* Bar2 M := q.comp (Subgroup.inclusion hWM)
  let DM : Subgroup ↥M := (CFSG.perfectResidual ↥W).map (Subgroup.inclusion hWM)
  let D : Subgroup G := DM.map M.subtype
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hCMa := map_centralizer_coe_le_centralizer ha
  have hWcent : W ≤ Subgroup.centralizer ({a} : Set G) :=
    inf_le_left.trans hCMa
  have hEcent := range_orbitDiagonalHom_le_centralizer hL ha hr haL
  have hWmap : (W.subgroupOf M).map q = E := by
    simpa [W, q, E, δ] using map_subgroupOf_diagonalPreimage_eq ha hr hr2 hEcent
  have hψrange : ψ.range = E := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hWmap
  haveI hBarPerf : Group.IsPerfect ↥(barImage M L) := isPerfect_barImage_of_mem_calC hL
  haveI hEperf : Group.IsPerfect ↥E := Group.IsPerfect.range (f := δ)
  have hDMmap : DM.map q = E := by
    haveI : Group.IsPerfect ↥ψ.range := hψrange.symm ▸ hEperf
    calc DM.map q = ((CFSG.perfectResidual ↥W).map (Subgroup.inclusion hWM)).map q := rfl
      _ = (CFSG.perfectResidual ↥W).map ψ := by rw [Subgroup.map_map]
      _ = ψ.range := map_perfectResidual_eq_range ψ
      _ = E := hψrange
  have hDmap : (D.subgroupOf M).map q = E := by
    rw [show D = DM.map M.subtype from rfl, subgroupOf_map_subtype_map_eq, hDMmap]
  have hDeq : D = (CFSG.perfectResidual ↥W).map W.subtype := by
    simp only [D, DM, Subgroup.map_map, Subgroup.subtype_comp_inclusion hWM]
  have hDW : D ≤ W :=
    hDeq.trans_le (Subgroup.map_subtype_le (K := CFSG.perfectResidual ↥W))
  have hDM : D ≤ M := hDW.trans hWM
  have hDperf : ⁅D, D⁆ = D := by
    simpa [hDeq] using isPerfect_map_perfectResidual_subtype (W := W)
  exact ⟨D, hDM, hDW.trans hWcent, hDperf, hDmap⟩

theorem exists_diagonal_perfect {M L : Subgroup G} {a : G} (hL : L ∈ calC M) (ha : a ∈ M)
    (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2)
    (haL : a ∉ Subgroup.normalizer (L : Set G)) :
    ∃ D : Subgroup G, D ≤ M ∧ D ≤ Subgroup.centralizer ({a} : Set G) ∧ ⁅D, D⁆ = D ∧
      D ≤ ⨆ i : Fin (orderOf a), conjugatePower a L i ∧
      (D.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) =
        (orbitDiagonalHom (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) (barImage M L)
          (orderOf a) (mk_pow_orderOf_eq_one ha)
          (conjugatesCommute_barImage hL ha hr haL)).range := by
  obtain ⟨D, hDM, hDcent, hDperf, hDmap⟩ := exists_perfect_map_diagonal hL ha hr hr2 haL
  have hmap : (D.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ≤
      ((⨆ i : Fin (orderOf a), conjugatePower a L i).subgroupOf M).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
    rw [hDmap]
    exact range_orbitDiagonalHom_le_map_iSup hL ha hr haL
  exact ⟨D, hDM, hDcent, hDperf,
    perfect_le_iSup_of_map_le hL ha hDM hDperf hmap, hDmap⟩

theorem ker_comp_le_center_of_ker_le_center {L Q H : Type*} [Group L] [Group Q]
    [Group H] {δ : Q →* H} (e : L ≃* Q) (h : δ.ker ≤ Subgroup.center Q) :
    (δ.comp e.toMonoidHom).ker ≤ Subgroup.center L := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_center_iff]
  intro z
  apply e.injective
  rw [map_mul, map_mul]
  have hxe : e x ∈ δ.ker := by
    rw [MonoidHom.mem_ker]
    simpa using hx
  exact Subgroup.mem_center_iff.mp (h hxe) (e z)

private theorem exists_elemAbelian_le_diagonal {M L : Subgroup G} {a : G} {p : ℕ}
    (hL : L ∈ calC M) (ha : a ∈ M) (hr : (orderOf a).Prime)
    (haL : a ∉ Subgroup.normalizer (L : Set G)) (hp : p.Prime) (hp2 : p ≠ 2)
    (P : Sylow p (Bar2 L)) (hPnc : ¬ IsCyclic ↥(P : Subgroup (Bar2 L))) :
    ∃ S : Subgroup (Bar2 M), S ≤
      (orbitDiagonalHom (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) (barImage M L)
        (orderOf a) (mk_pow_orderOf_eq_one ha)
        (conjugatesCommute_barImage hL ha hr haL)).range ∧
      IsElemAbelian p S ∧ Nat.card S = p ^ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let δ : ↥(barImage M L) →* Bar2 M :=
    orbitDiagonalHom (q ⟨a, ha⟩) (barImage M L) (orderOf a) (mk_pow_orderOf_eq_one ha)
      (conjugatesCommute_barImage hL ha hr haL)
  haveI hLperf : Group.IsPerfect (Bar2 L) :=
    Group.IsPerfect.mk (uc22p22j_perfect_bar2 L hL.2.1)
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_bar_equiv hL
  let φ : Bar2 L →* Bar2 M := δ.comp e.toMonoidHom
  let Z₀ : Subgroup (Bar2 L) := φ.ker
  haveI hZ₀normal : Z₀.Normal := MonoidHom.normal_ker φ
  have hZ₀center : Z₀ ≤ Subgroup.center (Bar2 L) :=
    ker_comp_le_center_of_ker_le_center e
      (orbitDiagonalHom_ker_le_center (q ⟨a, ha⟩) (barImage M L) (orderOf a)
        (mk_pow_orderOf_eq_one ha) (conjugatesCommute_barImage hL ha hr haL) hr.pos)
  obtain ⟨E₁, hE₁elem, hE₁card⟩ :=
    CFSG.GroupTheory.exists_elemAbelian_card_prime_sq_quotient_center (p := p) hp2 P hPnc
      Z₀ hZ₀center
  let Φ : Bar2 L ⧸ Z₀ →* Bar2 M := QuotientGroup.lift Z₀ φ le_rfl
  have hΦinj : Function.Injective Φ :=
    (QuotientGroup.injective_lift_iff Z₀ φ le_rfl).2 rfl
  refine ⟨E₁.map Φ, ?_, hE₁elem.map Φ, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨e y, rfl⟩
  · rw [Subgroup.card_map_of_injective hΦinj, hE₁card]

private theorem not_dvd_card_ker_mk_comp {M D : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp
      (D.subgroupOf M).subtype).ker) := by
  haveI : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hle : (((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp
      (D.subgroupOf M).subtype).ker).map (D.subgroupOf M).subtype ≤
        CFSG.pCore 2 ↥M := by
    rintro y ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff ((x : ↥(D.subgroupOf M)) : ↥M)).1 hx
  have hdvd : Nat.card (((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp
      (D.subgroupOf M).subtype).ker) ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    rw [← Subgroup.card_map_of_injective (D.subgroupOf M).subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
  rw [hn] at hdvd
  intro hpdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow (hpdvd.trans hdvd)) with h | h
  · exact hp.ne_one h
  · exact hp2 h

private theorem le_pRank_of_elemAbelian_lift {M D : Subgroup G} (hDM : D ≤ M)
    {p : ℕ} (hp : p.Prime) (ψ : ↥(D.subgroupOf M) →* Bar2 M) {S : Subgroup (Bar2 M)}
    (hS : S ≤ ψ.range) (hSe : IsElemAbelian p S) (hSc : Nat.card S = p ^ 2)
    (hker : ¬ p ∣ Nat.card ψ.ker) :
    2 ≤ CFSG.Open.pRank p D := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S', hS'elem, hS'map, hS'card⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_lift_of_le_range ψ hker hS hSe
  let Sg : Subgroup G := (S'.map (D.subgroupOf M).subtype).map M.subtype
  have hSg_elem : IsElemAbelian p Sg :=
    (hS'elem.map (D.subgroupOf M).subtype).map M.subtype
  have hSg_card : Nat.card Sg = p ^ 2 := by
    rw [show Sg = (S'.map (D.subgroupOf M).subtype).map M.subtype from rfl,
      Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective (D.subgroupOf M).subtype_injective,
      hS'card, hSc]
  have hSgD : Sg ≤ D := by
    have h1 : S'.map (D.subgroupOf M).subtype ≤ D.subgroupOf M :=
      Subgroup.map_subtype_le (K := S')
    have h2 := Subgroup.map_mono (f := M.subtype) h1
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDM] at h2
  exact CFSG.SectionRank.le_pRank (p := p) hp.one_lt hSgD hSg_elem hSg_card

theorem two_le_pRank_diagonal {M L : Subgroup G} {a : G} {D : Subgroup G}
    (hL : L ∈ calC M) (ha : a ∈ M) (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2)
    (haL : a ∉ Subgroup.normalizer (L : Set G)) (hDM : D ≤ M)
    (hDmap : (D.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) =
      (orbitDiagonalHom (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) (barImage M L)
        (orderOf a) (mk_pow_orderOf_eq_one ha)
        (conjugatesCommute_barImage hL ha hr haL)).range)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : ∃ P : Sylow p (Bar2 L), ¬ IsCyclic ↥(P : Subgroup (Bar2 L))) :
    2 ≤ CFSG.Open.pRank p D := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let E : Subgroup (Bar2 M) :=
    (orbitDiagonalHom (q ⟨a, ha⟩) (barImage M L) (orderOf a) (mk_pow_orderOf_eq_one ha)
      (conjugatesCommute_barImage hL ha hr haL)).range
  obtain ⟨P, hPnc⟩ := hP
  obtain ⟨S, hS_le_E, hS_elem, hS_card⟩ :=
    exists_elemAbelian_le_diagonal hL ha hr haL hp hp2 P hPnc
  let ψ : ↥(D.subgroupOf M) →* Bar2 M := q.comp (D.subgroupOf M).subtype
  have hψrange : ψ.range = E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    simpa [E, q] using hDmap
  have hS_le_ψ : S ≤ ψ.range := by
    rw [hψrange]
    simpa [E, q] using hS_le_E
  have hker : ¬ p ∣ Nat.card ψ.ker := by
    simpa [ψ, q] using not_dvd_card_ker_mk_comp hp hp2
  exact le_pRank_of_elemAbelian_lift hDM hp ψ hS_le_ψ hS_elem hS_card hker

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

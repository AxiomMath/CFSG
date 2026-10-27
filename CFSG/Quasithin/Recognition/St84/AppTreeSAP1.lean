module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Recognition.St84.L2Group

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.LieType.BorelTits
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem isPGroup_le_sup_pCoreOf_of_relIndex_three {G : Type*} [Group G] [Finite G]
    {L B R : Subgroup G}
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hQB : pCoreOf 2 (L ⊔ B) ≤ B)
    (hIdx : B.relIndex (L ⊔ B) = 3)
    (hLidx : (pCoreOf 2 L).relIndex L = 6)
    (hB1 : IsPGroup 2 ↥(L ⊓ B))
    (hRB : R ≤ B) (hR2 : IsPGroup 2 R)
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) :
    R ≤ L ⊔ pCoreOf 2 (L ⊔ B) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := L ⊔ B with hP
  set Q : Subgroup G := pCoreOf 2 P with hQ
  have hIdxP : B.relIndex P = 3 := by rw [hP]; exact hIdx
  have hQleB : Q ≤ B := by rw [hQ, hP]; exact hQB
  have hBleP : B ≤ P := by rw [hP]; exact le_sup_right
  have hQleP : Q ≤ P := by rw [hQ]; exact pCoreOf_le 2 P
  have hQnP : P ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ]; exact le_normalizer_pCoreOf 2 P
  have hPnL : P ≤ Subgroup.normalizer (L : Set G) := by
    rw [hP]; exact sup_le Subgroup.le_normalizer hBL
  have hPnO2 : P ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hPnL.trans (normalizer_le_normalizer_map_of_characteristic (K := CFSG.pCore 2 ↥L))
  have hO2leQ : pCoreOf 2 L ≤ Q := by
    rw [hQ]
    exact le_pCoreOf_of_le_normalizer (r := 2) ((pCoreOf_le 2 L).trans le_sup_left) hPnO2
      (pCoreOf_isPGroup 2 L)
  have hO2leB : pCoreOf 2 L ≤ B := hO2leQ.trans hQleB
  have hO2leP : pCoreOf 2 L ≤ P := (pCoreOf_le 2 L).trans le_sup_left
  set D : Subgroup G := ((B.subgroupOf P).normalCore).map P.subtype with hD
  have hDleB : D ≤ B := by
    rw [hD]
    calc ((B.subgroupOf P).normalCore).map P.subtype
        ≤ (B.subgroupOf P).map P.subtype := Subgroup.map_mono (Subgroup.normalCore_le _)
      _ = B ⊓ P := Subgroup.subgroupOf_map_subtype B P
      _ = B := inf_eq_left.mpr hBleP
  have hDleP : D ≤ P := hDleB.trans hBleP
  have hDsub : D.subgroupOf P = (B.subgroupOf P).normalCore := by
    rw [hD, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hDnP : P ≤ Subgroup.normalizer (D : Set G) := by
    have h : (D.subgroupOf P).Normal := by
      rw [hDsub]; exact Subgroup.normalCore_normal _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hDleP).mp h
  have hDindex : D.relIndex P ∣ 6 := by
    have h := Subgroup.index_normalCore_dvd_factorial_index (B.subgroupOf P)
    have hBidx : (B.subgroupOf P).index = 3 := hIdxP
    rw [hBidx] at h
    have hDidx : (B.subgroupOf P).normalCore.index = D.relIndex P := by
      rw [Subgroup.relIndex, hDsub]
    rw [hDidx] at h
    rw [show Nat.factorial 3 = 6 by norm_num] at h
    exact h
  have hLD : L ⊓ D = pCoreOf 2 L := by
    refine le_antisymm ?_ (le_inf (pCoreOf_le 2 L) ?_)
    · have hleB : L ⊓ D ≤ L ⊓ B := inf_le_inf_left L hDleB
      have h2 : IsPGroup 2 ↥(L ⊓ D) := hB1.to_le hleB
      have hnorm : L ≤ Subgroup.normalizer (L ⊓ D : Set G) :=
        (le_inf Subgroup.le_normalizer ((le_sup_left : L ≤ P).trans hDnP)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      exact le_pCoreOf (r := 2) inf_le_left
        (Subgroup.normal_subgroupOf_of_le_normalizer hnorm) h2
    · have hN'le : (pCoreOf 2 L).subgroupOf P ≤ B.subgroupOf P := by
        intro x hx
        exact Subgroup.mem_subgroupOf.mpr
          (hQleB (hO2leQ (Subgroup.mem_subgroupOf.mp hx)))
      have hN'normal : ((pCoreOf 2 L).subgroupOf P).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hPnO2
      haveI : ((pCoreOf 2 L).subgroupOf P).Normal := hN'normal
      have hcore : (pCoreOf 2 L).subgroupOf P ≤ (B.subgroupOf P).normalCore :=
        Subgroup.normal_le_normalCore.mpr hN'le
      calc pCoreOf 2 L = ((pCoreOf 2 L).subgroupOf P).map P.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hO2leP).symm
        _ ≤ ((B.subgroupOf P).normalCore).map P.subtype := Subgroup.map_mono hcore
        _ = D := rfl
  have hPD : P = L ⊔ D := by
    have hMle : L ⊔ D ≤ P := sup_le le_sup_left hDleP
    have hMrel : D.relIndex (L ⊔ D) = 6 := by
      have h1 : (D.subgroupOf P).relIndex ((L ⊔ D).subgroupOf P) = D.relIndex (L ⊔ D) :=
        Subgroup.relIndex_subgroupOf hMle
      rw [← h1]
      have hMs : (L ⊔ D).subgroupOf P = L.subgroupOf P ⊔ D.subgroupOf P :=
        Subgroup.subgroupOf_sup le_sup_left hDleP
      rw [hMs, hDsub, Subgroup.relIndex_sup_right, ← hDsub,
        Subgroup.relIndex_subgroupOf (le_sup_left : L ≤ P)]
      rw [show D.relIndex L = (L ⊓ D).relIndex L from by
        rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.inf_subgroupOf_left]]
      rw [hLD, hLidx]
    have hpos : 0 < (L ⊔ D).relIndex P := by
      rw [Subgroup.relIndex]
      exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hkey : 6 * (L ⊔ D).relIndex P = D.relIndex P := by
      rw [← hMrel]
      exact Subgroup.relIndex_mul_relIndex (H := D) (K := L ⊔ D) (L := P)
        (le_sup_right : D ≤ L ⊔ D) hMle
    rw [← hkey] at hDindex
    have hle : 6 * (L ⊔ D).relIndex P ≤ 6 := Nat.le_of_dvd (by norm_num) hDindex
    have hk1 : (L ⊔ D).relIndex P ≤ 1 := by
      have h := Nat.le_of_mul_le_mul_left
        (show 6 * (L ⊔ D).relIndex P ≤ 6 * 1 by simpa using hle) (by norm_num : 0 < 6)
      simpa using h
    have hk : (L ⊔ D).relIndex P = 1 := le_antisymm hk1 hpos
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hk) hMle
  have hRLQ : R ≤ Subgroup.normalizer ((L ⊔ Q : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (hRB.trans hBL) ((hRB.trans hBleP).trans hQnP)
  set Y : Subgroup G := (L ⊔ Q) ⊔ R with hY
  have hLQY : L ⊔ Q ≤ Y := by rw [hY]; exact le_sup_left
  have hRY : R ≤ Y := by rw [hY]; exact le_sup_right
  have hLY : L ≤ Y := le_sup_left.trans hLQY
  have hB_LQ : B ≤ Subgroup.normalizer ((L ⊔ Q : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hBL (hBleP.trans hQnP)
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hY]
    exact F1.le_normalizer_sup hB_LQ hBR
  have hLY' : L ≤ Subgroup.normalizer (Y : Set G) := by
    have hkey : ∀ u ∈ L, conjSub u Y ≤ Y := by
      intro u hu
      have huLQ : conjSub u (L ⊔ Q) = L ⊔ Q :=
        F1.conjSub_eq_of_mem_normalizer (le_sup_left.trans Subgroup.le_normalizer hu)
      calc conjSub u Y = conjSub u ((L ⊔ Q) ⊔ R) := by rw [hY]
        _ = conjSub u (L ⊔ Q) ⊔ conjSub u R := conjSub_sup u (L ⊔ Q) R
        _ = (L ⊔ Q) ⊔ conjSub u R := by rw [huLQ]
        _ ≤ Y := by
            refine sup_le hLQY (fun x hx => ?_)
            obtain ⟨r, hr, rfl⟩ := hx
            have hrl : r * u * r⁻¹ ∈ L :=
              (Subgroup.mem_normalizer_iff.mp (hBL (hRB hr)) u).mp hu
            have e : u * r * u⁻¹ = (u * (r * u * r⁻¹)⁻¹) * r := by group
            change u * r * u⁻¹ ∈ Y
            rw [e]
            exact Y.mul_mem (Y.mul_mem (hLY hu) (hLY (L.inv_mem hrl))) (hRY hr)
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub l Y = Y
    refine le_antisymm (hkey l hl) ?_
    have h2 := conjSub_mono l (hkey l⁻¹ (L.inv_mem hl))
    rwa [conjSub_inv_conjSub] at h2
  have hPnY : P ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hP]
    exact sup_le hLY' hBY
  have hP0nY : P ≤ Subgroup.normalizer ((Y ⊓ D : Subgroup G) : Set G) :=
    (le_inf hPnY hDnP).trans Subgroup.inf_normalizer_le_normalizer_inf
  set T : Subgroup G := ((L ⊓ B) ⊔ Q) ⊔ R with hT
  have hT2g : IsPGroup 2 T := by
    have h1 : IsPGroup 2 ↥(L ⊓ B) := hB1
    have h2 : IsPGroup 2 ↥((L ⊓ B) ⊔ Q) :=
      h1.to_sup_of_normal_right' (pCoreOf_isPGroup 2 P) (by
        intro x hx
        exact hQnP ((inf_le_right.trans hBleP) hx))
    rw [hT]
    have hnormR : ((L ⊓ B) ⊔ Q) ≤ Subgroup.normalizer (R : Set G) :=
      sup_le (fun y hy => hBR ((inf_le_right : L ⊓ B ≤ B) hy))
        (fun y hy => hBR (hQleB hy))
    exact h2.to_sup_of_normal_right' hR2 hnormR
  have hYsplit : ∀ y, y ∈ Y ↔ ∃ x ∈ (L ⊔ Q), ∃ r ∈ R, y = x * r := by
    intro y
    rw [hY]
    exact F1.mem_sup_iff_exists_mul_of_normalizes hRLQ
  have hP0leT : Y ⊓ D ≤ T := by
    intro y hy
    obtain ⟨hyY, hyD⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨x, hx, r, hr, rfl⟩ := (hYsplit y).mp hyY
    have hyB : x * r ∈ B := hDleB hyD
    have hxB : x ∈ B := by
      have := B.mul_mem hyB (B.inv_mem (hRB hr))
      simpa using this
    have hx' : x ∈ (L ⊔ Q) ⊓ B := ⟨hx, hxB⟩
    have hmod : (L ⊔ Q) ⊓ B = (L ⊓ B) ⊔ Q := by
      refine le_antisymm ?_ ?_
      · intro z hz
        obtain ⟨hzLQ, hzB⟩ := Subgroup.mem_inf.mp hz
        obtain ⟨l, hl, q, hq, rfl⟩ :=
          (F1.mem_sup_iff_exists_mul_of_normalizes (hQleP.trans hPnL)).mp hzLQ
        have hlB : l ∈ B := by
          have hmem : l * q * q⁻¹ ∈ B := B.mul_mem hzB (B.inv_mem (hQleB hq))
          simpa using hmem
        exact (L ⊓ B ⊔ Q).mul_mem (Subgroup.mem_sup_left ⟨hl, hlB⟩)
          (Subgroup.mem_sup_right hq)
      · refine le_inf (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
          (sup_le inf_le_right hQleB)
    rw [hmod] at hx'
    have hxT : x ∈ ((L ⊓ B) ⊔ Q) := hx'
    have hrT : r ∈ T := (le_sup_right : R ≤ T) hr
    exact T.mul_mem ((le_sup_left : ((L ⊓ B) ⊔ Q) ≤ T) hxT) hrT
  have hP0_2 : IsPGroup 2 ↥(Y ⊓ D) := hT2g.to_le hP0leT
  have hP0leQ : Y ⊓ D ≤ Q := by
    have hP0leP : Y ⊓ D ≤ P := by
      refine inf_le_left.trans ?_
      rw [hY]
      exact sup_le (sup_le le_sup_left (hQleB.trans hBleP)) (hRB.trans hBleP)
    exact le_pCoreOf (r := 2) hP0leP
      (Subgroup.normal_subgroupOf_of_le_normalizer hP0nY) hP0_2
  have hYP : Y ≤ P := by
    rw [hY]
    exact sup_le (sup_le le_sup_left (hQleB.trans hBleP)) (hRB.trans hBleP)
  have hDedekind : Y = L ⊔ (Y ⊓ D) := by
    refine le_antisymm ?_ (sup_le hLY inf_le_left)
    intro y hy
    have hyLD : y ∈ L ⊔ D := by
      rw [← hPD]
      exact hYP hy
    obtain ⟨l, hl, d, hd, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes (hDleP.trans hPnL)).mp hyLD
    have hdY : d ∈ Y := by
      have hmem : l⁻¹ * (l * d) ∈ Y := Y.mul_mem (Y.inv_mem (hLY hl)) hy
      simpa using hmem
    exact (L ⊔ (Y ⊓ D)).mul_mem (Subgroup.mem_sup_left hl)
      (Subgroup.mem_sup_right ⟨hdY, hd⟩)
  have hYleLQ : Y ≤ L ⊔ Q := by
    rw [hDedekind]
    exact sup_le le_sup_left (hP0leQ.trans le_sup_right)
  have hgoal : R ≤ L ⊔ Q := hRY.trans hYleLQ
  rwa [hQ, hP] at hgoal

end CFSG.Quasithin.F112R.St84

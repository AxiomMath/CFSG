module

public import CFSG.RankThree.GF2n.Tim79aSec33Base
public import CFSG.RankThree.GF2n.Tim79aSec24CoreTilde

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Sec3Setup

variable {M V Q P H : Subgroup G} [Finite G]

theorem exists_mem_Ycomm_not_le (hs : Sec3Setup M V Q P H)
    (hF : PairFacts (XbarZ V H) (VZ V H)) : ∃ y ∈ Ycomm V H, ¬ Aof V H y ≤ V := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨g, hgC, hgne, -⟩ := hF.moves
  obtain ⟨y, rfl⟩ := xToZ_surjective hVH g
  have hyH : (y : G) ∈ H := xOf_le_H hVH y.2
  have hcomm := hc.commute_conj_of_commute_tilde (x₁ := 1) (x₂ := y) (by
    intro a ha b hb
    rw [map_one, conjSubgroup_one] at ha
    exact Subgroup.mem_centralizer_iff.mp (hgC hb) a ha)
  have hcomm' : ∀ u ∈ V, ∀ w ∈ conjSubgroup (y : G) V, u * w = w * u := fun u hu w hw =>
    hcomm u (by rw [OneMemClass.coe_one, conjSubgroup_one]; exact hu) w hw
  refine ⟨y, ⟨y.2, fun u hu w hw => ?_⟩, fun hle => ?_⟩
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcomm' u hu w hw)]
    exact (wOf V H).one_mem
  · have hne : conjSubgroup (y : G) V ≠ V := by
      intro heq
      apply hgne
      have h1 := imgZ_conj hVH y
      rw [heq] at h1
      exact h1.symm
    have hbot := inf_conjSubgroup_eq_bot_of_isTI hc.ti hne
    apply hc.conj_inf_wOf_ne_bot hyH
    rw [eq_bot_iff]
    intro a ha
    have h2 : a ∈ V ⊓ conjSubgroup (y : G) V := ⟨hle ha, ha.1⟩
    rw [hbot] at h2
    exact h2

end Sec3Setup

theorem sec3ExistsStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
      PairFacts (XbarZ V H) (VZ V H) → ∃ y ∈ Ycomm V H, ¬ Aof V H y ≤ V := by
  intro G _ _ M V Q P H hs hF
  exact hs.exists_mem_Ycomm_not_le hF

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem conj_VZ_le_centralizer (hc : MinCex M V Q P H) {y : ↥(xOf V H)}
    (hy : (y : G) ∈ Ycomm V H) :
    conjSub (VZ V H) (xToZ hc.V_le_H y) ≤ Subgroup.centralizer (VZ V H : Set (XbarZ V H)) := by
  have hVH : V ≤ H := hc.V_le_H
  have hcomm := hc.commute_conj_of_mem_Ycomm hy
  intro b hb
  have hb' : b ∈ imgZ V H (conjSubgroup (y : G) V) := by
    rw [imgZ_conj hVH y]
    exact hb
  obtain ⟨b', hb'', rfl⟩ := Subgroup.mem_map.mp hb'
  obtain ⟨w, hwT, hwb⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hb'')
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨u, huV, hua⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp ha')
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hua, ← hwb, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm u huV w hwT)

theorem conj_VZ_ne (hc : MinCex M V Q P H) (hd : Sec23Data V H) {y : ↥(xOf V H)}
    (hne : conjSubgroup (y : G) V ≠ V) : conjSub (VZ V H) (xToZ hc.V_le_H y) ≠ VZ V H := by
  have hVH : V ≤ H := hc.V_le_H
  intro heq
  apply hne
  have hgN : projZ V H (xToXbar hVH y) ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)) :=
    mem_normalizer_iff_conjSubgroup_eq.mpr heq
  have hbN := hc.mem_normalizer_Vy_of_tilde hd hgN
  rw [normalizer_Vy_eq, Subgroup.mem_subgroupOf] at hbN
  have hN := (Subgroup.mem_inf.mp hbN).1
  rw [coe_xToXbar, hc.normalizer_barOf_V] at hN
  obtain ⟨m, hmN, hmy⟩ := mem_barOf_iff.mp hN
  have hw : (m : G)⁻¹ * y ∈ wOf V H := by
    have h1 : piBar V H (m⁻¹ * Subgroup.inclusion (xOf_le_H hVH) y) = 1 := by
      rw [map_mul, map_inv, hmy, inv_mul_cancel]
    exact (piBar_eq_one_iff _).1 h1
  have hwN : (m : G)⁻¹ * y ∈ Subgroup.normalizer (V : Set G) :=
    hc.normalizer_eq ▸ hc.pCoreH_le_M (wOf_le_pCore V H hw)
  have hyN : (y : G) ∈ Subgroup.normalizer (V : Set G) := by
    have := Subgroup.mul_mem _ hmN hwN
    simpa using this
  exact mem_normalizer_iff_conjSubgroup_eq.mp hyN

end MinCex

namespace Sec3Setup

variable {M V Q P H : Subgroup G} [Finite G]

theorem aof_eq_conj_inf_P (hs : Sec3Setup M V Q P H)
    (hF : PairFacts (XbarZ V H) (VZ V H)) {y : G} (hy : y ∈ Ycomm V H)
    (hnot : ¬ Aof V H y ≤ V) : Aof V H y = conjSubgroup y V ⊓ P := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  refine le_antisymm (le_inf inf_le_left (hs.aof_le_P hy)) ?_
  obtain ⟨y, rfl⟩ : ∃ y' : ↥(xOf V H), (y' : G) = y := ⟨⟨y, hy.1⟩, rfl⟩
  have hyH : (y : G) ∈ H := xOf_le_H hVH y.2
  have hne : conjSubgroup (y : G) V ≠ V := by
    intro heq
    apply hnot
    intro a ha
    have h1 : a ∈ conjSubgroup (y : G) V := ha.1
    rw [heq] at h1
    exact h1
  have hdisj := hF.disjoint (xToZ hVH y) (hc.conj_VZ_le_centralizer hy)
    (hc.conj_VZ_ne hs.setup.data hne)
  intro x hx
  obtain ⟨hxT, hxP⟩ := Subgroup.mem_inf.mp hx
  have hxH : x ∈ H := hc.PleH hxP
  have hxX : x ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hyH) hxT
  set r : Xbar V H := ⟨piBar V H ⟨x, hxH⟩, mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hxX, rfl⟩⟩
  have hrO : projZ V H r ∈ pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) := by
    have hb : Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) :=
      hs.tilde
    rw [← hb]
    exact ⟨r, mem_Rbar.mpr (mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hxP, rfl⟩), rfl⟩
  have hrT : projZ V H r ∈ conjSub (VZ V H) (xToZ hVH y) := by
    show projZ V H r ∈ conjSubgroup (xToZ hVH y) (VZ V H)
    rw [← imgZ_conj hVH y]
    exact ⟨r, Subgroup.mem_subgroupOf.mpr (mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hxT, rfl⟩), rfl⟩
  have hr1 : projZ V H r = 1 := by
    have h1 : projZ V H r ∈ conjSub (VZ V H) (xToZ hVH y) ⊓
        pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) := ⟨hrT, hrO⟩
    rw [hdisj] at h1
    exact h1
  have hrZ : r ∈ Subgroup.center (Xbar V H) := (QuotientGroup.eq_one_iff _).mp hr1
  have hxC : x ∈ cX V H := mem_cX_of_centralizes hVH hxH fun z => by
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hrZ z)
    simp only [Subgroup.coe_mul] at h1
    show (r : Hbar V H) * z * (r : Hbar V H)⁻¹ = z
    rw [← h1]
    group
  exact ⟨hxT, hc.mem_wOf_of_mem_conj_of_mem_cX hyH hxT hxC⟩

end Sec3Setup

theorem sec3TIStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
      PairFacts (XbarZ V H) (VZ V H) →
      ∀ y ∈ Ycomm V H, ¬ Aof V H y ≤ V → Aof V H y = conjSubgroup y V ⊓ P := by
  intro G _ _ M V Q P H hs hF y hy hnot
  exact hs.aof_eq_conj_inf_P hF hy hnot

end CFSG.RankThree.GF2n.Tim79a

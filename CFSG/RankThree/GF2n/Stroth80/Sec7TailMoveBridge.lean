module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarDict
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveMain
public import CFSG.RankThree.GF2n.Stroth80.Sec12Cases

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem mem_normalizer_subgroupOf_iff' {Y : Type*} [Group Y] {S T : Subgroup Y} (hTS : T ≤ S)
    (x : S) :
    x ∈ Subgroup.normalizer ((T.subgroupOf S : Subgroup S) : Set S) ↔
      (x : Y) ∈ Subgroup.normalizer (T : Set Y) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTS, Subgroup.mem_subgroupOf]

@[expose] def Sec717MoveFrameStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    ∃ (K : Type) (_ : Field K) (E : Type) (_ : AddCommGroup E) (_ : Module K E)
      (_ : FiniteDimensional K E) (B' : LinearMap.BilinForm K E)
      (φ : ↥(bar M Q (H0 M Z)) →* (E ≃ₗ[K] E))
      (Tt : ↥(bar M Q (H0 M Z)) → Submodule K E) (q : ℕ),
      MoveFrame B' φ ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
        ((bar M Q L).subgroupOf (bar M Q (H0 M Z)))
        ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
        ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) Tt q

theorem sec717Move_of_frame (hF : Sec717MoveFrameStatement) : Sec717MoveStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn hex hLK
  obtain ⟨h, hhH, hhK, hhN⟩ := hex
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQCN : Q ≤ hc.CN t := hc.Q_le_CN ht
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hZ0H : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hLCN : L ≤ hc.CN t := hL.2.1
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hLM : L ≤ M := fun x hx => hc.Rt_le_M t (hCNR (hLCN hx))
  have hLH : L ≤ H0 M Z := fun x hx => hc.Rt_le_H0 t (hCNR (hLCN hx))
  have hQL : Q ≤ L := hL.1
  obtain ⟨K, _, E, _, _, _, B', φ, Tt, q, F⟩ :=
    hF G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn
  have hhM : h ∈ M := (Subgroup.mem_inf.mp hhH).1
  have hmem : QuotientGroup.mk' (Q.subgroupOf M) (⟨h, hhM⟩ : M) ∈ bar M Q (H0 M Z) :=
    (mk_mem_bar_iff_sec4 hQH ⟨h, hhM⟩).mpr hhH
  have hbZ : bar M Q Z0 ≤ bar M Q (H0 M Z) := bar_mono' hZ0H
  have hbL : bar M Q L ≤ bar M Q (H0 M Z) := bar_mono' hLH
  have hZ0pre : ∀ x : Mbar M Q, x ∈ bar M Q Z0 →
      ∃ z : M, (z : G) ∈ Z0 ∧ QuotientGroup.mk' (Q.subgroupOf M) z = x := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    exact ⟨z, hz, hzx⟩
  have hK : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      (⟨QuotientGroup.mk' (Q.subgroupOf M) (⟨h, hhM⟩ : M), hmem⟩ : ↥(bar M Q (H0 M Z))) * a *
        (⟨QuotientGroup.mk' (Q.subgroupOf M) (⟨h, hhM⟩ : M), hmem⟩ : ↥(bar M Q (H0 M Z)))⁻¹ ∈
        Subgroup.normalizer (((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :
          Subgroup ↥(bar M Q (H0 M Z))) : Set ↥(bar M Q (H0 M Z))) := by
    intro a ha
    rw [mem_normalizer_subgroupOf_iff' hbZ]
    obtain ⟨z, hz, hza⟩ := hZ0pre a.1 (Subgroup.mem_subgroupOf.mp ha)
    have hzc : (⟨h, hhM⟩ * z * ⟨h, hhM⟩⁻¹ : M) ∈ ((NormH0 M Z Z0).subgroupOf M) := by
      have h1 : h * (z : G) * h⁻¹ ∈ conjSubgroup h Z0 :=
        mem_conjSubgroup.mpr (by simpa [mul_assoc] using hz)
      exact Subgroup.mem_subgroupOf.mpr (hhK h1)
    have hnorm := mk_mem_normalizer_bar_of_normalizer hQZ0
      (⟨h, hhM⟩ * z * ⟨h, hhM⟩⁻¹ : M) (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hzc)).2
    convert hnorm using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hza]
  have hN : ¬ ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      (⟨QuotientGroup.mk' (Q.subgroupOf M) (⟨h, hhM⟩ : M), hmem⟩ : ↥(bar M Q (H0 M Z))) * a *
        (⟨QuotientGroup.mk' (Q.subgroupOf M) (⟨h, hhM⟩ : M), hmem⟩ : ↥(bar M Q (H0 M Z)))⁻¹ ∈
        (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
    intro hall
    apply hhN
    intro x hx
    have hz : h⁻¹ * x * h ∈ Z0 := mem_conjSubgroup.mp hx
    have hzM : h⁻¹ * x * h ∈ M := hZ0M hz
    have hxM : x ∈ M := by
      have := M.mul_mem (M.mul_mem hhM hzM) (M.inv_mem hhM)
      simpa [mul_assoc] using this
    have hbz : QuotientGroup.mk' (Q.subgroupOf M) (⟨h⁻¹ * x * h, hzM⟩ : M) ∈ bar M Q Z0 :=
      (mk_mem_bar_iff_sec4 hQZ0 _).mpr hz
    have h1 := hall ⟨_, hbZ hbz⟩ (Subgroup.mem_subgroupOf.mpr hbz)
    have h2 : QuotientGroup.mk' (Q.subgroupOf M) (⟨x, hxM⟩ : M) ∈ bar M Q (hc.CN t) := by
      have h3 := Subgroup.mem_subgroupOf.mp h1
      convert h3 using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← map_mul, ← map_inv]
      congr 1
      ext
      simp [mul_assoc]
    exact (mk_mem_bar_iff_sec4 hQCN _).mp h2
  obtain ⟨m, hmL, hmV⟩ := F.sec717Move_frame _ hK hN
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) m.1
  have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp (hy ▸ m.2)
  have hmL' : m.1 ∈ Subgroup.normalizer (bar M Q L : Set (Mbar M Q)) :=
    (mem_normalizer_subgroupOf_iff' hbL m).mp hmL
  have hyL : (y : G) ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_mk_mem_normalizer_bar hQL hLM y (hy ▸ hmL')
  have hyK : (y : G) ∈ NormH0 M Z Z0 := hLK (Subgroup.mem_inf.mpr ⟨hyH, hyL⟩)
  apply hmV
  rw [mem_normalizer_subgroupOf_iff' hbZ]
  rw [← hy]
  exact mk_mem_normalizer_bar_of_normalizer hQZ0 y (Subgroup.mem_inf.mp hyK).2

end CFSG.RankThree.GF2n.Stroth80

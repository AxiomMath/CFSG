module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRecogCtx

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

structure CtxYBase {Y : Type} [Group Y] (V L N R K : Subgroup Y) (q : ℕ) : Prop where
  K_eq : K = Subgroup.normalizer (V : Set Y)
  VL : V ≤ L
  LN : L ≤ N
  NR : N ≤ R
  RK : R ≤ K
  N2 : IsPGroup 2 N
  Nn : ∀ k ∈ K, k ∈ Subgroup.normalizer (N : Set Y)
  Rn : ∀ k ∈ K, k ∈ Subgroup.normalizer (R : Set Y)
  Ln : ∀ k ∈ K, k ∈ Subgroup.normalizer (L : Set Y)
  ZN : ∀ x ∈ N, (∀ n ∈ N, x * n = n * x) → x ∈ V
  Vc : ∀ v ∈ V, ∀ n ∈ N, v * n = n * v
  Vcard : Nat.card V = q
  Ncard : Nat.card N = q ^ 9
  Lcard : Nat.card L = q ^ 5
  ti : ∀ g : Y, ∀ a ∈ V, a ≠ 1 → g * a * g⁻¹ ∈ V → g ∈ Subgroup.normalizer (V : Set Y)
  Vsq : ∀ a ∈ V, a * a = 1
  Lcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a

theorem Ctx.ti_bar {Z0 : Subgroup G} (hQZ0 : Q ≤ Z0)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) :
    ∀ g x : Mbar M Q, x ∈ bar M Q Z0 → x ≠ 1 → g * x * g⁻¹ ∈ bar M Q Z0 →
      g ∈ Subgroup.normalizer ((bar M Q Z0 : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
  intro g x hx hx1 hgx
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g
  obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
  have hx'Z : (x' : G) ∈ Z0 := (mk_mem_bar_iff_sec4 hQZ0 x').mp hx
  have hx'Q : (x' : G) ∉ Q := fun h => hx1 ((QuotientGroup.eq_one_iff x').mpr h)
  rw [← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff_sec4 hQZ0] at hgx
  exact mk_mem_normalizer_bar_of_normalizer hQZ0 g' (hTI g' g'.2 x' hx'Z hx'Q hgx)

theorem Ctx.yBase (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (h78 : Stroth78Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZNc : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    {L : Subgroup G} (hL : Sec717L hc t Z0 L)
    (hLn : ∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) :
    CtxYBase ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q L).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z))) (Nat.card Z) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hc.Rt_le_H0 t hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩
  have hQK : Q ≤ NormH0 M Z Z0 := fun q hq =>
    Subgroup.mem_inf.mpr ⟨hQH hq, Subgroup.le_normalizer (hQZ0 hq)⟩
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hZ0N : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hQL : Q ≤ L := hL.1
  have hLN : L ≤ hc.CN t := hL.2.1
  have hZ0L : Z0 ≤ L := hL.2.2.2.2.2
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hHM : H0 M Z ≤ M := fun x hx => hx.1
  have hKbar := bar_NormH0_eq hc hQZ0 hZ0M
  have hN2 := sec7_CN_pgroup_bar h34 h311a hc hs
  set Hb : Subgroup (Mbar M Q) := bar M Q (H0 M Z) with hHb
  set Vy : Subgroup ↥Hb := (bar M Q Z0).subgroupOf Hb with hVy
  set Ly : Subgroup ↥Hb := (bar M Q L).subgroupOf Hb with hLy
  set Ny : Subgroup ↥Hb := (bar M Q (hc.CN t)).subgroupOf Hb with hNy
  set Ry : Subgroup ↥Hb := (bar M Q (Rt M (LB M Q B) t)).subgroupOf Hb with hRy
  set Ky : Subgroup ↥Hb := (bar M Q (NormH0 M Z Z0)).subgroupOf Hb with hKy
  have hVH : bar M Q Z0 ≤ Hb := bar_mono' hZ0H0
  have hNH : bar M Q (hc.CN t) ≤ Hb := bar_mono' (hNR.trans hRH)
  have hRH' : bar M Q (Rt M (LB M Q B) t) ≤ Hb := bar_mono' hRH
  have hLH' : bar M Q L ≤ Hb := bar_mono' ((hLN.trans hNR).trans hRH)
  have hVLy : Vy ≤ Ly := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hZ0L (Subgroup.mem_subgroupOf.mp hx))
  have hLNy : Ly ≤ Ny := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hLN (Subgroup.mem_subgroupOf.mp hx))
  have hNRy : Ny ≤ Ry := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hNR (Subgroup.mem_subgroupOf.mp hx))
  have hRKy : Ry ≤ Ky := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hRK (Subgroup.mem_subgroupOf.mp hx))
  have hKV : ∀ g ∈ Subgroup.normalizer (Vy : Set ↥Hb), g ∈ Ky := by
    intro g hg
    rw [hVy, ← Subgroup.subgroupOf_normalizer_eq hVH] at hg
    have hgn : (g : Mbar M Q) ∈
        Subgroup.normalizer ((bar M Q Z0 : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := hg
    have : (g : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) := by
      rw [hKbar]
      exact mem_NormIn.mpr ⟨g.2, hgn⟩
    exact this
  have hN2y : IsPGroup 2 ↥Ny := hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hNn : ∀ k ∈ Ky, k ∈ Subgroup.normalizer (Ny : Set ↥Hb) := by
    intro k hk
    have hk' : (k : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) := Subgroup.mem_subgroupOf.mp hk
    obtain ⟨y, hyk⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (k : Mbar M Q)
    have hy' : (y : G) ∈ NormH0 M Z Z0 := (mk_mem_bar_iff_sec4 hQK y).mp (hyk ▸ hk')
    have hmem := mk_mem_normalizer_bar_of_normalizer hQN y
      (conjSubgroup_eq_self_iff.mp (sec7_conj_CN_eq hZt hZcard hc hs hZ0 hy'))
    rw [hNy, ← Subgroup.subgroupOf_normalizer_eq hNH]
    show (k : Mbar M Q) ∈ Subgroup.normalizer ((bar M Q (hc.CN t) : Subgroup (Mbar M Q)) :
      Set (Mbar M Q))
    rw [← hyk]
    exact hmem
  have hRn : ∀ k ∈ Ky, k ∈ Subgroup.normalizer (Ry : Set ↥Hb) := by
    intro k hk
    have hk' : (k : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) := Subgroup.mem_subgroupOf.mp hk
    obtain ⟨y, hyk⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (k : Mbar M Q)
    have hy' : (y : G) ∈ NormH0 M Z Z0 := (mk_mem_bar_iff_sec4 hQK y).mp (hyk ▸ hk')
    have hcR : conjSubgroup (y : G) (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
      (sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hy').1
    have hmem := mk_mem_normalizer_bar_of_normalizer hQR y (conjSubgroup_eq_self_iff.mp hcR)
    rw [hRy, ← Subgroup.subgroupOf_normalizer_eq hRH']
    show (k : Mbar M Q) ∈ Subgroup.normalizer ((bar M Q (Rt M (LB M Q B) t) :
      Subgroup (Mbar M Q)) : Set (Mbar M Q))
    rw [← hyk]
    exact hmem
  have hLnY : ∀ k ∈ Ky, k ∈ Subgroup.normalizer (Ly : Set ↥Hb) := by
    intro k hk
    have hk' : (k : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) := Subgroup.mem_subgroupOf.mp hk
    obtain ⟨y, hyk⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (k : Mbar M Q)
    have hy' : (y : G) ∈ NormH0 M Z Z0 := (mk_mem_bar_iff_sec4 hQK y).mp (hyk ▸ hk')
    have hmem := mk_mem_normalizer_bar_of_normalizer hQL y
      (conjSubgroup_eq_self_iff.mp (hLn (y : G) hy'))
    rw [hLy, ← Subgroup.subgroupOf_normalizer_eq hLH']
    show (k : Mbar M Q) ∈ Subgroup.normalizer ((bar M Q L : Subgroup (Mbar M Q)) :
      Set (Mbar M Q))
    rw [← hyk]
    exact hmem
  have hZNy : ∀ x ∈ Ny, (∀ n ∈ Ny, x * n = n * x) → x ∈ Vy := by
    intro x hx hxc
    obtain ⟨x0, hx0⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
    have hx0N : (x0 : G) ∈ hc.CN t :=
      (mk_mem_bar_iff_sec4 hQN x0).mp (hx0 ▸ Subgroup.mem_subgroupOf.mp hx)
    have hx0Z : (x0 : G) ∈ Z0 := by
      refine (hZNc (x0 : G)).mpr ⟨hx0N, fun r hr => ?_⟩
      have hrM : r ∈ M := hc.Rt_le_M t (hNR hr)
      have hrbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩ ∈ bar M Q (hc.CN t) :=
        (mk_mem_bar_iff_sec4 hQN ⟨r, hrM⟩).mpr hr
      have hrH : QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩ ∈ Hb := hNH hrbar
      have hcomm := hxc ⟨_, hrH⟩ (Subgroup.mem_subgroupOf.mpr hrbar)
      have hcomm' : QuotientGroup.mk' (Q.subgroupOf M) x0 *
          QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩ =
          QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩ * QuotientGroup.mk' (Q.subgroupOf M) x0 := by
        have h1 := congrArg Subtype.val hcomm
        simp only [Subgroup.coe_mul] at h1
        rw [← hx0] at h1
        exact h1
      exact mem_Q_of_mk_mul_comm hcomm'
    exact Subgroup.mem_subgroupOf.mpr
      (by rw [← hx0]; exact (mk_mem_bar_iff_sec4 hQZ0 x0).mpr hx0Z)
  have hVcy : ∀ v ∈ Vy, ∀ n ∈ Ny, v * n = n * v := by
    intro v hv n hn
    apply Subtype.ext
    exact Ctx.recog_bar_Z0_comm hc hZ0 _ (Subgroup.mem_subgroupOf.mp hv) _
      (bar_mono' hNR (Subgroup.mem_subgroupOf.mp hn))
  have hVcard : Nat.card Vy = Nat.card Z := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv]
    exact card_bar_Z0 hc hs hZcard hZ0
  have hCNcard : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 9 := by
    have h := h78 G M Q Z B hc n t hs.toSec5 hs.large hs.notPlus4 3 (by norm_num) (Or.inl hp3)
    rcases h with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | omega
  have hNcard : Nat.card Ny = Nat.card Z ^ 9 := by
    have h1 := bar_card_mul_card_of_le (M := M) (S := hc.CN t) hQN
      (fun x hx => hc.Rt_le_M t (hNR hx))
    have h2 : Nat.card (bar M Q (hc.CN t)) * Nat.card Q = Nat.card Z ^ 9 * Nat.card Q := by
      rw [h1, hCNcard, Nat.mul_comm]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hLcard : Nat.card Ly = Nat.card Z ^ 5 := by
    have h1 := bar_card_mul_card_of_le (M := M) (S := L) hQL
      (fun x hx => hc.Rt_le_M t (hNR (hLN hx)))
    have h2 : Nat.card (bar M Q L) * Nat.card Q = Nat.card Z ^ 5 * Nat.card Q := by
      rw [h1, hL.2.2.1, Nat.mul_comm]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH').toEquiv]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hKeq : Ky = Subgroup.normalizer (Vy : Set ↥Hb) := by
    refine le_antisymm (fun k hk => ?_) hKV
    have hk' : (k : Mbar M Q) ∈ NormIn Hb (bar M Q Z0) := by
      rw [← hKbar]
      exact Subgroup.mem_subgroupOf.mp hk
    rw [hVy, ← Subgroup.subgroupOf_normalizer_eq hVH]
    exact (mem_NormIn.mp hk').2
  have hti : ∀ g : ↥Hb, ∀ a ∈ Vy, a ≠ 1 → g * a * g⁻¹ ∈ Vy →
      g ∈ Subgroup.normalizer (Vy : Set ↥Hb) := by
    intro g a ha ha1 hga
    have h1 := Ctx.ti_bar hQZ0 hTI (g : Mbar M Q) (a : Mbar M Q) (Subgroup.mem_subgroupOf.mp ha)
      (fun h => ha1 (Subtype.ext h)) (Subgroup.mem_subgroupOf.mp hga)
    rw [hVy, ← Subgroup.subgroupOf_normalizer_eq hVH]
    exact h1
  have hVsq : ∀ a ∈ Vy, a * a = 1 := by
    intro a ha
    apply Subtype.ext
    have := sq_eq_one_bar hc hs hZc hZ0 (a : Mbar M Q) (Subgroup.mem_subgroupOf.mp ha)
    simpa [pow_two] using this
  have hLcomm : ∀ a ∈ Ly, ∀ b ∈ Ly, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (a : Mbar M Q)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (b : Mbar M Q)
    have hxL : (x : G) ∈ L := (mk_mem_bar_iff_sec4 hQL x).mp (hx ▸ Subgroup.mem_subgroupOf.mp ha)
    have hyL : (y : G) ∈ L := (mk_mem_bar_iff_sec4 hQL y).mp (hy ▸ Subgroup.mem_subgroupOf.mp hb)
    apply Subtype.ext
    show (a : Mbar M Q) * (b : Mbar M Q) = (b : Mbar M Q) * (a : Mbar M Q)
    rw [← hx, ← hy]
    exact step716_mk_mul_comm (hL.2.2.2.2.1 (x : G) hxL (y : G) hyL)
  exact ⟨hKeq, hVLy, hLNy, hNRy, hRKy, hN2y, hNn, hRn, hLnY, hZNy, hVcy, hVcard, hNcard, hLcard,
    hti, hVsq, hLcomm⟩

end CFSG.RankThree.GF2n.Stroth80


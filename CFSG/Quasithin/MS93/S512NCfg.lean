module

public import CFSG.Quasithin.MS93.S512NW
public import CFSG.Quasithin.MS93.S512NV

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512N

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

namespace Cfg

variable {h : PUHyp M T L} {δ μ₁ μ₂ : Vtx (puAmalgam h.le)} (hc : Cfg h k δ μ₁ μ₂)
include hc

theorem commutator_zm_δ_qv_le (hk : k = 1) :
    ⁅ZM _ δ, Qv _ (baseB (puAmalgam h.le))⁆ ≤ S5.bSub h.le L (baseA _) := by
  have := finite_zm h hc.isMVtx_δ
  rw [Subgroup.commutator_le]
  intro z hz t ht
  have htδ : t ∈ stab _ δ := qv_le_stab_of_adj _ hc.adj ht
  have htα : t ∈ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_adj _ (adj_baseA_baseB (puAmalgam h.le)).symm ht
  have hBn := S310.stab_le_normalizer_bSub h (baseA (puAmalgam h.le))
  have htz : t * z * t⁻¹ ∈ ZM _ δ :=
    (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _ htδ) z).1 hz
  by_cases hzB : z ∈ S5.bSub h.le L (baseA _)
  · have e : ⁅z, t⁆ = z * (t * z⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hzB ((Subgroup.mem_normalizer_iff.1 (hBn htα) _).1 (inv_mem hzB))
  · set H : Subgroup ↥(ZM _ δ) := (S5.bSub h.le L (baseA _)).subgroupOf (ZM _ δ) with hH
    have hzH : (⟨z, hz⟩ : ↥(ZM _ δ)) ∉ H := hzB
    have htzH : (⟨t * z * t⁻¹, htz⟩ : ↥(ZM _ δ)) ∉ H := fun h1 => hzB (by
      have h2 := (Subgroup.mem_normalizer_iff.1 (hBn (inv_mem htα)) _).1
        (Subgroup.mem_subgroupOf.1 h1)
      simpa [mul_assoc] using h2)
    have hidx : H.index = 2 := by
      have h1 : H.index ≤ 2 := by
        have := hc.relIndex_bSub_δ
        rw [hk, pow_one] at this
        exact this.le
      have h2 : H.index ≠ 1 := fun h1 => hzH (by
        rw [Subgroup.index_eq_one.1 h1]
        exact Subgroup.mem_top _)
      have h3 : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
      omega
    have hu : (⟨z, hz⟩ : ↥(ZM _ δ))⁻¹ * ⟨t * z * t⁻¹, htz⟩ ∈ H := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false (fun h1 => hzH (by simpa using H.inv_mem h1)) htzH
    have hu' : z⁻¹ * (t * z * t⁻¹) ∈ S5.bSub h.le L (baseA _) := hu
    have hZc : ZM _ δ ≤ Subgroup.centralizer (ZM _ δ : Set (puAmalgam h.le).Universal) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (isElemAbelian_zm _ h.hyp20 h.critDist_pos hc.isMVtx_δ).1
    set w := t * z * t⁻¹ with hw
    have hcomm : z * w = w * z := Subgroup.mem_centralizer_iff.1 (hZc htz) z hz
    have hcomm' : z * w⁻¹ = w⁻¹ * z := by
      calc z * w⁻¹ = w⁻¹ * (w * z) * w⁻¹ := by group
        _ = w⁻¹ * (z * w) * w⁻¹ := by rw [hcomm]
        _ = w⁻¹ * z := by group
    have e : ⁅z, t⁆ = (z⁻¹ * w)⁻¹ := by
      rw [commutatorElement_def, mul_inv_rev, inv_inv, ← hcomm', hw]
      group
    rw [e]
    exact inv_mem hu'

theorem natHyp (hd : S5.IsSp4Data M T L k F a) :
    NatHyp h k (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁)) (ZM _ μ₂) (ZM _ δ)
      (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) ⊓ Qv _ μ₁) where
  b := hc.two_lt
  vv := hc.nclStab_le_vv
  vn := S310.stab_le_normalizer_nclStab _ _ _
  comm := hc.commutator_le_bSub hd
  sq _ hv := hc.sq_mem_bSub hd hv
  ne hle := by
    have h1 := Subgroup.relIndex_eq_one.2 ((le_nclStab _ _ _).trans hle :
      ZM _ μ₁ ≤ S5.bSub h.le L (baseA (puAmalgam h.le)))
    rw [hc.idxB] at h1
    have : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
    omega
  qv := hc.commutator_qv_le_bSub hd
  es := zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hc.crit₂
  ee := isElemAbelian_zm _ h.hyp20 h.critDist_pos hc.isMVtx_μ₂
  eq := hc.relIndex_qv_zm_μ₂ hd
  eu := hc.relIndex_centralizer_zm_μ₂
  zv := hc.zm_δ_le
  yv := inf_le_left
  zy x hx := by
    obtain ⟨z, hz, hzx⟩ := hc.exists_mul_zm_δ hd hx
    refine ⟨z, hz, Subgroup.mem_inf.2 ⟨?_, hzx⟩⟩
    exact (S5.nclStab _ _ _).mul_mem ((S5.nclStab _ _ _).inv_mem (hc.zm_δ_le hz)) hx
  zi := hc.relIndex_bSub_δ.le
  ye := Subgroup.commutator_le.2 fun _ hx _ hw =>
    S310.zm_le_bSub h (isMVtx_baseA _) (hc.commutator_mem_zm hd hx hw)
  gen := hc.le_zm_δ_sup_commutator
  zt := hc.commutator_zm_δ_qv_le

theorem commutator_mem_critR (hd : S5.IsSp4Data M T L k F a) {z v : (puAmalgam h.le).Universal}
    (hz : z ∈ ZM _ μ₁) (hv : v ∈ S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁)) :
    ⁅z, v⁆ ∈ ⁅ZM _ μ₁, ZM _ δ⁆ := by
  obtain ⟨d, hd', hdv⟩ := hc.exists_mul_zm_δ hd hv
  set n := d⁻¹ * v with hn
  have hcomm : z * n = n * z :=
    Subgroup.mem_centralizer_iff.1
      (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ h.hyp20 hc.isMVtx_μ₁) hdv) z hz
  have hn' : n * z⁻¹ = z⁻¹ * n := by
    calc n * z⁻¹ = z⁻¹ * (z * n) * z⁻¹ := by group
      _ = z⁻¹ * (n * z) * z⁻¹ := by rw [hcomm]
      _ = z⁻¹ * n := by group
  have hv' : v = d * n := by rw [hn]; group
  have e : ⁅z, v⁆ = ⁅z, d⁆ := by
    rw [hv', commutatorElement_def, commutatorElement_def]
    calc z * (d * n) * z⁻¹ * (d * n)⁻¹ = z * d * (n * z⁻¹) * n⁻¹ * d⁻¹ := by group
      _ = z * d * (z⁻¹ * n) * n⁻¹ * d⁻¹ := by rw [hn']
      _ = z * d * z⁻¹ * d⁻¹ := by group
  rw [e]
  exact Subgroup.commutator_mem_commutator hz hd'

theorem commutator_le_dSub (hd : S5.IsSp4Data M T L k F a)
    (hR : ⁅ZM _ μ₁, ZM _ δ⁆ ≤ S5.dSub h.le L (baseA _)) :
    ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁),
        S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁)⁆ ≤ S5.dSub h.le L (baseA _) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hDn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (S5.dSub h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    S310.le_normalizer_inf (stab_le_normalizer_qv _ _)
      (le_normalizer_centralizer (stab_le_normalizer_puTrans h.le hLn _))
  have hVn := S310.stab_le_normalizer_nclStab (puAmalgam h.le) (baseA (puAmalgam h.le)) (ZM _ μ₁)
  have hkey : ⁅ZM _ μ₁, S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁)⁆ ≤
      S5.dSub h.le L (baseA _) := by
    rw [Subgroup.commutator_le]
    exact fun z hz v hv => hR (hc.commutator_mem_critR hd hz hv)
  refine commutator_iSup_le (fun g => ?_) fun g => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hDn (mul_mem (mul_mem g.2 (hc.zm_μ₁_le_qv.trans (qv_le_stab _ _) hx)) (inv_mem g.2))
  · have hVg := map_conj_eq_of_mem_normalizer (hVn g.2)
    have hDg := map_conj_eq_of_mem_normalizer (hDn g.2)
    rw [← hVg, ← Subgroup.map_commutator, ← hDg]
    exact Subgroup.map_mono hkey

end Cfg

omit [Fintype F] in
theorem Cfg.of_chain (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)} (hch : S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂)
    (hQ : (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k)
    (hB : (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k)
    (hB₂ : (S5.bSub h.le L μ₁).relIndex (ZM _ μ₂) = 2 ^ k) :
    Cfg h k (geo _ (baseA (puAmalgam h.le)) α' 2) μ₁ μ₂ := by
  obtain ⟨hc, hαβ, hcμ, hmid, hy, -, hc₂, -, hmid₂, hy₂⟩ := chain_geo h hb4 hch
  obtain ⟨-, -, -, -, -, h2, -⟩ := pair_geo h hb4 hc
  refine ⟨hb4, ?_, hcμ, hmid, hy, hc₂, hmid₂, hy₂, hQ, hB, hB₂⟩
  rw [← hαβ]
  exact h2

end S512N

end CFSG.Quasithin.MS93

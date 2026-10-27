module

public import CFSG.RankThree.GF2n.Stroth80.DictB
public import CFSG.RankThree.GF2n.Tim77Prop24Core
public import CFSG.RankThree.GF2n.Stroth80.QuadIso

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem stroth_2_6_of_le_M {M Q Z : Subgroup G} (hh : StrothHyp M Q Z) {K : Type} [Field K]
    [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    {g t : G} (htQ : t ∈ Q) (htB : t ∈ conjSubgroup g Z) (htZ : t ∉ Z)
    (hBM : conjSubgroup g Z ≤ M) : conjSubgroup g Z ≤ Q := by
  classical
  set B := conjSubgroup g Z with hB
  have hh79 := hh.toHyp79
  have ht1 : t ≠ 1 := fun h1 => htZ (h1 ▸ Z.one_mem)
  have hBZ : B ≠ Z := fun e => htZ (e ▸ htB)
  have hZB : Z ⊓ B = ⊥ := inf_conjSubgroup_eq_bot_of_isTI hh.ti hBZ
  have hTIB : IsTI B := isTI_conjSubgroup hh.ti g
  have hCt : ∀ c, c * t = t * c → c ∈ Subgroup.normalizer (B : Set G) := fun c hc =>
    Tim77.mem_normalizer_of_commute_of_isTI hTIB htB ht1 hc
  have hZt : ∀ z ∈ Z, z * t = t * z := fun z hz => hh79.V_central hz htQ
  have hBc : ∀ x ∈ B, ∀ z ∈ Z, x * z * x⁻¹ = z := by
    intro x hxB z hz
    have hxN : x ∈ Subgroup.normalizer (Z : Set G) := by
      rw [hh.normalizer_Z.1]; exact hBM hxB
    have hzN := hCt z (hZt z hz)
    have h1 : x * z * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hxN z).mp hz
    have h2 : z * x⁻¹ * z⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hzN _).mp (B.inv_mem hxB)
    have hmem : x * z * x⁻¹ * z⁻¹ ∈ Z ⊓ B := by
      refine ⟨Z.mul_mem h1 (Z.inv_mem hz), ?_⟩
      have : x * z * x⁻¹ * z⁻¹ = x * (z * x⁻¹ * z⁻¹) := by group
      rw [this]
      exact B.mul_mem hxB h2
    rw [hZB, Subgroup.mem_bot] at hmem
    have := mul_inv_eq_one.mp hmem
    exact this
  by_contra hBQ
  obtain ⟨x, hxB, hxQ⟩ : ∃ x ∈ B, x ∉ Q := by
    by_contra hcon
    push Not at hcon
    exact hBQ hcon
  have hxM : x ∈ M := hBM hxB
  have hxNQ : x ∈ Subgroup.normalizer (Q : Set G) := hh.Q_normal.2 hxM
  obtain ⟨T, hTπ, hTQ, hTB⟩ := h.linear_of_centralizes hxM (hBc x hxB)
  have ht0 : M₀.π t ≠ 0 := fun h0 => htZ ((M₀.π_ker t htQ).mp h0)
  have hts : M₀.Qf (M₀.π t) = 0 := by
    have hsq : t ^ 2 = 1 := (CFSG.Open.IsElemAbelian.map hh.isElemAbelian_Z
      (MulAut.conj g).toMonoidHom).2 t htB
    exact (M₀.sq_iff_Qf h.reg htQ).mp hsq
  have hD : ∀ v : M₀.E, M₀.B v (M₀.π t) = 0 → ∃ u ∈ B ⊓ Q, M₀.π u = v - T v := by
    intro v hv
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj v
    have hyt : y * t = t * y := (M₀.comm_iff_B h.reg hyQ htQ).mpr hv
    have hyN := hCt y hyt
    refine ⟨⁅y, x⁆, ⟨?_, ?_⟩, ?_⟩
    · rw [commutatorElement_def]
      exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN x).mp hxB) (B.inv_mem hxB)
    · rw [show ⁅y, x⁆ = y * (x * y⁻¹ * x⁻¹) by rw [commutatorElement_def]; group]
      exact Q.mul_mem hyQ ((Subgroup.mem_normalizer_iff.mp hxNQ _).mp (Q.inv_mem hyQ))
    · rw [show ⁅y, x⁆ = y * (x * y⁻¹ * x⁻¹) by rw [commutatorElement_def]; group,
        M₀.π_mul _ hyQ _ ((Subgroup.mem_normalizer_iff.mp hxNQ _).mp (Q.inv_mem hyQ)),
        hTπ _ (Q.inv_mem hyQ), Tim79.QuadModel.pi_inv M₀ hyQ, map_neg]
      abel
  have hDzero : ∀ v : M₀.E, M₀.B v (M₀.π t) = 0 → T v = v := by
    intro v hv
    by_contra hne
    set d := v - T v with hd
    have hd0 : d ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0).symm
    have hmul : ∀ c : K, ∃ u ∈ B ⊓ Q, M₀.π u = c • d := by
      intro c
      have hcv : M₀.B (c • v) (M₀.π t) = 0 := by
        rw [map_smul, LinearMap.smul_apply, hv, smul_zero]
      obtain ⟨u, hu, hπ⟩ := hD (c • v) hcv
      exact ⟨u, hu, by rw [hπ, hd, smul_sub, map_smul]⟩
    choose F hFmem hFπ using hmul
    have hinj : Function.Injective (fun c : K => (⟨F c, hFmem c⟩ : ↥(B ⊓ Q))) := by
      intro c c' hcc'
      have h1 : F c = F c' := congrArg Subtype.val hcc'
      have h2 : c • d = c' • d := by rw [← hFπ c, ← hFπ c', h1]
      exact smul_left_injective K hd0 h2
    have hle : Nat.card K ≤ Nat.card ↥(B ⊓ Q) := Nat.card_le_card_of_injective _ hinj
    have hlt : Nat.card ↥(B ⊓ Q) < Nat.card B := by
      have hrel : (B ⊓ Q).relIndex B ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        intro hle'
        exact hxQ (hle' hxB).2
      have h1 := Subgroup.card_mul_index ((B ⊓ Q).subgroupOf B)
      have h2 : ((B ⊓ Q).subgroupOf B).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h3 : Nat.card ↥((B ⊓ Q).subgroupOf B) = Nat.card ↥(B ⊓ Q) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      have h4 : 2 ≤ ((B ⊓ Q).subgroupOf B).index := by
        have : ((B ⊓ Q).subgroupOf B).index ≠ 1 := hrel
        omega
      have h5 : 0 < Nat.card ↥((B ⊓ Q).subgroupOf B) := Nat.card_pos
      rw [h3] at h1 h5
      nlinarith
    have hcardB : Nat.card B = Nat.card K := by
      rw [hB, card_conjSubgroup, h.card]
    omega
  have hT1 : ∀ e : M₀.E, T e = e :=
    Tim79.QuadModel.eq_one_of_fix_perp (T := (T : M₀.E →ₗ[K] M₀.E)) hTQ ht0 hts hDzero
  apply hxQ
  refine hh.centralizer_Qt x hxM (fun y hy => ?_)
  have hyx : x * y * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxNQ y).mp hy
  exact (M₀.comm_mem_iff hy hyx).mpr (by rw [hTπ y hy, hT1])

end CFSG.RankThree.GF2n.Stroth80

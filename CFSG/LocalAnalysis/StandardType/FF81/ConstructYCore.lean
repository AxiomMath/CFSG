module

public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYCen
import CFSG.LargeExtraspecial.A2ModCfgSL

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT (blockSL blockSL2)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G} {K : ℕ → Subgroup G}
  {t : G}

theorem FrameSystem.le_centralizer_L (hA : HypA G n b L) (hF : FrameSystem n b L K t)
    {R : Subgroup G} (hRC : R ≤ Subgroup.centralizer ({b} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal)
    (hR3 : ¬ 3 ∣ Nat.card R) : ∀ r ∈ R, ∀ y ∈ L, r * y = y * r := by
  have hn : 3 ≤ n := by rcases hA.n_cases with rfl | rfl <;> omega
  obtain ⟨ψL, hinjL, hrangeL, -⟩ := hF.sysL.exists_injective_marking hn
  have hLs : IsSimpleGroup ↥L := by
    have := CFSG.LargeExtraspecial.A2Mod.isSimpleGroup_sl_zmodTwo (k := n + 1) (by omega)
    exact ((MonoidHom.ofInjective hinjL).trans (MulEquiv.subgroupCongr hrangeL)).symm.isSimpleGroup
  have hcR : ∀ c ∈ Subgroup.centralizer ({b} : Set G), ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro c hc r hr
    have h := hRn.conj_mem ⟨r, hRC hr⟩ (Subgroup.mem_subgroupOf.mpr hr) ⟨c, hc⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  have hcL : ∀ c ∈ Subgroup.centralizer ({b} : Set G), ∀ y ∈ L, c * y * c⁻¹ ∈ L :=
    fun c hc y hy => (Subgroup.mem_normalizer_iff.mp (hA.nor hc) y).mp hy
  obtain ⟨x3, hx3K, hx3o, -⟩ := hF.conj_b 2 (by omega)
  have hx3L : x3 ∈ L := hF.le_L le_rfl (by omega) hx3K
  have hRL : ∀ z ∈ R, z ∈ L → z = 1 := by
    have := hLs
    have hN : ((R ⊓ L).subgroupOf L).Normal := by
      refine ⟨fun z hz y => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      refine ⟨?_, ?_⟩
      · simpa using hcR y (hA.le y.2) z hz.1
      · simpa using L.mul_mem (L.mul_mem y.2 hz.2) (L.inv_mem y.2)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ L).subgroupOf L) with h | h
    · intro z hzR hzL
      have hz : (⟨z, hzL⟩ : ↥L) ∈ (R ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr ⟨hzR, hzL⟩
      rw [h, Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
    · exfalso
      have hx : (⟨x3, hx3L⟩ : ↥L) ∈ (R ⊓ L).subgroupOf L := h ▸ Subgroup.mem_top _
      have hx3R : x3 ∈ R := (Subgroup.mem_subgroupOf.mp hx).1
      exact hR3 (hx3o ▸ Subgroup.orderOf_dvd_natCard R hx3R)
  intro r hr y hy
  have hc : r * y * r⁻¹ * y⁻¹ = 1 := by
    refine hRL _ ?_ ?_
    · have h := R.mul_mem hr (hcR y (hA.le hy) r⁻¹ (R.inv_mem hr))
      rwa [show r * (y * r⁻¹ * y⁻¹) = r * y * r⁻¹ * y⁻¹ by group] at h
    · exact L.mul_mem (hcL r (hRC hr) y hy) (L.inv_mem hy)
  calc r * y = r * y * r⁻¹ * y⁻¹ * (y * r) := by group
    _ = y * r := by rw [hc, one_mul]

theorem FrameSystem.core_of_72 (hA : HypA G n b L) (hF : FrameSystem n b L K t) [NeZero n]
    {ρ : SL(2, ZMod 2)} (hρ : (ρ : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 1])
    (h72 : ∀ (L' : Subgroup G) (φ : ↥L' ≃* SL(n + 1, ZMod 2)) (w : ↥L'),
      φ w = blockSL2 (ZMod 2) n 0 ρ → ∀ x : G, x ∈ Subgroup.normalizer (L' : Set G) →
        Nat.Coprime (orderOf x) 3 → x * (w : G) = w * x →
        (∀ B : SL(n - 1, ZMod 2), x * (φ.symm (blockSL (ZMod 2) (n + 1) (n - 1) 2
          (by have := NeZero.pos n; omega) B) : G) =
            (φ.symm (blockSL (ZMod 2) (n + 1) (n - 1) 2 (by have := NeZero.pos n; omega) B) :
              G) * x) →
        ∀ y ∈ L', x * y = y * x) :
    ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b} : Set G) →
      (R.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
        R ≤ Subgroup.centralizer ((⨆ i : Fin (n + 2), K (i : ℕ) : Subgroup G) : Set G) := by
  intro R hRC hRn hR3
  have hn4 : 4 ≤ n := by rcases hA.n_cases with rfl | rfl <;> omega
  have hRL := hF.le_centralizer_L hA hRC hRn hR3
  obtain ⟨g, hgb, hLg, -⟩ := hF.tau
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨ψ, hinj, hrange, hblk⟩ := hF.sysL'.exists_injective_marking (by omega : 3 ≤ k + 2)
  let φ : ↥(⨆ i : Fin (k + 2), K (i : ℕ)) ≃* SL(k + 2 + 1, ZMod 2) :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm
  have hφs : ∀ B : SL(k + 2 + 1, ZMod 2),
      ((φ.symm B : ↥(⨆ i : Fin (k + 2), K (i : ℕ))) : G) = ψ B := fun B => by
    simp only [φ, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    exact MonoidHom.ofInjective_apply hinj
  have hbK : b ∈ K 0 := by
    rw [hF.K0]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  rw [← hblk ⟨0, by omega⟩] at hbK
  have hb' := eq_or_eq_inv_of_mem_map_blockSL2 hinj hρ ⟨0, by omega⟩ hA.ord hbK
  rw [show (⟨0, by omega⟩ : Fin (k + 2)) = 0 from Fin.ext (by simp)] at hb'
  let w : ↥(⨆ i : Fin (k + 2), K (i : ℕ)) := φ.symm (blockSL2 (ZMod 2) (k + 2) 0 ρ)
  have hw : φ w = blockSL2 (ZMod 2) (k + 2) 0 ρ := φ.apply_symm_apply _
  have hwb : (w : G) = ψ (blockSL2 (ZMod 2) (k + 2) 0 ρ) := hφs _
  have hJL : (blockSL (ZMod 2) (k + 2 + 1) (k + 1) 2 (by omega)).range.map ψ ≤ L := by
    rw [range_blockSL_two_eq_iSup, Subgroup.map_iSup]
    refine iSup_le fun j => ?_
    rw [hblk ⟨(j : ℕ) + 2, by omega⟩]
    exact hF.le_L (by simp) (by simp; omega)
  have hRLg : ∀ x ∈ R, ∀ y ∈ ⨆ i : Fin (k + 2), K (i : ℕ), x * y = y * x := by
    intro x hx
    have hgbL : g * b * g⁻¹ ∈ L := hF.le_L (by omega) (by omega) hgb
    have hxN : x ∈ Subgroup.normalizer
        (((⨆ i : Fin (k + 2), K (i : ℕ)) : Subgroup G) : Set G) := by
      rw [hLg]
      exact hA.centralizer_conj_le_normalizer g
        (Subgroup.mem_centralizer_singleton_iff.mpr (hRL x hx _ hgbL))
    have hx3 : Nat.Coprime (orderOf x) 3 := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_)
      exact hR3 (h3.trans (Subgroup.orderOf_dvd_natCard R hx))
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp (hRC hx)
    have hxw : x * (w : G) = w * x := by
      rw [hwb]
      rcases hb' with h | h
      · rw [← h]
        exact hxb
      · rw [h] at hxb
        exact Commute.inv_right_iff.mp hxb
    refine h72 _ φ w hw x hxN hx3 hxw fun B => ?_
    rw [hφs]
    exact hRL x hx _ (hJL ⟨_, ⟨B, rfl⟩, rfl⟩)
  rw [Subgroup.le_centralizer_iff]
  refine iSup_le fun i => ?_
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hi : (i : ℕ) < k + 2
  · exact hRLg x hx y (le_iSup (fun j : Fin (k + 2) => K (j : ℕ)) ⟨i, hi⟩ hy)
  · exact hRL x hx y (hF.le_L (by omega) i.2 hy)

end CFSG.StandardType.FF81

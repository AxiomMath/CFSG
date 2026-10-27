module

public import CFSG.LocalAnalysis.StandardType.FF81.FrameConj
public import CFSG.LocalAnalysis.StandardType.FF81.FrameAut
public import CFSG.LocalAnalysis.StandardType.FF81.FrameModel

public section

namespace CFSG.StandardType.FF81

open scoped MatrixGroups

variable {G : Type} [Group G] {n : ℕ} {b : G} {L : Subgroup G}

theorem exists_swap_of_containsMonomial {z : Fin 3 → ↥L} (h : ContainsMonomial b z) :
    ∃ τ : G, τ * b * τ⁻¹ = z 0 ∧ τ * (z 0 : G) * τ⁻¹ = b ∧ τ * (z 1 : G) * τ⁻¹ = z 1 ∧
      τ * (z 2 : G) * τ⁻¹ = z 2 := by
  obtain ⟨τ, -, hτ⟩ := h (Equiv.swap 0 1) (fun _ => 1) (by decide)
  have h0 : (Equiv.swap (0 : Fin 4) 1) 0 = 1 := by decide
  have h1 : (Equiv.swap (0 : Fin 4) 1) 1 = 0 := by decide
  have h2 : (Equiv.swap (0 : Fin 4) 1) 2 = 2 := by decide
  have h3 : (Equiv.swap (0 : Fin 4) 1) 3 = 3 := by decide
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · have h := hτ 0
    simp only [xs, GGFF.zs, h0, ZMod.val_one, pow_one] at h
    simpa using h
  · have h := hτ 1
    simp only [xs, GGFF.zs, h1, ZMod.val_one, pow_one] at h
    simpa using h
  · have h := hτ 2
    simp only [ZMod.val_one, pow_one] at h
    rw [show xs b z ((Equiv.swap 0 1) 2) = xs b z 2 from
      congrArg (fun i : Fin 4 => xs b z i) h2] at h
    simpa [xs, GGFF.zs] using h
  · have h := hτ 3
    simp only [ZMod.val_one, pow_one] at h
    rw [show xs b z ((Equiv.swap 0 1) 3) = xs b z 3 from
      congrArg (fun i : Fin 4 => xs b z i) h3] at h
    simpa [xs, GGFF.zs] using h

private lemma mem_map_conj_coe {τ : G} (y : ↥L) :
    τ * (y : G) * τ⁻¹ ∈ L.map (MulAut.conj τ : G →* G) :=
  Subgroup.mem_map.mpr ⟨y, y.2, by
    change (MulAut.conj τ) (y : G) = τ * (y : G) * τ⁻¹
    rw [MulAut.conj_apply]⟩

private lemma conjModel_apply {n : ℕ} (φ : ↥L ≃* SL(n + 1, ZMod 2)) {τ : G} (y : ↥L) :
    (((MulAut.conj τ).subgroupMap L).symm.trans φ)
      (⟨τ * (y : G) * τ⁻¹, mem_map_conj_coe y⟩ :
        ↥(L.map (MulAut.conj τ : G →* G))) = φ y := by
  rw [MulEquiv.trans_apply]
  have hAy : (⟨τ * (y : G) * τ⁻¹, mem_map_conj_coe y⟩ :
        ↥(L.map (MulAut.conj τ : G →* G))) =
      (MulAut.conj τ).subgroupMap L y := by
    apply Subtype.ext
    rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  rw [hAy, MulEquiv.symm_apply_apply]

private lemma conjModel_symm_apply_coe {n : ℕ} (φ : ↥L ≃* SL(n + 1, ZMod 2)) {τ : G}
    (A : SL(n + 1, ZMod 2)) :
    (((((MulAut.conj τ).subgroupMap L).symm.trans φ).symm A :
        ↥(L.map (MulAut.conj τ : G →* G))) : G) =
      τ * (φ.symm A : G) * τ⁻¹ := by
  rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulEquiv.coe_subgroupMap_apply,
    MulAut.conj_apply]

private lemma mem_normalizer_map_conj [Finite G] (hA : HypA G n b L) {z : Fin 3 → ↥L}
    (hz : GGFF.Model ↥L z) {τ x : G} (hτb : τ * b * τ⁻¹ = z 0)
    (hxz : x * (z 0 : G) * x⁻¹ ∈ Subgroup.zpowers (z 0 : G)) :
    x ∈ Subgroup.normalizer ((L.map (MulAut.conj τ : G →* G) : Subgroup G) : Set G) := by
  have hg : (τ⁻¹ * x * τ) * b * (τ⁻¹ * x * τ)⁻¹ ∈ Subgroup.zpowers b := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have hb : (τ⁻¹ * x * τ) * b * (τ⁻¹ * x * τ)⁻¹ = b ^ k := by
      calc
        (τ⁻¹ * x * τ) * b * (τ⁻¹ * x * τ)⁻¹
            = τ⁻¹ * (x * (τ * b * τ⁻¹) * x⁻¹) * τ := by group
        _ = τ⁻¹ * (x * (z 0 : G) * x⁻¹) * τ := by rw [hτb]
        _ = τ⁻¹ * (z 0 : G) ^ k * τ := by rw [hk]
        _ = (τ⁻¹ * (z 0 : G) * τ) ^ k := by
              simpa [MulAut.conj_apply] using
                map_zpow (MulAut.conj τ⁻¹) (z 0 : G) k
        _ = b ^ k := by
              rw [show τ⁻¹ * (z 0 : G) * τ = b from by rw [← hτb]; group]
    rw [hb]
    exact Subgroup.zpow_mem_zpowers b k
  have hgN : τ⁻¹ * x * τ ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact HypA.map_conj_eq hA hz hg
  have hle : (Subgroup.normalizer (L : Set G)).map (MulAut.conj τ : G →* G) ≤
      Subgroup.normalizer ((L.map (MulAut.conj τ : G →* G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_map (MulAut.conj τ : G →* G)
  have hxmem : x ∈ (Subgroup.normalizer (L : Set G)).map
      (MulAut.conj τ : G →* G) :=
    Subgroup.mem_map.mpr ⟨τ⁻¹ * x * τ, hgN, by simp [MulAut.conj_apply, mul_assoc]⟩
  exact hle hxmem

theorem commute_map_conj [Finite G] (hA : HypA G n b L) [NeZero n] {z : Fin 3 → ↥L}
    (hz : GGFF.Model ↥L z) {φ : ↥L ≃* SL(n + 1, ZMod 2)} (hφ0 : φ (z 0) = tOne n) {τ : G}
    (hτb : τ * b * τ⁻¹ = z 0) (hτz : τ * (z 0 : G) * τ⁻¹ = b)
    (hτJ : (frameJ φ).map (MulAut.conj τ).toMonoidHom = frameJ φ) {x : G} (hxb : x * b = b * x)
    (hxJ : ∀ j ∈ frameJ φ, x * j = j * x)
    (hxz : x * (z 0 : G) * x⁻¹ ∈ Subgroup.zpowers (z 0 : G)) (hx3 : Nat.Coprime (orderOf x) 3) :
    ∀ y ∈ L.map (MulAut.conj τ).toMonoidHom, x * y = y * x := by
  have hn : 4 ≤ n := by rcases hA.n_cases with rfl | rfl <;> norm_num
  let L' : Subgroup G := L.map (MulAut.conj τ : G →* G)
  let e : ↥L ≃* ↥L' := (MulAut.conj τ).subgroupMap L
  let φ' : ↥L' ≃* SL(n + 1, ZMod 2) := e.symm.trans φ
  have hA0 : (⟨τ * (z 0 : G) * τ⁻¹, mem_map_conj_coe (z 0)⟩ : ↥L') =
      (MulAut.conj τ).subgroupMap L (z 0) := by
    apply Subtype.ext
    rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  have hφ'w : φ' ((MulAut.conj τ).subgroupMap L (z 0)) = tOne n := by
    rw [← hA0]
    exact (conjModel_apply (L := L) (φ := φ) (τ := τ) (z 0)).trans hφ0
  have hwval : (((MulAut.conj τ).subgroupMap L (z 0) : ↥L') : G) = b := by
    rw [show (((MulAut.conj τ).subgroupMap L (z 0) : ↥L') : G) =
        τ * (z 0 : G) * τ⁻¹ from by
      rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]]
    exact hτz
  have hxN : x ∈ Subgroup.normalizer (L' : Set G) := by
    simpa [L'] using mem_normalizer_map_conj hA hz hτb hxz
  have hxw : x * (((MulAut.conj τ).subgroupMap L (z 0) : ↥L') : G) =
      (((MulAut.conj τ).subgroupMap L (z 0) : ↥L') : G) * x := by
    rw [hwval]
    exact hxb
  have hxJ' : ∀ B : SL(n - 1, ZMod 2),
      x * ((φ'.symm (jBlock n B) : ↥L') : G) =
        ((φ'.symm (jBlock n B) : ↥L') : G) * x := by
    intro B
    have hB : ((φ.symm (jBlock n B) : ↥L) : G) ∈ frameJ φ := by
      rw [frameJ, mem_pullSL_iff, MulEquiv.apply_symm_apply]
      exact MonoidHom.mem_range.mpr ⟨B, rfl⟩
    have hB' : τ * ((φ.symm (jBlock n B) : ↥L) : G) * τ⁻¹ ∈ frameJ φ := by
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj τ).toMonoidHom hB
      rwa [hτJ] at hmem
    have hsymm : ((φ'.symm (jBlock n B) : ↥L') : G) =
        τ * (φ.symm (jBlock n B) : G) * τ⁻¹ :=
      conjModel_symm_apply_coe (L := L) (φ := φ) (τ := τ) (jBlock n B)
    rw [hsymm]
    exact hxJ _ hB'
  change ∀ y ∈ L.map (MulAut.conj τ : G →* G), x * y = y * x
  exact commute_of_commute_centralizer hn φ' hφ'w hxN hx3 hxw hxJ'

end CFSG.StandardType.FF81

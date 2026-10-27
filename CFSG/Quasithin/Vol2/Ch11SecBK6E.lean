module

public import CFSG.Quasithin.Vol2.Ch11SecBK6D
public import CFSG.Quasithin.Vol2.Ch11SecAKA16

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usp qSp nSp nSp_zero)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Open (pCoreOf)
open scoped IsMulCommutative

namespace BK6

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem r2_sp4 (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSp4 L V n) {A : Subgroup G}
    (hAT : A ≤ T) (hA : autI hfl.elem A ∈ E3.aSet n (autI hfl.elem X))
    (hAR : ¬ A ≤ pCoreOf 2 (LOf L V₂ ⊔ T)) :
    ⁅V₂, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₁ ∧
      E3.mQuot A (A ⊓ Subgroup.centralizer (V₂ : Set G)) = n ∧
      E3.mQuot V₂ (V₂ ⊓ Subgroup.centralizer (A : Set G)) = n := by
  obtain ⟨_, K, _, _, _, hK, π, hπ⟩ := exists_real_sp4 hfl hk
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hn := hfl.two_le
  have hV₁V : V₁ ≤ V := hfl.le₁₂.trans hfl.le₂
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hfl.sylow le_sup_left (sup_le Subgroup.le_normalizer hfl.T_le_L)
  have hP := SecA.isSylowTwoOf_autOn hfl.le_normalizer hTL'
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  have hF₁ := isFlagW_of_flag24 hfl hV₁V hfl.cV_le hfl.stable₁ (by rw [hfl.index₁, mul_one])
    hfl.T_le_V₁
  have hF₂ := isFlagW_of_flag24 hfl hfl.le₂ (hfl.cV_le.trans hfl.le₁₂) hfl.stable₂ hfl.index₂
    hfl.T_le_V₂
  obtain ⟨S₁, hS₁, hc₁, hU₁⟩ := exists_eq_pre_of_isFlagW_sp hsq hf hg (by rw [hK]; exact hF₁)
  rw [(eq_std_of_stable_sp hS₁).1 (by rw [hc₁, pow_one])] at hU₁
  obtain ⟨S₂, hS₂, hc₂, hU₂⟩ := exists_eq_pre_of_isFlagW_sp hsq hf hg (by rw [hK]; exact hF₂)
  rw [(eq_std_of_stable_sp hS₂).2.1 hc₂] at hU₂
  have hlf := KA.lineFacts_sp hK4 hf (fun h hh z hz => SecA.autOn_fixes_cV h hh z hz) g
  set e₀ : Fin 2 ⊕ Fin 2 → K := mat 2 K g *ᵥ vec4 1 0 0 0 with he₀
  set e₁ : Fin 2 ⊕ Fin 2 → K := mat 2 K g *ᵥ vec4 0 1 0 0 with he₁
  have hginv : ∀ s t : K, mat 2 K g⁻¹ *ᵥ (s • e₀ + t • e₁) = vec4 s t 0 0 := fun s t => by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, he₀, he₁, mat_inv_mulVec,
      mat_inv_mulVec]
    exact vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4])
  have hgv : ∀ s t : K, mat 2 K g *ᵥ vec4 s t 0 0 = s • e₀ + t • e₁ := fun s t => by
    rw [← hginv s t, mat_mulVec_inv]
  have hform : ∀ (x y z r : K) (w : ↥V) (s t : K), f w = s • e₀ + t • e₁ →
      f (((π (g * (qSp x y z * nSp r) * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) w) =
        (s + r * t) • e₀ + t • e₁ := by
    intro x y z r w s t hst
    rw [hf.act4, KA.gconj_mulVec_sp, hst, hginv, map_mul, ← Matrix.mulVec_mulVec, nSp_mulVec,
      qSp_mulVec, ← hgv]
    congr 1
    exact vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4])
  have hind : ∀ s t : K, s • e₀ + t • e₁ = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have e := hginv s t
    rw [h, Matrix.mulVec_zero] at e
    exact ⟨by simpa [vec4] using (congrFun e (.inl 0)).symm,
      by simpa [vec4] using (congrFun e (.inl 1)).symm⟩
  obtain ⟨w₁, hw₁⟩ := hf.surj e₁
  have hw₁' : f w₁ = (0 : K) • e₀ + (1 : K) • e₁ := by rw [hw₁, zero_smul, one_smul, zero_add]
  have hV₂mem : ∀ w : ↥V, (w : G) ∈ V₂ ↔ ∃ s t : K, f w = s • e₀ + t • e₁ := by
    intro w
    change w ∈ V₂.subgroupOf V ↔ _
    rw [hU₂]
    change f w ∈ gmapSp g (spPlane K) ↔ _
    rw [mem_gmapSp, mem_spPlane]
    constructor
    · rintro ⟨h2, h3⟩
      set x := mat 2 K g⁻¹ *ᵥ f w with hx
      refine ⟨x (.inl 0), x (.inl 1), ?_⟩
      have hx' : x = vec4 (x (.inl 0)) (x (.inl 1)) 0 0 :=
        vec4_eq (by simp [vec4]) (by simp [vec4]) (by simpa [vec4] using h2)
          (by simpa [vec4] using h3)
      rw [← hgv, ← hx', hx, mat_mulVec_inv]
    · rintro ⟨s, t, hst⟩
      rw [hst, hginv]
      exact ⟨rfl, rfl⟩
  have hO2 : ∀ s ∈ pCoreOf 2 (perfectCore (autOn L V ⊓ SecA.stabW (V₂.subgroupOf V))),
      ∀ u ∈ V₂.subgroupOf V, s u = u := by
    rw [hU₂]
    exact hlf.1
  refine r2_of_param hfl hK hf.map_mul_inv (fun a b h => (hf.eq_iff a b).mp h) hf.surj hind
    (fun w => by
      change w ∈ V₁.subgroupOf V ↔ _
      rw [hU₁]
      exact mem_gmapSp_spLine_iff) hV₂mem ?_ ?_ hO2 hAT hA hAR
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := (hg p).mp hp
    obtain ⟨x, y, z, r, rfl⟩ := hu
    exact ⟨r, hform x y z r⟩
  · intro p hp h
    obtain ⟨u, hu, rfl⟩ := (hg p).mp hp
    obtain ⟨x, y, z, r, rfl⟩ := hu
    have h1 := h w₁ ((hV₂mem w₁).mpr ⟨0, 1, hw₁'⟩)
    rw [hform x y z r w₁ 0 1 hw₁', hw₁'] at h1
    have hr : r = 0 := by
      have h2 := (hind (0 + r * 1 - 0) (1 - 1) (by
        rw [sub_smul, sub_smul, ← add_sub_add_comm, h1, sub_self])).1
      linear_combination h2
    subst hr
    rw [hU₂, nSp_zero, mul_one]
    exact mem_pCoreOf_of_qSp hn hK hf g x y z

end BK6

theorem factR2_holds : FactR2 := by
  intro G _ _ L V X T V₁ V₂ n h A hAT _ hA hAR
  rcases h.kind with hk | hk
  · exact BK6.r2_sl3 h hk hAT hA hAR
  · exact BK6.r2_sp4 h hk hAT hA hAR

end CFSG.Quasithin.Vol2.Ch11.SecB

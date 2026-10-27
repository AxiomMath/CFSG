module

public import CFSG.Quasithin.Vol2.Ch11SecBK6B
public import CFSG.Quasithin.Vol2.Ch11SecBK6C
public import CFSG.Quasithin.Vol2.KGNatSL3LineFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usl uSL coe_uSL mem_Usl Usp qSp nSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Open (pCoreOf)
open scoped IsMulCommutative

namespace BK6

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem r2_sl3 (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSL3 L V n) {A : Subgroup G}
    (hAT : A ≤ T) (hA : autI hfl.elem A ∈ E3.aSet n (autI hfl.elem X))
    (hAR : ¬ A ≤ pCoreOf 2 (LOf L V₂ ⊔ T)) :
    ⁅V₂, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₁ ∧
      E3.mQuot A (A ⊓ Subgroup.centralizer (V₂ : Set G)) = n ∧
      E3.mQuot V₂ (V₂ ⊓ Subgroup.centralizer (A : Set G)) = n := by
  obtain ⟨_, K, _, _, _, hK, π, hπ⟩ := exists_real_sl3 hfl hk
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hn := hfl.two_le
  have hV₁V : V₁ ≤ V := hfl.le₁₂.trans hfl.le₂
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hfl.sylow le_sup_left (sup_le Subgroup.le_normalizer hfl.T_le_L)
  have hP := SecA.isSylowTwoOf_autOn hfl.le_normalizer hTL'
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  have hF₁ := isFlagW_of_flag24 hfl hV₁V hfl.cV_le hfl.stable₁ (by rw [hfl.index₁, mul_one])
    hfl.T_le_V₁
  have hF₂ := isFlagW_of_flag24 hfl hfl.le₂ (hfl.cV_le.trans hfl.le₁₂) hfl.stable₂ hfl.index₂
    hfl.T_le_V₂
  have hU₁ := eq_U1_of_isFlagW hsq hf hg (by rw [hK]; exact hF₁)
  have hU₂ := eq_U2_of_isFlagW hsq hf hg (by rw [hK]; exact hF₂)
  have hlf := KGNat.factLineSL3_holds K n hn hK _ hsq _ _ π hπ
    (fun h hh z hz => SecA.autOn_fixes_cV h hh z hz) _ hP _ hF₂
  set e₀ : Fin 3 → K := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] with he₀
  set e₁ : Fin 3 → K := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0] with he₁
  have hginv : ∀ s t : K,
      ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (s • e₀ + t • e₁) =
        ![s, t, 0] := fun s t => by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, he₀, he₁, ginv_g_mulVec,
      ginv_g_mulVec]
    exact KGNat.vec3_eq (by simp) (by simp) (by simp)
  have hgv : ∀ s t : K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![s, t, 0] = s • e₀ + t • e₁ :=
    fun s t => by
      rw [he₀, he₁, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
      congr 1
      exact KGNat.vec3_eq (by simp) (by simp) (by simp)
  have hform : ∀ (a b c : K) (w : ↥V) (s t : K), f w = s • e₀ + t • e₁ →
      f (((rho3 π (g * uSL a b c * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) w) =
        (s + a * t) • e₀ + t • e₁ := by
    intro a b c w s t hst
    rw [hf.act3, gconj_mulVec, hst, hginv, coe_uSL, uMat_mulVec, ← hgv]
    congr 1
    exact KGNat.vec3_eq (by simp) (by simp) (by simp)
  have hind : ∀ s t : K, s • e₀ + t • e₁ = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have e := hginv s t
    rw [h, Matrix.mulVec_zero] at e
    exact ⟨by simpa using (congrFun e 0).symm, by simpa using (congrFun e 1).symm⟩
  obtain ⟨w₁, hw₁⟩ := hf.surj e₁
  have hw₁' : f w₁ = (0 : K) • e₀ + (1 : K) • e₁ := by rw [hw₁, zero_smul, one_smul, zero_add]
  have hV₂mem : ∀ w : ↥V, (w : G) ∈ V₂ ↔ ∃ s t : K, f w = s • e₀ + t • e₁ := by
    intro w
    change w ∈ V₂.subgroupOf V ↔ _
    rw [hU₂, mem_pre_plane_iff]
    constructor
    · intro h2
      set x := ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w with hx
      refine ⟨x 0, x 1, ?_⟩
      have hx' : x = ![x 0, x 1, 0] := KGNat.vec3_eq (by simp) (by simp) (by simpa using h2)
      rw [← hgv, ← hx', hx, g_ginv_mulVec]
    · rintro ⟨s, t, hst⟩
      rw [hst, hginv]
      rfl
  refine r2_of_param hfl hK hf.map_mul_inv (fun a b h => (hf.eq_iff a b).mp h) hf.surj hind
    (fun w => by
      change w ∈ V₁.subgroupOf V ↔ _
      rw [hU₁]
      exact mem_pre_line_iff hf g w) hV₂mem ?_ ?_ hlf.1 hAT hA hAR
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := (hg p).mp hp
    obtain ⟨a, b, c, rfl⟩ := mem_Usl.mp hu
    exact ⟨a, hform a b c⟩
  · intro p hp h
    obtain ⟨u, hu, rfl⟩ := (hg p).mp hp
    obtain ⟨a, b, c, rfl⟩ := mem_Usl.mp hu
    have h1 := h w₁ ((hV₂mem w₁).mpr ⟨0, 1, hw₁'⟩)
    rw [hform a b c w₁ 0 1 hw₁', hw₁'] at h1
    have ha : a = 0 := by
      have h2 := (hind (0 + a * 1 - 0) (1 - 1) (by
        rw [sub_smul, sub_smul, ← add_sub_add_comm, h1, sub_self])).1
      linear_combination h2
    subst ha
    rw [hU₂]
    exact mem_pCoreOf_of_rad2 hn hK hf g b c

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB

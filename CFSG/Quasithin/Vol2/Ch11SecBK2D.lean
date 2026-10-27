module

public import CFSG.Quasithin.Vol2.KGNatSL3Line
public import CFSG.Quasithin.Vol2.KGNatSL3PointT
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL)

namespace BK2

section Count

variable {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module K M]

theorem eq_line_of_card {v₀ : M} (hv₀ : v₀ ≠ 0) {I : AddSubgroup M}
    (hI : Nat.card I = Nat.card K) (hsub : ∀ y ∈ I, ∃ c : K, y = c • v₀) :
    ∀ c : K, c • v₀ ∈ I := by
  have hinj : Function.Injective fun c : K => c • v₀ := fun c c' h => by
    have h1 : (c - c') • v₀ = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hv₀)
  have hsubset : (I : Set M) ⊆ Set.range fun c : K => c • v₀ := fun y hy => by
    obtain ⟨c, hc⟩ := hsub y hy
    exact ⟨c, hc.symm⟩
  have hfin : (Set.range fun c : K => c • v₀).Finite := Set.finite_range _
  have heq := Set.eq_of_subset_of_ncard_le hsubset (by
    rw [Set.ncard_range_of_injective hinj, ← Nat.card_coe_set_eq]
    exact hI.ge) hfin
  intro c
  have : c • v₀ ∈ (I : Set M) := heq ▸ ⟨c, rfl⟩
  exact this

theorem false_of_line {v₀ y : M} (hv₀ : v₀ ≠ 0) {I : AddSubgroup M}
    (hI : Nat.card I = Nat.card K) (hline : ∀ c : K, c • v₀ ∈ I) (hy : y ∈ I)
    (hny : ∀ c : K, y ≠ c • v₀) : False := by
  have : Finite I := Nat.finite_of_card_ne_zero (by rw [hI]; exact Nat.card_pos.ne')
  have hinj : Function.Injective fun o : Option K =>
      (o.elim ⟨y, hy⟩ fun c => ⟨c • v₀, hline c⟩ : I) := by
    rintro (_ | c) (_ | c') h
    · rfl
    · exact absurd (congrArg Subtype.val h) (hny c')
    · exact absurd (congrArg Subtype.val h).symm (hny c)
    · have h1 : c • v₀ = c' • v₀ := congrArg Subtype.val h
      have h2 : (c - c') • v₀ = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr h1
      exact congrArg some (sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv₀))
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Finite.card_option, hI] at h
  omega

end Count

section SL3

variable {K : Type} [Field K] [Finite K] {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

omit [Finite K] in
theorem uSL_mem_stabRow2 (a b c : K) : uSL a b c ∈ KGNat.stabRow2 K :=
  KGNat.mem_stabRow2.mpr ⟨by simp [coe_uSL, uMat], by simp [coe_uSL, uMat],
    by simp [coe_uSL, uMat]⟩

theorem mem_pre_line_iff_of_stable (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) {Y : Subgroup W} (hZY : Z ≤ Y)
    (hYU : Y ≤ hf.pre (KGNat.gmap g (flagSpace 3 K 2)).toAddSubgroup)
    (hYi : Z.relIndex Y = Nat.card K)
    (hst : ∀ a : K, ∀ w ∈ Y, ((KGNat.rho3 π (g * uSL a 0 0 * g⁻¹) : ↥H) : MulAut W) w ∈ Y) :
    ∀ w, w ∈ Y ↔ w ∈ hf.pre (KGNat.gmap g (flagSpace 3 K 1)).toAddSubgroup := by
  set v₀ := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] with hv₀def
  have hv₀ : v₀ ≠ 0 := KGNat.g_e0_ne_zero g
  have hI : Nat.card (hf.img Y) = Nat.card K := by rw [hf.card_img, hYi]
  have hline : ∀ y ∈ hf.img Y, ∃ c : K, y = c • v₀ := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        f w = x := ⟨_, rfl⟩
    have hfw : f w = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ x := by
      rw [← hx, KGNat.g_ginv_mulVec]
    have h2 : x 2 = 0 := by rw [← hx]; exact (KGNat.mem_pre_plane_iff hf g w).mp (hYU hw)
    by_cases h1 : x 1 = 0
    · refine ⟨x 0, ?_⟩
      have he : x = x 0 • ![1, 0, 0] := KGNat.vec3_eq (by simp) (by simp [h1]) (by simp [h2])
      rw [hfw]
      conv_lhs => rw [he]
      rw [Matrix.mulVec_smul]
    · exfalso
      have hall : ∀ c : K, c • v₀ ∈ hf.img Y := by
        intro c
        refine ⟨((KGNat.rho3 π (g * uSL (c / x 1) 0 0 * g⁻¹) : ↥H) : MulAut W) w * w⁻¹,
          Y.mul_mem (hst _ w hw) (Y.inv_mem hw), ?_⟩
        have hu : uMat (c / x 1) 0 0 *ᵥ x = x + c • ![1, 0, 0] := by
          rw [KGNat.uMat_mulVec]
          refine KGNat.vec3_eq ?_ (by simp) (by simp [h2])
          simp only [Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one,
            h2, mul_zero, add_zero]
          rw [div_mul_cancel₀ c h1, add_comm]
        rw [hf.map_mul_inv, hf.act3, KGNat.gconj_mulVec, coe_uSL, hx, hu, Matrix.mulVec_add,
          ← hfw, Matrix.mulVec_smul, add_sub_cancel_left]
      refine false_of_line hv₀ hI hall ⟨w, hw, rfl⟩ fun c hc => h1 ?_
      have h3 : x = c • ![1, 0, 0] := by
        rw [← hx, hc, Matrix.mulVec_smul, KGNat.ginv_g_mulVec]
      rw [h3]
      simp
  have hall := eq_line_of_card hv₀ hI hline
  intro w
  constructor
  · intro hw
    obtain ⟨c, hc⟩ := hline _ ⟨w, hw, rfl⟩
    exact (KGNat.mem_pre_line_iff hf g w).mpr ⟨c, hc⟩
  · intro hw
    obtain ⟨c, hc⟩ := (KGNat.mem_pre_line_iff hf g w).mp hw
    rw [hf.mem_iff hZY w, hc]
    exact hall c

omit [Finite K] in
theorem stabRow2_mulVec_two {B : SpecialLinearGroup (Fin 3) K} (hB : B ∈ KGNat.stabRow2 K)
    (y : Fin 3 → K) : ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ y) 2 = y 2 := by
  obtain ⟨h20, h21, h22⟩ := KGNat.mem_stabRow2.mp hB
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21, h22]

theorem l2Point_SL3 {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π)
    {P : Subgroup (MulAut W)} (hP : QuasithinUnique.IsSylowTwoOf P H) {U₁ U₂ : Subgroup W}
    (hU₁ : Ch11.SecA.IsFlagW H P Z (2 ^ n) 1 U₁) (hU₂ : Ch11.SecA.IsFlagW H P Z (2 ^ n) 2 U₂)
    {Q : Subgroup (MulAut W)}
    (hQ : QuasithinUnique.IsSylowTwoOf Q (perfectCore (H ⊓ Ch11.SecA.stabW U₂)))
    {Y : Subgroup W} (hZY : Z ≤ Y) (hYU : Y ≤ U₂) (hYi : Z.relIndex Y = 2 ^ n)
    (hQY : Q ≤ Ch11.SecA.stabW Y) :
    ∃ x ∈ perfectCore (H ⊓ Ch11.SecA.stabW U₂), ∀ w, w ∈ Y ↔ x w ∈ U₁ := by
  have hSL := KGNat.commutator_SL2_eq_top (KGNat.four_le_card hn hK)
  obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
  obtain ⟨g, hg⟩ := KGNat.exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU₁ hU₂ hYi
  rw [KGNat.eq_U1_of_isFlagW hW hf hg hU₁]
  obtain rfl := KGNat.eq_U2_of_isFlagW hW hf hg hU₂
  have hPS : P ≤ perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (KGNat.gmap g (flagSpace 3 K 2)).toAddSubgroup)) := fun x hx => by
    obtain ⟨u, hu, rfl⟩ := (hg x).mp hx
    obtain ⟨a, b, c, rfl⟩ := mem_Usl.mp hu
    exact (KGNat.mem_perfectCore_HU2_iff hSL hf g _).mpr ⟨_, uSL_mem_stabRow2 a b c, rfl⟩
  have hPS' := C1GN.isSylowTwoOf_of_le hP hPS ((perfectCore_le _).trans inf_le_left)
  obtain ⟨x₀, hx₀, hQeq⟩ := hPS'.exists_conj hQ
  obtain ⟨B₀, hB₀, rfl⟩ := (KGNat.mem_perfectCore_HU2_iff hSL hf g x₀).mp hx₀
  refine ⟨((KGNat.rho3 π (g * B₀⁻¹ * g⁻¹) : ↥H) : MulAut W),
    (KGNat.mem_perfectCore_HU2_iff hSL hf g _).mpr ⟨B₀⁻¹, (KGNat.stabRow2 K).inv_mem hB₀, rfl⟩,
    fun w => ?_⟩
  have hplane : hf.pre (KGNat.gmap (g * B₀) (flagSpace 3 K 2)).toAddSubgroup =
      hf.pre (KGNat.gmap g (flagSpace 3 K 2)).toAddSubgroup := by
    ext v
    rw [KGNat.mem_pre_plane_iff, KGNat.mem_pre_plane_iff, _root_.mul_inv_rev,
      Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
      stabRow2_mulVec_two ((KGNat.stabRow2 K).inv_mem hB₀)]
  have hst : ∀ a : K, ∀ w ∈ Y,
      ((KGNat.rho3 π ((g * B₀) * uSL a 0 0 * (g * B₀)⁻¹) : ↥H) : MulAut W) w ∈ Y := by
    intro a w hw
    have hmem : ((KGNat.rho3 π ((g * B₀) * uSL a 0 0 * (g * B₀)⁻¹) : ↥H) : MulAut W) ∈ Q := by
      rw [hQeq]
      refine ⟨((KGNat.rho3 π (g * uSL a 0 0 * g⁻¹) : ↥H) : MulAut W),
        (hg _).mpr ⟨_, ⟨a, 0, 0, rfl⟩, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← Subgroup.coe_inv, ← map_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul,
        ← map_mul]
      congr 2
      group
    exact (Ch11.SecA.mem_stabW.mp (hQY hmem) w).mp hw
  rw [mem_pre_line_iff_of_stable hf (g * B₀) hZY (hplane ▸ hYU) hYi hst w]
  change f w ∈ KGNat.gmap (g * B₀) (flagSpace 3 K 1) ↔
    f (((KGNat.rho3 π (g * B₀⁻¹ * g⁻¹) : ↥H) : MulAut W) w) ∈ KGNat.gmap g (flagSpace 3 K 1)
  rw [KGNat.mem_gmap, KGNat.mem_gmap, hf.act3, KGNat.gconj_mulVec, KGNat.ginv_g_mulVec,
    _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]

end SL3

end BK2

end CFSG.Quasithin.Vol2.Ch11.SecB

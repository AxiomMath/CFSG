module

public import CFSG.Quasithin.Vol2.Ch11SecO1bE
public import CFSG.Quasithin.Vol2.Ch11SecGFacts
public import CFSG.Quasithin.Vol2.Ch11SecO1bD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA
open CFSG.Open (pCoreOf)
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}
  [IsMulCommutative ↥(fsuV T I)] {K : Type} [Field K] [Finite K] [CharP K 2]
  {π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))} {f : ↥(fsuV T I) → (Fin 2 ⊕ Fin 2 → K)}
  {g : StatedSp 2 K}

omit [CharP K 2] in
theorem fix_spHyp_of_relIndex (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hV₁ : IsVi T L I n 1 V₁) {V₃ : Subgroup G} (hV₃ : IsVi T L I n 3 V₃) {B : Subgroup G}
    (hB : B.relIndex V₃ ≤ 2) {x : G} (hx : x ∈ ROf T L V₁)
    (hxB : x ∈ Subgroup.centralizer (B : Set G)) {N : StatedSp 2 K}
    (hxN : ∀ w, f (SecA.conjV (fsuV T I) x (r1_le_normalizer hS hV₁ hx) w) =
      mat 2 K (g * N * g⁻¹) *ᵥ f w)
    (y : Fin 2 ⊕ Fin 2 → K) (hy : y (.inr 0) = 0) : mat 2 K N *ᵥ y = y := by
  by_contra hNy
  choose w hw using fun c : K => hf.surj (mat 2 K g *ᵥ (c • y))
  have hwV₃ : ∀ c, ((w c : ↥(fsuV T I)) : G) ∈ V₃ := fun c => by
    rw [mem_V3_sp4_iff hS hK hf hg hV₃, hw, mat_inv_mulVec, Pi.smul_apply, hy, smul_zero]
  let φ : K → ↥V₃ ⧸ B.subgroupOf V₃ := fun c => QuotientGroup.mk ⟨w c, hwV₃ c⟩
  have hφ : Function.Injective φ := by
    intro c c' h
    by_contra hcc
    have h1 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h1
    set u : ↥(fsuV T I) := (w c)⁻¹ * w c' with hu
    have h1' : (u : G) ∈ B := by
      rw [hu, Subgroup.coe_mul, Subgroup.coe_inv]
      exact h1
    have h2 : SecA.conjV (fsuV T I) x (r1_le_normalizer hS hV₁ hx) u = u := Subtype.ext (by
      rw [SecA.conjV_apply_coe]
      have h3 : (u : G) * x = x * u := Subgroup.mem_centralizer_iff.mp hxB _ h1'
      rw [← h3, mul_inv_cancel_right])
    have hfu : f u = mat 2 K g *ᵥ ((c' - c) • y) := by
      rw [hu, hf.map_mul, hf.map_inv, hw, hw, sub_smul, Matrix.mulVec_sub]
      abel
    have h4 := congrArg f h2
    rw [hxN, hfu, KA.gconj_mulVec_sp, mat_inv_mulVec] at h4
    have h5 := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) h4
    simp only [mat_inv_mulVec, Matrix.mulVec_smul] at h5
    exact hNy (smul_right_injective _ (sub_ne_zero.mpr (Ne.symm hcc)) h5)
  have h5 : Nat.card K ≤ B.relIndex V₃ := Nat.card_le_card_of_injective φ hφ
  have h6 := four_le_card hS.one_lt hK
  omega

end CFSG.Quasithin.Vol2.Ch11.SecO1b

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecO1b Matrix
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped IsMulCommutative commutatorElement

theorem r1CorankFact_holds : R1CorankFact := by
  intro G _ _ T L I n V₁ V₃ hS hk hV₁ hV₃ D B hD hBV₃ hB hDB
  have := SecO1.isMulCommutative hS
  have hDV : D ≤ Subgroup.normalizer (fsuV T I : Set G) := fun d hd =>
    r1_le_normalizer hS hV₁ (hD hd)
  rcases hk with hk | hk
  · obtain ⟨K, _, _, _, hK, π, f, hf, g, hg⟩ := exists_coord_sl3_syl hS hk
    exact comm_le_of le_rfl hDV fun u _ d hd => comm_mem_V1_sl3 hS hK hf hg hV₁ (hD hd) u
  · obtain ⟨K, _, _, _, hK, π, f, hπ, hf, g, hg⟩ := exists_coord_sp4_syl hS hk
    have hB2 := relIndex_le_two hS.elem (SecA.IsVi.le_fsuV hV₃) hB
    refine comm_le_of le_rfl hDV fun u _ d hd => ?_
    obtain ⟨N, -, hN⟩ := r1_shape_sp4 hS hK hπ hf hg hV₁ (hD hd)
    exact comm_mem_V1_of_fix hS hK hf hg hV₁ (hD hd) hN
      (fix_spHyp_of_relIndex hS hK hf hg hV₁ hV₃ hB2 (hD hd) (hDB hd) hN) u

theorem r1CommFact_holds : R1CommFact := by
  intro G _ _ T L I n V₁ V₃ hS hk hV₁ hV₃ A hA hne
  have := SecO1.isMulCommutative hS
  have hAV : A ≤ Subgroup.normalizer (fsuV T I : Set G) := fun a ha =>
    r1_le_normalizer hS hV₁ (hA ha)
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  rcases hk with hk | hk
  · obtain ⟨K, _, _, _, hK, π, f, hf, g, hg⟩ := exists_coord_sl3_syl hS hk
    refine Or.inl (eq_of_kstable_le hf.map_mul (SecO1.IsCoord.injective_of_bot hf) hV₁V
      (mem_V1_sl3_iff hS hK hf hg hV₁)
      (comm_le_of le_rfl hAV fun u _ a ha => comm_mem_V1_sl3 hS hK hf hg hV₁ (hA ha) u) hne
      (kstable_comm hf.map_mul le_rfl (fun v _ c => ?_) hAV
        fun x hx => r1_linear_sl3 hS hK hf hg hV₁ (hA hx)))
    obtain ⟨v', hv'⟩ := hf.surj (c • f v)
    exact ⟨v', v'.2, hv'⟩
  · obtain ⟨K, _, _, _, hK, π, f, hπ, hf, g, hg⟩ := exists_coord_sp4_syl hS hk
    have hlin := fun x (hx : x ∈ A) => r1_linear_sp4 hS hK hπ hf hg hV₁ (hA hx)
    by_cases h3 : ⁅V₃, A⁆ = ⊥
    · refine Or.inl (eq_of_kstable_le hf.map_mul (SecO1.IsCoord.injective_of_bot hf) hV₁V
        (mem_V1_sp4_iff hS hK hf hg hV₁) (comm_le_of le_rfl hAV fun u _ a ha => ?_) hne
        (kstable_comm hf.map_mul le_rfl (fun v _ c => ?_) hAV hlin))
      · obtain ⟨N, -, hN⟩ := r1_shape_sp4 hS hK hπ hf hg hV₁ (hA ha)
        refine comm_mem_V1_of_fix hS hK hf hg hV₁ (hA ha) hN (fun y hy => ?_) u
        obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ y)
        have hwV₃ : (w : G) ∈ V₃ := by
          rw [mem_V3_sp4_iff hS hK hf hg hV₃, hw, mat_inv_mulVec]
          exact hy
        have hc : ⁅(w : G), a⁆ = 1 :=
          Subgroup.mem_bot.mp (h3 ▸ Subgroup.commutator_mem_commutator hwV₃ ha)
        have h1 : SecA.conjV (fsuV T I) a (hAV ha) w = w := by
          have h2 : ((SecA.conjV (fsuV T I) a (hAV ha) w * w⁻¹)⁻¹ : ↥(fsuV T I)) = 1 :=
            Subtype.ext (by rw [← commutator_coe_eq (hAV ha) w, hc]; rfl)
          rwa [inv_eq_one, mul_inv_eq_one] at h2
        have h4 := congrArg f h1
        rw [hN, hw, KA.gconj_mulVec_sp, mat_inv_mulVec] at h4
        have h5 := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) h4
        simpa only [mat_inv_mulVec] using h5
      · obtain ⟨v', hv'⟩ := hf.surj (c • f v)
        exact ⟨v', v'.2, hv'⟩
    · refine Or.inr (eq_of_kstable_le hf.map_mul (SecO1.IsCoord.injective_of_bot hf) hV₁V
        (mem_V1_sp4_iff hS hK hf hg hV₁)
        (comm_le_of (SecA.IsVi.le_fsuV hV₃) hAV fun u hu a ha => ?_) h3
        (kstable_comm hf.map_mul (SecA.IsVi.le_fsuV hV₃) (fun v hv c => ?_) hAV hlin))
      · obtain ⟨N, hN', hN⟩ := r1_shape_sp4 hS hK hπ hf hg hV₁ (hA ha)
        exact comm_mem_V1_sp4 hS hK hf hg hV₁ hV₃ hN' (hA ha) hN u hu
      · obtain ⟨v', hv'⟩ := hf.surj (c • f v)
        refine ⟨v', ?_, hv'⟩
        rw [mem_V3_sp4_iff hS hK hf hg hV₃, hv', Matrix.mulVec_smul, Pi.smul_apply,
          (mem_V3_sp4_iff hS hK hf hg hV₃ v).mp hv, smul_zero]

end CFSG.Quasithin.Vol2.Ch11.SecG

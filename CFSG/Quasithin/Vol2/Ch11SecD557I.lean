module

public import CFSG.Quasithin.Background.G13Perm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G2SL3Setting
public import CFSG.Quasithin.H13.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups

variable {G : Type} [Group G] {n : ℕ} {L K V V₁ : Subgroup G}

theorem mem_rconj_iff_of_natData (D : NatData3 n L K V V₁) (a : ↥L) (w : ↥V) :
    (w : G) ∈ rconj V₁ (a : G) ↔ ∃ c : GaloisField 2 n,
      D.θ a • Multiplicative.toAdd (D.ψ w) = c • vE (GaloisField 2 n) 0 := by
  rw [mem_rconj]
  have h1 := D.line (conjAct V ⟨a, D.hnorm a.2⟩ w)
  rw [conjAct_coe_apply, D.equiv a w, natAct3_apply, toAdd_ofAdd] at h1
  exact h1

theorem wS_smul_vE {F : Type*} [Field F] [CharP F 2] {i j : Fin 3} (hij : i ≠ j) (c : F)
    (a : Fin 3) : CFSG.Quasithin.G1.wS F hij • (c • vE F a) = c • vE F (Equiv.swap i j a) := by
  funext k
  rw [CFSG.Quasithin.G1.wS_smul]
  simp only [Pi.smul_apply, vE, Pi.single_apply, smul_eq_mul, Equiv.swap_apply_eq_iff]

theorem mem_rconj_iff_of_swap (D : NatData3 n L K V V₁) (a : ↥L) {i : Fin 3} (h0i : (0 : Fin 3) ≠ i)
    (ha : D.θ a = CFSG.Quasithin.G1.wS (GaloisField 2 n) h0i) (w : ↥V) :
    (w : G) ∈ rconj V₁ (a : G) ↔ ∃ c : GaloisField 2 n,
      Multiplicative.toAdd (D.ψ w) = c • vE (GaloisField 2 n) i := by
  rw [mem_rconj_iff_of_natData D a w, ha]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h1 : CFSG.Quasithin.G1.wS (GaloisField 2 n) h0i •
        CFSG.Quasithin.G1.wS (GaloisField 2 n) h0i • Multiplicative.toAdd (D.ψ w) =
        CFSG.Quasithin.G1.wS (GaloisField 2 n) h0i • (c • vE (GaloisField 2 n) 0) := by
      rw [hc]
    rw [CFSG.Quasithin.G1.wS_smul_smul, wS_smul_vE, Equiv.swap_apply_left] at h1
    exact h1
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc, wS_smul_vE, Equiv.swap_apply_right]

theorem rconj_le_of_natData (D : NatData3 n L K V V₁) (hV₁V : V₁ ≤ V) (a : ↥L) :
    rconj V₁ (a : G) ≤ V := fun w hw => by
  rw [mem_rconj] at hw
  exact (Subgroup.mem_normalizer_iff.mp (D.hnorm a.2) w).mpr (hV₁V hw)

theorem exists_weyl (D : NatData3 n L K V V₁) (hV₁V : V₁ ≤ V) :
    ∃ x ∈ L, ∃ y ∈ L, V = V₁ ⊔ rconj V₁ x ⊔ rconj V₁ y ∧ rconj V₁ x ⊓ rconj V₁ y = ⊥ := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  obtain ⟨x, hx⟩ := D.surj (CFSG.Quasithin.G1.wS (GaloisField 2 n) h01)
  obtain ⟨y, hy⟩ := D.surj (CFSG.Quasithin.G1.wS (GaloisField 2 n) h02)
  refine ⟨x, x.2, y, y.2, le_antisymm (fun v hv => ?_)
    (sup_le (sup_le hV₁V (rconj_le_of_natData D hV₁V x)) (rconj_le_of_natData D hV₁V y)), ?_⟩
  · set u := Multiplicative.toAdd (D.ψ ⟨v, hv⟩) with hu
    let w : Fin 3 → ↥V := fun i =>
      D.ψ.symm (Multiplicative.ofAdd (u i • vE (GaloisField 2 n) i))
    have hw : ∀ i, Multiplicative.toAdd (D.ψ (w i)) = u i • vE (GaloisField 2 n) i := fun i => by
      simp only [w, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have hv' : (⟨v, hv⟩ : ↥V) = w 0 * w 1 * w 2 := by
      apply D.ψ.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul D.ψ, map_mul D.ψ, toAdd_mul, toAdd_mul, hw, hw, hw, ← hu]
      funext k
      fin_cases k <;> simp [vE]
    have hv'' : v = (w 0 : G) * (w 1 : G) * (w 2 : G) := congrArg Subtype.val hv'
    rw [hv'']
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
      (Subgroup.mem_sup_left ?_)) (Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)))
      (Subgroup.mem_sup_right ?_)
    · exact (D.line (w 0)).mpr ⟨u 0, hw 0⟩
    · exact (mem_rconj_iff_of_swap D x h01 hx (w 1)).mpr ⟨u 1, hw 1⟩
    · exact (mem_rconj_iff_of_swap D y h02 hy (w 2)).mpr ⟨u 2, hw 2⟩
  · rw [eq_bot_iff]
    rintro w ⟨hwx, hwy⟩
    have hwV : w ∈ V := rconj_le_of_natData D hV₁V x hwx
    obtain ⟨c₁, hc₁⟩ := (mem_rconj_iff_of_swap D x h01 hx ⟨w, hwV⟩).mp hwx
    obtain ⟨c₂, hc₂⟩ := (mem_rconj_iff_of_swap D y h02 hy ⟨w, hwV⟩).mp hwy
    have h1 : c₁ = 0 := by
      have := congrFun (hc₁.symm.trans hc₂) 1
      simpa [vE] using this
    have hψ : D.ψ ⟨w, hwV⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hc₁, h1, zero_smul, toAdd_one]
    have h2 : (⟨w, hwV⟩ : ↥V) = 1 := D.ψ.injective (hψ.trans (map_one _).symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)

end CFSG.Quasithin.Vol2.Ch11.SecD

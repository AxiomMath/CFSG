module

public import CFSG.Quasithin.Background.F7TwoInvSp4Root
public import CFSG.Quasithin.Background.F7TwoInvSp4Model

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.ComponentClassification.UnbalancedCatalog

variable {K : Type} [Field K]

theorem sp4_fieldSp_sp4UpRoot (σ : K ≃+* K) (i : Fin 3) (c : K) :
    fieldSp 2 K σ (sp4UpRoot i c) = sp4UpRoot i (σ c) := by
  refine statedSp_ext ?_
  unfold sp4UpRoot
  rw [coe_fieldSp, coe_upperUnipotentSp, coe_upperUnipotentSp, fromBlocks_map,
    Matrix.map_smul' _ _ _ (map_mul σ), sp4SymE_map]
  simp

theorem sp4_fieldSp_sp4LowRoot [CharP K 2] (σ : K ≃+* K) (i : Fin 3) (c : K) :
    fieldSp 2 K σ (sp4LowRoot i c) = sp4LowRoot i (σ c) := by
  refine statedSp_ext ?_
  unfold sp4LowRoot
  rw [coe_fieldSp, coe_lowerSp, coe_lowerSp, fromBlocks_map,
    Matrix.map_smul' _ _ _ (map_mul σ), sp4SymE_map]
  simp

theorem sp4_fieldSp_torusHom (σ : K ≃+* K) (τ : Fin 2 → Kˣ) :
    fieldSp 2 K σ (torusHom τ) = torusHom (fun i => Units.map (σ : K →* K) (τ i)) := by
  refine statedSp_ext ?_
  rw [coe_fieldSp, coe_torusHom, coe_torusHom, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext x
  rcases x with i | i <;> simp

theorem sp4UpRoot_zero_injective {s s' : K} (h : sp4UpRoot 0 s = sp4UpRoot 0 s') : s = s' := by
  have h1 := congrFun₂ (congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h) (Sum.inl 0) (Sum.inr 0)
  unfold sp4UpRoot at h1
  simpa [coe_upperUnipotentSp, sp4SymE] using h1

theorem invAutGen_sp4_fieldSp [CharP K 2] [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) {σ : K ≃+* K} (hσ : σ ≠ 1) (hσσ : σ * σ = 1) :
    InvAutGen (StatedSp 2 K) (fieldSp 2 K σ) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hsP := isSimpleGroup_sp4_proj h4
  have hs : IsSimpleGroup (StatedSp 2 K) := (SpChain.projSpEquiv K).isSimpleGroup
  have hnonab : ∃ x y : StatedSp 2 K, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := sp4_proj_nonabelian h4
    refine ⟨(SpChain.projSpEquiv K).symm x, (SpChain.projSpEquiv K).symm y, fun h => hxy ?_⟩
    simpa using congrArg (SpChain.projSpEquiv K) h
  have hφ2 : fieldSp 2 K σ * fieldSp 2 K σ = 1 := by rw [← map_mul, hσσ, map_one]
  have hφ1 : fieldSp 2 K σ ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
      by_contra hcon
      push Not at hcon
      exact hσ (RingEquiv.ext hcon)
    have h1 := congrArg (fun φ : MulAut (StatedSp 2 K) => φ (sp4UpRoot 0 c)) h
    simp only [MulAut.one_apply, sp4_fieldSp_sp4UpRoot] at h1
    exact hc (sp4UpRoot_zero_injective h1)
  let b : Option (Bool × Fin 3) → StatedSp 2 K
    | none => 1
    | some (false, i) => sp4UpRoot i 1
    | some (true, i) => sp4LowRoot i 1
  have hbfix : ∀ o, fieldSp 2 K σ (b o) = b o := by
    rintro (_ | ⟨_ | _, i⟩)
    · exact map_one _
    · exact (sp4_fieldSp_sp4UpRoot σ i 1).trans (by rw [map_one])
    · exact (sp4_fieldSp_sp4LowRoot σ i 1).trans (by rw [map_one])
  let U : Option (Bool × Fin 3) → Subgroup (StatedSp 2 K) := fun o =>
    (torus 2 K).map (MulAut.conj (b o)).toMonoidHom
  have hTodd : Odd (Nat.card (torus 2 K)) := by
    have hc : Nat.card (torus 2 K) = (Nat.card K - 1) ^ 2 := by
      have h1 : Nat.card (torus 2 K) = Nat.card (Fin 2 → Kˣ) :=
        (Nat.card_congr
          (MonoidHom.ofInjective (torusHom_injective (r := 2) (k := K))).toEquiv).symm
      rw [h1, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units]
    rw [hc]
    refine Odd.pow ?_
    have h2 : Even (Nat.card K) := by
      rw [hK]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨k, hk⟩ := h2
    exact ⟨k - 1, by omega⟩
  have hodd : ∀ o, Odd (Nat.card (U o)) := fun o => by
    change Odd (Nat.card ((torus 2 K).map (MulAut.conj (b o)).toMonoidHom))
    rw [Subgroup.card_map_of_injective (MulAut.conj (b o)).injective]
    exact hTodd
  have hinv : ∀ o, ∀ x ∈ U o, fieldSp 2 K σ x ∈ U o := by
    intro o x hx
    obtain ⟨t, ⟨τ, rfl⟩, rfl⟩ := hx
    refine ⟨torusHom (fun i => Units.map (σ : K →* K) (τ i)), ⟨_, rfl⟩, ?_⟩
    change MulAut.conj (b o) _ = fieldSp 2 K σ (MulAut.conj (b o) (torusHom τ))
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hbfix,
      sp4_fieldSp_torusHom]
  refine invAutGen_of_odd_iSup hs hnonab hφ2 hφ1 (U := U) hodd hinv ?_
  refine sp4_eq_top_of_torus_conj (by omega) (fun τ => ?_) (fun i τ => ?_) (fun i τ => ?_)
  · exact Subgroup.mem_iSup_of_mem none ⟨torusHom τ, torusHom_mem_torus τ, by simp [b]⟩
  · exact Subgroup.mem_iSup_of_mem (some (false, i)) ⟨torusHom τ, torusHom_mem_torus τ, rfl⟩
  · exact Subgroup.mem_iSup_of_mem (some (true, i)) ⟨torusHom τ, torusHom_mem_torus τ, rfl⟩

end CFSG.Quasithin.F7Two

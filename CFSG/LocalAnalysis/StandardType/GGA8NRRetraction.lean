module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLift
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoProj
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.StandardType.GGHalf (F2)
open Matrix

private noncomputable def a8nr_fieldEquiv : F2 ≃+* ZMod 2 := by
  classical
  letI : Fintype F2 := Fintype.ofFinite F2
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  exact FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, hcard, ZMod.card])

private noncomputable def a8nr_slFieldEquiv :
    SpecialLinearGroup (Fin 9) F2 ≃* SpecialLinearGroup (Fin 9) (ZMod 2) := by
  classical
  let ε : F2 ≃+* ZMod 2 := a8nr_fieldEquiv
  refine MulEquiv.ofBijective (SpecialLinearGroup.map ε.toRingHom) ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have h' := congrArg
      (fun X : SpecialLinearGroup (Fin 9) (ZMod 2) =>
        ((X : Matrix (Fin 9) (Fin 9) (ZMod 2)) i j)) h
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h'
    exact ε.injective h'
  · intro b
    refine ⟨SpecialLinearGroup.map ε.symm.toRingHom b, ?_⟩
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    simp

private noncomputable def a8nr_slGL :
    SpecialLinearGroup (Fin 9) (ZMod 2) ≃* GL (Fin 9) (ZMod 2) :=
  MulEquiv.ofBijective SpecialLinearGroup.toGL
    (toGL_nine_bijective_of_card_two (K := ZMod 2) (Nat.card_zmod 2))

private noncomputable def a8nr_rho0 {G : Type} [Group G] {K : Subgroup G}
    (φ : SpecialLinearGroup (Fin 9) F2 →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = K) : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm).trans
    (a8nr_slFieldEquiv.trans (a8nr_slGL.trans ggSL9GLEquiv))

private theorem a8nr_center_eq_bot {G : Type} [Group G] {K : Subgroup G}
    (ρ₀ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) : Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply ρ₀.injective
  rw [map_one]
  have hc : ρ₀ x ∈ Subgroup.center (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h := Subgroup.mem_center_iff.mp hx (ρ₀.symm z)
    calc z * ρ₀ x = ρ₀ (ρ₀.symm z) * ρ₀ x := by rw [MulEquiv.apply_symm_apply]
      _ = ρ₀ (ρ₀.symm z * x) := by rw [map_mul]
      _ = ρ₀ (x * ρ₀.symm z) := by rw [h]
      _ = ρ₀ x * ρ₀ (ρ₀.symm z) := by rw [map_mul]
      _ = ρ₀ x * z := by rw [MulEquiv.apply_symm_apply]
  have h1 : ρ₀ x ∈ (⊥ : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
    rwa [center_ggSL9_eq_bot] at hc
  exact Subgroup.mem_bot.mp h1

private theorem a8nr_F2_card : Nat.card F2 = 2 := by
  have := GaloisField.card 2 1 (by omega)
  simpa using this

private theorem a8nr_exists_realizing {G : Type} [Group G] {K : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} {hrange : φ.range = K}
    {A : GL (Fin 9) F2} {b : G}
    (hb : (b, A) ∈ LinFusion.ggInducedPairs φ) :
    ∃ k : ↥K, ∀ u : SpecialLinearGroup (Fin 9) F2,
      b * φ u * b⁻¹ = (k : G) * φ u * (k : G)⁻¹ := by
  obtain ⟨B, hB⟩ := (toGL_nine_bijective_of_card_two (K := F2) a8nr_F2_card).2 A
  have hBmat : (B : Matrix (Fin 9) (Fin 9) F2) = (A : Matrix (Fin 9) (Fin 9) F2) := by
    have := congrArg (fun X : GL (Fin 9) F2 => (X : Matrix (Fin 9) (Fin 9) F2)) hB
    simpa using this
  refine ⟨⟨φ B, ?_⟩, ?_⟩
  · rw [← hrange]; exact ⟨B, rfl⟩
  · intro u
    have h1 : b * φ u * b⁻¹ = φ (InnerDiagA.conjSL A u) :=
      (LinFusion.mem_ggInducedPairs.mp hb) u
    have h2 : InnerDiagA.conjSL A u = B * u * B⁻¹ :=
      LinFusion.conjSL_eq_of_smul (m := 8) (c := 1) (by simpa using hBmat) u
    calc b * φ u * b⁻¹ = φ (InnerDiagA.conjSL A u) := h1
      _ = φ (B * u * B⁻¹) := by rw [h2]
      _ = φ B * φ u * (φ B)⁻¹ := by rw [map_mul, map_mul, map_inv]

theorem ggA8NR_retraction
    (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (hab : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a) (hpow : ∀ b ∈ Bs, b ^ 7 = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs)
    (hinn : GGInnerDiagOn Bs K)
    (hKm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1) :
    ∃ _ρ₀ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V),
      ∀ b ∈ Bs, ∃ k ∈ K, k ∈ Bs ∧ k⁻¹ * b ∈ Subgroup.centralizer (K : Set G) := by
  classical
  have hperf : commutator K = ⊤ := hinn.1
  obtain ⟨φ, hrange, hinj⟩ :=
    GGHalf.exists_slLift_two (m := 6) (by norm_num) hperf hKm
  let ρ₀ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := a8nr_rho0 φ hinj hrange
  have hX : Subgroup.center K = ⊥ := a8nr_center_eq_bot ρ₀
  have hkerφ : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 9) F2) := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hinj]
    exact bot_le
  have hAex0 := exists_mem_ggInducedPairs_of_innerDiagOn (Bs := Bs) (X := K) (n := 8) (f := 1)
      hMp (by norm_num) hKm.1 hinn hkerφ hrange
  have hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹ := by
    intro b hb
    obtain ⟨A, hA⟩ := hAex0 b hb
    obtain ⟨k, hk⟩ :=
      a8nr_exists_realizing (K := K) (φ := φ) (hrange := hrange) (A := A) hA
    refine ⟨(k : G), k.2, fun y hy => ?_⟩
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hy)
    rw [← hu]
    exact hk u
  have hnorm : Bs ≤ Subgroup.normalizer (K : Set G) := hinn.le_normalizer
  have hBs : GGBstar 7 Bs Bs := by
    refine ⟨le_refl Bs, ?_, ?_, hSC⟩
    · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        exact hab (a : G) a.2 (b : G) b.2
      · exact hpow x hx
    · omega
  refine ⟨ρ₀, fun b hb => ?_⟩
  obtain ⟨x, hx, c, hc, hbc⟩ :=
    ggBstar_split_of_inner (p := 7) (B := Bs) hBs hX hnorm hinner b hb
  refine ⟨x, hx.2, hx.1, ?_⟩
  have hxc : x⁻¹ * (x * c) = c := by group
  rw [hbc, hxc]
  exact hc.2

end CFSG.StandardType

end

module

public import CFSG.Quasithin.Background.F7TwoInvU3OddLower
public import CFSG.RankThree.CentralLiftU.UnitaryBorelLift

public section

namespace CFSG.Quasithin.F7Two.U3Odd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.RankThree.CentralLiftU
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem isPGroup_lowerU (hp : p ≠ 2) : IsPGroup p (lowerU h) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one]
  have hx := u3_fullUnitriangular_pow_prime hp (mem_lowerU.mp x.2)
  have h1 : jGL K * ((x : hypSU h 1 1) : GL (HypIndex 1 1) K) ^ p * (jGL K)⁻¹ = 1 := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
    exact hx
  have h2 : ((x : hypSU h 1 1) : GL (HypIndex 1 1) K) ^ p = 1 := by
    calc ((x : hypSU h 1 1) : GL (HypIndex 1 1) K) ^ p
        = (jGL K)⁻¹ * (jGL K * ((x : hypSU h 1 1) : GL (HypIndex 1 1) K) ^ p * (jGL K)⁻¹) *
          jGL K := by group
      _ = 1 := by rw [h1]; group
  exact Subtype.ext (Subtype.ext (by simpa using h2))

theorem exists_rootElt (h : UnitaryFieldData p f K) :
    ∃ (u : hypSU h 1 1) (β : K), β ≠ 0 ∧ u ∈ hypUnitriangular h 1 1 ∧
      ((u : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u3Mat h 0 β := by
  obtain ⟨β, hβ, hβ0⟩ := exists_mem_traceZero_ne_zero' h
  have hβ' : β + h.bar β = -((0 : K) * h.bar 0) := by
    have := h.mem_traceZero.mp hβ
    simpa [UnitaryFieldData.trace] using this
  obtain ⟨u, hu, hu'⟩ := exists_mem_of_uMat hβ'
  exact ⟨u, β, hβ0, hu, hu'⟩

theorem mem_hypFlag_one {v : HypIndex 1 1 → K} :
    v ∈ hypFlag h 1 1 1 ↔ v (.inr (.inl 0)) = 0 ∧ v (.inr (.inr 0)) = 0 := by
  rw [hypFlag_eq_posFlag h le_rfl (by norm_num), mem_posFlag]
  constructor
  · intro hv
    exact ⟨hv (.inr (.inl 0)) (by simp), hv (.inr (.inr 0)) (by simp)⟩
  · rintro ⟨hz, hf⟩ a ha
    rcases a with i | i | i
    · simp at ha
    · rw [Subsingleton.elim i 0]
      exact hz
    · rw [Subsingleton.elim i 0]
      exact hf

theorem exists_lowerU_not_mem_isoStabilizer (h : UnitaryFieldData p f K) :
    ∃ g : hypSU h 1 1, g ∈ lowerU h ∧ g ∉ isoStabilizer h 1 1 (hypFlag h 1 1 1) := by
  obtain ⟨u, β, hβ, hu, hum⟩ := exists_rootElt h
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : hypSU h 1 1,
      g₀ = ⟨jGL K * (u : GL (HypIndex 1 1) K) * (jGL K)⁻¹, jGL_conj_mem_hypSU h u.2⟩ :=
    ⟨_, rfl⟩
  refine ⟨g₀, ?_, ?_⟩
  · subst hg₀
    rw [mem_lowerU]
    have e : jGL K * (jGL K * (u : GL (HypIndex 1 1) K) * (jGL K)⁻¹) * (jGL K)⁻¹ =
        (u : GL (HypIndex 1 1) K) := by
      calc jGL K * (jGL K * (u : GL (HypIndex 1 1) K) * (jGL K)⁻¹) * (jGL K)⁻¹
          = (jGL K * jGL K) * (u : GL (HypIndex 1 1) K) * ((jGL K)⁻¹ * (jGL K)⁻¹) := by group
        _ = (u : GL (HypIndex 1 1) K) := by rw [jGL_inv, jGL_mul_self]; group
    rw [e]
    exact mem_hypUnitriangular_iff.mp hu
  · intro hg
    rw [mem_isoStabilizer] at hg
    have he : (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) ∈ hypFlag h 1 1 1 := by
      rw [mem_hypFlag_one]
      simp
    have h1 : g₀ • (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) ∈ g₀ • hypFlag h 1 1 1 :=
      Submodule.smul_mem_pointwise_smul (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) g₀
        (hypFlag h 1 1 1) he
    rw [hg] at h1
    have h2 := (mem_hypFlag_one.mp h1).2
    have h3 : ((g₀ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
        (.inr (.inr 0)) (.inl 0) = β := by
      rw [hg₀]
      change ((jGL K * (u : GL (HypIndex 1 1) K) * (jGL K)⁻¹ : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inl 0) = β
      rw [jGL_conj_apply, hum]
      simp
    refine hβ ?_
    rw [← h3]
    change (((g₀ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
      (Pi.single (.inl 0) 1 : HypIndex 1 1 → K)) (.inr (.inr 0)) = 0 at h2
    rw [mulVec_single_one, col_apply] at h2
    exact h2

theorem conj_mem_lowerU_of_torus {t x : hypSU h 1 1} (ht : t ∈ hypTorus h 1 1)
    (hx : x ∈ lowerU h) : t * x * t⁻¹ ∈ lowerU h := by
  obtain ⟨a, d, -, -, hd⟩ := ht
  have h1 := conj_mem_lowerU_aux (D := (t : GL (HypIndex 1 1) K)) ⟨_, hd⟩ (RingEquiv.refl K)
    (mem_lowerU.mp hx)
  have e : glAut (RingEquiv.refl K) (x : GL (HypIndex 1 1) K) = x :=
    congrArg (fun φ : MulAut (GL (HypIndex 1 1) K) => φ x) (map_one glAut)
  rw [e] at h1
  exact mem_lowerU.mpr h1

theorem sup_lowerU_map_eq_top (hs : IsSimpleGroup (hypPSU h 1 1)) :
    (hypUnitriangular h 1 1).map (hypProj h 1 1) ⊔ (lowerU h).map (hypProj h 1 1) = ⊤ := by
  rw [← Subgroup.map_sup]
  set H : Subgroup (hypSU h 1 1) := hypUnitriangular h 1 1 ⊔ lowerU h with hH
  have hmap : ∀ t ∈ hypTorus h 1 1, ∀ x ∈ H, t * x * t⁻¹ ∈ H := by
    intro t ht x hx
    have : H.map (MulAut.conj t).toMonoidHom ≤ H := by
      rw [hH, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact conj_mem_hypUnitriangular_of_mem_hypBorel le_rfl (hypTorus_le_hypBorel h ht) hy
      · rintro _ ⟨y, hy, rfl⟩
        exact conj_mem_lowerU_of_torus ht hy
    exact this ⟨x, hx, rfl⟩
  have hT : hypTorus h 1 1 ≤ Subgroup.normalizer (H : Set (hypSU h 1 1)) := fun t ht =>
    Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => hmap t ht x hx, fun hx => by
      have h1 := hmap t⁻¹ (inv_mem ht) _ hx
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rwa [e] at h1⟩
  have hB : isoStabilizer h 1 1 (hypFlag h 1 1 1) ≤
      Subgroup.normalizer (H : Set (hypSU h 1 1)) := by
    intro g hg
    have hgB : g ∈ hypBorel h 1 1 := mem_hypBorel.mpr fun i hi1 hi2 => by
      obtain rfl : i = 1 := le_antisymm hi2 hi1
      exact mem_isoStabilizer.mp hg
    have h1 := hypBorel_le_sup (h := h) le_rfl le_rfl hgB
    exact (sup_le ((le_sup_left : hypUnitriangular h 1 1 ≤ H).trans Subgroup.le_normalizer) hT :
      hypUnitriangular h 1 1 ⊔ hypTorus h 1 1 ≤ Subgroup.normalizer (H : Set (hypSU h 1 1))) h1
  obtain ⟨g₀, hg₀L, hg₀⟩ := exists_lowerU_not_mem_isoStabilizer h
  have hg₀H : g₀ ∈ H := (le_sup_right : lowerU h ≤ H) hg₀L
  rcases eq_of_isoStabilizer_hypFlag_le h le_rfl le_rfl le_rfl le_rfl
    (Subgroup.normalizer (H : Set (hypSU h 1 1))) hB with hN | hN
  · exact absurd (hN ▸ Subgroup.le_normalizer hg₀H) hg₀
  · have hnorm : H.Normal := Subgroup.normalizer_eq_top_iff.mp hN
    have : (H.map (hypProj h 1 1)).Normal := hnorm.map (hypProj h 1 1) (hypProj_surjective h 1 1)
    rcases hs.eq_bot_or_eq_top_of_normal (H.map (hypProj h 1 1)) with h0 | h1
    · refine absurd ?_ hg₀
      have : hypProj h 1 1 g₀ ∈ H.map (hypProj h 1 1) := ⟨g₀, hg₀H, rfl⟩
      rw [h0, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_hypProj] at this
      exact hypScalars_le_isoStabilizer _ this
    · exact h1

theorem hypPSU_nonabelian (hs : IsSimpleGroup (hypPSU h 1 1)) :
    ∃ x y : hypPSU h 1 1, x * y ≠ y * x := by
  by_contra hcomm
  push Not at hcomm
  let _ : CommGroup (hypPSU h 1 1) :=
    { (inferInstance : Group (hypPSU h 1 1)) with mul_comm := fun a b => hcomm a b }
  have hN : ((hypUnitriangular h 1 1).map (hypProj h 1 1)).Normal := inferInstance
  obtain ⟨u, β, hβ, hu, hum⟩ := exists_rootElt h
  rcases hs.eq_bot_or_eq_top_of_normal ((hypUnitriangular h 1 1).map (hypProj h 1 1)) with
    h0 | h1
  ·
    have hu1 : hypProj h 1 1 u ∈ (hypUnitriangular h 1 1).map (hypProj h 1 1) := ⟨u, hu, rfl⟩
    rw [h0, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_hypProj] at hu1
    set W : Submodule K (HypIndex 1 1 → K) :=
      K ∙ (Pi.single (.inr (.inr 0)) 1 : HypIndex 1 1 → K) with hW
    have hfix : u • W = W := mem_isoStabilizer.mp (hypScalars_le_isoStabilizer (h := h) W hu1)
    have hmem : (Pi.single (.inr (.inr 0)) 1 : HypIndex 1 1 → K) ∈ W :=
      Submodule.mem_span_singleton_self _
    have h2 : u • (Pi.single (.inr (.inr 0)) 1 : HypIndex 1 1 → K) ∈ u • W :=
      Submodule.smul_mem_pointwise_smul _ _ _ hmem
    rw [hfix] at h2
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h2
    have h4 : (u • (Pi.single (.inr (.inr 0)) 1 : HypIndex 1 1 → K)) (.inl 0) = β := by
      change (((u : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        (Pi.single (.inr (.inr 0)) 1 : HypIndex 1 1 → K)) (.inl 0) = β
      rw [mulVec_single_one, col_apply, hum]
      simp
    refine hβ ?_
    rw [← h4, ← ha]
    simp
  ·
    have hle : (hypUnitriangular h 1 1).map (hypProj h 1 1) ≤
        projIsoStabilizer h 1 1 (hypFlag h 1 1 1) := by
      refine Subgroup.map_mono fun g hg => ?_
      have hgB : g ∈ hypBorel h 1 1 := hypUnitriangular_le_hypBorel h hg
      exact hypBorel_le_isoStabilizer h le_rfl le_rfl hgB
    exact (isCoatom_projIsoStabilizer_hypFlag h le_rfl le_rfl le_rfl le_rfl).1
      (top_le_iff.mp (h1 ▸ hle))

end CFSG.Quasithin.F7Two.U3Odd

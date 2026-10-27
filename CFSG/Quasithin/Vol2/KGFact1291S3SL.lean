module

public import CFSG.Quasithin.Vol2.KGFact1291S3Red
public import CFSG.Quasithin.Vol2.KGFact1297SL
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.Quasithin.H13.KG1291S

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

variable {n : ℕ}

theorem modO2_parabolic {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    Nonempty (ModO2 (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) ≃*
      Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) (by omega)
  have hU2 : IsPGroup 2 (unitriangular n (ZMod 2)) := hU₀ ▸ U₀.isPGroup'
  refine KG1291S.modO2_perm3_of_index_three
    (BinaryParabolic.unitriangular_le_flagStabilizer _) hU2
    (BinaryParabolic.relIndex_parabolic hj hjn) fun hle => ?_
  have hr := hle (BinaryParabolic.reflection_mem_parabolic hj hjn)
  rw [normalizer_unitriangular, BinaryParabolic.upperTriangular_eq_unitriangular] at hr
  exact BinaryParabolic.reflection_notMem_unitriangular hj hjn hr

theorem exists_parabolic_not_le {Y : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hUY : unitriangular n (ZMod 2) ≤ Y) (hY : Y ≠ ⊤) :
    ∃ H : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)), unitriangular n (ZMod 2) ≤ H ∧
      ¬ H ≤ Y ∧ Nonempty (ModO2 H ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨J, hJ, rfl⟩ := KG1297.exists_eq_flagStabilizer hUY
  obtain ⟨j, hjJ⟩ : J.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hY (flagStabilizer_empty n (ZMod 2))
  obtain ⟨hj, hjn⟩ := hJ j hjJ
  refine ⟨flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}),
    BinaryParabolic.unitriangular_le_flagStabilizer _, fun hle => ?_, modO2_parabolic hj hjn⟩
  have hsub := KG1297.subset_of_flagStabilizer_le hJ hle
  exact (hsub hjJ).2 rfl

theorem s3Hyp_SL (hn : 1 ≤ n) (B : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) :
    S3Hyp B := by
  intro T Y hTY _ hY
  obtain ⟨U₀, hU₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) hn
  obtain ⟨g, -, hg⟩ := KG1297.exists_conj_sylow (P := ⊤) T U₀ le_top le_top
  set c := MulAut.conj g with hc
  have hinj : Function.Injective (c.toMonoidHom : _ → _) := c.injective
  have hsurj : Function.Surjective (c.toMonoidHom : _ → _) := c.surjective
  have hUY : unitriangular n (ZMod 2) ≤ Y.map c.toMonoidHom := by
    rw [← hU₀, ← hg]
    exact Subgroup.map_mono hTY
  have hY' : Y.map c.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hY
    have := congrArg (Subgroup.comap c.toMonoidHom) htop
    rwa [Subgroup.comap_map_eq_self_of_injective hinj, Subgroup.comap_top] at this
  obtain ⟨H, hUH, hHY, ⟨eH⟩⟩ := exists_parabolic_not_le hUY hY'
  have hHH : (H.comap c.toMonoidHom).map c.toMonoidHom = H :=
    Subgroup.map_comap_eq_self_of_surjective hsurj H
  refine ⟨H.comap c.toMonoidHom, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    have : (T : Subgroup _).map c.toMonoidHom = unitriangular n (ZMod 2) := by
      rw [← hU₀, ← hg]
    rw [this]
    exact hUH
  · intro hle
    apply hHY
    rw [← hHH]
    exact Subgroup.map_mono hle
  · obtain ⟨e'⟩ := KG1296.nonempty_modO2_map c (H.comap c.toMonoidHom)
    rw [hHH] at e'
    exact ⟨e'.trans eH⟩

end CFSG.Quasithin.H13.KG1291S

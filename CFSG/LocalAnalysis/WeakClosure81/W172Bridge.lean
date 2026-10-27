module

public import CFSG.LocalAnalysis.WeakClosure81.W172Lem26A

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace ModDataE

variable {J E : Subgroup G} (M : ModDataE J E)

theorem w172_finrank_sp_le (S : Subgroup G) :
    Module.finrank (ZMod 2) ↥(M.sp S) ≤ rk ↥S := by
  classical
  have hcard : Nat.card ↥(S ⊓ E) = Nat.card ↥(M.sp S) :=
    Nat.card_congr (Equiv.ofBijective
      (fun x : ↥(S ⊓ E) => (⟨M.ι (x : G), (x : G), x.2, rfl⟩ : ↥(M.sp S)))
      ⟨fun x y h => Subtype.ext (M.ι_injOn x.2.2 y.2.2 (congrArg Subtype.val h)),
        fun ⟨w, e, he, hw⟩ => ⟨⟨e, he⟩, Subtype.ext hw⟩⟩)
  have h2 : Nat.card ↥(M.sp S) = 2 ^ Module.finrank (ZMod 2) ↥(M.sp S) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(M.sp S)), Nat.card_zmod]
  have hdvd : 2 ^ Module.finrank (ZMod 2) ↥(M.sp S) ∣ Nat.card ↥S := by
    rw [← h2, ← hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  unfold rk
  exact (padicValNat_dvd_iff_le Nat.card_pos.ne').1 hdvd

end ModDataE

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem w172_img_vInH_conj (c : MinCex172 D V₀ V H) (M : ModDataE H (eOmegaZ H D.T))
    {e : LGL 2 M.W} (hge : M.img V = Subgroup.zpowers e) (j : ↥H) :
    M.img (vInH V H (j : G)) = Subgroup.zpowers ((M.ρ j)⁻¹ * e * M.ρ j) := by
  have hVH : V ≤ H := c.w172_V_le_H
  have hjH : conjSubgroup H (j : G) = H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer j.2)
  have hVj : vInH V H (j : G) = conjSubgroup V (j : G) := by
    unfold vInH
    apply inf_eq_left.2
    have := E3.conjSubgroup_mono_left (j : G) hVH
    rwa [hjH] at this
  have h1 := M.img_conj hVH j⁻¹
  have h2 : ((j⁻¹ : ↥H) : G)⁻¹ = (j : G) := by simp
  rw [h2, hge] at h1
  rw [hVj, ← h1]
  unfold cj
  rw [MonoidHom.map_zpowers]
  congr 1
  simp [MulAut.conj_apply]

theorem w172_commSub_conj_le_sp (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H)
    (M : ModDataE H (eOmegaZ H D.T)) {e : LGL 2 M.W} (hge : M.img V = Subgroup.zpowers e)
    (he : e * e = 1) (j : ↥H) :
    commSub (Subgroup.zpowers ((M.ρ j)⁻¹ * e * M.ρ j)) ≤ M.sp (conjSubgroup V₀ (j : G)) := by
  classical
  have hg := c.w172_gam183_of_mem h162 j.2
  obtain ⟨-, hcond, -⟩ := w172_two5_hyps h162 c hg M
  have hA := c.w172_img_vInH_conj M hge j
  have hy2 : ((M.ρ j)⁻¹ * e * M.ρ j) ^ 2 = 1 := by
    calc ((M.ρ j)⁻¹ * e * M.ρ j) ^ 2 = (M.ρ j)⁻¹ * (e * e) * M.ρ j := by rw [pow_two]; group
      _ = 1 := by rw [he]; group
  have hrank : mOf (M.img (vInH V H (j : G))) ⊥ ≤ 1 := by
    rw [mOf_bot, hA]
    unfold mRank
    rw [Nat.card_zpowers]
    have hle : orderOf ((M.ρ j)⁻¹ * e * M.ρ j) ≤ 2 :=
      Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hy2)
    calc Nat.log 2 (orderOf ((M.ρ j)⁻¹ * e * M.ρ j)) ≤ Nat.log 2 2 := Nat.log_mono_right hle
      _ = 1 := Nat.log_eq_one_iff.2 ⟨by norm_num, by norm_num, le_refl 2⟩
  have h3 := hcond ⊥ bot_le hrank
  rw [fixSub_bot, commSpace_top_eq_commSub, hA] at h3
  exact h3

theorem w172_finrank_commSub_conj_le (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H)
    (M : ModDataE H (eOmegaZ H D.T)) {e : LGL 2 M.W} (hge : M.img V = Subgroup.zpowers e)
    (he : e * e = 1) {y : LGL 2 M.W} (hy : y ∈ M.img H) :
    Module.finrank (ZMod 2) ↥(commSub (Subgroup.zpowers (y⁻¹ * e * y))) ≤ rk ↥V₀ := by
  obtain ⟨j, -, rfl⟩ := M.mem_img.1 hy
  calc Module.finrank (ZMod 2) ↥(commSub (Subgroup.zpowers ((M.ρ j)⁻¹ * e * M.ρ j)))
      ≤ Module.finrank (ZMod 2) ↥(M.sp (conjSubgroup V₀ (j : G))) :=
        Submodule.finrank_mono (c.w172_commSub_conj_le_sp h162 M hge he j)
    _ ≤ rk ↥(conjSubgroup V₀ (j : G)) := M.w172_finrank_sp_le _
    _ = rk ↥V₀ := by unfold rk; rw [E3.card_conjSubgroup]

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end

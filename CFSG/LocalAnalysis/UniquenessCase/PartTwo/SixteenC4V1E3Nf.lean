module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4OutBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R52b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1E3GenB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

include F in
theorem s16c4v1e3_out_le {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEN : E ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hE2 : IsElemAbelian2 E) (hn : ¬ E ≤ lBar V₀ V hV L) :
    Nat.card E * Nat.card (fixV E) ≤ 2 ^ 6 := by
  obtain ⟨τ, hτE, hτ⟩ := F.exists_isSemi_of_not_le hEN hE2 hn
  have hE16 : Nat.card E ≤ 2 ^ 4 := F.s16c4_card_le_sixteen hEN hE2
  let E₀ : Subgroup (MulAut (Vtil V₀ V hV)) := E ⊓ lBar V₀ V hV L
  by_cases h3 : 3 ≤ Nat.card E₀
  · have hf : Nat.card (fixV E) ≤ 4 := F.s16c4_out_C_le_four hEN hE2 hτE hτ h3
    calc Nat.card E * Nat.card (fixV E) ≤ 2 ^ 4 * 4 := Nat.mul_le_mul hE16 hf
      _ = 2 ^ 6 := by norm_num
  · have hE0le : Nat.card E₀ ≤ 2 := by omega
    have hE4 : Nat.card E ≤ 4 := by
      have h := F.card_le_two_mul_card_inf hEN hE2 hτE hτ
      have h2 : 2 * Nat.card E₀ ≤ 4 := by omega
      exact h.trans h2
    have hfix16 : Nat.card (fixV E) ≤ 16 := by
      have hcard : Nat.card ↥(fixSp (F.suSub E₀)) ≤ 2 ^ 8 := by
        have hle : Nat.card ↥(fixSp (F.suSub E₀)) ≤ Nat.card (Fin 4 → F.K) :=
          Nat.card_le_card_of_injective
            (fun x : ↥(fixSp (F.suSub E₀)) => (x : Fin 4 → F.K)) Subtype.val_injective
        rw [Nat.card_fun, Nat.card_fin, F.card_K] at hle
        norm_num at hle ⊢
        exact hle
      have h16 : Nat.card (fixV E) * Nat.card (fixV E) ≤ 16 * 16 := by
        have h := (F.s16c4_out_card_sq_le (E := E) hτE hτ).trans hcard
        norm_num at h ⊢
        exact h
      exact Nat.mul_self_le_mul_self_iff.mp h16
    calc Nat.card E * Nat.card (fixV E) ≤ 4 * 16 := Nat.mul_le_mul hE4 hfix16
      _ = 2 ^ 6 := by norm_num

include F in
theorem s16c4v1e3_in_le {E : Subgroup (MulAut (Vtil V₀ V hV))} (hEL : E ≤ lBar V₀ V hV L)
    (hE2 : IsElemAbelian2 E) : Nat.card E * Nat.card (fixV E) ≤ 2 ^ 8 := by
  obtain ⟨hsq, hcomm⟩ := F.suSub_sq_comm hEL hE2
  have hcardE : Nat.card (F.suSub E) = Nat.card E := F.card_suSub hEL
  have hcardfix : Nat.card (fixV E) = Nat.card (fixSp (F.suSub E)) := F.card_fixV_eq hEL
  have hfixcard : Nat.card ↥(fixSp (F.suSub E)) =
      Nat.card F.K ^ Module.finrank F.K ↥(fixSp (F.suSub E)) :=
    Module.natCard_eq_pow_finrank
  have hadd := finrank_commSp_add_finrank_fixSp (F := F.K) (σ := F.σ) F.isUnitary hsq
  have hF : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  rw [← hcardE, hcardfix, hfixcard, F.card_K]
  rcases card_cases (F := F.K) (σ := F.σ) F.isUnitary hsq hcomm (n := 1) le_rfl hF with
    ⟨h0, hlt⟩ | ⟨h1, hlt⟩ | ⟨h2, hlt⟩ | ⟨h3c, hlt⟩
  · have hv : Module.finrank F.K ↥(fixSp (F.suSub E)) = 4 := by omega
    rw [hv]
    calc Nat.card (F.suSub E) * 4 ^ 4 ≤ 1 * 4 ^ 4 := Nat.mul_le_mul hlt le_rfl
      _ ≤ 2 ^ 8 := by norm_num
  · have hv : Module.finrank F.K ↥(fixSp (F.suSub E)) = 3 := by omega
    rw [hv]
    calc Nat.card (F.suSub E) * 4 ^ 3 ≤ 2 ^ 1 * 4 ^ 3 := Nat.mul_le_mul hlt le_rfl
      _ ≤ 2 ^ 8 := by norm_num
  · have hv : Module.finrank F.K ↥(fixSp (F.suSub E)) = 2 := by omega
    rw [hv]
    calc Nat.card (F.suSub E) * 4 ^ 2 ≤ 2 ^ (4 * 1) * 4 ^ 2 := Nat.mul_le_mul hlt le_rfl
      _ ≤ 2 ^ 8 := by norm_num
  · have hv : Module.finrank F.K ↥(fixSp (F.suSub E)) = 1 := by omega
    rw [hv]
    calc Nat.card (F.suSub E) * 4 ^ 1 ≤ 2 ^ (3 * 1) * 4 ^ 1 := Nat.mul_le_mul hlt le_rfl
      _ ≤ 2 ^ 8 := by norm_num

include F in
theorem s16c4v1e3_card_mul_le {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEN : E ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hE2 : IsElemAbelian2 E) : Nat.card E * Nat.card (fixV E) ≤ 2 ^ 8 := by
  by_cases hEL : E ≤ lBar V₀ V hV L
  · exact F.s16c4v1e3_in_le hEL hE2
  · exact (F.s16c4v1e3_out_le hEN hE2 hEL).trans (by norm_num)

include F in
theorem s16c4v1e3_in_eq {E : Subgroup (MulAut (Vtil V₀ V hV))} (hEL : E ≤ lBar V₀ V hV L)
    (hE2 : IsElemAbelian2 E) (hne : E ≠ ⊥)
    (h : Nat.card E * Nat.card (fixV E) = 2 ^ 8) :
    ∃ W : Submodule F.K (Fin 4 → F.K), Module.finrank F.K ↥W = 2 ∧
      (∀ u ∈ W, ∀ u' ∈ W, herm F.σ u u' = 0) ∧ F.suSub E = PW (σ := F.σ) W ∧
      Nat.card (commV E) = 2 ^ 4 := by
  obtain ⟨hsq, hcomm⟩ := F.suSub_sq_comm hEL hE2
  have hcardE : Nat.card (F.suSub E) = Nat.card E := F.card_suSub hEL
  have hcardfix : Nat.card (fixV E) = Nat.card (fixSp (F.suSub E)) := F.card_fixV_eq hEL
  have hfixcard : Nat.card ↥(fixSp (F.suSub E)) =
      Nat.card F.K ^ Module.finrank F.K ↥(fixSp (F.suSub E)) :=
    Module.natCard_eq_pow_finrank
  have hadd := finrank_commSp_add_finrank_fixSp (F := F.K) (σ := F.σ) F.isUnitary hsq
  have hF : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  have hprod : Nat.card (F.suSub E) * Nat.card ↥(fixSp (F.suSub E)) = 2 ^ 8 := by
    rw [hcardE, ← hcardfix]
    exact h
  rcases card_cases (F := F.K) (σ := F.σ) F.isUnitary hsq hcomm (n := 1) le_rfl hF with
    ⟨h0, hlt⟩ | ⟨h1, hlt⟩ | ⟨h2, hlt⟩ | ⟨h3c, hlt⟩
  · have hE1 : Nat.card E ≤ 1 := by rw [← hcardE]; exact hlt
    exact absurd ((Subgroup.card_le_one_iff_eq_bot E).1 hE1) hne
  · have hv : Module.finrank F.K ↥(fixSp (F.suSub E)) = 3 := by omega
    have hfix : Nat.card ↥(fixSp (F.suSub E)) = 4 ^ 3 := by rw [hfixcard, F.card_K, hv]
    have hprod' : Nat.card (F.suSub E) * 4 ^ 3 = 2 ^ 8 := by rw [← hfix]; exact hprod
    have hle : Nat.card (F.suSub E) * 4 ^ 3 ≤ 2 ^ 1 * 4 ^ 3 := Nat.mul_le_mul hlt le_rfl
    norm_num at hprod' hle
    omega
  · have hv : Module.finrank F.K ↥(fixSp (F.suSub E)) = 2 := by omega
    have hfix : Nat.card ↥(fixSp (F.suSub E)) = 4 ^ 2 := by rw [hfixcard, F.card_K, hv]
    have hprod' : Nat.card (F.suSub E) * 4 ^ 2 = 2 ^ 8 := by rw [← hfix]; exact hprod
    have hcard4 : Nat.card (F.suSub E) = 2 ^ (4 * 1) := by
      norm_num at hprod' ⊢
      omega
    obtain ⟨hu2, hcommfix, hPW⟩ :=
      eq_PW_of_card_eq (F := F.K) (σ := F.σ) F.isUnitary F.two_eq_zero hsq hcomm
        (n := 1) le_rfl hF hcard4
    refine ⟨commSp (F.suSub E), hu2, ?_, hPW, ?_⟩
    · intro u hu u' hu'
      have hu'h : u' ∈ horth F.σ (commSp (F.suSub E)) := by
        rw [← fixSp_eq_horth (F := F.K) (σ := F.σ) F.isUnitary hsq, ← hcommfix]
        exact hu'
      exact (mem_horth).1 hu'h u hu
    · rw [F.card_commV_eq hEL, Module.natCard_eq_pow_finrank (K := F.K), hu2, F.card_K]
      norm_num
  · have hv : Module.finrank F.K ↥(fixSp (F.suSub E)) = 1 := by omega
    have hfix : Nat.card ↥(fixSp (F.suSub E)) = 4 ^ 1 := by rw [hfixcard, F.card_K, hv]
    have hprod' : Nat.card (F.suSub E) * 4 ^ 1 = 2 ^ 8 := by rw [← hfix]; exact hprod
    have hle : Nat.card (F.suSub E) * 4 ^ 1 ≤ 2 ^ (3 * 1) * 4 ^ 1 := Nat.mul_le_mul hlt le_rfl
    norm_num at hprod' hle
    omega

include F in
theorem s16c4v1e3_gen_transfer {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEL : E ≤ lBar V₀ V hV L) {g : ↥(SUid F.σ 4)}
    (hg : F.suSub E ⊔ (F.suSub E).map (MulAut.conj g).toMonoidHom = ⊤) :
    ∃ φ ∈ lBar V₀ V hV L, lBar V₀ V hV L ≤ E ⊔ E.map (MulAut.conj φ).toMonoidHom := by
  let ι : ↥(SUid F.σ 4) →* MulAut (Vtil V₀ V hV) :=
    (lBar V₀ V hV L).subtype.comp F.π.toMonoidHom
  have hι_range : ι.range = lBar V₀ V hV L := by
    dsimp only [ι]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr F.π.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hErange : E ≤ ι.range := by rw [hι_range]; exact hEL
  have hsuSub : F.suSub E = E.comap ι := by
    ext γ
    rw [F.mem_suSub]
    rfl
  have hmap1 : (F.suSub E).map ι = E := by
    rw [hsuSub]
    exact Subgroup.map_comap_eq_self hErange
  have hconj : ι.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (ι g)).toMonoidHom.comp ι := by
    ext x y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  have hmap2 : ((F.suSub E).map (MulAut.conj g).toMonoidHom).map ι =
      E.map (MulAut.conj (ι g)).toMonoidHom := by
    rw [Subgroup.map_map, hconj, ← Subgroup.map_map, hmap1]
  refine ⟨ι g, ?_, ?_⟩
  · show ((F.π g : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) ∈ lBar V₀ V hV L
    exact (F.π g).2
  · have hmap := congrArg (Subgroup.map ι) hg
    rw [Subgroup.map_sup, Subgroup.map_top, hmap1, hmap2, hι_range] at hmap
    exact hmap.ge

include F in
theorem s16c4v1e3_eq_case {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEN : E ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hE2 : IsElemAbelian2 E) (hne : E ≠ ⊥)
    (h : Nat.card E * Nat.card (fixV E) = 2 ^ 8) :
    Nat.card (commV E) = 2 ^ 4 ∧ ∃ φ ∈ lBar V₀ V hV L,
      lBar V₀ V hV L ≤ E ⊔ E.map (MulAut.conj φ).toMonoidHom := by
  have hEL : E ≤ lBar V₀ V hV L := by
    by_contra hn
    have h6 := F.s16c4v1e3_out_le hEN hE2 hn
    have h86 : (2 : ℕ) ^ 6 < 2 ^ 8 := by norm_num
    omega
  obtain ⟨W, hW, hti, hEW, hc⟩ := F.s16c4v1e3_in_eq hEL hE2 hne h
  obtain ⟨g, hg⟩ := s16c4v1e3_generation F.isUnitary F.two_eq_zero hW hti
  rw [← hEW] at hg
  exact ⟨hc, F.s16c4v1e3_gen_transfer hEL hg⟩

end UFrame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

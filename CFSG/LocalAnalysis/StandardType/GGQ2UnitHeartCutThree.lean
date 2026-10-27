module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRaw
public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitCutThree

public section

namespace CFSG.StandardType.GGQ2Frame.UnitRaw

open CFSG CFSG.Assembly Module
open CFSG.StandardType (GGLabelIso)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def equivLabelsH {N : ℕ} (S : Finset (Fin N)) : Set LargeEvenLabel :=
  {lab | GGLabelIso (label S) lab}

private theorem l02qfrh_natCast_eq_zero (N : ℕ) (h3 : 3 ∣ N) : (N : F) = 0 := by
  obtain ⟨k, rfl⟩ := h3
  rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]

private theorem l02qfrh_oneLine_le_ker (N : ℕ) (h3 : 3 ∣ N) :
    oneLine N ≤ LinearMap.ker (sumFun N) := by
  rw [oneLine, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, sumFun_apply]
  obtain ⟨k, rfl⟩ := h3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]

private def l02qfrh_sumQ (N : ℕ) (h3 : 3 ∣ N) : Vfull N →ₗ[F] F :=
  (oneLine N).liftQ (sumFun N) (l02qfrh_oneLine_le_ker N h3)

private theorem l02qfrh_sumQ_mk {N : ℕ} (h3 : 3 ∣ N) (w : W N) :
    l02qfrh_sumQ N h3 ((oneLine N).mkQ w) = sumFun N w := by
  simp [l02qfrh_sumQ]

private theorem l02qfrh_heart_eq_ker {N : ℕ} (h3 : 3 ∣ N) :
    heart N = LinearMap.ker (l02qfrh_sumQ N h3) := by
  ext x
  obtain ⟨w, rfl⟩ := (oneLine N).mkQ_surjective x
  rw [heart, Submodule.mem_map, LinearMap.mem_ker, l02qfrh_sumQ_mk]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have h1 : y - w ∈ oneLine N := by
      have hzero : (oneLine N).mkQ (y - w) = 0 := by
        rw [map_sub, hxy, sub_self]
      rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at hzero
    have hsum : sumFun N w = 0 := by
      have hyw : sumFun N (y - w) = 0 := l02qfrh_oneLine_le_ker N h3 h1
      calc sumFun N w = sumFun N y - sumFun N (y - w) := by rw [map_sub]; abel
        _ = 0 := by rw [hy, hyw, sub_zero]
    exact hsum
  · intro hx
    exact ⟨w, hx, rfl⟩

private def l02qfrh_phi (N : ℕ) (h3 : 3 ∣ N) (S : Finset (Fin N)) :
    ↥(cent S) →ₗ[F] F :=
  (l02qfrh_sumQ N h3).comp (cent S).subtype

theorem finrank_centH {N : ℕ} (h3 : 3 ∣ N) (S : Finset (Fin N)) (hS : S.Nonempty)
    (hne : S ≠ Finset.univ) : finrank F (centH S) = N - S.card - 1 := by
  have hkereq : LinearMap.ker (l02qfrh_phi N h3 S) =
      (heart N).comap (cent S).subtype := by
    ext x
    simp only [LinearMap.mem_ker, l02qfrh_phi, LinearMap.comp_apply, Submodule.mem_comap,
      Submodule.subtype_apply]
    rw [l02qfrh_heart_eq_ker h3, LinearMap.mem_ker]
  have hφne : l02qfrh_phi N h3 S ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i : Fin N, i ∉ S := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hne (by ext i; simp [h i])
    have hmem : (oneLine N).mkQ (Pi.single i (1 : F)) ∈ cent S := by
      rw [mem_cent_iff]
      refine ⟨Pi.single i (1 : F), rfl, ?_⟩
      intro a ha b hb
      have hai : a ≠ i := fun h => hi (h ▸ ha)
      have hbi : b ≠ i := fun h => hi (h ▸ hb)
      simp [hai, hbi]
    have hval : l02qfrh_phi N h3 S ⟨(oneLine N).mkQ (Pi.single i (1 : F)), hmem⟩ = 1 := by
      show (l02qfrh_sumQ N h3) ((oneLine N).mkQ (Pi.single i (1 : F))) = 1
      rw [l02qfrh_sumQ_mk, sumFun_apply]
      simp
    intro hzero
    have h1 : (1 : F) = 0 := by
      rw [← hval, hzero, LinearMap.zero_apply]
    exact one_ne_zero h1
  have hrn : finrank F (LinearMap.ker (l02qfrh_phi N h3 S)) + 1 = finrank F ↥(cent S) :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hφne
  have hcentH_fin : finrank F (centH S) = finrank F ↥(cent S ⊓ heart N) := by
    rw [centH, ← Submodule.finrank_map_subtype_eq (heart N), Submodule.map_comap_subtype,
      inf_comm]
  have hkerfin : finrank F (LinearMap.ker (l02qfrh_phi N h3 S)) =
      finrank F ↥(cent S ⊓ heart N) := by
    rw [hkereq, ← Submodule.finrank_map_subtype_eq (cent S), Submodule.map_comap_subtype]
  rw [hkerfin, ← hcentH_fin, finrank_cent S hS hne] at hrn
  omega

theorem unitHeart_noInternalTwoNode {N : ℕ} (hN : 4 ≤ N) (h3 : 3 ∣ N) (v : ↥(heart N)) (hv : v ≠ 0)
    (U : Submodule F ↥(heart N)) (hU : finrank F U = 2) (hvU : v ∈ U) (S T : Finset (Fin N))
    (hS : admissible S) (hT : admissible T)
    (hocc_S : occursH (Submodule.span F {v}) S) (hocc_T : occursH U T)
    (hcent_S : centH S = Submodule.span F {v}) (hcent_T : centH T ≤ U)
    (hin : v ∈ insideH S) :
    ∀ labK ∈ equivLabelsH S, ∀ labJ ∈ equivLabelsH T,
      ¬ CFSG.StandardType.GGQ2Frame.TwoNodeLabels 3 labK labJ := by
  exfalso
  have hS4 : 4 ≤ S.card := hS
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hSne : S ≠ Finset.univ := by
    intro hSuniv
    have hcv : (v : Vfull N) ∈ cent (Finset.univ : Finset (Fin N)) := by
      rw [mem_cent_iff]
      obtain ⟨w, hw⟩ := (oneLine N).mkQ_surjective (v : Vfull N)
      refine ⟨w, hw, ?_⟩
      intro i _ j _
      have hd : diffFun N i j (v : Vfull N) = 0 := by
        have hocc := hocc_S
        rw [occursH, hSuniv] at hocc
        obtain ⟨-, hmax⟩ := hocc
        have hi : i ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ i
        have := (hmax i hi j).mp (Finset.mem_univ j)
        exact this _ ⟨v, Submodule.mem_span_singleton_self v, rfl⟩
      have hd' : diffFun N i j ((oneLine N).mkQ w) = 0 := by simpa [hw] using hd
      rw [diffFun_mk, sub_eq_zero] at hd'
      exact hd'
    rw [cent_univ] at hcv
    have hv0 : (v : Vfull N) = 0 := by simpa using hcv
    exact hv (Subtype.coe_injective (by simpa using hv0))
  have hfin1 : finrank F (centH S) = 1 := by
    rw [hcent_S, finrank_span_singleton hv]
  have hdim := finrank_centH h3 S hSn hSne
  rw [hfin1] at hdim
  have hcard : S.card = N - 2 := by
    have hSle : S.card ≤ N := by simpa using Finset.card_le_univ S
    omega
  have hcardmod : (S.card : F) = 1 := by
    rw [hcard, Nat.cast_sub (show 2 ≤ N by omega), l02qfrh_natCast_eq_zero N h3]
    decide
  obtain ⟨w, hw, hsupp, hsum⟩ :=
    (mem_inside_iff S (v : Vfull N)).mp ((mem_insideH_iff S v).mp hin)
  have hconst : ∀ i ∈ S, ∀ j ∈ S, w i = w j := by
    intro i hi j hj
    have hocc := hocc_S
    rw [occursH] at hocc
    obtain ⟨-, hmax⟩ := hocc
    have hd : diffFun N i j (v : Vfull N) = 0 := by
      have := (hmax i hi j).mp hj
      exact this _ ⟨v, Submodule.mem_span_singleton_self v, rfl⟩
    have hd' : diffFun N i j ((oneLine N).mkQ w) = 0 := by simpa [hw] using hd
    rw [diffFun_mk, sub_eq_zero] at hd'
    exact hd'
  have hw0 : w = 0 := by
    funext i
    by_cases hi : i ∈ S
    · have h1 : S.sum w = (S.card : F) * w i := by
        rw [Finset.sum_congr rfl (fun j hj => (hconst i hi j hj).symm), Finset.sum_const,
          nsmul_eq_mul]
      have h2 : S.sum w = ∑ j, w j := by
        simpa using Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => hsupp x hx)
      have h3 : (S.card : F) * w i = 0 := by
        rw [← h1, h2, hsum]
      rw [hcardmod, one_mul] at h3
      exact h3
    · exact hsupp i hi
  have hv0 : (v : Vfull N) = 0 := by
    rw [← hw, hw0, map_zero]
  exact hv (Subtype.coe_injective (by simpa using hv0))

end

end CFSG.StandardType.GGQ2Frame.UnitRaw

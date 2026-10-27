module

public import CFSG.LocalAnalysis.StandardType.GGSporKStepFour
public import CFSG.LocalAnalysis.StandardType.GGSporKStepZero
public import CFSG.LocalAnalysis.StandardType.GGSporKStepOne
public import CFSG.LocalAnalysis.StandardType.GGSporKStepThree
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenBasic
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionDefining

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem ggSporK_sylow_dvd_card {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E) :
    p ^ (Nat.card W).factorization p ∣ Nat.card ↥H := by
  have hp : p.Prime := hyp.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hE : IsElemAbelian p E := hyp.1.2.2.1
  have hfus : GGControlsStrongFusion H E := hyp.1.2.2.2.2
  have hE1 : E ⊓ ⊤ ≠ ⊥ := by
    rw [inf_top_eq]
    rintro rfl
    have hc : Nat.card (⊥ : Subgroup W) = p ^ 2 := hyp.1.2.2.2.1
    rw [Subgroup.card_bot] at hc
    have h2 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    exact absurd hc (ne_of_lt h2)
  obtain ⟨S, -, hSp, hidx, -, hSH, -⟩ := hfus.exists_sylow_normalizer_le hp hE hE1
  obtain ⟨a, ha⟩ := hSp.exists_card_eq
  rw [Subgroup.relIndex_top_right] at hidx
  have hW : Nat.card W = p ^ a * S.index := by rw [← ha]; exact (Subgroup.card_mul_index S).symm
  have hfac : (Nat.card W).factorization p = a := by
    have hidx0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hW, Nat.factorization_mul (pow_ne_zero a hp.ne_zero) hidx0, Finsupp.add_apply,
      hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hidx]
    simp
  rw [hfac, ← ha]
  exact Subgroup.card_dvd_of_le hSH

theorem ggSporK_false_of_inputsA_W {W : Type} [Group W] [Finite W] (p : ℕ)
    (hCen : BMNoLiePComp p W) (hG1 : BMPPrimeCore p W) (hZ : BMCentreZ p W) (hOrd : BMOrd p W)
    (H E : Subgroup W) (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥) : False := by
  have hP' : LargeEvenPPrimeCore p ↥H = ⊥ := ggSporK_pPrimeCore_eq_bot hCen hG1 hyp
  have h2 : CFSG.pCore 2 ↥H = ⊥ := ggSporK_pCore_two_eq_bot hyp.1.1 hyp.1.2.1 hP'
  have hJ : ∃ J : Subgroup W, IsComponentOf J H := ggSporK_exists_component h2 hL
  have hP : CFSG.pCore p ↥H = ⊥ := ggSporK_pCore_eq_bot hCen hG1 hZ hyp hP' hJ
  obtain ⟨L, hLc, hLs, -, hcent, hnorm⟩ := ggSporK_layer_simple hCen hG1 hZ hyp hP' hP hJ
  obtain ⟨-, hmark⟩ := ggSporK_component_data hyp h2 hLc
  let f : ↥H →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hact : ∀ (h : ↥H) (x : ↥L), (((f h) x : ↥L) : W) = (h : W) * (x : W) * (h : W)⁻¹ :=
    fun _ _ => rfl
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have hc : (h : W) ∈ Subgroup.centralizer (L : Set W) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hact h ⟨x, hx⟩
      rw [hh] at h1
      have h2' : x = (h : W) * x * (h : W)⁻¹ := h1
      calc x * (h : W) = (h : W) * x * (h : W)⁻¹ * (h : W) := by rw [← h2']
        _ = (h : W) * x := by group
    have hmem : (h : W) ∈ H ⊓ Subgroup.centralizer (L : Set W) := ⟨h.2, hc⟩
    rw [hcent, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcard : Nat.card ↥H ∣ Nat.card (MulAut ↥L) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact Subgroup.card_subgroup_dvd_card f.range
  exact hOrd L hLs hmark ((ggSporK_sylow_dvd_card hyp).trans hcard)

end CFSG.StandardType.SporadicShape

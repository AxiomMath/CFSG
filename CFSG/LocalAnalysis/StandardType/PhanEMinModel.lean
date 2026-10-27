module

public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.LocalAnalysis.StandardType.PhanEChevModel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (hA : TauCeti.IsFiniteType τ.cartan)
  (k : Type) [Field k] [CharP k 2]

theorem isSign_eq_one_of_charTwo {σ : k} (h : IsSign σ) : σ = 1 := by
  rcases h with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

theorem minNm_mul_self_of_charTwo (i : Fin τ.rank) : hV.nm k i * hV.nm k i = 1 := by
  have h : (-1 : kˣ) = 1 := by
    ext
    rw [Units.val_neg, Units.val_one, CharTwo.neg_eq]
  rw [← pow_two, hV.nm_sq k i, h, hV.hm_one k i]

@[expose] noncomputable def minChevModel :
    ChevModel2 (hV.minDatum hA k) (hV.nm k) (hV.torus k) k where
  x := hV.xm k
  x_mem γ _ g := hV.mem_rootGroup k
  x_add γ _ c d := hV.xm_add k γ c d
  x_inj γ hγ := hV.xm_injective k ((hV.mem_minDatum_roots hA k).1 hγ)
  nm_conj i γ hγ c := by
    have hroot : IsRoot τ γ := (hV.mem_minDatum_roots hA k).1 hγ
    obtain ⟨σ, hσ, h⟩ := hV.nm_conj_xm k hroot i
    change hV.nm k i * hV.xm k γ c * (hV.nm k i)⁻¹ =
      hV.xm k (weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple i) γ) c
    rw [h c, weylAction_simple_apply hA i γ, isSign_eq_one_of_charTwo k hσ, one_mul]
  nm_sq i := minNm_mul_self_of_charTwo hV k i
  hh i := hV.hHom k i
  hh_range i := rfl
  hh_conj i t γ hγ c := by
    have hroot : IsRoot τ γ := (hV.mem_minDatum_roots hA k).1 hγ
    change hV.hm k i t * hV.xm k γ c * (hV.hm k i t)⁻¹ =
      hV.xm k γ (((t ^ (∑ j, τ.cartan i j * γ j) : kˣ) : k) * c)
    exact hV.hm_conj_xm k hroot i t c
  nm_def i := by
    change hV.nt k i 1 = hV.xm k (Pi.single i 1) 1 * hV.xm k (-Pi.single i 1) (-1) *
      hV.xm k (Pi.single i 1) 1
    rw [MinData.Valid.nt, inv_one, Units.val_one]
  hh_def i t := by
    change hV.hm k i t =
      (hV.xm k (Pi.single i 1) t * hV.xm k (-Pi.single i 1) (-((t⁻¹ : kˣ) : k)) *
        hV.xm k (Pi.single i 1) t) * (hV.nm k i)⁻¹
    rw [MinData.Valid.hm, ← MinData.Valid.nm, MinData.Valid.nt]

end CFSG.ClassicalInvolution.Phan.PhanE

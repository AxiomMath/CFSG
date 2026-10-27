module

public import CFSG.Milestones.ASVolI.F411.aSwG2N
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section G2

set_option linter.unusedSectionVars false


theorem burnsideF411T_swap_G2_ne_three_of_pCore {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .G2 p f Gp M₁ M₂) (hp3 : p ≠ 3)
    (hB : pCoreOf p (M₁ ⊓ M₂) = pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) :
    burnsideF411_Swap M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Gp.Normal := hyp.normal
  obtain ⟨chart, hBch, hP1, hP2⟩ := hyp.lie_amalgam
  rcases chart.coordinates with
    ⟨c, hk, -⟩ | ⟨-, hp, hd, K, fK, finK, card, marking, h1, h2, h3, -, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c <;> decide)
  rotate_left
  iterate 4 exact absurd hk (by decide)
  letI := fK
  haveI := finK
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := burnsideF4h_cl_charP card
  have e1 : ∀ L, G2Native.fullImage K marking L =
      (G2Native.fullLocal K L).map marking.toMonoidHom := fun L => rfl
  rw [e1] at h1 h2 h3
  obtain ⟨hl, -, -⟩ := burnsideF4h_g2_full K p f hp hd card
  have hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
    have hmap := burnsideF4h_isLieParabolics_marking Gp marking hl
    rw [← h1, ← h2, ← h3, ← hBch, ← hP1, ← hP2] at hmap
    exact hmap
  set Z := Subgroup.center (G2Native.Parent K) with hZdef
  have hZ : Z = ⊥ := center_adjointGroup_eq_bot
  let χ₀ : G2Native.Parent K →* ↥Gp := marking.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hχ : Function.Bijective χ₀ := by
    refine ⟨fun a b hab => ?_, marking.surjective.comp (QuotientGroup.mk'_surjective Z)⟩
    have h : (QuotientGroup.mk' Z a : G2Native.FullModel K) = QuotientGroup.mk' Z b :=
      marking.injective hab
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hZ,
      Subgroup.mem_bot] at h
    exact inv_mul_eq_one.mp h
  let χ : G2Native.Parent K ≃* ↥Gp := MulEquiv.ofBijective χ₀ hχ
  have hQ : ∀ L, (G2Native.fullLocal K L).map marking.toMonoidHom = L.map χ.toMonoidHom :=
    fun L => by
      rw [G2Native.fullLocal, Subgroup.map_map]
      rfl
  have hι : Function.Injective (Gp.subtype.comp χ.toMonoidHom) :=
    Gp.subtype_injective.comp χ.injective
  have hpb : G2Native.positiveBorel K = borelSub Tag.G2 K := by
    unfold borelSub Subgroup.subgroupOf
    rw [← burnsideF4h_g2_map_positiveBorel]
    exact (Subgroup.comap_map_eq_self_of_injective (adjointGroup Tag.G2 K).subtype_injective
      _).symm
  have hBE : Gp ⊓ (M₁ ⊓ M₂) = (borelSub Tag.G2 K).map (Gp.subtype.comp χ.toMonoidHom) := by
    rw [hBch, h1, hQ, Subgroup.map_map, hpb]
  have hPE : Gp ⊓ M₁ =
      (G2Native.pointParabolic K).map (Gp.subtype.comp χ.toMonoidHom) := by
    rw [hP1, h2, hQ, Subgroup.map_map]
  have hUE : pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) =
      (posUnipotentSub Tag.G2 K).map (Gp.subtype.comp χ.toMonoidHom) := by
    rw [hBE, burnsideF411a_pCoreOf_map hι, burnsideF411a_g2_pCoreOf_borelSub p]
  have h3K : (3 : K) ≠ 0 := by
    intro h
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).1 (by exact_mod_cast h)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd)
  have hBT := burnsideF411_borelTitsIn hyp ⟨by decide, by decide⟩
  have hctr : burnsideF411_ctr ((posUnipotentSub Tag.G2 K).map (Gp.subtype.comp χ.toMonoidHom)) =
      (G2Native.longRoot K).map (Gp.subtype.comp χ.toMonoidHom) := by
    ext y
    rw [burnsideF411_mem_ctr]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hc⟩
      refine ⟨x, (burnsideF411a_g2_center_iff h3K x).1 ⟨hx, fun x' hx' => hι ?_⟩, rfl⟩
      rw [map_mul, map_mul]
      exact hc _ ⟨x', hx', rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxU, hxc⟩ := (burnsideF411a_g2_center_iff h3K x).2 hx
      refine ⟨⟨x, hxU, rfl⟩, ?_⟩
      rintro _ ⟨x', hx', rfl⟩
      rw [← map_mul, ← map_mul, hxc x' hx']
  have hZ' : Gp ⊓ M₁ ≤
      Subgroup.normalizer (burnsideF411_ctr (pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) : Set E) := by
    rw [hPE, hUE, hctr]
    exact (Subgroup.map_mono burnsideF4h_g2_point_le_normalizer).trans
      (Subgroup.le_normalizer_map _)
  exact burnsideF411_swap_of_center hyp.normal hyp.split hP hBT hB hZ'

theorem burnsideF411T_swap_G2_ne_three_top {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .G2 p f Gp M₁ M₂) (hp3 : p ≠ 3) (hGp : Gp = ⊤) :
    burnsideF411_Swap M₁ M₂ :=
  burnsideF411T_swap_G2_ne_three_of_pCore hyp hp3 (by rw [hGp, top_inf_eq])

end G2

end CFSG.ASVolI

module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXAA
public import CFSG.Quasithin.Background.D2Tools
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_stableUnder_bot {X : Subgroup (MulAut W)} :
    StableUnder X (⊥ : Subgroup W) := by
  intro x hx u hu
  rw [Subgroup.mem_bot] at hu ⊢
  rw [hu, map_one]

private theorem w16g_sup_zpowers_eq_of_relIndex {H X : Subgroup (MulAut W)} {ℓ : MulAut W}
    {p : ℕ} (hp : p.Prime) (hHle : H ≤ X) (hHrel : H.relIndex X = p) (hℓX : ℓ ∈ X)
    (hℓnot : ℓ ∉ H) : H ⊔ Subgroup.zpowers ℓ = X := by
  have hle : H ⊔ Subgroup.zpowers ℓ ≤ X := sup_le hHle (Subgroup.zpowers_le.mpr hℓX)
  have h1 := Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers ℓ) X le_sup_left hle
  rw [hHrel] at h1
  have hne1 : H.relIndex (H ⊔ Subgroup.zpowers ℓ) ≠ 1 := by
    intro h
    have hle' : H ⊔ Subgroup.zpowers ℓ ≤ H := Subgroup.relIndex_eq_one.mp h
    have hzle : Subgroup.zpowers ℓ ≤ H :=
      le_trans (le_sup_right : Subgroup.zpowers ℓ ≤ H ⊔ Subgroup.zpowers ℓ) hle'
    exact hℓnot (hzle (Subgroup.mem_zpowers ℓ))
  have hdvd : H.relIndex (H ⊔ Subgroup.zpowers ℓ) ∣ p := ⟨_, h1.symm⟩
  rcases (Nat.dvd_prime hp).1 hdvd with hd1 | hdp
  · exact absurd hd1 hne1
  · have he1 : (H ⊔ Subgroup.zpowers ℓ).relIndex X = 1 := by
      have h1' := h1
      rw [hdp] at h1'
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact h1')
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp he1)

private theorem w16g_s13IsoSum_eq_of_secIsoOn {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hAB : SecIsoOn X A ⊥ B ⊥) (hBA : SecIsoOn X B ⊥ A ⊥) :
    s13IsoSum X A = s13IsoSum X B := by
  apply le_antisymm
  · unfold s13IsoSum
    refine iSup_le fun V => iSup_le fun hV => ?_
    exact le_iSup₂ (f := fun V (_ : IsIrrOn X V ⊥ ∧ SecIsoOn X V ⊥ B ⊥) => V) V
      ⟨hV.1, secIsoOn_trans hV.2 hAB⟩
  · unfold s13IsoSum
    refine iSup_le fun V => iSup_le fun hV => ?_
    exact le_iSup₂ (f := fun V (_ : IsIrrOn X V ⊥ ∧ SecIsoOn X V ⊥ A ⊥) => V) V
      ⟨hV.1, secIsoOn_trans hV.2 hBA⟩

theorem w16g_secIsoOn_of_kerOn_eq (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hX : IsElemAbelian 3 X) {U₀ U₁ : Subgroup W} (h₀ : IsIrrOn X U₀ ⊥) (h₁ : IsIrrOn X U₁ ⊥)
    (hne₀ : commSub U₀ X ≠ ⊥) (hne₁ : commSub U₁ X ≠ ⊥)
    (hker : X ⊓ centSub U₀ = X ⊓ centSub U₁) :
    SecIsoOn X U₁ ⊥ U₀ ⊥ ∧ SecIsoOn X U₀ ⊥ U₁ ⊥ := by
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  by_cases hU : U₀ = U₁
  · subst hU
    exact ⟨secIsoOn_refl h₁.2.1 w16g_stableUnder_bot bot_le,
      secIsoOn_refl h₁.2.1 w16g_stableUnder_bot bot_le⟩
  · have hdisj : U₀ ⊓ U₁ = ⊥ := by
      have hstab : StableUnder X (U₀ ⊓ U₁) := stableUnder_inf h₀.2.1 h₁.2.1
      rcases h₀.2.2.2 (U₀ ⊓ U₁) hstab bot_le inf_le_left with h | h
      · exact h
      · exfalso
        have hU₀le : U₀ ≤ U₁ := by rw [← h]; exact inf_le_right
        rcases h₁.2.2.2 U₀ h₀.2.1 bot_le hU₀le with h0 | h0
        · exact (not_le_of_gt h₀.1) h0.le
        · exact hU h0
    let H : Subgroup (MulAut W) := X ⊓ centSub U₀
    have hHker : H = X ⊓ centSub U₁ := by
      change X ⊓ centSub U₀ = X ⊓ centSub U₁
      exact hker
    have hHle : H ≤ X := by change X ⊓ centSub U₀ ≤ X; exact inf_le_left
    have hHcent₀ : H ≤ centSub U₀ := by
      change X ⊓ centSub U₀ ≤ centSub U₀; exact inf_le_right
    have hHcent₁ : H ≤ centSub U₁ := by rw [hHker]; exact inf_le_right
    have hrel : H.relIndex X = 3 :=
      w16g_index_kerOn_eq_prime (p := 3) hW (by norm_num) (by norm_num) hX h₀ hne₀
    have hHneX : H ≠ X := by
      intro hHX
      have h1 : H.relIndex X = 1 := by rw [hHX]; exact Subgroup.relIndex_self X
      rw [h1] at hrel
      exact (by norm_num : (1 : ℕ) ≠ 3) hrel
    have hHlt : H < X := lt_of_le_of_ne hHle hHneX
    obtain ⟨x, hxX, hxH⟩ := SetLike.exists_of_lt hHlt
    have hxH₀ : x ∉ X ⊓ centSub U₀ := by change x ∉ H; exact hxH
    have hxH₁ : x ∉ X ⊓ centSub U₁ := by rw [← hHker]; exact hxH
    have hnt₀ : ∃ u ∈ U₀, x u ≠ u := by
      by_contra h
      push Not at h
      exact hxH₀ (Subgroup.mem_inf.mpr ⟨hxX, mem_centSub.mpr h⟩)
    have hnt₁ : ∃ u ∈ U₁, x u ≠ u := by
      by_contra h
      push Not at h
      exact hxH₁ (Subgroup.mem_inf.mpr ⟨hxX, mem_centSub.mpr h⟩)
    have hx3 : x ^ 3 = 1 := hX.2 x hxX
    have hfix₀ : ∀ w ∈ U₀, x w = w → w = 1 := by
      intro w hw hxw
      have hbot := w16g_inf_fixV_zpowers_eq_bot hW hX.1 h₀ hxX hnt₀
      have h1 : w ∈ s13IsoSum X U₀ := w16g_le_s13IsoSum_self h₀ hw
      have h2 : w ∈ fixV (Subgroup.zpowers x) := mem_fixV_zpowers_iff_apply.mpr hxw
      have h3 : w ∈ (⊥ : Subgroup W) := by
        rw [← hbot]; exact Subgroup.mem_inf.mpr ⟨h1, h2⟩
      simpa using h3
    have hfix₁ : ∀ w ∈ U₁, x w = w → w = 1 := by
      intro w hw hxw
      have hbot := w16g_inf_fixV_zpowers_eq_bot hW hX.1 h₁ hxX hnt₁
      have h1 : w ∈ s13IsoSum X U₁ := w16g_le_s13IsoSum_self h₁ hw
      have h2 : w ∈ fixV (Subgroup.zpowers x) := mem_fixV_zpowers_iff_apply.mpr hxw
      have h3 : w ∈ (⊥ : Subgroup W) := by
        rw [← hbot]; exact Subgroup.mem_inf.mpr ⟨h1, h2⟩
      simpa using h3
    have hrel₀ : ∀ w ∈ U₀, x (x w) = x w * w := by
      intro w hw
      have hx3w : x (x (x w)) = w := by
        have h := congrArg (fun f : MulAut W => f w) hx3
        simpa [pow_three, MulAut.mul_apply, MulAut.one_apply] using h
      have hcU : x (x w) * x w * w ∈ U₀ :=
        U₀.mul_mem (U₀.mul_mem (h₀.2.1 x hxX (x w) (h₀.2.1 x hxX w hw))
          (h₀.2.1 x hxX w hw)) hw
      have hxc : x (x (x w) * x w * w) = x (x w) * x w * w := by
        rw [map_mul, map_mul, hx3w]
        ac_rfl
      have hc1 : x (x w) * x w * w = 1 := hfix₀ _ hcU hxc
      have hc1' : x (x w) * (x w * w) = 1 := by rw [← mul_assoc]; exact hc1
      calc x (x w) = x (x w) * 1 := (mul_one _).symm
        _ = x (x w) * ((x w * w) * (x w * w)) := by rw [hW (x w * w)]
        _ = (x (x w) * (x w * w)) * (x w * w) := (mul_assoc _ _ _).symm
        _ = 1 * (x w * w) := by rw [hc1']
        _ = x w * w := one_mul _
    have hrel₁ : ∀ w ∈ U₁, x (x w) = x w * w := by
      intro w hw
      have hx3w : x (x (x w)) = w := by
        have h := congrArg (fun f : MulAut W => f w) hx3
        simpa [pow_three, MulAut.mul_apply, MulAut.one_apply] using h
      have hcU : x (x w) * x w * w ∈ U₁ :=
        U₁.mul_mem (U₁.mul_mem (h₁.2.1 x hxX (x w) (h₁.2.1 x hxX w hw))
          (h₁.2.1 x hxX w hw)) hw
      have hxc : x (x (x w) * x w * w) = x (x w) * x w * w := by
        rw [map_mul, map_mul, hx3w]
        ac_rfl
      have hc1 : x (x w) * x w * w = 1 := hfix₁ _ hcU hxc
      have hc1' : x (x w) * (x w * w) = 1 := by rw [← mul_assoc]; exact hc1
      calc x (x w) = x (x w) * 1 := (mul_one _).symm
        _ = x (x w) * ((x w * w) * (x w * w)) := by rw [hW (x w * w)]
        _ = (x (x w) * (x w * w)) * (x w * w) := (mul_assoc _ _ _).symm
        _ = 1 * (x w * w) := by rw [hc1']
        _ = x w * w := one_mul _
    have hU₀ne : U₀ ≠ ⊥ := bot_lt_iff_ne_bot.mp h₀.1
    obtain ⟨u, huU₀, hu1⟩ := (Subgroup.bot_or_exists_ne_one U₀).resolve_left hU₀ne
    have hU₁ne : U₁ ≠ ⊥ := bot_lt_iff_ne_bot.mp h₁.1
    obtain ⟨u', hu'U₁, hu'1⟩ := (Subgroup.bot_or_exists_ne_one U₁).resolve_left hU₁ne
    let v : W := u * u'
    let D : Subgroup W := klein v (x v) (hW v) (hW (x v)) (by rw [mul_comm])
    have hvv : x (x v) = x v * v := by
      change x (x (u * u')) = x (u * u') * (u * u')
      rw [map_mul, map_mul, hrel₀ u huU₀, hrel₁ u' hu'U₁]
      ac_rfl
    have hDstab : StableUnder X D := by
      have hHcentD : H ≤ centSub D := by
        intro c hc
        have hcv : c v = v := by
          change c (u * u') = u * u'
          rw [map_mul, (mem_centSub.mp (hHcent₀ hc) u huU₀),
            (mem_centSub.mp (hHcent₁ hc) u' hu'U₁)]
        have hcxv : c (x v) = x v := by
          have hcomm : c * x = x * c :=
            congrArg Subtype.val (hX.1.is_comm.comm ⟨c, hHle hc⟩ ⟨x, hxX⟩)
          rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hcv]
        rw [mem_centSub]
        intro z hz
        rw [mem_klein] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact map_one c
        · exact hcv
        · exact hcxv
        · rw [map_mul, hcv, hcxv]
      have hHstab : H ≤ stabSub D := hHcentD.trans (centSub_le_stabSub D)
      have hxstab : Subgroup.zpowers x ≤ stabSub D := by
        refine Subgroup.zpowers_le.mpr ?_
        rw [mem_stabSub]
        have hxD : ∀ z ∈ D, x z ∈ D := by
          intro z hz
          rw [mem_klein] at hz ⊢
          rcases hz with rfl | rfl | rfl | rfl
          · exact Or.inl (map_one x)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · rw [hvv]
            exact Or.inr (Or.inr (Or.inr (mul_comm (x v) v)))
          · rw [map_mul, hvv, ← mul_assoc, hW (x v), one_mul]
            exact Or.inr (Or.inl rfl)
        intro z
        constructor
        · intro hz
          have h1 : x (x z) ∈ D := hxD (x z) hz
          have h2 : x (x (x z)) ∈ D := hxD (x (x z)) h1
          have h3 : x (x (x z)) = z := by
            have h := congrArg (fun f : MulAut W => f z) hx3
            simpa [pow_three, MulAut.mul_apply, MulAut.one_apply] using h
          rwa [h3] at h2
        · exact hxD z
      have hXle : X ≤ stabSub D := by
        have hsup : H ⊔ Subgroup.zpowers x = X :=
          w16g_sup_zpowers_eq_of_relIndex (p := 3) (by norm_num) hHle hrel hxX hxH
        rw [← hsup]
        exact sup_le hHstab hxstab
      intro y hy w hw
      exact (mem_stabSub.mp (hXle hy) w).mpr hw
    have hu_mem : u ∈ D ⊔ U₁ := by
      refine Subgroup.mem_sup.mpr ⟨v, ?_, u', hu'U₁, ?_⟩
      · rw [mem_klein]; exact Or.inr (Or.inl rfl)
      · change (u * u') * u' = u
        rw [mul_assoc, hW u', mul_one]
    have hAle : U₀ ≤ D ⊔ U₁ := by
      have hJstab : StableUnder X ((D ⊔ U₁) ⊓ U₀) :=
        stableUnder_inf (stableUnder_sup hDstab h₁.2.1) h₀.2.1
      have hJne : ((D ⊔ U₁) ⊓ U₀) ≠ ⊥ := by
        intro hbot
        have : u ∈ (⊥ : Subgroup W) := by
          rw [← hbot]; exact Subgroup.mem_inf.mpr ⟨hu_mem, huU₀⟩
        exact hu1 (by simpa using this)
      rcases h₀.2.2.2 ((D ⊔ U₁) ⊓ U₀) hJstab bot_le inf_le_right with h | h
      · exact absurd h hJne
      · rw [← h]; exact inf_le_left
    have hDU₀ : D ⊓ U₀ = ⊥ := by
      rw [eq_bot_iff]
      intro d hd
      obtain ⟨hdD, hdU₀⟩ := Subgroup.mem_inf.mp hd
      rw [mem_klein] at hdD
      rcases hdD with h1 | h1 | h1 | h1
      · rw [h1]; exact Subgroup.mem_bot.mpr rfl
      · exfalso
        have hvU₀ : v ∈ U₀ := h1 ▸ hdU₀
        have hu'U₀ : u' ∈ U₀ := by
          have h2 : u' = u * v := by
            change u' = u * (u * u')
            rw [← mul_assoc, hW u, one_mul]
          rw [h2]; exact U₀.mul_mem huU₀ hvU₀
        have h3 : u' ∈ (⊥ : Subgroup W) := by
          rw [← hdisj]; exact Subgroup.mem_inf.mpr ⟨hu'U₀, hu'U₁⟩
        exact hu'1 (by simpa using h3)
      · exfalso
        have hxvU₀ : x v ∈ U₀ := h1 ▸ hdU₀
        have hxuU₀ : x u ∈ U₀ := h₀.2.1 x hxX u huU₀
        have hxu'U₀ : x u' ∈ U₀ := by
          have h2 : x u' = (x u)⁻¹ * (x v) := by
            change x u' = (x u)⁻¹ * x (u * u')
            rw [map_mul, inv_mul_cancel_left]
          rw [h2]; exact U₀.mul_mem (U₀.inv_mem hxuU₀) hxvU₀
        have h3 : x u' ∈ (⊥ : Subgroup W) := by
          rw [← hdisj]; exact Subgroup.mem_inf.mpr ⟨hxu'U₀, h₁.2.1 x hxX u' hu'U₁⟩
        have hx1 : x u' = 1 := by simpa using h3
        exact hu'1 (x.injective (by rw [hx1, map_one]))
      · exfalso
        have hdU₀' : v * (x v) ∈ U₀ := h1 ▸ hdU₀
        have hprod : v * (x v) = (u * x u) * (u' * x u') := by
          change (u * u') * x (u * u') = (u * x u) * (u' * x u')
          rw [map_mul]; ac_rfl
        have hu'xu'U₀ : u' * x u' ∈ U₀ := by
          have h2 : u' * x u' = (u * x u)⁻¹ * (v * (x v)) := by
            rw [hprod, inv_mul_cancel_left]
          rw [h2]
          exact U₀.mul_mem (U₀.inv_mem (U₀.mul_mem huU₀ (h₀.2.1 x hxX u huU₀))) hdU₀'
        have h3 : u' * x u' ∈ (⊥ : Subgroup W) := by
          rw [← hdisj]
          exact Subgroup.mem_inf.mpr ⟨hu'xu'U₀, U₁.mul_mem hu'U₁ (h₁.2.1 x hxX u' hu'U₁)⟩
        have h1' : u' * x u' = 1 := by simpa using h3
        have h2' : (u')⁻¹ = x u' := inv_eq_of_mul_eq_one_right h1'
        have h3' : (u')⁻¹ = u' := inv_eq_of_mul_eq_one_right (hW u')
        exact hu'1 (hfix₁ u' hu'U₁ (h2'.symm.trans h3'))
    have hAB' : ¬ U₀ ≤ D := by
      intro hle
      have hle' : U₀ ≤ D ⊓ U₀ := le_inf hle le_rfl
      rw [hDU₀] at hle'
      exact (not_le_of_gt h₀.1) hle'
    have hsec := secIsoOn_of_le_sup hW2 h₀ h₁ hDstab bot_le hAle hAB'
    exact ⟨hsec.2, hsec.1⟩

theorem s13_isoComps_eq_of_kerOn_eq (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hX : IsElemAbelian 3 X) {U U' : Subgroup W} (hU : U ∈ s13IsoComps X)
    (hU' : U' ∈ s13IsoComps X) (hker : s13KerOn X U = s13KerOn X U') : U = U' := by
  obtain ⟨U₀, h₀, hne₀, rfl⟩ := hU
  obtain ⟨U₁, h₁, hne₁, rfl⟩ := hU'
  have hker' : X ⊓ centSub U₀ = X ⊓ centSub U₁ := by
    simp only [s13KerOn] at hker
    rwa [w16g_inf_centSub_s13IsoSum_eq h₀, w16g_inf_centSub_s13IsoSum_eq h₁] at hker
  obtain ⟨hs1, hs2⟩ := w16g_secIsoOn_of_kerOn_eq hW hX h₀ h₁ hne₀ hne₁ hker'
  exact w16g_s13IsoSum_eq_of_secIsoOn hs2 hs1

end CFSG.LocalAnalysis.WeakClosure81

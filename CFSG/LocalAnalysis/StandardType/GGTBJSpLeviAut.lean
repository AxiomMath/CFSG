module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBShape
public import CFSG.LocalAnalysis.StandardType.GGTBJSpParabolicAut

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot TableBSymp SpCoord TypeBDatum Multiplicative
open CFSG.Open (StatedSp)

variable {p m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggTBJ_sp_automizer_fix_of_commute {ζ : Kˣ} (hζ : ζ ^ p = 1)
    {J : Subgroup (StatedSp m K)}
    (κ : (Fin m → Multiplicative (ZMod p)) ≃* (spTorusSp (m := m) hζ).range)
    (hκ : ∀ f, (κ f : StatedSp m K) = spTorusSp hζ f)
    {u : MulAut (Fin m → Multiplicative (ZMod p))}
    (hu : u ∈ (ggAutomizer J (spTorusSp (m := m) hζ).range).map
      (MulAut.congr κ.symm).toMonoidHom)
    {δ : Fin m → Multiplicative (ZMod p)}
    (hδ : ∀ j ∈ J, spTorusSp hζ δ * j = j * spTorusSp hζ δ) : u δ = δ := by
  obtain ⟨n, hn, hact⟩ := (mem_map_congr_ggAutomizer_iff _ J κ u).mp hu
  apply κ.injective
  apply Subtype.ext
  have h := hact δ
  rw [hκ δ, hκ (u δ)] at h
  rw [hκ (u δ), hκ δ]
  calc spTorusSp hζ (u δ) = n * spTorusSp hζ δ * n⁻¹ := h.symm
    _ = spTorusSp hζ δ := by rw [← hδ n hn]; group

theorem ggTBJ_sp_zero_block_automizer_eq (hp : p.Prime)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (t : Fin m → Kˣ)
    {J : Subgroup (StatedSp m K)}
    (hperm : ∀ i k : Fin m, i ≠ k → t i = 1 → t k = 1 → permSp K (Equiv.swap i k) ∈ J)
    (hswap : ∀ i : Fin m, t i = 1 → spSwapSp i ∈ J)
    (hcentral : ∀ x : Fin m → Kˣ, (∀ i, t i = 1 → x i = 1) →
      ∀ j ∈ J, diagSp K m x * j = j * diagSp K m x)
    (Z : Finset (Fin m)) (hZ : ∀ i, i ∈ Z ↔ t i = 1)
    (κ : (Fin m → Multiplicative (ZMod p)) ≃* (spTorusSp (m := m) hζ).range)
    (hκ : ∀ f, (κ f : StatedSp m K) = spTorusSp hζ f) :
    (ggAutomizer J (spTorusSp (m := m) hζ).range).map (MulAut.congr κ.symm).toMonoidHom =
      signedSupportedAut m p Z := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply le_antisymm
  · intro u hu
    refine mem_signedSupportedAut_of_fix hp
      (mem_signedAut_of_isSignedPerm (ggTBJ_sp_torus_automizer_signed hp hζo hζ J κ hκ hu)) Z
      fun j hj => ?_
    have htj : t j ≠ 1 := fun h => hj ((hZ j).mpr h)
    refine ggTBJ_sp_automizer_fix_of_commute hζ κ hκ hu fun n hn => ?_
    have hx : ∀ i, t i = 1 →
        zmodPowHom hζ ((Pi.mulSingle j (ofAdd (1 : ZMod p)) :
          Fin m → Multiplicative (ZMod p)) i) = 1 := by
      intro i hi
      have hij : i ≠ j := fun h => htj (h ▸ hi)
      simp [Pi.mulSingle_eq_of_ne hij]
    simpa only [ggTBJSpC_spTorusSp_eq_diagSp hζ] using hcentral _ hx n hn
  · apply signedSupportedAut_le
    · intro i hi
      have hti : t i = 1 := (hZ i).mp hi
      refine (mem_map_congr_ggAutomizer_iff _ J κ (sgnAut i)).mpr ⟨spSwapSp i, hswap i hti, ?_⟩
      intro f
      rw [hκ f, hκ (sgnAut i f)]
      exact ggTBJSpC_conj_spSwapSp hζ i f
    · intro a ha b hb hab
      have hta : t a = 1 := (hZ a).mp ha
      have htb : t b = 1 := (hZ b).mp hb
      refine (mem_map_congr_ggAutomizer_iff _ J κ (permAut (Equiv.swap a b))).mpr
        ⟨permSp K (Equiv.swap a b), hperm a b hab hta htb, ?_⟩
      intro f
      rw [hκ f, hκ (permAut (Equiv.swap a b) f)]
      exact ggTBJSpC_conj_permSp hζ (Equiv.swap a b) f

theorem ggTBJ_sp_class_block_automizer_eq (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (t : Fin m → Kˣ)
    {J : Subgroup (StatedSp m K)} {lam : Kˣ} (hlam : lam ≠ 1)
    (hperm : ∀ i k : Fin m, i ≠ k → t i = t k → (t i = lam ∨ t i = lam⁻¹) →
      permSp K (Equiv.swap i k) ∈ J)
    (hmixed : ∀ i k : Fin m, t i = lam → t k = lam⁻¹ → lam ≠ 1 →
      spSwapSp i * spSwapSp k * permSp K (Equiv.swap i k) ∈ J)
    (hcentral : ∀ x : Fin m → Kˣ,
      (∃ c : Kˣ, ∀ i, (t i = lam → x i = c) ∧ (t i = lam⁻¹ → x i = c⁻¹)) →
      ∀ j ∈ J, diagSp K m x * j = j * diagSp K m x)
    (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1)
    (hspos : ∀ i, t i ≠ lam⁻¹ → s i = 1) (hsneg : ∀ i, t i = lam⁻¹ → s i = -1)
    (S : Finset (Fin m)) (hS : ∀ i, i ∈ S ↔ (t i = lam ∨ t i = lam⁻¹))
    (κ : (Fin m → Multiplicative (ZMod p)) ≃* (spTorusSp (m := m) hζ).range)
    (hκ : ∀ f, (κ f : StatedSp m K) = spTorusSp hζ f) :
    (ggAutomizer J (spTorusSp (m := m) hζ).range).map (MulAut.congr κ.symm).toMonoidHom =
      twistedPermAut m p S s hs := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hlamInv : lam ≠ lam⁻¹ := by
    intro h
    have hsq : lam * lam = 1 :=
      (congrArg (fun z : Kˣ => z * lam) h).trans (inv_mul_cancel lam)
    have hsq' : (lam : K) ^ 2 = 1 := by
      simpa [pow_two] using congrArg (fun z : Kˣ => (z : K)) hsq
    have hzero : ((lam : K) - 1) * ((lam : K) - 1) = 0 := by
      have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination hsq' - ((lam : K) - 1) * htwo
    exact hlam (Units.ext (sub_eq_zero.mp ((mul_eq_zero.mp hzero).elim id id)))
  have hsgn : ∀ i, s i = 1 ∨ s i = -1 := by
    intro i
    by_cases hi : t i = lam⁻¹
    · exact Or.inr (hsneg i hi)
    · exact Or.inl (hspos i hi)
  have hone_ne : (1 : ZMod p) ≠ -1 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := by linear_combination h
    exact coord_two_ne_zero hp hp2 h2
  have hst : ∀ a b : Fin m, (t a = lam ∨ t a = lam⁻¹) → (t b = lam ∨ t b = lam⁻¹) →
      (s a = s b ↔ t a = t b) := by
    intro a b ha hb
    constructor
    · intro h
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact ha.trans hb.symm
      · exfalso
        have h1 : s a = 1 := hspos a (by rw [ha]; exact hlamInv)
        have h2 : s b = -1 := hsneg b hb
        exact hone_ne (h1.symm.trans (h.trans h2))
      · exfalso
        have h1 : s a = -1 := hsneg a ha
        have h2 : s b = 1 := hspos b (by rw [hb]; exact hlamInv)
        exact hone_ne (h2.symm.trans (h.symm.trans h1))
      · exact ha.trans hb.symm
    · intro h
      by_cases ha' : t a = lam⁻¹
      · rw [hsneg a ha', hsneg b (h.symm.trans ha')]
      · rw [hspos a ha', hspos b (fun hb => ha' (h.trans hb))]
  apply le_antisymm
  · intro u hu
    refine mem_twistedPermAut_of_fix hp
      (mem_signedAut_of_isSignedPerm (ggTBJ_sp_torus_automizer_signed hp hζo hζ J κ hκ hu)) S s hs
      hsgn (fun j hj => ?_) ?_
    ·
      have htj : ¬ (t j = lam ∨ t j = lam⁻¹) := fun h => hj ((hS j).mpr h)
      refine ggTBJ_sp_automizer_fix_of_commute hζ κ hκ hu fun n hn => ?_
      have hx : ∃ c : Kˣ, ∀ i, (t i = lam → zmodPowHom hζ ((Pi.mulSingle j (ofAdd (1 : ZMod p)) :
          Fin m → Multiplicative (ZMod p)) i) = c) ∧
          (t i = lam⁻¹ → zmodPowHom hζ ((Pi.mulSingle j (ofAdd (1 : ZMod p)) :
            Fin m → Multiplicative (ZMod p)) i) = c⁻¹) := by
        refine ⟨1, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
        · have hij : i ≠ j := fun h => htj (Or.inl (h ▸ hi))
          simp [Pi.mulSingle_eq_of_ne hij]
        · have hij : i ≠ j := fun h => htj (Or.inr (h ▸ hi))
          simp [Pi.mulSingle_eq_of_ne hij]
      simpa only [ggTBJSpC_spTorusSp_eq_diagSp hζ] using hcentral _ hx n hn
    ·
      refine ggTBJ_sp_automizer_fix_of_commute hζ κ hκ hu fun n hn => ?_
      let c : Kˣ := zmodPowHom hζ (ofAdd (1 : ZMod p))
      have hx : ∃ c' : Kˣ, ∀ i, (t i = lam → zmodPowHom hζ
          ((fun i => if i ∈ S then ofAdd (s i) else 1 : Fin m → Multiplicative (ZMod p)) i) =
            c') ∧
          (t i = lam⁻¹ → zmodPowHom hζ
          ((fun i => if i ∈ S then ofAdd (s i) else 1 : Fin m → Multiplicative (ZMod p)) i) =
            c'⁻¹) := by
        refine ⟨c, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
        · have hmem : i ∈ S := (hS i).mpr (Or.inl hi)
          simp only [hmem, if_true, hspos i (by rw [hi]; exact hlamInv), c]
        · have hmem : i ∈ S := (hS i).mpr (Or.inr hi)
          simp only [hmem, if_true, hsneg i hi, c, ← map_inv, ofAdd_neg]
      simpa only [ggTBJSpC_spTorusSp_eq_diagSp hζ] using hcentral _ hx n hn
  · apply twistedPermAut_le
    intro a ha b hb hab
    have hta : t a = lam ∨ t a = lam⁻¹ := (hS a).mp ha
    have htb : t b = lam ∨ t b = lam⁻¹ := (hS b).mp hb
    have hconj : diagAut s hs * permAut (Equiv.swap a b) * (diagAut s hs)⁻¹ =
        ggTBJSpC_reflAut p m t a b := by
      have h := ggTBJSpC_diagAut_conj_reflAut (p := p) s (1 : ZMod p) (-1) s hsgn hsgn
        (fun i => ⟨id, id⟩) hab
      rw [h]
      by_cases hab' : t a = t b
      · rw [ggTBJSpC_reflAut, ggTBJSpC_reflAut, if_pos ((hst a b hta htb).mpr hab'),
          if_pos hab']
      · rw [ggTBJSpC_reflAut, ggTBJSpC_reflAut, if_neg (fun h => hab' ((hst a b hta htb).mp h)),
          if_neg hab']
    rw [hconj]
    refine (mem_map_congr_ggAutomizer_iff _ J κ (ggTBJSpC_reflAut p m t a b)).mpr
      ⟨ggTBJSpC_reflElt t a b, ggTBJSpC_reflElt_mem_of_paired hlam hperm hmixed hta htb hab, ?_⟩
    intro f
    rw [hκ f, hκ (ggTBJSpC_reflAut p m t a b f)]
    by_cases h : t a = t b
    · exact ggTBJSpC_reflElt_conj_same hζ h f
    · exact ggTBJSpC_reflElt_conj_mixed hζ h f

end CFSG.StandardType

end

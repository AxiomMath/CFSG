module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFDefs
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Main
import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFLift
import CFSG.LocalAnalysis.StandardType.ZS.H3Recognition
import CFSG.LocalAnalysis.StandardType.ZS.J34Recognition
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableDegThree
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsTransport
import CFSG.LocalAnalysis.StandardType.ZS.TableWeyl
import CFSG.LocalAnalysis.StandardType.ZS.WeylModule
import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases

public section

namespace CFSG.StandardType.ZS

private lemma dMax_eq_of_dmax {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} {d e : ℕ}
    (h1 : DMax p A d) (h2 : DMax p A e) : d = e := by
  have hle : e ≤ d := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hord⟩ := h2.2
    rw [← hord]
    exact h1.1 x hx y hy hxr hyr
  have hle' : d ≤ e := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hord⟩ := h1.2
    rw [← hord]
    exact h2.1 x hx y hy hxr hyr
  omega

private lemma h3_model_of_h3ExcData {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] [Module.Finite (ZMod p) W] {X : Subgroup (W ≃ₗ[ZMod p] W)} {d : ℕ}
    (hp2 : p ≠ 2) (hW : Module.finrank (ZMod p) W = 4) (hsplit : SplitSupport X 3)
    (hDmax : DMax p X d)
    (hH3 : DimThree.ExcData p .H3 (movedGroup X) ∧ (p % 10 = 1 ∨ p % 10 = 9) ∧
      (∀ g ∈ movedGroup X, ∃ k ∈ movedGroup X, k * g * k⁻¹ = g⁻¹) ∧
      H3Frame p (movedGroup X)) :
    d = 5 ∧ p ≠ 5 ∧ ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W),
      α ^ 2 = α + 1 ∧ X = basisClosure f (h3Mats α) := by
  obtain ⟨hdata, hp10, -, hframe⟩ := hH3
  obtain ⟨-, -, hcard, -, hdmax, -⟩ := hdata
  have hcardY : Nat.card (movedGroup X) = 120 := by simpa [ExcRow.ord] using hcard
  have hcardX : Nat.card X = 120 := by
    rw [← card_movedGroup_of_splitSupport hsplit]; exact hcardY
  have hp5 : p ≠ 5 := by rintro rfl; norm_num at hp10
  have hd5 : d = 5 := by
    have := dMax_eq_of_dmax ((dmax_movedGroup_iff hsplit d).mpr hDmax) hdmax
    simpa [ExcRow.dmax] using this
  obtain ⟨α, f, hα, hXeq⟩ :=
    exists_basis_eq_h3Mats_of_h3Frame hp2 hp5 hW hsplit hcardX
      (H3Frame.of_movedGroup hsplit hframe)
  exact ⟨hd5, hp5, α, f, hα, hXeq⟩

private lemma j34_model_of_j34ExcData {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] [Module.Finite (ZMod p) W] {X : Subgroup (W ≃ₗ[ZMod p] W)} {d : ℕ}
    (hp2 : p ≠ 2) (hW : Module.finrank (ZMod p) W = 4) (hsplit : SplitSupport X 3)
    (hDmax : DMax p X d) (hdata : DimThree.ExcData p .J34 (movedGroup X))
    (hframe : J34Frame p (movedGroup X)) :
    d = 4 ∧ p ≠ 7 ∧ ∃ (β : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W),
      2 * β ^ 2 + β + 1 = 0 ∧ X = basisClosure f (j34Mats β) := by
  obtain ⟨hadm, -, hcard, -, hdmax, -⟩ := hdata
  have hcardY : Nat.card (movedGroup X) = 336 := by simpa [ExcRow.ord] using hcard
  have hcardX : Nat.card X = 336 := by
    rw [← card_movedGroup_of_splitSupport hsplit]; exact hcardY
  have hp7 : p ≠ 7 := by simpa [ExcRow.admissible] using hadm
  have hd4 : d = 4 := by
    have := dMax_eq_of_dmax ((dmax_movedGroup_iff hsplit d).mpr hDmax) hdmax
    simpa [ExcRow.dmax] using this
  obtain ⟨β, f, hβ, hXeq⟩ :=
    exists_basis_eq_j34Mats_of_j34Frame hp2 hW hsplit hcardX
      (J34Frame.of_movedGroup hsplit hframe)
  exact ⟨hd4, hp7, β, f, hβ, hXeq⟩

private lemma false_of_j35ExcData {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] [Module.Finite (ZMod p) W] {X : Subgroup (W ≃ₗ[ZMod p] W)} {l : ℕ}
    (hIY : AbsIrred p (movedGroup X)) (hsplit : SplitSupport X l)
    (hcen : ∀ z ∈ X, (∀ x ∈ X, z * x = x * z) → orderOf z ≤ 3)
    (hJ35 : DimThree.ExcData p .J35 (movedGroup X)) : False := by
  obtain ⟨-, -, -, hcen6, -, -⟩ := hJ35
  have hcen6' : Nat.card (Subgroup.center (movedGroup X)) = 6 := by
    simpa [ExcRow.cen] using hcen6
  obtain ⟨z, hzY, hzc, hzord⟩ := exists_orderOf_eq_card_center_of_absIrred hIY
  rw [hcen6'] at hzord
  obtain ⟨z', hz'X, hz'c, hz'ord⟩ :=
    exists_central_orderOf_eq_of_movedGroup hsplit hzY hzc
  have hz3 := hcen z' hz'X hz'c
  omega

private theorem false_of_central_orderOf_four {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V]
    {X : Subgroup (V ≃ₗ[ZMod p] V)} {l : ℕ} (hs : SplitSupport X l)
    (hcen : ∀ z ∈ X, (∀ x ∈ X, z * x = x * z) → orderOf z ≤ 3)
    {z : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X}
    (hz : z ∈ movedGroup X) (hzc : ∀ x ∈ movedGroup X, z * x = x * z)
    (hzo : orderOf z = 4) : False := by
  obtain ⟨z', hz'X, hz'c, hz'o⟩ := exists_central_orderOf_eq_of_movedGroup hs hz hzc
  have hle := hcen z' hz'X hz'c
  omega

private theorem false_of_linWeyl_of_five_le {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {A : Subgroup (V ≃ₗ[ZMod p] V)} (hp : p ≠ 2)
    (h5 : 5 ≤ Module.finrank (ZMod p) V)
    (hirr : ∀ P : Submodule (ZMod p) V, (∀ a ∈ A, ∀ w ∈ P, a w ∈ P) → P = ⊥ ∨ P = ⊤)
    (htv : QTwoLin.TransvectionFree A)
    (hd : ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A) (h : LinWeyl p A) : False := by
  have h3 : 3 ≤ Module.finrank (ZMod p) V := by omega
  rcases isCartanModel_cases_of_linWeyl hp h3 hirr h with
    ⟨ℓ, hA, T, hT⟩ | ⟨ℓ, hℓ, hA⟩ | ⟨ℓ, hℓ, hA⟩ | hA | hA | hA | hA
  · obtain ⟨x, hx, y, hy, hrx, hry, hxy⟩ := hd
    exact absurd (orderOf_mul_le_three_of_typeA hp T hT hx hy hrx hry) (by omega)
  · exact hprim (isImprimitiveOnV_of_isCartanModel_B hp hℓ hA)
  · exact hprim (isImprimitiveOnV_of_isCartanModel_D hp hℓ hA)
  · obtain ⟨x, hx, y, hy, hrx, hry, hxy⟩ := hd
    exact absurd (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inl rfl) hA htv hx hy hrx hry)
      (by omega)
  · obtain ⟨x, hx, y, hy, hrx, hry, hxy⟩ := hd
    exact absurd
      (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inr (Or.inl rfl)) hA htv hx hy hrx hry)
      (by omega)
  · obtain ⟨x, hx, y, hy, hrx, hry, hxy⟩ := hd
    exact absurd
      (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inr (Or.inr rfl)) hA htv hx hy hrx hry)
      (by omega)
  · have hdet : ((CartanMatrix.F₄.det : ℤ) : ZMod p) ≠ 0 := by
      rw [CartanMatrix.F₄_det]; norm_num
    have hdim : Module.finrank (ZMod p) V = 4 := IsCartanModel.finrank_eq_card_of_det hA hdet
    omega

private theorem false_of_family_of_five_le {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W]
    [Module.Finite (ZMod p) W] {X : Subgroup (W ≃ₗ[ZMod p] W)} {l d : ℕ} (hp : p ≠ 2)
    (hU : UseInputAt l) (hl : 5 ≤ l) (hgen : ReflGen p X) (htv : QTwoLin.TransvectionFree X)
    (hs : SplitSupport X l) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X))
    (hnotOrth : ¬ IsOrthType p (movedGroup X)) (hDMax : DMax p X d) (hd : 3 < d) : False := by
  let _ : Module.Finite (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) :=
    Module.Finite.of_injective (HardMathSupport.Kantor79.commutatorSpace X).subtype
      (HardMathSupport.Kantor79.commutatorSpace X).subtype_injective
  have hfinV : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) = l :=
    hs.2.1
  have hdmaxA : DMax p (movedGroup X) d := (dmax_movedGroup_iff hs d).mpr hDMax
  have htvA : QTwoLin.TransvectionFree (movedGroup X) := transvectionFree_movedGroup hs htv
  have hdA : ∃ x ∈ movedGroup X, ∃ y ∈ movedGroup X,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hdmaxA.2
    exact ⟨x, hx, y, hy, hxr, hyr, by rw [hxy]; exact hd⟩
  have hfam : Family p (movedGroup X) := TableFacts.family_movedGroup hp hU hgen hs
  cases hfam with
  | weyl h =>
      exact false_of_linWeyl_of_five_le hp (by rw [hfinV]; exact hl)
        (absIrred_movedGroup hgen hs).1 htvA hdA hprim h
  | slpm hA =>
      exact (not_transvectionFree_of_mem_iff_det (by rw [hfinV]; omega) hA) htvA
  | orth Q hQ hJ => exact hnotOrth ⟨Q, hQ, Or.inl hJ⟩
  | orthClass Q c hQ hc hJ => exact hnotOrth ⟨Q, hQ, Or.inr ⟨c, hc, hJ⟩⟩
  | gmmn f i₀ i₁ ζ m hi hm hζ hA =>
      have hcard := Module.finrank_eq_card_basis f
      simp only [Fintype.card_fin] at hcard
      exact hprim (hA.symm ▸ isImprimitiveOnV_gmmn (b := f) (hn := by omega) i₀ i₁ ζ)
  | g2mmn f i₀ i₁ ζ m hi hm hζ hA =>
      have hcard := Module.finrank_eq_card_basis f
      simp only [Fintype.card_fin] at hcard
      exact hprim (hA.symm ▸ isImprimitiveOnV_g2mmn (b := f) (hn := by omega) i₀ i₁ ζ)
  | exc k hadm hdimK hcard hcK hdmaxK hone hmodel =>
      have hkd : k.dmax = 3 := by cases k <;> simp_all [ExcRow.deg, ExcRow.dmax] <;> omega
      have h3 : DMax p (movedGroup X) 3 := by rw [hkd] at hdmaxK; exact hdmaxK
      exact absurd (dMax_eq_of_dmax hdmaxA h3) (by omega)
  | h4 hp5 hdim4 hcard hneg hdmax5 hone =>
      have : l = 4 := by rw [← hfinV, hdim4]
      omega

theorem tfPrimCorankOne_three
    {p : ℕ} [Fact p.Prime] : TFPrimCorankOne p 3 := by
  intro W _ _ _ X d hp2 _ hW hR hTF hsplit hprim horth hcen hDmax _
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let _ : Module.Finite (ZMod p) V := Module.Finite.of_injective V.subtype V.subtype_injective
  have hRY : ReflGen p (movedGroup X) := reflGen_movedGroup hR
  have hIY : AbsIrred p (movedGroup X) := absIrred_movedGroup hR hsplit
  have hTFY : QTwoLin.TransvectionFree (movedGroup X) :=
    transvectionFree_movedGroup hsplit hTF
  have h3 : Module.finrank (ZMod p) V = 3 := hsplit.2.1
  rcases DimThree.rows_of_finrank_eq_three hp2 h3 hRY hIY hprim with
      hSL | hOrth | hH3 | hJ34 | hJ35
  · exact (not_transvectionFree_of_mem_iff_det (by rw [h3]; norm_num) hSL hTFY).elim
  · exact (horth hOrth).elim
  · obtain ⟨hd5, hp5, α, f, hα, hXeq⟩ := h3_model_of_h3ExcData hp2 hW hsplit hDmax hH3
    exact Or.inl ⟨rfl, hd5, hp5, α, f, hα, hXeq⟩
  · obtain ⟨hdata, hframe⟩ := hJ34
    obtain ⟨hd4, hp7, β, f, hβ, hXeq⟩ := j34_model_of_j34ExcData hp2 hW hsplit hDmax hdata hframe
    exact Or.inr (Or.inl ⟨rfl, hd4, hp7, β, f, hβ, hXeq⟩)
  · obtain ⟨hdata, -⟩ := hJ35
    exact (false_of_j35ExcData hIY hsplit hcen hdata).elim

theorem tfPrimCorankOne_four {p : ℕ} [Fact p.Prime] (hL : DLargeFourModel p) :
    TFPrimCorankOne p 4 := by
  intro W _ _ _ X d hp h3l hdim hgen htv hs hprim hnotOrth hcen hDMax hd
  let _ : Module.Finite (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) :=
    Module.Finite.of_injective (HardMathSupport.Kantor79.commutatorSpace X).subtype
      (HardMathSupport.Kantor79.commutatorSpace X).subtype_injective
  have hpairX : ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hDMax.2
    exact ⟨x, hx, y, hy, hxr, hyr, by rw [hxy]; exact hd⟩
  have hpair : ∃ x ∈ movedGroup X, ∃ y ∈ movedGroup X,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) :=
    (TableFacts.exists_pair_movedGroup_iff hs (fun k => 3 < k)).mpr hpairX
  have hDMaxA : DMax p (movedGroup X) d := (dmax_movedGroup_iff hs d).mpr hDMax
  have hres := hL (HardMathSupport.Kantor79.commutatorSpace X) (movedGroup X) hp hs.2.1
    (reflGen_movedGroup hgen) (absIrred_movedGroup hgen hs) hprim
    (transvectionFree_movedGroup hs htv) hpair
  rcases hres with horth | hN4EN4 | hF4c | hH4c
  · exfalso
    exact hnotOrth horth
  · exfalso
    obtain ⟨hd4, f, t, ht2, hN4EN4⟩ := hN4EN4
    rcases hN4EN4 with hN4 | hEN4
    · obtain ⟨z, hz, hzc, hzo⟩ := exists_central_orderOf_four_basisClosure_weylN4Mats hp f ht2
      exact false_of_central_orderOf_four hs hcen (hN4.symm ▸ hz)
        (fun x hx => hzc x (hN4.symm ▸ hx)) hzo
    · obtain ⟨z, hz, hzc, hzo⟩ := exists_central_orderOf_four_basisClosure_weylEN4Mats hp f ht2
      exact false_of_central_orderOf_four hs hcen (hEN4.symm ▸ hz)
        (fun x hx => hzc x (hEN4.symm ▸ hx)) hzo
  · obtain ⟨hp3, hd4, f, hF4⟩ := hF4c
    refine Or.inr (Or.inr (Or.inr ⟨rfl, dMax_eq_of_dmax hDMaxA hd4, hp3, ?_⟩))
    obtain ⟨f', hf'⟩ := exists_basis_eq_basisClosure_blockSucc_of_movedGroup hs hdim hF4
    exact ⟨f', hf'⟩
  · obtain ⟨hp5, hd5, α, f, hα, hH4⟩ := hH4c
    refine Or.inr (Or.inr (Or.inl ⟨rfl, dMax_eq_of_dmax hDMaxA hd5, hp5, α, ?_⟩))
    obtain ⟨f', hf'⟩ := exists_basis_eq_basisClosure_blockSucc_of_movedGroup hs hdim hH4
    exact ⟨f', hα, hf'⟩

theorem tfPrimCorankOne_of_five_le {p : ℕ} [Fact p.Prime] {l : ℕ} (hl : 5 ≤ l)
    (hU : UseInputAt l) : TFPrimCorankOne p l := by
  intro W _ _ _ X d hp h3l hdim hgen htv hs hprim hnotOrth hcen hDMax hd
  exact (false_of_family_of_five_le hp hU hl hgen htv hs hprim hnotOrth hDMax hd).elim

end CFSG.StandardType.ZS

end

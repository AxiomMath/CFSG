module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthALRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

private lemma ct_nb4_not_g2_of_card_ne_two {κ : Type} [Fintype κ] {M : CoxeterMatrix κ}
    (h : Fintype.card κ ≠ 2) :
    ¬ ∃ e : Fin 2 ≃ κ, M = CoxeterMatrix.G₂.reindex e := by
  rintro ⟨e, -⟩
  exact h ((Fintype.card_congr e).symm.trans (Fintype.card_fin 2))

private lemma ct_nb4_A2_not_g2 :
    ¬ ∃ e : Fin 2 ≃ Fin 2, CoxeterMatrix.A 2 = CoxeterMatrix.G₂.reindex e := by
  rintro ⟨e, he⟩
  have h01 := congrArg (fun M : CoxeterMatrix (Fin 2) => M.M 0 1) he
  rw [CoxeterMatrix.reindex_apply] at h01
  have hA : (CoxeterMatrix.A 2).M 0 1 = 3 := by decide
  have hG : CoxeterMatrix.G₂.M (e.symm 0) (e.symm 1) = 6 := by
    generalize hx : (e.symm 0 : Fin 2) = x
    generalize hy : (e.symm 1 : Fin 2) = y
    have hxy : x ≠ y := by
      rw [← hx, ← hy]
      exact fun h => (by decide : (0 : Fin 2) ≠ 1) (e.symm.injective h)
    fin_cases x <;> fin_cases y <;> simp_all [CoxeterMatrix.G₂]
  rw [hA, hG] at h01
  exact (by decide : (3 : ℕ) ≠ 6) h01

private lemma ct_nb4_not_g2_A (n : ℕ) :
    ¬ ∃ e : Fin 2 ≃ Fin n, CoxeterMatrix.A n = CoxeterMatrix.G₂.reindex e := by
  rcases n with _ | _ | _ | n
  · exact ct_nb4_not_g2_of_card_ne_two (by rw [Fintype.card_fin]; omega)
  · exact ct_nb4_not_g2_of_card_ne_two (by rw [Fintype.card_fin]; omega)
  · exact ct_nb4_A2_not_g2
  · exact ct_nb4_not_g2_of_card_ne_two (by rw [Fintype.card_fin]; omega)

private lemma ct_nb4_le_three_A (n : ℕ) (i j : Fin n) (_hij : i ≠ j) :
    (CoxeterMatrix.A n).M i j ≤ 3 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

private lemma ct_nb4_le_three_D (n : ℕ) (i j : Fin n) (_hij : i ≠ j) :
    ggCoxeterMatrixD n i j ≤ 3 := by
  rw [ggCoxeterMatrixD_apply]
  split_ifs <;> omega

private lemma ct_nb4_le_three_E6 (i j : Fin 6) (hij : i ≠ j) :
    (CoxeterMatrix.E₆).M i j ≤ 3 := by
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆]

private lemma ct_nb4_le_three_E7 (i j : Fin 7) (hij : i ≠ j) :
    (CoxeterMatrix.E₇).M i j ≤ 3 := by
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₇]

private lemma ct_nb4_le_three_E8 (i j : Fin 8) (hij : i ≠ j) :
    (CoxeterMatrix.E₈).M i j ≤ 3 := by
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₈]

private theorem ct_nb4_join_contra
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    {ιV : Additive ↥Bs ≃+ V} {W : Subgroup (MulAut ↥Bs)}
    (hWleInd : W ≤ ggInduced ⊤ Bs) (hWleAInf : W ≤ ggAInf 3 B Bs x L D J)
    (hEA : IsElemAbelian 3 Bs) (hnoT : GGNoTransvection 3 Bs)
    (horth : ∀ g : V ≃ₗ[ZMod 3] V,
      (∃ a ∈ ggAInf 3 B Bs x L D J, ggLin (p := 3) ιV a = g) ↔ ∀ v, Q (g v) = Q v)
    {c₁ : ZMod 3} (hc₁ : c₁ ≠ 0) {a₀ s : MulAut ↥Bs}
    (ha₀W : a₀ ∈ W) (hsW : s ∈ W)
    (ha₀refl : GGIsReflection 3 a₀) (hsr : GGIsReflection 3 s)
    (ha₀ : OrthReflOfNorm Q c₁ (ggLin (p := 3) ιV a₀))
    (hsc : OrthReflOfNorm Q (-c₁) (ggLin (p := 3) ιV s))
    {κ : Type} {M : CoxeterMatrix κ} (hM : GGIsWeylMatrix M)
    (hnotG2 : ¬ ∃ e : Fin 2 ≃ κ, M = CoxeterMatrix.G₂.reindex e)
    (hle : ∀ i j : κ, i ≠ j → M.M i j ≤ 3)
    (hT : GGWeylOfType 3 M W) : False := by
  obtain ⟨e, he⟩ := hT
  have hroot : ∀ a : ↥W, GGIsReflection 3 (a : MulAut ↥Bs) →
      ∃ (i : κ) (g : M.Group), a = e (g * M.simple i * g⁻¹) :=
    CFSG.StandardType.SecFiveRootRefl.ggSecFiveRootReflInput_holds G 3 Bs
      Nat.prime_three (by decide) hEA hnoT W hWleInd κ M hM hnotG2 e he
  obtain ⟨i, g, hi⟩ := hroot ⟨a₀, ha₀W⟩ ha₀refl
  obtain ⟨j, h, hj⟩ := hroot ⟨s, hsW⟩ hsr
  obtain ⟨k, hk⟩ := ggOrth_simple_conj M hM hle i j
  let w : MulAut ↥Bs := (e (h * k * g⁻¹) : ↥W)
  have hwAInf : w ∈ ggAInf 3 B Bs x L D J := hWleAInf (e (h * k * g⁻¹)).2
  have horth_w : ggLin (p := 3) ιV w ∈ QuadraticMap.orthogonalGroup Q := by
    rw [QuadraticMap.mem_orthogonalGroup_iff]
    exact (horth (ggLin (p := 3) ιV w)).mp ⟨w, hwAInf, rfl⟩
  have hconj : OrthReflOfNorm Q c₁
      (ggLin (p := 3) ιV w * ggLin (p := 3) ιV a₀ * (ggLin (p := 3) ιV w)⁻¹) :=
    OrthReflOfNorm.conj ha₀ (ggLin (p := 3) ιV w) horth_w
  have hw_eq : s = w * a₀ * w⁻¹ := by
    have hj' : s = (e (h * M.simple j * h⁻¹) : MulAut ↥Bs) := congrArg Subtype.val hj
    have hi' : a₀ = (e (g * M.simple i * g⁻¹) : MulAut ↥Bs) := congrArg Subtype.val hi
    rw [hj', hi']
    show (e (h * M.simple j * h⁻¹) : MulAut ↥Bs) =
      (e (h * k * g⁻¹) : MulAut ↥Bs) * (e (g * M.simple i * g⁻¹) : MulAut ↥Bs) *
        (e (h * k * g⁻¹) : MulAut ↥Bs)⁻¹
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hk]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hlin : ggLin (p := 3) ιV s =
      ggLin (p := 3) ιV w * ggLin (p := 3) ιV a₀ * (ggLin (p := 3) ιV w)⁻¹ := by
    have h := congrArg (ggLin (p := 3) ιV) hw_eq
    rw [map_mul, map_mul, map_inv] at h
    exact h
  have hconj' : OrthReflOfNorm Q c₁ (ggLin (p := 3) ιV s) := by
    rw [hlin]
    exact hconj
  have hc : c₁ = -c₁ := orthReflOfNorm_unique hconj' hsc
  have h2 : (2 : ZMod 3) * c₁ = 0 := by
    have h3 : c₁ + c₁ = 0 := by
      nth_rewrite 2 [hc]
      abel
    rwa [two_mul]
  exact hc₁ ((mul_eq_zero.mp h2).resolve_left (by decide))

theorem ggOrthNbr_join
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) {c₁ : ZMod 3} (hc₁ : c₁ ≠ 0)
    (hL : ∀ a ∈ ggAutomizer L Bs, GGIsReflection 3 a → OrthReflOfNorm Q c₁ (ggLin (p := 3) ι a))
    (hexL : ∃ a ∈ ggAutomizer L Bs, GGIsReflection 3 a)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) {s : MulAut ↥Bs} (hs : s ∈ ggAutomizer K Bs)
    (hsr : GGIsReflection 3 s) (hsc : OrthReflOfNorm Q (-c₁) (ggLin (p := 3) ι s)) :
    (∃ n : ℕ, 2 ≤ n ∧ GGWeylOfType 3 (CoxeterMatrix.B n) (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) ∨
      GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∨
      GGWeylOfType 3 CoxeterMatrix.G₂ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hR : GGSecFiveRestHyp 3 B Bs x L D J := S.cfg.1
  have hWC : GGSecFiveWeylCase' 3 B Bs x D J := S.cfg.2.1
  have hEA : IsElemAbelian 3 Bs := hR.1.2.1.2.1
  have hnoT : GGNoTransvection 3 Bs := hR.2.2.2.1
  have hWeyl : GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    hR.2.2.2.2.1 y K hnb (hWC y K hnb) (Or.inr hWC)
  obtain ⟨a₀, ha₀L, ha₀refl⟩ := hexL
  have ha₀ : OrthReflOfNorm Q c₁ (ggLin (p := 3) ι a₀) := hL a₀ ha₀L ha₀refl
  have ha₀W : a₀ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := Subgroup.mem_sup_left ha₀L
  have hsW : s ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := Subgroup.mem_sup_right hs
  have hWleInd : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hWleAInf : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAInf 3 B Bs x L D J := by
    refine sup_le le_sup_left ?_
    show ggAutomizer K Bs ≤ ggAutomizer L Bs ⊔
      ⨆ (y : G) (K : Subgroup G) (_ : GGNbr 3 B x D J y K), ggAutomizer K Bs
    exact ((le_iSup (fun _ : GGNbr 3 B x D J y K => ggAutomizer K Bs) hnb).trans
      (le_iSup₂ (f := fun (y : G) (K : Subgroup G) =>
        ⨆ (_ : GGNbr 3 B x D J y K), ggAutomizer K Bs) y K)).trans le_sup_right
  rcases ggWeylReflectionGroup_cases hWeyl with hA | hB | hD | hE6 | hE7 | hE8 | hF4 | hG2
  · obtain ⟨n, hn, hT⟩ := hA
    exact False.elim (ct_nb4_join_contra hWleInd hWleAInf hEA hnoT S.orth hc₁ ha₀W hsW
      ha₀refl hsr ha₀ hsc (Or.inl ⟨n, Equiv.refl _, hn, Or.inl (by
        ext i j; simp [CoxeterMatrix.reindex_apply])⟩) (ct_nb4_not_g2_A n)
      (ct_nb4_le_three_A n) hT)
  · obtain ⟨n, hn, hT⟩ := hB
    exact Or.inl ⟨n, hn, hT⟩
  · obtain ⟨n, hn, hT⟩ := hD
    exact False.elim (ct_nb4_join_contra hWleInd hWleAInf hEA hnoT S.orth hc₁ ha₀W hsW
      ha₀refl hsr ha₀ hsc (Or.inl ⟨n, Equiv.refl _, by omega, Or.inr (Or.inr ⟨hn, by
        ext i j; simp [CoxeterMatrix.reindex_apply]⟩)⟩) 
      (ct_nb4_not_g2_of_card_ne_two (by rw [Fintype.card_fin]; omega))
      (ct_nb4_le_three_D n) hT)
  · exact False.elim (ct_nb4_join_contra hWleInd hWleAInf hEA hnoT S.orth hc₁ ha₀W hsW
      ha₀refl hsr ha₀ hsc (Or.inr (Or.inl ⟨Equiv.refl _, by
        ext i j; simp [CoxeterMatrix.reindex_apply]⟩))
      (ct_nb4_not_g2_of_card_ne_two (by rw [Fintype.card_fin]; decide))
      ct_nb4_le_three_E6 hE6)
  · exact False.elim (ct_nb4_join_contra hWleInd hWleAInf hEA hnoT S.orth hc₁ ha₀W hsW
      ha₀refl hsr ha₀ hsc (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, by
        ext i j; simp [CoxeterMatrix.reindex_apply]⟩)))
      (ct_nb4_not_g2_of_card_ne_two (by rw [Fintype.card_fin]; decide))
      ct_nb4_le_three_E7 hE7)
  · exact False.elim (ct_nb4_join_contra hWleInd hWleAInf hEA hnoT S.orth hc₁ ha₀W hsW
      ha₀refl hsr ha₀ hsc (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, by
        ext i j; simp [CoxeterMatrix.reindex_apply]⟩))))
      (ct_nb4_not_g2_of_card_ne_two (by rw [Fintype.card_fin]; decide))
      ct_nb4_le_three_E8 hE8)
  · exact Or.inr (Or.inl hF4)
  · exact Or.inr (Or.inr hG2)

end CFSG.StandardType.OrthF3

end

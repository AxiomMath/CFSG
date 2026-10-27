module

public import CFSG.Timmesfeld.ARS.CaseHRankOne
public import CFSG.Timmesfeld.ARS.FrameSL3

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

theorem conjSub_centralizer (H : Subgroup G) (g : G) :
    conjSub (Subgroup.centralizer (H : Set G)) g =
      Subgroup.centralizer ((conjSub H g : Subgroup G) : Set G) := by
  have key : ∀ (K : Subgroup G) (x : G), conjSub (Subgroup.centralizer (K : Set G)) x ≤
      Subgroup.centralizer ((conjSub K x : Subgroup G) : Set G) := fun K x => by
    have := Subgroup.map_centralizer_le_centralizer_image (K : Set G) (MulAut.conj x).toMonoidHom
    rwa [← Subgroup.coe_map] at this
  refine le_antisymm (key H g) ?_
  have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (key (conjSub H g) g⁻¹)
  change conjSub (conjSub (Subgroup.centralizer ((conjSub H g : Subgroup G) : Set G)) g⁻¹) g ≤
    conjSub (Subgroup.centralizer ((conjSub (conjSub H g) g⁻¹ : Subgroup G) : Set G)) g at this
  rwa [Plane.conjSub_inv_conjSub, Plane.conjSub_conjSub_inv] at this

theorem conjSub_shortRoot' (hR : IsRootClass R) (X Y Z : Subgroup G) (g : G) :
    conjSub (shortRoot R X Y Z) g = shortRoot R (conjSub X g) (conjSub Y g) (conjSub Z g) := by
  change Subgroup.map _ (_ ⊓ _) = _
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective]
  change conjSub _ g ⊓ conjSub (M R Z) g = _
  rw [conjSub_centralizer, Sec5.conjSub_M hR]
  change Subgroup.centralizer (((X ⊔ Y).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ⊓
    M R (conjSub Z g) = _
  rw [Subgroup.map_sup]

section Apartment

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

theorem apartment {A A₀ P P' : Subgroup G} (hA : A ∈ R) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') :
    ⁅A₀, P⁆ ∈ lambdaSet R P ∧ ⁅A₀, P⁆ ∈ lambdaSet R A₀ ∧
      ⁅A₀, P'⁆ ∈ lambdaSet R P' ∧ ⁅A₀, P'⁆ ∈ lambdaSet R A₀ ∧
      (Special R P P' ∧ ⁅P, P'⁆ = A) ∧ (Special R A ⁅A₀, P⁆ ∧ ⁅A, ⁅A₀, P⁆⁆ = P) ∧
      (Special R A ⁅A₀, P'⁆ ∧ ⁅A, ⁅A₀, P'⁆⁆ = P') ∧
      (Special R ⁅A₀, P'⁆ ⁅A₀, P⁆ ∧ ⁅⁅A₀, P'⁆, ⁅A₀, P⁆⁆ = A₀) ∧
      ⁅A₀, P'⁆ ∈ omegaSet R P ∧ ⁅A₀, P⁆ ∈ omegaSet R P' := by
  have := h.finite
  have hR := h.root
  have hA₀R : A₀ ∈ R := hA₀.1
  have hop : Opposite A A₀ := hA₀.2
  have hPR : P ∈ R := hP.2.1
  have hP'R : P' ∈ R := hP'.2.1
  obtain ⟨hQA₀, hQP⟩ := commutator_mem_lambdaSet h hA₀R hPR hP.2.2
  obtain ⟨hQ'A₀, hQ'P'⟩ := commutator_mem_lambdaSet h hA₀R hP'R hP'.2.2
  have hnotle : ¬ P' ≤ A ⊔ P := fun hle => hPP' (eq_of_mem_lambdaStar_of_le h hA hA₀ hP hP' hle).symm
  have hnotle' : ¬ P ≤ A ⊔ P' := fun hle => hPP' (eq_of_mem_lambdaStar_of_le h hA hA₀ hP' hP hle)
  have hQ'Ω := commutator_mem_omegaSet h hH hA hA₀ hP hP' hnotle
  have hQΩ := commutator_mem_omegaSet h hH hA hA₀ hP' hP hnotle'
  have hfar : ∀ {X : Subgroup G}, X ∈ lambdaSet R A₀ → X ∉ lambdaSet R A ∧ X ≠ A := by
    intro X hX
    refine ⟨fun hXA => notMem_lambdaSet_of_opposite h hA hop hXA hX, ?_⟩
    rintro rfl
    exact hop.not_commuting (hR.ne_bot X hX.1.1) hX.1.2.2.symm
  have hPP'nc : ¬ Commuting P P' := fun hc => hnotle (le_line h hH hA hP.1 hA le_sup_left hPR
    le_sup_right hP.1.1.2.1.symm hP'R hP'.1.1.2.2.symm hc.symm)
  have hQQ'nc : ¬ Commuting ⁅A₀, P'⁆ ⁅A₀, P⁆ := by
    intro hc
    have hne : ⁅A₀, P⁆ ≠ ⁅A₀, P'⁆ := by
      intro e
      apply hQ'Ω.2.not_commuting (hR.ne_bot P hPR)
      rw [← e]
      exact hQP.1.2.2
    have hl := mem_lambdaSet_of_commuting hH hQ'A₀.1.1 hQA₀.1.1 hne hc
    exact notMem_lambdaSet_of_opposite h hPR hQ'Ω.2 hQP hl
  refine ⟨hQP, hQA₀, hQ'P', hQ'A₀, special_of_mem_lambdaSet_of_mem_lambdaSet h hA hP.1 hP'.1 hPP'nc,
    special_of_mem_lambdaSet h hH hA hP.1 hQP (hfar hQA₀).1 (hfar hQA₀).2,
    special_of_mem_lambdaSet h hH hA hP'.1 hQ'P' (hfar hQ'A₀).1 (hfar hQ'A₀).2,
    special_of_mem_lambdaSet_of_mem_lambdaSet h hA₀R hQ'A₀ hQA₀ hQQ'nc, hQ'Ω, hQΩ⟩

theorem exists_hom_SL3_apartment {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀)
    (hPP' : P ≠ P') {n : ℕ} (hq : Nat.card A = 2 ^ n) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 n) →* G,
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup
        (Pi.single (α₁ (GaloisField 2 n)) 1)).map ψ = P ∧
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup
        (Pi.single (α₂ (GaloisField 2 n)) 1)).map ψ = P' ∧
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup (fun _ => 1)).map ψ = A ∧
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup
        (-Pi.single (α₁ (GaloisField 2 n)) 1)).map ψ = ⁅A₀, P'⁆ ∧
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup
        (-Pi.single (α₂ (GaloisField 2 n)) 1)).map ψ = ⁅A₀, P⁆ ∧
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup (-fun _ => 1)).map ψ = A₀ ∧
      ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 n)) := by
  have := h.finite
  have hR := h.root
  have hPR : P ∈ R := hP.2.1
  obtain ⟨hQP, -, hQ'P', -, ⟨hsPP', hcPP'⟩, ⟨-, hcAQ⟩, ⟨-, hcAQ'⟩, ⟨hsQ'Q, hcQ'Q⟩, hQ'Ω, hQΩ⟩ :=
    apartment h hH hA hA₀ hP hP' hPP'
  have h2 : ⁅⁅A₀, P'⁆, ⁅P, P'⁆⁆ = P' := by
    rw [hcPP', Subgroup.commutator_comm, hcAQ']
  have h4 : ⁅⁅P, P'⁆, ⁅A₀, P⁆⁆ = P := by
    rw [hcPP', hcAQ]
  obtain ⟨ψ, h1, h2', h3, h4', h5, h6, hker, -⟩ := exists_hom_SL3 hR h.noIsolated hPR
    hP'.2.1 hQ'Ω.1 hQΩ.1 hsPP' hQ'Ω.2 hQΩ.2 hQ'P'.1.2.2.symm h2 hQP.1.2.2 h4 hsQ'Q
    ((hR.card_eq hPR hA).trans hq)
  rw [hcPP'] at h3
  rw [hcQ'Q] at h6
  exact ⟨ψ, h1, h2', h3, h4', h5, h6, hker⟩

theorem shortRoot_eq_shortRoot (hT : MTransitive R) {X Y Z : Subgroup G} (hX : X ∈ R)
    (h3 : 3 ≤ (linesThrough R X).ncard) (hY : Y ∈ omegaSet R X) (hZ : Z ∈ lambdaStar R X Y) :
    shortRoot R X Y Z = shortRoot R Y X ⁅Y, Z⁆ := by
  have := h.finite
  have hR := h.root
  have hYR : Y ∈ R := hY.1
  have hop : Opposite X Y := hY.2
  have hXΩ : X ∈ omegaSet R Y := ⟨hX, hop.symm⟩
  have hZR : Z ∈ R := hZ.2.1
  obtain ⟨-, -, -, w, -, -, hwXY, hXw, hYw⟩ := Sec5.exists_swap hR hX hYR hop
  have hUw : conjSub (shortRoot R X Y Z) w = shortRoot R X Y Z :=
    conjSub_of_forall_commute fun u hu => Subgroup.mem_centralizer_iff.1 hu.1 w hwXY
  rw [conjSub_shortRoot' hR, hXw, hYw] at hUw
  have hYX : shortRoot R Y X (conjSub Z w) = shortRoot R X Y Z := hUw
  have hZw : conjSub Z w ∈ lambdaStar R Y X := by
    refine ⟨?_, hR.conjSub_mem hZR w, ?_⟩
    · have := conjSub_mem_lambdaSet hR hZ.1 w
      rwa [hXw] at this
    · have := Sec3.special_conjSub hR hZ.2.2 w
      rwa [hYw] at this
  obtain ⟨hZ'Y, hZ'Z⟩ := commutator_mem_lambdaSet h hYR hZR hZ.2.2
  have hZ'X : ⁅Y, Z⁆ ∉ lambdaSet R X := fun hl =>
    notMem_lambdaSet_of_opposite h hX hop hl hZ'Y
  have hZ'ne : ⁅Y, Z⁆ ≠ X := by
    intro e
    rw [e] at hZ'Y
    exact hop.not_commuting (hR.ne_bot X hX) hZ'Y.1.2.2.symm
  have hZ's : ⁅Y, Z⁆ ∈ lambdaStar R Y X :=
    ⟨hZ'Y, hZ'Y.1.1, (special_of_mem_lambdaSet h hH hX hZ.1 hZ'Z hZ'X hZ'ne).1⟩
  have hfix : ∀ u ∈ shortRoot R X Y Z, conjSub (Y ⊔ ⁅Y, Z⁆) u = Y ⊔ ⁅Y, Z⁆ := by
    intro u hu
    have huY := conjSub_right_of_mem_shortRoot hu
    have huZ := conjSub_self_of_mem_shortRoot h hZR hu
    change Subgroup.map _ (Y ⊔ ⁅Y, Z⁆) = _
    rw [Subgroup.map_sup, Subgroup.map_commutator]
    change conjSub Y u ⊔ ⁅conjSub Y u, conjSub Z u⁆ = _
    rw [huY, huZ]
  have hL : 3 ≤ (linesThrough R Y).ncard := (ncard_linesThrough_eq h hX hYR) ▸ h3
  by_cases heq : conjSub Z w = ⁅Y, Z⁆
  · rw [← hYX, heq]
  exfalso
  have hnle : ¬ conjSub Z w ≤ Y ⊔ ⁅Y, Z⁆ := fun hle =>
    heq (eq_of_mem_lambdaStar_of_le h hYR hXΩ hZ's hZw hle)
  have hV := sup_mem_linesThrough h hYR hZ's.1
  have hV' := sup_mem_linesThrough h hYR hZw.1
  have hVV' : Y ⊔ ⁅Y, Z⁆ ≠ Y ⊔ conjSub Z w := fun e => hnle (e ▸ le_sup_right)
  obtain ⟨W, hW, hWV, hWV'⟩ : ∃ W ∈ linesThrough R Y, W ≠ Y ⊔ ⁅Y, Z⁆ ∧ W ≠ Y ⊔ conjSub Z w := by
    by_contra hno
    push Not at hno
    have hsub : linesThrough R Y ⊆ {Y ⊔ ⁅Y, Z⁆, Y ⊔ conjSub Z w} := fun W hW => by
      by_cases hWV : W = Y ⊔ ⁅Y, Z⁆
      · exact Or.inl hWV
      · exact Or.inr (hno W hW hWV)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hVV'] at this
    omega
  have hPW : ¬ conjSub Z w ≤ W := fun hle => hWV' (eq_sup_of_le h hYR hZw.1 hW hle)
  obtain ⟨-, -, hreg⟩ := shortRoot_moufang_of h hH hT hYR hXΩ hZw
  obtain ⟨⟨u, hu⟩, hue, -⟩ := hreg (Y ⊔ ⁅Y, Z⁆) hV W hW hnle hPW
  have hu' : u ∈ shortRoot R X Y Z := hYX ▸ hu
  exact hWV (hue.symm.trans (hfix u hu'))

end Apartment

end CaseH

end CFSG.Timmesfeld.ARS

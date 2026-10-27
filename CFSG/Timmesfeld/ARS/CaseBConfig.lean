module

public import CFSG.Timmesfeld.ARS.CaseBLevi
public import CFSG.Timmesfeld.ARS.CaseD4Frame

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseB

theorem card_sup_eq_of_opposite [Finite G] (hR : IsRootClass R) {X Y X' Y' : Subgroup G}
    (hX : X ∈ R) (hXY : Opposite X Y) (hX' : X' ∈ R) (hXY' : Opposite X' Y') :
    Nat.card ↥(X ⊔ Y) = Nat.card ↥(X' ⊔ Y') := by
  obtain ⟨n, -, hn, φ, -⟩ := hXY.exists_mulEquiv_SL2' hR hX
  obtain ⟨n', -, hn', φ', -⟩ := hXY'.exists_mulEquiv_SL2' hR hX'
  have e : n = n' :=
    Nat.pow_right_injective le_rfl (hn.symm.trans ((hR.card_eq hX hX').trans hn'))
  subst e
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr φ'.toEquiv]

theorem commuting_of_le_normalizer [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {X Y : Subgroup G} (hX : X ∈ R) (hY : Y ∈ R) (hne : X ≠ Y)
    (hle : X ≤ Subgroup.normalizer (Y : Set G)) : Commuting X Y := by
  rcases hR.rel X hX Y hY hne with hc | ho | hs
  · exact hc
  · exfalso
    obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX
    obtain ⟨y, hy, -, hxy⟩ := ho.2.1 x hx hx1
    rw [conjSub_eq_self_iff.2 (hle hx)] at hxy
    apply hne
    calc X = conjSub (conjSub X y) y⁻¹ := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
      _ = Y := by
        rw [hxy]
        exact conjSub_eq_self_iff.2 (Subgroup.le_normalizer (Y.inv_mem hy))
  · exfalso
    have hZY : ⁅X, Y⁆ ≠ Y := fun e =>
      (hs.symm.ne_commutator hR) (by rw [Subgroup.commutator_comm, e])
    refine hs.not_commuting hR fun x hx y hy => ?_
    have h1 : ⁅x, y⁆ ∈ ⁅X, Y⁆ := Subgroup.commutator_mem_commutator hx hy
    have h2 : ⁅x, y⁆ ∈ Y := by
      rw [commutatorElement_def]
      exact Y.mul_mem ((Subgroup.mem_normalizer_iff.1 (hle hx) y).1 hy) (Y.inv_mem hy)
    have h3 : ⁅x, y⁆ ∈ ⁅X, Y⁆ ⊓ Y := ⟨h1, h2⟩
    rw [inf_eq_bot hR hiso hs.1 hY hZY, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3

section Levi

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (h8 : Sec8 R A)
  (hA₀ : A₀ ∈ omegaSet R A) {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ) (hAΔ : A ∈ Δ)
include h hA h8 hA₀ hΔ hAΔ

theorem levi_eq_sup_of_ne {B B' : Subgroup G} (hB : B ∈ leviSet R A A₀)
    (hB' : B' ∈ leviSet R A A₀) (hne : B ≠ B') : levi R A A₀ = B ⊔ B' := by
  have := h.finite
  obtain ⟨C, hC, D, hD, hCD, hV⟩ := exists_levi_eq_sup h hA h8 hA₀ hΔ hAΔ
  have hle : B ⊔ B' ≤ levi R A A₀ :=
    sup_le (le_iSup₂ (f := fun X (_ : X ∈ leviSet R A A₀) => X) B hB)
      (le_iSup₂ (f := fun X (_ : X ∈ leviSet R A A₀) => X) B' hB')
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hV, card_sup_eq_of_opposite h.root hC.1.1 hCD hB.1.1
    (opposite_of_mem_leviSet h hA h8 hA₀ hΔ hAΔ hB hB' hne)]

theorem exists_mem_levi_conjSub_eq {B B' : Subgroup G} (hB : B ∈ leviSet R A A₀)
    (hB' : B' ∈ leviSet R A A₀) : ∃ v ∈ levi R A A₀, conjSub B v = B' := by
  by_cases hne : B = B'
  · exact ⟨1, one_mem _, by rw [conjSub_one, hne]⟩
  obtain ⟨y, hy, hyB⟩ := exists_mem_sup_conjSub_eq_of_opposite h.root hB.1.1
    (opposite_of_mem_leviSet h hA h8 hA₀ hΔ hAΔ hB hB' hne)
  refine ⟨y, ?_, hyB⟩
  rw [levi_eq_sup_of_ne h hA h8 hA₀ hΔ hAΔ hB hB' hne]
  exact hy

theorem not_commuting_and_commuting {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀)
    {B B' : Subgroup G} (hB : B ∈ leviSet R A A₀) (hB' : B' ∈ leviSet R A A₀) (hne : B ≠ B')
    (hBX : Commuting B X) (hB'X : Commuting B' X) : False := by
  have := h.finite
  have hR := h.root
  have hXR : X ∈ R := hX.1.1.1
  have hVX : ∀ v ∈ levi R A A₀, conjSub X v = X := by
    intro v hv
    rw [levi_eq_sup_of_ne h hA h8 hA₀ hΔ hAΔ hB hB' hne] at hv
    exact conjSub_of_forall_commute fun x hx => Commuting.sup_left hBX hB'X v hv x hx
  obtain ⟨B₀, hB₀, hXB₀⟩ := exists_mem_leviSet_mem_lambdaSet h hA h8 hA₀ hΔ hAΔ hX
  have hcol : ∀ Y ∈ leviSet R A A₀, Y ≤ M R X := by
    intro Y hY
    obtain ⟨v, hv, hvY⟩ := exists_mem_levi_conjSub_eq h hA h8 hA₀ hΔ hAΔ hB₀ hY
    have := conjSub_mem_lambdaSet hR hXB₀ v
    rw [hvY, hVX v hv] at this
    exact QD.le_M (mem_lambdaSet_comm hY.1.1 this)
  exact Sec3.not_opposite_of_isPGroup_sup hR hB.1.1 hB'.1.1
    ((Q_eq_M h hXR).2.2.2.2.to_le (sup_le (hcol B hB) (hcol B' hB')))
    (opposite_of_mem_leviSet h hA h8 hA₀ hΔ hAΔ hB hB' hne)

theorem exists_mem_leviSet_ne (B : Subgroup G) : ∃ B' ∈ leviSet R A A₀, B ≠ B' := by
  obtain ⟨C, hC, D, hD, hCD, -⟩ := exists_levi_eq_sup h hA h8 hA₀ hΔ hAΔ
  by_cases hBC : B = C
  · exact ⟨D, hD, hBC ▸ hCD.1⟩
  · exact ⟨C, hC, hBC⟩

theorem mem_lambdaSet_of_commuting {X Y : Subgroup G} (hX : X ∈ lambdaStar R A A₀)
    (hY : Y ∈ leviSet R A A₀) (hYX : Commuting Y X) : X ∈ lambdaSet R Y := by
  obtain ⟨Y', hY', hYY'⟩ := exists_mem_leviSet_ne h hA h8 hA₀ hΔ hAΔ Y
  exact CaseD4.mem_lambdaSet_of_commuting_of_not h hA h8.2 hA₀ hY hY'
    (opposite_of_mem_leviSet h hA h8 hA₀ hΔ hAΔ hY hY' hYY')
    (fun T hT h1 h2 => not_commuting_and_commuting h hA h8 hA₀ hΔ hAΔ hT hY hY' hYY' h2 h1) hX
    hYX

theorem special_of_commuting {X Y Y' : Subgroup G} (hX : X ∈ lambdaStar R A A₀)
    (hY : Y ∈ leviSet R A A₀) (hY' : Y' ∈ leviSet R A A₀) (hne : Y ≠ Y')
    (hYX : Commuting Y X) : Special R Y' X :=
  have := h.finite
  CaseD4.special_of_commuting_of_not h.root hA hX hY'
    (fun h1 h2 => not_commuting_and_commuting h hA h8 hA₀ hΔ hAΔ hX hY hY' hne h1 h2) hYX

theorem natural_of_commuting {X Y Y' : Subgroup G} (hX : X ∈ lambdaStar R A A₀)
    (hY : Y ∈ leviSet R A A₀) (hY' : Y' ∈ leviSet R A A₀) (hne : Y ≠ Y')
    (hYX : Commuting Y X) :
    Special R Y' X ∧ (∀ u ∈ Y ⊔ Y', conjSub (X ⊔ ⁅Y', X⁆) u = X ⊔ ⁅Y', X⁆) ∧
      (∀ n ∈ X ⊔ ⁅Y', X⁆, (∀ y ∈ Y, Commute y n) → n ∈ X) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hs := special_of_commuting h hA h8 hA₀ hΔ hAΔ hX hY hY' hne hYX
  have hl := mem_lambdaSet_of_commuting h hA h8 hA₀ hΔ hAΔ hX hY hYX
  have hop : Opposite Y Y' := opposite_of_mem_leviSet h hA h8 hA₀ hΔ hAΔ hY hY' hne
  exact ⟨hs, fun u hu => Sec3.conjSub_sup_commutator_eq hR hiso hY.1.1 hY'.1.1 hop hl
    ⟨hX.1.1.1, hs⟩ hu, fun n hn hnY => Sec3.mem_of_forall_commute_of_mem_sup hR hiso hY.1.1
      hY'.1.1 hop hl ⟨hX.1.1.1, hs⟩ hn hnY⟩

omit h8 hΔ hAΔ in
theorem exists_mem_lambdaStar_not_commuting {E : Subgroup G} (hE : E ∈ lambdaStar R A A₀) :
    ∃ Y ∈ lambdaStar R A A₀, ¬ Commuting E Y := by
  by_contra! hall
  have hEM : Commuting E (M R A) := by
    rw [M_eq_gen_lambdaStar h hA hA₀, commuting_iff_le_centralizer]
    exact gen_le fun Y hY => commuting_iff_le_centralizer.1 (hall Y hY)
  have hmem : E ∈ {B | B ∈ R ∧ Commuting B (M R A)} := ⟨hE.1.1.1, hEM⟩
  rw [(Q_eq_M h hA).2.2.2.1, Set.mem_singleton_iff] at hmem
  exact hE.1.1.2.1 hmem

omit h8 hA₀ hΔ hAΔ in
theorem special_of_not_commuting {X Y : Subgroup G} (hX : X ∈ lambdaSet R A)
    (hY : Y ∈ lambdaSet R A) (hXY : ¬ Commuting X Y) : Special R X Y ∧ ⁅X, Y⁆ = A := by
  have := h.finite
  have hR := h.root
  have hne : X ≠ Y := fun e => hXY (e ▸ hR.commuting_self hX.1.1)
  have hs : Special R X Y := by
    rcases hR.rel X hX.1.1 Y hY.1.1 hne with hc | ho | hs
    · exact absurd hc hXY
    · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hX.1.1 hY.1.1
        ((Q_eq_M h hA).2.2.2.2.to_le (sup_le (QD.le_M hX) (QD.le_M hY))))
    · exact hs
  refine ⟨hs, QD.eq_of_le_of_mem hR h.noIsolated hs.1 hA ?_⟩
  rw [← (Q_eq_M h hA).2.2.1]
  exact Subgroup.commutator_mono (QD.le_M hX) (QD.le_M hY)

theorem exists_partner {E B B' : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hB : B ∈ leviSet R A A₀) (hB' : B' ∈ leviSet R A A₀) (hne : B ≠ B')
    (hBE : Commuting B E) : ∃ C ∈ lambdaStar R A A₀, Commuting B' C ∧ ¬ Commuting E C := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨Y, hY, hEY⟩ := exists_mem_lambdaStar_not_commuting h hA hA₀ hE
  by_cases hB'Y : Commuting B' Y
  · exact ⟨Y, hY, hB'Y, hEY⟩
  have hYR : Y ∈ R := hY.1.1.1
  have hsY : Special R Y B' := by
    have hne' : Y ≠ B' := fun e => hB'Y (e ▸ hR.commuting_self hYR)
    rcases hR.rel Y hYR B' hB'.1.1 hne' with hc | ho | hs
    · exact absurd hc.symm hB'Y
    · exact absurd ho.symm (CaseD4.not_opposite_of_mem_leviSet hR hA hY hB')
    · exact hs
  obtain ⟨hmemY, D, hD, hB'D, hYD⟩ :=
    exists_opposite_of_mem_lambdaStar h hA h8.2 hA₀ hB' hY hsY
  have hY₁ : ⁅Y, B'⁆ ∈ lambdaStar R A A₀ := hmemY _ hsY.1 le_sup_right
  refine ⟨⁅Y, B'⁆, hY₁, hsY.2.2.symm, fun hEY₁ => ?_⟩
  have hsEY : Special R E Y := (special_of_not_commuting h hA hE.1 hY.1 hEY).1
  rw [Subgroup.commutator_comm] at hY₁ hEY₁
  set N := Y ⊔ ⁅B', Y⁆ with hNdef
  have hψ : Y ∈ psiSet R B' := ⟨hYR, hsY.symm⟩
  have hinv : ∀ x ∈ D ⊔ B', conjSub N x = N := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hD.1.1 hB'.1.1 hB'D.symm hYD hψ hx
  have hBV : B ≤ D ⊔ B' := by
    rw [sup_comm, ← levi_eq_sup_of_ne h hA h8 hA₀ hΔ hAΔ hB' hD hB'D.1]
    exact le_iSup₂ (f := fun X (_ : X ∈ leviSet R A A₀) => X) B hB
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hE.1.1.1
  set K := N ⊓ Subgroup.centralizer ({e} : Set G) with hKdef
  have hY₁K : ⁅B', Y⁆ ≤ K := fun y hy => ⟨Subgroup.mem_sup_right hy,
    Subgroup.mem_centralizer_singleton_iff.2 (hEY₁ e he y hy).eq.symm⟩
  have hKY : K ⊓ Y = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    have hc : Commute e y := (Subgroup.mem_centralizer_singleton_iff.1 hy.1.2).symm
    exact (Subgroup.mem_bot).2
      (eq_one_of_commute_of_special hR hiso hE.1.1.1 hYR hsEY he he1 hy.2 hc)
  have hcardN : Nat.card N = Nat.card Y ^ 2 := Sec3.card_sup_commutator hR hiso hYD hψ
  have hcK : Nat.card K ≤ Nat.card ↥⁅B', Y⁆ := by
    have h1 := card_mul_card_le_card_sup hKY
    have h2 : Nat.card ↥(K ⊔ Y) ≤ Nat.card N :=
      Subgroup.card_le_of_le (sup_le inf_le_left le_sup_left)
    have hpos : 0 < Nat.card Y := Nat.card_pos
    rw [hR.card_eq hY₁.1.1.1 hYR]
    nlinarith
  have hKeq : ⁅B', Y⁆ = K := Subgroup.eq_of_le_of_card_ge hY₁K hcK
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := by
    refine le_normalizer_of_conjSub_le fun b hb => ?_
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hinv b (hBV hb)]
      exact conj_mem_conjSub b hn.1
    · have hbe : Commute b e := hBE b hb e he
      have hne' : Commute n e := Subgroup.mem_centralizer_singleton_iff.1 hn.2
      exact Subgroup.mem_centralizer_singleton_iff.2
        (((hbe.mul_left hne').mul_left hbe.inv_left).eq)
  have hBY₁ : B ≠ ⁅B', Y⁆ := fun e' =>
    (hY₁.2.2).not_commuting hR (e' ▸ hB.2.2.2)
  have hc := commuting_of_le_normalizer hR hiso hB.1.1 hY₁.1.1.1 hBY₁ (hKeq ▸ hBK)
  exact not_commuting_and_commuting h hA h8 hA₀ hΔ hAΔ hY₁ hB hB' hne hc
    (by rw [Subgroup.commutator_comm]; exact hsY.2.2.symm)

omit hA h8 hA₀ hΔ hAΔ h in
theorem leviSet_comm : leviSet R A₀ A = leviSet R A A₀ := by
  simp only [leviSet, Set.inter_comm]

theorem hyp_symm : A₀ ∈ R ∧ Sec8 R A₀ ∧ A ∈ omegaSet R A₀ ∧
    ∃ Δ₀ : Set (Subgroup G), IsWeakTI R Δ₀ ∧ A₀ ∈ Δ₀ := by
  have hR := h.root
  obtain ⟨g, hg⟩ := hR.exists_conjSub_eq hA hA₀.1
  exact ⟨hA₀.1, Sec8.of_mem hR hA hA₀.1 h8, ⟨hA, hA₀.2.symm⟩, conjSet Δ g,
    Sec5.isWeakTI_conjSet hR hΔ g, hg ▸ conjSub_mem_conjSet hAΔ g⟩

theorem config {A₁ B₁ E F : Subgroup G} (hA₁ : A₁ ∈ leviSet R A A₀)
    (hB₁ : B₁ ∈ leviSet R A A₀) (hne : A₁ ≠ B₁) (hE : E ∈ lambdaStar R A A₀)
    (hB₁E : Commuting B₁ E) (hF : F ∈ lambdaStar R A₀ A) (hA₁F : Commuting A₁ F)
    (hEF : Opposite E F) :
    Special R A₁ E ∧ Commuting B₁ E ∧ ⁅B₁, ⁅A₁, E⁆⁆ = E ∧ Commuting A₁ F ∧
      ⁅⁅A₁, E⁆, F⁆ = A₁ ∧ Special R B₁ F := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨hA₀R, h8₀, hAΩ, Δ₀, hΔ₀, hA₀Δ₀⟩ := hyp_symm h hA h8 hA₀ hΔ hAΔ
  have hA₁' : A₁ ∈ leviSet R A₀ A := by rw [leviSet_comm]; exact hA₁
  have hB₁' : B₁ ∈ leviSet R A₀ A := by rw [leviSet_comm]; exact hB₁
  have hA₁R : A₁ ∈ R := hA₁.1.1
  have hER : E ∈ R := hE.1.1.1
  have hFR : F ∈ R := hF.1.1.1
  obtain ⟨hsAE, hinv, hfix⟩ :=
    natural_of_commuting h hA h8 hA₀ hΔ hAΔ hE hB₁ hA₁ hne.symm hB₁E
  set D := ⁅A₁, E⁆ with hDdef
  have hDR : D ∈ R := hsAE.1
  have hD : D ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA h8.2 hA₀ hA₁ hE hsAE.symm).1 D hDR
    rw [Subgroup.commutator_comm E A₁] at this
    exact this le_sup_right
  have hDE : D ≠ E := by
    have := hsAE.symm.ne_commutator hR
    rw [Subgroup.commutator_comm E A₁] at this
    exact this.symm
  have hBN : B₁ ≤ Subgroup.normalizer ((E ⊔ D : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (hinv y (Subgroup.mem_sup_left hy))
  have hsBD : Special R B₁ D := by
    have hnc : ¬ Commuting B₁ D := by
      intro hc
      refine hDE (Subgroup.eq_of_le_of_card_ge (fun d hd => ?_) (hR.card_eq hER hDR).le)
      exact hfix d (Subgroup.mem_sup_right hd) fun y hy => hc y hy d hd
    have hne' : B₁ ≠ D := fun e => hnc (by rw [← e]; exact hR.commuting_self hB₁.1.1)
    rcases hR.rel _ hB₁.1.1 _ hDR hne' with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ho (CaseD4.not_opposite_of_mem_leviSet hR hA hD hB₁)
    · exact hs
  have h3 : ⁅B₁, D⁆ = E := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hER hsBD.1).le
    exact hfix x (Linear.commutator_le_of_le_normalizer hBN le_sup_right hx) fun y hy =>
      (hsBD.2.1 x hx y hy).symm
  have hFl : F ∈ lambdaSet R A₁ :=
    mem_lambdaSet_of_commuting h hA₀R h8₀ hAΩ hΔ₀ hA₀Δ₀ hF hA₁' hA₁F
  have hA₁Fl : A₁ ∈ lambdaSet R F := mem_lambdaSet_comm hA₁R hFl
  have hA₁ψ : A₁ ∈ psiSet R E := ⟨hA₁R, hsAE.symm⟩
  have hinv' : ∀ x ∈ F ⊔ E, conjSub (A₁ ⊔ ⁅E, A₁⁆) x = A₁ ⊔ ⁅E, A₁⁆ := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hFR hER hEF.symm hA₁Fl hA₁ψ hx
  have hfix' : ∀ n ∈ A₁ ⊔ ⁅E, A₁⁆, (∀ a ∈ F, Commute a n) → n ∈ A₁ := fun n hn hnF =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hFR hER hEF.symm hA₁Fl hA₁ψ hn hnF
  rw [Subgroup.commutator_comm E A₁] at hinv' hfix'
  have hFN : F ≤ Subgroup.normalizer ((A₁ ⊔ D : Subgroup G) : Set G) := fun f hf =>
    conjSub_eq_self_iff.1 (hinv' f (Subgroup.mem_sup_left hf))
  have hsDF : Special R D F := by
    have hnc : ¬ Commuting D F := by
      intro hc
      have hDA : D = A₁ := (Subgroup.eq_of_le_of_card_ge (fun d hd =>
        hfix' d (Subgroup.mem_sup_right hd) fun f hf => (hc d hd f hf).symm)
        (hR.card_eq hA₁R hDR).le)
      exact hD.2.2.not_commuting hR (hDA ▸ hA₁.2.2.2)
    have hne' : D ≠ F := fun e => hnc (by rw [← e]; exact hR.commuting_self hDR)
    rcases hR.rel _ hDR _ hFR hne' with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd hsAE.2.1 (not_commuting_of_opposite_of_mem_lambdaSet hR hDR ho hA₁Fl)
    · exact hs
  have h5 : ⁅D, F⁆ = A₁ := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hA₁R hsDF.1).le
    exact hfix' x (commutator_le_of_le_normalizer le_sup_right hFN hx) fun f hf =>
      (hsDF.2.2 x hx f hf).symm
  exact ⟨hsAE, hB₁E, h3, hA₁F, h5,
    special_of_commuting h hA₀R h8₀ hAΩ hΔ₀ hA₀Δ₀ hF hA₁' hB₁' hne hA₁F⟩

theorem exists_extremal_triple {A₁ B₁ : Subgroup G} (hA₁ : A₁ ∈ leviSet R A A₀)
    (hB₁ : B₁ ∈ leviSet R A A₀) (hne : A₁ ≠ B₁) :
    ∃ E ∈ lambdaStar R A A₀, ∃ C ∈ lambdaStar R A A₀, Commuting B₁ E ∧ Commuting A₁ C ∧
      Special R E C ∧ ⁅E, C⁆ = A ∧ ⁅A₀, C⁆ ∈ lambdaStar R A₀ A ∧ Commuting A₁ ⁅A₀, C⁆ ∧
      Commuting ⁅A₀, C⁆ C ∧ ⁅A, ⁅A₀, C⁆⁆ = C ∧ Opposite E ⁅A₀, C⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨E, hE, hEB⟩ := CaseD4.exists_mem_lambdaStar_forall_commuting h hA h8.2 hA₀
    (Q := fun _ : Unit => B₁) (fun _ => hB₁) (fun _ _ => hR.commuting_self hB₁.1.1)
    (CaseD4.lambdaStar_nonempty h hA hA₀) Finset.univ
  have hB₁E : Commuting B₁ E := hEB () (Finset.mem_univ _)
  obtain ⟨C, hC, hA₁C, hEC⟩ := exists_partner h hA h8 hA₀ hΔ hAΔ hE hB₁ hA₁ hne.symm hB₁E
  obtain ⟨hsEC, hECA⟩ := special_of_not_commuting h hA hE.1 hC.1 hEC
  obtain ⟨hF, hFC, hAFC, hY⟩ := CaseD4.commutator_props h hA hA₀ hC
  exact ⟨E, hE, C, hC, hB₁E, hA₁C, hsEC, hECA, hF, hY A₁ hA₁ hA₁C, hFC, hAFC,
    CaseD4.opposite_of_extremal hR hiso hA hC.1.1.1 hE.1.1.1 hF.1.1.1 hC.1.1.2.2
      hE.1.1.2.2.symm hsEC hECA hFC hF.2.2 hAFC⟩

end Levi

end CaseB

end CFSG.Timmesfeld.ARS

module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFacts
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF4
public import CFSG.RankThree.PartTwo.Sec4.E27.D4TypeI

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Seitz CFSG.Open TauCeti
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec4.E27

section Classify


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem exists_conj_with_A0 (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ)
    (hn : 2 ≤ n) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) (hτ : tauAut σ ∈ E) :
    ∃ g ∈ Gsub σ, ∃ a ∈ A0sub σ, a ^ 3 = 1 ∧ a ≠ 1 ∧
      MulAut.conj a ∈ E.map (MulAut.congr (MulAut.conj g)).toMonoidHom := by
  have hAB := trialityABFacts_of_par hgold P hn
  have hinj := conj_injective_C0 σ n P.one_le P.card P.frob
  have hI9 := card_innerPart_eq σ n P.one_le P.card P.frob hE hcard
  have hIab := innerPart_isElemAbelian σ n P.one_le P.card P.frob hE
  have hIG : innerPart σ E ≤ Gsub σ := by
    intro x hx
    have hcomm : MulAut.conj x * tauAut σ = tauAut σ * MulAut.conj x :=
      comm_of_isElemAbelian hE hx hτ
    show tauAut σ x = x
    have h1 := aut_conj_conj (tauAut σ) x
    have h2 : tauAut σ * MulAut.conj x * (tauAut σ)⁻¹ = MulAut.conj x := by
      rw [← hcomm]; group
    exact hinj (h1.symm.trans h2)
  obtain ⟨x, hxI, hx1⟩ : ∃ x ∈ innerPart σ E, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : innerPart σ E = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at hI9
    omega
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hE.2 _ hxI)
  obtain ⟨g, hgG, hg⟩ := gsub_three_conj σ hAB n hn P.card P.frob (hIG hxI) hx3 hx1
  set I' : Subgroup (C0 σ) := (innerPart σ E).map (MulAut.conj g).toMonoidHom with hI'
  have hI'ab : IsElemAbelian 3 I' := CFSG.Open.IsElemAbelian.map hIab _
  have hI'c : Nat.card I' = 3 ^ 2 := by
    rw [hI', Subgroup.card_map_of_injective (MulAut.conj g).injective, hI9]
    norm_num
  have hτg : tauAut σ g = g := hgG
  have hI'G : I' ≤ Gsub σ := by
    rintro _ ⟨y, hy, rfl⟩
    show tauAut σ (g * y * g⁻¹) = g * y * g⁻¹
    have hyG : tauAut σ y = y := hIG hy
    rw [map_mul, map_mul, map_inv, hτg, hyG]
  have hmem : ∀ y ∈ innerPart σ E,
      MulAut.conj (g * y * g⁻¹) ∈ E.map (MulAut.congr (MulAut.conj g)).toMonoidHom := by
    intro y hy
    refine ⟨MulAut.conj y, hy, ?_⟩
    show (MulAut.congr (MulAut.conj g)) (MulAut.conj y) = MulAut.conj (g * y * g⁻¹)
    rw [congr_apply_eq, ← map_inv, ← map_mul, ← map_mul]
  rcases hg with hgA | hgB
  · exact ⟨g, hgG, g * x * g⁻¹, hgA, by rw [conj_pow, hx3]; group,
      fun h => hx1 (by
        have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [this, h]; group), hmem x hxI⟩
  ·
    set b : C0 σ := g * x * g⁻¹ with hb
    have hb3 : b ^ 3 = 1 := by rw [hb, conj_pow, hx3]; group
    have hb1 : b ≠ 1 := fun h => hx1 (by
      have : x = g⁻¹ * b * g := by rw [hb]; group
      rw [this, h]; group)
    have hbI' : b ∈ I' := ⟨x, hxI, rfl⟩
    have hle : I' ≤ Asub σ ⊔ Bsub σ := fun e he =>
      centralizer_le_AB σ hAB n hn P.card P.frob hgB hb3 hb1 (by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact comm_of_isElemAbelian hI'ab he hbI')
    obtain ⟨a₁, b₁, ha₁, hb₁, ha₁3, hb₁3, ha₁1, hb₁1, hI'eq⟩ :=
      plane_in_AB σ hAB n hn P.card P.frob
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hI'ab) hI'c hle
    have ha₁I' : a₁ ∈ I' := by
      rw [hI'eq]; exact Subgroup.subset_closure (by simp)
    refine ⟨g, hgG, a₁, ⟨ha₁, hI'G ha₁I'⟩, ha₁3, ha₁1, ?_⟩
    obtain ⟨y, hy, rfl⟩ := ha₁I'
    exact hmem y hy

theorem typeI_of_tau_mem (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ)
    (hn : 2 ≤ n) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) (hτ : tauAut σ ∈ E) : seitzHyperGamma 3 E = ⊤ := by
  obtain ⟨g, hgG, a, ha, ha3, ha1, hcaE⟩ := exists_conj_with_A0 hgold P hn hE hcard hτ
  set φ : MulAut (C0 σ) := MulAut.conj g with hφ
  set E' : Subgroup (MulAut (C0 σ)) := E.map (MulAut.congr φ).toMonoidHom with hE'
  have hE'ab : IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hE _
  have hE'c : Nat.card E' = 27 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.congr φ).injective, hcard]
  have hτg : tauAut σ g = g := hgG
  have hcτ : (MulAut.congr φ) (tauAut σ) = tauAut σ := by
    rw [congr_apply_eq, hφ]
    have h1 := aut_conj_conj (tauAut σ) g
    rw [hτg] at h1
    have h2 : tauAut σ * MulAut.conj g = MulAut.conj g * tauAut σ := by
      rw [← mul_inv_eq_iff_eq_mul]; exact h1
    rw [← h2]
    group
  have hτE' : tauAut σ ∈ E' := ⟨tauAut σ, hτ, hcτ⟩
  exact seitzHyperGamma_eq_top_of_conj φ
    (typeI_seitzHyperGamma hgold P hn hE'ab hE'c hτE' ha ha3 ha1 hcaE)

theorem typeI_of_conj_tau (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ)
    (hn : 2 ≤ n) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) (φ : MulAut (C0 σ))
    (hτ : tauAut σ ∈ E.map (MulAut.congr φ).toMonoidHom) : seitzHyperGamma 3 E = ⊤ :=
  seitzHyperGamma_eq_top_of_conj φ
    (typeI_of_tau_mem hgold P hn (CFSG.Open.IsElemAbelian.map hE _)
      (by rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hcard]) hτ)

theorem classX_of_no_conj_tau (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ)
    (hn : 2 ≤ n) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27)
    (hno : ∀ φ : MulAut (C0 σ), tauAut σ ∉ E.map (MulAut.congr φ).toMonoidHom)
    {x : C0 σ} (hx : MulAut.conj x ∈ E) (hx1 : x ≠ 1) : IsClassX σ x := by
  have hAB := trialityABFacts_of_par hgold P hn
  have hinj := conj_injective_C0 σ n P.one_le P.card P.frob
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hE.2 _ hx)
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  obtain ⟨g₀, hg₀⟩ := KS11Lie6Proof.d4ThreeConj_holds X (2 ^ n) σ P.card P.frob h3 x hx3 hx1
  rcases hg₀ with hA | hB
  · exact ⟨hx3, hx1, g₀, hA⟩
  · exfalso
    obtain ⟨β, hβE, g, e, he, hβ⟩ := exists_outer_shape σ n P.one_le P.card P.frob hE hcard
    have hβ3 : (MulAut.conj g * tauAut σ ^ e) ^ 3 = 1 := by rw [← hβ]; exact hE.2 β hβE
    have hcomm : Commute (MulAut.conj x) (MulAut.conj g * tauAut σ ^ e) := by
      rw [← hβ]; exact comm_of_isElemAbelian hE hx hβE
    obtain ⟨ψ, b, -, -, -, hψ⟩ := outer_Y_case σ hAB n hn P.card P.frob he hx3 hx1 hβ3 hcomm
      ⟨g₀, hB⟩
    apply hno ψ
    have hsub : Subgroup.closure ({MulAut.conj x, MulAut.conj g * tauAut σ ^ e} :
        Set (MulAut (C0 σ))) ≤ E := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | hy
      · exact hx
      · rw [Set.mem_singleton_iff.mp hy, ← hβ]; exact hβE
    have hτcl : tauAut σ ∈ Subgroup.closure ({MulAut.conj b, tauAut σ} : Set (MulAut (C0 σ))) :=
      Subgroup.subset_closure (by simp)
    rw [← hψ] at hτcl
    exact Subgroup.map_mono hsub hτcl

end Classify

end CFSG.RankThree.PartTwo.Sec4.E27

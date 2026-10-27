module

public import CFSG.RankThree.PartOne.AUTSL.FourGlue
public import CFSG.RankThree.PartOne.AUTSL.FourStr

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.AUTSL.Four

open CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G Γ : Type} [Group G] [Group Γ]

theorem fourFacts_of_lineStr {p : ℕ} {E I : Subgroup G} {O Ē : Subgroup Γ}
    {lam : Fin 3 → Subgroup Γ} (hL : LineStr p O Ē lam) (hEN : E ≤ Subgroup.normalizer (I : Set G))
    (ψ : ↥I →* Γ) (hψinj : Function.Injective ψ) (hψO : ∀ x, ψ x ∈ O)
    (abar : ↥E →* Γ) (hainj : Function.Injective abar) (harange : abar.range = Ē)
    (hcompat : ∀ (e : ↥E) (x : ↥I) (hx : (e : G) * x * (e : G)⁻¹ ∈ I),
      ψ ⟨(e : G) * x * (e : G)⁻¹, hx⟩ = abar e * ψ x * (abar e)⁻¹)
    (hEI : ∀ (e : ↥E) (he : (e : G) ∈ I), abar e = ψ ⟨e, he⟩)
    (hnorm : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)) (hyI : y ∈ I) (e : ↥E),
      abar (conjAut E y hy e) = ψ ⟨y, hyI⟩ * abar e * (ψ ⟨y, hyI⟩)⁻¹) :
    FourFacts p E I := by
  have hmapcomap : ∀ H : Subgroup Γ, H ≤ Ē → (H.comap abar).map abar = H := by
    intro H hH
    rw [Subgroup.map_comap_eq, harange]
    exact inf_eq_right.2 hH
  have hmap_inj : Function.Injective (Subgroup.map abar : Subgroup ↥E → Subgroup Γ) :=
    Subgroup.map_injective hainj
  have hmapℓ : ∀ i, ((lam i).comap abar).map abar = lam i := fun i => hmapcomap _ (hL.le i)
  have hhyp : ∀ k : Fin 3, (⨆ j, ⨆ (_ : j ≠ k), (lam j).comap abar).map abar =
      ⨆ j, ⨆ (_ : j ≠ k), lam j := by
    intro k
    simp only [Subgroup.map_iSup, hmapℓ]
  have hcardE : Nat.card ↥Ē = Nat.card ↥E := by
    rw [← harange]
    exact (Nat.card_congr (MonoidHom.ofInjective hainj).toEquiv).symm
  refine ⟨fun i => (lam i).comap abar, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← Subgroup.card_map_of_injective hainj, hmapℓ]
    exact hL.card i
  · apply hmap_inj
    rw [Subgroup.map_iSup]
    simp only [hmapℓ]
    rw [hL.top, ← harange, MonoidHom.range_eq_map]
  · intro i
    apply hmap_inj
    rw [Subgroup.map_inf_eq _ _ _ hainj, hhyp i, hmapℓ i, hL.indep i, Subgroup.map_bot]
  · intro y hy hyI
    have hzO : ψ ⟨y, hyI⟩ ∈ O := hψO _
    have hzE : ∀ e' ∈ Ē, ψ ⟨y, hyI⟩ * e' * (ψ ⟨y, hyI⟩)⁻¹ ∈ Ē := by
      intro e' he'
      rw [← harange] at he'
      obtain ⟨e, rfl⟩ := he'
      rw [← hnorm y hy hyI e, ← harange]
      exact ⟨_, rfl⟩
    obtain ⟨π, hπ⟩ := hL.mono _ hzO hzE
    refine ⟨π, fun i => ?_⟩
    ext e
    simp only [Subgroup.mem_map, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    have hlam : abar e ∈ lam (π i) ↔ ∃ x ∈ lam i, ψ ⟨y, hyI⟩ * x * (ψ ⟨y, hyI⟩)⁻¹ = abar e := by
      rw [← hπ i]
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hlam]
    constructor
    · rintro ⟨e₀, he₀, rfl⟩
      exact ⟨abar e₀, he₀, (hnorm y hy hyI e₀).symm⟩
    · rintro ⟨x, hx, hxe⟩
      have hxE : x ∈ Ē := hL.le i hx
      rw [← harange] at hxE
      obtain ⟨e₀, rfl⟩ := hxE
      refine ⟨e₀, hx, hainj ?_⟩
      rw [hnorm y hy hyI e₀, hxe]
  · intro D J S hDE hcard hJI hJc hJperf hSJ hS1 hS2 hSnorm hSE
    set D₀ : Subgroup ↥E := D.comap E.subtype with hD₀def
    set J₀ : Subgroup ↥I := J.comap I.subtype with hJ₀def
    set S₀ : Subgroup ↥I := S.comap I.subtype with hS₀def
    have hD₀ : D₀.map E.subtype = D := by
      rw [hD₀def, Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.2 hDE
    have hJ₀ : J₀.map I.subtype = J := by
      rw [hJ₀def, Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.2 hJI
    have hSI : S ≤ I := hSJ.trans hJI
    have hS₀ : S₀.map I.subtype = S := by
      rw [hS₀def, Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.2 hSI
    have hDb : D₀.map abar ≤ Ē := harange ▸ Subgroup.map_le_range abar D₀
    have hJb : J₀.map ψ ≤ O := by
      rintro _ ⟨x, -, rfl⟩
      exact hψO x
    have hcardb : p * Nat.card ↥(D₀.map abar) = Nat.card ↥Ē := by
      rw [Subgroup.card_map_of_injective hainj, hcardE, ← hcard,
        ← Subgroup.card_map_of_injective (Subgroup.subtype_injective E) (K := D₀), hD₀]
    have hcen : J₀.map ψ ≤ Subgroup.centralizer ((D₀.map abar : Subgroup Γ) : Set Γ) := by
      rintro _ ⟨j, hj, rfl⟩ _ ⟨d, hd, rfl⟩
      have hj' : (j : G) ∈ J := hj
      have hd' : (d : G) ∈ D := hd
      have hcomm : (d : G) * j = j * d := Subgroup.mem_centralizer_iff.1 (hJc hj') d hd'
      have hx : (d : G) * (j : G) * (d : G)⁻¹ ∈ I := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact j.2
      have h1 := hcompat d j hx
      have h2 : (⟨(d : G) * j * (d : G)⁻¹, hx⟩ : ↥I) = j := by
        apply Subtype.ext
        simp only
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [h2] at h1
      have h3 := congrArg (fun z => z * abar d) h1
      simp only [inv_mul_cancel_right] at h3
      exact h3.symm
    have hperf : ⁅J₀.map ψ, J₀.map ψ⁆ = J₀.map ψ := by
      rw [← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective (Subgroup.subtype_injective I)
      rw [Subgroup.map_commutator, hJ₀, hJperf]
    have hSJ₀ : S₀ ≤ J₀ := fun x hx => hSJ hx
    have hS1' : S₀.map ψ ≠ ⊥ := by
      intro h0
      apply hS1
      have : S₀ = ⊥ := by
        apply Subgroup.map_injective hψinj
        rw [h0, Subgroup.map_bot]
      rw [← hS₀, this, Subgroup.map_bot]
    have hS2' : IsPGroup 2 (S₀.map ψ) := by
      rintro ⟨_, x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hS2 ⟨(x : G), hx⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : (x : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h2 : x ^ 2 ^ k = 1 := Subtype.ext h1
      show ψ x ^ 2 ^ k = 1
      rw [← map_pow, h2, map_one]
    have hfwd : ∀ e' ∈ Ē, ∀ s ∈ S₀.map ψ, e' * s * e'⁻¹ ∈ S₀.map ψ := by
      intro e' he' s hs
      rw [← harange] at he'
      obtain ⟨e, rfl⟩ := he'
      obtain ⟨x, hx, rfl⟩ := hs
      have heN : (e : G) ∈ Subgroup.normalizer (S : Set G) := hSnorm e.2
      have hx' : (e : G) * x * (e : G)⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 heN _).1 hx
      have hxI : (e : G) * x * (e : G)⁻¹ ∈ I := hSI hx'
      refine ⟨⟨(e : G) * x * (e : G)⁻¹, hxI⟩, hx', ?_⟩
      exact hcompat e x hxI
    have hnormS : Ē ≤ Subgroup.normalizer ((S₀.map ψ : Subgroup Γ) : Set Γ) := by
      intro e' he'
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hfwd e' he' h hh, fun hh => ?_⟩
      have := hfwd e'⁻¹ (inv_mem he') _ hh
      simpa [mul_assoc] using this
    have hSE' : S₀.map ψ = ⁅S₀.map ψ, Ē⁆ := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        have hxS : (x : G) ∈ S := hx
        rw [hSE, Subgroup.commutator_def] at hxS
        have key : ∃ hg : (x : G) ∈ I, ψ ⟨x, hg⟩ ∈ ⁅S₀.map ψ, Ē⁆ := by
          refine Subgroup.closure_induction
            (p := fun g _ => ∃ hg : g ∈ I, ψ ⟨g, hg⟩ ∈ ⁅S₀.map ψ, Ē⁆) ?_ ?_ ?_ ?_ hxS
          · rintro g ⟨s', hs', e', he', rfl⟩
            have hs'I : s' ∈ I := hSI hs'
            have he'N : e' ∈ Subgroup.normalizer (I : Set G) := hEN he'
            have h1 : e' * s'⁻¹ * e'⁻¹ ∈ I :=
              (Subgroup.mem_normalizer_iff.1 he'N _).1 (inv_mem hs'I)
            have hg : ⁅s', e'⁆ ∈ I := by
              rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc e']
              exact mul_mem hs'I (by simpa [mul_assoc] using h1)
            refine ⟨hg, ?_⟩
            have hsb : ψ ⟨s', hs'I⟩ ∈ S₀.map ψ := ⟨⟨s', hs'I⟩, hs', rfl⟩
            have heb : abar ⟨e', he'⟩ ∈ Ē := harange ▸ ⟨⟨e', he'⟩, rfl⟩
            have hcm := Subgroup.commutator_mem_commutator hsb heb
            have h2 : (⟨⁅s', e'⁆, hg⟩ : ↥I) = ⟨s', hs'I⟩ * ⟨e' * s'⁻¹ * e'⁻¹, h1⟩ := by
              apply Subtype.ext
              simp [commutatorElement_def, mul_assoc]
            have h3 : ψ ⟨e' * s'⁻¹ * e'⁻¹, h1⟩ =
                abar ⟨e', he'⟩ * (ψ ⟨s', hs'I⟩)⁻¹ * (abar ⟨e', he'⟩)⁻¹ := by
              have := hcompat ⟨e', he'⟩ (⟨s', hs'I⟩ : ↥I)⁻¹ h1
              rw [map_inv] at this
              exact this
            rw [h2, map_mul, h3]
            have h4 : ψ ⟨s', hs'I⟩ * (abar ⟨e', he'⟩ * (ψ ⟨s', hs'I⟩)⁻¹ *
                (abar ⟨e', he'⟩)⁻¹) = ⁅ψ ⟨s', hs'I⟩, abar ⟨e', he'⟩⁆ := by
              simp [commutatorElement_def, mul_assoc]
            rw [h4]
            exact hcm
          · refine ⟨one_mem _, ?_⟩
            have h1 : (⟨1, one_mem I⟩ : ↥I) = 1 := rfl
            rw [h1, map_one]
            exact one_mem _
          · rintro g₁ g₂ _ _ ⟨h1, h1'⟩ ⟨h2, h2'⟩
            refine ⟨mul_mem h1 h2, ?_⟩
            have : (⟨g₁ * g₂, mul_mem h1 h2⟩ : ↥I) = ⟨g₁, h1⟩ * ⟨g₂, h2⟩ := rfl
            rw [this, map_mul]
            exact mul_mem h1' h2'
          · rintro g _ ⟨h1, h1'⟩
            refine ⟨inv_mem h1, ?_⟩
            have : (⟨g⁻¹, inv_mem h1⟩ : ↥I) = (⟨g, h1⟩ : ↥I)⁻¹ := rfl
            rw [this, map_inv]
            exact inv_mem h1'
        obtain ⟨hxI, hxT⟩ := key
        exact hxT
      · rw [Subgroup.commutator_le]
        intro s hs e' he'
        have h1 := hfwd e' he' s hs
        have h2 : ⁅s, e'⁆ = s * (e' * s⁻¹ * e'⁻¹) := by
          simp [commutatorElement_def, mul_assoc]
        rw [h2]
        exact mul_mem hs (hfwd e' he' s⁻¹ (inv_mem hs))
    obtain ⟨k, hk1, hk2⟩ := hL.data (D₀.map abar) (J₀.map ψ) (S₀.map ψ) hDb hcardb hJb hcen hperf
      (Subgroup.map_mono hSJ₀) hS1' hS2' hnormS hSE'
    refine ⟨k, ?_, ?_⟩
    · rw [← hD₀]
      congr 1
      apply hmap_inj
      rw [hhyp k, ← hk1]
    · intro e he
      have heI : (e : G) ∈ I := hJI he
      have h1 : abar e ∈ J₀.map ψ := ⟨⟨e, heI⟩, he, (hEI e heI).symm⟩
      have h2 : abar e ∈ Ē := harange ▸ ⟨e, rfl⟩
      exact hk2 ⟨h1, h2⟩

end CFSG.RankThree.PartOne.AUTSL.Four

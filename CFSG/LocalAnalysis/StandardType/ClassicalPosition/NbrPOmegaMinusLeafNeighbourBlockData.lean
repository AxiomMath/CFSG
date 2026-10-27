module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafCore

public section

namespace CFSG.StandardType.ClassicalPosition.NbrLeaf

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition

open scoped commutatorElement

local notation "Ix" n:max => (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
local notation "Mx" n:max f:max => Matrix (Ix n) (Ix n) (GaloisField 2 f)
set_option quotPrecheck false in
local notation "UK" n:max f:max => (ggU .POmegaMinus n f).K
set_option quotPrecheck false in
local notation "ρm" n:max f:max => Spin.spinMatrix
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
set_option quotPrecheck false in
local notation "Gm" n:max f:max => LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
local notation "AdS" f:max S:max => Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
local notation "Fadj" n:max f:max e:max => formAdj (RingHom.id (GaloisField 2 f)) (Gm n f) e
local notation "BlkC" n:max f:max S:max ε:max =>
  (glBlockCentralizer (ρm n f) S ε : Subgroup (UK n f))
local notation "rk" f:max e:max =>
  Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))

private theorem nbrpmmx_liftComponents
    {X : Type} [Group X] [Finite X] (n f : ℕ) (hn : 4 ≤ n)
    (ψ : UK n f →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaMinus n f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Ix n) (GaloisField 2 f))) (hF : FullD n f ψ D S)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) :
    ∃ S' : Set (GL (Ix n) (GaloisField 2 f)),
      S' ⊆ S ∧
      (∀ s ∈ S', s ∈ (ρm n f).range) ∧
      (∀ s ∈ S', ∀ s' ∈ S', Commute s s') ∧
      (∀ s ∈ S', Odd (orderOf s)) ∧
      ∃ K' : Subgroup (UK n f),
        IsComponentOf K' ((Subgroup.centralizer S').comap (ρm n f)) ∧
        K'.map ψ = K := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  let F := GaloisField 2 f
  let Q : QuadraticForm F ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → F) :=
    Spin.quadMinus n F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  let j : spinGroup Q →* GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F := Spin.spinMatrix Q
  have hinj : Function.Injective j := nbrpom_spinMatrix_injective n f
  let P : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F → Prop := fun s => s ∈ j.range
  have heB : e ∈ B₁ := h11 heD
  have heID : GGPsiInnerDiag (Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)) ψ e := h8 e heB
  obtain ⟨se₀, hse₀⟩ :=
    exists_conj_eq_POmegaMinus n (minusCoeffs_irr 2 f) hn ψ h2 heID
  let se : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F := j se₀
  have hsej : se ∈ j.range := ⟨se₀, rfl⟩
  have hseLift : IsGLLift j ψ se e := fun u =>
    ⟨se₀ * u * se₀⁻¹, by
      show j (se₀ * u * se₀⁻¹) = j se₀ * j u * (j se₀)⁻¹
      rw [map_mul, map_mul, map_inv], hse₀ u⟩
  have hlift : ∀ d ∈ Subgroup.zpowers e, ∃ s : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
      P s ∧ IsGLLift j ψ s d := by
    intro d hd
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hd
    refine ⟨se ^ m, Subgroup.zpow_mem _ hsej m, ?_⟩
    rw [← hm]
    exact nbrpom_lift_zpow n f ψ hsej hseLift m
  have hcent : Subgroup.centralizer (Subgroup.zpowers e : Set X) =
      Subgroup.centralizer ({e} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hKcomp' : IsComponentOf K (Subgroup.centralizer (Subgroup.zpowers e : Set X)) := by
    rw [hcent]; exact hKcomp
  have hJ : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer
      (Subgroup.zpowers e : Set X)) := by
    rw [h1]
    exact CFSG.Assembly.IsComponentOf.of_le_of_le hKcomp'
      (le_inf hKG₀ hKcomp'.1) inf_le_right
  obtain ⟨K', hK'comp, hK'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift j hinj ψ h2 P hJ hlift
  let S' : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :=
    {s | P s ∧ ∃ d ∈ Subgroup.zpowers e, IsGLLift j ψ s d}
  have hSU' : ∀ s ∈ S', s ∈ j.range := fun s hs => hs.1
  have hSe : S' ⊆ S := by
    intro s hs
    obtain ⟨d, hd, hsl⟩ := hs.2
    exact hF s hs.1 ⟨d, Subgroup.zpowers_le.mpr heD hd, hsl⟩
  have hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s' := by
    intro s hs s' hs'
    obtain ⟨d, hd, hsl⟩ := hs.2
    obtain ⟨d', hd', hs'l⟩ := hs'.2
    have hdd' : Commute d d' := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hd
      obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.mp hd'
      rw [← hm, ← hm']
      exact (Commute.refl e).zpow_zpow m m'
    obtain ⟨s₀, hs₀, hsl₀⟩ := nbrpom_lift_to_mem n f ψ hs.1 hsl
    obtain ⟨s₁, hs₁, hsl₁⟩ := nbrpom_lift_to_mem n f ψ hs'.1 hs'l
    have hc := conj_eq_commute_POmegaMinus n (minusCoeffs_irr 2 f) hn ψ h2 hdd' hsl₀ hsl₁
    have hc' : s * s' = s' * s := by
      rw [← hs₀, ← hs₁, ← map_mul, ← map_mul, hc.eq]
    exact hc'
  have hodd' : ∀ s ∈ S', Odd (orderOf s) := by
    intro s hs
    obtain ⟨d, hd, hsl⟩ := hs.2
    have hdB : d ∈ B₁ := Subgroup.zpowers_le.mpr heB hd
    have hdpow : d ^ p = 1 := h9.2 d hdB
    have hspowj : s ^ p ∈ j.range := Subgroup.pow_mem _ hs.1 p
    have hslpow : IsGLLift j ψ (s ^ p) 1 := by
      have h := hsl.pow p
      rwa [hdpow] at h
    have huniq : s ^ p = 1 :=
      nbrpom_lift_unique n f hn ψ h2 hspowj (Subgroup.one_mem _) hslpow isGLLift_one
    have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr huniq
    have hpodd : Odd p := h5.odd_of_ne_two h6
    rcases h5.eq_one_or_self_of_dvd (orderOf s) hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hpodd
  exact ⟨S', hSe, hSU', hS', hodd', K', hK'comp, hK'map⟩

variable {X : Type} [Group X] [Finite X] (n f : ℕ) (hn : 4 ≤ n) (ψ : UK n f →* X) (p : ℕ)
  (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .POmegaMinus n f ψ p G₀ B₁ D J L x)
include hn hH
variable (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f)) (ε e_J : Mx n f)
  (hB : SetD n f ψ J S J') (hF : FullD n f ψ D S) (hE : EpsD n f S J' ε)
  (heJ : IsPrimIdemIn (AdS f S) e_J)
include S J' ε e_J hB hF hE heJ
variable (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
  (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K)
include heD hKG₀ hKcomp hJK

theorem nbrpmmx_neighbourBlockData :
    ∃ (S' : Set (GL (Ix n) (GaloisField 2 f))) (K' : Subgroup (UK n f)) (ε' e' : Mx n f),
      S' ⊆ S ∧ SetD n f ψ K S' K' ∧ EpsD n f S' K' ε' ∧ IsPrimIdemIn (AdS f S') e' ∧
        e' * ε' = e' ∧ SplitD n f ε' e' ∧ J' ≤ K' ∧ ε * ε' = ε := by
  obtain ⟨S', hSe, hSU', hS', hodd', K', hK'comp, hK'map⟩ :=
    nbrpmmx_liftComponents n f hn ψ p G₀ B₁ D J L x hH S hF e heD K hKG₀ hKcomp
  obtain ⟨ε', e', hε', he', he'ε', hsplit', hK'ε'⟩ :=
    nbrpom_L3 n f hn S' hSU' hS' K' hK'comp
  have hJK' : J' ≤ K' := by
    have hmapJK : J'.map ψ ≤ K'.map ψ := by
      calc J'.map ψ = J := hB.2.2.2.2
        _ ≤ K := hJK
        _ = K'.map ψ := hK'map.symm
    have hleJK : J' ≤ K' ⊔ ψ.ker := Subgroup.map_le_map_iff.mp hmapJK
    have hperf : commutator ↥J' = ⊤ := hB.2.2.2.1.2.2.1
    exact perfect_le_of_le_sup_center hH.2.1 hleJK hperf
  have hG : IsUnit (Gm n f).det :=
    nbrpom_isUnit_det (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f)
        (minusCoeffs_irr 2 f))
  have htie : ε * ε' = ε := by
    have hAe_le : AdS f S' ≤ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe)
    have hε'A : ε' ∈ AdS f S := hAe_le hε'.1
    have hcommA : ∀ a ∈ AdS f S, ∀ b ∈ AdS f S, a * b = b * a :=
      fun a ha b hb => (adjoin_comm hB.2.1 a ha b hb).eq
    have hmem : ε * ε' ∈ AdS f S := Subalgebra.mul_mem _ hE.1.1 hε'A
    have hidem : IsIdempotentElem (ε * ε') := by
      rw [IsIdempotentElem]
      calc (ε * ε') * (ε * ε') = ε * (ε' * (ε * ε')) := by rw [mul_assoc]
        _ = ε * ((ε' * ε) * ε') := by rw [mul_assoc]
        _ = ε * ((ε * ε') * ε') := by rw [hcommA ε' hε'A ε hE.1.1]
        _ = ε * (ε * (ε' * ε')) := by rw [mul_assoc]
        _ = ε * (ε * ε') := by rw [hε'.2.1.eq]
        _ = (ε * ε) * ε' := by rw [← mul_assoc]
        _ = ε * ε' := by rw [hE.1.2.1.eq]
    have hadj : formAdj (RingHom.id (GaloisField 2 f)) (Gm n f) (ε * ε') = ε * ε' := by
      rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG, hE.1.2.2.2.1, hε'.2.2.2.1]
      exact hcommA ε' hε'A ε hE.1.1
    have hbelow : (ε * ε') * ε = ε * ε' := by
      rw [mul_assoc, hcommA ε' hε'A ε hE.1.1, ← mul_assoc, hE.1.2.1.eq]
    rcases hE.1.2.2.2.2 (ε * ε') hmem hidem hadj hbelow with h0 | heq
    · exfalso
      have hJ'bot : J' = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        have huG : u ∈ BlkC n f S ε := by
          have h := (Subgroup.commutator_le_sup (BlkC n f S ε) (BlkC n f S ε))
            (hE.2.1 hu)
          rwa [sup_idem] at h
        have huGe : u ∈ BlkC n f S' ε' := by
          have h := (Subgroup.commutator_le_sup (BlkC n f S' ε') (BlkC n f S' ε'))
            (hK'ε'.1 (hJK' hu))
          rwa [sup_idem] at h
        have huG' : (ρm n f) u ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) :=
          Subgroup.mem_comap.mp huG
        have huGe' : (ρm n f) u ∈ Subgroup.centralizer S' ⊓ glFixing (1 - ε') :=
          Subgroup.mem_comap.mp huGe
        have huc : (ρm n f) u ∈ Subgroup.centralizer S := huG'.1
        let U : Mx n f := ((ρm n f) u : Mx n f)
        have hfixJ : U * (1 - ε) = 1 - ε := huG'.2
        have hfixe : U * (1 - ε') = 1 - ε' := huGe'.2
        have hcomm_u : U * ε = ε * U := commute_adjoin huc hE.1.1
        have h1 : ε * (1 - ε') = ε := by rw [mul_sub, mul_one, h0, sub_zero]
        have hmat_eU : U * ε = ε := by
          calc U * ε = U * (ε * (1 - ε')) := by rw [h1]
            _ = (U * ε) * (1 - ε') := by rw [mul_assoc]
            _ = (ε * U) * (1 - ε') := by rw [hcomm_u]
            _ = ε * (U * (1 - ε')) := by rw [mul_assoc]
            _ = ε * (1 - ε') := by rw [hfixe]
            _ = ε := h1
        have hmat_one : U = 1 := by
          calc U = U * 1 := by rw [mul_one]
            _ = U * (ε + (1 - ε)) := by rw [add_sub_cancel]
            _ = U * ε + U * (1 - ε) := by rw [mul_add]
            _ = ε + (1 - ε) := by rw [hmat_eU, hfixJ]
            _ = 1 := by rw [add_sub_cancel]
        have hGL : (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
            (minusCoeffs 2 f).2)) u = 1 := by
          apply Units.ext
          exact hmat_one
        have hu1 : u = 1 := nbrpom_spinMatrix_injective n f (by
          calc (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
              (minusCoeffs 2 f).2)) u = 1 := hGL
            _ = (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
              (minusCoeffs 2 f).2)) 1 := (map_one _).symm)
        exact Subgroup.mem_bot.mpr hu1
      have hnt : Nontrivial ↥J' :=
        CFSG.ComponentClassification.Quasisimple.nontrivial hB.2.2.2.1.2.2
      exact (Subgroup.nontrivial_iff_ne_bot J').mp hnt hJ'bot
    · exact heq
  exact ⟨S', K', ε', e', hSe, ⟨hSU', hS', hodd', hK'comp, hK'map⟩, ⟨hε', hK'ε'⟩, he', he'ε',
    hsplit', hJK', htie⟩

end CFSG.StandardType.ClassicalPosition.NbrLeaf

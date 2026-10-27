module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentW
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10Exc
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Split
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Pos
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Norm
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Real
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP8dSmall
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9UTwA
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentC
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentCOrth
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentS

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType

theorem classical_D6_or_signedB6
    {G : Type} [Group G] [Finite G]
    {S : ℕ → LargeEvenLabel → Prop} {Bs K : Subgroup G} {z : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : n = 7 ∨ n = 8) (hz : z ∈ Bs)
    (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNT : GGNoTransvection 3 Bs)
    (hS : ∀ lab, S 3 lab → (lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨
      lab.tag = .twD) ∧ lab.n = 1)
    (hK : GGInnerDiagOnLabel S 3 Bs K) (h2loc : CFSG.Open.twoLocalPrimeRank 3 G ≤ n)
    (W : Subgroup (MulAut ↥(ggGamma K hN).range))
    (hW : W ≤ ggAutomizer (⊤ : Subgroup (MulAut ↥K)) (ggGamma K hN).range)
    (hWord : Nat.card W = if n = 7 then 23040 else 2903040) :
    n = 7 ∧ (GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) 3 Bs K ∨
      GGSignedB6At Bs z) := by
  have hTypes : ∀ lab, S 3 lab →
      (lab.tag = .A ∧ lab.n = 1) ∨
        (((lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1) ∨
          ((lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1)) := by
    intro lab hs
    obtain ⟨ht, hf⟩ := hS lab hs
    rcases ht with hA | hB | hC | hD | hTwD
    · exact Or.inl ⟨hA, hf⟩
    · exact Or.inr (Or.inl ⟨Or.inl hB, hf⟩)
    · exact Or.inr (Or.inl ⟨Or.inr hC, hf⟩)
    · exact Or.inr (Or.inr ⟨Or.inl hD, hf⟩)
    · exact Or.inr (Or.inr ⟨Or.inr hTwD, hf⟩)
  have hCases := hK.mono_label
    (T := fun _ lab => (lab.tag = .A ∧ lab.n = 1) ∨
      (((lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1) ∨
        ((lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1))) hTypes
  rcases hCases.elim_or with hA | hRest
  · obtain ⟨hn7, hSigned⟩ := n_eq_seven_signedB6At_of_linear_label
      hBs hcard hn hz hz1 hN hNK hker hBstar (fun _ h => h) hA W hW hWord
    exact ⟨hn7, Or.inr hSigned⟩
  · rcases hRest.elim_or with hBC | hOrth
    · obtain ⟨hn7, hSigned⟩ := n_eq_seven_signedB6At_of_sp_label
        hBs hcard hn hz hz1 hN hNK hker hBstar (fun _ h => h) hBC W hW hWord
      exact ⟨hn7, Or.inr hSigned⟩
    · exact classical_D6_or_signedB6_of_orth_label hBs hcard hn hz hz1 hN hNK hker
        hBstar hNT (fun _ h => h) hOrth h2loc W hW hWord

@[expose] def GGNoSignedB6AtInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {Bs : Subgroup G} (M : GGFrameModelData Bs 7),
    Nat.card M.A = 2903040 → (∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS 7))) →
    IsElemAbelian 3 Bs → GGNoTransvection 3 Bs → ∀ {x z : G}, x ∈ Bs → x ≠ 1 →
    Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) ≤ 103680 →
    M.IsRoot z → GGSignedB6At Bs z → False

theorem ggNoSignedB6AtInput_holds :
    GGNoSignedB6AtInput := by
  intro G _ _ Bs M hA hgen hBs hNT x z hx hx1 hHx hz hsgn
  exact false_of_signedB6At M hA hgen hBs hNT hx hx1 hHx hz hsgn

private theorem glueIdentAux_restr {G : Type} [Group G] {Bs K : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop} {T : LargeEvenLabel → Prop} {lab : LargeEvenLabel}
    (hperf : commutator ↥K = ⊤) (hlab : LargeEvenInLambda2 lab)
    (hraw : CFSG.StandardType.LargeEvenRawDatum lab fun R _ I _ => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R,
        S 3 lab ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hST : S 3 lab → T lab) : GGInnerDiagOnLabel (fun _ lab => T lab) 3 Bs K := by
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hS, hBsN, hbs⟩
  exact ⟨hs, hna, θ, hST hS, hBsN, hbs⟩

theorem glueTwo
    {G : Type} [Group G] [Finite G] {B Bs K : Subgroup G} {z : G} {n : ℕ}
    (M : GGFrameModelData Bs n) (hn : n = 7 ∨ n = 8)
    (hA : Nat.card M.A = if n = 7 then 2903040 else 696729600)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS n)))
    (hB : LargeEvenIsBmax 3 B) (hBBs : B ≤ Bs) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ n) (hNT : GGNoTransvection 3 Bs)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hz : M.IsRoot z) (hKz : K ≤ Subgroup.centralizer ({z} : Set G))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.n = 1) 3 Bs K)
    (hHx : n = 7 → ∃ x ∈ Bs, x ≠ 1 ∧
      Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) ≤ 103680) :
    (n = 7 ∧ GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) 3 Bs K) ∨
      GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∧ lab.n = 1) 3 Bs K := by
  have hGS : GGNoSignedB6AtInput := ggNoSignedB6AtInput_holds
  have hzBs : z ∈ Bs := hz.1
  have hz1 : z ≠ 1 := hz.2.1
  have hn7 : 7 ≤ n := by rcases hn with h | h <;> omega
  have h2loc : CFSG.Open.twoLocalPrimeRank 3 G ≤ n :=
    twoLocalPrimeRank_le_of_bmax_le hB hBBs hcard
  have hrank : LargeEvenTwoLocalRank 3 G ≤ n := h2loc
  obtain ⟨W, hW, hWcard⟩ :=
    exists_weyl_le_automizer_of_isRoot M hn hA hgen hBs hNT hz hN hNK hker
  have h23040 : 23040 ∣ Nat.card W := by
    rw [hWcard]
    split_ifs with h7
    · exact dvd_rfl
    · norm_num
  have hlow : 23040 ∣ Nat.card
      (ggAutomizer (⊤ : Subgroup (MulAut ↥K)) (ggGamma K hN).range) :=
    h23040.trans (Subgroup.card_dvd_of_le hW)
  obtain ⟨hperf, lab, hlab2, hraw⟩ := hK
  cases htag : lab.tag
  case A =>
    have hKA : GGInnerDiagOnLabel (fun _ lab => lab.tag = .A ∧ lab.n = 1) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab =>
        lab.tag = .A ∧ lab.n = 1) hperf hlab2 hraw (fun hS => ⟨htag, hS⟩)
    obtain ⟨rfl, hsgn⟩ := n_eq_seven_signedB6At_of_linear_label
      hBs hcard hn hzBs hz1 hN hNK hker hBstar (fun _ h => h) hKA W hW hWcard
    exfalso
    obtain ⟨x, hxBs, hx1, hHxle⟩ := hHx rfl
    exact hGS M (by simpa using hA) hgen hBs hNT hxBs hx1 hHxle hz hsgn
  case twA =>
    have hKtwA : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.n = 1) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab =>
        lab.tag = .twA ∧ lab.n = 1) hperf hlab2 hraw (fun hS => ⟨htag, hS⟩)
    exact (P9_Wa_twA_false hBs hcard hn hzBs hz1 hN hker hBstar
      (fun lab' h => ⟨h.1, h.2⟩) hKtwA h2loc W hW hWcard).elim
  case B =>
    have hKB : GGInnerDiagOnLabel (fun _ lab => lab.tag = .B ∧ lab.n = 1) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab =>
        lab.tag = .B ∧ lab.n = 1) hperf hlab2 hraw (fun hS => ⟨htag, hS⟩)
    obtain ⟨rfl, hsgn⟩ := n_eq_seven_signedB6At_of_sp_label
      hBs hcard hn hzBs hz1 hN hNK hker hBstar
      (fun _ h => ⟨Or.inl h.1, h.2⟩) hKB W hW hWcard
    exfalso
    obtain ⟨x, hxBs, hx1, hHxle⟩ := hHx rfl
    exact hGS M (by simpa using hA) hgen hBs hNT hxBs hx1 hHxle hz hsgn
  case C =>
    have hKC : GGInnerDiagOnLabel (fun _ lab => lab.tag = .C ∧ lab.n = 1) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab =>
        lab.tag = .C ∧ lab.n = 1) hperf hlab2 hraw (fun hS => ⟨htag, hS⟩)
    obtain ⟨rfl, hsgn⟩ := n_eq_seven_signedB6At_of_sp_label
      hBs hcard hn hzBs hz1 hN hNK hker hBstar
      (fun _ h => ⟨Or.inr h.1, h.2⟩) hKC W hW hWcard
    exfalso
    obtain ⟨x, hxBs, hx1, hHxle⟩ := hHx rfl
    exact hGS M (by simpa using hA) hgen hBs hNT hxBs hx1 hHxle hz hsgn
  case D =>
    have hKD : GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.n = 1) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab =>
        lab.tag = .D ∧ lab.n = 1) hperf hlab2 hraw (fun hS => ⟨htag, hS⟩)
    obtain ⟨rfl, hres⟩ := classical_D6_or_signedB6 hBs hcard hn hzBs hz1 hN hNK hker hBstar
      hNT (fun lab' h => ⟨Or.inr (Or.inr (Or.inr (Or.inl h.1))), h.2⟩) hKD h2loc W hW hWcard
    rcases hres with hD | hsgn
    · exact Or.inl ⟨rfl, hD⟩
    · exfalso
      obtain ⟨x, hxBs, hx1, hHxle⟩ := hHx rfl
      exact hGS M (by simpa using hA) hgen hBs hNT hxBs hx1 hHxle hz hsgn
  case twD =>
    have hKtwD : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twD ∧ lab.n = 1) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab =>
        lab.tag = .twD ∧ lab.n = 1) hperf hlab2 hraw (fun hS => ⟨htag, hS⟩)
    obtain ⟨rfl, hres⟩ := classical_D6_or_signedB6 hBs hcard hn hzBs hz1 hN hNK hker hBstar
      hNT (fun lab' h => ⟨Or.inr (Or.inr (Or.inr (Or.inr h.1))), h.2⟩) hKtwD h2loc W hW hWcard
    rcases hres with hD | hsgn
    · exact Or.inl ⟨rfl, hD⟩
    · exfalso
      obtain ⟨x, hxBs, hx1, hHxle⟩ := hHx rfl
      exact hGS M (by simpa using hA) hgen hBs hNT hxBs hx1 hHxle hz hsgn
  case E6 =>
    have hKE6 : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ lab.n = 1) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab =>
        lab.tag = .E6 ∧ lab.n = 1) hperf hlab2 hraw (fun hS => ⟨htag, hS⟩)
    exact (p10g_E6_ambient hBs hcard hn7 hzBs hz1 hN hker hBstar hKE6).elim
  case twE6 =>
    have hKtw : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6 ∧ lab.n = 1) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab =>
        lab.tag = .twE6 ∧ lab.n = 1) hperf hlab2 hraw (fun hS => ⟨htag, hS⟩)
    have htw : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs K := by
      obtain ⟨hperf', lab', hlab', hraw'⟩ := hKtw
      refine ⟨hperf', lab', hlab', ?_⟩
      refine largeEvenRawDatum_mono (fun R _ I F h => ?_) hraw'
      obtain ⟨hs, hna', θ', ⟨ht, hn1⟩, hrest⟩ := h
      refine ⟨hs, hna', θ', ⟨?_, hrest⟩⟩
      obtain ⟨t', r', m'⟩ := lab'
      dsimp only at ht hn1
      subst ht
      subst hn1
      have hr : r' = 0 := hlab'.2
      subst hr
      rfl
    obtain ⟨e, hreal⟩ := p10_twE6_realization hBs hcard hn7 hzBs hz1 hN hker hBstar htw
    have hdvd : Nat.card (ggAutomizer (⊤ : Subgroup (MulAut ↥K))
        (ggGamma K hN).range) ∣ 103680 :=
      p10i_twE6_normalizer_bound (ggGamma K hN).range e hreal
    have h23 : 23040 ∣ 103680 := hlow.trans hdvd
    exfalso
    exact absurd h23 (by norm_num)
  case E7 =>
    exact Or.inr (glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab =>
      lab.tag = .E7 ∧ lab.n = 1) hperf hlab2 hraw (fun hS => ⟨htag, hS⟩))
  case E8 =>
    have hKE8 : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E8 ∧ lab.n = 1) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab =>
        lab.tag = .E8 ∧ lab.n = 1) hperf hlab2 hraw (fun hS => ⟨htag, hS⟩)
    rcases hn with rfl | rfl
    · exfalso
      have hE8 : LargeEvenMarking ↥K fun lab _ _ _ _ _ => lab.tag = .E8 :=
        largeEvenMarking_mono (fun lab R _ I F θ h => h.1.1) hKE8
      have hz3 : z ^ 3 = 1 := hBs.2 z hzBs
      have h8 := P10ef_E8_twoLocalRank hKz hz3 hz1 hE8
      omega
    · exact (P10d_E8_not_eight hBs hcard hzBs hz1 hN hker hBstar hKE8).elim
  case F4 =>
    have hKsm : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧
        (lab.tag = .F4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
          lab.tag = .B2der ∨ lab.tag = .G2der)) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab => lab.n = 1 ∧
        (lab.tag = .F4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
          lab.tag = .B2der ∨ lab.tag = .G2der)) hperf hlab2 hraw
        (fun hS => ⟨hS, Or.inl htag⟩)
    exact (p8d_small_label_exclusion hBs hcard hn7 hzBs hz1 hN hker hBstar hKsm).elim
  case twF4der =>
    have hKsm : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧
        (lab.tag = .F4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
          lab.tag = .B2der ∨ lab.tag = .G2der)) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab => lab.n = 1 ∧
        (lab.tag = .F4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
          lab.tag = .B2der ∨ lab.tag = .G2der)) hperf hlab2 hraw
        (fun hS => ⟨hS, Or.inr (Or.inl htag)⟩)
    exact (p8d_small_label_exclusion hBs hcard hn7 hzBs hz1 hN hker hBstar hKsm).elim
  case triD4 =>
    have hKsm : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧
        (lab.tag = .F4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
          lab.tag = .B2der ∨ lab.tag = .G2der)) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab => lab.n = 1 ∧
        (lab.tag = .F4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
          lab.tag = .B2der ∨ lab.tag = .G2der)) hperf hlab2 hraw
        (fun hS => ⟨hS, Or.inr (Or.inr (Or.inl htag))⟩)
    exact (p8d_small_label_exclusion hBs hcard hn7 hzBs hz1 hN hker hBstar hKsm).elim
  case B2der =>
    have hKsm : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧
        (lab.tag = .F4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
          lab.tag = .B2der ∨ lab.tag = .G2der)) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab => lab.n = 1 ∧
        (lab.tag = .F4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
          lab.tag = .B2der ∨ lab.tag = .G2der)) hperf hlab2 hraw
        (fun hS => ⟨hS, Or.inr (Or.inr (Or.inr (Or.inl htag)))⟩)
    exact (p8d_small_label_exclusion hBs hcard hn7 hzBs hz1 hN hker hBstar hKsm).elim
  case G2der =>
    have hKsm : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧
        (lab.tag = .F4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
          lab.tag = .B2der ∨ lab.tag = .G2der)) 3 Bs K :=
      glueIdentAux_restr (S := fun _ lab => lab.n = 1) (T := fun lab => lab.n = 1 ∧
        (lab.tag = .F4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
          lab.tag = .B2der ∨ lab.tag = .G2der)) hperf hlab2 hraw
        (fun hS => ⟨hS, Or.inr (Or.inr (Or.inr (Or.inr htag)))⟩)
    exact (p8d_small_label_exclusion hBs hcard hn7 hzBs hz1 hN hker hBstar hKsm).elim
  case G2 =>
    exfalso
    obtain ⟨R, hR, I, F, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
    obtain ⟨-, -, -, hSn, -, -⟩ := hQ
    have hn : lab.n = 1 := hSn
    have h2 : 2 ≤ lab.n := by
      have h := hlab2
      simp only [LargeEvenInLambda2, htag] at h
      exact h.2.2
    omega
  case twB2 =>
    exfalso
    obtain ⟨R, hR, I, F, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
    obtain ⟨-, -, -, hSn, -, -⟩ := hQ
    have hn : lab.n = 1 := hSn
    have h3 : 3 ≤ lab.n := by
      have h := hlab2
      simp only [LargeEvenInLambda2, htag] at h
      exact h.2.2.2
    omega
  case twF4 =>
    exfalso
    obtain ⟨R, hR, I, F, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
    obtain ⟨-, -, -, hSn, -, -⟩ := hQ
    have hn : lab.n = 1 := hSn
    have h3 : 3 ≤ lab.n := by
      have h := hlab2
      simp only [LargeEvenInLambda2, htag] at h
      exact h.2.2.2
    omega

end CFSG.StandardType.FrameRoute

end

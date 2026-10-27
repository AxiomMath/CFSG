module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSEnds
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNamedInputs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA3
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA3E7
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteG0
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteOrder

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

@[expose] def FSPoint {G : Type} [Group G] [Finite G] (B Bs : Subgroup G)
    (P : LargeEvenLabel → Prop) : Prop :=
  Nat.card Bs = 3 * Nat.card B ∧
    ∃ y ∈ B, ∃ K : Subgroup G, LargeEvenSStar 3 B y K ∧
      (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧ Subgroup.center K = ⊥ ∧
      LargeEvenMarking K (fun lab _ _ _ _ _ => P lab)

section E7Aux

open CFSG.LieType.Chevalley CFSG.LieType.RootSystem

private theorem psi_isMaxElemAb3_of_ggBstar {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    (h : GGBstar 3 B Bs) {y : G} (hy : y ∈ B) :
    IsMaxElemAb3 (Subgroup.centralizer ({y} : Set G)) Bs := by
  refine ⟨?_, h.2.1, ?_⟩
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact congrArg Subtype.val (h.2.1.1.is_comm.comm ⟨y, h.1 hy⟩ ⟨b, hb⟩)
  · intro E' hE'C hE' hBsE'
    refine le_antisymm (fun e he => ?_) hBsE'
    refine h.2.2.2 e ?_ (hE'.2 e he)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hE'.1.is_comm.comm ⟨b, hBsE' hb⟩ ⟨e, he⟩)

private theorem psi_orderOf_eq_three_of_isBmax {G : Type} [Group G] [Finite G] {B : Subgroup G}
    (h : LargeEvenIsBmax 3 B) {y : G} (hy : y ∈ B) (hne : y ≠ 1) : orderOf y = 3 := by
  have hdvd : orderOf y ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (h.1.2 y hy)
  have hne1 : orderOf y ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd h1 hne1
  · exact h3

private theorem psi_marking_FSLab_of_D61 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hm : LargeEvenMarking K fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) :
    LargeEvenMarking K fun lab _ _ _ _ _ => FSLab lab := by
  refine largeEvenMarking_mono (P := fun lab _ _ _ _ _ =>
      lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1)
    (P' := fun lab _ _ _ _ _ => FSLab lab) ?_ hm
  intro lab R _ I F θ h
  exact ⟨h.2.2, Or.inl ⟨h.1, h.2.1⟩⟩

private theorem psi_cyclic_of_sStar {G : Type} [Group G] [Finite G] {B : Subgroup G} {y : G}
    {K : Subgroup G} (h : LargeEvenSStar 3 B y K) :
    ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S :=
  h.2.2.2.2

private theorem psi_card_coxeterE7 :
    Nat.card (CoxeterMatrix.E₇).Group = 2903040 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E7 = CartanMatrix.E 7 := cartanE_eq 7
  have hmat : CoxeterMatrix.E₇ = coxeterMatrix (isFiniteType_cartan .E7) := by
    have h := coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E7)
      (M := CoxeterMatrix.E₇) (isFiniteType_cartan .E7) (hc.symm ▸ ggIntCartan_E₇)
    exact h.symm
  have hgroup : WeylGroup .E7 = (CoxeterMatrix.E₇).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (WeylGroup .E7) = Nat.card (CoxeterMatrix.E₇).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact CFSG.StandardType.NoOffExc.card_weyl_E7

private theorem psi_weylOrder_lt_card_automizer
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {A₀ : Subgroup (MulAut ↥Bs)}
    (e : CoxeterMatrix.E₇.Group ≃* ↥A₀) (hA₀ : A₀ ≤ ggAutomizer ⊤ Bs) :
    2 ^ 7 * (Nat.factorial 7) < Nat.card (ggAutomizer ⊤ Bs) := by
  calc 2 ^ 7 * (Nat.factorial 7) = 645120 := by norm_num
    _ < 2903040 := by norm_num
    _ = Nat.card (CoxeterMatrix.E₇).Group := (psi_card_coxeterE7).symm
    _ = Nat.card ↥A₀ := Nat.card_congr e.toEquiv
    _ ≤ Nat.card (ggAutomizer ⊤ Bs) := Subgroup.card_le_of_le hA₀

end E7Aux

theorem psi_E7_of_fsPoint_of_le
    (hAC : FS81ThmACRankInput) (hLSS : LSS92TorusMaxInput)
    {G : Type} [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) {A₀ : Subgroup (MulAut ↥Bs)}
    (e : CoxeterMatrix.E₇.Group ≃* ↥A₀) (hA₀G0 : A₀ ≤ ggAutomizer (ggG0 3 B x L D J) Bs)
    (hcard : Nat.card Bs = 3 ^ 7)
    (hA4 : ∀ y : G, y ∈ B → y ≠ 1 → ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) ∧
      g * y * g⁻¹ ∉ Subgroup.zpowers y)
    (hFS : FSPoint B Bs fun lab => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) :
    ∃ ψ : (ggU .E7 0 1).K →* G, ψ.ker ≤ Subgroup.center (ggU .E7 0 1).K ∧
      ψ.range = ggG0 3 B x L D J := by
  obtain ⟨hcBs, y, hyB, K, hSStar, hKnorm, hKcenter, hKmark⟩ := hFS
  have hsimple : IsSimpleGroup G := hR.1.1.1
  have hchar : IsCharTwoType G := hR.1.1.2.2.2.1
  have hBstar : GGBstar 3 B Bs := hR.1.2.1
  have hbmax : LargeEvenIsBmax 3 B := hR.1.1.2.2.2.2.2.2.1.1
  have hKle : K ≤ Subgroup.centralizer ({y} : Set G) := hSStar.2.2.2.1.1
  have hFSLab : LargeEvenMarking K fun lab _ _ _ _ _ => FSLab lab :=
    psi_marking_FSLab_of_D61 hKmark
  have hA2 := psi_cyclic_of_sStar hSStar
  have hy1 : y ≠ 1 := hSStar.2.2.1
  have horder : orderOf y = 3 :=
    psi_orderOf_eq_three_of_isBmax hbmax hyB hy1
  have hBcard : Nat.card B = 3 ^ (5 + 1) := by
    have h : 3 * Nat.card B = 3 * 3 ^ (5 + 1) := by
      rw [← hcBs, hcard]
      norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hA3 : twoLocalPrimeRank 3 (Subgroup.centralizer ({y} : Set G)) = twoLocalPrimeRank 3 G :=
    twoLocalPrimeRank_centralizer_eq_of_local hbmax hBcard hyB hy1 hKle hKcenter
      (exists_twoLocal_three_of_D6 hKcenter hKmark)
  have hA4' : ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) ∧
      g * y * g⁻¹ ∉ Subgroup.zpowers y :=
    hA4 y hyB hy1
  have hA : FS81HypA y K :=
    ⟨horder, hKle, hKnorm, hKcenter, hFSLab, hA2, hA3, hA4'⟩
  have hmax : IsMaxElemAb3 (Subgroup.centralizer ({y} : Set G)) Bs :=
    psi_isMaxElemAb3_of_ggBstar hBstar hyB
  have hyBs : y ∈ Bs := hBstar.1 hyB
  have haut : 2 ^ 7 * Nat.factorial 7 < Nat.card (ggAutomizer ⊤ Bs) :=
    psi_weylOrder_lt_card_automizer e (hA₀G0.trans (ggAutomizer_mono Bs le_top))
  have hIsEm : IsEm 7 (⊤ : Subgroup G) :=
    hAC G hsimple hchar y K Bs 7 hA hmax hyBs hcard (by norm_num) haut
  obtain ⟨ψ, hsurj, hker⟩ := ggPsi_E7 G hsimple hIsEm
  have hGtop : ggG0 3 B x L D J = ⊤ :=
    ggG0_eq_top_of_torusInputs_of_le CoxeterMatrix.E₇ 7 (by norm_num) hLSS
      (fun G _ _ hEm hs E hE hc => lss92_torus_order_E7 G hEm hs E hE hc)
      hR e hA₀G0 hIsEm hcard
  exact ⟨ψ, hker, by rw [hGtop, MonoidHom.range_eq_top.mpr hsurj]⟩

section E8Aux

open CFSG.LieType.Chevalley CFSG.LieType.RootSystem

private theorem psi_marking_FSLab_of_E8 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hm : LargeEvenMarking K fun lab _ _ _ _ _ =>
      ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) :
    LargeEvenMarking K fun lab _ _ _ _ _ => FSLab lab := by
  refine largeEvenMarking_mono (P := fun lab _ _ _ _ _ =>
      ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1)
    (P' := fun lab _ _ _ _ _ => FSLab lab) ?_ hm
  intro lab R _ I F θ h
  exact ⟨h.2, h.1.elim (fun h1 => Or.inr (Or.inl h1)) (fun h1 => Or.inr (Or.inr h1))⟩

private theorem psi_marking_cases {G : Type} [Group G] {K : Subgroup G}
    (hm : LargeEvenMarking K fun lab _ _ _ _ _ =>
      ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) :
    LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) ∨
    LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .E7 ∧ lab.rank = 0 ∧ lab.n = 1) := by
  obtain ⟨hc, lab, hlab, hraw⟩ := hm
  have hP : ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1 := by
    obtain ⟨R, _, I, F, -, -, θ, hθ⟩ := largeEvenRawDatum_exists hraw
    exact hθ
  obtain ⟨hdisj, hn⟩ := hP
  rcases hdisj with ⟨ht, hr⟩ | ⟨ht, hr⟩
  · left
    refine ⟨hc, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, -⟩
    exact ⟨hs, hna, θ, ht, hr, hn⟩
  · right
    refine ⟨hc, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, -⟩
    exact ⟨hs, hna, θ, ht, hr, hn⟩

private theorem psi_card_coxeterE8 :
    Nat.card (CoxeterMatrix.E₈).Group = 696729600 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E8 = CartanMatrix.E 8 := cartanE_eq 8
  have hmat : CoxeterMatrix.E₈ = coxeterMatrix (isFiniteType_cartan .E8) := by
    have h := coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E8)
      (M := CoxeterMatrix.E₈) (isFiniteType_cartan .E8) (hc.symm ▸ ggIntCartan_E₈)
    exact h.symm
  have hgroup : WeylGroup .E8 = (CoxeterMatrix.E₈).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (WeylGroup .E8) = Nat.card (CoxeterMatrix.E₈).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact CFSG.StandardType.NoOffExc.card_weyl_E8

private theorem psi_weylOrder_lt_card_automizer_E8
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {A₀ : Subgroup (MulAut ↥Bs)}
    (e : CoxeterMatrix.E₈.Group ≃* ↥A₀) (hA₀ : A₀ ≤ ggAutomizer ⊤ Bs) :
    2 ^ 8 * (Nat.factorial 8) < Nat.card (ggAutomizer ⊤ Bs) := by
  calc 2 ^ 8 * (Nat.factorial 8) = 10321920 := by norm_num
    _ < 696729600 := by norm_num
    _ = Nat.card (CoxeterMatrix.E₈).Group := (psi_card_coxeterE8).symm
    _ = Nat.card ↥A₀ := Nat.card_congr e.toEquiv
    _ ≤ Nat.card (ggAutomizer ⊤ Bs) := Subgroup.card_le_of_le hA₀

end E8Aux

theorem psi_E8_of_fsPoint_of_le
    (hAC : FS81ThmACRankInput) (hLSS : LSS92TorusMaxInput)
    {G : Type} [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) {A₀ : Subgroup (MulAut ↥Bs)}
    (e : CoxeterMatrix.E₈.Group ≃* ↥A₀) (hA₀G0 : A₀ ≤ ggAutomizer (ggG0 3 B x L D J) Bs)
    (hcard : Nat.card Bs = 3 ^ 8)
    (hA4 : ∀ y : G, y ∈ B → y ≠ 1 → ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) ∧
      g * y * g⁻¹ ∉ Subgroup.zpowers y)
    (hFS : FSPoint B Bs fun lab =>
      ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) :
    ∃ ψ : (ggU .E8 0 1).K →* G, ψ.ker ≤ Subgroup.center (ggU .E8 0 1).K ∧
      ψ.range = ggG0 3 B x L D J := by
  obtain ⟨hcBs, y, hyB, K, hSStar, hKnorm, hKcenter, hKmark⟩ := hFS
  have hsimple : IsSimpleGroup G := hR.1.1.1
  have hchar : IsCharTwoType G := hR.1.1.2.2.2.1
  have hBstar : GGBstar 3 B Bs := hR.1.2.1
  have hbmax : LargeEvenIsBmax 3 B := hR.1.1.2.2.2.2.2.2.1.1
  have hKle : K ≤ Subgroup.centralizer ({y} : Set G) := hSStar.2.2.2.1.1
  have hFSLab : LargeEvenMarking K fun lab _ _ _ _ _ => FSLab lab :=
    psi_marking_FSLab_of_E8 hKmark
  have hA2 := psi_cyclic_of_sStar hSStar
  have hy1 : y ≠ 1 := hSStar.2.2.1
  have horder : orderOf y = 3 :=
    psi_orderOf_eq_three_of_isBmax hbmax hyB hy1
  have hBcard : Nat.card B = 3 ^ (6 + 1) := by
    have h : 3 * Nat.card B = 3 * 3 ^ (6 + 1) := by
      rw [← hcBs, hcard]
      norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hA3 : twoLocalPrimeRank 3 (Subgroup.centralizer ({y} : Set G)) = twoLocalPrimeRank 3 G := by
    rcases psi_marking_cases hKmark with hm | hm
    · exact twoLocalPrimeRank_centralizer_eq_of_local hbmax hBcard hyB hy1 hKle hKcenter
        (exists_twoLocal_three_of_twD7 hKcenter hm)
    · exact twoLocalPrimeRank_centralizer_eq_of_local hbmax hBcard hyB hy1 hKle hKcenter
        (exists_twoLocal_three_of_E7 hKcenter hm)
  have hA4' : ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) ∧
      g * y * g⁻¹ ∉ Subgroup.zpowers y :=
    hA4 y hyB hy1
  have hA : FS81HypA y K :=
    ⟨horder, hKle, hKnorm, hKcenter, hFSLab, hA2, hA3, hA4'⟩
  have hmax : IsMaxElemAb3 (Subgroup.centralizer ({y} : Set G)) Bs :=
    psi_isMaxElemAb3_of_ggBstar hBstar hyB
  have hyBs : y ∈ Bs := hBstar.1 hyB
  have haut : 2 ^ 8 * Nat.factorial 8 < Nat.card (ggAutomizer ⊤ Bs) :=
    psi_weylOrder_lt_card_automizer_E8 e (hA₀G0.trans (ggAutomizer_mono Bs le_top))
  have hIsEm : IsEm 8 (⊤ : Subgroup G) :=
    hAC G hsimple hchar y K Bs 8 hA hmax hyBs hcard (by norm_num) haut
  obtain ⟨ψ, hsurj, hker⟩ := ggPsi_E8 G hsimple hIsEm
  have hGtop : ggG0 3 B x L D J = ⊤ :=
    ggG0_eq_top_of_torusInputs_of_le CoxeterMatrix.E₈ 8 (by norm_num) hLSS
      (fun G _ _ hEm hs E hE hc => lss92_torus_order_E8 G hEm hs E hE hc)
      hR e hA₀G0 hIsEm hcard
  exact ⟨ψ, hker, by rw [hGtop, MonoidHom.range_eq_top.mpr hsurj]⟩

end CFSG.StandardType.FrameRoute

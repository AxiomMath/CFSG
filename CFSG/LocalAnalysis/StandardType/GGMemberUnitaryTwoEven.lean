module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2MemberQuotPos
public import CFSG.LocalAnalysis.StandardType.GGNsq2MemberFix
public import CFSG.LocalAnalysis.StandardType.GGNsq2DetInv
public import CFSG.LocalAnalysis.StandardType.GGNsq2PairLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitPairOfPosition
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPair
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixType
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1Aux
import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrSixEdge
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2
import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

open NsQuot

private lemma twoCentral_eq_one_of_center_eq_bot_ev2 {G : Type} [Group G]
    {X : Subgroup G} (hZ : Subgroup.center ↥X = ⊥) {z : G} (hz : z ∈ twoCentral X) : z = 1 := by
  have hzc : (⟨z, twoCentral_le X hz⟩ : ↥X) ∈ Subgroup.center ↥X :=
    Subgroup.mem_center_iff.2 fun l => Subtype.ext (twoCentral_central hz l l.2)
  rw [hZ, Subgroup.mem_bot] at hzc
  exact congrArg Subtype.val hzc

private lemma congr_ne_ev2 {A A' : Type} [Group A] [Group A'] (σ : A ≃* A')
    {r r' : MulAut A} (hne : r * r' ≠ r' * r) :
    MulAut.congr σ r * MulAut.congr σ r' ≠ MulAut.congr σ r' * MulAut.congr σ r := by
  intro h
  apply hne
  apply (MulAut.congr σ).injective
  rw [map_mul, map_mul]
  exact h

private lemma rankOne_card_ev2
    {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] [Finite Q]
    {X B Bs N : Subgroup G} {f : ↥N →* Q}
    {K : Type} [Field K] [Finite K] [CharP K 2] {ψ : Su K 2 1 6 →* Q}
    (hlocal : GGNSLocalHyp 3 (img _ f B) (img _ f Bs) K 1 6 ψ)
    (ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (img _ f X) (img _ f Bs)))
    (hεrefl : ∀ a b : Fin 6, a ≠ b → GGIsReflection 3
      ((ε (Equiv.swap a b) : ↥(ggAutomizer (img _ f X) (img _ f Bs))) : MulAut ↥(img _ f Bs)))
    (hεblock : ∀ a b : Fin 6, a ≠ b →
      ggRankOneIn (img _ f X) (img _ f Bs)
        ((ε (Equiv.swap a b) : ↥(ggAutomizer (img _ f X) (img _ f Bs))) :
          MulAut ↥(img _ f Bs)) = (ggSuPairBlock K 2 1 6 a b).map ψ)
    {ρ : MulAut ↥(img _ f Bs)}
    (hρA : ρ ∈ ggAutomizer (img _ f X) (img _ f Bs)) (hρrefl : GGIsReflection 3 ρ) :
    Nat.card ↥(ggRankOneIn (img _ f X) (img _ f Bs) ρ) = 6 := by
  obtain ⟨a, b, hab, hρeq⟩ := ggMUR1_refl_eq_swap Nat.prime_three (by norm_num)
    hlocal.bstar.2.1 ε hεrefl hρA hρrefl
  rw [hρeq, hεblock a b hab]
  rw [ggPhanNSAPairAux_card_map_pair ψ hlocal.card hlocal.ker (by norm_num : 3 ≤ 6) hab]
  norm_num

private lemma rankTwo_le_ev2
    {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
    {X Bs N : Subgroup G} {f : ↥N →* Q}
    (hD : Datum 3 N f X Bs (twoCentral X))
    {r r' : MulAut ↥Bs}
    (hfix : ∀ z ∈ twoCentral X,
      (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs r', h * z = z * h) → z = 1) :
    QTwo.ggRankTwoIn (img _ f X) (img _ f Bs) (MulAut.congr hD.tau r) (MulAut.congr hD.tau r') ≤
      img _ f (X ⊓ Subgroup.centralizer
        ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G)) := by
  rw [← hD.img_rankTwoIn hfix]
  exact img_mono (ggOTwoPrime_le _)

private lemma hfix_ev2
    {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] [Finite Q]
    {X B Bs : Subgroup G} {f : ↥(Subgroup.normalizer (X : Set G)) →* Q}
    {K : Type} [Field K] [Finite K] [CharP K 2] {ψ : Su K 2 1 6 →* Q}
    (hU : GGU62OuterDiagInput)
    (hD : Datum 3 (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X))
    (hperf : Group.IsPerfect ↥X) (hK4 : Nat.card K = 4)
    (hlocal : GGNSLocalHyp 3 (img _ f B) (img _ f Bs) K 1 6 ψ)
    (hrange : ψ.range = img _ f X)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ (img _ f Bs))
    (hC3 : Nat.card ↥(img _ f Bs ⊓ Subgroup.centralizer (ψ.range : Set Q)) ≤ 3)
    (h3pow : 3 ^ 6 ≤ Nat.card ↥Bs ∨ Subgroup.center ↥X = ⊥)
    {r r' : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrA' : r' ∈ ggAutomizer X Bs)
    (hr : GGIsReflection 3 r) (hr' : GGIsReflection 3 r') :
    ∀ z ∈ twoCentral X,
      (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs r', h * z = z * h) → z = 1 := by
  let ρ : MulAut ↥(img _ f Bs) := MulAut.congr hD.tau r
  let ρ' : MulAut ↥(img _ f Bs) := MulAut.congr hD.tau r'
  have hρA : ρ ∈ ggAutomizer (img _ f X) (img _ f Bs) :=
    hD.map_automizer_le (Subgroup.le_normalizer) (Subgroup.mem_map.2 ⟨r, hrA, rfl⟩)
  have hρA' : ρ' ∈ ggAutomizer (img _ f X) (img _ f Bs) :=
    hD.map_automizer_le (Subgroup.le_normalizer) (Subgroup.mem_map.2 ⟨r', hrA', rfl⟩)
  have hρrefl : GGIsReflection 3 ρ := (ggIsReflection_congr_iff hD.tau r).2 hr
  have hρrefl' : GGIsReflection 3 ρ' := (ggIsReflection_congr_iff hD.tau r').2 hr'
  have hρAψ : ρ ∈ ggAutomizer ψ.range (img _ f Bs) := by rw [hrange]; exact hρA
  have hρA'ψ : ρ' ∈ ggAutomizer ψ.range (img _ f Bs) := by rw [hrange]; exact hρA'
  rcases h3pow with h3p | hZ
  · have h3p' : 3 ^ 6 ≤ Nat.card ↥(img _ f Bs) := by
      rw [hD.card_img le_rfl]; exact h3p
    obtain ⟨δ, hδ⟩ := exists_ggNSDetChar hlocal (by norm_num : 2 ^ 1 + 1 ∣ 6)
    obtain ⟨b₁, hb₁fix, hb₁fix', hb₁δ⟩ :=
      ggNSDet_exists_fixed_pair_ne_one hlocal hK4 hd hδ hC3 h3p' hρAψ hρrefl hρA'ψ hρrefl'
    let h₀ : ↥Bs := hD.tau.symm b₁
    have hb₁ : hD.tau h₀ = b₁ := hD.tau.apply_symm_apply b₁
    have hh₀fix : r h₀ = h₀ := by
      apply hD.tau.injective
      rw [← congr_apply_tau hD.tau r h₀, hb₁]
      exact hb₁fix
    have hh₀fix' : r' h₀ = h₀ := by
      apply hD.tau.injective
      rw [← congr_apply_tau hD.tau r' h₀, hb₁]
      exact hb₁fix'
    have hh₀H : (h₀ : G) ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs r' :=
      ⟨Subgroup.mem_map.2 ⟨h₀, hh₀fix, rfl⟩, Subgroup.mem_map.2 ⟨h₀, hh₀fix', rfl⟩⟩
    intro z hz hcz
    exact hD.twoCentral_eq_one_of_det_ne_one hU hperf hlocal.card hlocal hrange hδ
      (by rw [hb₁]; exact hb₁δ) hz (hcz _ hh₀H)
  · intro z hz _
    exact twoCentral_eq_one_of_center_eq_bot_ev2 hZ hz

private lemma commute_ev2
    {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] [Finite Q]
    {X B Bs : Subgroup G} {f : ↥(Subgroup.normalizer (X : Set G)) →* Q}
    {K : Type} [Field K] [Finite K] [CharP K 2] {ψ : Su K 2 1 6 →* Q}
    (hD : Datum 3 (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X))
    (hlocal : GGNSLocalHyp 3 (img _ f B) (img _ f Bs) K 1 6 ψ)
    (ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (img _ f X) (img _ f Bs)))
    (hεrefl : ∀ a b : Fin 6, a ≠ b → GGIsReflection 3
      ((ε (Equiv.swap a b) : ↥(ggAutomizer (img _ f X) (img _ f Bs))) : MulAut ↥(img _ f Bs)))
    (hεblock : ∀ a b : Fin 6, a ≠ b →
      ggRankOneIn (img _ f X) (img _ f Bs)
        ((ε (Equiv.swap a b) : ↥(ggAutomizer (img _ f X) (img _ f Bs))) :
          MulAut ↥(img _ f Bs)) =
      (ggSuPairBlock K 2 1 6 a b).map ψ)
    {r r' : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrA' : r' ∈ ggAutomizer X Bs)
    (hr : GGIsReflection 3 r) (hr' : GGIsReflection 3 r') (hne : r ≠ r')
    (hfix : ∀ z ∈ twoCentral X,
      (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs r', h * z = z * h) → z = 1) :
    r * r' = r' * r →
      ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs r', a * b = b * a := by
  intro hcomm a ha b hb
  let ρ : MulAut ↥(img _ f Bs) := MulAut.congr hD.tau r
  let ρ' : MulAut ↥(img _ f Bs) := MulAut.congr hD.tau r'
  have hρA : ρ ∈ ggAutomizer (img _ f X) (img _ f Bs) :=
    hD.map_automizer_le (Subgroup.le_normalizer) (Subgroup.mem_map.2 ⟨r, hrA, rfl⟩)
  have hρA' : ρ' ∈ ggAutomizer (img _ f X) (img _ f Bs) :=
    hD.map_automizer_le (Subgroup.le_normalizer) (Subgroup.mem_map.2 ⟨r', hrA', rfl⟩)
  have hρrefl : GGIsReflection 3 ρ := (ggIsReflection_congr_iff hD.tau r).2 hr
  have hρrefl' : GGIsReflection 3 ρ' := (ggIsReflection_congr_iff hD.tau r').2 hr'
  have hneρ : ρ ≠ ρ' := fun h => hne ((MulAut.congr hD.tau).injective h)
  have hcommρ : ρ * ρ' = ρ' * ρ := by
    dsimp only [ρ, ρ']
    rw [← map_mul, ← map_mul, hcomm]
  have hpos : GGTableBPosSU 3 (img _ f Bs) (img _ f X) K 1 6 ψ := ⟨ε, hεrefl, hεblock⟩
  have hconcl := ggPairConcl_of_unitary_position (p := 3) Nat.prime_three (by norm_num)
    hlocal.bstar.2.1 hlocal.card (by norm_num) hlocal.ker hpos
    hρA hρA' hρrefl hρrefl' hneρ
  exact hD.commute_lift hfix (hconcl.1 hcommρ) a ha b hb

private lemma pair_ev2
    {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] [Finite Q]
    {X B Bs : Subgroup G} {f : ↥(Subgroup.normalizer (X : Set G)) →* Q}
    {K : Type} [Field K] [Finite K] [CharP K 2] {ψ : Su K 2 1 6 →* Q}
    (hD : Datum 3 (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X))
    (hlocal : GGNSLocalHyp 3 (img _ f B) (img _ f Bs) K 1 6 ψ)
    (hrange : ψ.range = img _ f X)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ (img _ f Bs))
    (ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (img _ f X) (img _ f Bs)))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)) (s : ↥(img _ f Bs)),
      ((((ε σ : ↥(ggAutomizer (img _ f X) (img _ f Bs))) : MulAut ↥(img _ f Bs)) s :
        ↥(img _ f Bs)) : Q) = ψ (ggPermSU σ⁻¹) * (s : Q) * (ψ (ggPermSU σ⁻¹))⁻¹)
    (hεrefl : ∀ a b : Fin 6, a ≠ b → GGIsReflection 3
      ((ε (Equiv.swap a b) : ↥(ggAutomizer (img _ f X) (img _ f Bs))) : MulAut ↥(img _ f Bs)))
    (hεblock : ∀ a b : Fin 6, a ≠ b →
      ggRankOneIn (img _ f X) (img _ f Bs)
        ((ε (Equiv.swap a b) : ↥(ggAutomizer (img _ f X) (img _ f Bs))) :
          MulAut ↥(img _ f Bs)) = (ggSuPairBlock K 2 1 6 a b).map ψ)
    {r r' : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrA' : r' ∈ ggAutomizer X Bs)
    (hr : GGIsReflection 3 r) (hr' : GGIsReflection 3 r')
    (hfix : ∀ z ∈ twoCentral X,
      (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs r', h * z = z * h) → z = 1) :
    r * r' ≠ r' * r →
      ∀ (K' : Type) [Field K'] [Finite K'] [CharP K' 2] (f' : ℕ),
        Nat.card K' = (2 ^ f') ^ 2 →
        Nat.card (ggRankOneIn X Bs r) = 2 ^ f' * ((2 ^ f') ^ 2 - 1) →
        ∃ W : Subgroup G, UnitaryBlockStandardPair K' 2 f' W
          (ggRankOneIn X Bs r) (ggRankOneIn X Bs r') := by
  intro hnc K' _ _ _ f' hK' hS
  let ρ : MulAut ↥(img _ f Bs) := MulAut.congr hD.tau r
  let ρ' : MulAut ↥(img _ f Bs) := MulAut.congr hD.tau r'
  have hρA : ρ ∈ ggAutomizer (img _ f X) (img _ f Bs) :=
    hD.map_automizer_le (Subgroup.le_normalizer) (Subgroup.mem_map.2 ⟨r, hrA, rfl⟩)
  have hρA' : ρ' ∈ ggAutomizer (img _ f X) (img _ f Bs) :=
    hD.map_automizer_le (Subgroup.le_normalizer) (Subgroup.mem_map.2 ⟨r', hrA', rfl⟩)
  have hρrefl : GGIsReflection 3 ρ := (ggIsReflection_congr_iff hD.tau r).2 hr
  have hρrefl' : GGIsReflection 3 ρ' := (ggIsReflection_congr_iff hD.tau r').2 hr'
  have hncρ := congr_ne_ev2 hD.tau hnc
  have h6 := rankOne_card_ev2 hlocal ε hεrefl hεblock hρA hρrefl
  have hpairbar := QTwo.ggQTwoDUnit_pair_of_position (p := 3) Nat.prime_three (by norm_num)
    hlocal.bstar.2.1 hlocal hrange hd ε hε hεrefl hεblock
    hρA hρrefl hρA' hρrefl' hncρ h6
  have hW := rankTwo_le_ev2 hD hfix
  obtain ⟨W', hW'⟩ := hD.pair_lift hfix hpairbar hW
  exact ⟨W', ggPhanNSAPairAux_stdPair_of_card (K := GaloisField 2 2) (f := 1)
    (by rw [QTwo.natCard_galoisField_two_two]; norm_num) hK' hW' hS⟩

theorem ggPairConcl_of_twA5_two_even
    (hU : GGU62OuterDiagInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hBB : B = Bs) (hcentX : Nat.card ↥(B ⊓ Subgroup.centralizer (X : Set G)) = p)
    (h5 : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X)
    (h3pow : 720 ≤ Nat.card ↥(ggAutomizer X Bs) →
      3 ^ 6 ≤ Nat.card ↥Bs ∨ Subgroup.center ↥X = ⊥)
    {r r' : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrA' : r' ∈ ggAutomizer X Bs)
    (hr : GGIsReflection p r) (hr' : GGIsReflection p r') (hne : r ≠ r') :
    GGPairConcl Bs X r r' := by
  classical
  obtain ⟨hp3, hperf, _hBsN, K, hKf, hKfin, hKchar, Q, hQg, hQfin, f, ψ, hD, hK4, hlocal,
    hrange, hd, ε, hε, hεrefl, hεblock⟩ :=
    ggNsq2Member_quotient_position hcfg hcentX h5
  subst hp3
  have hC3 : Nat.card ↥(img _ f Bs ⊓ Subgroup.centralizer (ψ.range : Set Q)) ≤ 3 := by
    rw [hrange, hD.cent hperf le_rfl]
    exact (hBB ▸ hcentX).le
  have h720 : Nat.card ↥(ggAutomizer (img _ f X) (img _ f Bs)) = 720 := by
    have h6 : (6 : ℕ).factorial = 720 := by decide
    rw [← Nat.card_congr ε.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin, h6]
  have hAL : 720 ≤ Nat.card ↥(ggAutomizer X Bs) := by
    rw [← h720]
    exact hD.card_automizer_le (twoCentral_le X) hD.LN
  have hfix := hfix_ev2 hU hD hperf hK4 hlocal hrange hd hC3 (h3pow hAL) hrA hrA' hr hr'
  exact ⟨commute_ev2 hD hlocal ε hεrefl hεblock hrA hrA' hr hr' hne hfix,
    pair_ev2 hD hlocal hrange hd ε hε hεrefl hεblock hrA hrA' hr hr' hfix⟩

end CFSG.StandardType

end

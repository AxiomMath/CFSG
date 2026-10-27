module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACE6
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrthNonFull

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open CFSG.StandardType.OmNsRootGen

theorem ggQTwoE6_D4_four_dvd_omega
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {k : ℕ} (hk : k = 3)
    {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)}
    {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}
    (hF : IsCoherentFrame Q 3 U e E u c t) {f f' : V}
    (hf : f ∈ polarPerp Q (⨆ j, U j)) (hf' : f' ∈ polarPerp Q (⨆ j, U j))
    (hQf : Q f = 0) (hQf' : Q f' = 0) (hff' : QuadraticMap.polar Q f f' = 1) :
    4 ∣ Nat.card (ggAutomizer ⊤ E) := by
  subst hk
  have hv : f + f' ∈ polarPerp Q (⨆ j, U j) :=
    (polarPerp Q (⨆ j, U j)).add_mem hf hf'
  have hQv : Q (f + f') ≠ 0 := by
    have h := QuadraticMap.map_add (Q : V → F) f f'
    rw [h, hQf, hQf', hff']
    norm_num
  exact four_dvd_ggAutomizer_signChange_pair hQ hF hv hQv rfl
    (by decide : (0 : Fin 3) ≠ 1) ⊤ (by simp) (by simp)

theorem ggQTwoE6_D4_split
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J)) :
    ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ J, g⁻¹ * b ∈ Subgroup.centralizer (J : Set G) := by
  intro b hb
  have hb' : b ∈ (Bs ⊓ Subgroup.centralizer (J : Set G)) ⊔ (Bs ⊓ J) := by
    rw [← ggQTwoE6_bstar_eq_sup_L hS hq2 htag hmark hJ]
    exact hb
  have hcomm : ∀ a ∈ Bs ⊓ Subgroup.centralizer (J : Set G), ∀ c ∈ Bs ⊓ J,
      Commute a c := fun a ha c hc => (Subgroup.mem_centralizer_iff.mp ha.2 c hc.2).symm
  obtain ⟨c, hc, g, hg, hb⟩ := (mem_sup_of_commute hcomm).mp hb'
  refine ⟨g, hg, ?_⟩
  have hcg : c * g = g * c := (Subgroup.mem_centralizer_iff.mp hc.2 g hg.2).symm
  have hceq : g⁻¹ * b = c := by
    rw [← hb]
    calc g⁻¹ * (c * g) = g⁻¹ * (g * c) := by rw [hcg]
      _ = c := by group
  rw [hceq]
  exact hc.2

theorem ggQTwoE6_D4_automizer_card_transport
    {G : Type} [Group G] {Bs J : Subgroup G}
    {φ : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) →* G}
    {η : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) ≃* ↥ggQTwoE6_Omega}
    {E : Subgroup ↥ggQTwoE6_Omega}
    (hφr : φ.range = J) (hφi : Function.Injective φ)
    (hE : E = ((Bs ⊓ J).comap φ).map η.toMonoidHom) :
    Nat.card (ggAutomizer J (Bs ⊓ J)) = Nat.card (ggAutomizer ⊤ E) := by
  let B₀ : Subgroup ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) := (Bs ⊓ J).comap φ
  have hBmap : B₀.map φ = Bs ⊓ J := by
    dsimp only [B₀]
    rw [Subgroup.map_comap_eq, hφr, inf_eq_right.mpr inf_le_right]
  have htopφ : (⊤ : Subgroup ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀)).map φ = J := by
    rw [Subgroup.map_top, hφr]
  have hcardφ : Nat.card (ggAutomizer J (Bs ⊓ J)) = Nat.card (ggAutomizer ⊤ B₀) := by
    calc Nat.card (ggAutomizer J (Bs ⊓ J))
        = Nat.card (ggAutomizer (Subgroup.map φ ⊤) (Subgroup.map φ B₀)) := by
          rw [htopφ, hBmap]
      _ = Nat.card (ggAutomizer ⊤ B₀) := by
          rw [F4AutWeyl.ggAutomizer_map_eq hφi ⊤ B₀ rfl,
            Subgroup.card_map_of_injective (MulAut.congr _).injective]
  have htopη : (⊤ : Subgroup ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀)).map η.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ η.surjective
  have hcardη : Nat.card (ggAutomizer ⊤ E) = Nat.card (ggAutomizer ⊤ B₀) := by
    calc Nat.card (ggAutomizer ⊤ E)
        = Nat.card (ggAutomizer (Subgroup.map η.toMonoidHom ⊤)
            (Subgroup.map η.toMonoidHom B₀)) := by
          rw [htopη, hE]
      _ = Nat.card (ggAutomizer ⊤ B₀) := by
          rw [F4AutWeyl.ggAutomizer_map_eq (f := η.toMonoidHom) η.injective ⊤ B₀ rfl,
            Subgroup.card_map_of_injective (MulAut.congr _).injective]
  rw [hcardφ, ← hcardη]

theorem ggQTwoE6_D4_four_dvd_bstar
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J)) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  obtain ⟨φ, η, E, k, U, e, u, c, t, f, f', hφr, hφi, hE, -, -, -, hF, hk, hf, hf',
    hQf, hQf', hff'⟩ := ggQTwoE6_D4_frame hS hq2 htag hmark hJ
  have hk3 : k = 3 := by omega
  have h4 : 4 ∣ Nat.card (ggAutomizer ⊤ E) :=
    ggQTwoE6_D4_four_dvd_omega ggQTwoE6_Q_nondegenerate hk3 hF hf hf' hQf hQf' hff'
  rw [B48Om.ggAutomizer_card_eq_of_split (ggQTwoE6_D4_split hS hq2 htag hmark hJ),
    ggQTwoE6_D4_automizer_card_transport hφr hφi hE]
  exact h4

theorem ggQTwoGuardFailsOn_e6 :
    GGQTwoGuardFailsOn (fun p lab => GGLabQTwo p lab ∧ lab.tag = .E6) := by
  intro G _ _ p B Bs x L D J hS hp hL
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, -, -, -, ⟨⟨hq, htag⟩, hN, -⟩⟩ := largeEvenRawDatum_exists hraw
  have hmarkLab : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab) :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ', _⟩ => ⟨hs, hna, θ', rfl⟩) hraw⟩
  have hmark := QTwoCav.innerDiagOnLabel_of_setting hS hmarkLab
  rcases ggQTwoE6_J_label hS hq htag hmark with hA5 | hD4 | hA2
  · exact ggQTwoE6_A5_four_dvd hS hA5
  · exact ggQTwoE6_D4_four_dvd_bstar hS hq htag hmark hD4
  · exfalso
    have hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
      hS.1.1.2.2.1.2.2.2.2.2.1
    have hJL : J ≤ L := hJc.1.trans inf_le_left
    exact ggQTwoE6_A2_impossible hS hq htag hmark hN
      (ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm hA2)

end CFSG.StandardType

end

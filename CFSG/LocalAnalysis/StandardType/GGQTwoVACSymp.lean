module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACSplit
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImage
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
public import CFSG.LocalAnalysis.StandardType.GGKGARank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2Symp_gamma_card
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSpGroup K m)}
    (hperf : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m), LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Nat.card (ggGamma L hBsN).range = 3 ^ m := by
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  have hpq : 3 ∣ Nat.card K + 1 := by
    have h3 : Nat.card K + 1 = 3 := by omega
    rw [h3]
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsE, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN hBsI0 hb
  have hAe : IsElemAbelian 3 (ggGamma L hBsN).range :=
    isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hBsE a.2 b.2))
      (fun a => Subtype.ext (by simpa using hBsE.2 a a.2)) (ggGamma L hBsN)
  have hAI : ∀ a ∈ (ggGamma L hBsN).range,
      ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
        (LargeEvenGSpSet K m), ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  have hself : GGTorusSelfCent 3 (ggGamma L hBsN).range :=
    ggTorusSelfCent_ggGamma hBsN hSC
  have hlow : 3 ^ m ≤ Nat.card (ggGamma L hBsN).range :=
    ggTorusSCRank_sp (m := m) (p := 3) (by omega) Nat.prime_three hpq
      L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
      (ggGamma L hBsN).range hAe hAI hself
  haveI : NeZero m := ⟨by omega⟩
  have hup : Nat.card (ggGamma L hBsN).range ≤ 3 ^ m :=
    KGA.kga_card_le_sp (K := K) (N := m) (p := 3) Nat.prime_three (by norm_num)
      (L' := L) (ψ := ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf hAe hAI
  exact le_antisymm hup hlow

theorem ggQ2TBFull_of_symp
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) (hL : GGInnerDiagOnLabel GGQ2VACLabSymp p Bs L) : GGQ2TBFull p Bs L := by
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hSymp, -, -⟩ := hQ
  obtain ⟨hq, htag⟩ := hSymp
  have hn1 : n = 1 := by
    have h1 : 1 ≤ n := hlab.1
    have h2 : n < 2 := hq
    omega
  have hmark : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = ⟨tag, rank, n⟩) :=
    ⟨hperf, ⟨tag, rank, n⟩, hlab,
      largeEvenRawDatum_mono (fun R' _ I' _ ⟨hs, hna, θ', _⟩ => ⟨hs, hna, θ', rfl⟩) hraw⟩
  rcases htag with hB | hC
  · subst hB
    have hr3 : 3 ≤ rank := by
      have h2 : 2 ≤ rank := hlab.2.1
      by_contra h3
      have heq : rank = 2 := by omega
      have h4 : 2 ≤ n := hlab.2.2 heq
      omega
    dsimp only [LargeEvenRawDatum] at hraw
    obtain ⟨K, _, _, hK, hQ'⟩ := hraw
    obtain ⟨-, -, θ', -, hBsN', hBsI0'⟩ := hQ'
    refine ⟨⟨.B, rank, n⟩, hq, hmark, ?_⟩
    rw [← QTwoCav.gamma_card hBsN',
      ggQ2Symp_gamma_card hS (by rw [hK]; simp [hn1]) hr3 (θ := θ') hperf hBsN' hBsI0']
    simp [GGQ2LieRank]
  · subst hC
    have hr3 : 3 ≤ rank := by
      have h2 : 2 ≤ rank := hlab.2.1
      by_contra h3
      have heq : rank = 2 := by omega
      have h4 : 2 ≤ n := hlab.2.2 heq
      omega
    dsimp only [LargeEvenRawDatum] at hraw
    obtain ⟨K, _, _, hK, hQ'⟩ := hraw
    obtain ⟨-, -, θ', -, hBsN', hBsI0'⟩ := hQ'
    refine ⟨⟨.C, rank, n⟩, hq, hmark, ?_⟩
    rw [← QTwoCav.gamma_card hBsN',
      ggQ2Symp_gamma_card hS (by rw [hK]; simp [hn1]) hr3 (θ := θ') hperf hBsN' hBsI0']
    simp [GGQ2LieRank]

theorem ggQTwoGuardFailsOn_of_cavFull (hCav : GGQ2CavOfTBFull)
    {S : ℕ → LargeEvenLabel → Prop}
    (hTB : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
      {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J → p = 3 →
        GGInnerDiagOnLabel S p Bs L → GGQ2TBFull p Bs L) :
    GGQTwoGuardFailsOn S := by
  intro G _ _ p B Bs x L D J hS hp hL
  exact hCav hS hp (hTB hS hp hL)

theorem ggQTwoGuardFailsOn_symp_of_cav
    (hCav : GGQ2CavOfTBFull) :
    GGQTwoGuardFailsOn GGQ2VACLabSymp :=
  ggQTwoGuardFailsOn_of_cavFull hCav fun hS hp hL => ggQ2TBFull_of_symp hS hp hL

end CFSG.StandardType

end

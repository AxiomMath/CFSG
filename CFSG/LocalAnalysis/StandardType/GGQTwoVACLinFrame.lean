module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeTorus
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeVac
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def GGQ2VACLabLin (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLabQTwo p lab ∧ lab.tag = .A

theorem ggQ2Lin_bstar_eq_sup {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n : ℕ} {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ) :
    Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ := by
  obtain ⟨-, -, hxBs, -, -⟩ := hcfg.tableB_facts
  have hCBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    GGConfig.bstar_inf_centralizer_L hcfg
  refine le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr hxBs) hF.torus_le)
  intro b hb
  obtain ⟨t, ht, hact⟩ := hF.act b hb
  have hψtB : ψ t ∈ Bs := hF.torus_le (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  have hcent : (ψ t)⁻¹ * b ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := hact l hl
    calc l * ((ψ t)⁻¹ * b)
        = (ψ t)⁻¹ * (ψ t * l * (ψ t)⁻¹) * b := by group
      _ = (ψ t)⁻¹ * (b * l * b⁻¹) * b := by rw [← h]
      _ = (ψ t)⁻¹ * b * l := by group
  have hmem : (ψ t)⁻¹ * b ∈ Bs ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨Bs.mul_mem (Bs.inv_mem hψtB) hb, hcent⟩
  rw [hCBL] at hmem
  have heq : b = ψ t * ((ψ t)⁻¹ * b) := by group
  rw [heq, sup_comm]
  exact Subgroup.mul_mem_sup (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩) hmem

theorem ggQ2Lin_center_eq_bot {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ) :
    Subgroup.center ↥L = ⊥ := by
  let e : ↥L ≃* Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 :=
    (MulEquiv.subgroupCongr hF.range).symm.trans (MonoidHom.ofInjective hF.inj).symm
  have h := Subgroup.map_center_eq e
  rw [GGHalf.center_eq_bot (n + 1)] at h
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥L) e.injective).mp h

theorem ggQ2Lin_disjoint {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n : ℕ} {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ) :
    Disjoint (Subgroup.zpowers x) ((GGHalf.halfTorus n).map ψ) := by
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hZL : Subgroup.center ↥L = ⊥ := ggQ2Lin_center_eq_bot hF
  have hxcomm : ∀ l ∈ L, Commute x l := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)).symm
  rw [Subgroup.disjoint_def]
  intro y hyx hyt
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hyt
  have hyL : ψ t ∈ L := by
    rw [← hF.range]
    exact ⟨t, rfl⟩
  have hyC : ψ t ∈ Subgroup.centralizer (L : Set G) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    rw [← hk]
    exact ((hxcomm l hl).zpow_left k).symm
  have hyZ : (⟨ψ t, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC z z.2)
  rw [hZL] at hyZ
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hyZ)

theorem ggQ2Lin_card_bstar {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n : ℕ} {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ) :
    Nat.card Bs = 3 * 3 ^ ((n + 1) / 2) := by
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hxcomm : ∀ l ∈ L, Commute x l := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)).symm
  have hcent : ((GGHalf.halfTorus n).map ψ : Subgroup G) ≤
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    have hyL : ψ t ∈ L := by
      rw [← hF.range]
      exact ⟨t, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hxcomm (ψ t) hyL).zpow_left k
  have hdisj := ggQ2Lin_disjoint hcfg hF
  have hnormal : ((GGHalf.halfTorus n).map ψ) ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers x) ((GGHalf.halfTorus n).map ψ) hnormal hdisj
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, GGConfig.orderOf_x hcfg]
  have hcardT : Nat.card ((GGHalf.halfTorus n).map ψ) = 3 ^ ((n + 1) / 2) := by
    rw [Subgroup.card_map_of_injective hF.inj, GGHalf.card_halfTorus]
  rw [hBs, hcard, hcardx, hcardT]

theorem ggQ2Lin_rank_ge_five {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hperf : commutator ↥L = ⊤)
    {rank : ℕ}
    (hraw : LargeEvenRawDatum ⟨.A, rank, 1⟩ (fun R _ I _F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
          GGQ2VACLabLin 3 ⟨.A, rank, 1⟩ ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I,
              LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :
    5 ≤ rank := by
  by_contra hlt
  have hle4 : rank ≤ 4 := by omega
  have hsmall := StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall
    (p := 3) (lab := ⟨.A, rank, 1⟩) ⟨rfl, rfl, Or.inl ⟨rfl, hle4⟩⟩
  obtain ⟨R', _, I', F',
      ⟨⟨hsimple', hnonab', θ', hlin', hBN', hact'⟩, hsmallX⟩⟩ :=
    largeEvenRawDatum_exists (hsmall _ hraw)
  have hBsE : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have htop : IsElemAbelian 3 (⊤ : Subgroup ↥Bs) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hBsE.1.is_comm.comm a b)⟩⟩, fun a _ =>
      Subtype.ext (hBsE.2 a a.2)⟩
  have hEA : IsElemAbelian 3 (ggBeta L θ' hBN').range := by
    have h := CFSG.Open.IsElemAbelian.map htop (ggBeta L θ' hBN')
    simpa only [Subgroup.map_top] using h
  have hsub : ((ggBeta L θ' hBN').range : Set (MulAut R')) ⊆ I' := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ' hBN' hact' b
  have hlt27 := hsmallX (ggBeta L θ' hBN').range hsub hEA
  have hge27 : 3 ^ 3 ≤ Nat.card (ggBeta L θ' hBN').range := by
    have hmul := (card_range_ggBeta_bstar hcfg hperf θ'
      (hcfg.2.1.1.trans hBN') hBN').2.2
    have h4 := hcfg.tableB_facts.2.2.2.2
    norm_num at h4 ⊢
    omega
  exact absurd hge27 (not_le.mpr hlt27)

theorem ggQ2Lin_frame {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hL : GGInnerDiagOnLabel GGQ2VACLabLin p Bs L) (hp : p = 3) :
    ∃ (n : ℕ) (ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G), 5 ≤ n ∧
      GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ ∧
      Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ := by
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hsimple, hnonab, θ, hlin, hBN, hact⟩ := hQ
  obtain ⟨hqtwo, htag⟩ := hlin
  obtain ⟨tag, rank, n⟩ := lab
  have hnlt : n < 2 := hqtwo
  have htag' : tag = .A := htag
  subst htag'
  have hparts : 1 ≤ n ∧ (1 ≤ rank ∧ (rank = 1 → 2 ≤ n)) := by
    simpa only [LargeEvenInLambda2] using hlab
  have hn : n = 1 := by omega
  subst hn
  have hrank2 : 2 ≤ rank := by
    have hne : rank ≠ 1 := by
      intro h1
      have := hparts.2.2 h1
      omega
    omega
  have hrank5 : 5 ≤ rank := ggQ2Lin_rank_ge_five hcfg hperf hraw
  have hHas : GGHasLabel ⟨.A, rank, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hmodelLZ : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL (rank + 1) 2 1 :=
    statedClassicalModel_of_hasLabel_typeA hlab hHas
  have hm : (rank - 2) + 1 + 1 + 1 = rank + 1 := by omega
  obtain ⟨φ, hφr, hφi⟩ := GGHalf.exists_slLift_two (m := rank - 2) (by omega) hperf
    (by simpa [hm] using hmodelLZ)
  obtain ⟨A, hframe⟩ := ggHalf_torusFrame (X := L) (p := 3) rfl hcfg.2.1
    (N := rank - 2 + 1 + 1) (by omega) hBN φ hφr hφi
  exact ⟨rank - 2 + 1 + 1, φ.comp (MulAut.conj A).toMonoidHom, by omega, hframe,
    ggQ2Lin_bstar_eq_sup hcfg hframe⟩

theorem ggQ2Lin_B_eq {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G} (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ) : B = Bs := by
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hSstar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hperf : commutator ↥L = ⊤ := hSstar.2.2.2.1.2.2.1
  have hbstar : Nat.card Bs = 3 * 3 ^ ((n + 1) / 2) := ggQ2Lin_card_bstar hcfg hF hBs
  have hd : 5 ≤ n + 1 := by omega
  have hlift : GGTorusLift 3 ((n + 1) / 2) (projectiveSL (n + 1) GGHalf.F2) := by
    have hcard : Nat.card GGHalf.F2 = 2 := GaloisField.card 2 1 (by omega)
    exact TwoThree.ggTorusLift_two (K := GGHalf.F2) (d := n + 1) hcard hd
  let eSL : ↥L ≃* Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 :=
    (MulEquiv.subgroupCongr hF.range).symm.trans (MonoidHom.ofInjective hF.inj).symm
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL (n + 1) GGHalf.F2 :=
    (QuotientGroup.congr (G' := Subgroup.center ↥L)
      (H' := Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2))
      eSL (Subgroup.map_center_eq eSL)).trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n + 1) GGHalf.F2).symm)
  have hliftR : GGTorusLift 3 ((n + 1) / 2) (↥L ⧸ Subgroup.center ↥L) :=
    TypeA.ggTorusLift_of_mulEquiv e hlift
  have hm : (n + 1) / 2 + 1 ≤ LargeEvenTwoLocalRank 3 G :=
    succ_le_twoLocalRank_of_torusLift (p := 3) (r := (n + 1) / 2) (by norm_num)
      (hcfg.tableB_facts.2.2.2.1) (hcfg.2.1.2.1.2 x hcfg.tableB_facts.2.2.1)
      hSstar.2.2.1 hperf (θ := MulEquiv.refl _) hliftR
  have hcardB : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  have hge : 3 ^ ((n + 1) / 2 + 1) ≤ Nat.card B := by
    rw [hcardB]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) hm
  have hBsle : Nat.card Bs ≤ 3 ^ ((n + 1) / 2 + 1) := by
    rw [hbstar, ← pow_succ' 3 ((n + 1) / 2)]
  have hcardEq : Nat.card B = Nat.card Bs := le_antisymm hBle (hBsle.trans hge)
  exact Subgroup.eq_of_le_of_card_ge hcfg.2.1.1 (by rw [hcardEq])

end CFSG.StandardType

end

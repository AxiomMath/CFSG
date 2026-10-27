module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGNbrLabelJOfTcjK
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6cL_dvd_of_split_twE6 {m : ℕ}
    (h : LargeEvenSplit 3 (⟨.twE6, 0, m⟩ : LargeEvenLabel)) : 3 ∣ 2 ^ m + 1 := by
  rcases h with ⟨huntw, -⟩ | ⟨-, -, hdvd⟩ | ⟨h, -⟩ | ⟨hn1, -⟩
  · simp [LargeEvenUntwisted] at huntw
  · exact hdvd
  · rcases h with h | h <;> simp at h
  · have hm1 : m = 1 := by simpa using hn1
    rw [hm1]; norm_num

theorem ggTwE6Comp_L_false
    {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput) (hRB : GGTwE6ThreeBstarRankInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hinn : GGInnerDiagOn Bs L) (hp : p = 3) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) {labJ labX : LargeEvenLabel}
    (hΛX : LargeEvenInLambda2 labX) (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hX : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L)) (hXtag : labX.tag = .twE6)
    (hKG : LargeEvenLabelAll (⟨.twE6, 0, labX.n⟩ : LargeEvenLabel) fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
            GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
              3 ∣ 2 ^ labX.n + 1 ∧
                ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → e ∈ A →
                  (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A ≤ 3 ^ 4) :
    False := by
  subst hp
  have hXrank : labX.rank = 0 := by simpa [hXtag] using hΛX.2
  have hlabX : labX = ⟨.twE6, 0, labX.n⟩ := by
    obtain ⟨tag, rank, n⟩ := labX
    have h1 : tag = .twE6 := by simpa using hXtag
    have h2 : rank = 0 := by simpa using hXrank
    subst h1
    subst h2
    rfl
  have hmΛ : LargeEvenInLambda2 (⟨.twE6, 0, labX.n⟩ : LargeEvenLabel) := by
    rwa [← hlabX]
  obtain ⟨lab, hlab, hhasL, R0, _, I0, F0, θ0, hP0⟩ :=
    largeEvenMarking_exists_hasLabel hcfg.1.2.2.2.2.2.2.2.1
  have hsplit : LargeEvenSplit 3 lab := hP0.1
  have hiso : GGLabelIso lab labX :=
    hRig lab labX (↥L ⧸ Subgroup.center ↥L) hlab hΛX hhasL hX
  have hlab_eq : lab = labX :=
    eq_of_ggLabelIso_of_twE6 (lab := labX) (lab' := lab) hXtag hiso
  have hsplitX : LargeEvenSplit 3 labX := hlab_eq ▸ hsplit
  have hdvd3 : 3 ∣ 2 ^ labX.n + 1 := by
    refine l6cL_dvd_of_split_twE6 (m := labX.n) ?_
    rw [← hlabX]
    exact hsplitX
  have hS : GGTableBTwE6ThreeLabel 3 labX := ⟨hXtag, rfl, hdvd3⟩
  have hME6 : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L :=
    ggInnerDiagOnLab_of_hasLabel hRig hinn hΛX hX hS hsplitX
  have hT : GGThmIHyp 3 B x L := hcfg.1
  have hSS := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian 3 B := hSS.1.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSS.2.2.2.1.1
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hy : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hy
  have hy1 : y ^ 3 = 1 := hBel.2 y hy
  have hLperf : commutator ↥L = ⊤ := hinn.1
  let P' : LargeEvenRawCont := fun R _ I _ =>
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ e : MulAut L', e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
        ∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
          GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
            3 ∣ 2 ^ labX.n + 1 ∧
              ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → e ∈ A →
                (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A ≤ 3 ^ 4
  have hAll : LargeEvenLabelAll labX P' := by
    rw [hlabX]
    exact hKG
  have hMrel := ggInnerDiagOn_relabel hRig hinn hΛX hX
  have hM2 : LargeEvenMarking ↥L (fun lab' R _ I F θ =>
      (lab' = labX ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      P' R I F) :=
    largeEvenMarking_and_labelAll (S := fun lab' => lab' = labX)
      (fun lab' _ hSeq => by rw [hSeq]; exact hAll)
      (fun lab' R _ I F θ hP => hP.1)
      hMrel
  obtain ⟨_lab', _hlab'Λ, _hhas', R, _hR, I, F, θ, ⟨⟨_hlabel', hN, hind⟩, hKGprop⟩⟩ :=
    largeEvenMarking_exists_hasLabel hM2
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hN hyBs
  have hep : (L.normalizerMonoidHom ⟨y, hyN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hy1)
    rw [h1, map_one]
  have hφe : ∃ φ ∈ I, ∀ l : ↥L,
      φ (ggQuotHom θ l) = ggQuotHom θ (L.normalizerMonoidHom ⟨y, hyN⟩ l) := by
    obtain ⟨φ, hφI, hφ⟩ := hind y⁻¹ (Bs.inv_mem hyBs)
    refine ⟨φ, hφI, fun l => hφ l (L.normalizerMonoidHom ⟨y, hyN⟩ l) ?_⟩
    show ((L.normalizerMonoidHom ⟨y, hyN⟩ l : ↥L) : G) = y⁻¹⁻¹ * (l : G) * y⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hDy : D = Subgroup.closure {x, y} := hnb.2.1
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  rw [hDy, ggInf_centralizer_pair hLx] at hcomp
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hyN hcomp
  have hJlab : GGHasLabel labJ (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr (Subgroup.center ↥(J.subgroupOf L))
      (Subgroup.center ↥J) (Subgroup.subgroupOfEquivOfLe hJL) (Subgroup.map_center_eq _)).symm hJ
  have hcard : 3 ^ 5 ≤ Nat.card (ggGamma L hN).range :=
    hRB G 3 B Bs x L D J hcfg hME6 hN
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma L hN).range :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hcard
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I := by
    intro b hb
    obtain ⟨φ, hφI, hindφ⟩ := hind b⁻¹ (Bs.inv_mem hb)
    have hφeq : φ = ggLAut L θ ⟨b⁻¹⁻¹,
        (Subgroup.normalizer (L : Set G)).inv_mem (hN (Bs.inv_mem hb))⟩ :=
      eq_ggLAut_of_induces L θ (hN (Bs.inv_mem hb)) hindφ
    have hb_eq : (⟨b⁻¹⁻¹, (Subgroup.normalizer (L : Set G)).inv_mem
        (hN (Bs.inv_mem hb))⟩ : Subgroup.normalizer (L : Set G)) = ⟨b, hN hb⟩ :=
      Subtype.ext (inv_inv b)
    rw [hφeq, hb_eq] at hφI
    exact hφI
  have hTB := ggTorusTBGroup_of_marking (p := 3) (r := 5) (by norm_num) hBs hSC hLperf θ hN hBsI hcard h3
  have hA : IsElemAbelian 3 (ggGamma L hN).range := hTB.2.2.2.1
  have hAI : ∀ a ∈ (ggGamma L hN).range, ∃ φ ∈ I, ∀ l : ↥L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := hTB.2.2.2.2.1
  obtain ⟨-, hbound⟩ := hKGprop ↥L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hLperf (L.normalizerMonoidHom ⟨y, hyN⟩) hep hφe
    (J.subgroupOf L) hJcomp hJlab
  have heA : L.normalizerMonoidHom ⟨y, hyN⟩ ∈ (ggGamma L hN).range := ⟨⟨y, hyBs⟩, rfl⟩
  exact absurd (le_trans hcard (hbound _ hA heA hAI)) (by norm_num)

theorem ggTwE6Comp_K_false
    {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    (hI3 : GGNbrSubcomponentInput) (hRk : GGTwE6ThreeNbrRankInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hinn : GGInnerDiagAll p B Bs x L D J) (hp : p = 3) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) {labJ labX : LargeEvenLabel}
    (hΛX : LargeEvenInLambda2 labX) (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hX : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K)) (hXtag : labX.tag = .twE6)
    (hKG : LargeEvenLabelAll (⟨.twE6, 0, labX.n⟩ : LargeEvenLabel) fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
            GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
              3 ∣ 2 ^ labX.n + 1 ∧
                ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → e ∈ A →
                  (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A ≤ 3 ^ 4) :
    False := by
  subst hp
  obtain ⟨labXt, labXr, labXn⟩ := labX
  have hXt : labXt = .twE6 := by simpa using hXtag
  subst hXt
  have hXr : labXr = 0 := by simpa using hΛX.2
  subst hXr
  obtain ⟨-, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hSS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  have hJK : J ≤ K := hI3 G 3 B x L D J hcfg.1 hcfg.2.2 y K hnb
  have hinnK : GGInnerDiagOn Bs K := hinn.2 y K hnb
  have hperfK : commutator ↥K = ⊤ := hinnK.1
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hinnK
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hN hxBs
  let e : MulAut ↥K := K.normalizerMonoidHom ⟨x, hxN⟩
  have hx1 : x ^ 3 = 1 := hBs.2 x hxBs
  have he3 : e ^ 3 = 1 := by
    dsimp only [e]
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx1)
    rw [h1, map_one]
  obtain ⟨R, _, θ, I, F, hBsI, hP⟩ :=
    exists_innerDiagDatum_of_labelAll hRig hinnK hΛX hX hKG hN
  have hφe : ∃ φ ∈ I, ∀ l : ↥K, φ (ggQuotHom θ l) = ggQuotHom θ (e l) := by
    refine ⟨ggLAut K θ ⟨x, hxN⟩, hBsI x hxBs, fun l => ?_⟩
    rw [ggQuotHom_apply, ggQuotHom_apply]
    change ggLAut K θ ⟨x, hxN⟩ (θ (l : ↥K ⧸ Subgroup.center ↥K)) =
      θ ((K.normalizerMonoidHom ⟨x, hxN⟩ l : ↥K) : ↥K ⧸ Subgroup.center ↥K)
    exact ggLAut_apply K θ ⟨x, hxN⟩ l
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSS hDJ hnb hJK
  have hJcomp : IsComponentOf (J.subgroupOf K) (ggFixSub e) :=
    ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  have hHasLabelJ : GGHasLabel labJ
      (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK).symm
      (Subgroup.map_center_eq _)) hJ
  have hPair := hP ↥K (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hperfK e he3 hφe (J.subgroupOf K) hJcomp hHasLabelJ
  have hm_dvd : 3 ∣ 2 ^ labXn + 1 := hPair.1
  have hBad : GGTwE6BadLabel 3 (⟨.twE6, 0, labXn⟩ : LargeEvenLabel) := ⟨rfl, rfl, hm_dvd⟩
  have hsplit : LargeEvenSplit 3 (⟨.twE6, 0, labXn⟩ : LargeEvenLabel) :=
    largeEvenSplit_of_twE6BadLabel hBad
  have hMark : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs K :=
    ggInnerDiagOnLab_of_hasLabel hRig hinnK hΛX hX hBad hsplit
  have hSelf : GGTorusSelfCent 3 (ggGamma K hN).range :=
    ggTorusSelfCent_ggGamma hN hSC
  have hcard : 3 ^ 5 ≤ Nat.card (ggGamma K hN).range :=
    hRk G 3 B Bs x L D J hcfg rfl y K hnb hMark hN hSelf
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma K hN).range := le_trans (by norm_num) hcard
  have hTorus : GGTorusTBGroup 3 5 R I ↥K (ggQuotHom θ) (ggGamma K hN).range :=
    ggTorusTBGroup_of_marking (p := 3) (r := 5) (by norm_num) hBs hSC hperfK θ hN hBsI hcard h3
  have hAb : IsElemAbelian 3 (ggGamma K hN).range := hTorus.2.2.2.1
  have hAI := hTorus.2.2.2.2.1
  have he_mem : e ∈ (ggGamma K hN).range := by
    refine ⟨⟨x, hxBs⟩, ?_⟩
    dsimp only [e]
    rfl
  have hle : Nat.card (ggGamma K hN).range ≤ 3 ^ 4 :=
    hPair.2 (ggGamma K hN).range hAb he_mem hAI
  norm_num at hcard hle
  omega

end CFSG.StandardType

end

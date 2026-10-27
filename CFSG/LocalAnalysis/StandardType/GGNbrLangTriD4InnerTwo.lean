module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangAxisCases
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
public import CFSG.LocalAnalysis.StandardType.GGTriD4InnerCompDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneProof
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.LocalAnalysis.StandardType.GGNbrLangRestRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylRest5
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import Certificates.Certificate8064

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggNbrLangTriD4InnerTwoAux_induces_unique {L : Type*} {R : Type} [Group L] [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {rel : L → L → Prop}
    (hfun : ∀ l, ∃! l', rel l l') {φ ψ : MulAut R}
    (hφ : LargeEvenInduces θ rel φ) (hψ : LargeEvenInduces θ rel ψ) : φ = ψ := by
  ext r
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) (θ.symm r)
  have hr : θ (QuotientGroup.mk' (Subgroup.center L) x) = r := by
    rw [hx, MulEquiv.apply_symm_apply]
  rw [← hr]
  obtain ⟨l', hl', -⟩ := hfun x
  exact (hφ x l' hl').trans (hψ x l' hl').symm

private theorem ggNbrLangTriD4InnerTwoAux_label_arith {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h1 : markTag lab = .PSL) (h2 : markRank lab = 2) (h3 : markDeg lab = 3) :
    lab.tag = .A ∧ lab.rank = 1 ∧ lab.n = 3 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t <;> simp_all [markTag, markRank, markDeg]
  case twD =>
    by_cases hl2 : l = 2
    · subst hl2
      simp only [if_true] at h3
      omega
    · by_cases hl3 : l = 3
      · simp [hl2, hl3] at h2
      · simp [hl2, hl3] at h2

private theorem ggNbrLangTriD4InnerTwoAux_labelAll_innerComp (hIC : GGTriD4InnerCompInput) :
    LargeEvenLabelAll ⟨.triD4, 0, 1⟩ (LargeEvenSimpleGuard fun R _ _ _ =>
      ∀ h : R, h ≠ 1 → h ^ 3 = 1 →
      ∀ Q : Subgroup R, IsComponentOf Q (Subgroup.centralizer ({h} : Set R)) →
        ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 8 ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 2) E))) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeTwisted_and (m := 3) (n := 1)
    (P := LargeEvenSimpleGuard fun R _ _ _ => ∀ h : R, h ≠ 1 → h ^ 3 = 1 →
      ∀ Q : Subgroup R, IsComponentOf Q (Subgroup.centralizer ({h} : Set R)) →
        ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 8 ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 2) E))) (fun K _ _ hKcard _ _ => by
      intro h h1 h3 Q' hQ'
      rcases hIC 1 le_rfl (Or.inl rfl) K (by simpa using hKcard) h h1 h3 Q' hQ' with
        ⟨E, hEfield, hEfin, hEcard, he⟩ | ⟨h2, -⟩
      · exact ⟨E, hEfield, hEfin, by simpa using hEcard, he⟩
      · omega) hQ

private theorem ggNbrLangTriD4InnerTwoAux_labelAll_combined (hKG : GGTriD4KnownInput)
    (hIC : GGTriD4InnerCompInput)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : lab.tag = .triD4 ∧ lab.n = 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        GGTriD4InnDiag R I ∧ GGTriD4Schur R ∧ ∀ h : R, h ≠ 1 → h ^ 3 = 1 →
      ∀ Q : Subgroup R, IsComponentOf Q (Subgroup.centralizer ({h} : Set R)) →
        ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 8 ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 2) E))) := by
  have hEq : lab = ⟨.triD4, 0, 1⟩ := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨ht, hn⟩ := hS
    have hl0 : l = 0 := by
      have := hlab.2
      rw [ht] at this
      exact this
    dsimp only at ht hn hl0
    subst ht; subst hn; subst hl0; rfl
  subst hEq
  intro Q hQ
  refine largeEvenRawDatum_mono (fun R _ I F h => ?_)
    (largeEvenLabelAll_and (largeEvenLabelAll_triD4_known hKG hlab rfl)
      (ggNbrLangTriD4InnerTwoAux_labelAll_innerComp hIC) Q hQ)
  obtain ⟨hQ', hKGg, hICg⟩ := h
  exact ⟨hQ', fun hs hna => by
    obtain ⟨hInn, hSchur, -, -⟩ := hKGg hs hna
    exact ⟨hs, hna, hInn, hSchur, hICg hs hna⟩⟩

private theorem ggNbrLangTriD4InnerTwoAux_label
    {R_J : Type} [Group R_J] {lab_J : LargeEvenLabel} (hlab_J : LargeEvenInLambda2 lab_J)
    (hMarked : MarkedModel lab_J R_J) (hPSL : CFSG.Blueprint.LieModel R_J .PSL 2 2 3) :
    lab_J.tag = .A ∧ lab_J.rank = 1 ∧ lab_J.n = 3 := by
  by_cases hc : markChar lab_J = 2
  · have hLie := NbrInnerMore.lieModel_of_markedModel_two hc hMarked
    obtain ⟨hT, hR, hD⟩ :=
      CFSG.SeitzReduction.RankOne.lieModel_PSL_two_two_unique_of_card_eq hPSL hLie rfl
    exact ggNbrLangTriD4InnerTwoAux_label_arith hlab_J hT hR hD
  · exact absurd hMarked
      (NbrInnerMore.not_markedModel_of_char_ne_two hPSL (by simp) (by simp) (by simp) hc)

theorem ggNbrLangAxisInnerOn_t3Two (hsub : GGNbrSubcomponentInput) (hKG : GGTriD4KnownInput)
    (hLID : GGBstarInnerDiagLInputOn fun _ _ => True) (hQ1 : GGBstarInnerDiagJInput)
    (hIC : GGTriD4InnerCompInput) :
    GGNbrLangAxisInnerOn fun p lab => GGNbrLangT3Label p lab ∧ lab.n = 1 := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN P hP
  have hKperf : commutator K = ⊤ := hP.1
  have hM1 := largeEvenMarking_and_labelAll_simple_imp
    (S := fun lab => lab.tag = .triD4 ∧ lab.n = 1)
    (P' := fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      GGTriD4InnDiag R I ∧ GGTriD4Schur R ∧ ∀ h : R, h ≠ 1 → h ^ 3 = 1 →
      ∀ Q : Subgroup R, IsComponentOf Q (Subgroup.centralizer ({h} : Set R)) →
        ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 8 ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 2) E)))
    (fun lab hlab hS => ggNbrLangTriD4InnerTwoAux_labelAll_combined hKG hIC hlab hS) hP
  refine largeEvenMarking_mono ?_ hM1
  rintro lab R _ I F θ ⟨hPθ, hfacts⟩
  refine ⟨hPθ, ?_⟩
  rintro hlab hxin hall b₀ hb₀ hb₀I
  have hS : lab.tag = .triD4 ∧ lab.n = 1 := ⟨hlab.1.1, hlab.2⟩
  obtain ⟨hs_R, hna_R, hInn, hSchur, hInnerComp⟩ := hfacts hS
  have hp3 : p = 3 := hlab.1.2
  subst hp3
  have hcfgcopy := hcfg
  obtain ⟨hI, hBstar, hDJ⟩ := hcfg
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hSStar : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hSStar.2.1
  have hBBs : B ≤ Bs := hBstar.1
  have hxBs : x ∈ Bs := hBBs hxB
  have hx3 : x ^ 3 = 1 := hBstar.2.1.2 x hxBs
  have hZ : Subgroup.center K = ⊥ := hSchur K hKperf θ
  have hIS : ∀ φ : MulAut R, φ ∈ I ↔ φ ∈ (MulAut.conj : R →* MulAut R).range := by
    intro φ
    rw [hInn, MonoidHom.mem_range]
    rfl
  obtain ⟨r, hr⟩ := (hIS _).1 (hxin hxBs)
  have hσ3 : ggLAut K θ ⟨x, hN hxBs⟩ ^ 3 = 1 := ggLAut_pow_eq_one_of_pow K θ (hN hxBs) hx3
  have hr3 : r ^ 3 = 1 := by
    have hconj : MulAut.conj (r ^ 3) = MulAut.conj (1 : R) := by
      rw [map_one, map_pow, hr]
      exact hσ3
    exact NbrLangRest.conj_injective_of_simple hs_R hna_R hconj
  have hr1 : r ≠ 1 := by
    rintro rfl
    have hσ1 : ggLAut K θ ⟨x, hN hxBs⟩ = 1 := by rw [← hr, map_one]
    have hxK : x ∈ Subgroup.centralizer (K : Set G) :=
      mem_centralizer_of_ggLAut_eq_one K θ hKperf (g := ⟨x, hN hxBs⟩) hσ1
    have hJK : J ≤ K := hsub G 3 B x L D J hI hDJ y K hK
    have hcomm : (⁅K, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left
        ((Subgroup.mem_centralizer_iff.mp hxK k hk).symm) m).eq
    exact hK.2.2.2 (by rw [hcomm]; exact bot_le)
  have hJK : J ≤ K := hsub G 3 B x L D J hI hDJ y K hK
  have hJc := isComponentOf_inf_centralizer_of_ggNbr hSStar hDJ hK hJK
  obtain ⟨Q, e, hQ⟩ := exists_component_fixed_of_centerless θ hZ (hN hxBs) hJc
  have hfix : ggAutFixedSubgroup (ggLAut K θ ⟨x, hN hxBs⟩) =
      Subgroup.centralizer ({r} : Set R) := by
    rw [← hr]
    ext y
    simp only [ggAutFixedSubgroup, Set.mem_setOf_eq, Subgroup.mem_centralizer_singleton_iff,
      MulAut.conj_apply]
    constructor
    · intro h
      calc y * r = r * y * r⁻¹ * r := by rw [h]
        _ = r * y := by group
    · intro h
      calc r * y * r⁻¹ = y * r * r⁻¹ := by rw [h]
        _ = y := by group
  have hQr : IsComponentOf Q (Subgroup.centralizer ({r} : Set R)) := hfix ▸ hQ
  obtain ⟨E, hEfield, hEfin, hEcard, heQ⟩ := hInnerComp r hr1 hr3 Q hQr
  letI : Field E := hEfield
  letI : Finite E := hEfin
  obtain ⟨eQ⟩ := heQ
  have hIDL : GGInnerDiagOnLab (fun _ _ => True) 3 B L :=
      ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hI
  have hIDL' : GGInnerDiagOnLab (fun _ _ => True) 3 Bs L :=
    hLID G 3 B Bs x L D J ⟨hI, hBstar, hDJ⟩ hIDL
  have hID : GGInnerDiagOn Bs L := hIDL'.innerDiagOn
  have hIDJ : GGInnerDiagOn Bs J := hQ1 G 3 B Bs x L D J ⟨hI, hBstar, hDJ⟩ hID
  obtain ⟨hJperf, lab_J, hlab_J, hraw_J⟩ := hIDJ
  have hraw_marked := largeEvenRawDatum_markedModel hlab_J
    (Q := fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : (↥J ⧸ Subgroup.center ↥J) ≃* R,
        Bs ≤ Subgroup.normalizer (J : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (fun R _ I F hQ => hQ.2.1) hraw_J
  obtain ⟨R', _, I', F', hQ', hMM'⟩ := largeEvenRawDatum_exists hraw_marked
  obtain ⟨hs', hna', θ', hNJ', hhall'⟩ := hQ'
  have hMarkedCenter : MarkedModel lab_J (J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv θ'.symm hMM'
  let eJQ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥Q ⧸ Subgroup.center ↥Q) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  let σJ : (↥J ⧸ Subgroup.center ↥J) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 2) E) := eJQ.trans eQ
  have hEchar : CharP E 2 := charP_two_of_card (m := 3) (by rw [hEcard]; norm_num)
  have hEadm : CFSG.Open.StatedLieAdmissible .PSL 2 2 3 := by
    norm_num [CFSG.Open.StatedLieAdmissible]
  have hSCM :
      CFSG.Open.StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin 2) E)) .PSL 2 2 3 :=
    statedClassicalModel_linear 2 3 (by simpa using hEcard) hEadm
  have hPSL0 : CFSG.Blueprint.LieModel
      (LargeEvenProj (LargeEvenSLGroup (Fin 2) E)) .PSL 2 2 3 :=
    Or.inl ⟨by decide, hSCM⟩
  have hPSLJ : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 2 2 3 :=
    lieModel_of_mulEquiv' σJ.symm hPSL0
  have hlab := ggNbrLangTriD4InnerTwoAux_label hlab_J hMarkedCenter hPSLJ
  obtain ⟨hAtag, hArank, hAn⟩ := hlab
  have hlab_eq : lab_J = ⟨.A, 1, 3⟩ := by
    obtain ⟨t, l, n⟩ := lab_J
    dsimp only at hAtag hArank hAn
    subst hAtag; subst hArank; subst hAn; rfl
  subst hlab_eq
  dsimp only [LargeEvenRawDatum] at hraw_J
  obtain ⟨K0, hK0field, hK0fin, hK0card, hQK⟩ := hraw_J
  obtain ⟨hs_J, hna_J, θ_J, hNJ, hhall_J⟩ := hQK
  have hDcard : Nat.card D = 3 ^ 2 := hDJ.1.2.2.1
  have hB : IsElemAbelian 3 B := hcfgcopy.1.2.2.2.2.2.2.1.1.1
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G :=
    hcfgcopy.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hcfgcopy.1.2.2.2.2.2.1.2.2.2
  have hB4 : 3 ^ 4 ≤ Nat.card B := by
    rw [hBcard]
    exact Nat.pow_le_pow_right (by norm_num) h4
  let hBJ : B ≤ Subgroup.normalizer (J : Set G) := hBBs.trans hNJ
  let α : ↥B →* MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K0)) :=
    (ggLAut J θ_J).comp (Subgroup.inclusion hBJ)
  have hE_ab : IsElemAbelian 3 α.range :=
    isElemAbelian_range (fun a b => hB.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hB.2 a a.2)) α
  have hI_inv : ∀ φ ∈ (LargeEvenMatConjImage (LargeEvenProjMk
      (LargeEvenSLGroup (Fin 2) K0)) Set.univ : Set (MulAut
        (LargeEvenProj (LargeEvenSLGroup (Fin 2) K0)))), φ⁻¹ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K0)) Set.univ := by
    rintro φ ⟨A, -, hφ⟩
    refine ⟨A⁻¹, Set.mem_univ _, fun h h' hh' => ?_⟩
    have hh : (h : GL (Fin 2) K0) = A * h' * A⁻¹ := by
      rw [hh']; group
    have h1 := hφ h' h hh
    simp only [MulAut.inv_apply]
    rw [← h1]
    simp
  have hE_I : (α.range : Set (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K0)))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K0)) Set.univ := by
    rintro φ ⟨b, rfl⟩
    have hbBs : ((b : ↥B) : G) ∈ Bs := hBBs b.2
    obtain ⟨ψ, hψI, hψind⟩ := hhall_J b hbBs
    let g : Subgroup.normalizer (J : Set G) :=
      ⟨((b : ↥B) : G)⁻¹, hBJ (B.inv_mem b.2)⟩
    have hαind : LargeEvenInduces θ_J (fun l l' => ((l' : G) = ((b : ↥B) : G)⁻¹ * l * b))
        (ggLAut J θ_J g) :=
      largeEvenInduces_ggLAut_inv (K := J) θ_J g.2
    have huniq : ggLAut J θ_J g = ψ := by
      refine ggNbrLangTriD4InnerTwoAux_induces_unique θ_J (fun l => ?_) hαind hψind
      have hlg : ((J.normalizerMonoidHom g l : J) : G) = ((b : ↥B) : G)⁻¹ * l * b := by
        simpa [g] using normalizerMonoidHom_coe J g l
      refine ⟨J.normalizerMonoidHom g l, hlg, ?_⟩
      intro y hy
      exact Subtype.ext (hy.trans hlg.symm)
    have hαb : α b = (ggLAut J θ_J g)⁻¹ := by
      dsimp only [α]
      change ggLAut J θ_J (⟨((b : ↥B) : G), hBJ b.2⟩ : Subgroup.normalizer (J : Set G)) =
        (ggLAut J θ_J g)⁻¹
      rw [← map_inv]
      have hg : (⟨((b : ↥B) : G), hBJ b.2⟩ : Subgroup.normalizer (J : Set G)) = g⁻¹ := by
        apply Subtype.ext
        simp [g]
      rw [hg]
    rw [hαb, huniq]
    exact hI_inv ψ hψI
  have hker_le : α.ker ≤ D.subgroupOf B := by
    intro b hb
    rw [Subgroup.mem_subgroupOf]
    rw [MonoidHom.mem_ker] at hb
    rw [hDJ.1.2.2.2.2.2.2]
    exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one J θ_J hJperf (g := ⟨b, hBJ b.2⟩) hb⟩
  have hker_card : Nat.card α.ker ≤ 3 ^ 2 := by
    rw [← hDcard]
    calc Nat.card α.ker ≤ Nat.card (D.subgroupOf B) := Subgroup.card_le_of_le hker_le
      _ = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDJ.1.1).toEquiv
  have hE9 : 3 ^ 2 ≤ Nat.card α.range := by
    have hcard := Subgroup.card_ker_mul_card_range α
    have h : 3 ^ 2 * 3 ^ 2 ≤ 3 ^ 2 * Nat.card α.range := by
      calc 3 ^ 2 * 3 ^ 2 = 3 ^ 4 := by norm_num
        _ ≤ Nat.card ↥B := hB4
        _ = Nat.card α.ker * Nat.card α.range := hcard.symm
        _ ≤ 3 ^ 2 * Nat.card α.range := Nat.mul_le_mul_right _ hker_card
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hK0char : CharP K0 2 := charP_two_of_card (m := 3) (by simpa using hK0card)
  haveI : CharP K0 2 := hK0char
  have hE3 : Nat.card α.range ≤ 3 :=
    NbrLangRest.card_le_of_forall_mem_conjImage_two (p := 3) Nat.prime_three (by norm_num)
      hs_J hna_J α.range hE_ab hE_I
  omega


end CFSG.StandardType

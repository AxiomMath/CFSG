module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOuterFactor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourRank
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_conjSubgroup_hom {N A : Subgroup G} {x : G} (hxN : x ∈ N) (hAN : A ≤ N) :
    (conjSubgroup A x).subgroupOf N =
      conjSubgroup (A.subgroupOf N) (⟨x, hxN⟩ : ↥N) := by
  ext y
  constructor
  · intro hy
    have hyA : x * (y : G) * x⁻¹ ∈ A :=
      mem_conjSubgroup_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    exact mem_conjSubgroup_iff.mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hyA))
  · intro hy
    have hyA : x * (y : G) * x⁻¹ ∈ A := by
      have h := Subgroup.mem_subgroupOf.mp (mem_conjSubgroup_iff.mp hy)
      simpa using h
    exact Subgroup.mem_subgroupOf.mpr (mem_conjSubgroup_iff.mpr hyA)

theorem mQuot_inf_pCoreOf_sup_le_two_19 {F S A : Subgroup G} (hFalt : IsAlt (Bar2 F) 5)
    (hS2 : IsPGroup 2 S) (hSF : S ≤ Subgroup.normalizer (F : Set G))
    (hAel : IsElemAbelian 2 A) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAFS : A ≤ F ⊔ S) :
    E3.mQuot A (A ⊓ pCoreOf 2 (F ⊔ S)) ≤ 2 := by
  classical
  let H : Subgroup G := F ⊔ S
  let Q : Subgroup G := pCoreOf 2 H
  change E3.mQuot A (A ⊓ Q) ≤ 2
  have hFS : H ≤ Subgroup.normalizer (F : Set G) := sup_le Subgroup.le_normalizer hSF
  have hφker : ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL F).comp
      (Subgroup.inclusion hFS)).ker = Q.subgroupOf H :=
    ker_rhoL_sup_eq_pCoreOf rfl hFalt hS2 hFS
  let φ : ↥H →* MulAut (Bar2 F) :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL F).comp (Subgroup.inclusion hFS)
  have hQsubEq : Q.subgroupOf H = CFSG.pCore 2 ↥H :=
    CFSG.openPCoreOf_subgroupOf 2 H
  have hQker : CFSG.pCore 2 ↥H ≤ φ.ker := by
    rw [hφker]
    intro x hx
    exact Subgroup.mem_map_of_mem H.subtype hx
  have hCQ : φ.ker ≤ CFSG.pCore 2 ↥H := by
    rw [hφker, hQsubEq]
  let Ψ : (↥H ⧸ CFSG.pCore 2 ↥H) →* MulAut (Bar2 F) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥H) φ hQker
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hφab : φ a = φ b := by
      have h1 : Ψ (QuotientGroup.mk a) = Ψ (QuotientGroup.mk b) := hxy
      simpa [Ψ, QuotientGroup.lift_mk] using h1
    refine QuotientGroup.eq.mpr ?_
    have hmem : a⁻¹ * b ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφab, inv_mul_cancel]
    exact hCQ hmem
  have hpRankAut : CFSG.Open.pRank 2 (⊤ : Subgroup (MulAut (Bar2 F))) ≤ 2 := by
    refine CFSG.SectionRank.pRank_le (p := 2) (by norm_num) ?_
    intro E _ hEab
    obtain ⟨e5⟩ := hFalt
    let e : MulAut (Bar2 F) ≃* Equiv.Perm (Fin 5) :=
      (MulAut.congr e5).trans CFSG.Quasithin.L139A5.autA5.symm
    have h4 := CFSG.ComponentClassification.RankTwoAltFive.card_le_four_of_elemAbelian_perm
      (E := E.map e.toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hEab e.toMonoidHom)
    calc Nat.card E = Nat.card (E.map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective e.injective).symm
      _ ≤ 4 := h4
      _ = 2 ^ 2 := by norm_num
  have hquotRank :
      CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 2 := by
    have h1 := CFSG.Quasithin.E3.pRank_le_pRank_map Ψ hΨinj (p := 2) Nat.prime_two
      (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))
    have h2 := CFSG.SectionRank.pRank_mono (p := 2) (by norm_num : 1 < 2)
      (H := Ψ.range) (K := ⊤) le_top
    calc CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))
        ≤ CFSG.Open.pRank 2 ((⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)).map Ψ) := h1
      _ = CFSG.Open.pRank 2 Ψ.range := by rw [Subgroup.map_top]
      _ ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (MulAut (Bar2 F))) := h2
      _ ≤ 2 := hpRankAut
  exact (CFSG.Quasithin.RonanE42.mQuot_inf_pCoreOf_le (K := H) (B := A)
    hAFS hAel.2 hAc).trans hquotRank

theorem pCoreOf_sup_inf_normalizer_le_sylow_19 {D : Data G} {F : Subgroup G}
    (hFM : F ≤ D.M) (hFsub : (F.subgroupOf D.M).IsSubnormal) :
    pCoreOf 2 (F ⊔ (D.T ⊓ Subgroup.normalizer (F : Set G))) ≤ D.T := by
  classical
  let N : Subgroup G := Subgroup.normalizer (F : Set G)
  let S : Subgroup G := D.T ⊓ N
  let H : Subgroup G := F ⊔ S
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le inf_le_left
  have hSN : S ≤ N := inf_le_right
  have hSylF : IsSylowIn 2 (D.T ⊓ F) F :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal
      (show QuasithinUnique.IsSylowTwoOf D.T D.M from
        CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM) hFM hFsub
  have hSylH : IsSylowIn 2 S H := by
    have hrel : S.relIndex H = (S ⊓ F).relIndex F := by
      have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hSN).1
      rwa [sup_comm] at h
    refine ⟨le_sup_right, hS2, ?_⟩
    rw [hrel]
    have hSF : S ⊓ F = D.T ⊓ F := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1.1, hx.2⟩
      · intro hx
        exact ⟨⟨hx.1, Subgroup.le_normalizer hx.2⟩, hx.2⟩
    rw [hSF]
    exact hSylF.2.2
  have hQn : ((pCoreOf 2 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hQT : pCoreOf 2 H ≤ S :=
    IsSylowIn.le_of_normal hSylH (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hQn
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  exact hQT.trans inf_le_left

theorem autA5_eq_conj_19 (c : Equiv.Perm (Fin 5)) (hc : c ∈ alternatingGroup (Fin 5)) :
    CFSG.Quasithin.L139A5.autA5 c = MulAut.conj (⟨c, hc⟩ : alternatingGroup (Fin 5)) := by
  rw [show CFSG.Quasithin.L139A5.autA5 c =
    MulAut.conjNormal (H := alternatingGroup (Fin 5)) c from rfl]
  exact MulAut.conjNormal_val (H := alternatingGroup (Fin 5)) (h := ⟨c, hc⟩)

theorem autA5_symm_conj_19 (c : Equiv.Perm (Fin 5)) (hc : c ∈ alternatingGroup (Fin 5)) :
    CFSG.Quasithin.L139A5.autA5.symm
      (MulAut.conj (⟨c, hc⟩ : alternatingGroup (Fin 5))) = c := by
  rw [← autA5_eq_conj_19 c hc, MulEquiv.symm_apply_apply]

theorem exists_rhoL_eq_19 {F : Subgroup G} (e5 : Bar2 F ≃* alternatingGroup (Fin 5))
    (c : alternatingGroup (Fin 5)) :
    ∃ x : ↥F, ((MulAut.congr e5).trans CFSG.Quasithin.L139A5.autA5.symm)
      (UC6S846.rhoL F ⟨(x : G), Subgroup.le_normalizer x.2⟩) = (c : Equiv.Perm (Fin 5)) := by
  obtain ⟨u, hu⟩ := e5.surjective c
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥F) u
  refine ⟨x, ?_⟩
  rw [MulEquiv.trans_apply, UC6S846.rhoL_inner F (x : G) x.2,
    CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
    autA5_symm_conj_19 (e5 (QuotientGroup.mk (⟨(x : G), x.2⟩ : ↥F)))
      (e5 (QuotientGroup.mk (⟨(x : G), x.2⟩ : ↥F))).2,
    show QuotientGroup.mk (⟨(x : G), x.2⟩ : ↥F) = u from hx, hu]

theorem exists_inCalO_of_proj_two_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A F : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hAM : ¬ A ≤ pCoreOf 2 D.M) (hF : F = L ∨ F = K)
    (hFalt : IsAlt (Bar2 F) 5) (hAF : A ≤ normalizer (F : Set G))
    (hCF : E3.cClos V₀ 2 D.T ≤ normalizer (F : Set G))
    (hqF : E3.mQuot A (A ⊓ pCoreOf 2 (F ⊔ (D.T ⊓ normalizer (F : Set G)))) = 2) :
    ∃ g : G, InCalO 2 D.M ⊥ V₀ g ∧ ¬ InCalO 1 D.M ⊥ V₀ g := by
  classical
  let N : Subgroup G := normalizer (F : Set G)
  let S : Subgroup G := D.T ⊓ N
  let H : Subgroup G := F ⊔ S
  let Q : Subgroup G := pCoreOf 2 H
  have hqF' : E3.mQuot A (A ⊓ Q) = 2 := hqF
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    have : IsMulCommutative A := hAel.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hFM : F ≤ D.M := by
    rcases hF with rfl | rfl
    · exact CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
    · exact CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hFsubOpen : CFSG.Open.IsSubnormal F D.M := by
    rcases hF with rfl | rfl
    · exact h.hyp.hL.1.1
    · exact h.hK.1
  have hFsub : (F.subgroupOf D.M).IsSubnormal :=
    (CFSG.Quasithin.isSubnormal_iff_subgroupOf hFM).mp hFsubOpen
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le inf_le_left
  have hSN : S ≤ N := inf_le_right
  have hAN : A ≤ N := hAF
  have hFH : F ≤ H := fun x hx => Subgroup.mem_sup_left hx
  have hFS : H ≤ Subgroup.normalizer (F : Set G) :=
    sup_le Subgroup.le_normalizer hSN
  have hAH : A ≤ H := by
    intro a ha
    change a ∈ F ⊔ S
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hAT ha, hAF ha⟩)
  have hHM : H ≤ D.M := sup_le hFM (inf_le_left.trans hTM)
  have hQH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hQN : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hQT : Q ≤ D.T := pCoreOf_sup_inf_normalizer_le_sylow_19 hFM hFsub
  have hC2T : E3.cClos V₀ 2 D.T ≤ D.T := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hC2 : E3.cClos V₀ 2 D.T ≤ H := by
    intro x hx
    change x ∈ F ⊔ S
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hC2T hx, hCF hx⟩)
  have hAQ : ¬ A ≤ Q := by
    intro hAQ'
    have h0 : E3.mQuot A (A ⊓ Q) = 0 := by
      rw [inf_eq_left.mpr hAQ', E3.mQuot_self]
    omega
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  have h5F : 5 ∣ Nat.card F := by
    rcases hF with hFL | hFK
    · rw [hFL]
      exact (h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2
    · rw [hFK]
      exact UC22.InS3.UC49.five_dvd_card_of_isAlt h.hKshape
  have hFcalC : F ∈ calC D.M := by
    rcases hF with hFL | hFK
    · rw [hFL]; exact h.hyp.hL.1
    · rw [hFK]; exact h.hK
  have hFsimple : IsSimpleGroup (Bar2 F) := by
    obtain ⟨e5⟩ := hFalt
    exact MulEquiv.isSimpleGroup e5
  have hP5 : ∀ N' : Subgroup G, N' ≤ H → H ≤ Subgroup.normalizer (N' : Set G) →
      ¬ N' ≤ Q → 5 ∣ Nat.card N' := by
    intro N' hNH hHN hNQ
    have hFN' : F ≤ N' :=
      le_of_normal_of_isSimple_19 hFsimple hFcalC.2.1 hS2 hSN
        (fun y hy _ hρ => UC22.F09.mem_pCoreOf_of_rhoL_eq_one hFalt hy hρ) hNH hHN hNQ
    exact h5F.trans (Subgroup.card_dvd_of_le hFN')
  have hZ : A ⊓ centerOf (E3.wClos V₀ 2 Q) ≠ ⊥ :=
    inf_centerOf_wClos_two_ne_bot_19 h.hyp.hyp125 hm hsp hN2 hHM hQH hQN hQT hAH hAgamma hAM
      hAQ (le_of_eq hqF') hC2 hP5
  let φN : ↥N →* MulAut (Bar2 F) := UC6S846.rhoL F
  have hφkerH : (φN.comp (Subgroup.inclusion hFS)).ker = Q.subgroupOf H :=
    ker_rhoL_sup_eq_pCoreOf rfl hFalt hS2 hFS
  have hkerQ : ∀ a : G, (haH : a ∈ H) → φN ⟨a, hFS haH⟩ = 1 → a ∈ Q := by
    intro a haH h1
    have hmem : (⟨a, haH⟩ : ↥H) ∈ (φN.comp (Subgroup.inclusion hFS)).ker := h1
    rw [hφkerH] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  let f : ↥A →* MulAut (Bar2 F) := φN.comp (Subgroup.inclusion hAN)
  have hfker : f.ker = (A ⊓ Q).subgroupOf A := by
    ext a
    constructor
    · intro ha
      have h1 : φN ⟨(a : G), hAF a.2⟩ = 1 := MonoidHom.mem_ker.mp ha
      exact Subgroup.mem_subgroupOf.mpr
        ⟨a.2, hkerQ a (hAH a.2) (by simpa using h1)⟩
    · intro ha
      have haQ : (a : G) ∈ Q := (Subgroup.mem_subgroupOf.mp ha).2
      have h1 : φN ⟨(a : G), hAF a.2⟩ = 1 :=
        UC6S846.rhoL_eq_one_of_mem_pCoreOf hFH (hFS (hAH a.2)) haQ
      exact MonoidHom.mem_ker.mpr h1
  let E : Subgroup (MulAut (Bar2 F)) := (A.subgroupOf N).map φN
  have hErange : E = f.range := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨(a : G), hAN a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  have hEcard : Nat.card E = 4 := by
    rw [hErange]
    have h1 : Nat.card f.range = f.ker.relIndex ⊤ := by
      rw [Subgroup.relIndex_ker (⊤ : Subgroup ↥A) f, Subgroup.map_top]
    rw [h1, hfker]
    have h2 : ((A ⊓ Q).subgroupOf A).relIndex (⊤ : Subgroup ↥A) = (A ⊓ Q).relIndex A := by
      rw [← Subgroup.relIndex_subgroupOf (H := A ⊓ Q) (K := A) (L := A) le_rfl,
        Subgroup.subgroupOf_self]
    rw [h2]
    have hA2 : IsPGroup 2 A := D.sylowM.isPGroup.to_le hAT
    rw [E3.relIndex_eq_two_pow hA2 (A ⊓ Q), hqF']
    norm_num
  have hEel : IsElemAbelian 2 E := by
    refine ⟨isMulCommutative_iff.mpr (fun x y => ?_), ?_⟩
    · obtain ⟨a, haA, ha⟩ := x.2
      obtain ⟨b, hbA, hb⟩ := y.2
      apply Subtype.ext
      change (x : MulAut (Bar2 F)) * (y : MulAut (Bar2 F)) =
        (y : MulAut (Bar2 F)) * (x : MulAut (Bar2 F))
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg φN (Subtype.ext (hAc a.1 (Subgroup.mem_subgroupOf.mp haA)
        b.1 (Subgroup.mem_subgroupOf.mp hbA)))
    · rintro x ⟨a, haA, ha⟩
      rw [← ha, ← map_pow,
        show (a : ↥N) ^ 2 = 1 from Subtype.ext
          (hAel.2 a.1 (Subgroup.mem_subgroupOf.mp haA))]
      exact map_one φN
  obtain ⟨e5⟩ := hFalt
  let ee : MulAut (Bar2 F) ≃* Equiv.Perm (Fin 5) :=
    (MulAut.congr e5).trans CFSG.Quasithin.L139A5.autA5.symm
  let Ep : Subgroup (Equiv.Perm (Fin 5)) := E.map ee.toMonoidHom
  have hEpel : IsElemAbelian 2 Ep := CFSG.SectionRank.isElemAbelian_map hEel ee.toMonoidHom
  have hEpcard : Nat.card Ep = 4 := by
    rw [Subgroup.card_map_of_injective ee.injective, hEcard]
  obtain ⟨c, hcalt, hcgood, hcgoodinv⟩ :=
    perm5_klein_conj_normalizer Ep hEpel hEpcard
  have hxex : ∃ x0 : ↥F, ee (φN ⟨(x0 : G), Subgroup.le_normalizer x0.2⟩) = c :=
    exists_rhoL_eq_19 e5 ⟨c, hcalt⟩
  obtain ⟨x0, hψx⟩ := hxex
  set x : G := (x0 : G) with hxdef
  have hxH : x ∈ H := hFH x0.2
  have hxN : x ∈ N := Subgroup.le_normalizer x0.2
  have hψx' : ee (φN ⟨x, hxN⟩) = c := hψx
  have key : ∀ (y : ↥F) (d : Equiv.Perm (Fin 5)) (hdalt : d ∈ alternatingGroup (Fin 5)),
      ee (φN ⟨(y : G), Subgroup.le_normalizer y.2⟩) = d →
      (∀ e ∈ Ep, e ∈ Subgroup.normalizer
        (conjSubgroup Ep d : Set (Equiv.Perm (Fin 5))) → e = 1) →
      ∀ a ∈ A, a ∈ Subgroup.normalizer (conjSubgroup A (y : G) : Set G) → a ∈ Q := by
    intro y d hdalt hψy hdgood a haA haNorm
    have hyN : (y : G) ∈ N := Subgroup.le_normalizer y.2
    have hψy' : ee (φN ⟨(y : G), hyN⟩) = d := hψy
    have haN : a ∈ N := hAF haA
    have hAyN : conjSubgroup A (y : G) ≤ N := by
      intro z hz
      rw [mem_conjSubgroup_iff] at hz
      have hz' : (y : G) * z * (y : G)⁻¹ ∈ N := hAF hz
      have hzeq : z = (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * (y : G) := by group
      rw [hzeq]
      exact N.mul_mem (N.mul_mem (N.inv_mem hyN) hz') hyN
    have haNorm' : (⟨a, haN⟩ : ↥N) ∈ Subgroup.normalizer
        ((conjSubgroup A (y : G)).subgroupOf N : Set ↥N) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hAyN]
      exact Subgroup.mem_subgroupOf.mpr haNorm
    have hYeq : (conjSubgroup A (y : G)).subgroupOf N =
        conjSubgroup (A.subgroupOf N) (⟨(y : G), hyN⟩ : ↥N) :=
      subgroupOf_conjSubgroup_hom hyN hAF
    rw [hYeq] at haNorm'
    have hconj0 : conjSubgroup (conjSubgroup (A.subgroupOf N) ⟨(y : G), hyN⟩)
        ⟨a, haN⟩ = conjSubgroup (A.subgroupOf N) ⟨(y : G), hyN⟩ :=
      conjSubgroup_eq_iff_mem_normalizer.mpr haNorm'
    have hmap0 : (conjSubgroup (A.subgroupOf N) ⟨(y : G), hyN⟩).map φN =
        conjSubgroup E (φN ⟨(y : G), hyN⟩) := by
      have h := Eq.symm <| map_conjSubgroup_hom φN (A.subgroupOf N) (⟨(y : G), hyN⟩ : ↥N)
      rwa [show (A.subgroupOf N).map φN = E from rfl] at h
    have hmap1 : (conjSubgroup (conjSubgroup (A.subgroupOf N) ⟨(y : G), hyN⟩)
        ⟨a, haN⟩).map φN =
        conjSubgroup (conjSubgroup E (φN ⟨(y : G), hyN⟩)) (φN ⟨a, haN⟩) := by
      have h := Eq.symm <| map_conjSubgroup_hom φN
        (conjSubgroup (A.subgroupOf N) ⟨(y : G), hyN⟩) (⟨a, haN⟩ : ↥N)
      rwa [show (conjSubgroup (A.subgroupOf N) ⟨(y : G), hyN⟩).map φN =
        conjSubgroup E (φN ⟨(y : G), hyN⟩) from hmap0] at h
    have hconjE : conjSubgroup (conjSubgroup E (φN ⟨(y : G), hyN⟩)) (φN ⟨a, haN⟩) =
        conjSubgroup E (φN ⟨(y : G), hyN⟩) := by
      rw [← hmap1, ← hmap0, hconj0]
    have hmapE : (conjSubgroup E (φN ⟨(y : G), hyN⟩)).map ee.toMonoidHom =
        conjSubgroup Ep d := by
      have h := Eq.symm <| map_conjSubgroup_hom ee.toMonoidHom E (φN ⟨(y : G), hyN⟩)
      rw [show E.map ee.toMonoidHom = Ep from rfl,
        show ee.toMonoidHom (φN ⟨(y : G), hyN⟩) = d from hψy'] at h
      exact h
    have hconjEe : conjSubgroup (conjSubgroup Ep d) (ee (φN ⟨a, haN⟩)) =
        conjSubgroup Ep d := by
      have h := congrArg (Subgroup.map ee.toMonoidHom) hconjE
      rw [← map_conjSubgroup_hom ee.toMonoidHom (conjSubgroup E (φN ⟨(y : G), hyN⟩))
        (φN ⟨a, haN⟩), hmapE] at h
      exact h
    have hnormEe : ee (φN ⟨a, haN⟩) ∈ Subgroup.normalizer
        (conjSubgroup Ep d : Set (Equiv.Perm (Fin 5))) :=
      conjSubgroup_eq_iff_mem_normalizer.mp hconjEe
    have hmemEp : ee (φN ⟨a, haN⟩) ∈ Ep :=
      Subgroup.mem_map_of_mem ee.toMonoidHom
        (Subgroup.mem_map_of_mem φN (Subgroup.mem_subgroupOf.mpr haA))
    have h1 : ee (φN ⟨a, haN⟩) = 1 := hdgood _ hmemEp hnormEe
    have h2 : φN ⟨a, haN⟩ = 1 :=
      ee.injective (h1.trans (map_one ee).symm)
    exact hkerQ a (hAH haA) (by simpa using h2)
  have hxQ : ∀ a ∈ A, a ∈ Subgroup.normalizer (conjSubgroup A x : Set G) → a ∈ Q :=
    key x0 c hcalt hψx' hcgood
  have hψxinv : ee (φN ⟨x⁻¹, Subgroup.le_normalizer (F.inv_mem x0.2)⟩) = c⁻¹ := by
    have h1 : (⟨x⁻¹, Subgroup.le_normalizer (F.inv_mem x0.2)⟩ : ↥N) =
        (⟨x, hxN⟩ : ↥N)⁻¹ := Subtype.ext (by simp)
    rw [h1, map_inv, map_inv, hψx']
  have hxQinv : ∀ a ∈ A, a ∈ Subgroup.normalizer (conjSubgroup A x⁻¹ : Set G) → a ∈ Q :=
    key x0⁻¹ c⁻¹ ((alternatingGroup (Fin 5)).inv_mem hcalt) (by simpa using hψxinv) hcgoodinv
  exact exists_inCalO_two_not_one_19 h.hyp.hyp125 hm hQH hQN hAH hAgamma hqF' hZ hxH
    hxQ hxQinv

theorem isAlt_bar2_left_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hLn : ¬ (L.subgroupOf D.M).Normal) : IsAlt (Bar2 L) 5 := by
  rcases dichotomy_19 h with ⟨-, x, hxM, hKx⟩ | ⟨-, hLn', -⟩
  · obtain ⟨e⟩ := uc22p20d_bar2_conj (x⁻¹) L
    have hLKx : uc22p20bCj x⁻¹ L = K := by rw [hKx]; rfl
    obtain ⟨e5⟩ := h.hKshape
    exact ⟨e.trans (hLKx.symm ▸ e5)⟩
  · exact absurd hLn' hLn

theorem rhoL_sup_eq_one_of_rhoL_eq_one_19 {D : Data G} {L K : Subgroup G}
    (hLc : L ∈ calC D.M) (hKc : K ∈ calC D.M) (hne : L ≠ K)
    {a : G} (haN : a ∈ Subgroup.normalizer ((L ⊔ K : Subgroup G) : Set G))
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hρL : UC6S846.rhoL L ⟨a, haL⟩ = 1) (hρK : UC6S846.rhoL K ⟨a, haK⟩ = 1) :
    UC6S846.rhoL (L ⊔ K) ⟨a, haN⟩ = 1 := by
  classical
  have hKL : K ≤ Subgroup.normalizer (L : Set G) := calC_le_normalizer_of_ne hLc hKc hne
  have hLK : L ≤ Subgroup.normalizer (K : Set G) := calC_le_normalizer_of_ne hKc hLc hne.symm
  have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ K) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left
      (sup_le Subgroup.le_normalizer hKL)
  have hO2K : pCoreOf 2 K ≤ pCoreOf 2 (L ⊔ K) := by
    have h' := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (X := K) (H := K ⊔ L)
      le_sup_left (sup_le Subgroup.le_normalizer hLK)
    simpa only [sup_comm] using h'
  apply MulEquiv.ext
  intro zbar
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(L ⊔ K)) zbar
  rw [MulAut.one_apply]
  refine (UC6S846.rhoL_fix_iff (L ⊔ K) ⟨a, haN⟩ z).2 ?_
  have hz' : (z : G) ∈ (L : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L K hKL]
    exact z.2
  obtain ⟨l, hlL, k, hkK, hlk⟩ := hz'
  have hcL : a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
    (UC6S846.rhoL_fix_iff L ⟨a, haL⟩ ⟨l, hlL⟩).1 (by rw [hρL]; rfl)
  have hcK : a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
    (UC6S846.rhoL_fix_iff K ⟨a, haK⟩ ⟨k, hkK⟩).1 (by rw [hρK]; rfl)
  have hlNormK : l ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K) (hLK hlL)
  have hconjK : l * (a * k * a⁻¹ * k⁻¹) * l⁻¹ ∈ pCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.mp hlNormK _).mp hcK
  have hzk : a * (z : G) * a⁻¹ * (z : G)⁻¹ =
      (a * l * a⁻¹ * l⁻¹) * (l * (a * k * a⁻¹ * k⁻¹) * l⁻¹) := by
    rw [← hlk]
    group
  rw [hzk]
  exact (pCoreOf 2 (L ⊔ K)).mul_mem (hO2L hcL) (hO2K hconjK)

theorem mem_pCoreOf_of_rhoL_sup_eq_one_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {y : G} (hyJ : y ∈ L ⊔ K)
    (hyN : y ∈ normalizer ((L ⊔ K : Subgroup G) : Set G))
    (hρ : UC6S846.rhoL (L ⊔ K) ⟨y, hyN⟩ = 1) : y ∈ pCoreOf 2 (L ⊔ K) :=
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.inf_centralizerBar_le_pCore_of_center_bar2
      (P := L ⊔ K) (center_bar2_sup_eq_bot_19 h)
    ⟨CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.mem_centralizerBar_iff.mpr
      ⟨hyJ, fun z hz =>
        (UC6S846.rhoL_fix_iff (L ⊔ K) ⟨y, hyN⟩ ⟨z, hz⟩).1 (by rw [hρ]; rfl)⟩, hyJ⟩

theorem mem_pCoreOf_LKT_of_rhoL_eq_one_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    {a : G} (haT : a ∈ D.T) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hρL : UC6S846.rhoL L ⟨a, haL⟩ = 1) (hρK : UC6S846.rhoL K ⟨a, haK⟩ = 1) :
    a ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
  have hLpM : S17.Lp D 5 ≤ D.M := S17.Lp_le_M D 5
  have hNM : D.M ≤ Subgroup.normalizer ((S17.Lp D 5 : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLpM).mp (s13_Lp_normal D.M 5)
  have hTNJ : D.T ≤ Subgroup.normalizer ((L ⊔ K : Subgroup G) : Set G) := by
    rw [← h.hLK]
    exact D.sylowM.le.trans hNM
  have haJN : a ∈ Subgroup.normalizer ((L ⊔ K : Subgroup G) : Set G) := hTNJ haT
  have hρJ : UC6S846.rhoL (L ⊔ K) ⟨a, haJN⟩ = 1 :=
    rhoL_sup_eq_one_of_rhoL_eq_one_19 h.hyp.hL.1 h.hK h.hne.symm haJN haL haK hρL hρK
  exact UC6S846.mem_pCoreOf_sup_of_rhoL_eq_one D.sylowM.isPGroup hTNJ
    (fun y hy hy' hρ => mem_pCoreOf_of_rhoL_sup_eq_one_19 h hy hy' hρ)
    (Subgroup.mem_sup_right haT : a ∈ (L ⊔ K) ⊔ D.T) haJN hρJ

theorem orest_LK_noswap_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    (hJA : ¬ ⁅L ⊔ K, A⁆ ≤ pCoreOf 2 D.M)
    (hq : 2 < E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)))
    (hin : A ≤ (D.T ⊓ (L ⊔ K)) ⊔ pCoreOf 2 (L ⊔ K ⊔ D.T))
    (hτ : E1.tauOf (L ⊔ K ⊔ D.T) D.T A ≤ normalizer (L : Set G)) :
    ∃ g : G, InCalO 2 D.M ⊥ V₀ g ∧ ¬ InCalO 1 D.M ⊥ V₀ g := by
  classical
  let J : Subgroup G := L ⊔ K
  let X : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 X
  let NL : Subgroup G := normalizer (L : Set G)
  let NK : Subgroup G := normalizer (K : Set G)
  let SL : Subgroup G := D.T ⊓ NL
  let SK : Subgroup G := D.T ⊓ NK
  let HL : Subgroup G := L ⊔ SL
  let HK : Subgroup G := K ⊔ SK
  let QL : Subgroup G := pCoreOf 2 HL
  let QK : Subgroup G := pCoreOf 2 HK
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, hmq⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    have : IsMulCommutative A := hAel.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hV : IsElemAbelian 2 V₀ := h.hyp.hyp125.pairFacts.elemAbelian₀
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hKc : K ∈ calC D.M := h.hK
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hLc.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hKc.1
  have hne : L ≠ K := h.hne.symm
  have hLalt : IsAlt (Bar2 L) 5 := isAlt_bar2_left_19 h hLn
  have hTsyl : IsSylowIn 2 D.T X := TwelveShort.isSylowIn_of_le D le_sup_right
  have hAτ : A ≤ E1.tauOf X D.T A :=
    le_sup_left.trans (E1.le_tauOf hTsyl hAT hAel)
  have hAL : A ≤ NL := hAτ.trans hτ
  have hAM : A ≤ D.M := hAT.trans hTM
  have hAK : A ≤ NK := fun a ha =>
    mem_normalizer_right_19 h (hAM ha) (hAL ha) hne
  have hAM' : ¬ A ≤ pCoreOf 2 D.M := by
    intro hAOM
    apply hJA
    have hJN : J ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
      (sup_le hLM hKM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    have hcalc : ⁅J, pCoreOf 2 D.M⁆ ≤ pCoreOf 2 D.M := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hJN
    exact (Subgroup.commutator_mono le_rfl hAOM).trans hcalc
  have hAW : A ≤ E3.wClos V₀ 2 D.T :=
    E3.le_wClos_of_mQuot_le (V := V₀) hV gA hAT hAg
      (k := 2) (by rw [hmq]; norm_num) (lt_trans (by norm_num) hm)
  have hC2T : E3.cClos V₀ 2 D.T ≤ D.T := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hC2τ : E3.cClos V₀ 2 D.T ≤ E1.tauOf X D.T A := by
    intro t ht
    have htT : t ∈ D.T := hC2T ht
    have htC : t ∈ Subgroup.centralizer (E3.wClos V₀ 2 D.T : Set G) :=
      (Subgroup.mem_inf.mp ht).2
    rw [E1.mem_tauOf]
    refine ⟨htT, (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
      (Subgroup.mem_sup_right htT), fun a ha => ?_⟩
    have h1 : a * t = t * a := Subgroup.mem_centralizer_iff.mp htC a (hAW ha)
    have h2 : ⁅t, a⁆ = 1 := by
      rw [commutatorElement_def, show t * a = a * t from h1.symm]
      group
    rw [h2]
    exact (pCoreOf 2 X).one_mem
  have hCFL : E3.cClos V₀ 2 D.T ≤ NL := hC2τ.trans hτ
  have hCFK : E3.cClos V₀ 2 D.T ≤ NK := by
    intro t ht
    exact mem_normalizer_right_19 h (hTM (hC2T ht)) (hCFL ht) hne
  have hSL2 : IsPGroup 2 SL := D.sylowM.isPGroup.to_le inf_le_left
  have hSK2 : IsPGroup 2 SK := D.sylowM.isPGroup.to_le inf_le_left
  have hSNL : SL ≤ NL := inf_le_right
  have hSNK : SK ≤ NK := inf_le_right
  have hHLX : HL ≤ X := sup_le (fun x hx => Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
    (fun x hx => Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1)
  have hHKX : HK ≤ X := sup_le (fun x hx => Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))
    (fun x hx => Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1)
  have hLsub : (L.subgroupOf D.M).IsSubnormal :=
    (CFSG.Quasithin.isSubnormal_iff_subgroupOf hLM).mp hLc.1
  have hKsub : (K.subgroupOf D.M).IsSubnormal :=
    (CFSG.Quasithin.isSubnormal_iff_subgroupOf hKM).mp hKc.1
  have hQLT : QL ≤ D.T := pCoreOf_sup_inf_normalizer_le_sylow_19 hLM hLsub
  have hQKT : QK ≤ D.T := pCoreOf_sup_inf_normalizer_le_sylow_19 hKM hKsub
  have hmL : E3.mQuot A (A ⊓ QL) ≤ 2 := by
    refine mQuot_inf_pCoreOf_sup_le_two_19 hLalt hSL2 hSNL hAel hAc ?_
    intro a ha
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hAT ha, hAL ha⟩)
  have hmK : E3.mQuot A (A ⊓ QK) ≤ 2 := by
    refine mQuot_inf_pCoreOf_sup_le_two_19 h.hKshape hSK2 hSNK hAel hAc ?_
    intro a ha
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hAT ha, hAK ha⟩)
  have hQeq : A ⊓ Q = A ⊓ QL ⊓ QK := by
    refine le_antisymm ?_ ?_
    · intro a ha
      obtain ⟨haA, haQ⟩ := Subgroup.mem_inf.mp ha
      have haHL : a ∈ HL := Subgroup.mem_sup_right
        (Subgroup.mem_inf.mpr ⟨hAT haA, hAL haA⟩)
      have haHK : a ∈ HK := Subgroup.mem_sup_right
        (Subgroup.mem_inf.mpr ⟨hAT haA, hAK haA⟩)
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mem_inf.mpr ⟨haA,
          CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hHLX (Subgroup.mem_inf.mpr ⟨haHL, haQ⟩)⟩
      · exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hHKX (Subgroup.mem_inf.mpr ⟨haHK, haQ⟩)
    · rintro a ⟨⟨haA, haQL⟩, haQK⟩
      have haT : a ∈ D.T := hQLT haQL
      have haNL : a ∈ NL := hAL haA
      have haNK : a ∈ NK := hAK haA
      have hρL : UC6S846.rhoL L ⟨a, haNL⟩ = 1 :=
        UC6S846.rhoL_eq_one_of_mem_pCoreOf (X := L) (H := HL)
          (fun x hx => Subgroup.mem_sup_left hx) haNL haQL
      have hρK : UC6S846.rhoL K ⟨a, haNK⟩ = 1 :=
        UC6S846.rhoL_eq_one_of_mem_pCoreOf (X := K) (H := HK)
          (fun x hx => Subgroup.mem_sup_left hx) haNK haQK
      have hQ : a ∈ Q := mem_pCoreOf_LKT_of_rhoL_eq_one_19 h haT haNL haNK hρL hρK
      exact Subgroup.mem_inf.mpr ⟨haA, hQ⟩
  have hmle : E3.mQuot A (A ⊓ Q) ≤ E3.mQuot A (A ⊓ QL) + E3.mQuot A (A ⊓ QK) := by
    have hA2 : IsPGroup 2 A := D.sylowM.isPGroup.to_le hAT
    have hEq2 : A ⊓ Q = (A ⊓ QL) ⊓ (A ⊓ QK) := by
      rw [hQeq]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    have hrel : (A ⊓ Q).relIndex A ≤ (A ⊓ QL).relIndex A * (A ⊓ QK).relIndex A := by
      rw [hEq2]
      exact Subgroup.relIndex_inf_le
    have h1 : (A ⊓ Q).relIndex A = 2 ^ E3.mQuot A (A ⊓ Q) :=
      E3.relIndex_eq_two_pow hA2 _
    have h2 : (A ⊓ QL).relIndex A = 2 ^ E3.mQuot A (A ⊓ QL) :=
      E3.relIndex_eq_two_pow hA2 _
    have h3 : (A ⊓ QK).relIndex A = 2 ^ E3.mQuot A (A ⊓ QK) :=
      E3.relIndex_eq_two_pow hA2 _
    rw [h1, h2, h3, ← pow_add] at hrel
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hrel
  by_cases hL2 : E3.mQuot A (A ⊓ QL) = 2
  · exact exists_inCalO_of_proj_two_19 D hSg h hm hN2 hAgamma hAM' (Or.inl rfl) hLalt hAL
      hCFL hL2
  · have hqQ : 2 < E3.mQuot A (A ⊓ Q) := hq
    have hL1 : E3.mQuot A (A ⊓ QL) ≤ 1 := by omega
    have hK2 : E3.mQuot A (A ⊓ QK) = 2 := by omega
    exact exists_inCalO_of_proj_two_19 D hSg h hm hN2 hAgamma hAM' (Or.inr rfl) h.hKshape hAK
      hCFK hK2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

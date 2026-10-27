module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RootLine
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QTor
public import CFSG.HardMathSupport.Seitz.ExceptionsTransport.G2SplitTorusPlane
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
public import CFSG.LieType.Chevalley.G2FieldFourCoverRoots
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.G2FieldFour
open CFSG.LieType.Chevalley.ExceptionalCover
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley
open CFSG.AGLEmbedding.KFactProofs.G2Q

theorem g2_prod_cartanChar_rootV {K : Type} [Field K] (ζ : Kˣ) :
    (∏ i, (cartanChar (τ := .G2) (Pi.mulSingle ia ζ) i) ^ rootV i) = 1 := by
  rw [cartanChar_mulSingle]
  calc (∏ i : Fin Tag.G2.rank, (ζ ^ Tag.G2.cartan ia i) ^ rootV i)
      = ∏ i : Fin Tag.G2.rank, ζ ^ (Tag.G2.cartan ia i * rootV i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        exact (zpow_mul ζ (Tag.G2.cartan ia i) (rootV i)).symm
    _ = ζ ^ (∑ i : Fin Tag.G2.rank, Tag.G2.cartan ia i * rootV i) :=
        Finset.prod_zpow_eq_zpow_sum ..
    _ = ζ ^ (0 : ℤ) := by
        have h : (∑ i : Fin Tag.G2.rank, Tag.G2.cartan ia i * rootV i) = 0 := by
          decide +kernel
        rw [h]
    _ = 1 := zpow_zero ζ


theorem g2_torusElt_ia_centralizes_rootV {K : Type} [Field K] (ζ : Kˣ) :
    ∀ g ∈ rootRankOneGroup .G2 K rootV,
      torusElt .G2 K ia ζ * g = g * torusElt .G2 K ia ζ := by
  intro g hg
  have hroot : IsRoot .G2 rootV := (mem_posRoots.1 rootV_mem).1
  obtain ⟨-, -, -, -, -, -, -, hcent⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .G2 K hroot
  have ha : (∏ i, (cartanChar (τ := .G2) (Pi.mulSingle ia ζ) i) ^ rootV i) = 1 :=
    g2_prod_cartanChar_rootV ζ
  have h := hcent (cartanChar (τ := .G2) (Pi.mulSingle ia ζ)) ha g hg
  have h2 : rootDiagUnit .G2 (cartanChar (τ := .G2) (Pi.mulSingle ia ζ)) =
      torusElt .G2 K ia ζ := by
    rw [torusElt_eq_rootDiagUnit, cartanChar_mulSingle]
  rwa [h2] at h

theorem g2_rootRankOneGroup_rootV_lieModel {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    LieModel ↥(rootRankOneGroup .G2 K rootV) .PSL 2 2 n := by
  have hroot : IsRoot .G2 rootV := (mem_posRoots.1 rootV_mem).1
  have hL : rootRankOneGroup .G2 K rootV =
      rootSubgroup .G2 K rootV ⊔ rootSubgroup .G2 K (-rootV) :=
    (exceptional_Lang_root_rank_one_torus_transport .G2 K hroot).1
  let e1 : Matrix.SpecialLinearGroup (Fin 2) K ≃*
      ↥(rootSubgroup .G2 K rootV ⊔ rootSubgroup .G2 K (-rootV)) := rootSL2Equiv hroot
  let e2 : ↥(rootSubgroup .G2 K rootV ⊔ rootSubgroup .G2 K (-rootV)) ≃*
      ↥(rootRankOneGroup .G2 K rootV) := (MulEquiv.subgroupCongr hL).symm
  let : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  exact CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two hn hKf
    (e1.trans e2).symm

theorem k_G2RootLine_holds : K_G2RootLine := by
  intro Y _ _ n hY hq r hr hr3 hdvd E hEel hEcard
  classical
  have hCE : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 2 n :=
    LieModel.chevalleyExceptionalModel hY (by decide)
  obtain ⟨hn2, K, hF, hFin, hcp, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model hCE
  have hdvdK : r ∣ Nat.card K - 1 := by
    rw [hK]
    exact hdvd
  let E' : Subgroup (adjointGroup .G2 K) := E.map e.toMonoidHom
  have hE'el : IsElemAbelian r E' :=
    CFSG.SectionRank.isElemAbelian_map hEel e.toMonoidHom
  have hE'card : Nat.card E' = r ^ 2 := by
    have h := Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective (K := E)
    rw [show E' = E.map e.toMonoidHom from rfl, h, hEcard]
  have hE'p : IsPGroup r E' := hE'el.isPGroup
  have hp5 : 5 ≤ r := by
    have hr2 : r ≠ 2 := by omega
    have hr3' : r ≠ 3 := by omega
    exact hr.five_le_of_ne_two_of_ne_three hr2 hr3'
  obtain ⟨g, hg⟩ :=
    CFSG.HardMathSupport.Seitz.ExceptionsTransport.exists_conj_le_torus
      hr hp5 hdvdK E' hE'p
  let T : Subgroup (adjointGroup .G2 K) := CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K
  let F0 : Subgroup (adjointGroup .G2 K) := E'.map (MulAut.conj g⁻¹).toMonoidHom
  have hF0le : F0 ≤ T := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨z, hz, hyz⟩ := hg y hy
    change ((g : ModGL .G2 K)⁻¹ * (y : ModGL .G2 K) * (g : ModGL .G2 K)) ∈ torusGroup .G2 K
    have h : (g : ModGL .G2 K)⁻¹ * (y : ModGL .G2 K) * (g : ModGL .G2 K) = z := by
      rw [hyz]
      calc (g : ModGL .G2 K)⁻¹ * ((g : ModGL .G2 K) * z * (g : ModGL .G2 K)⁻¹) *
            (g : ModGL .G2 K)
          = ((g : ModGL .G2 K)⁻¹ * (g : ModGL .G2 K)) * z *
              ((g : ModGL .G2 K)⁻¹ * (g : ModGL .G2 K)) := by group
        _ = z := by rw [inv_mul_cancel]; simp
    rw [h]
    exact hz
  let F : Subgroup T := F0.subgroupOf T
  have hF0el : IsElemAbelian r F0 :=
    CFSG.SectionRank.isElemAbelian_map hE'el (MulAut.conj g⁻¹).toMonoidHom
  have hcardF0 : Nat.card F0 = r ^ 2 := by
    rw [show F0 = E'.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective,
      hE'card]
  have hcardF : Nat.card F = r ^ 2 := by
    rw [← hcardF0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF0le).toEquiv
  let A : Subgroup (adjointGroup .G2 K) :=
    (torusTorsion K r).subgroupOf (adjointGroup .G2 K)
  let Tr : Subgroup T := A.subgroupOf T
  have hTTA : torusTorsion K r ≤ adjointGroup .G2 K :=
    (torusTorsion_le_torusGroup r).trans torusGroup_le_adjoint
  have hFleTr : F ≤ Tr := by
    intro y hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    refine (mem_torusTorsion_iff).2 ⟨Subgroup.mem_subgroupOf.1 (y : T).2, ?_⟩
    have hy0 : ((y : T) : adjointGroup .G2 K) ∈ F0 := hy
    have hpow : (((y : T) : adjointGroup .G2 K) ^ r) = 1 := hF0el.2 _ hy0
    simpa using congrArg (fun z : adjointGroup .G2 K => (z : ModGL .G2 K)) hpow
  have hTrcard : Nat.card Tr = r ^ 2 := by
    have h1 : Nat.card Tr = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A ≤ T from by
        intro x hx
        exact Subgroup.mem_subgroupOf.2 ((torusTorsion_le_torusGroup r)
          (Subgroup.mem_subgroupOf.1 hx)))).toEquiv
    rw [h1]
    have h2 : Nat.card A = Nat.card (torusTorsion K r) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTTA).toEquiv
    rw [h2]
    have : NeZero r := ⟨hr.ne_zero⟩
    exact natCard_torusTorsion hdvdK
  have hF_eq_Tr : F = Tr :=
    Subgroup.eq_of_le_of_card_ge hFleTr (by rw [hcardF, hTrcard])
  have : Fact r.Prime := ⟨hr⟩
  have hdvdU : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units (α := K)]
    exact hdvdK
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' r hdvdU
  let yA : adjointGroup .G2 K := ⟨tz ζ 1, tz_mem_adjointGroup ζ 1⟩
  have hyA_tz : (yA : ModGL .G2 K) = tz ζ 1 := rfl
  have htz : (tz ζ 1 : ModGL .G2 K) = torusElt .G2 K ia ζ := tz_left ζ
  have hyA_pow : (tz ζ 1 : ModGL .G2 K) ^ r = 1 := by
    rw [htz]
    change (torusEltHom .G2 K ia ζ) ^ r = 1
    rw [← map_pow (torusEltHom .G2 K ia) ζ r, ← hζ, pow_orderOf_eq_one, map_one]
  have hyA_ne : (tz ζ 1 : ModGL .G2 K) ≠ 1 := by
    intro h1
    have h2 : (ζ : K) ^ 2 = 1 :=
      sq_eq_one_of_torusElt_eq_one ia (a := ζ) (by rw [← htz]; exact h1)
    have hζ2 : ζ ^ 2 = 1 := Units.ext h2
    have hdvd2 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one hζ2
    have hζ1 : ζ = 1 := by
      have hord : orderOf ζ = 1 := by
        have h2le : orderOf ζ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
        omega
      exact orderOf_eq_one_iff.1 hord
    rw [hζ1, orderOf_one] at hζ
    omega
  have hyA_order : orderOf yA = r := by
    rw [← Subgroup.orderOf_coe yA]
    exact orderOf_eq_prime hyA_pow hyA_ne
  have hyA_tors : (yA : ModGL .G2 K) ∈ torusTorsion K r := by
    rw [mem_torusTorsion_iff]
    exact ⟨tz_mem_torusGroup ζ 1, hyA_pow⟩
  have hyA_T : yA ∈ T := by
    change yA ∈ CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K
    rw [mem_torusSub]
    exact tz_mem_torusGroup ζ 1
  let yT : ↥T := ⟨yA, hyA_T⟩
  have hyT_Tr : yT ∈ Tr := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hyA_tors
  have hyT_F : yT ∈ F := by
    rw [hF_eq_Tr]
    exact hyT_Tr
  have hyA_F0 : yA ∈ F0 := hyT_F
  let b : adjointGroup .G2 K := (MulAut.conj g) yA
  have hbE' : b ∈ E' := by
    obtain ⟨x, hxE, hx⟩ := Subgroup.mem_map.1 hyA_F0
    have hb : (MulAut.conj g) yA = x := by
      rw [← hx]
      change g * (g⁻¹ * x * (g⁻¹)⁻¹) * g⁻¹ = x
      group
    change (MulAut.conj g) yA ∈ E'
    rw [hb]
    exact hxE
  let B' : Subgroup (adjointGroup .G2 K) := Subgroup.zpowers b
  have hB'le : B' ≤ E' := Subgroup.zpowers_le.2 hbE'
  have hB'card : Nat.card B' = r := by
    rw [Nat.card_zpowers]
    have h1 : orderOf b = orderOf yA := by
      rw [show b = (MulAut.conj g) yA from rfl]
      exact (MulAut.conj g).orderOf_eq yA
    rw [h1, hyA_order]
  have hrootV : IsRoot .G2 rootV := (mem_posRoots.1 rootV_mem).1
  obtain ⟨hLgroup, -, -, -, -, -, -, hcent⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .G2 K hrootV
  obtain ⟨-, -, -, -, -, hLle, -⟩ := exceptional_Lang_root_rank_one_data .G2 K rootV
  let L_adj : Subgroup (adjointGroup .G2 K) :=
    (rootRankOneGroup .G2 K rootV).subgroupOf (adjointGroup .G2 K)
  let L' : Subgroup (adjointGroup .G2 K) := L_adj.map (MulAut.conj g).toMonoidHom
  have hyA_cent : yA ∈ Subgroup.centralizer (L_adj : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : (l : ModGL .G2 K) ∈ rootRankOneGroup .G2 K rootV := hl
    have hcomm := g2_torusElt_ia_centralizes_rootV (K := K) ζ (l : ModGL .G2 K) hl'
    have hcomm' : torusElt .G2 K ia ζ * (l : ModGL .G2 K) =
        (l : ModGL .G2 K) * torusElt .G2 K ia ζ := hcomm
    exact Subtype.ext (by simpa [hyA_tz, htz] using hcomm'.symm)
  have hb_cent : b ∈ Subgroup.centralizer (L' : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := Subgroup.mem_map.1 hl
    have hcomm : l0 * yA = yA * l0 :=
      (Subgroup.mem_centralizer_iff.1 hyA_cent) l0 hl0
    change (MulAut.conj g) l0 * (MulAut.conj g) yA =
      (MulAut.conj g) yA * (MulAut.conj g) l0
    calc (MulAut.conj g) l0 * (MulAut.conj g) yA
        = (MulAut.conj g) (l0 * yA) := (map_mul (MulAut.conj g) l0 yA).symm
      _ = (MulAut.conj g) (yA * l0) := by rw [hcomm]
      _ = (MulAut.conj g) yA * (MulAut.conj g) l0 := map_mul (MulAut.conj g) yA l0
  have hB'cent : B' ≤ Subgroup.centralizer (L' : Set (adjointGroup .G2 K)) :=
    Subgroup.zpowers_le.2 hb_cent
  have hL2 : LieModel ↥L' .PSL 2 2 n := by
    have eLadj : ↥L_adj ≃* ↥(rootRankOneGroup .G2 K rootV) :=
      Subgroup.subgroupOfEquivOfLe hLle
    have eMap : ↥L_adj ≃* ↥L' :=
      Subgroup.equivMapOfInjective L_adj (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective
    have hrootModel : LieModel ↥(rootRankOneGroup .G2 K rootV) .PSL 2 2 n :=
      g2_rootRankOneGroup_rootV_lieModel hn2 hK
    exact LieModel.of_mulEquiv (eMap.symm.trans eLadj).symm hrootModel
  let B : Subgroup Y := B'.comap e.toMonoidHom
  have hBcard : Nat.card B = r := by
    have hmap : B.map e.toMonoidHom = B' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective B'
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective (K := B), hmap,
      hB'card]
  have hBle : B ≤ E := by
    calc B = B'.comap e.toMonoidHom := rfl
      _ ≤ (E.map e.toMonoidHom).comap e.toMonoidHom := Subgroup.comap_mono hB'le
      _ = E := Subgroup.comap_map_eq_self_of_injective e.injective E
  let Y0 : Subgroup Y := L'.comap e.toMonoidHom
  have hY0le : Y0 ≤ Subgroup.centralizer (B : Set Y) := by
    have h := CFSG.GorensteinWalter.centralizer_map_le_of_mulEquiv e.symm B' L'
      (Subgroup.le_centralizer_iff.mp hB'cent)
    simpa [Y0, B, Subgroup.comap_equiv_eq_map_symm] using h
  have hY0L2 : LieModel ↥Y0 .PSL 2 2 n := by
    let f : ↥Y0 →* ↥L' :=
      { toFun := fun y => ⟨e y, y.2⟩
        map_one' := by ext; simp
        map_mul' := fun y z => by ext; simp }
    have hfinj : Function.Injective f := by
      intro y z h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    have hfsurj : Function.Surjective f := by
      intro l
      refine ⟨⟨e.symm l, ?_⟩, ?_⟩
      · show e (e.symm l) ∈ L'
        rw [MulEquiv.apply_symm_apply]
        exact l.2
      · apply Subtype.ext
        exact MulEquiv.apply_symm_apply e l
    exact LieModel.of_mulEquiv (MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩).symm hL2
  exact ⟨B, hBle, hBcard, Y0, hY0le, hY0L2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

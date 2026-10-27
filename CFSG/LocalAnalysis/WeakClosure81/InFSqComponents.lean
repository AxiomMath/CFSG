module

public import CFSG.LocalAnalysis.WeakClosure81.InFSqAlmostSimple
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Setup
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierCyclicCentralFactor
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9Group
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Near (IsChiefFactorOf IsNormalIn)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InFGroup CompFactorAutInF W3Lem45_2Chief)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (InF)
open scoped Pointwise commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

theorem isComponent_map_conjAut {K : Subgroup Q} (hK : CFSG.IsComponent K) (t : Q) :
    CFSG.IsComponent (K.map (MulAut.conj t).toMonoidHom) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK

theorem orbitClosure_normal {K T : Subgroup Q} (hKT : orbitClosure K T ⊔ T = ⊤) :
    (orbitClosure K T).Normal := by
  have hF : orbitClosure K T ≤ Subgroup.normalizer (orbitClosure K T : Set Q) :=
    Subgroup.le_normalizer
  have hT : T ≤ Subgroup.normalizer (orbitClosure K T : Set Q) :=
    fun t ht =>
      CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514.mem_normalizer_orbitClosure ht
  have htop : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (orbitClosure K T : Set Q) := by
    rw [← hKT]
    exact sup_le hF hT
  exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr htop)

theorem centralizer_orbitClosure_le {K T : Subgroup Q}
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) (hT : IsPGroup 2 T)
    (hKT : orbitClosure K T ⊔ T = ⊤) :
    Subgroup.centralizer (orbitClosure K T : Set Q) ≤ orbitClosure K T := by
  let F : Subgroup Q := orbitClosure K T
  have hF : F.Normal := orbitClosure_normal hKT
  have hQF2 : IsPGroup 2 (Q ⧸ F) := by
    haveI : F.Normal := hF
    haveI : (F.subgroupOf (⊤ : Subgroup Q)).Normal := hF.subgroupOf ⊤
    have htop : IsPGroup 2 ((⊤ : Subgroup Q) ⧸ F.subgroupOf ⊤) :=
      CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Q)
        (L := F) (Q := T) (K := ⊤) hT le_top
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hF]; exact le_top) hKT
    have he : (F.subgroupOf (⊤ : Subgroup Q)).map
        (Subgroup.topEquiv (G := Q)).toMonoidHom = F := by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact IsPGroup.of_equiv htop
      (QuotientGroup.congr (F.subgroupOf ⊤) F Subgroup.topEquiv he)
  let C : Subgroup Q := Subgroup.centralizer (F : Set Q)
  have hCnorm : C.Normal := by
    haveI : F.Normal := hF
    exact Subgroup.normal_centralizer
  let φ : C →* Q ⧸ F := (QuotientGroup.mk' F).comp C.subtype
  let Z : Subgroup C := φ.ker
  have hZeq : Z = (C ⊓ F).subgroupOf C := by
    ext c
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hc
      exact ⟨c.2, (QuotientGroup.eq_one_iff (c : Q)).mp hc⟩
    · rintro ⟨-, hcF⟩
      exact (QuotientGroup.eq_one_iff (c : Q)).mpr hcF
  have hZcenter : Z ≤ Subgroup.center C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hz' : z ∈ (C ⊓ F).subgroupOf C := hZeq ▸ hz
    have hzF : (z : Q) ∈ F := (Subgroup.mem_subgroupOf.mp hz').2
    exact (Subgroup.mem_centralizer_iff.mp x.2 (z : Q) hzF).symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCZ2 : IsPGroup 2 (C ⧸ Z) := by
    have hrange2 : IsPGroup 2 φ.range := hQF2.to_subgroup φ.range
    exact IsPGroup.of_equiv hrange2 (QuotientGroup.quotientKerEquivRange φ).symm
  obtain ⟨n, hn⟩ := hCZ2.exists_card_eq
  have hZindex : Z.index = 2 ^ n := by
    rw [Subgroup.index_eq_card, hn]
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := C)
  let D : Subgroup C := (S : Subgroup C) ⊔ Z
  have hDtop : D = ⊤ := by
    have hDdvd2 : D.index ∣ 2 ^ n := by
      rw [← hZindex]
      exact Subgroup.index_dvd_of_le (show Z ≤ D from le_sup_right)
    have hDdvdS : D.index ∣ (S : Subgroup C).index :=
      Subgroup.index_dvd_of_le (show (S : Subgroup C) ≤ D from le_sup_left)
    have hnot2 : ¬ 2 ∣ D.index := fun h => S.not_dvd_index (h.trans hDdvdS)
    have hcop : Nat.Coprime D.index (2 ^ n) :=
      Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hnot2
    have h1 : D.index = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hDdvd2
    exact Subgroup.index_eq_one.mp h1
  have hSnormal : (S : Subgroup C).Normal :=
    CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor.internal_factor_normal
      (S : Subgroup C) Z hZcenter hDtop
  have hSchar : (S : Subgroup C).Characteristic :=
    Sylow.characteristic_of_normal S hSnormal
  have hSN : (S.map C.subtype).Normal := by
    haveI : C.Normal := hCnorm
    haveI : (S : Subgroup C).Characteristic := hSchar
    exact ConjAct.normal_of_characteristic_of_normal (H := C) (K := (S : Subgroup C))
  have hN2 : IsPGroup 2 (S.map C.subtype) := IsPGroup.map S.isPGroup' C.subtype
  have hNnorm : ∀ x ∈ (⊤ : Subgroup Q), ∀ y ∈ S.map C.subtype, x * y * x⁻¹ ∈ S.map C.subtype :=
    fun x _ y hy => hSN.conj_mem y hy x
  have hSNbot : S.map C.subtype ≤ pCoreOf 2 (⊤ : Subgroup Q) :=
    CFSG.ClassicalGroups.PCoreSection.le_pCoreOf le_top hNnorm hN2
  rw [hO2] at hSNbot
  have hSbot : (S : Subgroup C) = ⊥ := by
    have hmapbot : S.map C.subtype = ⊥ := le_bot_iff.mp hSNbot
    exact Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective |>.mp hmapbot
  have hCleF : C ≤ F := by
    have hZtop : Z = ⊤ := by
      rw [← hDtop]
      change Z = (S : Subgroup C) ⊔ Z
      rw [hSbot, bot_sup_eq]
    rw [hZeq] at hZtop
    have hCF : C ≤ C ⊓ F :=
      (Subgroup.subgroupOf_eq_top (H := C ⊓ F) (K := C)).mp hZtop
    exact hCF.trans inf_le_right
  exact hCleF

theorem orbitClosure_le_layer {K T : Subgroup Q} (hK : CFSG.IsComponent K) :
    orbitClosure K T ≤ CFSG.layer Q := by
  refine orbitClosure_le fun a _ => ?_
  exact CFSG.LocalCores.component_le_layer (isComponent_map_conjAut hK a)

theorem layer_le_orbitClosure {K T : Subgroup Q}
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) (hT : IsPGroup 2 T)
    (hKT : orbitClosure K T ⊔ T = ⊤) :
    CFSG.layer Q ≤ orbitClosure K T := by
  let F : Subgroup Q := orbitClosure K T
  have hF : F.Normal := orbitClosure_normal hKT
  have hC : Subgroup.centralizer (F : Set Q) ≤ F :=
    centralizer_orbitClosure_le hO2 hT hKT
  change CFSG.layer Q ≤ F
  refine sSup_le fun K' hK' => ?_
  rcases CFSG.LocalCores.component_normal_subgroup hK' hF with h | h
  · exact h
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans hC

theorem orbitClosure_le_of_mem_le {K T W : Subgroup Q} (hWn : W.Normal)
    {t : Q} (htW : K.map (MulAut.conj t).toMonoidHom ≤ W) :
    orbitClosure K T ≤ W := by
  refine orbitClosure_le fun s hs => ?_
  haveI : W.Normal := hWn
  have hWmap : W.map (MulAut.conj (s * t⁻¹)).toMonoidHom = W :=
    Subgroup.Normal.map_conj_eq W (s * t⁻¹)
  have h1 : (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj (s * t⁻¹)).toMonoidHom ≤ W := by
    rw [← hWmap]
    exact Subgroup.map_mono htW
  have h2 : (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj (s * t⁻¹)).toMonoidHom
      = K.map (MulAut.conj s).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rwa [h2] at h1

theorem comm_subgroup_map_conj_of_isComponent {K K' : Subgroup Q}
    (hK : CFSG.IsComponent K) (hK' : K'.Normal) (t : Q) :
    K.map (MulAut.conj t).toMonoidHom ≤ K' ∨
      ⁅K.map (MulAut.conj t).toMonoidHom, K'⁆ = ⊥ :=
  CFSG.LocalCores.component_normal_subgroup (isComponent_map_conjAut hK t) hK'

theorem isChiefFactorOf_orbitClosure {K T : Subgroup Q} (hK : CFSG.IsComponent K)
    (hKT : orbitClosure K T ⊔ T = ⊤) :
    IsChiefFactorOf ⊤ (orbitClosure K T)
      (orbitClosure K T ⊓ Subgroup.centralizer (orbitClosure K T : Set Q)) := by
  classical
  let F : Subgroup Q := orbitClosure K T
  let Z : Subgroup Q := F ⊓ Subgroup.centralizer (F : Set Q)
  have hF : F.Normal := orbitClosure_normal hKT
  have hZ : Z.Normal := by
    haveI : F.Normal := hF
    exact Subgroup.normal_inf_normal F (Subgroup.centralizer (F : Set Q))
  have hZle : Z ≤ F := inf_le_left
  have hZlt : Z < F := by
    refine lt_of_le_of_ne hZle ?_
    intro heq
    have hFC : F ≤ Subgroup.centralizer (F : Set Q) := heq.symm.le.trans inf_le_right
    have hcomm : ⁅F, F⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hFC
    have hFab : IsMulCommutative ↥F := Subgroup.commutator_self_eq_bot_iff.mp hcomm
    have hKF : K ≤ F := le_orbitClosure K T
    have hKcomm : IsMulCommutative ↥K := by
      refine ⟨⟨fun a b => ?_⟩⟩
      have h := hFab.is_comm.comm
        (⟨(a : Q), hKF a.2⟩ : F) (⟨(b : Q), hKF b.2⟩ : F)
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
    haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    haveI : Group.IsPerfect ↥K := hK.1.1
    exact Group.IsPerfect.not_isMulCommutative K hKcomm
  refine ⟨⟨le_top, ?_⟩, ⟨le_top, ?_⟩, hZlt, ?_⟩
  · exact le_of_eq (Subgroup.normalizer_eq_top (h := hZ)).symm
  · exact le_of_eq (Subgroup.normalizer_eq_top (h := hF)).symm
  · intro K' hK' hZK' hK'F
    have hK'norm : K'.Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hK'.2)
    by_cases hex : ∃ t ∈ T, K.map (MulAut.conj t).toMonoidHom ≤ K'
    · right
      obtain ⟨t, -, htW⟩ := hex
      exact le_antisymm hK'F (orbitClosure_le_of_mem_le hK'norm htW)
    · left
      push Not at hex
      have hcomm_all : ∀ t ∈ T, ⁅K.map (MulAut.conj t).toMonoidHom, K'⁆ = ⊥ := by
        intro t ht
        rcases comm_subgroup_map_conj_of_isComponent hK hK'norm t with h | h
        · exact absurd h (hex t ht)
        · exact h
      have hFleCK' : F ≤ Subgroup.centralizer (K' : Set Q) := by
        refine orbitClosure_le fun t ht => ?_
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm_all t ht)
      have hK'leCF : K' ≤ Subgroup.centralizer (F : Set Q) := by
        have h : ⁅K', F⁆ = ⊥ := by
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hFleCK'
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      exact le_antisymm (le_inf hK'F hK'leCF) hZK'

theorem inF_top_of_components (h43c : W3Lem45_2Chief) {m : ℕ} (hm : 1 ≤ m)
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥)
    {K : Subgroup Q} (hK : CFSG.IsComponent K) {T : Subgroup Q}
    (hTsyl : IsSylowIn 2 T ⊤) (hKT : orbitClosure K T ⊔ T = ⊤)
    (hcf : ∀ T : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
      CompFactorAutInF m ⊤ T) :
    InF m (⊤ : Subgroup Q) := by
  let F : Subgroup Q := orbitClosure K T
  have hF : F.Normal := orbitClosure_normal hKT
  have hT2 : IsPGroup 2 T := hTsyl.isPGroup
  have hQF2 : IsPGroup 2 (Q ⧸ F) := by
    haveI : F.Normal := hF
    haveI : (F.subgroupOf (⊤ : Subgroup Q)).Normal := hF.subgroupOf ⊤
    have htop : IsPGroup 2 ((⊤ : Subgroup Q) ⧸ F.subgroupOf ⊤) :=
      CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Q)
        (L := F) (Q := T) (K := ⊤) hT2 le_top
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hF]; exact le_top) hKT
    have he : (F.subgroupOf (⊤ : Subgroup Q)).map
        (Subgroup.topEquiv (G := Q)).toMonoidHom = F := by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact IsPGroup.of_equiv htop
      (QuotientGroup.congr (F.subgroupOf ⊤) F Subgroup.topEquiv he)
  have hFT : ∀ T' : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → F ⊔ T' = ⊤ := by
    intro T' hT'
    have hT'in : IsSylowIn 2 T' ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT'
    haveI : F.Normal := hF
    let P : Sylow 2 Q := hT'in.isPGroup.toSylow (by simpa using hT'in.not_dvd_relIndex)
    have h := CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top (N := F) hQF2 P
    rw [IsPGroup.toSylow_coe] at h
    rw [sup_comm]
    exact h
  have hC : Subgroup.centralizer (F : Set Q) ≤ F :=
    centralizer_orbitClosure_le hO2 hT2 hKT
  have hFeq : F = CFSG.layer Q :=
    le_antisymm (orbitClosure_le_layer hK) (layer_le_orbitClosure hO2 hT2 hKT)
  have hperf : ⁅F, F⁆ = F := by
    rw [hFeq]
    exact CFSG.LocalCores.layer_perfect
  have hchief : IsChiefFactorOf ⊤ F (F ⊓ Subgroup.centralizer (F : Set Q)) :=
    isChiefFactorOf_orbitClosure hK hKT
  exact inF_top_of_chiefFactor_perfect h43c hm hO2 hperf inf_le_right hchief hC hFT hcf

theorem inFSq_of_components (h43c : W3Lem45_2Chief) {G : Type} [Group G] [Finite G]
    {m : ℕ} {H : Subgroup G} {K T : Subgroup (Bar2 H)}
    (hm : 1 ≤ m) (hK : CFSG.IsComponent K) (hT : IsSylowIn 2 T ⊤)
    (hKT : orbitClosure K T ⊔ T = ⊤)
    (hcf : ∀ T : Subgroup (Bar2 H), CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
      CompFactorAutInF m ⊤ T) :
    InFSq m H := by
  have hO2 : pCoreOf 2 (⊤ : Subgroup (Bar2 H)) = ⊥ := by
    rw [CFSG.CGT.PushingUpLit.Glue.pCoreOf_top_eq, pCore_two_bar2_eq_bot]
  exact inF_top_of_components h43c hm hO2 hK hT hKT hcf

end CFSG.LocalAnalysis.WeakClosure81

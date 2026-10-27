module

public import CFSG.Quasithin.Vol2.Ch11SecO10P
public import CFSG.Quasithin.Vol2.Ch11SecE42S3b
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT2

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecE
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G} {z : G}

theorem fsuV_le_reducedAggregate_of_fsu {K I' : Subgroup G} (hfsu : FSU G T K I') :
    fsuV T I' ≤ reducedAggregate (K ⊔ T) := by
  have hN := (SecA.reducedAggregate_props (K ⊔ T)).2.2.2
  refine conjClosure_le fun t ht x hx => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_sup_right ht)) x).mp
    (hfsu.irrPlus.1 hx)

theorem isElemAbelian_fsuV_of_fsu {K I' : Subgroup G} (hfsu : FSU G T K I') :
    IsElemAbelian 2 (fsuV T I') := by
  obtain ⟨hsq, hcomm, -⟩ := SecA.reducedAggregate_props (K ⊔ T)
  have hV := fsuV_le_reducedAggregate_of_fsu hfsu
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (hV a.2) _ (hV b.2))⟩⟩, fun x hx => hsq x (hV hx)⟩

theorem fsuV_le_T_of_fsu {K I' : Subgroup G} (hfsu : FSU G T K I')
    (hT : QuasithinUnique.IsSylowTwoOf T (K ⊔ T)) : fsuV T I' ≤ T :=
  (fsuV_le_reducedAggregate_of_fsu hfsu).trans ((SecA.reducedAggregate_props (K ⊔ T)).2.2.1.trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT))

theorem kz_setting (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1)
    (hc : Conf11_4_2 T L I n V₁ z) :
    ⁅kz L V₁ z, kz L V₁ z⁆ = kz L V₁ z ∧
      CFSG.IsQuasisimple (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∧
      QuasithinUnique.IsSylowTwoOf T (kz L V₁ z ⊔ T) ∧
      T ≤ Subgroup.normalizer (kz L V₁ z : Set G) ∧ LOf L V₁ ≤ kz L V₁ z := by
  have h := hc.hyp
  obtain ⟨hTK, hLK, -, -, -, -⟩ := conf_spec hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X h hc.vi hX).1.1
  have hKc := (kz_spec hF43 h1102 h1110 h1111 h hcV hc.vi hc.mem hc.ne_one).1
  exact ⟨perfect_of_mem_cComp hKc, isQuasisimple_kz hF hS hc,
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right, hTK, hLK⟩

theorem inf_centralizer_fsuV_le_kz (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43)
    (h701 : Stmt7_0_1) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h1141 : Stmt11_4_1) (hc : Conf11_4_2 T L I n V₁ z) {I' : Subgroup G}
    (hfsu : FSU G T (kz L V₁ z) I') :
    T ⊓ Subgroup.centralizer (fsuV T I' : Set G) ≤ pCoreOf 2 (kz L V₁ z ⊔ T) := by
  obtain ⟨hKp, hq, hTs, hTK, -⟩ := kz_setting hF hS hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨hKV, -, hO, hne⟩ := fsuV_spec h701 hfsu hTK
  exact inf_centralizer_le_pCoreOf_of_quasisimple hKp hq hTs hTK hKV hO hne

theorem fsuV_le_rOf_kz (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (h701 : Stmt7_0_1)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1)
    (hc : Conf11_4_2 T L I n V₁ z) {I' : Subgroup G} (hfsu : FSU G T (kz L V₁ z) I') :
    fsuV T I' ≤ ROf T L V₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hTs, hTK, hLK⟩ := kz_setting hF hS hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨hKV, hTV, -, -⟩ := fsuV_spec h701 hfsu hTK
  have hVT := fsuV_le_T_of_fsu hfsu hTs
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right)
    (sup_le (hLK.trans hKV) hTV) (hc.hyp.fsu.sylow.1.to_le hVT)

theorem isFFModule_fsuV_kz (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (h701 : Stmt7_0_1)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1)
    (hc : Conf11_4_2 T L I n V₁ z) {I' : Subgroup G} (hfsu : FSU G T (kz L V₁ z) I')
    (hJ : ¬ thompsonJ (ROf T L V₁) ≤ pCoreOf 2 (kz L V₁ z ⊔ T)) :
    ∃ _ : IsMulCommutative ↥(fsuV T I'),
      IsFFModule (V := ↥(fsuV T I'))
        (Subgroup.normalizer ((autOn (kz L V₁ z) (fsuV T I') : Set (MulAut ↥(fsuV T I'))))) := by
  obtain ⟨-, -, -, hTK, -⟩ := kz_setting hF hS hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨-, hTV, -, -⟩ := fsuV_spec h701 hfsu hTK
  have hVe := isElemAbelian_fsuV_of_fsu hfsu
  have hVR := fsuV_le_rOf_kz hF hS hF43 h701 h1102 h1110 h1111 h1141 hc hfsu
  obtain ⟨A, hA, hAO⟩ : ∃ A, IsMaxElemAbelian (ROf T L V₁) A ∧
      ¬ A ≤ pCoreOf 2 (kz L V₁ z ⊔ T) := by
    by_contra hcon
    refine hJ ?_
    unfold thompsonJ
    exact iSup₂_le fun A hA => by_contra fun h' => hcon ⟨A, hA, h'⟩
  have hAT : A ≤ T := hA.1.trans (SecD.ROf_le_T hc.hyp V₁)
  have hAV : ¬ A ≤ Subgroup.centralizer (fsuV T I' : Set G) := fun hle => hAO fun a ha =>
    inf_centralizer_fsuV_le_kz hF hS hF43 h701 h1102 h1110 h1111 h1141 hc hfsu
      ⟨hAT ha, hle ha⟩
  obtain ⟨B, hB, hB1, hBe, hBc⟩ := isFFModule_autOn hVe hVR hTV hAT hA hAV
  exact ⟨hVe.1, B, hB.trans (SecS.autOn_le_normalizer hTK), hB1, hBe, hBc⟩

end CFSG.Quasithin.Vol2.Ch11.O10

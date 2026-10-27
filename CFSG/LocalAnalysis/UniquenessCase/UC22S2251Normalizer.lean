module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251f
import CFSG.LocalAnalysis.UniquenessCase.UC22P22nA
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowFrattiniSup
import CFSG.Quasithin.Background.BlueprintB2Bridge
import CFSG.Quasithin.Background.G2
import CFSG.RankThree.PartOne.S11c.Simple168
import CFSG.RankThree.FFModules.RepMulAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

variable {G : Type} [Group G] [Finite G]

namespace S2251

theorem normalizer_mbarImage_eq {M V T W : Subgroup G}
    (hV : M ≤ normalizer (V : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hWT : W ≤ T)
    (hTW : T ≤ normalizer (W : Set G))
    (hR : ∀ R : Subgroup G, W ≤ R → R ≤ T →
      normalizer (R : Set G) ≤ normalizer (W : Set G)) :
    normalizer (mbarImage M V W : Set (MBar M V)) =
      mbarImage M V (M ⊓ normalizer (W : Set G)) := by
  have : (kerAct M V).Normal := kerAct_normal M V hV
  set C : Subgroup G := M ⊓ centralizer (V : Set G)
  have hCM : C ≤ M := inf_le_left
  have hCn : M ≤ normalizer (C : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hCM).1 (by
      simpa [C, kerAct] using (kerAct_normal M V hV))
  have hmem : ∀ x : M, (QuotientGroup.mk x : MBar M V) ∈ mbarImage M V W ↔
      (x : G) ∈ W ⊔ C := by
    intro x
    change x ∈ ((W.subgroupOf M).map (QuotientGroup.mk' (kerAct M V).normalCore)).comap
      (QuotientGroup.mk' (kerAct M V).normalCore) ↔ (x : G) ∈ W ⊔ C
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.normalCore_eq_self]
    have hC : C.subgroupOf M = kerAct M V := by
      ext y
      simp [C, kerAct, Subgroup.mem_subgroupOf]
    rw [← hC, ← Subgroup.subgroupOf_sup (hWT.trans hT.le) hCM]
    rfl
  refine le_antisymm ?_ ?_
  · intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : (g : G) ∈ normalizer ((W ⊔ C : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      by_cases hxM : x ∈ M
      · have hyM : (g : G) * x * (g : G)⁻¹ ∈ M :=
          M.mul_mem (M.mul_mem g.2 hxM) (M.inv_mem g.2)
        have h := (mem_normalizer_iff.1 hq (QuotientGroup.mk (⟨x, hxM⟩ : M)))
        simpa only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, hmem,
          Subgroup.coe_mul, Subgroup.coe_inv] using h
      · have hyM : (g : G) * x * (g : G)⁻¹ ∉ M := by
          intro hx
          apply hxM
          have h := M.mul_mem (M.mul_mem (M.inv_mem g.2) hx) g.2
          simpa [mul_assoc] using h
        exact ⟨fun hx => (hxM ((sup_le (hWT.trans hT.le) hCM) hx)).elim,
          fun hx => (hyM ((sup_le (hWT.trans hT.le) hCM) hx)).elim⟩
    obtain ⟨c, hc, n, hn, hgn⟩ :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_mul_of_mem_normalizer_sup
        hCM hCn (CFSG.ABGLocalTools.isSylowOf_iff.1 hT) hWT hTW
        (hR _ (le_inf hWT le_sup_left) inf_le_left) g.2 hg
    refine ⟨⟨n, hn.1⟩, hn, ?_⟩
    have hgc : g = (⟨c, hCM hc⟩ : M) * ⟨n, hn.1⟩ := Subtype.ext hgn
    rw [hgc, QuotientGroup.mk_mul,
      (uc22br_gt_mk_eq_one_iff hV ⟨c, hCM hc⟩).2 hc.2, one_mul]
    rfl
  · rintro _ ⟨x, hx, rfl⟩
    exact P2251f.mem_normalizer_mbarImage x.2 hx.2

theorem normalizer_mbarImage_jOf (D : Data G) :
    normalizer (mbarImage D.M D.U (jOf D.T) : Set (MBar D.M D.U)) =
      mbarImage D.M D.U (D.M ⊓ normalizer (jOf D.T : Set G)) := by
  refine normalizer_mbarImage_eq (P22x.uc22p22xf_hV D) D.sylowM
    (uc22p22e_jOf_le_self D.T) ?_ ?_
  · intro t ht
    exact CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem
      (uc22p22e_normalizes_jOf_T D t ht)
  · intro R hJR hRT g hg
    exact CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem
      (uc22p22e_conj_jOf fun x hx => hRT ((mem_normalizer_iff.1 hg x).1 (hJR hx)))

theorem normalizer_mbarImage_proofS (D : Data G) :
    normalizer (mbarImage D.M D.U (proofS D) : Set (MBar D.M D.U)) =
      mbarImage D.M D.U (D.M ⊓ normalizer (proofS D : Set G)) := by
  have hS : proofS D = CFSG.Quasithin.baum D.T := by
    change D.T ⊓ centralizer
      (((CFSG.elemThompsonCenterTorsion D.T 2).map D.T.subtype) : Set G) = _
    rw [CFSG.Quasithin.elemThompsonCenterTorsion_map_subtype_eq_omegaOneCenterOf]
    rfl
  rw [hS]
  refine normalizer_mbarImage_eq (P22x.uc22p22xf_hV D) D.sylowM inf_le_left ?_ ?_
  · exact le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_baum D.T)
  · intro R hBR hRT
    have h := CFSG.Quasithin.baum_eq_of_le hBR hRT
    rw [h]
    exact CFSG.Quasithin.normalizer_le_normalizer_baum R

theorem inf_centralizer_proofN_eq_bot (D : Data G) :
    mbarImage D.M D.U
        ((D.M ⊓ normalizer (jOf D.T : Set G)) ⊓ centralizer (proofE D : Set G)) ⊓
      centralizer (mbarImage D.M D.U (proofN D) : Set (MBar D.M D.U)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := P22x.uc22p22xf_hV D
  set X : Subgroup G := D.M ⊓ normalizer (jOf D.T : Set G)
  set K : Subgroup G := X ⊓ centralizer (proofE D : Set G)
  set Xb := mbarImage D.M D.U X
  set Kb := mbarImage D.M D.U K
  set Db := centralizer (mbarImage D.M D.U (proofN D) : Set (MBar D.M D.U))
  have hNb : (mbarImage D.M D.U (proofN D)).Normal :=
    uc22br4_mbarImage_normal _ _ _ (uc22p22e_jOf_le_self D.M) (uc22p22t_M_le_normalizer_jOf D)
  have hDb : Db.Normal := Subgroup.normal_centralizer
  have hDX : Db ≤ Xb := by
    refine (Subgroup.centralizer_le (P22x.mbarImage_mono _ _
      (uc22p22e_jOf_le D.sylowM))).trans ?_
    change centralizer (mbarImage D.M D.U (jOf D.T) : Set (MBar D.M D.U)) ≤
      mbarImage D.M D.U (D.M ⊓ normalizer (jOf D.T : Set G))
    rw [← normalizer_mbarImage_jOf D]
    exact centralizer_le_normalizer _
  have hXK : X ≤ normalizer (K : Set G) := by
    have hXE : X ≤ normalizer (proofE D : Set G) := fun x hx =>
      CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem
        (uc22p22e_conj_omegaZJ (fun y hy => (mem_normalizer_iff.1 hx.2 y).1 hy)
          (fun y hy => by simpa using (mem_normalizer_iff.1 (inv_mem hx.2) y).1 hy))
    exact (le_inf le_normalizer (hXE.trans
      ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).1
        (normal_subgroupOf_centralizer_normalizer _)))).trans inf_normalizer_le_normalizer_inf
  have hXKb : Xb ≤ normalizer (Kb : Set (MBar D.M D.U)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact P2251f.mem_normalizer_mbarImage x.2 (hXK hx)
  have hIb : ((Kb ⊓ Db).subgroupOf Db).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer inf_le_right).2
    exact (le_inf (hDX.trans hXKb) le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hI2 : IsPGroup 2 ↥(Kb ⊓ Db) := by
    apply CFSG.Quasithin.isPGroup_two_of_odd_orderOf_eq_one
    intro a ha haodd
    obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
      uc22br4_exists_conjModule D.M D.U hV (P22x.uc22p22xf_hel D)
    let φ := CFSG.RankThree.FFModules.repMulAut ρ
    have hφinj : Function.Injective φ :=
      CFSG.RankThree.FFModules.repMulAut_injective (uc22br4_injective _ _ hV e ρ hc)
    have hU2 : IsPGroup 2 (Multiplicative Umod) := fun u =>
      ⟨1, CFSG.RankThree.FFModules.multiplicative_sq u⟩
    set Jb := mbarImage D.M D.U (jOf D.T)
    have hJ2 : IsPGroup 2 Jb :=
      ((D.sylowM.isPGroup.to_le (uc22p22e_jOf_le_self D.T)).comap_subtype).map _
    have hφa : φ a = 1 := CFSG.Quasithin.thompson_AxB_element hU2 φ (hJ2.map φ)
      (Nat.coprime_two_right.2 haodd) (fun b hb => by
        rw [← map_mul, ← map_mul]
        exact congrArg φ ((mem_centralizer_iff.1 ha.2 b
          (P22x.mbarImage_mono _ _ (uc22p22e_jOf_le D.sylowM) hb)).symm)) (by
        intro u hu
        obtain ⟨x, hx, rfl⟩ := ha.1
        let v : D.U := e.symm u
        have hvJ : (v : G) ∈ centralizer (jOf D.T : Set G) := by
          rw [mem_centralizer_iff]
          intro j hj
          have hjM : j ∈ D.M := D.sylowM.le (uc22p22e_jOf_le_self D.T hj)
          have h := hu (QuotientGroup.mk (⟨j, hjM⟩ : D.M)) ⟨⟨j, hjM⟩, hj, rfl⟩
          have heq : ρ (QuotientGroup.mk (⟨j, hjM⟩ : D.M))
              (Multiplicative.toAdd (e v)) = Multiplicative.toAdd (e v) := by
            have h' := congrArg Multiplicative.toAdd h
            change ρ (QuotientGroup.mk (⟨j, hjM⟩ : D.M))
              (Multiplicative.toAdd u) = Multiplicative.toAdd u at h'
            simpa only [v, e.apply_symm_apply] using h'
          exact (mul_inv_eq_iff_eq_mul.1
            ((uc22br_gt_conj_iff _ _ hV e ρ hc _ v).2 heq))
        have hvE := P2251e.inf_centralizer_le_proofE D ⟨v.2, hvJ⟩
        have hxE := hx.2
        have heq := (uc22br_gt_conj_iff _ _ hV e ρ hc x v).1
          (mul_inv_eq_iff_eq_mul.2 (mem_centralizer_iff.1 hxE _ hvE).symm)
        change Multiplicative.ofAdd
          (ρ (QuotientGroup.mk x) (Multiplicative.toAdd u)) = u
        have heq' : ρ (QuotientGroup.mk x) (Multiplicative.toAdd u) =
            Multiplicative.toAdd u := by simpa only [v, e.apply_symm_apply] using heq
        rw [heq']
        rfl)
    exact hφinj (hφa.trans (map_one φ).symm)
  have hI : (Kb ⊓ Db).IsSubnormal :=
    Subgroup.IsSubnormal.trans inf_le_right hIb.isSubnormal hDb.isSubnormal
  have hle : Kb ⊓ Db ≤ CFSG.pCore 2 (MBar D.M D.U) := by
    have hc : CFSG.pCore 2 ↥(Kb ⊓ Db) = ⊤ := by
      apply top_le_iff.1
      exact le_sSup ⟨Subgroup.normal_top, hI2.to_subgroup ⊤⟩
    have h := uc22br4_map_pCore_le_pCore_of_isSubnormal 2 hI
    simpa only [hc, Subgroup.map_top, Subgroup.range_subtype] using h
  have hred : CFSG.pCore 2 (MBar D.M D.U) = ⊥ := by
    apply (uc22br4_pCore_bot_iff _ _ hV).2
    exact uc22p22na_twoReduced_iSup_conj D.sylowM
      (show D.Z ≤ centralizer (D.T : Set G) from by
        intro z hz
        exact mem_centralizer_iff.2
          ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.1 hz).2.1))
  exact le_bot_iff.1 (hle.trans hred.le)

theorem centralizer_proofN_le_mbarImage_normalizer (D : Data G) :
    centralizer (mbarImage D.M D.U (proofN D) : Set (MBar D.M D.U)) ≤
      mbarImage D.M D.U (D.M ⊓ normalizer (proofS D : Set G)) := by
  set X : Subgroup G := D.M ⊓ normalizer (jOf D.T : Set G)
  set K : Subgroup G := X ⊓ centralizer (proofE D : Set G)
  set Xb := mbarImage D.M D.U X
  set Kb := mbarImage D.M D.U K
  set Db := centralizer (mbarImage D.M D.U (proofN D) : Set (MBar D.M D.U))
  have : (mbarImage D.M D.U (proofN D)).Normal :=
    uc22br4_mbarImage_normal _ _ _ (uc22p22e_jOf_le_self D.M) (uc22p22t_M_le_normalizer_jOf D)
  have hDb : Db.Normal := Subgroup.normal_centralizer
  have hDX : Db ≤ Xb := by
    refine (Subgroup.centralizer_le (P22x.mbarImage_mono _ _
      (uc22p22e_jOf_le D.sylowM))).trans ?_
    change centralizer (mbarImage D.M D.U (jOf D.T) : Set (MBar D.M D.U)) ≤
      mbarImage D.M D.U (D.M ⊓ normalizer (jOf D.T : Set G))
    rw [← normalizer_mbarImage_jOf D]
    exact centralizer_le_normalizer _
  have hXK : X ≤ normalizer (K : Set G) := by
    have hXE : X ≤ normalizer (proofE D : Set G) := fun x hx =>
      CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem
        (uc22p22e_conj_omegaZJ (fun y hy => (mem_normalizer_iff.1 hx.2 y).1 hy)
          (fun y hy => by simpa using (mem_normalizer_iff.1 (inv_mem hx.2) y).1 hy))
    exact (le_inf le_normalizer (hXE.trans
      ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).1
        (normal_subgroupOf_centralizer_normalizer _)))).trans inf_normalizer_le_normalizer_inf
  have hXKb : Xb ≤ normalizer (Kb : Set (MBar D.M D.U)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact P2251f.mem_normalizer_mbarImage x.2 (hXK hx)
  have hc : Db ≤ centralizer (Kb : Set (MBar D.M D.U)) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro k hk
    have h1 : d * k * d⁻¹ * k⁻¹ ∈ Kb :=
      Kb.mul_mem ((mem_normalizer_iff.1 (hXKb (hDX hd)) k).1 hk) (Kb.inv_mem hk)
    have h2 : d * k * d⁻¹ * k⁻¹ ∈ Db := by
      have h := Db.mul_mem hd (hDb.conj_mem d⁻¹ (Db.inv_mem hd) k)
      simpa [mul_assoc] using h
    have hbot : d * k * d⁻¹ * k⁻¹ = 1 := by
      have h : d * k * d⁻¹ * k⁻¹ ∈ Kb ⊓ Db := ⟨h1, h2⟩
      rw [show Kb ⊓ Db = ⊥ from inf_centralizer_proofN_eq_bot D, mem_bot] at h
      exact h
    have hcomm : d * k = k * d := by
      have h := mul_inv_eq_one.1 hbot
      exact mul_inv_eq_iff_eq_mul.1 h
    exact hcomm.symm
  have hSK : proofS D ≤ K := fun s hs => ⟨⟨D.sylowM.le hs.1,
    CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem
      (uc22p22e_normalizes_jOf_T D s hs.1)⟩, hs.2⟩
  refine (hc.trans (Subgroup.centralizer_le (P22x.mbarImage_mono _ _ hSK))).trans ?_
  rw [← normalizer_mbarImage_proofS D]
  exact centralizer_le_normalizer _

theorem isSubnormal_mbarImage_of_centralizes (D : Data G) {H Y : Subgroup G}
    (hNY : H ⊓ D.M ≤ normalizer (Y : Set G))
    (hSH : normalizer (proofS D : Set G) ≤ H)
    (hc : mbarImage D.M D.U Y ≤
      centralizer (mbarImage D.M D.U (proofN D) : Set (MBar D.M D.U))) :
    CFSG.Open.IsSubnormal (mbarImage D.M D.U Y) ⊤ := by
  set Db := centralizer (mbarImage D.M D.U (proofN D) : Set (MBar D.M D.U))
  have : (mbarImage D.M D.U (proofN D)).Normal :=
    uc22br4_mbarImage_normal _ _ _ (uc22p22e_jOf_le_self D.M) (uc22p22t_M_le_normalizer_jOf D)
  have : Db.Normal := Subgroup.normal_centralizer
  have hDbY : Db ≤ normalizer (mbarImage D.M D.U Y : Set (MBar D.M D.U)) := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := centralizer_proofN_le_mbarImage_normalizer D hd
    exact P2251f.mem_normalizer_mbarImage x.2 (hNY ⟨hSH hx.2, hx.1⟩)
  have hnormal : ((mbarImage D.M D.U Y).subgroupOf Db).Normal :=
    (normal_subgroupOf_iff_le_normalizer hc).2 hDbY
  exact CFSG.Open.IsSubnormal.step hc hnormal
    (CFSG.Open.IsSubnormal.top_iff.2 (Subgroup.Normal.isSubnormal inferInstance))

end S2251

end CFSG.LocalAnalysis.UniquenessCase.UC22

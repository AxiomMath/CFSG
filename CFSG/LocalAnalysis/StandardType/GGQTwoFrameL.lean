module

public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLAut
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLRank

import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLAux
import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLCover
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
import CFSG.RankThree.PartOne.KF.UnitaryDiag
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem qTwo_frameL {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m : ℕ} (hm : 5 ≤ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) :
    ∃ F : QTwoFrameL 3 B Bs x L D J, F.m = m := by
  classical
  have hCfg : GGConfig 3 B Bs x L D J := hcfg.1.1
  have hE : IsElemAbelian 3 Bs := hCfg.2.1.2.1
  have h3 : ∀ b : ↥Bs, b ^ 3 = 1 := fun b => Subtype.ext (by
    show ((b : ↥Bs) : G) ^ 3 = 1
    exact hE.2 (b : G) b.2)
  obtain ⟨F0, hF0field, hF0finite, hF0char, hF0fact, hcardF0, he⟩ := qTwoFrameL_fieldIso hL
  letI : Field F0 := hF0field
  letI : Finite F0 := hF0finite
  letI : CharP F0 2 := hF0char
  letI : Fact (Nat.Prime 2) := hF0fact
  obtain ⟨e⟩ := he
  have hInnAll : GGInnerDiagAll 3 B Bs x L D J := hcfg.1.2.2.1
  have hMark : GGInnerDiagOn Bs L := hInnAll.1
  unfold GGInnerDiagOn at hMark
  unfold LargeEvenMarking at hMark
  unfold LargeEvenMarkingLegacy at hMark
  obtain ⟨hcomL, lab, hlab, hraw⟩ := hMark
  obtain ⟨R, hR, I, F, hQ⟩ := qTwoFrameLP_rawDatumLegacy_exists hraw
  obtain ⟨θ, hP⟩ := hQ.2.2
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := hP.1
  obtain ⟨Δ, hΔN, hΔle, hΔ2, hΔmax, ψ, hψsurj, hψker, hψcompat⟩ :=
    qTwoFrameL_cover (L := ↥L) hm hcomL hcardF0 e
  letI : Δ.Normal := hΔN
  have hΔchar : Δ.Characteristic :=
    qTwoFrameLP_characteristic_of_central_twoPower hΔle hΔ2 hΔmax
  let ρ : ↥Bs →* MulAut (↥L ⧸ Δ) :=
    (qTwoFrameLP_centerQuotAutOfCharacteristic Δ hΔchar).comp (ggGamma L hBsN)
  have hρ_mk : ∀ (b : ↥Bs) (l : ↥L),
      ρ b (QuotientGroup.mk l) = QuotientGroup.mk ⟨(b : G) * l * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBsN b.2) l).mp l.2⟩ := by
    intro b l
    show qTwoFrameLP_centerQuotAutOfCharacteristic Δ hΔchar (ggGamma L hBsN b)
      (QuotientGroup.mk l) = _
    rw [qTwoFrameLP_centerQuotAutOfCharacteristic_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (ggGamma_coe L hBsN b l))
  let ρZ : ↥Bs →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
    (centerQuotAut ↥L).comp (ggGamma L hBsN)
  have hρZ : ∀ (b : ↥Bs) (l : ↥L),
      ρZ b (QuotientGroup.mk l) = QuotientGroup.mk ⟨(b : G) * l * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBsN b.2) l).mp l.2⟩ := by
    intro b l
    show centerQuotAut ↥L (ggGamma L hBsN b) (QuotientGroup.mk l) = _
    rw [centerQuotAut_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (ggGamma_coe L hBsN b l))
  have hρ_frame : ∀ b : ↥Bs,
      MulAut.congr e (ρZ b) ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)))
        (LargeEvenGUSet (Fin m) F0 (2 ^ 1)) :=
    fun b => qTwoFrameL_autInn hm hcardF0 e hBsN h3 ρZ hρZ b
  let Ab : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)))) :=
    (ρZ.range).map (MulAut.congr e).toMonoidHom
  have hAb : IsElemAbelian 3 Ab := by
    have h := (qTwoFrameLP_isElemAbelian_top hE).map ρZ
    have h2 := h.map (MulAut.congr e).toMonoidHom
    rw [← show (ρZ.range).map (MulAut.congr e).toMonoidHom =
        Subgroup.map (MulAut.congr e).toMonoidHom (Subgroup.map ρZ ⊤) from by
      rw [MonoidHom.range_eq_map]] at h2
    exact h2
  have hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)))
      (LargeEvenGUSet (Fin m) F0 (2 ^ 1)) := by
    rintro a ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := hy
    exact hρ_frame b
  have hcardAb : 3 ^ (m / 3 + 2) ≤ Nat.card Ab := by
    have h1 : Nat.card Ab = Nat.card ρZ.range := by
      show Nat.card ((ρZ.range).map (MulAut.congr e).toMonoidHom) = Nat.card ρZ.range
      rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
    have h2 : Nat.card ρZ.range = Nat.card (ggGamma L hBsN).range := by
      rw [show ρZ = (centerQuotAut ↥L).comp (ggGamma L hBsN) from rfl, MonoidHom.range_comp]
      rw [Subgroup.card_map_of_injective (qTwoFrameLP_centerQuotAut_injective hcomL)]
    rw [h1, h2]
    exact qTwoFrameL_rank hm hcfg hcardF0 e hBsN
  have hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F0 :=
    { prime := by norm_num
      one_le := by norm_num
      card := by rw [hcardF0]; norm_num }
  have hcardEq : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hcardF0]; norm_num
  have hdq : (m, 2 ^ 1) ≠ (3, 2) := by
    rintro heq
    have hm3 : m = 3 := by simpa using congrArg Prod.fst heq
    omega
  obtain ⟨P, hP, hframe⟩ :=
    TableBUD.exists_unitary_frame hUFD hcardEq (by omega) hdq (by norm_num) (by norm_num)
      hAb hAbI hcardAb
  let eSU : Su F0 2 1 m ≃* ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) :=
    MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := 1) hcardEq m)
  have heSU : ∀ u : Su F0 2 1 m, (eSU u : GL (Fin m) F0) = (u : GL (Fin m) F0) := by
    intro u
    change ((MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU
      (p := 2) (f := 1) hcardEq m)) u : GL (Fin m) F0) = (u : GL (Fin m) F0)
    rw [MulEquiv.subgroupCongr_apply]
  let Φ : Su F0 2 1 m ≃* ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) :=
    eSU.trans (CFSG.RankThree.PartOne.KFU.conjSU hUFD ⟨P, hP⟩)
  let πSU : Su F0 2 1 m →* (↥L ⧸ Δ) :=
    ψ.comp Φ.toMonoidHom
  have hπ_surj : Function.Surjective πSU :=
    hψsurj.comp Φ.surjective
  have hπ_ker : πSU.ker ≤ Subgroup.center (Su F0 2 1 m) := by
    intro u hu
    have hu' : Φ u ∈ ψ.ker := by
      refine MonoidHom.mem_ker.mpr ?_
      have h := MonoidHom.mem_ker.mp hu
      change ψ (Φ u) = 1 at h
      exact h
    have hc : Φ u ∈ Subgroup.center ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) := hψker hu'
    have hmap : Subgroup.map Φ.toMonoidHom (Subgroup.center (Su F0 2 1 m)) =
        Subgroup.center ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) :=
      Subgroup.map_center_eq Φ
    have hmem : Φ u ∈ Subgroup.map Φ.toMonoidHom (Subgroup.center (Su F0 2 1 m)) := by
      rwa [hmap]
    obtain ⟨w, hw, hwu⟩ := hmem
    rw [Φ.injective hwu] at hw
    exact hw
  let πZ : (↥L ⧸ Δ) →* (↥L ⧸ Subgroup.center ↥L) :=
    QuotientGroup.map Δ (Subgroup.center ↥L) (MonoidHom.id ↥L) (by simpa using hΔle)
  have hπZ_mk (l : ↥L) :
      πZ ((QuotientGroup.mk' Δ) l) = (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) :=
    QuotientGroup.map_mk Δ (Subgroup.center ↥L) (MonoidHom.id ↥L) (by simpa using hΔle) l
  have hπZ_rho : ∀ (b : ↥Bs) (y : ↥L ⧸ Δ), πZ (ρ b y) = ρZ b (πZ y) := by
    intro b y
    induction y using QuotientGroup.induction_on
    rfl
  have hπZ_ker : πZ.ker ≤ Subgroup.center (↥L ⧸ Δ) := by
    intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective Δ x
    rw [MonoidHom.mem_ker, hπZ_mk l] at hx
    rw [QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l', rfl⟩ := QuotientGroup.mk'_surjective Δ y
    show (QuotientGroup.mk (l' * l) : ↥L ⧸ Δ) = QuotientGroup.mk (l * l')
    rw [(Subgroup.mem_center_iff.mp hx) l']
  have hψproj : ∀ v : ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)),
      e (πZ (ψ v)) = LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) v := by
    intro v
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective Δ (ψ v)
    have h1 : e (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) v :=
      hψcompat v l hl.symm
    rw [← hπZ_mk l, hl] at h1
    exact h1
  have hψproj_inv : ∀ v : ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)),
      πZ (ψ v) = e.symm (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) v) := by
    intro v
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact hψproj v
  haveI : Group.IsPerfect ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcardEq (by omega) hdq
  have hcommH : commutator ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  have hdiag : ∀ b : ↥Bs, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
      ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
        (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧
          ρ b (πSU u) = πSU u' := by
    intro b
    obtain ⟨M, hM, hdiagM, hρb⟩ := hframe (MulAut.congr e (ρZ b)) ⟨ρZ b, ⟨b, rfl⟩, rfl⟩
    have hMN : M ∈ Subgroup.normalizer
        ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1) : Subgroup (GL (Fin m) F0)) : Set _) :=
      TableBUE.gu_subset_normalizer hUFD hM
    let D : Subgroup.normalizer
        ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1) : Subgroup (GL (Fin m) F0)) : Set _) :=
      ⟨M, hMN⟩
    have hPN : (P : GL (Fin m) F0) ∈ Subgroup.normalizer
        ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1) : Subgroup (GL (Fin m) F0)) : Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact CFSG.RankThree.PartOne.KFU.conj_mem_unitarySU hUFD hP hy
      · intro hy
        have h := CFSG.RankThree.PartOne.KFU.conj_mem_unitarySU hUFD (inv_mem hP) hy
        simp only [inv_inv] at h
        rwa [show (P : GL (Fin m) F0)⁻¹ * ((P : GL (Fin m) F0) * y *
              (P : GL (Fin m) F0)⁻¹) * (P : GL (Fin m) F0) = y from by group] at h
    have hgN : (P : GL (Fin m) F0)⁻¹ * M * P ∈ Subgroup.normalizer
        ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1) : Subgroup (GL (Fin m) F0)) : Set _) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hMN) hPN
    have hΦcoe : ∀ u : Su F0 2 1 m, (Φ u : GL (Fin m) F0) =
        (P : GL (Fin m) F0) * (u : GL (Fin m) F0) * (P : GL (Fin m) F0)⁻¹ := by
      intro u
      have h1 := CFSG.RankThree.PartOne.KFU.coe_conjSU hUFD ⟨P, hP⟩ (eSU u)
      calc (Φ u : GL (Fin m) F0)
          = (P : GL (Fin m) F0) *
              ((eSU u : ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1))) : GL (Fin m) F0) *
              (P : GL (Fin m) F0)⁻¹ := h1
        _ = (P : GL (Fin m) F0) * (u : GL (Fin m) F0) * (P : GL (Fin m) F0)⁻¹ := by
          rw [heSU u]
    let A : ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) →* (↥L ⧸ Δ) :=
      (ρ b).toMonoidHom.comp ψ
    let B : ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) →* (↥L ⧸ Δ) :=
      ψ.comp ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1)).normalizerMonoidHom D)
    have hcentral : ∀ v : ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)),
        A v * (B v)⁻¹ ∈ Subgroup.center (↥L ⧸ Δ) := by
      intro v
      change (ρ b (ψ v)) * (ψ ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1)).normalizerMonoidHom D v))⁻¹ ∈ Subgroup.center (↥L ⧸ Δ)
      apply hπZ_ker
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have hA : πZ (ρ b (ψ v)) =
          e.symm (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1))
            ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1)).normalizerMonoidHom D v)) := by
        rw [hπZ_rho b (ψ v), hψproj_inv v]
        rw [show ρZ b (e.symm (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) v)) =
              e.symm ((MulAut.congr e (ρZ b))
                (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) v)) from by
          simp [MulAut.congr_apply]]
        rw [hρb]
        first
          | rfl
          | exact congrArg e.symm (CFSG.StandardType.TableBUD.projConj_mk_coe D v)
      have hB : πZ (ψ ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1)).normalizerMonoidHom D v)) =
          e.symm (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1))
            ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1)).normalizerMonoidHom D v)) :=
        hψproj_inv ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1)).normalizerMonoidHom D v)
      rw [hA, hB, mul_inv_cancel]
    have hAB : A = B :=
      qTwoFrameLP_eq_of_mul_inv_mem_center hcommH A B hcentral
    have hphi : ∀ v : ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)),
        ρ b (ψ v) = ψ ((LargeEvenSUGroup (Fin m) F0 (2 ^ 1)).normalizerMonoidHom D v) := by
      intro v
      have hABv : A v = B v := congrArg (fun f : ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) →*
        (↥L ⧸ Δ) => f v) hAB
      change A v = B v
      exact hABv
    refine ⟨(P : GL (Fin m) F0)⁻¹ * M * P,
      qTwoFrameLP_ggIsDiagMat_of_isDiag hdiagM, fun u => ?_⟩
    have humem : (u : GL (Fin m) F0) ∈ LargeEvenSUGroup (Fin m) F0 (2 ^ 1) := by
      have hmem : (eSU u : GL (Fin m) F0) ∈ LargeEvenSUGroup (Fin m) F0 (2 ^ 1) := (eSU u).2
      rwa [heSU u] at hmem
    have hmem : (P : GL (Fin m) F0)⁻¹ * M * P * (u : GL (Fin m) F0) *
        ((P : GL (Fin m) F0)⁻¹ * M * P)⁻¹ ∈ LargeEvenSUGroup (Fin m) F0 (2 ^ 1) :=
      (Subgroup.mem_normalizer_iff.mp hgN (u : GL (Fin m) F0)).mp humem
    let u' : Su F0 2 1 m := eSU.symm
      ⟨(P : GL (Fin m) F0)⁻¹ * M * P * (u : GL (Fin m) F0) *
        ((P : GL (Fin m) F0)⁻¹ * M * P)⁻¹, hmem⟩
    have hu'coe : (u' : GL (Fin m) F0) =
        ((P : GL (Fin m) F0)⁻¹ * M * P) * (u : GL (Fin m) F0) *
          ((P : GL (Fin m) F0)⁻¹ * M * P)⁻¹ := by
      show ((eSU.symm ⟨(P : GL (Fin m) F0)⁻¹ * M * P * (u : GL (Fin m) F0) *
          ((P : GL (Fin m) F0)⁻¹ * M * P)⁻¹, hmem⟩ : Su F0 2 1 m) : GL (Fin m) F0) = _
      rw [show eSU.symm ⟨(P : GL (Fin m) F0)⁻¹ * M * P * (u : GL (Fin m) F0) *
            ((P : GL (Fin m) F0)⁻¹ * M * P)⁻¹, hmem⟩ =
          (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU
            (p := 2) (f := 1) hcardEq m)).symm
            ⟨(P : GL (Fin m) F0)⁻¹ * M * P * (u : GL (Fin m) F0) *
              ((P : GL (Fin m) F0)⁻¹ * M * P)⁻¹, hmem⟩ from rfl,
        MulEquiv.subgroupCongr_symm_apply]
    have hΦu' : Φ u' = (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)).normalizerMonoidHom D (Φ u) := by
      apply Subtype.ext
      rw [hΦcoe u']
      show (P : GL (Fin m) F0) * (u' : GL (Fin m) F0) * (P : GL (Fin m) F0)⁻¹ =
        M * (Φ u : GL (Fin m) F0) * M⁻¹
      rw [hu'coe, hΦcoe u]
      group
    refine ⟨u', hu'coe, ?_⟩
    rw [show πSU u = ψ (Φ u) from rfl, show πSU u' = ψ (Φ u') from rfl, hΦu']
    exact hphi (Φ u)
  let c : ↥L →* (↥L ⧸ Δ) := QuotientGroup.mk' Δ
  have hc_surj : Function.Surjective c := QuotientGroup.mk'_surjective Δ
  have hc_ker : c.ker ≤ Subgroup.center ↥L := by
    rw [show c.ker = Δ from QuotientGroup.ker_mk' Δ]
    exact hΔle
  have hc_two : IsPGroup 2 c.ker := by
    rw [show c.ker = Δ from QuotientGroup.ker_mk' Δ]
    exact hΔ2
  have hρ_induced : ∀ (b : ↥Bs) (l : ↥L),
      c ⟨(b : G) * l * (b : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hBsN b.2) l).mp l.2⟩ = ρ b (c l) := by
    intro b l
    exact (hρ_mk b l).symm
  exact ⟨
    { F0 := F0
      hcardF0 := hcardF0
      m := m
      hm := hm
      L0 := ↥L ⧸ Δ
      c := c
      hc_surj := hc_surj
      hc_ker := hc_ker
      hc_two := hc_two
      πSU := πSU
      hπ_surj := hπ_surj
      hπ_ker := hπ_ker
      ρ := ρ
      hdiag := hdiag
      hBsN := hBsN
      hρ_induced := hρ_induced }, rfl⟩

end CFSG.StandardType.QTwo

end

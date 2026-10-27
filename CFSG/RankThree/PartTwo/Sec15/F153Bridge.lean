module

public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannReduced
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProof
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFFamilies
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerTransport
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.RankThree.PartTwo.Sec15.SimsBaumann (W315 isTwoReducedIn_W315)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

private theorem f153_map_conj_eq_self {G H : Type*} [Group G] [Group H] (f : G →* H)
    (l y : G) (h : f l * f y = f y * f l) : f (l * y * l⁻¹) = f y := by
  rw [map_mul, map_mul, map_inv, h, mul_inv_cancel_right]

private theorem f153_oResidual_normal (Y : Type*) [Group Y] : (oResidual 2 Y).Normal := by
  refine ⟨fun x hx g => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ?_
    have h : orderOf (g * y * g⁻¹) = orderOf y := by
      simpa using (MulAut.conj g).orderOf_eq y
    change Nat.Coprime (orderOf (g * y * g⁻¹)) 2
    rw [h]
    exact hy
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ ihx ihy => simpa [mul_assoc] using Subgroup.mul_mem _ ihx ihy
  | inv x _ ih => simpa [mul_assoc] using Subgroup.inv_mem _ ih


theorem comm_W315_ne_bot
    (hF : generalizedFitting X = CFSG.pCore 2 X) {S : Subgroup X} (hS2 : IsPGroup 2 S)
    (hS1 : S ≠ ⊥) (hQS : CFSG.pCore 2 X ≤ S) (hXS : oResidual 2 X ⊔ S = ⊤)
    (hno : ¬ ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal) :
    ⁅W315 X, oResidual 2 X⁆ ≠ ⊥ := by
  intro h
  have hZC : CFSG.Quasithin.omegaOneCenterOf S ≤ Subgroup.centralizer (S : Set X) := by
    unfold CFSG.Quasithin.omegaOneCenterOf CFSG.Quasithin.omegaOneOf
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1.2
  have hZW : CFSG.Quasithin.omegaOneCenterOf S ≤ W315 X := by
    unfold W315 CFSG.Quasithin.omegaOneCenterOf CFSG.Quasithin.omegaOneOf
    rw [Subgroup.closure_le]
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
      refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
      rw [hF] at hg
      exact Subgroup.mem_centralizer_iff.mp hx.1.2 g (hQS hg)
    have hxF : x ∈ CFSG.generalizedFitting X := CFSG.centralizer_generalizedFitting_le X hxC
    rw [hF] at hxF
    have hxZ : x ∈ CFSG.Quasithin.centerOf (CFSG.pCore 2 X) := by
      refine Subgroup.mem_inf.mpr ⟨hxF, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      exact Subgroup.mem_centralizer_iff.mp hx.1.2 g (hQS hg)
    exact Subgroup.subset_closure ⟨hxZ, hx.2⟩
  have hZ1 : CFSG.Quasithin.omegaOneCenterOf S ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hS2 hS1
  have hZS : CFSG.Quasithin.omegaOneCenterOf S ≤ S :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le S
  have hZchar := CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf S
  have hLW : oResidual 2 X ≤ Subgroup.centralizer (W315 X : Set X) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  have hLN : oResidual 2 X ≤ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf S : Set X) :=
    le_trans hLW (le_trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZW))
      (Subgroup.centralizer_le_normalizer _))
  have hSN : S ≤ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf S : Set X) :=
    le_trans (Subgroup.le_centralizer_iff.mp hZC) (Subgroup.centralizer_le_normalizer _)
  have htop := sup_le hLN hSN
  rw [hXS] at htop
  have hnorm : Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf S : Set X) = ⊤ :=
    top_le_iff.mp htop
  have hZnormal : (CFSG.Quasithin.omegaOneCenterOf S).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hnorm
  exact hno ⟨CFSG.Quasithin.omegaOneCenterOf S, hZ1, hZS, hZchar, hZnormal⟩

theorem not_thompsonJ_le_centralizer_W315
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    {S : Subgroup X} (hS2 : IsPGroup 2 S) (hQS : CFSG.pCore 2 X ≤ S)
    (hXS : oResidual 2 X ⊔ S = ⊤)
    (hJ : ¬ CFSG.Quasithin.thompsonJ S ≤ CFSG.pCore 2 X)
    (hWL : ⁅W315 X, oResidual 2 X⁆ ≠ ⊥) :
    ¬ CFSG.Quasithin.thompsonJ S ≤ Subgroup.centralizer (W315 X : Set X) := by
  intro hJC
  have hWn : (W315 X).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (isTwoReducedIn_W315 hq hWL).2.1)
  haveI hCn : (Subgroup.centralizer (W315 X : Set X)).Normal := Subgroup.normal_centralizer
  have hLn : (oResidual 2 X).Normal := f153_oResidual_normal X
  have hKn : (oResidual 2 (X ⧸ CFSG.pCore 2 X)).Normal := f153_oResidual_normal _
  have hK : CFSG.IsComponent (oResidual 2 (X ⧸ CFSG.pCore 2 X)) := ⟨hq, hKn.isSubnormal⟩
  have hWQ : W315 X ≤ Subgroup.centralizer (CFSG.pCore 2 X : Set X) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1.2
  have hQC : CFSG.pCore 2 X ≤ Subgroup.centralizer (W315 X : Set X) := by
    intro q hq'
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWQ hw) q hq').symm
  have hJS : CFSG.Quasithin.thompsonJ S ≤ S := by
    unfold CFSG.Quasithin.thompsonJ
    exact iSup₂_le fun A hA => hA.1
  set π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X) with hπdef
  have hgen : ∀ x : X, Nat.Coprime (orderOf x) 2 → π x ∈ oResidual 2 (X ⧸ CFSG.pCore 2 X) :=
    fun x hx => Subgroup.subset_closure (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd π x) hx)
  have hπL : oResidual 2 X ≤ (oResidual 2 (X ⧸ CFSG.pCore 2 X)).comap π :=
    (Subgroup.closure_le _).mpr fun x hx => hgen x hx
  have hπL' : ∀ l ∈ oResidual 2 X, π l ∈ oResidual 2 (X ⧸ CFSG.pCore 2 X) :=
    fun l hl => hπL hl
  have hDn : (Subgroup.normalClosure (CFSG.Quasithin.thompsonJ S : Set X)).Normal :=
    Subgroup.normalClosure_normal
  have hJD : CFSG.Quasithin.thompsonJ S ≤ Subgroup.normalClosure (CFSG.Quasithin.thompsonJ S : Set X) :=
    Subgroup.le_normalClosure
  have hDC : Subgroup.normalClosure (CFSG.Quasithin.thompsonJ S : Set X) ≤
      Subgroup.centralizer (W315 X : Set X) := by
    apply Subgroup.normalClosure_le_normal
    intro j hj
    exact hJC hj
  set N : Subgroup (X ⧸ CFSG.pCore 2 X) :=
    (Subgroup.normalClosure (CFSG.Quasithin.thompsonJ S : Set X)).map π with hNdef
  have hNn : N.Normal := hDn.map π (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.component_normal_subgroup hK hNn with hKN | hcomm
  ·
    exfalso
    apply hWL
    rw [Subgroup.commutator_comm]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun l hl => ?_
    have hπl : π l ∈ N := hKN (hπL' l hl)
    obtain ⟨d, hd, hdl⟩ := Subgroup.mem_map.mp hπl
    have hdq : d⁻¹ * l ∈ CFSG.pCore 2 X := QuotientGroup.eq.mp hdl
    have key : d * (d⁻¹ * l) ∈ Subgroup.centralizer (W315 X : Set X) :=
      Subgroup.mul_mem _ (hDC hd) (hQC hdq)
    rwa [mul_inv_cancel_left] at key
  ·
    have hconj : ∀ x : X, ∀ j ∈ CFSG.Quasithin.thompsonJ S, x * j * x⁻¹ ∈ S := by
      intro x j hj
      have hjS : j ∈ S := hJS hj
      have hx : x ∈ oResidual 2 X ⊔ S := by rw [hXS]; exact Subgroup.mem_top x
      obtain ⟨l, hl, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      have hsjs : s * j * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs hjS) (S.inv_mem hs)
      have hsjsD : s * j * s⁻¹ ∈ Subgroup.normalClosure (CFSG.Quasithin.thompsonJ S : Set X) :=
        hDn.conj_mem j (hJD hj) s
      have hcommute : π l * π (s * j * s⁻¹) = π (s * j * s⁻¹) * π l := by
        have hmem : ⁅π l, π (s * j * s⁻¹)⁆ ∈ ⁅oResidual 2 (X ⧸ CFSG.pCore 2 X), N⁆ :=
          Subgroup.commutator_mem_commutator (hπL' l hl) (Subgroup.mem_map_of_mem π hsjsD)
        rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hmem
      have hpi : π (l * s * j * (l * s)⁻¹) = π (s * j * s⁻¹) := by
        rw [show l * s * j * (l * s)⁻¹ = l * (s * j * s⁻¹) * l⁻¹ by group]
        exact f153_map_conj_eq_self π l (s * j * s⁻¹) hcommute
      have hq2 : (s * j * s⁻¹)⁻¹ * (l * s * j * (l * s)⁻¹) ∈ CFSG.pCore 2 X :=
        QuotientGroup.eq.mp hpi.symm
      have h3 := S.mul_mem hsjs (hQS hq2)
      rwa [mul_inv_cancel_left] at h3
    have hJcore : CFSG.Quasithin.thompsonJ S ≤ S.normalCore :=
      fun j hj => show ∀ b : X, b * j * b⁻¹ ∈ S from fun b => hconj b j hj
    have hcoreP : IsPGroup 2 S.normalCore := IsPGroup.to_le hS2 (Subgroup.normalCore_le S)
    have hcoreQ : S.normalCore ≤ CFSG.pCore 2 X := by
      unfold CFSG.pCore
      exact le_sSup ⟨Subgroup.normalCore_normal S, hcoreP⟩
    exact hJ (hJcore.trans hcoreQ)

theorem pCore_le_centralizer_W315 :
    CFSG.pCore 2 X ≤ Subgroup.centralizer (W315 X : Set X) :=
  CFSG.AGLEmbedding.AscTenThree.le_centralizer_omegaOneCenterOf_self _

theorem oResidual_quotient_eq_map {S : Subgroup X} (hS2 : IsPGroup 2 S)
    (hXS : oResidual 2 X ⊔ S = ⊤) :
    oResidual 2 (X ⧸ CFSG.pCore 2 X) =
      (oResidual 2 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
  have hLn : (oResidual 2 X).Normal := Stage1.Thm6.Prod.oResidual_normal 2 X
  refine Push153.oResidual_eq_of_pow (Push153.map_oResidual_le _) fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) y
  have hSL : S ≤ Subgroup.normalizer (oResidual 2 X : Set X) := fun s _ =>
    (Subgroup.normalizer_eq_top_iff.mpr hLn) ▸ Subgroup.mem_top s
  obtain ⟨e, he⟩ := CFSG.HardMathSupport.Cooperstein.Coordinator.exists_pow_mem_sup hS2 hSL
    (show x ∈ oResidual 2 X ⊔ S by rw [hXS]; exact Subgroup.mem_top x)
  exact ⟨e, ⟨x ^ 2 ^ e, he, by simp⟩⟩


section Factor

variable {S : Subgroup X}

theorem oResidual_le_normalizer_W315
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hWL : ⁅W315 X, oResidual 2 X⁆ ≠ ⊥) :
    oResidual 2 X ≤ Subgroup.normalizer (W315 X : Set X) := fun _ _ =>
  (isTwoReducedIn_W315 hq hWL).2.1 (Subgroup.mem_top _)

theorem exists_central_factor_W315 (hS2 : IsPGroup 2 S)
    (hXS : oResidual 2 X ⊔ S = ⊤)
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hWL : ⁅W315 X, oResidual 2 X⁆ ≠ ⊥) :
    ∃ h : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) →* ↥(autOn (oResidual 2 X) (W315 X)),
      Function.Surjective h ∧
        h.ker ≤ Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) := by
  classical
  set Q := CFSG.pCore 2 X with hQ
  set L := oResidual 2 X with hL
  set K := oResidual 2 (X ⧸ Q) with hK
  have hLV : L ≤ Subgroup.normalizer (W315 X : Set X) := oResidual_le_normalizer_W315 hq hWL
  have hKeq : K = L.map (QuotientGroup.mk' Q) := oResidual_quotient_eq_map hS2 hXS
  let π : ↥L →* ↥K :=
    ((QuotientGroup.mk' Q).comp L.subtype).codRestrict K (fun l => by
      rw [hKeq]; exact ⟨l, l.2, rfl⟩)
  have hπ : Function.Surjective π := by
    rintro ⟨y, hy⟩
    rw [hKeq] at hy
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨⟨l, hl⟩, rfl⟩
  let φ : ↥L →* ↥(autOn L (W315 X)) :=
    (CFSG.QuasithinUnique.Setup.rho (W315 X) L hLV).codRestrict _ fun l =>
      (CFSG.QuasithinUnique.Setup.range_rho hLV).le ⟨l, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rw [← CFSG.QuasithinUnique.Setup.range_rho hLV] at hx
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l, rfl⟩
  have hφ1 : ∀ l : ↥L, φ l = 1 ↔ (l : X) ∈ Subgroup.centralizer (W315 X : Set X) := by
    intro l
    rw [← CFSG.QuasithinUnique.Setup.rho_eq_one_iff hLV l]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hk : π.ker ≤ φ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    rw [hφ1]
    have h1 : QuotientGroup.mk' Q (l : X) = 1 := congrArg Subtype.val hl
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact pCore_le_centralizer_W315 h1
  have hq' := CFSG.HardMathSupport.Cooperstein.Coordinator.isQuasisimple_to_open' hq
  have hLn : L.Normal := Stage1.Thm6.Prod.oResidual_normal 2 X
  have hcen : ∀ a ∈ φ.ker, π a ∈ Subgroup.center ↥K := by
    have hN : (φ.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπ
    rcases CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.normal_le_center_or_eq_top
      hq'.1 hq'.2 _ hN with hc | htop
    · intro a ha
      exact hc ⟨a, ha, rfl⟩
    · exfalso
      apply hWL
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp ?_)
      intro l hl
      have hmem : π ⟨l, hl⟩ ∈ φ.ker.map π := by rw [htop]; trivial
      obtain ⟨a, ha, hal⟩ := hmem
      have hker : a⁻¹ * ⟨l, hl⟩ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hal, inv_mul_cancel]
      have h2 := hk hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.mp ha, inv_one, one_mul] at h2
      exact (hφ1 ⟨l, hl⟩).mp h2
  obtain ⟨h, hs, hker, -⟩ := CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.exists_central_factor
    π hπ φ hφ hk hcen
  exact ⟨h, hs, hker⟩

end Factor


section FFHypPart

variable {S : Subgroup X}


theorem isQuasisimple_autOn_W315 (hS2 : IsPGroup 2 S) (hXS : oResidual 2 X ⊔ S = ⊤)
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hWL : ⁅W315 X, oResidual 2 X⁆ ≠ ⊥) :
    CFSG.IsQuasisimple ↥(autOn (oResidual 2 X) (W315 X)) := by
  obtain ⟨h, hs, hk⟩ := exists_central_factor_W315 hS2 hXS hq hWL
  have hq' := isQuasisimple_to_open' hq
  have hperf : ⁅(⊤ : Subgroup ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))),
      (⊤ : Subgroup ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))⁆ = ⊤ := by
    rw [← _root_.commutator_def]; exact hq'.1
  obtain ⟨e⟩ := StarAux.nonempty_quotientCenterEquiv_of_central_ker h hs hk hperf
  haveI := hq'.2
  exact isQuasisimple_of_open' ⟨StarAux.commutator_eq_top_of_surjective h hs hq'.1,
    e.symm.isSimpleGroup⟩

theorem nonempty_autOn_centerQuotientEquiv_W315 (hS2 : IsPGroup 2 S)
    (hXS : oResidual 2 X ⊔ S = ⊤)
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hWL : ⁅W315 X, oResidual 2 X⁆ ≠ ⊥) :
    Nonempty (↥(autOn (oResidual 2 X) (W315 X)) ⧸ Subgroup.center ↥(autOn (oResidual 2 X) (W315 X)) ≃*
      ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ⧸ Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) := by
  obtain ⟨h, hs, hk⟩ := exists_central_factor_W315 hS2 hXS hq hWL
  have hq' := isQuasisimple_to_open' hq
  have hperf : ⁅(⊤ : Subgroup ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))),
      (⊤ : Subgroup ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))⁆ = ⊤ := by
    rw [← _root_.commutator_def]; exact hq'.1
  obtain ⟨e⟩ := StarAux.nonempty_quotientCenterEquiv_of_central_ker h hs hk hperf
  exact ⟨e.symm⟩

theorem quasithinGenFitting_autOn_top (hS2 : IsPGroup 2 S) (hXS : oResidual 2 X ⊔ S = ⊤)
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hWL : ⁅W315 X, oResidual 2 X⁆ ≠ ⊥) :
    CFSG.Open.quasithinGenFitting (autOn (⊤ : Subgroup X) (W315 X)) =
      autOn (oResidual 2 X) (W315 X) := by
  have hLV := oResidual_le_normalizer_W315 hq hWL
  have hLn : (oResidual 2 X).Normal := Stage1.Thm6.Prod.oResidual_normal 2 X
  have hSL : S ≤ Subgroup.normalizer (oResidual 2 X : Set X) := fun s _ =>
    (Subgroup.normalizer_eq_top_iff.mpr hLn) ▸ Subgroup.mem_top s
  refine CFSG.Quasithin.InternalSec.quasithinGenFitting_eq_of_two_pow
    (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le le_top)
    (CFSG.Quasithin.InternalSec.autOn_normal_of (fun y _ => ?_))
    (isQuasisimple_to_open' (isQuasisimple_autOn_W315 hS2 hXS hq hWL))
    (CFSG.Quasithin.InternalSec.autOn_two_of hLV fun y hy => ?_)
    (CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot (isTwoReducedIn_W315 hq hWL))
  · exact (Subgroup.normalizer_eq_top_iff.mpr hLn) ▸ Subgroup.mem_top y
  · obtain ⟨e, he⟩ := exists_pow_mem_sup hS2 hSL
      (show y ∈ oResidual 2 X ⊔ S by rw [hXS]; exact Subgroup.mem_top y)
    exact ⟨e, Subgroup.mem_sup_left he⟩

end FFHypPart


section Final

variable {S : Subgroup X}

theorem W315_le_pCore : W315 X ≤ CFSG.pCore 2 X :=
  CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _

theorem ffHyp_W315 (hK : CFSG.Open.IsKGroup X) (hS2 : IsPGroup 2 S)
    (hXS : oResidual 2 X ⊔ S = ⊤)
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hWL : ⁅W315 X, oResidual 2 X⁆ ≠ ⊥) :
    FFHyp (V := IntMod (W315 X) (isTwoReducedIn_W315 hq hWL).2.2.1)
      (autI (isTwoReducedIn_W315 hq hWL).2.2.1 (⊤ : Subgroup X))
      (autI (isTwoReducedIn_W315 hq hWL).2.2.1 (oResidual 2 X)) := by
  have hVred := isTwoReducedIn_W315 hq hWL
  refine ⟨(quasithinGenFitting_autOn_top hS2 hXS hq hWL).symm,
    isQuasisimple_autOn_W315 hS2 hXS hq hWL, ?_, ?_⟩
  · have h5 := CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hVred
    rw [CFSG.Open.pCoreOf] at h5
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (autOn (⊤ : Subgroup X) (W315 X)).subtype_injective).mp h5
  · obtain ⟨e⟩ := nonempty_autOn_centerQuotientEquiv_W315 hS2 hXS hq hWL
    have hq' := isQuasisimple_to_open' hq
    have hnonab : ∃ a b : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ⧸
        Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)), a * b ≠ b * a := hq.2.2
    have hcat : CFSG.Open.IsCatalogGroup (↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ⧸
        Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) :=
      ((catalogSimpleSections_of_isKGroup hK).quotient (CFSG.pCore 2 X))
        (oResidual 2 (X ⧸ CFSG.pCore 2 X))
        (Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) inferInstance hq'.2 hnonab
    exact CFSG.AGLEmbedding.IsCatalogGroup.of_mulEquiv e hcat

end Final

section Core

variable {S : Subgroup X}

theorem false_of_noFFModule_of_pushing_up
    (hK : CFSG.Open.IsKGroup X)
    (hF : generalizedFitting X = CFSG.pCore 2 X)
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hQS : CFSG.pCore 2 X ≤ S)
    (hXS : oResidual 2 X ⊔ S = ⊤)
    (hJ : ¬ CFSG.Quasithin.thompsonJ S ≤ CFSG.pCore 2 X)
    (hno : ¬ ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal)
    {T : Type} [Group T] (hT : NoFFModule T)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ⧸
      Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃* T) : False := by
  have hWL := comm_W315_ne_bot hF hS2 hS1 hQS hXS hno
  have hred := isTwoReducedIn_W315 hq hWL
  have hV := hred.2.2.1
  have hJC := not_thompsonJ_le_centralizer_W315 hq hS2 hQS hXS hJ hWL
  have hVS : W315 X ≤ S := W315_le_pCore.trans hQS
  have hSN : S ≤ Subgroup.normalizer (W315 X : Set X) := fun s _ => hred.2.1 (Subgroup.mem_top s)
  obtain ⟨A, hAS, hA1, hAe, hAoff⟩ := (B2_7_of_not_le hV hVS hSN hJC).1
  have hFFmod : IsFFModule (autI hV (⊤ : Subgroup X)) :=
    ⟨A, hAS.trans (autI_mono hV le_top), hA1, hAe, hAoff⟩
  obtain ⟨e'⟩ := nonempty_autOn_centerQuotientEquiv_W315 hS2 hXS hq hWL
  exact hT (IntMod (W315 X) hV) (fun v => IntMod.sq_eq_one v) (autI hV ⊤)
    (autI hV (oResidual 2 X)) (ffHyp_W315 hK hS2 hXS hq hWL) ⟨e'.trans e⟩ hFFmod

end Core

theorem le_normalizer_map_subtype_of_normal {G : Type} [Group G] {H : Subgroup G}
    {C : Subgroup ↥H} (hC : C.Normal) :
    H ≤ Subgroup.normalizer ((C.map H.subtype : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have hn' : n ∈ C.map H.subtype := hn
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hn'
    refine Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : H) * c * (⟨g, hg⟩ : H)⁻¹, hC.conj_mem c hc _, ?_⟩
    simp
  · intro hn
    have hn' : g * n * g⁻¹ ∈ C.map H.subtype := hn
    obtain ⟨c, hc, hcn⟩ := Subgroup.mem_map.mp hn'
    have hconj : (⟨g, hg⟩ : H)⁻¹ * c * (⟨g, hg⟩ : H) ∈ C := by
      have h := hC.conj_mem c hc (⟨g, hg⟩ : H)⁻¹
      rwa [inv_inv] at h
    refine Subgroup.mem_map.mpr ⟨_, hconj, ?_⟩
    have key : H.subtype ((⟨g, hg⟩ : H)⁻¹ * c * (⟨g, hg⟩ : H)) = g⁻¹ * H.subtype c * g := by
      simp
    rw [key, hcn]
    group

theorem leaf_false_of_noFFModule {G : Type} [Group G] [Finite G] {Y S : Subgroup G}
    (hKH : CFSG.Open.IsKGroup ↥(Y ⊔ S))
    (hY : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y)
    (hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y)
    (hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hS2 : IsPGroup 2 S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hFF : FF153 Y S) (hno : ¬ CharNormal153 Y S)
    {T : Type} [Group T] (hT : NoFFModule T)
    (e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* T) : False := by
  obtain ⟨φ⟩ := Push153.nonempty_oResidual_quotient_equiv hS2 hSY hY3
  have hF : generalizedFitting ↥(Y ⊔ S) = CFSG.pCore 2 ↥(Y ⊔ S) :=
    Push153.generalizedFitting_sup_eq hY hS2 hSY
  have hq : CFSG.IsQuasisimple ↥(oResidual 2 (↥(Y ⊔ S) ⧸ CFSG.pCore 2 ↥(Y ⊔ S))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hYq
  have hSmap : (S.subgroupOf (Y ⊔ S)).map (Y ⊔ S).subtype = S := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_right]
  have hS2' : IsPGroup 2 ↥(S.subgroupOf (Y ⊔ S)) :=
    hS2.of_injective (Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ Y ⊔ S)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ Y ⊔ S)).injective
  have hS1' : S.subgroupOf (Y ⊔ S) ≠ ⊥ := by
    intro h
    apply hFF.2
    have hSb : S = ⊥ := by
      have h2 := hSmap
      rw [h, Subgroup.map_bot] at h2
      exact h2.symm
    exact (Push153.thompsonJ_le_self S).trans (hSb.le.trans bot_le)
  have hQS' : CFSG.pCore 2 ↥(Y ⊔ S) ≤ S.subgroupOf (Y ⊔ S) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hFF.1 ((Push153.mem_pCore_iff_mem_pCoreOf x).mp hx)
  have hXS : oResidual 2 ↥(Y ⊔ S) ⊔ S.subgroupOf (Y ⊔ S) = ⊤ := by
    rw [Push153.oResidual_sup_eq hS2 hSY hY3]
    have h := Subgroup.subgroupOf_sup (le_sup_left : Y ≤ Y ⊔ S) (le_sup_right : S ≤ Y ⊔ S)
    rw [Subgroup.subgroupOf_self] at h
    exact h.symm
  have hJ' : ¬ CFSG.Quasithin.thompsonJ (S.subgroupOf (Y ⊔ S)) ≤ CFSG.pCore 2 ↥(Y ⊔ S) := by
    intro h
    apply hFF.2
    have key : CFSG.Quasithin.thompsonJ ((S.subgroupOf (Y ⊔ S)).map (Y ⊔ S).subtype) =
        (CFSG.Quasithin.thompsonJ (S.subgroupOf (Y ⊔ S))).map (Y ⊔ S).subtype :=
      CFSG.Quasithin.thompsonJ_map_of_injective' (Y ⊔ S).subtype_injective _
    rw [hSmap] at key
    rw [key]
    exact Subgroup.map_mono h
  have hno' : ¬ ∃ C : Subgroup ↥(Y ⊔ S), C ≠ ⊥ ∧ C ≤ S.subgroupOf (Y ⊔ S) ∧
      (C.subgroupOf (S.subgroupOf (Y ⊔ S))).Characteristic ∧ C.Normal := by
    rintro ⟨C', hC'b, hC'S, hC'char, hC'n⟩
    apply hno
    unfold CharNormal153
    refine ⟨C'.map (Y ⊔ S).subtype, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hC'b ((Subgroup.map_eq_bot_iff_of_injective C' (Y ⊔ S).subtype_injective).mp h)
    · exact Subgroup.map_le_iff_le_comap.mpr hC'S
    · let ι : ↥(S.subgroupOf (Y ⊔ S)) ≃* ↥S := Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ Y ⊔ S)
      have hc := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.characteristic_map_equiv' ι hC'char
      have heq : (C'.subgroupOf (S.subgroupOf (Y ⊔ S))).map ι.toMonoidHom =
          (C'.map (Y ⊔ S).subtype).subgroupOf S := by
        ext x
        constructor
        · intro hx
          obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
          rw [← hyx]
          exact Subgroup.mem_subgroupOf.mpr
            (Subgroup.mem_map.mpr ⟨y.1, Subgroup.mem_subgroupOf.mp hy, rfl⟩)
        · intro hx
          obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
          have hcS : c ∈ S.subgroupOf (Y ⊔ S) := Subgroup.mem_subgroupOf.mpr (by
            have h' : (c : G) = (x : G) := hcx
            rw [h']
            exact x.2)
          exact Subgroup.mem_map.mpr ⟨⟨c, hcS⟩, Subgroup.mem_subgroupOf.mpr hc, Subtype.ext hcx⟩
      rw [heq] at hc
      exact hc
    · exact le_normalizer_map_subtype_of_normal hC'n
  have e' : ↥(oResidual 2 (↥(Y ⊔ S) ⧸ CFSG.pCore 2 ↥(Y ⊔ S))) ⧸
      Subgroup.center ↥(oResidual 2 (↥(Y ⊔ S) ⧸ CFSG.pCore 2 ↥(Y ⊔ S))) ≃* T :=
    (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).trans e
  exact false_of_noFFModule_of_pushing_up hKH hF hq hS2' hS1' hQS' hXS hJ' hno' hT e'

end CFSG.RankThree.PartTwo.Sec15.F153

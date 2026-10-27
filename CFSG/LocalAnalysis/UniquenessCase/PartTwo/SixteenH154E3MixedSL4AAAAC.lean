module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Lift
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private def s16h_sl4_stabSub {W : Type*} [CommGroup W] (S : Subgroup W) : Subgroup (MulAut W) where
  carrier := {φ | S.map φ.toMonoidHom = S}
  mul_mem' := by
    intro a b ha hb
    have hcomp : (a * b).toMonoidHom = a.toMonoidHom.comp b.toMonoidHom := by
      ext x
      rfl
    show S.map (a * b).toMonoidHom = S
    rw [hcomp, ← Subgroup.map_map, hb, ha]
  one_mem' := by
    show S.map (1 : MulAut W).toMonoidHom = S
    rw [show (1 : MulAut W).toMonoidHom = MonoidHom.id W from rfl, Subgroup.map_id]
  inv_mem' := by
    intro a ha
    show S.map (a⁻¹).toMonoidHom = S
    have hcomp : (a⁻¹).toMonoidHom.comp a.toMonoidHom = MonoidHom.id W := by
      ext x
      simpa using MulEquivClass.coe_symm_apply_apply a x
    have hh := congrArg (fun T : Subgroup W => T.map (a⁻¹).toMonoidHom) ha
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at hh
    exact hh.symm

private lemma s16h_sl4_map_inv_eq_self {W : Type*} [CommGroup W] {S : Subgroup W}
    {σ : MulAut W} (h : S.map σ.toMonoidHom = S) : S.map (σ⁻¹).toMonoidHom = S := by
  have hcomp : (σ⁻¹).toMonoidHom.comp σ.toMonoidHom = MonoidHom.id W := by
    ext x
    simpa using MulEquivClass.coe_symm_apply_apply σ x
  have hh := congrArg (fun T : Subgroup W => T.map (σ⁻¹).toMonoidHom) h
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at hh
  exact hh.symm

theorem s16h_sl4_scalar_data_of_mbar
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {x : G} (hxM : x ∈ D.M)
    {φ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hφM : φ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hφ3 : orderOf φ = 3)
    (hstabW : ∀ z ∈ wTil ⊥ V h.hyp151.isElemAbelian L,
      φ z ∈ wTil ⊥ V h.hyp151.isElemAbelian L)
    (hstabWx : ∀ z ∈ wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x),
      φ z ∈ wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x))
    (hstabZ : ∀ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L),
      φ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hfpf : ∀ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L), φ z = z → z = 1)
    (h3C : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V)) :
    ∃ d : G, d ∈ D.M ∧ orderOf d = 3 ∧
      (∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L,
        d * w * d⁻¹ ∈ wSub ⊥ V h.hyp151.isElemAbelian L) ∧
      (∀ w ∈ conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x,
        d * w * d⁻¹ ∈ conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x) ∧
      (∀ z ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G),
        d * z * d⁻¹ ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) ∧
      (∀ z ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G),
        d * z * d⁻¹ = z → z = 1) := by
  have hV := h.hyp151.isElemAbelian
  have hMnorm : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hxstab : x ∈ stabTil ⊥ V := hMs hxM
  set C₀ : Subgroup G := preBarSub D.M ⊥ V hV ⊥ with hC₀def
  set P : Subgroup G := preBarSub D.M ⊥ V hV (Subgroup.zpowers φ) with hPdef
  have h3C₀ : ¬ 3 ∣ Nat.card ↥C₀ := by
    rw [hC₀def, ← cTilde_eq_preBarSub_bot hV hMnorm]
    exact h3C
  have hPM : P ≤ D.M := by
    intro g hg
    exact ((mem_preBarSub D.M ⊥ V hV (Subgroup.zpowers φ)).1 hg).1
  have hPstab : P ≤ stabTil ⊥ V := by
    intro g hg
    exact ((mem_preBarSub D.M ⊥ V hV (Subgroup.zpowers φ)).1 hg).2.choose
  have hbarP : barSub ⊥ V hV P = Subgroup.zpowers φ := by
    rw [hPdef, barSub_preBarSub]
    exact inf_eq_left.mpr (Subgroup.zpowers_le.mpr hφM)
  have hrel : (P ⊓ C₀).relIndex P = 3 := by
    have hh := s16c1G44_relIndex_inf_preBarSub_eq_card_barSub (M := D.M) (X := P)
      (V₀ := ⊥) (V := V) (hV := hV) hPM hPstab
    rw [hbarP, Nat.card_zpowers, hφ3] at hh
    exact hh
  have h3dvd : 3 ∣ Nat.card ↥P := by
    have hh := Subgroup.relIndex_mul_card (H := P ⊓ C₀) (K := P)
    rw [inf_eq_left.mpr inf_le_left, hrel] at hh
    exact ⟨Nat.card ↥(P ⊓ C₀), hh.symm⟩
  obtain ⟨d, hdord⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3dvd
  have hdorderG : orderOf (d : G) = 3 := by
    rw [Subgroup.orderOf_coe, hdord]
  obtain ⟨hdM, hdstab, hdbar⟩ :=
    (mem_preBarSub D.M ⊥ V hV (Subgroup.zpowers φ)).1 d.2
  set ψ : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨(d : G), hdstab⟩ with hψdef
  have hψne : ψ ≠ 1 := by
    intro hψ1
    have hdC : (d : G) ∈ F11.CTilde D.M ⊥ V :=
      (mem_cTilde_iff hV hMnorm).2 ⟨hdM, hdstab, hψ1⟩
    have hdvd : 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V) := by
      rw [← hdorderG]
      exact Subgroup.orderOf_dvd_natCard (F11.CTilde D.M ⊥ V) hdC
    exact h3C hdvd
  have hψ3 : orderOf ψ = 3 := by
    have hdvd : orderOf ψ ∣ 3 := by
      rw [← hφ3]
      exact orderOf_dvd_of_mem_zpowers hdbar
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.1 h1) hψne
    · exact h3
  have hφmem : φ ∈ Subgroup.zpowers ψ := by
    have hle : Subgroup.zpowers ψ ≤ Subgroup.zpowers φ := Subgroup.zpowers_le.mpr hdbar
    have hcard : Nat.card ↥(Subgroup.zpowers φ) ≤ Nat.card ↥(Subgroup.zpowers ψ) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hφ3, hψ3]
    have heq : Subgroup.zpowers ψ = Subgroup.zpowers φ :=
      Subgroup.eq_of_le_of_card_ge hle hcard
    rw [heq]
    exact Subgroup.mem_zpowers φ
  have hφstabW : φ ∈ s16h_sl4_stabSub (wTil ⊥ V hV L) := by
    show (wTil ⊥ V hV L).map φ.toMonoidHom = wTil ⊥ V hV L
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro q hq
      rw [Subgroup.mem_map] at hq
      obtain ⟨z, hz, rfl⟩ := hq
      exact hstabW z hz
    · rw [Subgroup.card_map_of_injective φ.injective]
  have hφstabWx : φ ∈ s16h_sl4_stabSub (wTil ⊥ V hV (conjSubgroup L x)) := by
    show (wTil ⊥ V hV (conjSubgroup L x)).map φ.toMonoidHom = wTil ⊥ V hV (conjSubgroup L x)
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro q hq
      rw [Subgroup.mem_map] at hq
      obtain ⟨z, hz, rfl⟩ := hq
      exact hstabWx z hz
    · rw [Subgroup.card_map_of_injective φ.injective]
  have hφstabZ : φ ∈ s16h_sl4_stabSub (commSub ⊤ (lBar ⊥ V hV L) ⊓
      fixV (lBar ⊥ V hV L)) := by
    show (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)).map φ.toMonoidHom =
      commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro q hq
      rw [Subgroup.mem_map] at hq
      obtain ⟨z, hz, rfl⟩ := hq
      exact hstabZ z hz
    · rw [Subgroup.card_map_of_injective φ.injective]
  have hmapW : (wTil ⊥ V hV L).map ψ.toMonoidHom = wTil ⊥ V hV L :=
    (Subgroup.zpowers_le.mpr hφstabW) hdbar
  have hmapWx : (wTil ⊥ V hV (conjSubgroup L x)).map ψ.toMonoidHom =
      wTil ⊥ V hV (conjSubgroup L x) :=
    (Subgroup.zpowers_le.mpr hφstabWx) hdbar
  have hmapZ : (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)).map ψ.toMonoidHom =
      commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L) :=
    (Subgroup.zpowers_le.mpr hφstabZ) hdbar
  have hfpfψ : ∀ z ∈ commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L), ψ z = z → z = 1 := by
    intro z hz hzfix
    have hψstab : ψ ∈ MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) z := by
      rw [MulAction.mem_stabilizer_iff]
      exact hzfix
    have hφstab : φ ∈ MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) z :=
      (Subgroup.zpowers_le.mpr hψstab) hφmem
    exact hfpf z hz (MulAction.mem_stabilizer_iff.mp hφstab)
  have hconjW : conjSubgroup (wSub ⊥ V hV L) (d : G) = wSub ⊥ V hV L := by
    rw [wSub, ← s15_Infra_preTil_map_actTil ⊥ V hV hdstab (wTil ⊥ V hV L)]
    rw [show actTil ⊥ V hV ⟨(d : G), hdstab⟩ = ψ from rfl,
      s16h_sl4_map_inv_eq_self hmapW]
  have hWcond : ∀ w ∈ wSub ⊥ V hV L,
      (d : G) * w * (d : G)⁻¹ ∈ wSub ⊥ V hV L := by
    intro w hw
    exact mem_conjSubgroup_iff.mp (hconjW.symm ▸ hw)
  have hWxeq : wSub ⊥ V hV (conjSubgroup L x) = conjSubgroup (wSub ⊥ V hV L) x :=
    s15_Infra_wSub_conjSubgroup ⊥ V L hV hxstab
  have hconjWx : conjSubgroup (conjSubgroup (wSub ⊥ V hV L) x) (d : G) =
      conjSubgroup (wSub ⊥ V hV L) x := by
    rw [← hWxeq, wSub, ← s15_Infra_preTil_map_actTil ⊥ V hV hdstab
      (wTil ⊥ V hV (conjSubgroup L x))]
    rw [show actTil ⊥ V hV ⟨(d : G), hdstab⟩ = ψ from rfl,
      s16h_sl4_map_inv_eq_self hmapWx]
  have hWxcond : ∀ w ∈ conjSubgroup (wSub ⊥ V hV L) x,
      (d : G) * w * (d : G)⁻¹ ∈ conjSubgroup (wSub ⊥ V hV L) x := by
    intro w hw
    exact mem_conjSubgroup_iff.mp (hconjWx.symm ▸ hw)
  have hconjZ : conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) (d : G) =
      wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) := by
    rw [s16h_wSub_inf_centralizer_eq_preTil D h]
    rw [← s15_Infra_preTil_map_actTil ⊥ V hV hdstab
      (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L))]
    rw [show actTil ⊥ V hV ⟨(d : G), hdstab⟩ = ψ from rfl,
      s16h_sl4_map_inv_eq_self hmapZ]
  have hZcond : ∀ z ∈ wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G),
      (d : G) * z * (d : G)⁻¹ ∈ wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) := by
    intro z hz
    exact mem_conjSubgroup_iff.mp (hconjZ.symm ▸ hz)
  have hfpfc : ∀ z ∈ wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G),
      (d : G) * z * (d : G)⁻¹ = z → z = 1 := by
    intro z hz hzfix
    rw [s16h_wSub_inf_centralizer_eq_preTil D h] at hz
    have hzV : z ∈ V := preTil_le ⊥ V hV _ hz
    have hzmk : mkTil ⊥ V hV (IntMod.mk hV ⟨z, hzV⟩) ∈
        commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L) :=
      (mem_preTil_iff_of_mem ⊥ V hV _ hzV).1 hz
    have hzψ : ψ (mkTil ⊥ V hV (IntMod.mk hV ⟨z, hzV⟩)) =
        mkTil ⊥ V hV (IntMod.mk hV ⟨z, hzV⟩) := by
      rw [show ψ = actTil ⊥ V hV ⟨(d : G), hdstab⟩ from rfl, actTil_mk,
        mkTil_eq_iff, actStab_apply_val]
      show (↑d * z * (↑d)⁻¹) * z⁻¹ ∈ (⊥ : Subgroup G)
      rw [hzfix]
      simp
    have hmk1 : mkTil ⊥ V hV (IntMod.mk hV ⟨z, hzV⟩) = 1 := hfpfψ _ hzmk hzψ
    have hzmem : ((IntMod.mk hV ⟨z, hzV⟩).val : G) ∈ (⊥ : Subgroup G) := by
      rw [← mem_modNull]
      exact (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV)
        (IntMod.mk hV ⟨z, hzV⟩)).1 hmk1
    exact Subgroup.mem_bot.1 hzmem
  exact ⟨(d : G), hdM, hdorderG, hWcond, hWxcond, hZcond, hfpfc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFourModules
public import CFSG.CGT.PushingUpLit.BHS6.NestedLinear
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Tools2
public import CFSG.Quasithin.Vol2.Ch3zTrans

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def IsNaturalChiefStep (H U L N : Subgroup G) (hstep : IsChiefStep H U L N)
    (hUH : U ≤ H) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) (m : ℕ) : Prop :=
  ∃ e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m),
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    IsNaturalModule (l2ChiefSectionRep hstep hUH hE e)

theorem natCard_quotient_of_isNaturalChiefStep {H U L N : Subgroup G} {m : ℕ}
    {hstep : IsChiefStep H U L N} {hUH : U ≤ H} {hE : IsElemAbelian 2 (Ch3z.chiefMod L N)}
    (h : IsNaturalChiefStep H U L N hstep hUH hE m) :
    Nat.card (N ⧸ L.subgroupOf N) = (Nat.card (GaloisField 2 m)) ^ 2 := by
  classical
  obtain ⟨e, hnat⟩ := h
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn (H := H) (U := U) hstep.2.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  haveI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr hNL
  have hquot : Nat.card (N ⧸ L.subgroupOf N) = Nat.card ↥(Ch3z.chiefMod L N) :=
    Nat.card_congr (Ch3z.chiefQuotEquiv hNL).toEquiv
  have hnat' : Nat.card (Additive (Ch3z.chiefMod L N)) = Nat.card (Fin 2 → GaloisField 2 m) := by
    obtain ⟨φ, -⟩ := hnat
    exact Nat.card_congr φ.toEquiv
  have hnat'' : Nat.card ↥(Ch3z.chiefMod L N) = Nat.card (Fin 2 → GaloisField 2 m) :=
    (Nat.card_congr Additive.ofMul).symm.trans hnat'
  rw [hquot, hnat'', Nat.card_fun]
  norm_num

theorem isNaturalChiefStep_of_eq {H U L N A : Subgroup G} {m : ℕ} (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hU : IsElemAbelian 2 U) (hUH : U ≤ H)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    (hA : IsElemAbelian 2 A) (hAH : A ≤ H)
    (hstep_eq : (centralizerMod L N A).relIndex N = 2 ^ m)
    (hA_eq : (A ⊓ pCoreOf 2 H).relIndex A = 2 ^ m) :
    IsNaturalChiefStep H U L N hstep hUH
      (CFSG.Quasithin.isElemAbelian_chiefMod hstep hUH hU.isPGroup) m := by
  classical
  let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hUH hU.isPGroup
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  obtain ⟨e, ρ, φ, -, -, hcompat, hnatiso, -⟩ :=
    l2_chiefStep_natural hm2 hL2 hU hUH hstep hnc hA hAH hstep_eq hA_eq
  refine ⟨e, ?_⟩
  have hρeq : ρ = l2ChiefSectionRep hstep hUH hE e := by
    refine MonoidHom.ext fun g' => LinearMap.ext fun w => ?_
    obtain ⟨h, rfl⟩ := e.surjective g'
    obtain ⟨h', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥H) h
    have hw : Additive.ofMul w.toMul = w := rfl
    rw [← hw, QuotientGroup.mk'_apply, hcompat h' w.toMul, l2ChiefSectionRep_apply_mk]
  rw [← hρeq]
  exact ⟨φ, hnatiso⟩

private theorem chiefIota_eq_of_mul_inv_mem {L N : Subgroup G}
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) {u v : ↥N}
    (h : (u : G) * (v : G)⁻¹ ∈ L) : Ch3z.chiefIota hNL u = Ch3z.chiefIota hNL v := by
  have hmem : ((u * v⁻¹ : ↥N) : G) ∈ L := by simpa using h
  have h1 : Ch3z.chiefIota hNL (u * v⁻¹) = 1 :=
    (Ch3z.chiefIota_eq_one_iff hNL (u * v⁻¹)).mpr hmem
  have hstep : u = (u * v⁻¹) * v := by group
  calc Ch3z.chiefIota hNL u = Ch3z.chiefIota hNL ((u * v⁻¹) * v) :=
        congrArg (Ch3z.chiefIota hNL) hstep
    _ = Ch3z.chiefIota hNL (u * v⁻¹) * Ch3z.chiefIota hNL v := map_mul _ _ _
    _ = Ch3z.chiefIota hNL v := by rw [h1, one_mul]

theorem mem_of_conj_mem_of_isNaturalChiefStep {H U L N : Subgroup G} {m : ℕ}
    {hstep : IsChiefStep H U L N} {hUH : U ≤ H} {hE : IsElemAbelian 2 (Ch3z.chiefMod L N)}
    (hnat : IsNaturalChiefStep H U L N hstep hUH hE m)
    {d : G} (hdH : d ∈ H) (hdQ : d ∉ pCoreOf 2 H) (hdo : Odd (orderOf d))
    {x : G} (hx : x ∈ N) (hxd : d * x * d⁻¹ * x⁻¹ ∈ L) : x ∈ L := by
  classical
  obtain ⟨e, hnatmod⟩ := hnat
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn (H := H) (U := U) hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn (H := H) (U := U) hstep.1
  have hNU : N ≤ U := hstep.1.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hNU.trans hUH).trans hHL
  let dH : ↥H := ⟨d, hdH⟩
  let q : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)
  let ψ : ↥H →* SL(2, GaloisField 2 m) := e.toMonoidHom.comp q
  let g : SL(2, GaloisField 2 m) := ψ dH
  let w : Additive (Ch3z.chiefMod L N) := Additive.ofMul (Ch3z.chiefIota hNL ⟨x, hx⟩)
  have hmem : d * x * d⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hdH) x).mp hx
  have hact : l2ChiefSectionAction hstep hE dH (Ch3z.chiefIota hNL ⟨x, hx⟩) =
      Ch3z.chiefIota hNL ⟨x, hx⟩ := by
    rw [l2ChiefSectionAction_eq_chiefPsi]
    rw [Ch3z.chiefPsi_iota hHL hHN hNL dH ⟨x, hx⟩ hmem]
    exact chiefIota_eq_of_mul_inv_mem hNL (by simpa using hxd)
  have hfix : (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)).mulVec
      (Classical.choose hnatmod w) = Classical.choose hnatmod w := by
    have h2 : l2ChiefSectionRep hstep hUH hE e (e (QuotientGroup.mk dH)) w = w := by
      rw [l2ChiefSectionRep_apply_mk, hact]
    have h1 := (Classical.choose_spec hnatmod) (e (QuotientGroup.mk dH)) w
    rw [h2] at h1
    simpa [g, ψ, q] using h1.symm
  have hoddg : Odd (orderOf g) := by
    have hdvd : orderOf g ∣ orderOf dH := by
      have := orderOf_map_dvd ψ dH
      simpa [g] using this
    have h2 : orderOf dH = orderOf d := by
      simpa [dH] using (Subgroup.orderOf_coe dH).symm
    exact Odd.of_dvd_nat (h2 ▸ hdo) hdvd
  by_contra hxL
  have hwne : w ≠ 0 := by
    intro h0
    refine hxL ?_
    have h1 : Ch3z.chiefIota hNL ⟨x, hx⟩ = 1 := by
      have := congrArg Additive.toMul h0
      simpa [w] using this
    exact (Ch3z.chiefIota_eq_one_iff hNL ⟨x, hx⟩).mp h1
  have hvne : Classical.choose hnatmod w ≠ 0 := by
    intro h0
    exact hwne ((Classical.choose hnatmod).injective (by simpa using h0))
  have hgsmul : g • (Classical.choose hnatmod w) = Classical.choose hnatmod w := by
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.smul_eq_mulVec']
    exact hfix
  have hg1 : g = 1 :=
    CFSG.CGT.PushingUpLit.BHS6.eq_one_of_odd_of_smul_eq hoddg hvne hgsmul
  have hq1 : q dH = 1 := e.injective (by rw [map_one]; exact hg1)
  have hdmemH : dH ∈ CFSG.Open.pCore 2 ↥H :=
    (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥H) dH).mp (by simpa [q] using hq1)
  exact hdQ (Subgroup.mem_map.mpr ⟨dH, hdmemH, rfl⟩)

end CFSG.Quasithin.Stroth

end

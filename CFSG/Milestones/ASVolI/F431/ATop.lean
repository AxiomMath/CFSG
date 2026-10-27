module

public import CFSG.GH74.KGroups.U33
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

section TopGeneral

theorem burnsideF4m_finite_mulAut (H : Type) [Group H] [Finite H] : Finite (MulAut H) :=
  Finite.of_injective (fun f : MulAut H => (f : H → H)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem burnsideF4m_eq_top_of_derived {E : Type} [Group E] [Finite E] {Gp : Subgroup E}
    [hGn : Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hcN : ∀ g ∈ Gp, (∀ n ∈ ⁅Gp, Gp⁆, g * n = n * g) → g = 1)
    (haut : Nat.card (MulAut ↥⁅Gp, Gp⁆) ≤ Nat.card Gp) : Gp = ⊤ := by
  haveI hN : (⁅Gp, Gp⁆ : Subgroup E).Normal := Subgroup.commutator_normal Gp Gp
  have hinj : Function.Injective (MulAut.conjNormal : E →* MulAut ↥⁅Gp, Gp⁆) := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hen : ∀ n ∈ ⁅Gp, Gp⁆, e * n = n * e := by
      intro n hn
      have h := congrArg (fun φ : MulAut ↥⁅Gp, Gp⁆ => ((φ ⟨n, hn⟩ : ↥⁅Gp, Gp⁆) : E)) he
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
      calc e * n = e * n * e⁻¹ * e := by group
        _ = n * e := by rw [h]
    have heC : e ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hk : e * g * e⁻¹ ∈ Gp := hGn.conj_mem g hg e
      have hh : g⁻¹ * (e * g * e⁻¹) ∈ Gp := Gp.mul_mem (Gp.inv_mem hg) hk
      have h1 : g⁻¹ * (e * g * e⁻¹) = 1 := by
        refine hcN _ hh fun n hn => ?_
        have hgn : g * n * g⁻¹ ∈ ⁅Gp, Gp⁆ := hN.conj_mem n hn g
        have hc1 : e⁻¹ * n = n * e⁻¹ := by
          calc e⁻¹ * n = e⁻¹ * (n * e) * e⁻¹ := by group
            _ = e⁻¹ * (e * n) * e⁻¹ := by rw [hen n hn]
            _ = n * e⁻¹ := by group
        have hc2 := hen _ hgn
        calc g⁻¹ * (e * g * e⁻¹) * n = g⁻¹ * e * g * (e⁻¹ * n) := by group
          _ = g⁻¹ * e * g * (n * e⁻¹) := by rw [hc1]
          _ = g⁻¹ * (e * (g * n * g⁻¹)) * g * e⁻¹ := by group
          _ = g⁻¹ * ((g * n * g⁻¹) * e) * g * e⁻¹ := by rw [hc2]
          _ = n * (g⁻¹ * (e * g * e⁻¹)) := by group
      have h2 : e * g * e⁻¹ = g := by
        calc e * g * e⁻¹ = g * (g⁻¹ * (e * g * e⁻¹)) := by group
          _ = g := by rw [h1, mul_one]
      calc g * e = e * g * e⁻¹ * e := by rw [h2]
        _ = e * g := by group
    rw [hc, Subgroup.mem_bot] at heC
    exact heC
  haveI := burnsideF4m_finite_mulAut ↥⁅Gp, Gp⁆
  have hle : Nat.card E ≤ Nat.card (MulAut ↥⁅Gp, Gp⁆) := Nat.card_le_card_of_injective _ hinj
  exact Subgroup.eq_top_of_card_eq Gp
    (le_antisymm (Subgroup.card_le_card_group Gp) (hle.trans haut))

theorem burnsideF4m_eq_top_of_model {E : Type} [Group E] [Finite E] {Gp : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {M : Type} [Group M]
    (ψ : M ≃* ↥Gp) (hcM : ∀ g : M, (∀ n ∈ commutator M, g * n = n * g) → g = 1)
    (hautM : Nat.card (MulAut ↥(commutator M)) ≤ Nat.card M) : Gp = ⊤ := by
  let f : M →* E := Gp.subtype.comp ψ.toMonoidHom
  have hf : ∀ m, f m = ((ψ m : ↥Gp) : E) := fun _ => rfl
  have hfi : Function.Injective f := Gp.subtype_injective.comp ψ.injective
  have hrange : f.range = Gp := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      rw [hf]
      exact (ψ m).2
    · intro hx
      exact ⟨ψ.symm ⟨x, hx⟩, by rw [hf, MulEquiv.apply_symm_apply]⟩
  have hmap : (commutator M).map f = ⁅Gp, Gp⁆ := by
    rw [map_commutator_eq, hrange]
  refine burnsideF4m_eq_top_of_derived hc ?_ ?_
  · intro g hg hgN
    have hg' : g ∈ f.range := hrange.symm ▸ hg
    obtain ⟨m, rfl⟩ := hg'
    have hm : m = 1 := hcM m fun n hn => hfi (by
      rw [map_mul, map_mul]
      exact hgN (f n) (hmap ▸ Subgroup.mem_map_of_mem f hn))
    rw [hm, map_one]
  · have e1 : ↥(commutator M) ≃* ↥⁅Gp, Gp⁆ :=
      ((commutator M).equivMapOfInjective f hfi).trans (MulEquiv.subgroupCongr hmap)
    rw [← Nat.card_congr (MulAut.congr e1).toEquiv, ← Nat.card_congr ψ.toEquiv]
    exact hautM

theorem burnsideF4m_indexTwo_centralizer {J N : Type*} [Group J] [Group N] {f : J →* N}
    {ρ : N} {Φ : J ≃* J} (D : CFSG.Quasithin.IndexTwoData f ρ Φ) (hZ : Subgroup.center J = ⊥)
    (g : N) (hg : ∀ x, g * f x = f x * g) : g = 1 := by
  rcases D.cover g with ⟨w, rfl⟩ | ⟨w, hw⟩
  · have hw : w ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply D.inj
      rw [map_mul, map_mul]
      exact (hg x).symm
    rw [hZ, Subgroup.mem_bot] at hw
    rw [hw, map_one]
  · exfalso
    apply D.outer
    have hsq : ρ * ρ = 1 := D.sq
    have hρ : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hsq
    have hg' : g = f w * ρ := by
      calc g = g * ρ * ρ := by rw [mul_assoc, hsq, mul_one]
        _ = f w * ρ := by rw [hw]
    refine ⟨w⁻¹, fun x => D.inj ?_⟩
    have h1 := hg x
    rw [hg'] at h1
    have h3 : ρ * f x * ρ⁻¹ = f (Φ x) := D.conj x
    rw [map_mul, map_mul, map_inv, inv_inv, ← h3, hρ]
    calc ρ * f x * ρ = (f w)⁻¹ * (f w * ρ * f x) * ρ := by group
      _ = (f w)⁻¹ * (f x * (f w * ρ)) * ρ := by rw [h1]
      _ = (f w)⁻¹ * f x * f w * (ρ * ρ) := by group
      _ = (f w)⁻¹ * f x * f w := by rw [hsq, mul_one]

end TopGeneral

section G2Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin

set_option linter.unusedSectionVars false


theorem burnsideF4m_u33_equiv_QP :
    Nonempty (U33G ≃* ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup) := by
  obtain ⟨e3⟩ := CFSG.Quasithin.u33Pres_mulEquiv_perm
  have hsz : CFSG.Quasithin.u33Gens.size = 5 := CFSG.Quasithin.u33Chain_check.1
  have hset : {g | ∃ k < CFSG.Quasithin.u33Gens.size,
      CFSG.Monster.B.Co2.permOfArr 28 CFSG.Quasithin.u33Gens[k]! = g} =
      Set.range CFSG.Quasithin.u33Img := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [hsz] at hk
      exact ⟨⟨k, hk⟩, (CFSG.Quasithin.permOfArr_u33Gens ⟨k, hk⟩).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [hsz]; exact k.2, CFSG.Quasithin.permOfArr_u33Gens k⟩
  rw [hset, CFSG.GH74.KGroups.U33.J_eq] at e3
  exact ⟨e3⟩

theorem burnsideF4m_g2_commutator {K : Type} [Field K] (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) : commutator (G2Group K) = (g2HomC h2).range := by
  apply Subgroup.map_injective (adjointGroup Tag.G2 K).subtype_injective
  have hcomp : (adjointGroup Tag.G2 K).subtype.comp (g2HomC h2) = g2Hom h2 :=
    MonoidHom.ext fun _ => rfl
  rw [map_commutator_eq, Subgroup.range_subtype, g2_derived_eq_range h2 hk2, MonoidHom.map_range,
    hcomp]

theorem burnsideF4m_g2_centralizer {K : Type} [Field K] (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) (g : G2Group K)
    (hg : ∀ n ∈ commutator (G2Group K), g * n = n * g) : g = 1 := by
  rw [burnsideF4m_g2_commutator h2 hk2] at hg
  exact burnsideF4m_indexTwo_centralizer (g2IndexTwoData h2 hk2) burnsideF4h_g2_center_u33 g
    fun x => hg _ ⟨x, rfl⟩

theorem burnsideF4m_g2_card_mulAut {K : Type} [Field K] (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    Nat.card (MulAut ↥(commutator (G2Group K))) ≤ Nat.card (G2Group K) := by
  have e1 : ↥(commutator (G2Group K)) ≃* U33G :=
    (MulEquiv.subgroupCongr (burnsideF4m_g2_commutator h2 hk2)).trans
      (MonoidHom.ofInjective (g2HomC_injective h2)).symm
  obtain ⟨e3⟩ := burnsideF4m_u33_equiv_QP
  rw [CFSG.GH74.KGroups.U33.card_mulAut (e1.trans e3)]
  have hidx := (g2IndexTwoData h2 hk2).index_range
  have hcard : Nat.card (g2HomC h2).range = 6048 := by
    rw [← card_u33Pres]
    exact (Nat.card_congr (MonoidHom.ofInjective (g2HomC_injective h2)).toEquiv).symm
  have h := Subgroup.card_mul_index (g2HomC h2).range
  rw [hcard, hidx] at h
  omega

theorem burnsideF4m_top_of_G2two {E : Type} [Group E] [Finite E] {Gp : Subgroup E} [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) (hmodel : IsGenLie ↥Gp .G2 2 1) : Gp = ⊤ := by
  obtain ⟨-, -, K, fK, finK, hK, ⟨e⟩⟩ := hmodel
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have h2 := two_eq_zero_of_card_two hK2
  have hk2 := eq_zero_or_eq_one_of_card_two hK2
  have hZ : Subgroup.center (G2Group K) = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let φ : AdjointQuotient Tag.G2 K ≃* G2Group K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact burnsideF4m_eq_top_of_model hc (φ.symm.trans e.symm) (burnsideF4m_g2_centralizer h2 hk2)
    (burnsideF4m_g2_card_mulAut h2 hk2)

end G2Two

section F4Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Sporadic.Schreier.Tits CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

set_option linter.unusedSectionVars false


theorem burnsideF4m_titsA_commutator : commutator ↥titsA = titsD.subgroupOf titsA := by
  apply Subgroup.map_injective titsA.subtype_injective
  rw [map_commutator_eq, Subgroup.range_subtype, titsA_commutator,
    Subgroup.map_subgroupOf_eq_of_le titsD_le_titsA]

theorem burnsideF4m_titsA_centralizer (g : ↥titsA)
    (hg : ∀ n ∈ commutator ↥titsA, g * n = n * g) : g = 1 := by
  rw [burnsideF4m_titsA_commutator] at hg
  apply titsConj_injective
  rw [map_one]
  refine MulEquiv.ext fun d => Subtype.ext ?_
  rw [coe_titsConj_apply, MulAut.one_apply]
  have h := congrArg Subtype.val (hg ⟨d, titsD_le_titsA d.2⟩ d.2)
  simp only [Subgroup.coe_mul] at h
  rw [h, mul_inv_cancel_right]

theorem burnsideF4m_titsA_card_mulAut :
    Nat.card (MulAut ↥(commutator ↥titsA)) ≤ Nat.card ↥titsA := by
  have e1 : ↥(commutator ↥titsA) ≃* ↥titsD :=
    (MulEquiv.subgroupCongr burnsideF4m_titsA_commutator).trans
      (Subgroup.subgroupOfEquivOfLe titsD_le_titsA)
  rw [Nat.card_congr (MulAut.congr e1).toEquiv, ← Nat.card_congr titsConjEquiv.toEquiv]

theorem burnsideF4m_top_of_F4two {E : Type} [Group E] [Finite E] {Gp : Subgroup E} [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) (hmodel : IsGenLie ↥Gp .F4tw 2 1) : Gp = ⊤ := by
  obtain ⟨-, -, ⟨-, K, fK, finK, hK, ⟨e⟩⟩ | ⟨h3, -⟩⟩ := hmodel
  · haveI : CharP K 2 := by
      have : Fintype K := Fintype.ofFinite K
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
    haveI : CharP K F4.prime := (inferInstance : CharP K 2)
    haveI : Fact (Nat.card K = 2) := ⟨hK⟩
    have hR : ExceptionalRoots.reeGroup K 0 = F4.reeGamma K 0 := burnsideF4gF4_reeGroup_eq
    let ψ1 : ↥(ExceptionalRoots.reeGroup K 0) ≃* ↥(F4.reeGamma K 0) := MulEquiv.subgroupCongr hR
    let ψ2 : ↥(reeFixed F4 K 0) ≃* ↥titsA := titsIso
    let ψ3 : ↥(reeFixed F4 K 0) ≃* ↥(F4.reeGamma K 0) := reeFixedEquivReeGamma K 0
    let ψ : ↥(ExceptionalRoots.reeGroup K 0) ≃* ↥titsA := (ψ1.trans ψ3.symm).trans ψ2
    have hZ : Subgroup.center ↥(ExceptionalRoots.reeGroup K 0) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      have h1 : ψ z = 1 := burnsideF4m_titsA_centralizer (ψ z) fun n _ => by
        obtain ⟨m, rfl⟩ := ψ.surjective n
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz m]
      exact ψ.injective (h1.trans (map_one ψ).symm)
    let φ : (↥(ExceptionalRoots.reeGroup K 0) ⧸ Subgroup.center ↥(ExceptionalRoots.reeGroup K 0))
        ≃* ↥(ExceptionalRoots.reeGroup K 0) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact burnsideF4m_eq_top_of_model hc ((ψ.symm.trans φ.symm).trans e.symm)
      burnsideF4m_titsA_centralizer burnsideF4m_titsA_card_mulAut
  · omega

end F4Two

section TopTwo

set_option linter.unusedSectionVars false


theorem burnsideF4m_top_G2two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 1 Gp M₁ M₂) : Gp = ⊤ := by
  haveI := hyp.finite
  haveI := hyp.normal
  exact burnsideF4m_top_of_G2two hyp.centralizer_trivial hyp.model

end TopTwo

section TopF4

set_option linter.unusedSectionVars false


theorem burnsideF4m_top_F4two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw 2 1 Gp M₁ M₂) : Gp = ⊤ := by
  haveI := hyp.finite
  haveI := hyp.normal
  exact burnsideF4m_top_of_F4two hyp.centralizer_trivial hyp.model

end TopF4

end CFSG.ASVolI

module

public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11c.Sec66Conj
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldOrthogonal

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedClassicalModel)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage coordinateFieldMap)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus plusIndexEquiv minusIndexEquiv
    coordinatePlusWitnessEquiv coordinateMinusWitnessEquiv coordinate_model_witness_plus
    coordinate_model_witness_minus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)
open CFSG.RankThree.PartOne (SubfieldConclusion)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (IsExtension fieldAutT inclEquiv)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (orthPlus_hyps orthMinus_hyps congr_eq_fieldAutT)

theorem no_plane_of_outPChain {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (h : OutStructure.OutPChain p T) (E : Subgroup (MulAut T)) (hE : IsElementaryAbelian p ↥E)
    (hcard : Nat.card E = p ^ 2) (hEinn : E ⊓ innerAut T = ⊥) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hnc : ¬ IsCyclic E := IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨β, hβ1⟩ : ∃ β : E, β ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton E := ⟨fun a b => by rw [hcon a, hcon b]⟩
    have h1 : Nat.card E = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [hcard] at h1
    have := hp.one_lt
    nlinarith
  obtain ⟨α, hαβ⟩ : ∃ α : E, α ∉ Subgroup.zpowers β := by
    by_contra hcon
    push Not at hcon
    exact hnc ⟨⟨β, fun x => hcon x⟩⟩
  have hαp : (α : MulAut T) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ α.2
  have hβp : (β : MulAut T) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ β.2
  have hα1 : α ≠ 1 := fun h => hαβ (h ▸ (Subgroup.zpowers β).one_mem)
  have hαord : orderOf α = p := orderOf_eq_prime (Subtype.ext hαp) hα1
  have hβord : orderOf β = p := orderOf_eq_prime (Subtype.ext hβp) hβ1
  have hcomm : (α : MulAut T) * β = β * α :=
    congrArg Subtype.val (IsMulCommutative.is_comm.comm α β)
  have hsubInn : ∀ x : E, (x : MulAut T) ∈ OutStructure.Inn T → x = 1 := by
    intro x hx
    have hxm : (x : MulAut T) ∈ E ⊓ innerAut T := ⟨x.2, hx⟩
    rw [hEinn, Subgroup.mem_bot] at hxm
    exact Subtype.ext hxm
  have hαI : (α : MulAut T) ^ (p ^ 1) ∈ OutStructure.Inn T := by
    rw [pow_one, hαp]
    exact (OutStructure.Inn T).one_mem
  have hβI : (β : MulAut T) ^ (p ^ 1) ∈ OutStructure.Inn T := by
    rw [pow_one, hβp]
    exact (OutStructure.Inn T).one_mem
  rcases h.comparable hcomm hαI hβI with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    have hγ1 := hsubInn (α * β ^ m) (by simpa using hm)
    apply hαβ
    have hαeq : α = β ^ (-m) := by
      rw [mul_eq_one_iff_eq_inv] at hγ1
      rw [hγ1, zpow_neg]
    rw [hαeq]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers β) _
  ·
    have hγ1 := hsubInn (β * α ^ m) (by simpa using hm)
    have hβα : β = α ^ (-m) := by
      rw [mul_eq_one_iff_eq_inv] at hγ1
      rw [hγ1, zpow_neg]
    have hβmem : β ∈ Subgroup.zpowers α := by
      rw [hβα]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers α) _
    have hle : Subgroup.zpowers β ≤ Subgroup.zpowers α := (Subgroup.zpowers_le).mpr hβmem
    have hcα : Nat.card (Subgroup.zpowers α) = p := by rw [Nat.card_zpowers, hαord]
    have hcβ : Nat.card (Subgroup.zpowers β) = p := by rw [Nat.card_zpowers, hβord]
    have heq : Subgroup.zpowers β = Subgroup.zpowers α :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcα, hcβ])
    exact hαβ (heq ▸ Subgroup.mem_zpowers α)

section ImageAndLinear

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem orth_mem_image_of_orderOf (hidx : (matrixProjectiveImage Q).index ≤ 3) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {a : MulAut (matrixProjectiveDerived Q)} (ha : orderOf a = p) :
    a ∈ matrixProjectiveImage Q := by
  refine OutStructure.mem_of_pow_mem_of_index_le_three _ hidx hp hp3 (k := 1) ?_
  rw [pow_one, ← ha, pow_orderOf_eq_one]
  exact one_mem _

theorem orth_not_mem_linearRange_of_not_inner [CharP K 2]
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {a : MulAut (matrixProjectiveDerived Q)} (hap : a ^ p = 1)
    (hna : a ∉ innerAut (matrixProjectiveDerived Q)) : a ∉ (linearConjugationHom Q).range := by
  rintro ⟨g, hg⟩
  have hQ : ∃ v, Q v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have haD : a ∈ OutStructure.orthD Q := (OutStructure.mem_orthD_iff Q a).mpr ⟨g, hg⟩
  refine hna (OutStructure.orthD_D2 Q hQ hnd hT hp hp2 haD (k := 1) ?_)
  rw [pow_one, hap]
  exact (OutStructure.Inn _).one_mem

end ImageAndLinear

theorem orth_lieModel_fixRes_of_simple_normal {C : Type} [Group C] [Finite C] (β : MulAut C)
    (N J : Subgroup C) (hfix : ∀ x, β x = x ↔ x ∈ N) (hJN : J ≤ N)
    (hJnorm : (J.subgroupOf N).Normal)
    (hq : ∀ [(J.subgroupOf N).Normal], IsPGroup 2 (↥N ⧸ J.subgroupOf N))
    (hsimple : IsSimpleGroup ↥J) (hnab : ∃ x y : ↥J, x * y ≠ y * x) {X : Type} [Group X]
    (e : ↥J ≃* X) {t : StatedLieTag} {n f : ℕ} (hX : LieModel X t n 2 f) :
    LieModel (↥(fixRes β) ⧸ Subgroup.center ↥(fixRes β)) t n 2 f := by
  have hNeq : fixSub β = N := Subgroup.ext hfix
  subst hNeq
  have hperf : Group.IsPerfect ↥J := isPerfect_of_simple_nonabelian hnab
  have hZ : Subgroup.center ↥J = ⊥ := center_eq_bot_of_simple' hnab
  have hsolv : Group.IsSolvable (↥(fixSub β) ⧸ J.subgroupOf (fixSub β)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpg : IsPGroup 2 (↥(fixSub β) ⧸ J.subgroupOf (fixSub β)) := @hq hJnorm
    have : Group.IsNilpotent (↥(fixSub β) ⧸ J.subgroupOf (fixSub β)) := hpg.isNilpotent
    infer_instance
  exact lieModel_fixRes_of_normal hJN hJnorm hperf hsolv ((centerQuotientEquivSelf hZ).trans e) hX

section FieldAutOfConclusion

variable {K : Type} [Field K] [Finite K] {d : ℕ} {k : Subfield K}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}

theorem orth_fieldAutT_of_subfieldConclusion {T : Type} [Group T] [Finite T] {p f f' n : ℕ}
    {t : StatedLieTag} (hM : LieModel T t n 2 f) (hff' : f = p * f') (hf' : 1 ≤ f')
    (hext : IsExtension k Q₀ Q) (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hconc : SubfieldConclusion k Q₀ Q σ p hext hQσ) (hd : 0 < d)
    (hX : LieModel (matrixProjectiveDerived Q₀) t n 2 f') (ψ : T ≃* matrixProjectiveDerived Q)
    (α : MulAut T) (hα : MulAut.congr ψ α = fieldAutT Q σ hQσ) : FieldAutT p α := by
  obtain ⟨⟨-, hJs, hJn⟩, -, hfixiff, hJN, hJnorm, hq, -, -, -, -⟩ := hconc
  have : Finite (matrixProjectiveDerived Q) := inferInstance
  refine fieldAutT_of_conj_fix ψ hM hff' hf' α (fieldAutT Q σ hQσ) 1
    (by rw [one_mul, inv_one, mul_one]; exact hα) ?_
  exact orth_lieModel_fixRes_of_simple_normal (fieldAutT Q σ hQσ) _ _ hfixiff hJN hJnorm hq hJs hJn
    (inclEquiv k hext hd).symm hX

end FieldAutOfConclusion

theorem lieModel_orthPlus_subfield {n f' : ℕ} (hn : 4 ≤ n) (hf' : 1 ≤ f') (k : Type) [Field k]
    [Finite k] (hk : Nat.card k = 2 ^ f') :
    LieModel (matrixProjectiveDerived (coordinateQuadPlus n k)) .POmegaPlus n 2 f' :=
  (lieModel_classical_iff (by decide)).mpr
    ⟨⟨Nat.prime_two, hf', hn⟩, k, inferInstance, inferInstance, hk,
      ⟨(statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n k) (coe_quadPlus n k)).symm⟩⟩

theorem lieModel_orthMinus_subfield {n f' : ℕ} (hn : 4 ≤ n) (hf' : 1 ≤ f') (k : Type) [Field k]
    [Finite k] (hk : Nat.card k = 2 ^ f') (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    LieModel (matrixProjectiveDerived (coordinateQuadMinus n k (by omega) b c)) .POmegaMinus n 2
      f' :=
  (lieModel_classical_iff (by decide)).mpr
    ⟨⟨Nat.prime_two, hf', hn⟩, k, inferInstance, inferInstance, hk, b, c, hirr,
      ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n (by omega)) (quadMinus n k b c)
        (coe_quadMinus n k b c)).symm⟩⟩

theorem sec66T_K2_POmegaPlus : Sec66T_K2 .POmegaPlus := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .POmegaPlus n 2 f :=
    (lieModel_classical_iff (by decide)).mp hM
  have hn : 4 ≤ n := hadm.2.2
  by_cases hn5 : 5 ≤ n
  · exact no_plane_of_outPNice hp
      (OutStructure.outPNice_POmegaPlus_ge_five hp (by omega) hn5 hC) E hE hcard hEinn
  · have hn4 : n = 4 := by omega
    subst hn4
    exact no_plane_of_outPChain hp (OutStructure.outPChain_POmegaPlus_four hp (by omega) hC) E hE
      hcard hEinn

theorem sec66T_K2_POmegaMinus : Sec66T_K2 .POmegaMinus := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .POmegaMinus n 2 f :=
    (lieModel_classical_iff (by decide)).mp hM
  exact no_plane_of_outPNice hp
    (OutStructure.outPNice_POmegaMinus hp (by omega) hadm.2.2 hC) E hE hcard hEinn

theorem sec66T_K2_POmegaOdd : Sec66T_K2 .POmegaOdd := by
  intro T _ _ p hp hp5 hmodel
  obtain ⟨n, f, hadm, -⟩ := hmodel
  exact absurd rfl hadm.2.2.2

theorem sec66T_K1_POmegaPlus : Sec66T_K1 .POmegaPlus := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn _ _ _ _ _ _ _ _ _
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .POmegaPlus n 2 f :=
    (lieModel_classical_iff (by decide)).mp hM
  have hf : 1 ≤ f := hadm.2.1
  have hn4 : 4 ≤ n := hadm.2.2
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, hidx⟩ := orthPlus_hyps hC K hK e
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_plus hC K hK e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinatePlusWitnessEquiv K e) α := ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def]
    exact (orderOf_congr _ α).trans hord
  have hainn : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rw [ha_def]
    exact fun h => hαinn ((mem_innerAut_congr _ α).mp h)
  have haE : a ∈ matrixProjectiveImage (coordinateQuadPlus n K) :=
    orth_mem_image_of_orderOf _ hidx hp hp3 ha
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have haD : a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range :=
    orth_not_mem_linearRange_of_not_inner _ hnd hS3 hp hp2 hap hainn
  have hdesc := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent T
    .POmegaPlus (Or.inr (Or.inl rfl)) n 2 f p hC hp hp3 hp2 K hK e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, V, cc, Q₀, hVκ, hVr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hfp1 : 1 ≤ f / p := (Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpf)
  have hff' : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  have hcard' : Nat.card (semilinearFixedSubfield V.val.right) = 2 ^ (f / p) := by
    rw [hVr]
    exact hcard
  have hord'' : orderOf V.val.right = p := by
    rw [hVr]
    exact hord'
  have hK' : Nat.card K = 2 ^ (f / p * p) := by
    rw [Nat.div_mul_cancel hpf]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield V.val.right ↔ V.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  obtain ⟨-, hconc⟩ :=
    CFSG.RankThree.PartOne.orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
      .POmegaPlus (Or.inr (Or.inl rfl)) n 2 (f / p) p hCM.1 hp hp3 hp2 K
      (semilinearFixedSubfield V.val.right) hcard' hK' V.val.right hord'' hσk
  exact orth_fieldAutT_of_subfieldConclusion hM hff' hfp1 _ _ hconc (by omega)
    (lieModel_orthPlus_subfield hn4 hfp1 _ hcard')
    ((coordinatePlusWitnessEquiv K e).trans Θ) α
    (congr_eq_fieldAutT _ Θ α V (hVκ.trans ha_def) g' hg'l hg'r hΘ _)

theorem sec66T_K1_POmegaMinus : Sec66T_K1 .POmegaMinus := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn _ _ _ _ _ _ _ _ _
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .POmegaMinus n 2 f :=
    (lieModel_classical_iff (by decide)).mp hM
  have hf : 1 ≤ f := hadm.2.1
  have hn4 : 4 ≤ n := hadm.2.2
  have hn1 : 1 ≤ n := by omega
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, hidx⟩ := orthMinus_hyps hC K hK b c hirr hn1 e
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_minus hC K hK b c hirr e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) α :=
    ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def]
    exact (orderOf_congr _ α).trans hord
  have hainn : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) := by
    rw [ha_def]
    exact fun h => hαinn ((mem_innerAut_congr _ α).mp h)
  have haE : a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) :=
    orth_mem_image_of_orderOf _ hidx hp hp3 ha
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have haD : a ∉ (linearConjugationHom (coordinateQuadMinus n K hn1 b c)).range :=
    orth_not_mem_linearRange_of_not_inner _ hnd hS3 hp hp2 hap hainn
  have hdesc := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent T
    .POmegaMinus (Or.inr (Or.inr rfl)) n 2 f p hC hp hp3 hp2 hn1 K hK b c hirr e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, V, cc, Q₀, hVκ, hVr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hfp1 : 1 ≤ f / p := (Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpf)
  have hff' : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  have hcard' : Nat.card (semilinearFixedSubfield V.val.right) = 2 ^ (f / p) := by
    rw [hVr]
    exact hcard
  have hord'' : orderOf V.val.right = p := by
    rw [hVr]
    exact hord'
  have hK' : Nat.card K = 2 ^ (f / p * p) := by
    rw [Nat.div_mul_cancel hpf]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield V.val.right ↔ V.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  obtain ⟨-, hconc⟩ :=
    CFSG.RankThree.PartOne.orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
      .POmegaMinus (Or.inr (Or.inr rfl)) n 2 (f / p) p hCM.1 hp hp3 hp2 hn1 K
      (semilinearFixedSubfield V.val.right) hcard' hK' V.val.right hord'' hσk b' c' hirr'
  exact orth_fieldAutT_of_subfieldConclusion hM hff' hfp1 _ _ hconc (by omega)
    (lieModel_orthMinus_subfield hn4 hfp1 _ hcard' b' c' hirr')
    ((coordinateMinusWitnessEquiv K hn1 b c e).trans Θ) α
    (congr_eq_fieldAutT _ Θ α V (hVκ.trans ha_def) g' hg'l hg'r hΘ _)

theorem sec66T_K1_POmegaOdd : Sec66T_K1 .POmegaOdd := by
  intro T _ _ p hp hp5 hmodel
  obtain ⟨n, f, hadm, -⟩ := hmodel
  exact absurd rfl hadm.2.2.2

end CFSG.RankThree.PartOne.Sec66T

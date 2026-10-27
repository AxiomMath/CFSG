module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthFixed
public import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JProd
public import CFSG.RankThree.PartOne.K1214.SylowSL2
public import CFSG.RankThree.PartOne.K159.CoverLift

public section

namespace CFSG.StandardType.OrthTorusGen

open Module Multiplicative QuadraticMap Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LayerCores CFSG.StandardType.LayerFacts
open CFSG.StandardType.SevOm
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [CharP K 2] in
theorem eq_left_or_right_of_splitFour {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {R : QuadraticForm K W}
    {T₁ T₂ T : Subgroup (W ≃ₗ[K] W)}
    (hsup : ⁅TauCeti.QuadraticMap.orthogonalGroup R,
      TauCeti.QuadraticMap.orthogonalGroup R⁆ = T₁ ⊔ T₂)
    (hc₁ : CFSG.Assembly.IsComponentOf T₁ (TauCeti.QuadraticMap.orthogonalGroup R))
    (hc₂ : CFSG.Assembly.IsComponentOf T₂ (TauCeti.QuadraticMap.orthogonalGroup R))
    (hTq : CFSG.IsQuasisimple T)
    (hTs : CFSG.Assembly.IsSubnormal T (TauCeti.QuadraticMap.orthogonalGroup R)) :
    T = T₁ ∨ T = T₂ := by
  haveI := CFSG.ClassicalInvolution.ModelFacts.finite_linearEquiv (F := K) (W := W)
  have hTA : CFSG.Assembly.IsComponentOf T (TauCeti.QuadraticMap.orthogonalGroup R) :=
    ⟨ggSubnormal_le hTs, hTs,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hTq⟩
  rcases isComponentOf_eq_or_commute hTA hc₁ with h1 | h1
  · exact Or.inl h1
  rcases isComponentOf_eq_or_commute hTA hc₂ with h2 | h2
  · exact Or.inr h2
  exfalso
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2
  have hTc : T ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup R,
      TauCeti.QuadraticMap.orthogonalGroup R⁆ := by
    rw [← ggCommutator_eq_of_isQuasisimple hTq]
    exact Subgroup.commutator_mono (ggSubnormal_le hTs) (ggSubnormal_le hTs)
  have h5 : ⁅TauCeti.QuadraticMap.orthogonalGroup R,
      TauCeti.QuadraticMap.orthogonalGroup R⁆ ≤ Subgroup.centralizer (T : Set (W ≃ₗ[K] W)) := by
    rw [hsup]
    exact sup_le h1 h2
  exact not_le_centralizer_self_of_isQuasisimple hTA.2.2 (hTc.trans h5)


omit [Finite K] in
theorem splitFour_inf_eq_bot {W : Type} [AddCommGroup W] [Module K W]
    {T₁ T₂ : Subgroup (W ≃ₗ[K] W)}
    (hcomm : ∀ x ∈ T₁, ∀ y ∈ T₂, x * y = y * x)
    {ψ₁ : SL(2, K) →* (W ≃ₗ[K] W)} (hψ₁ : Function.Injective ψ₁)
    (hr₁ : ψ₁.range = T₁) :
    T₁ ⊓ T₂ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨hy₁, hy₂⟩ := Subgroup.mem_inf.mp hy
  have hcent : ∀ z ∈ T₁, z * y = y * z := fun z hz => hcomm z hz y hy₂
  obtain ⟨a, rfl⟩ : ∃ a : SL(2, K), ψ₁ a = y := by
    have : y ∈ ψ₁.range := by rw [hr₁]; exact hy₁
    exact this
  have ha : a ∈ Subgroup.center (SL(2, K)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply hψ₁
    rw [map_mul, map_mul]
    exact hcent (ψ₁ b) (hr₁ ▸ MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  have hmem : a ∈ (⊥ : Subgroup (SL(2, K))) := by
    rw [← CFSG.RankThree.PartOne.K1214.center_SL2_eq_bot]
    exact ha
  have ha1 : a = 1 := Subgroup.mem_bot.mp hmem
  rw [ha1, map_one]

omit [Finite K] in
theorem mem_supportedBlock_of_vanishes (hQ : (polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) {k : Fin r} (hk : toAdd s k = 0)
    {z : V ≃ₗ[K] V} (hzO : z ∈ orthDerived Q) (hzE : ∀ c ∈ E, z * c = c * z)
    (hzfix : ∀ v, (∀ u ∈ F.U k, polar Q u v = 0) → z v = v) :
    z ∈ supportedBlock Q (F.ι s) (X - 1) := by
  have hx := F.oddOrderIsometry hQ hp2 hp hEΩ s
  have hzC : z ∈ isometryCentralizer Q (F.ι s) :=
    Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup hzO,
      Subgroup.mem_centralizer_singleton_iff.mpr (hzE _ (F.mem s))⟩
  have hperp : othersSpace (F.ι s).toLinearMap (X - 1) ≤ suppPerp Q (fixedSpace (F.ι s)) :=
    fun r hr => mem_suppPerp.mpr fun w hw => hx.fixed_others.2 w hw r hr
  exact mem_supportedBlock.mpr ⟨hzC, fun v hv =>
    hzfix v fun u hu => mem_suppPerp.mp (hperp hv) u (F.le_fixedSpace hk hu)⟩

omit [Finite K] [CharP K 2] in
theorem splitFour_zero_card (hQ : (polarBilin Q).Nondegenerate) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) (hV : finrank K V ≤ 2 * r + 2)
    (s : Multiplicative (Fin r → ZMod p))
    (hsp4 : finrank K (fixedSpace (F.ι s)) = 4) :
    (Finset.univ.filter (fun j => toAdd s j = 0)).card = 1 ∨
      (Finset.univ.filter (fun j => toAdd s j = 0)).card = 2 := by
  classical
  have hdim : finrank K (fixedSpace (F.ι s)) =
      finrank K V - 2 * Fintype.card {j : Fin r // toAdd s j ≠ 0} := by
    rw [fixedSpace_eq_suppPerp_frame F s, suppPerp,
      LinearMap.BilinForm.finrank_orthogonal (B := polarBilin Q) hQ,
      finrank_iSup_frame_pieces F hU (fun j => toAdd s j ≠ 0)]
  have hVge : 2 * r ≤ finrank K V := by
    have h := Submodule.finrank_le (⨆ j : {j : Fin r // True}, F.U j.1)
    rw [finrank_iSup_frame_pieces F hU (fun _ => True),
      show Fintype.card {j : Fin r // True} = r from by simp] at h
    exact h
  have hcard : (Finset.univ.filter (fun j => toAdd s j = 0)).card =
      Fintype.card {j : Fin r // toAdd s j = 0} :=
    (Fintype.card_subtype (fun j : Fin r => toAdd s j = 0)).symm
  have hcompl : Fintype.card {j : Fin r // toAdd s j = 0} =
      r - Fintype.card {j : Fin r // toAdd s j ≠ 0} := by
    simpa using Fintype.card_subtype_compl (fun j : Fin r => toAdd s j ≠ 0)
  have hkle : Fintype.card {j : Fin r // toAdd s j ≠ 0} ≤ r := by
    simpa using Fintype.card_subtype_le (fun j : Fin r => toAdd s j ≠ 0)
  omega


omit [Finite K] [CharP K 2] in
theorem splitFour_TJ_isComponent (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) (hx : OddOrderIsometry Q p (F.ι s))
    {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : CFSG.Assembly.IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer {F.ι s}))
    (hJX : J ≤ supportedBlock Q (F.ι s) (X - 1)) :
    CFSG.Assembly.IsComponentOf
      ((J.subgroupOf (supportedBlock Q (F.ι s) (X - 1))).map (fixRho hx))
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace (F.ι s)).subtype)) ∧
      CFSG.IsQuasisimple
        ((J.subgroupOf (supportedBlock Q (F.ι s) (X - 1))).map (fixRho hx)) := by
  set F₀ := supportedBlock Q (F.ι s) (X - 1) with hF₀
  set ρ := fixRho hx with hρ
  set OW := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace (F.ι s)).subtype) with hOW
  set TJ := (J.subgroupOf F₀).map ρ
  have hρinj : Function.Injective ρ := fixRho_injective hx
  have hrange : ρ.range = OW := range_fixRho hx
  have hJcentral : CFSG.Assembly.IsSubnormal J (isometryCentralizer Q (F.ι s)) :=
    (isComponentOf_isometryCentralizer hJ).2.1
  have hJsub : CFSG.Assembly.IsSubnormal J F₀ :=
    ggSubnormal_mono hJcentral hJX (supportedBlock_le_isometryCentralizer _)
  have hTJsub : CFSG.Assembly.IsSubnormal TJ OW := by
    have h := ggSubnormal_map ρ (CFSG.Assembly.IsSubnormal.of_mathlib hJsub.subgroupOf)
    rwa [Subgroup.map_top, hrange] at h
  have hJq : CFSG.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ.2.2
  let eTJ : ↥TJ ≃* ↥J :=
    ((J.subgroupOf F₀).equivMapOfInjective ρ hρinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hJX)
  have hTJq : CFSG.IsQuasisimple TJ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eTJ.symm hJq
  have hTJle : TJ ≤ OW := by
    rw [← hrange]
    exact Subgroup.map_le_range ρ (J.subgroupOf F₀)
  exact ⟨⟨hTJle, hTJsub,
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native TJ).mpr hTJq⟩,
    hTJq⟩

omit [Finite K] [CharP K 2] in
theorem splitFour_mem_of_map_mem (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) (hx : OddOrderIsometry Q p (F.ι s))
    {J : Subgroup (V ≃ₗ[K] V)}
    {T : Subgroup (fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s))}
    (hTJ : (J.subgroupOf (supportedBlock Q (F.ι s) (X - 1))).map (fixRho hx) = T)
    {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q (F.ι s) (X - 1))
    (hmem : fixRho hx ⟨g, hg⟩ ∈ T) : g ∈ J := by
  rw [← hTJ] at hmem
  obtain ⟨j, hj, hje⟩ := Subgroup.mem_map.mp hmem
  have hjeq : j = (⟨g, hg⟩ : ↥(supportedBlock Q (F.ι s) (X - 1))) :=
    fixRho_injective hx hje
  rw [hjeq] at hj
  exact hj

theorem exists_proj_of_isCompl {G : Type*} [Group G] {D T₁ T₂ : Subgroup G}
    (hT₂D : T₂ ≤ D) (hsup : T₁ ⊔ T₂ = D) (hinf : T₁ ⊓ T₂ = ⊥)
    (hcomm : ∀ x ∈ T₁, ∀ y ∈ T₂, x * y = y * x) :
    ∃ φ : ↥D →* ↥(T₂.subgroupOf D), ∀ d : ↥D,
      ((φ d : ↥(T₂.subgroupOf D)) : ↥D) = 1 ↔ d ∈ T₁.subgroupOf D := by
  classical
  let hc : ∀ u ∈ T₂, ∀ v ∈ T₁, u * v = v * u := fun u hu v hv => (hcomm v hv u hu).symm
  have hinf' : T₂ ⊓ T₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hinj : Function.Injective (CFSG.RankThree.PartTwo.Sec14.Ronan148J.commProdHom hc) :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148J.commProdHom_injective hc hinf'
  have hrange : (CFSG.RankThree.PartTwo.Sec14.Ronan148J.commProdHom hc).range = T₂ ⊔ T₁ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148J.commProdHom_range hc
  have hEq : T₂ ⊔ T₁ = D := by rw [sup_comm]; exact hsup
  let e : (↥T₂ × ↥T₁) ≃* ↥D :=
    (MonoidHom.ofInjective hinj).trans
      ((MulEquiv.subgroupCongr hrange).trans (MulEquiv.subgroupCongr hEq))
  have he : ∀ q : ↥T₂ × ↥T₁, ((e q : ↥D) : G) = (q.1 : G) * (q.2 : G) := fun q => rfl
  let φ₀ : ↥D →* ↥T₂ := (MonoidHom.fst T₂ T₁).comp e.symm.toMonoidHom
  refine ⟨(Subgroup.subgroupOfEquivOfLe hT₂D).symm.toMonoidHom.comp φ₀, fun d => ?_⟩
  constructor
  · intro h
    rw [Subgroup.mem_subgroupOf]
    have h1 : (e.symm d).1 = 1 := by
      apply Subtype.ext
      have hc' : ((((Subgroup.subgroupOfEquivOfLe hT₂D).symm.toMonoidHom.comp φ₀) d :
          ↥(T₂.subgroupOf D)) : G) = 1 := by
        simpa using congrArg (fun z : ↥D => (z : G)) h
      simpa [φ₀] using hc'
    have h3 : (d : G) = ((e.symm d).2 : G) := by
      calc (d : G) = ((e (e.symm d) : ↥D) : G) := by rw [e.apply_symm_apply]
        _ = ((e.symm d).1 : G) * ((e.symm d).2 : G) := he (e.symm d)
        _ = ((e.symm d).2 : G) := by rw [h1]; simp
    rw [h3]
    exact (e.symm d).2.2
  · intro hd
    rw [Subgroup.mem_subgroupOf] at hd
    have h2 : e (1, (⟨d, hd⟩ : T₁)) = d := by
      apply Subtype.ext
      exact (he (1, (⟨d, hd⟩ : T₁))).trans (by simp)
    have h1 : e.symm d = (1, (⟨d, hd⟩ : T₁)) := by
      have h2' := e.symm_apply_apply (1, (⟨d, hd⟩ : T₁))
      rw [h2] at h2'
      exact h2'
    apply Subtype.ext
    change ((e.symm d).1 : G) = 1
    rw [h1]
    rfl

theorem isPGroup_closure_pair {G : Type*} [Group G] {p e : ℕ} {u v : G}
    (huv : u * v = v * u) (hu : u ^ p ^ e = 1) (hv : v ^ p ^ e = 1) :
    IsPGroup p ↥(Subgroup.closure ({u, v} : Set G)) := by
  intro x
  refine ⟨e, Subtype.ext ?_⟩
  have hmain : ∀ y ∈ Subgroup.closure ({u, v} : Set G), y ^ p ^ e = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => rcases hy with rfl | rfl <;> assumption
    | one => simp
    | mul a b ha hb iha ihb =>
        rw [(CFSG.RankThree.PartOne.K159.commute_of_mem_closure'
          (S := ({u, v} : Set G)) ?_ ha hb).mul_pow (p ^ e), iha, ihb, mul_one]
        intro s hs t ht
        rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
        · exact Commute.refl _
        · exact huv
        · exact huv.symm
        · exact Commute.refl _
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  exact hmain x x.2

theorem isCyclic_closure_pair_of_sl2 {W : Type} [AddCommGroup W] [Module K W]
    {D T₂ : Subgroup (W ≃ₗ[K] W)} (hT₂D : T₂ ≤ D)
    {ψ : SL(2, K) →* (W ≃ₗ[K] W)} (hψ : Function.Injective ψ) (hr : ψ.range = T₂)
    {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {u v : ↥(T₂.subgroupOf D)}
    (huv : u * v = v * u) (hu : orderOf u ∣ p ^ e) (hv : orderOf v ∣ p ^ e) :
    IsCyclic ↥(Subgroup.closure ({u, v} : Set ↥(T₂.subgroupOf D))) := by
  classical
  let e₂ : ↥(T₂.subgroupOf D) ≃* SL(2, K) :=
    (Subgroup.subgroupOfEquivOfLe hT₂D).trans
      (((MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hr)).symm)
  let P := Subgroup.closure ({u, v} : Set ↥(T₂.subgroupOf D))
  have hP : IsPGroup p P := isPGroup_closure_pair huv
    (orderOf_dvd_iff_pow_eq_one.mp hu) (orderOf_dvd_iff_pow_eq_one.mp hv)
  have hP' : IsPGroup p (P.map e₂.toMonoidHom) := hP.map e₂.toMonoidHom
  have hcyc : IsCyclic ↥(P.map e₂.toMonoidHom) :=
    CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hp2 _ hP'
  exact isCyclic_of_injective
    (P.equivMapOfInjective e₂.toMonoidHom e₂.injective).toMonoidHom
    (P.equivMapOfInjective e₂.toMonoidHom e₂.injective).injective


end CFSG.StandardType.OrthTorusGen

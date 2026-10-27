module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Defs
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.CatalogQ
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def r925FittingIn {Γ : Type} [Group Γ] (J : Subgroup Γ) : Subgroup Γ :=
  (genFittingFitting ↥J).map J.subtype

@[expose] def r925LayerIn {Γ : Type} [Group Γ] (J : Subgroup Γ) : Subgroup Γ :=
  (genFittingLayer ↥J).map J.subtype

@[expose] def r925PCoreGe5 (Γ : Type) [Group Γ] : Subgroup Γ :=
  ⨆ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, CFSG.pCore p.1 Γ

theorem r925_fstar_eq_sup {Γ : Type} [Group Γ] (J : Subgroup Γ) :
    Fstar J = r925FittingIn J ⊔ r925LayerIn J :=
  (Subgroup.map_sup _ _ _)

theorem r925_centralizer_fstar_le_fitting {Γ : Type} [Group Γ] [Finite Γ] (J : Subgroup Γ) :
    centralizer (Fstar J : Set Γ) ⊓ J ≤ r925FittingIn J := by
  intro x hx
  obtain ⟨hxcent, hxJ⟩ := hx
  have hcent : (⟨x, hxJ⟩ : ↥J) ∈ Subgroup.centralizer (genFittingFStar ↥J : Set ↥J) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    change (y : Γ) * x = x * (y : Γ)
    have hyF : (y : Γ) ∈ Fstar J := by
      rw [Fstar]
      exact Subgroup.mem_map_of_mem J.subtype hy
    exact Subgroup.mem_centralizer_iff.mp hxcent (y : Γ) hyF
  have hstar : (⟨x, hxJ⟩ : ↥J) ∈ genFittingFStar ↥J :=
    CFSG.Open.Open.generalized_fitting_self_centralizing ↥J hcent
  have hlayer : genFittingLayer ↥J = CFSG.layer ↥J :=
    CFSG.WholeGroup.layerOf_congr (fun K => (CFSG.isComponent_iff_open K).symm)
  haveI : (genFittingFitting ↥J).Normal := by
    change (CFSG.fittingSubgroup ↥J).Normal
    infer_instance
  rw [genFittingFStar.eq_sup] at hstar
  obtain ⟨f, hf, e, he, hfe⟩ := Subgroup.mem_sup_of_normal_left.mp hstar
  have hecent : (⟨e, he⟩ : ↥(genFittingLayer ↥J)) ∈ Subgroup.center (genFittingLayer ↥J) := by
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    have hmF : (m : ↥J) ∈ genFittingFStar ↥J := by
      rw [genFittingFStar.eq_sup]
      exact Subgroup.mem_sup_right m.2
    have hxm : (m : ↥J) * (⟨x, hxJ⟩ : ↥J) = (⟨x, hxJ⟩ : ↥J) * (m : ↥J) :=
      Subgroup.mem_centralizer_iff.mp hcent (m : ↥J) hmF
    have hcomm : f ∈ Subgroup.centralizer (genFittingLayer ↥J : Set ↥J) := by
      have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.LocalCores.fitting_layer_commute (G := ↥J))
      rw [hlayer]
      exact h hf
    have hfm : f * (m : ↥J) = (m : ↥J) * f :=
      (Subgroup.mem_centralizer_iff.mp hcomm (m : ↥J) m.2).symm
    have hfm' : f⁻¹ * (m : ↥J) = (m : ↥J) * f⁻¹ := by
      have h2 : f⁻¹ * (m : ↥J) * f = (m : ↥J) := by
        rw [mul_assoc, ← hfm, ← mul_assoc, inv_mul_cancel, one_mul]
      calc f⁻¹ * (m : ↥J) = f⁻¹ * (m : ↥J) * (f * f⁻¹) := by group
        _ = (f⁻¹ * (m : ↥J) * f) * f⁻¹ := by group
        _ = (m : ↥J) * f⁻¹ := by rw [h2]
    have hee : e = f⁻¹ * (⟨x, hxJ⟩ : ↥J) := by rw [← hfe]; group
    have hmain : e * (m : ↥J) = (m : ↥J) * e := by
      calc e * (m : ↥J) = (f⁻¹ * (⟨x, hxJ⟩ : ↥J)) * (m : ↥J) := by rw [hee]
        _ = f⁻¹ * ((⟨x, hxJ⟩ : ↥J) * (m : ↥J)) := by group
        _ = f⁻¹ * ((m : ↥J) * (⟨x, hxJ⟩ : ↥J)) := by rw [← hxm]
        _ = (f⁻¹ * (m : ↥J)) * (⟨x, hxJ⟩ : ↥J) := by group
        _ = ((m : ↥J) * f⁻¹) * (⟨x, hxJ⟩ : ↥J) := by rw [hfm']
        _ = (m : ↥J) * (f⁻¹ * (⟨x, hxJ⟩ : ↥J)) := by group
        _ = (m : ↥J) * e := by rw [hee]
    exact hmain.symm
  have heF : e ∈ genFittingFitting ↥J := by
    have hmem : e ∈ (Subgroup.center (genFittingLayer ↥J)).map (genFittingLayer ↥J).subtype :=
      Subgroup.mem_map_of_mem (genFittingLayer ↥J).subtype hecent
    rw [hlayer] at hmem
    change e ∈ CFSG.fittingSubgroup ↥J
    exact CFSG.WholeGroup.center_layer_le_fittingSubgroup (G := ↥J) hmem
  have hxfit : (⟨x, hxJ⟩ : ↥J) ∈ genFittingFitting ↥J := by
    rw [← hfe]
    exact Subgroup.mul_mem _ hf heF
  rw [r925FittingIn]
  exact Subgroup.mem_map_of_mem J.subtype hxfit

private theorem r925_pCore_map_subtype_le {Γ : Type} [Group Γ] {J : Subgroup Γ} (hJ : J.Normal)
    (p : ℕ) : (CFSG.pCore p ↥J).map J.subtype ≤ CFSG.pCore p Γ := by
  haveI : J.Normal := hJ
  exact le_sSup ⟨inferInstance, IsPGroup.map (CFSG.pCore_isPGroup) J.subtype⟩

theorem r925_fitting_le_pCoreGe5 {Γ : Type} [Group Γ] [Finite Γ] (h2 : CFSG.pCore 2 Γ = ⊥) :
    r925FittingIn (CFSG.pPrimeCore 3 Γ) ≤ r925PCoreGe5 Γ := by
  set J := CFSG.pPrimeCore 3 Γ with hJ
  have hJnorm : J.Normal := CFSG.pPrimeCore_normal
  haveI hFn : (genFittingFitting ↥J).Normal := by
    change (CFSG.fittingSubgroup ↥J).Normal
    infer_instance
  haveI hFnil : Group.IsNilpotent ↥(genFittingFitting ↥J) := by
    change Group.IsNilpotent ↥(CFSG.fittingSubgroup ↥J)
    infer_instance
  have hsup : genFittingFitting ↥J ≤
      ⨆ p : (Nat.card ↥J).primeFactors.attach, CFSG.pCore p.1 ↥J :=
    CFSG.normal_nilpotent_le_sup_pCore (N := genFittingFitting ↥J) hFn hFnil
  have hmap : r925FittingIn J ≤
      (⨆ p : (Nat.card ↥J).primeFactors.attach, CFSG.pCore p.1 ↥J).map J.subtype := by
    change (genFittingFitting ↥J).map J.subtype ≤ _
    exact Subgroup.map_mono hsup
  refine hmap.trans ?_
  rw [Subgroup.map_iSup]
  refine iSup_le ?_
  intro p
  haveI : Fact p.1.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.1.2⟩
  refine (r925_pCore_map_subtype_le hJnorm p.1.1).trans ?_
  by_cases hp2 : p.1.1 = 2
  · rw [hp2, h2]
    exact bot_le
  by_cases hp3 : p.1.1 = 3
  · exfalso
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcop : Nat.Coprime 3 (Nat.card ↥J) :=
      CFSG.pPrimeCore_coprime_card (p := 3) (G := Γ)
    have h3dvd : 3 ∣ Nat.card ↥J := hp3 ▸ Nat.dvd_of_mem_primeFactors p.1.2
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop) h3dvd
  · have hp5 : 5 ≤ p.1.1 := by
      by_contra h
      have hlt : p.1.1 < 5 := not_le.1 h
      have h2p : 2 ≤ p.1.1 := (Fact.out : p.1.1.Prime).two_le
      interval_cases p.1.1
      · exact hp2 rfl
      · exact hp3 rfl
      · exact (by norm_num : ¬ Nat.Prime 4) Fact.out
    exact le_iSup (fun r : {q : ℕ // q.Prime ∧ 5 ≤ q} => CFSG.pCore r.1 Γ)
      ⟨p.1.1, Fact.out, hp5⟩

theorem r925_pCoreGe5_orderOf {Γ : Type} [Group Γ] [Finite Γ] :
    ∀ x ∈ r925PCoreGe5 Γ, Nat.Coprime (orderOf x) 6 := by
  intro x hx
  set π : Set Nat.Primes := {p | 5 ≤ p.1} with hπ
  have hle : r925PCoreGe5 Γ ≤ CFSG.piCore π Γ := by
    refine iSup_le ?_
    rintro ⟨p, hp, hp5⟩
    haveI : Fact p.Prime := ⟨hp⟩
    refine CFSG.LocalCores.le_piCore_of_normal CFSG.pCore_normal ?_
    intro q hq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p) (G := Γ))
    have hqp : q.1 = p := by
      have hd : q.1 ∣ p ^ n := hn ▸ hq
      rcases (Nat.dvd_prime hp).mp (q.2.dvd_of_dvd_pow hd) with h | h
      · exact absurd h q.2.ne_one
      · exact h
    show 5 ≤ q.1
    omega
  have hcard : orderOf x ∣ Nat.card (CFSG.piCore π Γ) :=
    (Subgroup.orderOf_dvd_natCard _ hx).trans (Subgroup.card_dvd_of_le hle)
  have hπ' : CFSG.IsPiSubgroup π (CFSG.piCore π Γ) :=
    CFSG.LocalCores.piCore_isPiSubgroup π
  rw [show (6 : ℕ) = 2 * 3 from by norm_num]
  refine Nat.Coprime.mul_right ?_ ?_
  · rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
    intro h2
    have hmem := hπ' ⟨2, Nat.prime_two⟩ (h2.trans hcard)
    rw [hπ] at hmem
    have h52 : (5 : ℕ) ≤ 2 := hmem
    omega
  · rw [Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd]
    intro h3
    have hmem := hπ' ⟨3, Nat.prime_three⟩ (h3.trans hcard)
    rw [hπ] at hmem
    have h53 : (5 : ℕ) ≤ 3 := hmem
    omega

private theorem r925_stage1_normalizes_component {Γ : Type} [Group Γ] [Finite Γ]
    (hr : ∀ q : ℕ, q.Prime → 5 ≤ q → CFSG.Open.pRank q (⊤ : Subgroup Γ) ≤ 2)
    {A : Subgroup Γ} (hA3 : IsThreeGen A) {E : Subgroup Γ} (hE : CFSG.IsComponent E) :
    A ≤ Subgroup.normalizer (E : Set Γ) := by
  rw [← show Subgroup.closure {a : Γ | a ∈ A ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} = A from hA3]
  refine (Subgroup.closure_le _).mpr ?_
  rintro a ⟨haA, k, hak⟩
  by_contra haN
  have horder : orderOf a ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hak
  have hodd : Odd (orderOf a) := Nat.not_even_iff_odd.mp fun h2 => by
    have h23 : 2 ∣ 3 ^ k := (even_iff_two_dvd.mp h2).trans horder
    have h23' : 2 ∣ 3 := Nat.prime_two.dvd_of_dvd_pow h23
    norm_num at h23'
  have h01 : E ≠ E.map (MulAut.conj a).toMonoidHom := by
    rintro h
    exact haN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have h02 : E ≠ E.map (MulAut.conj (a * a)).toMonoidHom := by
    rintro h
    have ha2N : a * a ∈ Subgroup.normalizer (E : Set Γ) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
    have hazp : a ∈ Subgroup.zpowers (a * a) := by
      rw [Subgroup.mem_zpowers_iff]
      obtain ⟨m, hm⟩ := hodd
      refine ⟨((m + 1 : ℕ) : ℤ), ?_⟩
      rw [zpow_natCast]
      calc (a * a) ^ (m + 1) = a ^ (2 * (m + 1)) := by rw [← pow_two, ← pow_mul]
        _ = a ^ (orderOf a + 1) := by rw [show 2 * (m + 1) = orderOf a + 1 by omega]
        _ = a := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
    exact haN ((Subgroup.zpowers_le.mpr ha2N) hazp)
  have h12 : E.map (MulAut.conj a).toMonoidHom ≠
      E.map (MulAut.conj (a * a)).toMonoidHom := by
    rintro h
    apply h01
    have h' : (E.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom =
        (E.map (MulAut.conj (a * a)).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom :=
      congrArg (fun H => H.map (MulAut.conj a⁻¹).toMonoidHom) h
    rw [Subgroup.map_map, Subgroup.map_map] at h'
    have hcomp1 : MonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom
        (MulAut.conj a).toMonoidHom = MonoidHom.id Γ := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    have hcomp2 : MonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom
        (MulAut.conj (a * a)).toMonoidHom = (MulAut.conj a).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hcomp1, hcomp2, Subgroup.map_id] at h'
    exact h'
  obtain ⟨c01, c02, c12⟩ := CFSG.RankThree.conjugate_components_commute hE h01 h02 h12
  have hE_quasi : CFSG.Open.IsQuasisimple ↥E :=
    ⟨(Group.isPerfect_def.mp hE.1.1), hE.1.2.1⟩
  obtain ⟨r, hr_prime, hr5, hrdvd⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.exists_prime_five_le_dvd_of_simple
      hE.1.2.1 hE.1.2.2
  obtain ⟨x, hxo, hxc⟩ :=
    CFSG.AGLEmbedding.exists_orderOf_eq_not_mem_center hr_prime (by omega) hE_quasi hrdvd
  set y : Γ := (x : Γ) with hy
  have hyE : y ∈ E := x.2
  have hyo : orderOf y = r := by rw [hy, Subgroup.orderOf_coe, hxo]
  have hyc : y ∉ Subgroup.centralizer (E : Set Γ) := by
    intro hc
    apply hxc
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc (z : Γ) z.2
  set y₁ : Γ := a * y * a⁻¹ with hy₁
  set y₂ : Γ := a * y₁ * a⁻¹ with hy₂
  have hy₁K₁ : y₁ ∈ E.map (MulAut.conj a).toMonoidHom := ⟨y, hyE, by simp [hy₁]⟩
  have hy₂K₂ : y₂ ∈ E.map (MulAut.conj (a * a)).toMonoidHom := by
    refine ⟨y, hyE, ?_⟩
    show (MulAut.conj (a * a)) y = y₂
    simp only [MulAut.conj_apply, hy₂, hy₁]
    group
  have hy₁o : orderOf y₁ = r := by rw [hy₁, CFSG.RankThree.orderOf_conj_eq, hyo]
  have hy₂o : orderOf y₂ = r := by rw [hy₂, CFSG.RankThree.orderOf_conj_eq, hy₁o]
  have hy₂form : y₂ = (a * a) * y * (a * a)⁻¹ := by rw [hy₂, hy₁]; group
  have hy₁c : y₁ ∉ Subgroup.centralizer (E.map (MulAut.conj a).toMonoidHom : Set Γ) :=
    fun h => hyc (CFSG.RankThree.conj_mem_centralizer_map_conj_iff.mp h)
  have hy₂c : y₂ ∉ Subgroup.centralizer (E.map (MulAut.conj (a * a)).toMonoidHom : Set Γ) := by
    rw [hy₂form]
    exact fun h => hyc (CFSG.RankThree.conj_mem_centralizer_map_conj_iff.mp h)
  have hW₁q : ∀ w ∈ Subgroup.zpowers y, w ^ r = 1 := fun w hw => by
    rw [← hyo]
    exact CFSG.RankThree.pow_orderOf_eq_one_of_mem_zpowers hw
  have hW₁K₁ : Subgroup.zpowers y ≤ Subgroup.centralizer
      (E.map (MulAut.conj a).toMonoidHom : Set Γ) := Subgroup.zpowers_le.2 (c01 hyE)
  have hy₁W₁ : y₁ ∈ Subgroup.centralizer (Subgroup.zpowers y : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hW₁K₁ hw) y₁ hy₁K₁).symm
  have hd₂ : Subgroup.zpowers y ⊓ Subgroup.zpowers y₁ = ⊥ := by
    rw [eq_bot_iff, ← CFSG.RankThree.zpowers_inf_eq_bot_of_not_mem hr_prime hy₁o hy₁c]
    exact fun w hw => ⟨hw.2, hW₁K₁ hw.1⟩
  obtain ⟨hW₂card, hW₂c, hW₂q⟩ :=
    CFSG.RankThree.card_sup_zpowers_of_disjoint hy₁W₁ inferInstance hW₁q hy₁o hd₂
  have hW₂K₂ : Subgroup.zpowers y ⊔ Subgroup.zpowers y₁ ≤ Subgroup.centralizer
      (E.map (MulAut.conj (a * a)).toMonoidHom : Set Γ) :=
    sup_le (Subgroup.zpowers_le.2 (c02 hyE)) (Subgroup.zpowers_le.2 (c12 hy₁K₁))
  have hy₂W₂ : y₂ ∈ Subgroup.centralizer
      ((Subgroup.zpowers y ⊔ Subgroup.zpowers y₁ : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hW₂K₂ hw) y₂ hy₂K₂).symm
  have hd₃ : (Subgroup.zpowers y ⊔ Subgroup.zpowers y₁) ⊓ Subgroup.zpowers y₂ = ⊥ := by
    rw [eq_bot_iff, ← CFSG.RankThree.zpowers_inf_eq_bot_of_not_mem hr_prime hy₂o hy₂c]
    exact fun w hw => ⟨hw.2, hW₂K₂ hw.1⟩
  obtain ⟨hW₃card, hW₃c, hW₃q⟩ :=
    CFSG.RankThree.card_sup_zpowers_of_disjoint hy₂W₂ hW₂c hW₂q hy₂o hd₃
  have hcard : Nat.card
      (Subgroup.zpowers y ⊔ Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ : Subgroup Γ) = r ^ 3 := by
    rw [hW₃card, hW₂card, Nat.card_zpowers, hyo]
    ring
  have h3 : 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup Γ) :=
    CFSG.SectionRank.le_pRank (by omega) le_top ⟨hW₃c, hW₃q⟩ hcard
  have := hr r hr_prime hr5
  omega

private theorem r925_out_solvable_of_component {Γ : Type} [Group Γ] [Finite Γ]
    (hKSch : UCK.KSch) (hΓ : CFSG.Open.IsKGroup Γ) {E : Subgroup Γ}
    (hE : CFSG.IsComponent E) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥E) := by
  haveI hperf : Group.IsPerfect ↥E := hE.1.1
  have hOutQuot : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥E ⧸ Subgroup.center ↥E)) := by
    haveI hsimple : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := hE.1.2.1
    haveI hK : CFSG.Open.IsKGroup (↥E ⧸ Subgroup.center ↥E) :=
      (hΓ.subgroup E).quotient (Subgroup.center ↥E)
    exact hKSch (↥E ⧸ Subgroup.center ↥E) hsimple hK
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥E

private theorem r925_centralizes_of_component {Γ : Type} [Group Γ] [Finite Γ]
    {A E : Subgroup Γ}
    (hEN : A ≤ Subgroup.normalizer (E : Set Γ))
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥E))
    (hE3 : ¬ 3 ∣ Nat.card ↥E)
    (hA : commutator ↥A = ⊤) (hA3 : IsThreeGen A) :
    A ≤ Subgroup.centralizer (E : Set Γ) := by
  haveI hperfA : Group.IsPerfect ↥A := ⟨hA⟩
  haveI hOutI : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥E) := hOut
  let ρ : ↥A →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  have hρ : ∀ (b : ↥A) (x : ↥E), ((ρ b) x : Γ) = (b : Γ) * x * (b : Γ)⁻¹ := fun b x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe E (Subgroup.inclusion hEN b) x
  rw [← show Subgroup.closure {a : Γ | a ∈ A ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} = A from hA3]
  refine (Subgroup.closure_le _).mpr ?_
  rintro a ⟨ha, k, hak⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro x hx
  have hρa1 : ρ ⟨a, ha⟩ = 1 := by
    obtain ⟨t, ht⟩ :=
      CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner ρ ⟨a, ha⟩
    have horder : orderOf (ρ ⟨a, ha⟩) ∣ 3 ^ k := by
      have h1 : orderOf (ρ ⟨a, ha⟩) ∣ orderOf (⟨a, ha⟩ : ↥A) := orderOf_map_dvd ρ ⟨a, ha⟩
      rw [Subgroup.orderOf_mk a ha] at h1
      exact h1.trans (orderOf_dvd_of_pow_eq_one hak)
    have hcard : orderOf (ρ ⟨a, ha⟩) ∣ Nat.card ↥E := by
      rw [ht]
      exact (orderOf_map_dvd (MulAut.conj : ↥E →* MulAut ↥E) t).trans
        (orderOf_dvd_natCard t)
    have hcop : Nat.Coprime (3 ^ k) (Nat.card ↥E) :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hE3).pow_left k
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop horder hcard)
  have hconj : a * x * a⁻¹ = x := by
    have h := congrArg (fun e : MulAut ↥E => (((e ⟨x, hx⟩ : ↥E)) : Γ)) hρa1
    rw [hρ ⟨a, ha⟩ ⟨x, hx⟩] at h
    simpa using h
  calc x * a = (a * x * a⁻¹) * a := by rw [hconj]
    _ = a * x := by group

theorem r925_layer_centralized (hKSch : UCK.KSch) {Γ : Type} [Group Γ] [Finite Γ]
    (hΓ : CFSG.Open.IsKGroup Γ)
    (hr : ∀ q : ℕ, q.Prime → 5 ≤ q → CFSG.Open.pRank q (⊤ : Subgroup Γ) ≤ 2)
    {A : Subgroup Γ} (hA : commutator ↥A = ⊤) (hA3 : IsThreeGen A) :
    A ≤ centralizer (r925LayerIn (CFSG.pPrimeCore 3 Γ) : Set Γ) := by
  haveI hFact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J := CFSG.pPrimeCore 3 Γ with hJ
  have hJnorm : J.Normal := by rw [hJ]; exact CFSG.pPrimeCore_normal
  have hcopJ : Nat.Coprime 3 (Nat.card ↥J) := by
    rw [hJ]; exact CFSG.pPrimeCore_coprime_card
  have hcomp : ∀ K : Subgroup ↥J, CFSG.IsComponent K →
      A ≤ Subgroup.centralizer (K.map J.subtype : Set Γ) := by
    intro K hK
    have hle : K.map J.subtype ≤ J := by
      rintro _ ⟨k, -, rfl⟩; exact k.2
    have hKsub : (K.map J.subtype).IsSubnormal := by
      have hsub : (K.map J.subtype).subgroupOf J = K := by
        change (K.map J.subtype).comap J.subtype = K
        rw [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
      have hKsn : ((K.map J.subtype).subgroupOf J).IsSubnormal := by
        rw [hsub]; exact hK.2
      exact Subgroup.IsSubnormal.trans hle hKsn hJnorm.isSubnormal
    have hE : CFSG.IsComponent (K.map J.subtype) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (K.equivMapOfInjective J.subtype J.subtype_injective) hK.1, hKsub⟩
    have hEN : A ≤ Subgroup.normalizer (K.map J.subtype : Set Γ) :=
      r925_stage1_normalizes_component hr hA3 hE
    have hOut : Group.IsSolvable
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(K.map J.subtype)) :=
      r925_out_solvable_of_component hKSch hΓ hE
    have hE3 : ¬ 3 ∣ Nat.card ↥(K.map J.subtype) := fun h3 =>
      (Nat.prime_three.coprime_iff_not_dvd.mp hcopJ)
        (h3.trans (Subgroup.card_dvd_of_le hle))
    exact r925_centralizes_of_component hEN hOut hE3 hA hA3
  rw [Subgroup.le_centralizer_iff]
  have hle : genFittingLayer ↥J ≤ (Subgroup.centralizer (A : Set Γ)).comap J.subtype := by
    rw [genFittingLayer.eq_sSup]
    refine sSup_le ?_
    rintro L hL
    intro x hx
    change J.subtype x ∈ Subgroup.centralizer (A : Set Γ)
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a ha
    have hKa : A ≤ Subgroup.centralizer (L.map J.subtype : Set Γ) :=
      hcomp L ((CFSG.isComponent_iff_open L).mpr hL)
    exact ((Subgroup.mem_centralizer_iff.mp (hKa ha)) (x : Γ)
      (Subgroup.mem_map_of_mem J.subtype hx)).symm
  change (genFittingLayer ↥J).map J.subtype ≤ Subgroup.centralizer (A : Set Γ)
  exact Subgroup.map_le_iff_le_comap.mpr hle

theorem r925_pcore_rep {Γ : Type} [Group Γ] [Finite Γ] (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hr : CFSG.Open.pRank p (⊤ : Subgroup Γ) ≤ 2) :
    ∃ ψ : Γ →* GL (Fin 2) (ZMod p),
      (∀ g : Γ, ψ g = 1 → ¬ p ∣ orderOf g → ∀ x ∈ CFSG.pCore p Γ, g * x = x * g) ∧
      (∀ g : Γ, (∀ x ∈ CFSG.pCore p Γ, g * x = x * g) → ψ g = 1) := by
  classical
  by_cases hP : CFSG.pCore p Γ = ⊥
  · refine ⟨1, ?_, ?_⟩
    · intro g _ _ x hx
      rw [hP, Subgroup.mem_bot] at hx
      rw [hx, mul_one, one_mul]
    · intro g _
      rfl
  obtain ⟨D, hD⟩ := CFSG.RankThree.PartTwo.Sec4.Census.exists_criticalAt (q := p) (by omega) hP
  have hp1 : 1 < p := by omega
  have hDp : IsPGroup p D := CFSG.pCore_isPGroup.to_le hD.le
  have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by simpa using hD.exp x x.2)
  have hrankD : CFSG.Open.pRank p (⊤ : Subgroup D) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp1 D.subtype D.subtype_injective).trans hr
  obtain ⟨-, hbound⟩ :=
    CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hDp hexp hrankD
  obtain ⟨-, hWcomm, hWpow⟩ := CFSG.SectionRank.Ccomm.frattini_quotient_elementary hDp
  obtain ⟨m, hm⟩ := (hDp.to_quotient (frattini D)).exists_card_eq
  have hmle : m ≤ 2 := by
    rw [hm] at hbound
    exact (Nat.pow_le_pow_iff_right hp1).1 hbound
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hWcomm hWpow hm
  obtain ⟨ι, hι⟩ := CFSG.Quasithin.exists_injective_GL_le_two (R := ZMod p) hmle
  let θ : MulAut (D ⧸ frattini D) →* GL (Fin 2) (ZMod p) :=
    ι.comp (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom
  have hθ : Function.Injective θ := hι.comp (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective
  let ψ : Γ →* GL (Fin 2) (ZMod p) := θ.comp hD.frattiniAct
  have hker : ∀ g : Γ, ψ g = 1 ↔ hD.frattiniAct g = 1 := by
    intro g
    change θ (hD.frattiniAct g) = 1 ↔ hD.frattiniAct g = 1
    rw [← map_one θ, hθ.eq_iff]
  refine ⟨ψ, ?_, ?_⟩
  · intro g hg hcop x hx
    have hgK : g ∈ hD.frattiniKer := by
      rw [CFSG.RankThree.PartTwo.Sec4.Census.CriticalAt.mem_frattiniKer_iff]
      exact (hker g).mp hg
    have hcop' : Nat.Coprime (orderOf g) p :=
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hcop).symm
    have h := hD.centralizes_of_mem_frattiniKer hgK hcop' x hx
    rwa [mul_inv_eq_iff_eq_mul] at h
  · intro g hg
    rw [hker]
    have hconj : hD.conjD g = 1 := by
      apply MulEquiv.ext
      intro d
      apply Subtype.ext
      rw [CFSG.RankThree.PartTwo.Sec4.Census.CriticalAt.conjD_apply, MulAut.one_apply]
      calc g * ↑d * g⁻¹ = ↑d * g * g⁻¹ := by rw [hg d (hD.le d.2)]
        _ = ↑d := by group
    change CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini D)
      (hD.conjD g) = 1
    rw [hconj, map_one]

theorem r925_pcore_centralized_of_rep {Γ : Type} [Group Γ] (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : Subgroup Γ} (hA : IsThreeGen A) {ψ : Γ →* GL (Fin 2) (ZMod p)}
    (hψ : ∀ g : Γ, ψ g = 1 → ¬ p ∣ orderOf g → ∀ x ∈ CFSG.pCore p Γ, g * x = x * g)
    (h1 : ∀ a ∈ A, ψ a = 1) : ∀ a ∈ A, ∀ x ∈ CFSG.pCore p Γ, a * x = x * a := by
  have hAC : A ≤ Subgroup.centralizer (CFSG.pCore p Γ : Set Γ) := by
    have hle : Subgroup.closure {a : Γ | a ∈ A ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} ≤
        Subgroup.centralizer (CFSG.pCore p Γ : Set Γ) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro a ⟨ha, k, hk⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro x hx
      have hp3 : ¬ p ∣ 3 ^ k := by
        intro hdiv
        have hp3' : p = 3 :=
          ((Nat.dvd_prime Nat.prime_three).mp
            ((Fact.out : p.Prime).dvd_of_dvd_pow hdiv)).resolve_left
            (Fact.out : p.Prime).ne_one
        omega
      have horder : orderOf a ∣ 3 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
      exact (hψ a (h1 a ha) (fun h => hp3 (h.trans horder)) x hx).symm
    rwa [show Subgroup.closure {a : Γ | a ∈ A ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} = A from hA] at hle
  intro a ha x hx
  exact (Subgroup.mem_centralizer_iff.mp (hAC ha)) x hx |>.symm

theorem r925_centralizes_pCoreGe5 {Γ : Type} [Group Γ] (A : Subgroup Γ)
    (h : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ a ∈ A, ∀ x ∈ CFSG.pCore p Γ, a * x = x * a) :
    ∀ a ∈ A, ∀ x ∈ r925PCoreGe5 Γ, a * x = x * a := by
  intro a ha x hx
  refine Subgroup.iSup_induction (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => CFSG.pCore p.1 Γ)
    (C := fun x => a * x = x * a) hx (fun p y hy => h p.1 p.2.1 p.2.2 a ha y hy) (by simp)
    (fun y z hy hz => ?_)
  rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]

theorem r925_pcore_reps {Γ : Type} [Group Γ] [Finite Γ]
    (hr : ∀ q : ℕ, q.Prime → 3 < q → CFSG.Open.pRank q (⊤ : Subgroup Γ) ≤ 2) :
    ∃ ψ : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, Γ →* GL (Fin 2) (ZMod p.1),
      ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (∀ g : Γ, ψ p g = 1 → ¬ p.1 ∣ orderOf g → ∀ x ∈ CFSG.pCore p.1 Γ, g * x = x * g) ∧
        (∀ g : Γ, (∀ x ∈ CFSG.pCore p.1 Γ, g * x = x * g) → ψ p g = 1) := by
  have h : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, ∃ ψ : Γ →* GL (Fin 2) (ZMod p.1),
      (∀ g : Γ, ψ g = 1 → ¬ p.1 ∣ orderOf g → ∀ x ∈ CFSG.pCore p.1 Γ, g * x = x * g) ∧
      (∀ g : Γ, (∀ x ∈ CFSG.pCore p.1 Γ, g * x = x * g) → ψ g = 1) := fun p => by
    haveI : Fact p.1.Prime := ⟨p.2.1⟩
    exact r925_pcore_rep p.1 p.2.2 (hr p.1 p.2.1 (by have := p.2.2; omega))
  choose ψ hψ using h
  exact ⟨ψ, hψ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

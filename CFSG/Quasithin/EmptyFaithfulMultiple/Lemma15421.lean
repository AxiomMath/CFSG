module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421Module
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421Component
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1542FourModule

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L15421

section General

variable {G : Type*} [Group G]

theorem not_isComponent_of_isSolvable {Γ : Type*} [Group Γ] [Group.IsSolvable Γ]
    (K : Subgroup Γ) : ¬ CFSG.IsComponent K := by
  rintro ⟨⟨-, hsimple, a, b, hab⟩, -⟩
  have : Group.IsSolvable (↥K ⧸ Subgroup.center ↥K) := inferInstance
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem autI_le_ffJ_of {I L J₀ : Subgroup G} (hIN : I ≤ Subgroup.normalizer (V : Set G))
    (hJ : autI hV (thompsonJ I) ≤ ffJ (autI hV I)) (hLI : L ≤ I) (hJ₀ : J₀ ≤ thompsonJ I)
    (hL : ⁅L, J₀⁆ = L) : autI hV L ≤ ffJ (autI hV I) := by
  rw [← hL, autI_commutator hV (hLI.trans hIN) (hJ₀.trans ((thompsonJ_le_self I).trans hIN))]
  exact (Subgroup.commutator_mono (autI_mono hV hLI) ((autI_mono hV hJ₀).trans hJ)).trans
    (commutator_le_right_of_le_normalizer (B6.le_normalizer_ffJ _))

variable [Finite G]

theorem le_normalizer_of_commute {I L₁ L₂ T₀ : Subgroup G}
    (hIN : I ≤ Subgroup.normalizer (V : Set G)) (hI : I = L₁ ⊔ T₀ ⊔ (L₂ ⊔ T₀))
    (hCI : I ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 I) (hL₁ : L₁ = oTwoUpper L₁)
    (hT₀N : T₀ ≤ Subgroup.normalizer (L₁ : Set G)) (hOT : pCoreOf 2 I ≤ T₀)
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, ∀ (hx : x ∈ Subgroup.normalizer (V : Set G))
      (hy : y ∈ Subgroup.normalizer (V : Set G)),
      convI hV ⟨x, hx⟩ * convI hV ⟨y, hy⟩ = convI hV ⟨y, hy⟩ * convI hV ⟨x, hx⟩) :
    I ≤ Subgroup.normalizer (L₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 I with hQ
  have hL₁I : L₁ ≤ I := hI ▸ le_sup_left.trans le_sup_left
  have hL₂I : L₂ ≤ I := hI ▸ le_sup_left.trans le_sup_right
  have hT₀I : T₀ ≤ I := hI ▸ le_sup_right.trans le_sup_left
  have hQN : I ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I
  set N₁ := L₁ ⊔ Q with hN₁
  have h₁ : L₁ ≤ Subgroup.normalizer (N₁ : Set G) :=
    B2F.le_normalizer_sup Subgroup.le_normalizer (hL₁I.trans hQN)
  have h₀ : T₀ ≤ Subgroup.normalizer (N₁ : Set G) := B2F.le_normalizer_sup hT₀N (hT₀I.trans hQN)
  have h₂ : L₂ ≤ Subgroup.normalizer (N₁ : Set G) := by
    intro y hy
    have hyI := hL₂I hy
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have hx' : x ∈ ((L₁ ⊔ Q : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L₁ Q (hL₁I.trans hQN)] at hx'
    obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.mp hx'
    have haI := hL₁I ha
    have hyN := hIN hyI
    have haN := hIN haI
    have hcN : y * a * y⁻¹ * a⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN haN) (Subgroup.inv_mem _ hyN))
        (Subgroup.inv_mem _ haN)
    have hc : y * a * y⁻¹ * a⁻¹ ∈ Q := by
      rw [← hCI]
      refine ⟨I.mul_mem (I.mul_mem (I.mul_mem hyI haI) (I.inv_mem hyI)) (I.inv_mem haI), ?_⟩
      have e : (⟨y * a * y⁻¹ * a⁻¹, hcN⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨y, hyN⟩ * ⟨a, haN⟩ * ⟨y, hyN⟩⁻¹ * ⟨a, haN⟩⁻¹ := rfl
      have h1 : convI hV ⟨y * a * y⁻¹ * a⁻¹, hcN⟩ = 1 := by
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm a ha y hy haN hyN]
        group
      exact (convI_eq_one_iff hV ⟨y * a * y⁻¹ * a⁻¹, hcN⟩).mp h1
    have hya : y * a * y⁻¹ ∈ N₁ := by
      have e : y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact N₁.mul_mem ((le_sup_right : Q ≤ N₁) hc) ((le_sup_left : L₁ ≤ N₁) ha)
    have hyq : y * q * y⁻¹ ∈ N₁ :=
      (le_sup_right : Q ≤ N₁) ((Subgroup.mem_normalizer_iff.mp (hQN hyI) q).mp hq)
    have e : y * (a * q) * y⁻¹ = (y * a * y⁻¹) * (y * q * y⁻¹) := by group
    rw [e]
    exact N₁.mul_mem hya hyq
  have hIN₁ : I ≤ Subgroup.normalizer (N₁ : Set G) := by
    rw [hI]
    exact sup_le (sup_le h₁ h₀) (sup_le h₂ h₀)
  have hO : oTwoUpper N₁ = L₁ :=
    oTwoUpper_sup_eq hL₁ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I) (hOT.trans hT₀N)
  intro g hg
  have := mem_normalizer_oTwoUpper (hIN₁ hg)
  rwa [hO] at this

end General

section Lemma15421

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

variable (s : Setting15419 G T)

theorem le_normalizer_of_noComponent (hB19 : InputB19) (hyp : MultipleCentralizerHypothesis G T)
    (h8 : Stmt1548 G T) (h12 : Stmt15412 G T) (hF : CharTwo s.I) (hT₀ : IsSylowTwoOf s.T₀ s.I)
    (hV : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter s.T₀) s.I))
    (hnc : ∀ K : Subgroup ↥(autI hV s.I), ¬ CFSG.IsComponent K) :
    s.I ≤ Subgroup.normalizer (s.L₁ : Set G) ∧ s.I ≤ Subgroup.normalizer (s.L₂ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := conjClosure (quasithinOmegaOneCenter s.T₀) s.I with hVdef
  have hIN : s.I ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT₀ hF le_rfl
  obtain ⟨hFF, -, hJeq, hJle⟩ :=
    B2_7_of_not_le hV hred.1 hIN (not_thompsonJ_le s hyp h8 hF hT₀)
  have hJ : autI hV (thompsonJ s.I) ≤ ffJ (autI hV s.I) := hJeq ▸ hJle
  have hO : CFSG.Open.pCore 2 ↥(autI hV s.I) = ⊥ := pCore_autOn_eq_bot hred
  obtain ⟨n, H, hcomm, hDH, hDab, hsq, hJH⟩ :=
    ffJ_eq_iSup_of_noComponent hB19 (fun v => IntMod.sq_eq_one v) hO hFF hnc
  have hcommD : ∀ i j, i ≠ j → ∀ a ∈ oddCoreOfSub (H i), ∀ b ∈ oddCoreOfSub (H j),
      a * b = b * a := fun i j hij a ha b hb => hcomm i j hij a (hDH i ha) b (hDH j hb)
  have hJT := thompsonJ_le_thompsonJ_I s hT₀
  have hD : ∀ L : Subgroup G, L ≤ s.I → L = oTwoUpper L → ⁅L, thompsonJ T⁆ = L →
      autI hV L ≤ ⨆ i, oddCoreOfSub (H i) := by
    intro L hLI hL hLJ
    refine autI_le_of_odd hV hL (hLI.trans hIN) fun x hx ho => ?_
    refine mem_iSup_of_odd hcomm hDH hsq ?_ ?_
    · rw [← hJH]
      exact autI_le_ffJ_of hV hIN hJ hLI hJT hLJ (convI_mem_autI hV hx _)
    · refine Odd.of_dvd_nat ho ?_
      have h := orderOf_map_dvd (convI hV) ⟨x, hIN (hLI hx)⟩
      rwa [Subgroup.orderOf_mk] at h
  have hL₁I : s.L₁ ≤ s.I := le_sup_left.trans le_sup_left
  have hL₂I : s.L₂ ≤ s.I := le_sup_left.trans le_sup_right
  have hD₁ := hD s.L₁ hL₁I (factor_L₁ s).eq_oTwoUpper (commutator_L₁ s)
  have hD₂ := hD s.L₂ hL₂I (factor_L₂ s).eq_oTwoUpper (commutator_L₂ s)
  have hc : ∀ x ∈ s.L₁, ∀ y ∈ s.L₂, ∀ (hx : x ∈ Subgroup.normalizer (V : Set G))
      (hy : y ∈ Subgroup.normalizer (V : Set G)),
      convI hV ⟨x, hx⟩ * convI hV ⟨y, hy⟩ = convI hV ⟨y, hy⟩ * convI hV ⟨x, hx⟩ :=
    fun x hx y hy hxN hyN => commute_of_mem_iSup hcommD hDab (hD₁ (convI_mem_autI hV hx hxN))
      (hD₂ (convI_mem_autI hV hy hyN))
  have hCI := inf_centralizer_eq s hyp h8 hF hT₀
  have hOT : pCoreOf 2 s.I ≤ s.T₀ := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hT₀
  refine ⟨le_normalizer_of_commute hV hIN rfl hCI (factor_L₁ s).eq_oTwoUpper
    (T₀_le_normalizer_L₁ s hyp h12) hOT hc, ?_⟩
  refine le_normalizer_of_commute hV hIN (sup_comm _ _) hCI (factor_L₂ s).eq_oTwoUpper
    (T₀_le_normalizer_L₂ s hyp h12) hOT fun x hx y hy hxN hyN => (hc y hy x hx hyN hxN).symm

theorem isSolvable_of_sup_pPrimeCore (htr : F6.IsGoldschmidtTripleIn s.I s.G₁ s.G₂)
    (h : s.G₁.subgroupOf s.I ⊔ CFSG.pPrimeCore 3 ↥s.I = ⊤) : Group.IsSolvable ↥s.I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨e₁⟩, -, -⟩ := id htr
  have hG₁I : s.G₁ ≤ s.I := le_sup_left
  have hS₃ : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have hq : Group.IsSolvable (↥s.G₁ ⧸ CFSG.Open.pCore 2 ↥s.G₁) :=
    Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective
  have hp : Group.IsSolvable ↥(CFSG.Open.pCore 2 ↥s.G₁) := by
    have := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥s.G₁) 2).isNilpotent
    infer_instance
  have hG₁ : Group.IsSolvable ↥s.G₁ :=
    Group.isSolvable_of_subgroup_quotient (CFSG.Open.pCore 2 ↥s.G₁)
  have hH : Group.IsSolvable ↥(s.G₁.subgroupOf s.I) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hG₁I).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hG₁I).injective
  have hN : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥s.I) := htr.isSolvable_pPrimeCore
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I)).comp (s.G₁.subgroupOf s.I).subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hx : x ∈ ((s.G₁.subgroupOf s.I ⊔ CFSG.pPrimeCore 3 ↥s.I : Subgroup ↥s.I) : Set ↥s.I) := by
      rw [h]
      exact Subgroup.mem_top x
    rw [Subgroup.mul_normal] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simpa using (CFSG.pPrimeCore 3 ↥s.I).inv_mem hb
  have hQ : Group.IsSolvable (↥s.I ⧸ CFSG.pPrimeCore 3 ↥s.I) := Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_subgroup_quotient (CFSG.pPrimeCore 3 ↥s.I)

theorem false_of_component (hC : ComponentComparison15421)
    (hyp : MultipleCentralizerHypothesis G T) (h8 : Stmt1548 G T) (h12 : Stmt15412 G T)
    (h19 : Stmt15419 G T) (hF : CharTwo s.I) (hT₀ : IsSylowTwoOf s.T₀ s.I)
    (hV : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter s.T₀) s.I))
    (hc : ∃ K : Subgroup ↥(autI hV s.I), CFSG.IsComponent K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := hyp.simple
  set V := conjClosure (quasithinOmegaOneCenter s.T₀) s.I with hVdef
  have hIN : s.I ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT₀ hF le_rfl
  obtain ⟨hFF, -⟩ := B2_7_of_not_le hV hred.1 hIN (not_thompsonJ_le s hyp h8 hF hT₀)
  have hO₂ : pCoreOf 2 s.I ≠ ⊥ := (h19 s).2.2.1
  have htr := isGoldschmidtTripleIn s hyp h12 h19 hT₀
  have hamal : IsGoldschmidtAmalgam
      ((s.G₁.subgroupOf s.I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I)))
      ((s.G₂.subgroupOf s.I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I))) := by
    rcases htr.goldschmidt_mod_pPrimeCore with ⟨-, h, -⟩ | ⟨-, -, -, h, -⟩
    · exact h
    · exfalso
      have hI := isSolvable_of_sup_pPrimeCore s htr h
      have hX : Group.IsSolvable ↥(autI hV s.I) := by
        rw [← range_convHom hV s.I hIN]
        exact Group.isSolvable_of_surjective (convHom hV s.I hIN).rangeRestrict_surjective
      obtain ⟨K, hK⟩ := hc
      exact not_isComponent_of_isSolvable K hK
  exact hC G s.I s.G₁ s.G₂ s.T₀ (isSQTKCat_of_hyp hyp hO₂) htr
    (G₁_inf_G₂ s hyp h12 h19) hamal hF hV (inf_centralizer_eq s hyp h8 hF hT₀) hFF hc
    (hyp.sylow.1.to_le (inf_centralizer_le s h8))

end Lemma15421

end L15421

section Main

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

open L15421 in
theorem stmt15421_of (hB19 : InputB19) (hC : ComponentComparison15421)
    (hyp : MultipleCentralizerHypothesis G T) (h8 : Stmt1548 G T) (h12 : Stmt15412 G T)
    (h19 : Stmt15419 G T) (h20 : Stmt15420 G T) : Stmt15421 G T := by
  intro s hF
  have hT₀ : IsSylowTwoOf s.T₀ s.I := h20 s s.I ⟨le_rfl, (h19 s).2.2.1⟩
  obtain ⟨-, hV, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT₀ hF le_rfl
  have hI : s.I = s.L₁ ⊔ s.L₂ ⊔ s.T₀ := by
    change s.L₁ ⊔ s.T₀ ⊔ (s.L₂ ⊔ s.T₀) = s.L₁ ⊔ s.L₂ ⊔ s.T₀
    rw [sup_sup_sup_comm, sup_idem]
  by_cases hc : ∃ K : Subgroup ↥(autI hV s.I), CFSG.IsComponent K
  · exact (false_of_component s hC hyp h8 h12 h19 hF hT₀ hV hc).elim
  · push Not at hc
    exact ⟨hI, le_normalizer_of_noComponent s hB19 hyp h8 h12 hF hT₀ hV hc⟩

end Main

end CFSG.Quasithin.EmptyFaithfulMultiple
